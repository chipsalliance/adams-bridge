// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
//======================================================================
//
// abr_splitter.sv
// --------
// Arithmetic share splitter for SCA protection.
// Pure 2-cycle pipeline stage — no handshake, no enable.
// Splits a 96-bit memory word (4 coefficients × 23 bits) into two shares:
//   share0 = rand (delayed 2 cycles)
//   share1 = (data - rand) mod q (1 cycle from add_sub_mod + 1 output register)
// Supports MLDSA (q=8380417, 23-bit coefficients) and MLKEM (q=3329, 12-bit).
// Validity is controlled by the producer's DV/addr delay chain, not by this module.
// LFSR is external — this module consumes 96 bits of randomness per word.
//
//======================================================================

module abr_splitter
    import abr_params_pkg::*;
    import ntt_defines_pkg::*;
    (
    input  wire                          clk,
    input  wire                          reset_n,
    input  wire                          zeroize,

    input  wire                          en_i,
    input  wire                          mode,              // 0 = MLDSA, 1 = MLKEM
    input  wire  [ABR_MEM_DATA_WIDTH-1:0] data_i,          // 96-bit input word
    input  wire  [ABR_MEM_DATA_WIDTH-1:0] rand_i,          // 96-bit random from LFSR

    output logic [ABR_MEM_DATA_WIDTH-1:0] share0_o,        // 96-bit share 0 (random)
    output logic [ABR_MEM_DATA_WIDTH-1:0] share1_o,        // 96-bit share 1 (data - rand) mod q
    output logic                          ready_o
);

    // Prime selection based on mode
    logic [NTT_REG_SIZE-1:0] prime;
    assign prime = mode ? NTT_REG_SIZE'(MLKEM_Q) : NTT_REG_SIZE'(MLDSA_Q);

    // Unpack 96-bit words into per-coefficient arrays
    logic [NTT_REG_SIZE-1:0] data_coeff  [COEFF_PER_CLK];
    logic [NTT_REG_SIZE-1:0] rand_coeff  [COEFF_PER_CLK];
    logic [NTT_REG_SIZE-1:0] share0_coeff[COEFF_PER_CLK];
    logic [NTT_REG_SIZE-1:0] share1_coeff[COEFF_PER_CLK];
    logic [NTT_REG_SIZE-1:0] share1_coeff_reg[COEFF_PER_CLK];
    logic [COEFF_PER_CLK-1:0] lane_ready;

    // Register share1 (add_sub_mod res_o) to make total share1 path = 2 cycles.
    // add_sub_mod: res_o is combinationally valid 1 cycle after add_en_i.
    // This register captures it, giving 2-cycle total latency matching
    // the 2-stage rand/DV/addr delay chain in the producer.
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            for (int idx = 0; idx < COEFF_PER_CLK; idx++) share1_coeff_reg[idx] <= '0;
        else if (zeroize)
            for (int idx = 0; idx < COEFF_PER_CLK; idx++) share1_coeff_reg[idx] <= '0;
        else
            share1_coeff_reg <= share1_coeff;
    end

    // Unpack inputs / pack outputs (23-bit coefficients in 24-bit slots)
    genvar k;
    generate
        for (k = 0; k < COEFF_PER_CLK; k++) begin : gen_pack
            assign data_coeff[k] = data_i[k*REG_SIZE +: NTT_REG_SIZE];
            assign rand_coeff[k] = rand_i[k*REG_SIZE +: NTT_REG_SIZE];
            assign share0_o[k*REG_SIZE +: REG_SIZE] = {1'b0, share0_coeff[k]};
            assign share1_o[k*REG_SIZE +: REG_SIZE] = {1'b0, share1_coeff_reg[k]};
        end
    endgenerate

    genvar i;
    generate
        for (i = 0; i < COEFF_PER_CLK; i++) begin : gen_lane

            // --- Reduce LFSR random to [0, q-1] ---
            // LFSR produces [0, 2^NTT_REG_SIZE-1]. add_sub_mod assumes inputs < q.
            // Since 2^NTT_REG_SIZE-1 < 2*q for both MLDSA and MLKEM, a single
            // conditional subtraction suffices.
            logic [NTT_REG_SIZE-1:0] rand_reduced;
            logic [NTT_REG_SIZE-1:0] rand_raw;

            assign rand_raw = mode ? {{(NTT_REG_SIZE-MLKEM_REG_SIZE){1'b0}},
                                      rand_coeff[i][MLKEM_REG_SIZE-1:0]}
                                   : rand_coeff[i];
            assign rand_reduced = (rand_raw >= prime) ? (rand_raw - prime) : rand_raw;

            // --- share1: (data - rand_reduced) mod q ---
            abr_ntt_add_sub_mod #(
                .REG_SIZE(NTT_REG_SIZE)
            ) u_sub (
                .clk      (clk),
                .reset_n  (reset_n),
                .zeroize  (zeroize),
                .add_en_i (en_i),
                .sub_i    (1'b1),
                .opa_i    (data_coeff[i]),
                .opb_i    (rand_reduced),
                .prime_i  (prime),
                .mlkem    (mode),
                .res_o    (share1_coeff[i]),
                .ready_o  (lane_ready[i])
            );

            // --- share0: rand_reduced delayed 2 cycles ---
            logic [NTT_REG_SIZE-1:0] rand_d1, rand_d2;

            always_ff @(posedge clk or negedge reset_n) begin
                if (!reset_n) begin
                    rand_d1 <= '0;
                    rand_d2 <= '0;
                end
                else if (zeroize) begin
                    rand_d1 <= '0;
                    rand_d2 <= '0;
                end
                else begin
                    rand_d1 <= rand_reduced;
                    rand_d2 <= rand_d1;
                end
            end

            assign share0_coeff[i] = rand_d2;

        end
    endgenerate

    // All lanes have identical timing — use lane 0's ready
    assign ready_o = lane_ready[0];

    // --- Input data range assertions ---
    `include "abr_sva.svh"

    genvar j;
    generate
        for (j = 0; j < COEFF_PER_CLK; j++) begin : gen_assert
            // MLDSA: bit 23 must be zero (values are < q = 8380417 < 2^23)
            `ABR_ASSERT(MldsaDataBit23Zero_A,
                en_i && !mode |-> data_i[j*REG_SIZE + NTT_REG_SIZE] == 1'b0,
                clk, !reset_n)

            // MLKEM: upper 12 bits (bits 23:12) must be zero (values are < q = 3329 < 2^12)
            `ABR_ASSERT(MlkemDataUpperZero_A,
                en_i && mode |-> data_i[j*REG_SIZE +: REG_SIZE] >> MLKEM_REG_SIZE == '0,
                clk, !reset_n)
        end
    endgenerate

endmodule
