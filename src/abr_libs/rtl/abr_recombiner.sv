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
// abr_recombiner.sv
// --------
// Arithmetic share recombiner — symmetric counterpart to abr_splitter.sv.
// data_o = (share0_i + share1_i) mod q   (MLDSA q=8380417 / MLKEM q=3329)
// LATENCY parameter selects combinational (0) or 2-cycle pipelined path.
// Inputs assumed pre-reduced to [0, q-1].
//
//======================================================================

`include "abr_sva.svh"

module abr_recombiner
    import abr_params_pkg::*;
    import ntt_defines_pkg::*;
    #(
    parameter LATENCY = 2  // 2 = pipelined (abr_ntt_add_sub_mod), 0 = combinational
    )
    (
    input  wire                          clk,
    input  wire                          reset_n,
    input  wire                          zeroize,

    input  wire                          en_i,
    input  wire                          mode,              // 0 = MLDSA, 1 = MLKEM
    input  wire  [REG_SIZE*COEFF_PER_CLK-1:0] share0_i,    // 96-bit share 0
    input  wire  [REG_SIZE*COEFF_PER_CLK-1:0] share1_i,    // 96-bit share 1

    output logic [REG_SIZE*COEFF_PER_CLK-1:0] data_o,      // 96-bit recombined word
    output logic                          ready_o
);

    // Prime selection based on mode
    logic [NTT_REG_SIZE-1:0] prime;
    assign prime = mode ? NTT_REG_SIZE'(MLKEM_Q) : NTT_REG_SIZE'(MLDSA_Q);

    // Unpack 96-bit words into per-coefficient arrays
    logic [NTT_REG_SIZE-1:0] share0_coeff    [COEFF_PER_CLK];
    logic [NTT_REG_SIZE-1:0] share1_coeff    [COEFF_PER_CLK];
    logic [NTT_REG_SIZE-1:0] data_coeff      [COEFF_PER_CLK];

    // 23-bit coefficients in 24-bit slots; bit 23 dropped on input, 0 on output
    genvar k;
    generate
        for (k = 0; k < COEFF_PER_CLK; k++) begin : gen_pack
            assign share0_coeff[k] = share0_i[k*REG_SIZE +: NTT_REG_SIZE];
            assign share1_coeff[k] = share1_i[k*REG_SIZE +: NTT_REG_SIZE];
        end
    endgenerate

    generate
    if (LATENCY == 0) begin : g_comb_recombiner
        // Combinational (a + b) mod q: one compare + conditional subtract.
        logic [NTT_REG_SIZE:0] sum_lane [COEFF_PER_CLK];
        genvar c;
        for (c = 0; c < COEFF_PER_CLK; c++) begin : gen_comb_lane
            assign sum_lane[c]   = {1'b0, share0_coeff[c]} + {1'b0, share1_coeff[c]};
            assign data_coeff[c] = (sum_lane[c] >= {1'b0, prime}) ? (sum_lane[c] - {1'b0, prime})
                                                                  : sum_lane[c][NTT_REG_SIZE-1:0];
        end
        assign ready_o = en_i;
        for (k = 0; k < COEFF_PER_CLK; k++) begin : gen_comb_pack
            assign data_o[k*REG_SIZE +: REG_SIZE] = {1'b0, data_coeff[k]};
        end
    end
    else begin : g_pipe_recombiner
        // 2-cycle pipelined path via abr_ntt_add_sub_mod.
        logic [NTT_REG_SIZE-1:0] data_coeff_reg [COEFF_PER_CLK];
        logic [COEFF_PER_CLK-1:0] lane_ready;

        // Flop res_o so data_o is aligned with ready_o (2 cycles after en_i).
        always_ff @(posedge clk or negedge reset_n) begin
            if (!reset_n)
                for (int idx = 0; idx < COEFF_PER_CLK; idx++) data_coeff_reg[idx] <= '0;
            else if (zeroize)
                for (int idx = 0; idx < COEFF_PER_CLK; idx++) data_coeff_reg[idx] <= '0;
            else
                data_coeff_reg <= data_coeff;
        end

        for (k = 0; k < COEFF_PER_CLK; k++) begin : gen_pipe_pack
            assign data_o[k*REG_SIZE +: REG_SIZE] = {1'b0, data_coeff_reg[k]};
        end

        genvar i;
        for (i = 0; i < COEFF_PER_CLK; i++) begin : gen_lane

            abr_ntt_add_sub_mod #(
                .REG_SIZE(NTT_REG_SIZE)
            ) u_add (
                .clk      (clk),
                .reset_n  (reset_n),
                .zeroize  (zeroize),
                .add_en_i (en_i),
                .sub_i    (1'b0),
                .opa_i    (share0_coeff[i]),
                .opb_i    (share1_coeff[i]),
                .prime_i  (prime),
                .mlkem    (mode),
                .res_o    (data_coeff[i]),
                .ready_o  (lane_ready[i])
            );

        end

        assign ready_o = lane_ready[0];
    end
    endgenerate

endmodule
