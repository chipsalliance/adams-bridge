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
// Arithmetic share recombiner for SCA protection — symmetric counterpart
// to abr_splitter.sv.
// 2-cycle pipeline stage with `en_i` input qualifier and `ready_o` strobe.
// Recombines two 96-bit shares into one 96-bit word:
//   data_o = (share0_i + share1_i) mod q
// Supports MLDSA (q=8380417, 23-bit coefficients) and MLKEM (q=3329, 12-bit).
// `ready_o` indicates when `data_o` is stable; the wrapper uses it directly
// as the downstream DV strobe.
// No randomness consumption — purely additive (mirror of the splitter's
// share1 subtraction path, with sub_i tied low).
//
// Inputs are assumed pre-reduced to [0, q-1] — the symmetric contract to the
// splitter's MldsaDataBit23Zero_A / MlkemDataUpperZero_A assertions. These
// mirror SVAs will be added in a follow-on sub-step (Step 27.6 / SVA pass);
// the assumption is documented inline below.
//
//======================================================================

`include "abr_sva.svh"

module abr_recombiner
    import abr_params_pkg::*;
    import ntt_defines_pkg::*;
    #(
    parameter LATENCY = 2  // Step 27.2.3: 2 = original pipelined (uses abr_ntt_add_sub_mod),
                           //              0 = combinational (a+b) mod q — used by the
                           //                  fused-PWS path so the recombiner can drop
                           //                  into pwm_a's read window at T = SRAM_LATENCY
                           //                  exactly when NTT[0]'s timing-driven PWS
                           //                  combinationally samples pwm_a_rd_data.
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

    // Unpack inputs / pack outputs (23-bit coefficients in 24-bit slots,
    // bit 23 dropped on input and forced to 0 on output — same convention
    // as abr_splitter.sv lines 84–90)
    genvar k;
    generate
        for (k = 0; k < COEFF_PER_CLK; k++) begin : gen_pack
            assign share0_coeff[k] = share0_i[k*REG_SIZE +: NTT_REG_SIZE];
            assign share1_coeff[k] = share1_i[k*REG_SIZE +: NTT_REG_SIZE];
        end
    endgenerate

    generate
    if (LATENCY == 0) begin : g_comb_recombiner
        // -------------------------------------------------------------------
        // Combinational (a + b) mod q per coefficient. Inputs are pre-reduced
        // (share0, share1 < q each), so sum < 2q. One compare + conditional
        // subtract is sufficient — no need for the 2-stage abr_ntt_add_sub_mod
        // pipeline. data_o tracks share0_i + share1_i with zero cycle delay;
        // ready_o = en_i so a consumer can use it as a combinational DV strobe.
        // -------------------------------------------------------------------
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
        // -------------------------------------------------------------------
        // Original 2-cycle pipelined path (uses abr_ntt_add_sub_mod). Preserved
        // verbatim for callers that need a registered output.
        // -------------------------------------------------------------------
        logic [NTT_REG_SIZE-1:0] data_coeff_reg [COEFF_PER_CLK];
        logic [COEFF_PER_CLK-1:0] lane_ready;

        // Register the combinational res_o from add_sub_mod to lock the 2-cycle
        // contract — mirrors splitter's share1_coeff_reg pattern (lines 68–79 of
        // abr_splitter.sv). add_sub_mod produces res_o combinationally 1 cycle
        // after add_en_i; this flop adds one more cycle to align with ready_o,
        // which strobes 2 cycles after add_en_i.
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

            // --- (share0 + share1) mod q ---
            // sub_i tied low → add mode. Both inputs assumed < q (see header
            // comment on the pre-reduced-share contract). Output res_o is
            // combinationally valid 1 cycle after add_en_i; data_coeff_reg
            // above adds the second cycle to align with lane_ready strobe.
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

        // All lanes have identical timing — use lane 0's ready
        assign ready_o = lane_ready[0];
    end
    endgenerate

    // --- Input range assertions (deferred to Step 27.6 SVA pass) ---
    // Mirror conditions to splitter's MldsaDataBit23Zero_A / MlkemDataUpperZero_A
    // (abr_splitter.sv lines 151–158). To be added in a follow-on sub-step:
    //   MLDSA: en_i && !mode |-> share0_i/share1_i bit-23 of each lane == 1'b0
    //   MLKEM: en_i &&  mode |-> share0_i/share1_i upper 12 bits of each lane == 0

endmodule
