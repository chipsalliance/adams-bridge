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
// Combinational path. Timing alignment with SRAM read latency is handled
// externally by the caller via *_recombine_en_pipe shift registers.
// Inputs assumed pre-reduced to [0, q-1].
//
//======================================================================

`include "abr_sva.svh"

module abr_recombiner
    import abr_params_pkg::*;
    import ntt_defines_pkg::*;
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

    // Combinational (a + b) mod q: one compare + conditional subtract.
    logic [NTT_REG_SIZE:0] sum_lane [COEFF_PER_CLK];
    generate
        genvar c;
        for (c = 0; c < COEFF_PER_CLK; c++) begin : gen_comb_lane
            assign sum_lane[c]   = {1'b0, share0_coeff[c]} + {1'b0, share1_coeff[c]};
            assign data_coeff[c] = (sum_lane[c] >= {1'b0, prime}) ? (sum_lane[c] - {1'b0, prime})
                                                                  : sum_lane[c][NTT_REG_SIZE-1:0];
        end

        for (k = 0; k < COEFF_PER_CLK; k++) begin : gen_comb_pack
            assign data_o[k*REG_SIZE +: REG_SIZE] = {1'b0, data_coeff[k]};
        end
    endgenerate

    assign ready_o = en_i;

endmodule
