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

// +---------------------------------------------------+
// | Copyright (c) LUBIS EDA GmbH, all rights reserved |
// | Contact: contact@lubis-eda.com                    |
// +---------------------------------------------------+

// Input contract of abr_recombiner: every 23-bit share coefficient is pre-reduced to
// [0, q-1] for the selected mode (these shares are produced by abr_splitter).
// Bit 23 of each 24-bit input slot is left unconstrained; the DUT must ignore it.

module fv_abr_recombiner_constraints
    import abr_params_pkg::*;
    import ntt_defines_pkg::*;
(
    input logic                                 pi_clk,
    input logic                                 pi_rst_b,
    input logic                                 pi_mode,
    input logic [REG_SIZE*COEFF_PER_CLK-1:0]    pi_share0_i,
    input logic [REG_SIZE*COEFF_PER_CLK-1:0]    pi_share1_i,
    input logic [REG_SIZE*COEFF_PER_CLK-1:0]    po_data_o
);

    default clocking default_clk @(posedge pi_clk); endclocking

    logic [NTT_REG_SIZE-1:0] fv_q;
    assign fv_q = pi_mode ? NTT_REG_SIZE'(MLKEM_Q) : NTT_REG_SIZE'(MLDSA_Q);

    for (genvar k = 0; k < COEFF_PER_CLK; k++) begin : gen_lane
        assume_share0_lt_q: assume property (pi_share0_i[k*REG_SIZE +: NTT_REG_SIZE] < fv_q);
        assume_share1_lt_q: assume property (pi_share1_i[k*REG_SIZE +: NTT_REG_SIZE] < fv_q);
    end

endmodule
