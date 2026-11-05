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

// Unit-level AIP for abr_recombiner: data_o = (share0_i + share1_i) mod q per coefficient
// lane, q = MLDSA_Q (mode = 0) or MLKEM_Q (mode = 1).

module fv_abr_recombiner_top
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

    fv_abr_recombiner_constraints fv_abr_recombiner_constraints_i (.*);

    // Reference: per-lane modular addition computed with the % operator, independent of
    // the compare-and-subtract structure used in the RTL.
    logic [NTT_REG_SIZE-1:0] fv_q;
    assign fv_q = pi_mode ? NTT_REG_SIZE'(MLKEM_Q) : NTT_REG_SIZE'(MLDSA_Q);

    for (genvar k = 0; k < COEFF_PER_CLK; k++) begin : gen_lane
        logic [NTT_REG_SIZE-1:0] fv_s0;
        logic [NTT_REG_SIZE-1:0] fv_s1;
        logic [NTT_REG_SIZE:0]   fv_sum;
        logic [NTT_REG_SIZE-1:0] fv_ref;

        assign fv_s0  = pi_share0_i[k*REG_SIZE +: NTT_REG_SIZE];
        assign fv_s1  = pi_share1_i[k*REG_SIZE +: NTT_REG_SIZE];
        assign fv_sum = {1'b0, fv_s0} + {1'b0, fv_s1};
        assign fv_ref = pi_mode ? NTT_REG_SIZE'(fv_sum % (NTT_REG_SIZE+1)'(MLKEM_Q))
                                : NTT_REG_SIZE'(fv_sum % (NTT_REG_SIZE+1)'(MLDSA_Q));

        // Recombined coefficient equals (share0 + share1) mod q.
        assert_data_mod_q_a: assert property (
            po_data_o[k*REG_SIZE +: NTT_REG_SIZE] == fv_ref
        );

        // Recombined coefficient is fully reduced.
        assert_data_lt_q_a: assert property (
            po_data_o[k*REG_SIZE +: NTT_REG_SIZE] < fv_q
        );

        // Bit 23 of every output slot is zero.
        assert_data_msb_zero_a: assert property (
            po_data_o[k*REG_SIZE + NTT_REG_SIZE] == 1'b0
        );

        // Both branches of the modular reduction are reachable in each mode.
        cover_lane_wrap_mldsa_c:    cover property (!pi_mode && (fv_sum >= {1'b0, fv_q}));
        cover_lane_no_wrap_mldsa_c: cover property (!pi_mode && (fv_sum <  {1'b0, fv_q}));
        cover_lane_wrap_mlkem_c:    cover property ( pi_mode && (fv_sum >= {1'b0, fv_q}));
        cover_lane_no_wrap_mlkem_c: cover property ( pi_mode && (fv_sum <  {1'b0, fv_q}));
    end

    // All-zero shares (the inactive bank in abr_top) recombine to an all-zero word, so the
    // OR-merge of both bank outputs in abr_top is lossless.
    assert_zero_shares_zero_data_a: assert property (
        (pi_share0_i == '0) && (pi_share1_i == '0)
        |->
        po_data_o == '0
    );

endmodule

bind fv_abr_recombiner_wrapper fv_abr_recombiner_top fv_abr_recombiner_top_i (
    .pi_clk      (clk),
    .pi_rst_b    (rst_b),
    .pi_mode     (pi_mode),
    .pi_share0_i (pi_share0_i),
    .pi_share1_i (pi_share1_i),
    .po_data_o   (po_data_o)
);
