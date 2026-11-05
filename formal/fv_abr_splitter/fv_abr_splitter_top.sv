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

// -------------------------------------------------
// Copyright(c) LUBIS EDA GmbH, All rights reserved
// Contact: contact@lubis-eda.com
// -------------------------------------------------
//#$includes

//`include "abr_sva.svh"
//$#//

module fv_abr_splitter_top
    //#$imports
    import abr_params_pkg::*;
    import ntt_defines_pkg::*;
    //$#//
#(
    //#$parameters
    //$#//
    //#$localparams
    //$#//
) (
    //#$ports
    input wire                           pi_clk,
    input wire                           pi_reset_n,
    input wire                           pi_zeroize,
    input wire                           pi_en_i,
    input wire                           pi_mode,
    input wire [ABR_MEM_DATA_WIDTH-1:0]  pi_data_i,
    input wire [ABR_MEM_DATA_WIDTH-1:0]  pi_rand_i,
    input logic [ABR_MEM_DATA_WIDTH-1:0] po_share0_o,
    input logic [ABR_MEM_DATA_WIDTH-1:0] po_share1_o,
    input logic                          po_ready_o
    //$#//
);

    default clocking default_clk @(posedge pi_clk); endclocking

    //#$instances
    fv_abr_splitter_constraints #(
    ) fv_abr_splitter_constraints_i (.*);

    //$#//

    localparam SB_DEPTH = 4;
    localparam SB_DW    = (SB_DEPTH == 1) ? 1 : $clog2(SB_DEPTH);

    logic [SB_DW-1:0]              fv_number_of_elements;
    logic [ABR_MEM_DATA_WIDTH-1:0] fv_reconstructed;

    assign fv_number_of_elements = SB_DW'(1);

    generate
        for (genvar k = 0; k < COEFF_PER_CLK; k++) begin : gen_reconstruct
            logic [NTT_REG_SIZE:0] fv_share_sum;
            assign fv_share_sum = pi_mode
                ? (NTT_REG_SIZE+1)'(po_share0_o[k*REG_SIZE +: MLKEM_REG_SIZE]) +
                  (NTT_REG_SIZE+1)'(po_share1_o[k*REG_SIZE +: MLKEM_REG_SIZE])
                : (NTT_REG_SIZE+1)'(po_share0_o[k*REG_SIZE +: NTT_REG_SIZE]) +
                  (NTT_REG_SIZE+1)'(po_share1_o[k*REG_SIZE +: NTT_REG_SIZE]);
            assign fv_reconstructed[k*REG_SIZE +: REG_SIZE] = pi_mode
                ? REG_SIZE'((fv_share_sum >= MLKEM_Q) ? fv_share_sum - MLKEM_Q : fv_share_sum)
                : REG_SIZE'((fv_share_sum >= MLDSA_Q) ? fv_share_sum - MLDSA_Q : fv_share_sum);
        end
    endgenerate

    lubis_scoreboard #(
        .OUTPUT_DATA_WIDTH  (ABR_MEM_DATA_WIDTH),
        .DEPTH              (SB_DEPTH),
        .MAX_DELAY          (2),
        .BYPASS             (0),
        .ASSUME_INVARIANTS  (0)
    ) fv_lubis_scoreboard_i (
        .clk                 (pi_clk),
        .rst                 (!pi_reset_n || pi_zeroize),
        .soft_rst            (1'b0),
        .push                (pi_en_i),
        .pop                 (po_ready_o),
        .full                (1'b0),
        .empty               (1'b0),
        .observed_data       (fv_reconstructed),
        .expected_data       (pi_data_i),
        .number_of_elements  (fv_number_of_elements),
        .stall               (1'b0),

        .selected_element    (/* unused */),
        .sampled_in          (/* unused */),
        .sampled_in_reg      (/* unused */),
        .sampled_out         (/* unused */),
        .sampled_out_reg     (/* unused */),
        .tracking_counter_out(/* unused */)
    );

    // ──────────── Range checks ────────────
    genvar i;
    generate
        for (i = 0; i < COEFF_PER_CLK; i++) begin : gen_range_checks

            // MLDSA output range
            // Full 24-bit slot < MLDSA_Q also implies the packed top bit is 0.
            property abr_splitter_mldsa_output_range;
                (!pi_mode && po_ready_o)
            |->
                po_share0_o[i*REG_SIZE +: REG_SIZE] < MLDSA_Q &&
                po_share1_o[i*REG_SIZE +: REG_SIZE] < MLDSA_Q
            ;endproperty
            assert_abr_splitter_mldsa_output_range: assert property (
                disable iff(!pi_reset_n | pi_zeroize) abr_splitter_mldsa_output_range);

            // MLKEM output range
            // Full 24-bit slot < MLKEM_Q also implies bits [23:12] are 0.
            property abr_splitter_mlkem_output_range;
                (pi_mode && po_ready_o)
            |->
                po_share0_o[i*REG_SIZE +: REG_SIZE] < MLKEM_Q &&
                po_share1_o[i*REG_SIZE +: REG_SIZE] < MLKEM_Q
            ;endproperty
            assert_abr_splitter_mlkem_output_range: assert property (
                disable iff(!pi_reset_n | pi_zeroize) abr_splitter_mlkem_output_range);

            // rand_reduced range
            // Single conditional subtraction brings the LFSR value into [0, q).
            property abr_splitter_rand_reduced_range;
                abr_splitter.rand_reduced[i] < (pi_mode ? MLKEM_Q : MLDSA_Q)
            ;endproperty
            assert_abr_splitter_rand_reduced_range: assert property (
                disable iff(!pi_reset_n | pi_zeroize) abr_splitter_rand_reduced_range);

        end
    endgenerate

    // ──────────── Randomness path correctness ────────────
    // share0 is delayed rand_reduced
    // share1 is registered sub-mod result
    generate
        for (genvar r = 0; r < COEFF_PER_CLK; r++) begin : gen_rand_model

            logic [NTT_REG_SIZE-1:0] fv_rand_raw;
            logic [NTT_REG_SIZE-1:0] fv_rand_reduced;

            assign fv_rand_raw = pi_mode
                ? {{(NTT_REG_SIZE-MLKEM_REG_SIZE){1'b0}},
                   pi_rand_i[r*REG_SIZE +: MLKEM_REG_SIZE]}
                : pi_rand_i[r*REG_SIZE +: NTT_REG_SIZE];

            assign fv_rand_reduced = (fv_rand_raw >= (pi_mode ? MLKEM_Q : MLDSA_Q))
                ? fv_rand_raw - (pi_mode ? MLKEM_Q : MLDSA_Q)
                : fv_rand_raw;

            property abr_splitter_share0_is_reduced_rand;
                ##2 po_share0_o[r*REG_SIZE +: REG_SIZE] ==
                    {1'b0, $past(fv_rand_reduced, 2)}
            ;endproperty
            assert_abr_splitter_share0_is_reduced_rand: assert property (
                disable iff(!pi_reset_n | pi_zeroize) abr_splitter_share0_is_reduced_rand);


            logic [NTT_REG_SIZE-1:0] fv_data;
            logic [NTT_REG_SIZE-1:0] fv_share1_exp;

            assign fv_data = pi_mode
                ? {{(NTT_REG_SIZE-MLKEM_REG_SIZE){1'b0}},
                   pi_data_i[r*REG_SIZE +: MLKEM_REG_SIZE]}
                : pi_data_i[r*REG_SIZE +: NTT_REG_SIZE];

            assign fv_share1_exp = (fv_data >= fv_rand_reduced)
                ? fv_data - fv_rand_reduced
                : NTT_REG_SIZE'(fv_data + (pi_mode ? MLKEM_Q : MLDSA_Q) - fv_rand_reduced);

            property abr_splitter_share1_is_masked_data;
                ##2 $past(pi_en_i, 2)
            |->
                po_share1_o[r*REG_SIZE +: REG_SIZE] ==
                    {1'b0, $past(fv_share1_exp, 2)}
            ;endproperty
            assert_abr_splitter_share1_is_masked_data: assert property (
                disable iff(!pi_reset_n | pi_zeroize) abr_splitter_share1_is_masked_data);

        end
    endgenerate

    // ──────────── Reset / zeroize checks ────────────
    property abr_splitter_reset_clears;
        $past(!pi_reset_n)
    |->
        po_share0_o == '0 && po_share1_o == '0 && !po_ready_o
    ;endproperty
    assert_abr_splitter_reset_clears: assert property (abr_splitter_reset_clears);

    property abr_splitter_zeroize_clears;
        pi_zeroize
    |=>
        po_share0_o == '0 && po_share1_o == '0 && !po_ready_o
    ;endproperty
    assert_abr_splitter_zeroize_clears: assert property (abr_splitter_zeroize_clears);

    generate
        for (genvar r = 0; r < COEFF_PER_CLK; r++) begin : gen_reset_zeroize_check
            property abr_splitter_reset_clears_regs;
                $past(!pi_reset_n)
            |->
                abr_splitter.rand_d1[r]                        == '0   &&
                abr_splitter.rand_d2[r]                        == '0   &&
                abr_splitter.share1_coeff_reg[r]               == '0   &&
                abr_splitter.gen_lane[r].u_sub.r0_reg          == '0   &&
                abr_splitter.gen_lane[r].u_sub.carry0_reg      == 1'b0 &&
                abr_splitter.gen_lane[r].u_sub.sub_n           == 1'b0 &&
                abr_splitter.gen_lane[r].u_sub.opb1            == '0   &&
                abr_splitter.gen_lane[r].u_sub.push_result_reg == '0   &&
                po_share0_o[r*REG_SIZE +: REG_SIZE]            == '0   &&
                po_share1_o[r*REG_SIZE +: REG_SIZE]            == '0   &&
                !po_ready_o
            ;endproperty
            assert_abr_splitter_reset_clears_regs: assert property (
                abr_splitter_reset_clears_regs);

            property abr_splitter_zeroize_clears_regs;
                pi_zeroize
            |=>
                abr_splitter.rand_d1[r]                        == '0   &&
                abr_splitter.rand_d2[r]                        == '0   &&
                abr_splitter.share1_coeff_reg[r]               == '0   &&
                abr_splitter.gen_lane[r].u_sub.r0_reg          == '0   &&
                abr_splitter.gen_lane[r].u_sub.carry0_reg      == 1'b0 &&
                abr_splitter.gen_lane[r].u_sub.sub_n           == 1'b0 &&
                abr_splitter.gen_lane[r].u_sub.opb1            == '0   &&
                abr_splitter.gen_lane[r].u_sub.push_result_reg == '0   &&
                po_share0_o[r*REG_SIZE +: REG_SIZE]            == '0   &&
                po_share1_o[r*REG_SIZE +: REG_SIZE]            == '0   &&
                !po_ready_o
            ;endproperty
            assert_abr_splitter_zeroize_clears_regs: assert property (
                abr_splitter_zeroize_clears_regs);
        end
    endgenerate


    // ──────────── Input Assertion Integrity ────────────
    generate
        for (i = 0; i < COEFF_PER_CLK; i++) begin : gen_input_contract

            // MldsaDataBit23Zero_A
            property abr_splitter_mldsa_data_bit23_zero;
                (pi_en_i && !pi_mode)
            |->
                pi_data_i[i*REG_SIZE + NTT_REG_SIZE] == 1'b0
            ;endproperty
            assert_abr_splitter_mldsa_data_bit23_zero: assert property (
                disable iff(!pi_reset_n | pi_zeroize) abr_splitter_mldsa_data_bit23_zero);

            // MlkemDataUpperZero_A
            property abr_splitter_mlkem_data_upper_zero;
                (pi_en_i && pi_mode)
            |->
                (pi_data_i[i*REG_SIZE +: REG_SIZE] >> MLKEM_REG_SIZE) == '0
            ;endproperty
            assert_abr_splitter_mlkem_data_upper_zero: assert property (
                disable iff(!pi_reset_n | pi_zeroize) abr_splitter_mlkem_data_upper_zero);

        end
    endgenerate
endmodule


bind abr_splitter fv_abr_splitter_top #(
    //#$bind
) fv_abr_splitter_top_i (
    .pi_clk (clk),
    .pi_reset_n (reset_n),
    .pi_zeroize (zeroize),
    .pi_en_i (en_i),
    .pi_mode (mode),
    .pi_data_i (data_i),
    .pi_rand_i (rand_i),
    .po_share0_o (share0_o),
    .po_share1_o (share1_o),
    .po_ready_o (ready_o)
    //$#//
);
