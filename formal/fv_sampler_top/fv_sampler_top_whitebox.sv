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

//$#//

module fv_sampler_top_whitebox
    //#$imports
    import abr_sampler_pkg::*;
    import abr_sha3_pkg::*;
    import abr_params_pkg::*;
    import abr_prim_alert_pkg::*;
    import fv_sampler_top_pkg::*;
    //$#//
#(
    //#$localparams
    parameter bit SHA3_EN_MASKING = 1,
    localparam int SHA3_SHARE = (SHA3_EN_MASKING) ? 2 : 1,
    parameter SRAM_LATENCY = 1, parameter int ABR_NUM_NTT = 1
    //$#//
) (
    //#$ports
    input logic                                        pi_clk,
    input logic                                        pi_rst_b,
    input logic                                        pi_zeroize,
    input abr_sampler_mode_e                           pi_sampler_mode_i,
    input logic                                        pi_sha3_start_i,
    input logic                                        pi_msg_start_i,
    input logic                                        pi_msg_valid_i,
    input logic                                        po_msg_rdy_o,
    input logic [MsgStrbW-1:0]                         pi_msg_strobe_i,
    input logic [MsgWidth-1:0]                         pi_msg_data_i[SHA3_SHARE],
    input logic                                        pi_sampler_start_i,
    input logic [ABR_MEM_ADDR_WIDTH-1:0]               pi_dest_base_addr_i,
    input mem_if_t                                     pi_sib_mem_rd_req_i,
    input logic [ABR_MEM_DATA_WIDTH-1:0]               po_sib_mem_rd_data_o,
    input logic                                        po_sampler_busy_o,
    input logic                                        po_sampler_ntt_dv_o,
    input logic [COEFF_PER_CLK-1:0][MLDSA_Q_WIDTH-1:0] po_sampler_ntt_data_o,
    input logic                                        po_sampler_mem_dv_o,
    input logic [ABR_MEM_DATA_WIDTH-1:0]               po_sampler_mem_data_o[ABR_NUM_NTT],
    input logic [ABR_MEM_ADDR_WIDTH-1:0]               po_sampler_mem_addr_o,
    input logic                                        pi_split_en_i,
    input logic [ABR_MEM_DATA_WIDTH-1:0]               pi_rand_i,
    input logic                                        pi_sha3_masked_i,
    input logic                                        pi_keccak_rand_valid_i,
    input logic                                        pi_keccak_rand_early_i,
    input logic [abr_sha3_pkg::StateW/2-1:0]           pi_keccak_rand_data_i,
    input logic                                        pi_keccak_rand_aux_i,
    input logic                                        po_sampler_state_dv_o,
    input logic [abr_sha3_pkg::StateW-1:0]             po_sampler_state_data_o//[SHA3_SHARE]
    //$#//
);


    default clocking default_clk @(posedge pi_clk);
    endclocking

    logic fv_splitter_mode; // 0 = MLDSA, 1 = MLKEM
    logic [23:0] fv_prime;
    logic [ABR_MEM_DATA_WIDTH-1:0] fv_splite_share0;
    logic [ABR_MEM_DATA_WIDTH-1:0] fv_splite_share1;
    logic [COEFF_PER_CLK-1:0][MLDSA_Q_WIDTH-1 : 0] fv_data_coeff;
    logic [COEFF_PER_CLK-1:0][MLDSA_Q_WIDTH-1 : 0] fv_rand_coeff;
    logic [COEFF_PER_CLK-1:0][MLDSA_Q_WIDTH-1 : 0] fv_rand_raw;
    logic [COEFF_PER_CLK-1:0][MLDSA_Q_WIDTH-1 : 0] fv_rand;
    logic [COEFF_PER_CLK-1:0][MLDSA_Q_WIDTH-1 : 0] fv_share1_next;
    logic [COEFF_PER_CLK-1:0][MLDSA_Q_WIDTH-1 : 0] fv_share1_coeff;

    // *********************************************** aux_code splitter ********************************************************************
    assign fv_splitter_mode = (pi_sampler_mode_i == ABR_CBD_SAMPLER);
    assign fv_prime = fv_splitter_mode ? MLDSA_Q_WIDTH'(MLKEM_Q) : MLDSA_Q_WIDTH'(MLDSA_Q);

    generate
        for (genvar i = 0; i < COEFF_PER_CLK; i++) begin : gen_fv_splitter

            assign fv_data_coeff[i] = abr_sampler_top.sampler_mem_data_pre[i][MLDSA_Q_WIDTH-2 : 0];
            assign fv_rand_coeff[i] = pi_rand_i[i * MLDSA_Q_WIDTH +: (MLDSA_Q_WIDTH - 1)];

            assign fv_rand_raw[i] = fv_splitter_mode ? {{(MLDSA_Q_WIDTH - MLKEM_REG_SIZE){1'b0}}, fv_rand_coeff[i][MLKEM_REG_SIZE-1 : 0]} : fv_rand_coeff[i];

            // it should in the range of [0, q-1], so if it is greater than or equal to q, we subtract q from it
            assign fv_rand[i] = (fv_rand_raw[i] >= fv_prime) ? (fv_rand_raw[i] - fv_prime) : fv_rand_raw[i];

            // Pack back into the flat word.
            assign fv_splite_share0[i * REG_SIZE +: REG_SIZE] = {0, fv_rand[i]};

            // share1 = (data - rand) mod Q -- a plain statement of the reconstruction
            // spec (share0 + share1 == data, mod Q), independent of how the DUT's
            // internal adder/carry pipeline happens to implement that subtraction.
            assign fv_share1_next[i] = (fv_data_coeff[i] >= fv_rand[i])
                ? (fv_data_coeff[i] - fv_rand[i])
                : (fv_data_coeff[i] + fv_prime - fv_rand[i]);

            assign fv_splite_share1[i * REG_SIZE +: REG_SIZE] = {1'b0, fv_share1_coeff[i]};
        end

    endgenerate

    // Held on splitter_en, otherwise stable -- a real register, not a
    // self-referencing assign.
    always_ff @(posedge pi_clk or negedge pi_rst_b) begin
        if (!pi_rst_b || pi_zeroize) begin
            fv_share1_coeff <= '0;
        end else if (abr_sampler_top.splitter_en) begin
            fv_share1_coeff <= fv_share1_next;
        end
    end

    logic [ABR_MEM_DATA_WIDTH-1:0] fv_share0_d1, fv_share0_d2, fv_share1_d;
    logic fv_split_ready;
    logic fv_split_ready_d1, fv_split_ready_d2;
    always_ff @(posedge pi_clk or negedge pi_rst_b) begin
    if (!pi_rst_b || pi_zeroize) begin
        fv_share0_d1 <= '0;
        fv_share1_d <= '0;
        fv_share0_d2 <= '0;
        fv_split_ready_d1 <= 1'b0;
        fv_split_ready_d2 <= 1'b0;
    end else begin
        fv_share0_d1 <= fv_splite_share0;
        fv_share1_d  <= fv_splite_share1;
        fv_share0_d2 <= fv_share0_d1;
        fv_split_ready_d1 <= abr_sampler_top.splitter_en;
        fv_split_ready_d2 <= fv_split_ready_d1;
    end
end

    // logic fv_sampler_mem_dv_o;
    // always_comb begin
    //     fv_sampler_mem_dv_o = (pi_split_en_i) ? abr_sampler_top.splitter_en : abr_sampler_top.sampler_mem_dv_pre;
    // end
/*
    //************************************************************************end *************************************************

    // Push  : fires the cycle a new pre-split coefficient/address is produced (before the splitter/output mux).
    // Pop   : fires the cycle the DUT actually presents the corresponding value on the output port
    //         (same cycle as push when pi_split_en_i==0 - bypass, or 2 cycles later when pi_split_en_i==1 -
    //         through abr_splitter's fixed 2-cycle pipeline). The scoreboard's own FIFO/tracking logic
    //         accounts for however many cycles separate push from pop, so no manual delay chain is needed here.
    logic fv_sb_push;
    // assign fv_sb_push = fv_sampler_mem_dv_o;

    logic fv_sb_pop;
    assign fv_sb_pop = po_sampler_mem_dv_o;

    logic [ABR_MEM_DATA_WIDTH-1:0] fv_sb_data0_exp;
    assign fv_sb_data0_exp = (pi_split_en_i) ? fv_splite_share0 : abr_sampler_top.sampler_mem_data_pre;

    logic [ABR_MEM_DATA_WIDTH-1:0] fv_sb_data1_exp;
    assign fv_sb_data1_exp = (pi_split_en_i) ? fv_splite_share1 : abr_sampler_top.sampler_mem_data_pre;


    // -- scoreboard: sampler_mem_data_o[0] (share0 / bypass) --
    logic [ABR_MEM_DATA_WIDTH-1:0] fv_sb_data0_sym;
    logic [1:0] fv_sb_data0_cnt;
    logic fv_sb_data0_empty;
    assign fv_sb_data0_empty = (fv_sb_data0_cnt == '0);
    lubis_scoreboard#(
        .BYPASS(1),
        .DATA_WIDTH(ABR_MEM_DATA_WIDTH),
        .DEPTH(2)
    ) fv_sampler_data0_sb(
        .clk(pi_clk),
        .rst(!pi_rst_b || pi_zeroize),
        .soft_rst(1'b0),
        .push(fv_sb_push),
        .pop(fv_sb_pop),
        .full(1'b0),
        .empty(fv_sb_data0_empty),
        .data_in(fv_sb_data0_exp),
        .data_out(po_sampler_mem_data_o[0]),
        .expected_data(fv_sb_data0_sym),
        .incr_val(1'h1),
        .sampled_in(),
        .sampled_in_reg(),
        .sampled_out(),
        .sampled_out_reg(),
        .chosen_symbolic_data(fv_sb_data0_sym),
        .tracking_counter_out(fv_sb_data0_cnt)
    );

    // -- scoreboard: sampler_mem_data_o[1] (share1), only when a second NTT/share output exists --
    generate if (ABR_NUM_NTT > 1) begin : gen_fv_sampler_data1_sb
            logic [ABR_MEM_DATA_WIDTH-1:0] fv_sb_data1_sym;
            logic [1:0] fv_sb_data1_cnt;
            logic fv_sb_data1_empty;
            assign fv_sb_data1_empty = (fv_sb_data1_cnt == '0);
            lubis_scoreboard#(
                .BYPASS(1),
                .DATA_WIDTH(ABR_MEM_DATA_WIDTH),
                .DEPTH(2)
            ) fv_sampler_data1_sb(
                .clk(pi_clk),
                .rst(!pi_rst_b || pi_zeroize),
                .soft_rst(1'b0),
                .push(fv_sb_push),
                .pop(fv_sb_pop),
                .full(1'b0),
                .empty(fv_sb_data1_empty),
                .data_in(fv_sb_data1_exp),
                .data_out(po_sampler_mem_data_o[1]),
                .expected_data(fv_sb_data1_sym),
                .incr_val(1'h1),
                .sampled_in(),
                .sampled_in_reg(),
                .sampled_out(),
                .sampled_out_reg(),
                .chosen_symbolic_data(fv_sb_data1_sym),
                .tracking_counter_out(fv_sb_data1_cnt)
            );
        end
    endgenerate
    // *********************************************** aux_code scoreboard end *************************************************
    */

    logic [COEFF_PER_CLK-1:0][MLDSA_Q_WIDTH-1 : 0] fv_sib_mem_rd_data_o;
    always_comb begin
        for (int i = 0; i < 4; i++) begin
            unique case (abr_sampler_top.sib_mem_rddata[0][i]) inside
                2'b00: fv_sib_mem_rd_data_o[i] = 0;
                2'b01: fv_sib_mem_rd_data_o[i] = 1;
                2'b11: fv_sib_mem_rd_data_o[i] = MLDSA_Q - 1;
                default: fv_sib_mem_rd_data_o[i] = '0;
            endcase
        end
    end

    // Checks the case, when no mode has been selected and the signals are reset accordingly
    property mode_mux_NONE_p;
        pi_sampler_mode_i == ABR_SAMPLER_NONE
    |->
        abr_sampler_top.mode == abr_sha3_pkg::Shake &&
        abr_sampler_top.strength == abr_sha3_pkg::L256 &&
        abr_sampler_top.vld_cycle == 0 &&
        abr_sampler_top.sampler_done == 0 &&
        po_sampler_mem_dv_o == 0 &&
        (!po_sampler_mem_dv_o || po_sampler_mem_data_o[0] == (pi_split_en_i ? fv_share0_d2 : 0)) &&
        (!po_sampler_mem_dv_o || po_sampler_mem_data_o[1] == (pi_split_en_i ? fv_share1_d : 0)) &&
        (po_sampler_mem_addr_o == (pi_split_en_i ? $past(abr_sampler_top.sampler_mem_addr_pre, 2) : 0)) &&
        po_sampler_state_dv_o == 0 &&
        po_sampler_state_data_o == 0 && //[0]

        abr_sampler_top.zeroize_rejb == pi_zeroize &&
        abr_sampler_top.zeroize_mldsa_rejs == pi_zeroize &&
        abr_sampler_top.zeroize_exp_mask == pi_zeroize &&
        abr_sampler_top.zeroize_sib == pi_zeroize &&
        abr_sampler_top.zeroize_sib_mem == pi_zeroize &&
        abr_sampler_top.zeroize_sha3 == pi_zeroize &&
        abr_sampler_top.zeroize_piso == pi_zeroize &&
        abr_sampler_top.piso_mode == 0
        ;
    endproperty
    a_mode_mux_none: assert property (disable iff (!pi_rst_b) mode_mux_NONE_p);

    // Checks the case, when SHAKE256 mode has been selected and the signals are set according to the mode
    property mode_mux_SHAKE256_p;
        pi_sampler_mode_i == ABR_SHAKE256
    |->
        abr_sampler_top.mode == abr_sha3_pkg::Shake &&
        abr_sampler_top.strength == abr_sha3_pkg::L256 &&
        abr_sampler_top.sampler_done == abr_sampler_top.sha3_state_dv &&

        po_sampler_state_dv_o == abr_sampler_top.sha3_state_dv &&
        po_sampler_state_data_o == abr_sampler_top.sha3_state && //[0]  [0]

        abr_sampler_top.zeroize_sha3 == abr_sampler_top.sha3_state_dv
        ;
    endproperty
    a_mode_mux_shake256: assert property (disable iff (!pi_rst_b) mode_mux_SHAKE256_p);

    // Checks the case, when SHAKE128 mode has been selected and the signals are set according to the mode
    property mode_mux_SHAKE128_p;
        pi_sampler_mode_i == ABR_SHAKE128
    |->
        abr_sampler_top.mode == abr_sha3_pkg::Shake &&
        abr_sampler_top.strength == abr_sha3_pkg::L128 &&
        abr_sampler_top.sampler_done == abr_sampler_top.sha3_state_dv &&

        po_sampler_state_dv_o == abr_sampler_top.sha3_state_dv &&
        po_sampler_state_data_o == abr_sampler_top.sha3_state && //[0]  [0]

        abr_sampler_top.zeroize_sha3 == abr_sampler_top.sha3_state_dv;
    endproperty
    a_mode_mux_shake128: assert property (disable iff (!pi_rst_b) mode_mux_SHAKE128_p);

    // Checks the case, when SHA512 mode has been selected and the signals are set according to the mode
    property mode_mux_SHA512_p;
        pi_sampler_mode_i == ABR_SHA512
    |->
        abr_sampler_top.mode == abr_sha3_pkg::Sha3 &&
        abr_sampler_top.strength == abr_sha3_pkg::L512 &&
        abr_sampler_top.sampler_done == abr_sampler_top.sha3_state_dv &&

        po_sampler_state_dv_o == abr_sampler_top.sha3_state_dv &&
        po_sampler_state_data_o == abr_sampler_top.sha3_state && //[0]  [0]

        abr_sampler_top.zeroize_sha3 == abr_sampler_top.sha3_state_dv
        ;
    endproperty
    a_mode_mux_sha512: assert property (disable iff (!pi_rst_b) mode_mux_SHA512_p);


    // Checks the case, when SHA256 mode has been selected and the signals are set according to the mode
    property mode_mux_SHA256_p;
        pi_sampler_mode_i == ABR_SHA256
    |->
        abr_sampler_top.mode == abr_sha3_pkg::Sha3 &&
        abr_sampler_top.strength == abr_sha3_pkg::L256 &&
        abr_sampler_top.sampler_done == abr_sampler_top.sha3_state_dv &&

        po_sampler_state_dv_o == abr_sampler_top.sha3_state_dv &&
        po_sampler_state_data_o == abr_sampler_top.sha3_state && //[0]  [0]

        abr_sampler_top.zeroize_sha3 == abr_sampler_top.sha3_state_dv
        ;
    endproperty
    a_mode_mux_sha256: assert property (disable iff (!pi_rst_b) mode_mux_SHA256_p);

    // Checks the case, when REJ_SAMPLER mode has been selected and the signals are set according to the mode
    property mode_mux_REJ_SAMPLER_MLDSA_p;
        pi_sampler_mode_i == MLDSA_REJ_SAMPLER
    |->
        abr_sampler_top.mode == abr_sha3_pkg::Shake &&
        abr_sampler_top.strength == abr_sha3_pkg::L128 &&
        abr_sampler_top.vld_cycle == abr_sampler_top.mldsa_rejs_dv &&
        abr_sampler_top.sampler_done == (abr_sampler_top.coeff_cnt == (ABR_COEFF_CNT / 4)) &&

        abr_sampler_top.zeroize_mldsa_rejs == abr_sampler_top.zeroize_mldsa_rejs | abr_sampler_top.sampler_done &&
        abr_sampler_top.zeroize_sha3 == abr_sampler_top.zeroize_sha3 | abr_sampler_top.sampler_done &&
        abr_sampler_top.zeroize_piso == abr_sampler_top.zeroize_piso | abr_sampler_top.sampler_done &&
        abr_sampler_top.piso_mode == 0
        ;
    endproperty
    a_mode_mux_rej_sampler_mldsa: assert property (disable iff (!pi_rst_b) mode_mux_REJ_SAMPLER_MLDSA_p);

    // Checks the case, when REJ_SAMPLER mode has been selected and the signals are set according to the mode
    property mode_mux_REJ_SAMPLER_MLKEM_p;
        pi_sampler_mode_i == MLKEM_REJ_SAMPLER
    |->
        abr_sampler_top.mode == abr_sha3_pkg::Shake &&
        abr_sampler_top.strength == abr_sha3_pkg::L128 &&
        abr_sampler_top.vld_cycle == abr_sampler_top.mlkem_rejs_dv &&
        abr_sampler_top.sampler_done == (abr_sampler_top.coeff_cnt == (ABR_COEFF_CNT / 4)) &&

        abr_sampler_top.zeroize_mlkem_rejs == abr_sampler_top.zeroize_mlkem_rejs | abr_sampler_top.sampler_done &&
        abr_sampler_top.zeroize_sha3 == abr_sampler_top.zeroize_sha3 | abr_sampler_top.sampler_done &&
        abr_sampler_top.zeroize_piso == abr_sampler_top.zeroize_piso | abr_sampler_top.sampler_done &&
        abr_sampler_top.piso_mode == 0
        ;
    endproperty
    a_mode_mux_rej_sampler_mlkem: assert property (disable iff (!pi_rst_b) mode_mux_REJ_SAMPLER_MLKEM_p);


    // Checks the case, when EXP_MASK mode has been selected and the signals are set according to the mode
    property mode_mux_EXP_MASK_p;
        pi_sampler_mode_i == ABR_EXP_MASK
    |->
        abr_sampler_top.mode == abr_sha3_pkg::Shake &&
        abr_sampler_top.strength == abr_sha3_pkg::L256 &&
        abr_sampler_top.vld_cycle == abr_sampler_top.exp_dv &&
        abr_sampler_top.sampler_done == (abr_sampler_top.coeff_cnt == (ABR_COEFF_CNT / 4)) &&

        po_sampler_mem_dv_o == (pi_split_en_i ? fv_split_ready_d2 : abr_sampler_top.exp_dv) &&
        (!po_sampler_mem_dv_o || po_sampler_mem_data_o[0] == (pi_split_en_i ? fv_share0_d2 : abr_sampler_top.exp_data)) &&
        (!po_sampler_mem_dv_o || po_sampler_mem_data_o[1] == (pi_split_en_i ? fv_share1_d : abr_sampler_top.exp_data)) &&
        po_sampler_mem_addr_o == (pi_split_en_i ? $past(abr_sampler_top.sampler_mem_addr_pre, 2) : abr_sampler_top.dest_addr) &&

        abr_sampler_top.zeroize_exp_mask == abr_sampler_top.zeroize_exp_mask | abr_sampler_top.sampler_done &&
        abr_sampler_top.zeroize_sha3 == abr_sampler_top.zeroize_sha3 | abr_sampler_top.sampler_done &&
        abr_sampler_top.zeroize_piso == abr_sampler_top.zeroize_piso | abr_sampler_top.sampler_done &&
        abr_sampler_top.piso_mode == 2
        ;
    endproperty
    a_mode_mux_exp_mask: assert property (disable iff (!pi_rst_b) mode_mux_EXP_MASK_p);

    // Checks the case, when REJ_BOUNDED mode has been selected and the signals are set according to the mode
    property mode_mux_REJ_BOUNDED_p;
        pi_sampler_mode_i == ABR_REJ_BOUNDED
    |->
        abr_sampler_top.mode == abr_sha3_pkg::Shake &&
        abr_sampler_top.strength == abr_sha3_pkg::L256 &&
        abr_sampler_top.vld_cycle == abr_sampler_top.rejb_dv &&
        abr_sampler_top.sampler_done == (abr_sampler_top.coeff_cnt == (ABR_COEFF_CNT / 4)) &&
        po_sampler_mem_dv_o == (pi_split_en_i ? fv_split_ready_d2 : abr_sampler_top.rejb_dv) &&
        (!po_sampler_mem_dv_o || po_sampler_mem_data_o[0] == (pi_split_en_i ? fv_share0_d2 : abr_sampler_top.rejb_data)) &&
        (!po_sampler_mem_dv_o || po_sampler_mem_data_o[1] == (pi_split_en_i ? fv_share1_d : abr_sampler_top.rejb_data)) &&
        po_sampler_mem_addr_o == (pi_split_en_i ? $past(abr_sampler_top.sampler_mem_addr_pre, 2) : abr_sampler_top.dest_addr) &&

        abr_sampler_top.zeroize_rejb == abr_sampler_top.zeroize_rejb | abr_sampler_top.sampler_done &&
        abr_sampler_top.zeroize_sha3 == abr_sampler_top.zeroize_sha3 | abr_sampler_top.sampler_done &&
        abr_sampler_top.zeroize_piso == abr_sampler_top.zeroize_piso | abr_sampler_top.sampler_done &&
        abr_sampler_top.piso_mode == 1
        ;
    endproperty
    a_mode_mux_rej_bounded: assert property (disable iff (!pi_rst_b) mode_mux_REJ_BOUNDED_p);

    // Checks the case, when SAMPLER_IN_BALL mode has been selected and the signals are set according to the mode
    property mode_mux_SAMPLE_IN_BALL_p;
        pi_sampler_mode_i == ABR_SAMPLE_IN_BALL
    |->
        abr_sampler_top.mode == abr_sha3_pkg::Shake &&
        abr_sampler_top.strength == abr_sha3_pkg::L256 &&
        abr_sampler_top.sampler_done == abr_sampler_top.sib_done &&

        abr_sampler_top.zeroize_sib_mem == pi_sampler_start_i &&
        abr_sampler_top.zeroize_sib == abr_sampler_top.zeroize_sib | abr_sampler_top.sampler_done &&
        abr_sampler_top.zeroize_sha3 == abr_sampler_top.zeroize_sha3 | abr_sampler_top.sampler_done &&
        abr_sampler_top.zeroize_piso == abr_sampler_top.zeroize_piso | abr_sampler_top.sampler_done &&
        abr_sampler_top.piso_mode == 3
        ;
    endproperty
    a_mode_mux_sample_in_ball: assert property (disable iff (!pi_rst_b) mode_mux_SAMPLE_IN_BALL_p);

    // Checks the case, when ABR_CBD_SAMPLER mode has been selected and the signals are set according to the mode
    logic [$clog2(COEFF_PER_CLK+1)-1:0] fv_cbd_coeff_index;
    assume property (##1 $stable(fv_cbd_coeff_index));
    assume property (fv_cbd_coeff_index < COEFF_PER_CLK);
    logic [COEFF_PER_CLK-1:0][MLDSA_Q_WIDTH-1:0] fv_sampler_cbd_data;

    generate
        for (genvar i = 0; i < COEFF_PER_CLK; i++) begin : gen_cbd_data
            assign fv_sampler_cbd_data[i] = {12'b0, abr_sampler_top.cbd_data[i]};
        end
    endgenerate


    property mode_mux_ABR_CBD_SAMPLER_p;
        pi_sampler_mode_i == ABR_CBD_SAMPLER
    |->
        abr_sampler_top.mode == abr_sha3_pkg::Shake &&
        abr_sampler_top.strength == abr_sha3_pkg::L256 &&
        abr_sampler_top.vld_cycle == abr_sampler_top.cbd_dv &&
        abr_sampler_top.sampler_done == (abr_sampler_top.coeff_cnt == (ABR_COEFF_CNT / 4)) &&
        po_sampler_mem_dv_o == (pi_split_en_i ? fv_split_ready_d2 : abr_sampler_top.cbd_dv) &&
        //po_sampler_mem_data_o[cbd_coeff_index][MLKEM_Q_WIDTH-1:0] == abr_sampler_top.cbd_data[cbd_coeff_index] &&
        (!po_sampler_mem_dv_o || po_sampler_mem_data_o[0] == (pi_split_en_i ? fv_share0_d2 : fv_sampler_cbd_data)) &&
        (!po_sampler_mem_dv_o || po_sampler_mem_data_o[1] == (pi_split_en_i ? fv_share1_d : fv_sampler_cbd_data)) &&
        po_sampler_mem_addr_o == (pi_split_en_i ? $past(abr_sampler_top.sampler_mem_addr_pre, 2) : abr_sampler_top.dest_addr) &&

        abr_sampler_top.zeroize_cbd == abr_sampler_top.zeroize_cbd | abr_sampler_top.sampler_done &&
        abr_sampler_top.zeroize_sha3 == abr_sampler_top.zeroize_sha3 | abr_sampler_top.sampler_done &&
        abr_sampler_top.zeroize_piso == abr_sampler_top.zeroize_piso | abr_sampler_top.sampler_done &&
        abr_sampler_top.piso_mode == ABR_CBD_MODE
        ;
    endproperty
    a_mode_mux_abr_cbd_sampler: assert property (disable iff (!pi_rst_b) mode_mux_ABR_CBD_SAMPLER_p);

    // Checks if in case of a data_hold signal from REJ_BOUNDED and data valid input signal, the PISO buffer keeps its output data and data valid signal stable.
    property register_REJ_BOUNDED_vld_hld_p;
        abr_sampler_top.rejb_piso_dv &&
        abr_sampler_top.rejb_piso_hold &&
        !abr_sampler_top.sampler_done
    |->
        ##1
        $stable(abr_sampler_top.rejb_piso_data) &&
        abr_sampler_top.rejb_piso_dv;
    endproperty
    a_register_rej_bounded_vld_hld: assert property (disable iff (!pi_rst_b || pi_zeroize) register_REJ_BOUNDED_vld_hld_p);

    // Checks if in case of a data_hold signal from REJ_SAMPLER and data valid input signal, the PISO buffer keeps its output data and data valid signal stable.
    property register_REJ_SAMPLER_vld_hld_p;
        abr_sampler_top.mldsa_rejs_piso_dv &&
        abr_sampler_top.mldsa_rejs_piso_hold &&
        !abr_sampler_top.sampler_done
    |->
        ##1
        $stable(abr_sampler_top.rejs_piso_data) &&
        abr_sampler_top.mldsa_rejs_piso_dv;
    endproperty
    a_register_rej_sampler_vld_hld: assert property (disable iff (!pi_rst_b || pi_zeroize) register_REJ_SAMPLER_vld_hld_p);


    // Checks if in case of a data_hold signal from SAMPLER_IN_BALL and data valid input signal, the PISO buffer keeps its output data and data valid signal stable.
    property register_SAMPLE_IN_BALL_CTRL_vld_hld_p;
        abr_sampler_top.sib_piso_dv &&
        abr_sampler_top.sib_piso_hold &&
        !abr_sampler_top.sampler_done
    |->
        ##1
        $stable(abr_sampler_top.sib_piso_data) &&
        abr_sampler_top.sib_piso_dv;
    endproperty
    a_register_sample_in_ball_ctrl_vld_hld: assert property (disable iff (!pi_rst_b || pi_zeroize) register_SAMPLE_IN_BALL_CTRL_vld_hld_p);

    // Helper lemma for a_register_sample_in_ball_ctrl_vld_hld.
    //
    // piso_hold is an OR of six mode-gated terms (abr_sampler_top.sv:542-547):
    // ((sampler_mode_i==ABR_SAMPLE_IN_BALL) & sib_piso_hold) is only one of
    // them, so sib_piso_hold alone does NOT imply piso_hold -- if sib_piso_hold
    // ever reads 1 while sampler_mode_i has moved to a different mode (nothing
    // in sample_in_ball_ctrl.sv resets its data_hold_o just because the mode
    // changed), that OR term drops out and piso_hold can legitimately be 0.
    // Scoped with sib_piso_dv instead, which already pins sampler_mode_i ==
    // ABR_SAMPLE_IN_BALL by its own definition (line 539) -- exactly the same
    // context the target property's antecedent guarantees -- so this is
    // purely combinational and true, and proves near-instantly.
    property sib_piso_hold_implies_piso_hold_p;
        abr_sampler_top.sib_piso_dv && abr_sampler_top.sib_piso_hold
    |->
        abr_sampler_top.piso_hold;
    endproperty
    a_sib_piso_hold_implies_piso_hold: assert property (disable iff (!pi_rst_b || pi_zeroize) sib_piso_hold_implies_piso_hold_p);

    // Checks that the piso_dv signal is asserted and stays asserted until the sampler is done.
    property register_SAMPLE_IN_BALL_CTRL_vld_stable_p;
        abr_sampler_top.sib_piso_dv
    |->
        abr_sampler_top.sib_piso_dv s_until abr_sampler_top.sampler_done;
    endproperty
    a_register_sample_in_ball_ctrl_vld_stable: assert property (disable iff (!pi_rst_b || pi_zeroize) register_SAMPLE_IN_BALL_CTRL_vld_stable_p);


    // Checks if there is no data incoming, the design can expect valid data in the future.
    property register_PISO_BITS_p;
        abr_sampler_top.abr_piso_inst.buffer_wr_ptr < abr_sampler_top.abr_piso_inst.PISO_ACT_OUTPUT_RATE &&
        !abr_sampler_top.sampler_done &&
        pi_sampler_mode_i inside {MLDSA_REJ_SAMPLER, MLKEM_REJ_SAMPLER, ABR_REJ_BOUNDED, ABR_EXP_MASK, ABR_SAMPLE_IN_BALL}
    |->
        s_eventually(abr_sampler_top.sha3_state_dv);
    endproperty
    a_register_piso_bits: assert property (disable iff (!pi_rst_b || pi_zeroize) register_PISO_BITS_p);
    // Checks if the piso hold signal is asserted correctly, based on the mode and sampler hold signals
    property signal_PISO_HOLD_p;
        abr_sampler_top.piso_hold == (((pi_sampler_mode_i == MLDSA_REJ_SAMPLER) & abr_sampler_top.mldsa_rejs_piso_hold) |
            ((pi_sampler_mode_i == MLKEM_REJ_SAMPLER) & abr_sampler_top.mlkem_rejs_piso_hold) |
            ((pi_sampler_mode_i == ABR_REJ_BOUNDED) & (abr_sampler_top.rejb_piso_hold | abr_sampler_top.rejb_hold_active)) |
            ((pi_sampler_mode_i == ABR_EXP_MASK) & abr_sampler_top.exp_piso_hold) |
            ((pi_sampler_mode_i == ABR_SAMPLE_IN_BALL) & abr_sampler_top.sib_piso_hold) |
            ((pi_sampler_mode_i == ABR_CBD_SAMPLER) & abr_sampler_top.cbd_piso_hold));
    endproperty
    a_signal_piso_hold: assert property (disable iff (!pi_rst_b || pi_zeroize) signal_PISO_HOLD_p);

    // Checks if REJ_SAMPLER data valid signals are asserted correctly, based on the mode and the piso data valid signal.
    property signal_REJS_PISO_DV_p;
        abr_sampler_top.mldsa_rejs_piso_dv == ((pi_sampler_mode_i == MLDSA_REJ_SAMPLER) & abr_sampler_top.piso_dv);
    endproperty
    a_signal_rejs_piso_dv: assert property (disable iff (!pi_rst_b || pi_zeroize) signal_REJS_PISO_DV_p);

    // Checks if REJ_BOUNDED data valid signals are asserted correctly, based on the mode and the piso data valid signal.
    property signal_REJB_PISO_DV_p;
        abr_sampler_top.rejb_piso_dv == ((pi_sampler_mode_i == ABR_REJ_BOUNDED) & (abr_sampler_top.piso_dv & ~abr_sampler_top.rejb_hold_active));
    endproperty
    a_signal_rejb_piso_dv: assert property (disable iff (!pi_rst_b || pi_zeroize) signal_REJB_PISO_DV_p);

    // Checks if EXP_MASK data valid signals are asserted correctly, based on the mode and the piso data valid signal.
    property signal_EXP_PISO_DV_p;
        abr_sampler_top.exp_piso_dv == ((pi_sampler_mode_i == ABR_EXP_MASK) & abr_sampler_top.piso_dv);
    endproperty
    a_signal_exp_piso_dv: assert property (disable iff (!pi_rst_b || pi_zeroize) signal_EXP_PISO_DV_p);

    // Checks if EXP_MASK input data is extracted correctly from piso output data
    property signal_EXP_PISO_DATA_p;
        abr_sampler_top.exp_piso_data == abr_sampler_top.piso_data[EXP_PISO_OUTPUT_RATE-1 : 0];

    endproperty
    a_signal_exp_piso_data: assert property (disable iff (!pi_rst_b || pi_zeroize) signal_EXP_PISO_DATA_p);

    // Checks if EXP_MASK input data is extracted correctly from piso output data
    property signal_CBD_PISO_DATA_p;
        abr_sampler_top.cbd_piso_data == abr_sampler_top.piso_data[CBD_PISO_OUTPUT_RATE-1 : 0];

    endproperty
    a_signal_cbd_piso_data: assert property (disable iff (!pi_rst_b || pi_zeroize) signal_CBD_PISO_DATA_p);

    // Checks if SAMPLE_IN_BALL data valid signals are asserted correctly, based on the mode and the piso data valid signal.
    property signal_SIB_PISO_DV_p;
        abr_sampler_top.sib_piso_dv == ((pi_sampler_mode_i == ABR_SAMPLE_IN_BALL) & abr_sampler_top.piso_dv);
    endproperty
    a_signal_sib_piso_dv: assert property (disable iff (!pi_rst_b || pi_zeroize) signal_SIB_PISO_DV_p);

    // Checks that the sampler_busy_o signal is asserted either through sampler_start_i or the sampler_fsm states.
    property signal_SAMPLER_BUSY_p;
        pi_sampler_start_i ||
        (abr_sampler_top.sampler_fsm_ps != abr_sampler_pkg::ABR_SAMPLER_IDLE)
    |->
        po_sampler_busy_o
        ;
    endproperty
    a_signal_sampler_busy: assert property (disable iff (!pi_rst_b || pi_zeroize) signal_SAMPLER_BUSY_p);

    // Checks if the sampler_busy_o signal is also deasserted at one point.
    property liveness_SAMPLER_BUSY_p;
        po_sampler_busy_o
    |->
        s_eventually(!po_sampler_busy_o);
    endproperty
    a_liveness_sampler_busy: assert property (disable iff (!pi_rst_b || pi_zeroize) liveness_SAMPLER_BUSY_p);

    // Complement of signal_SAMPLER_BUSY_p, conditioned on split_en_i=0 so no
    // trailing splitter_ready from the split pipeline can hold busy_o high:
    // sampler_busy_o de-asserts the cycle after the FSM is IDLE and no new
    // start is pending.
    property signal_SAMPLER_BUSY_deassert_p;
        !pi_split_en_i &&
        !pi_sampler_start_i &&
        (abr_sampler_top.sampler_fsm_ps == abr_sampler_pkg::ABR_SAMPLER_IDLE)
    |->
        !po_sampler_busy_o
        ;
    endproperty
    a_signal_sampler_busy_deassert: assert property (disable iff (!pi_rst_b || pi_zeroize) signal_SAMPLER_BUSY_deassert_p);

    // With split_en_i=1 and the FSM idle, sampler_busy_o exactly tracks the split pipeline's splitter_en|splitter_ready (so it drains, not stuck high).
    property signal_SAMPLER_BUSY_split_drain_p;
        pi_split_en_i &&
        !pi_sampler_start_i &&
        (abr_sampler_top.sampler_fsm_ps == abr_sampler_pkg::ABR_SAMPLER_IDLE)
    |->
        po_sampler_busy_o == (abr_sampler_top.splitter_en | abr_sampler_top.splitter_ready)
        ;
    endproperty
    a_signal_sampler_busy_split_drain: assert property (disable iff (!pi_rst_b || pi_zeroize) signal_SAMPLER_BUSY_split_drain_p);

    // Busy covers the splitter drain: while split_en_i=1, sampler_busy_o
    // cannot de-assert before splitter_ready has -- busy_o is never seen low
    // while a splitter_ready pulse is still outstanding.
    property signal_SAMPLER_BUSY_covers_ready_p;
        pi_split_en_i &&
        abr_sampler_top.splitter_ready
    |->
        po_sampler_busy_o
        ;
    endproperty
    a_signal_sampler_busy_covers_ready: assert property (disable iff (!pi_rst_b || pi_zeroize) signal_SAMPLER_BUSY_covers_ready_p);

    // Checks that sampler_ntt_dv_o represents the data valid signal from REJ_SAMPLER.
    property signal_SAMPLER_NTT_DV_p;
        po_sampler_ntt_dv_o == abr_sampler_top.mldsa_rejs_dv | abr_sampler_top.mlkem_rejs_dv
        ;
    endproperty
    a_signal_sampler_ntt_dv: assert property (disable iff (!pi_rst_b || pi_zeroize) signal_SAMPLER_NTT_DV_p);

    //  Checks that sampler_ntt_data_o represents the output data from REJ_SAMPLER.
    property signal_SAMPLER_NTT_DATA_MLDSA_p;
        abr_sampler_top.sampler_mode_i == MLDSA_REJ_SAMPLER
    |=>
        po_sampler_ntt_data_o[fv_cbd_coeff_index] == $past(abr_sampler_top.mldsa_rejs_data_q[fv_cbd_coeff_index]);
    endproperty
    a_signal_sampler_ntt_data_mldsa: assert property (disable iff (!pi_rst_b || pi_zeroize) signal_SAMPLER_NTT_DATA_MLDSA_p);

    property signal_SAMPLER_NTT_DATA_MLKEM_p;
        abr_sampler_top.sampler_mode_i == MLKEM_REJ_SAMPLER
    |=>
        po_sampler_ntt_data_o[fv_cbd_coeff_index] == $past(abr_sampler_top.mlkem_rejs_data_q[fv_cbd_coeff_index]);
    endproperty
    a_signal_sampler_ntt_data_mlkem: assert property (disable iff (!pi_rst_b || pi_zeroize) signal_SAMPLER_NTT_DATA_MLKEM_p);

    // Checks that sib_mem_cs_mux is assigned correctly.
    property signal_SIB_MEM_CS_MUX_p;
        abr_sampler_top.sib_mem_cs_mux[0] == ((pi_sib_mem_rd_req_i.rd_wr_en == RW_READ) | abr_sampler_top.sib_mem_cs[0]) &&
        abr_sampler_top.sib_mem_cs_mux[1] == abr_sampler_top.sib_mem_cs[1]
        ;
    endproperty
    a_signal_sib_mem_cs_mux: assert property (disable iff (!pi_rst_b || pi_zeroize) signal_SIB_MEM_CS_MUX_p);

    // Checks that sib_mem_addr_mux is assigned correctly.
    property signal_SIB_MEM_ADDR_MUX_p;
        abr_sampler_top.sib_mem_addr_mux[0] == ((pi_sib_mem_rd_req_i.rd_wr_en == RW_READ) ? pi_sib_mem_rd_req_i.addr[5 : 0] : abr_sampler_top.sib_mem_addr[0]) &&
        abr_sampler_top.sib_mem_addr_mux[1] == abr_sampler_top.sib_mem_addr[1]
        ;
    endproperty
    a_signal_sib_mem_addr_mux: assert property (disable iff (!pi_rst_b || pi_zeroize) signal_SIB_MEM_ADDR_MUX_p);

    // Checks that sib_mem_rd_data is assigned correctly.
    property signal_SIB_MEM_RD_DATA_p;
        po_sib_mem_rd_data_o == fv_sib_mem_rd_data_o //{1'b0,abr_sampler_top.sib_mem_rddata[0][3],1'b0,abr_sampler_top.sib_mem_rddata[0][2],1'b0,abr_sampler_top.sib_mem_rddata[0][1],1'b0,abr_sampler_top.sib_mem_rddata[0][0]}
        ;
    endproperty
    a_signal_sib_mem_rd_data: assert property (disable iff (!pi_rst_b || pi_zeroize) signal_SIB_MEM_RD_DATA_p);

    // Checks that rejs_data is delayed by one clock cycle.
    //property signal_REJS_DATA_p;
    //    $past(abr_sampler_top.mldsa_rejs_data_q) == abr_sampler_top.rejs_data
    //;
    //endproperty
    //signal_REJS_DATA_a: assert property(disable iff (!pi_rst_b || pi_zeroize) signal_REJS_DATA_p);

    // Checks, if there is either a sampler_start_i or a sampler_done, the coeff_cnt is set to 0
    property signal_COEFF_CNT_sampler_start_p;
        pi_sampler_start_i || abr_sampler_top.sampler_done
    |=>
        abr_sampler_top.coeff_cnt == 'd0
        ;
    endproperty
    a_signal_coeff_cnt_sampler_start: assert property (disable iff (!pi_rst_b || pi_zeroize) signal_COEFF_CNT_sampler_start_p);

    // Checks, if there is no a sampler_start_i nor a sampler_done, but a vld_cycle, the coeff_cnt increments
    property signal_COEFF_CNT_vld_cycle_p;
        !(pi_sampler_start_i || abr_sampler_top.sampler_done) && abr_sampler_top.vld_cycle
    |=>
        abr_sampler_top.coeff_cnt == $past(abr_sampler_top.coeff_cnt) + 'd1
        ;
    endproperty
    a_signal_coeff_cnt_vld_cycle: assert property (disable iff (!pi_rst_b || pi_zeroize) signal_COEFF_CNT_vld_cycle_p);

    // Checks, if there is no a sampler_start_i, no sampler_done and no vld_cycle, the coeff_cnt stays stable
    property signal_COEFF_CNT_no_vld_cycle_p;
        !(pi_sampler_start_i || abr_sampler_top.sampler_done) && !abr_sampler_top.vld_cycle
    |=>
        abr_sampler_top.coeff_cnt == $past(abr_sampler_top.coeff_cnt);
    endproperty
    a_signal_coeff_cnt_no_vld_cycle: assert property (disable iff (!pi_rst_b || pi_zeroize) signal_COEFF_CNT_no_vld_cycle_p);

    // Checks, if there is either a sampler_done, the dest_addr is set to 0
    property signal_DEST_ADDR_sampler_done_p;
        abr_sampler_top.sampler_done
    |=>
        abr_sampler_top.dest_addr == 'd0
        ;
    endproperty
    a_signal_dest_addr_sampler_done: assert property (disable iff (!pi_rst_b || pi_zeroize) signal_DEST_ADDR_sampler_done_p);

    // Checks, if there is no sampler_done, but a sampler_start_i, the dest_addr is set to dest_base_addr_i
    property signal_DEST_ADDR_sampler_start_p;
        !abr_sampler_top.sampler_done && pi_sampler_start_i
    |=>
        abr_sampler_top.dest_addr == $past(pi_dest_base_addr_i);
    endproperty
    a_signal_dest_addr_sampler_start: assert property (disable iff (!pi_rst_b || pi_zeroize) signal_DEST_ADDR_sampler_start_p);

    // Checks, if there is no sampler_done, no sampler_start_i, but a vld_cycle, the dest_addr increments
    property signal_DEST_ADDR_vld_cycle_p;
        !abr_sampler_top.sampler_done && !pi_sampler_start_i && abr_sampler_top.vld_cycle
    |=>
        abr_sampler_top.dest_addr == 14'($past(abr_sampler_top.dest_addr) + 14'd1);
    endproperty
    a_signal_dest_addr_vld_cycle: assert property (disable iff (!pi_rst_b || pi_zeroize) signal_DEST_ADDR_vld_cycle_p);

    // Checks, if there is no sampler_done, no sampler_start_i and no vld_cycle, the dest_addr stays stable
    property signal_DEST_ADDR_no_vld_cycle_p;
        !abr_sampler_top.sampler_done && !pi_sampler_start_i && !abr_sampler_top.vld_cycle
    |=>
        abr_sampler_top.dest_addr == $past(abr_sampler_top.dest_addr);
    endproperty
    a_signal_dest_addr_no_vld_cycle: assert property (disable iff (!pi_rst_b || pi_zeroize) signal_DEST_ADDR_no_vld_cycle_p);

    // Checks that sha3 output is 0, whenever there is no data valid signal asserted.
    property signal_ABR_SHA3_DATA_p;
        !abr_sampler_top.sha3_state_dv
    |->
        abr_sampler_top.sha3_state == '0 //[0]
        ;
    endproperty
    a_signal_abr_sha3_data: assert property (disable iff (!pi_rst_b || pi_zeroize) signal_ABR_SHA3_DATA_p);

    // Checks that all sequential assigned signals are resetted correctly.
    property signal_reset_p;
        $past(!pi_rst_b || pi_zeroize)
    |->
        abr_sampler_top.dest_addr == 'd0 &&
        abr_sampler_top.coeff_cnt == 'd0 &&
        abr_sampler_top.sampler_fsm_ps == abr_sampler_pkg::ABR_SAMPLER_IDLE &&
        abr_sampler_top.split_addr_d1 == 'd0 &&
        abr_sampler_top.split_addr_d2 == 'd0 &&

        // u_splitter internal registers: rand_d1/d2 (share0 delay chain) and
        // share1_coeff_reg are flat COEFF_PER_CLK-wide arrays declared once at
        // the abr_splitter module level. Assignment-pattern literals ('{default:'0})
        // are not allowed in an SVA equality context, so each lane is compared
        // individually instead.
        abr_sampler_top.u_splitter.rand_d1[0] == 'd0 &&
        abr_sampler_top.u_splitter.rand_d1[1] == 'd0 &&
        abr_sampler_top.u_splitter.rand_d1[2] == 'd0 &&
        abr_sampler_top.u_splitter.rand_d1[3] == 'd0 &&
        abr_sampler_top.u_splitter.rand_d2[0] == 'd0 &&
        abr_sampler_top.u_splitter.rand_d2[1] == 'd0 &&
        abr_sampler_top.u_splitter.rand_d2[2] == 'd0 &&
        abr_sampler_top.u_splitter.rand_d2[3] == 'd0 &&
        abr_sampler_top.u_splitter.share1_coeff_reg[0] == 'd0 &&
        abr_sampler_top.u_splitter.share1_coeff_reg[1] == 'd0 &&
        abr_sampler_top.u_splitter.share1_coeff_reg[2] == 'd0 &&
        abr_sampler_top.u_splitter.share1_coeff_reg[3] == 'd0 &&

        // r0_reg/push_result_reg live inside abr_ntt_add_sub_mod, one instance
        // (u_sub) per gen_lane[i] -- these are separate scoped instances, not a
        // flat array, so each lane needs its own reference.
        abr_sampler_top.u_splitter.gen_lane[0].u_sub.r0_reg == 'd0 &&
        abr_sampler_top.u_splitter.gen_lane[1].u_sub.r0_reg == 'd0 &&
        abr_sampler_top.u_splitter.gen_lane[2].u_sub.r0_reg == 'd0 &&
        abr_sampler_top.u_splitter.gen_lane[3].u_sub.r0_reg == 'd0 &&
        abr_sampler_top.u_splitter.gen_lane[0].u_sub.push_result_reg == '0 &&
        abr_sampler_top.u_splitter.gen_lane[1].u_sub.push_result_reg == '0 &&
        abr_sampler_top.u_splitter.gen_lane[2].u_sub.push_result_reg == '0 &&
        abr_sampler_top.u_splitter.gen_lane[3].u_sub.push_result_reg == '0 &&
        po_sampler_mem_dv_o == 1'b0
        ;
    endproperty
    a_signal_reset: assert property (signal_reset_p);

    // Checks that the sampler_fsm signal is updated accordingly.
    property signal_sampler_fsm_p;
        !(!pi_rst_b || pi_zeroize)
    |=>
        abr_sampler_top.sampler_fsm_ps == $past(abr_sampler_top.sampler_fsm_ns);
    endproperty
    a_signal_sampler_fsm: assert property (disable iff (!pi_rst_b || pi_zeroize) signal_sampler_fsm_p);

    // Checks that the sampler_fsm signal stays in its specified value range.
    property signal_sampler_fsm_in_range_p;
        abr_sampler_top.sampler_fsm_ps inside {abr_sampler_pkg::ABR_SAMPLER_IDLE, abr_sampler_pkg::ABR_SAMPLER_PROC, abr_sampler_pkg::ABR_SAMPLER_WAIT, abr_sampler_pkg::ABR_SAMPLER_RUN, abr_sampler_pkg::ABR_SAMPLER_DONE};
    endproperty
    a_signal_sampler_fsm_in_range: assert property (disable iff (!pi_rst_b || pi_zeroize) signal_sampler_fsm_in_range_p);


    generate
        for (genvar i = 0; i < 4; i++) begin : gen_mem_split_check
            property mem_split_zero_less_prime_p;
                pi_split_en_i && po_sampler_mem_dv_o
            |->
                po_sampler_mem_data_o[0][i*REG_SIZE +: REG_SIZE] < fv_prime;
            endproperty
            a_mem_split_zero_less_prime: assert property (disable iff (!pi_rst_b || pi_zeroize) mem_split_zero_less_prime_p);
        end
    endgenerate

    // splitter_mode == 1 iff sampler_mode_i == ABR_CBD_SAMPLER. In all other
    // memory-path modes, splitter_mode == 0. Incorrect mode would cause the
    // wrong modulus (MLDSA_Q vs MLKEM_Q) to be used inside the splitter.
    property signal_splitter_mode_p;
        abr_sampler_top.splitter_mode == (pi_sampler_mode_i == ABR_CBD_SAMPLER);
    endproperty
    a_signal_splitter_mode: assert property (disable iff (!pi_rst_b || pi_zeroize) signal_splitter_mode_p);

    // splitter_en is asserted only when sampler_mode_i is one of the
    // memory-path modes (ABR_EXP_MASK, ABR_REJ_BOUNDED, ABR_CBD_SAMPLER) and
    // split_en_i=1. Never asserted for NTT-path modes (MLDSA_REJ_SAMPLER,
    // MLKEM_REJ_SAMPLER) or state-path modes (the SHAKE/SHA modes) -- those
    // never drive sampler_mem_dv_pre in the first place.
    property signal_splitter_en_p;
        abr_sampler_top.splitter_en
    |->
        pi_split_en_i && (pi_sampler_mode_i inside {ABR_EXP_MASK, ABR_REJ_BOUNDED, ABR_CBD_SAMPLER});
    endproperty
    a_signal_splitter_en: assert property (disable iff (!pi_rst_b || pi_zeroize) signal_splitter_en_p);

    // When the split path is selected, the top-level valid strobe is just the
    // splitter's own ready strobe passed straight through -- no extra latch
    // or delay at the sampler_top mux.
    property signal_sampler_mem_dv_o_split_p;
        pi_split_en_i
    |->
        po_sampler_mem_dv_o == abr_sampler_top.splitter_ready;
    endproperty
    a_signal_sampler_mem_dv_o_split: assert property (disable iff (!pi_rst_b || pi_zeroize) signal_sampler_mem_dv_o_split_p);


    // With split_en_i=0 (bypass), po_sampler_mem_dv_o passes straight through from sampler_mem_dv_pre, no splitter pipeline involved.
    property signal_sampler_mem_dv_o_bypass_p;
        !pi_split_en_i
    |->
        po_sampler_mem_dv_o == abr_sampler_top.sampler_mem_dv_pre;
    endproperty
    a_signal_sampler_mem_dv_o_bypass: assert property (disable iff (!pi_rst_b || pi_zeroize) signal_sampler_mem_dv_o_bypass_p);

    // splitter_ready is splitter_en delayed by EXACTLY 2 cycles
    property signal_splitter_ready_latency_p;
        abr_sampler_top.splitter_ready == $past(abr_sampler_top.splitter_en, 2);
    endproperty
    a_signal_splitter_ready_latency: assert property (disable iff (!pi_rst_b || pi_zeroize) signal_splitter_ready_latency_p);

    // {sampler_ntt_dv_o, sampler_mem_dv_o, sampler_state_dv_o} is always
    // at most one-hot -- never two or three of them asserted at once.
    property signal_sampler_dv_onehot0_p;
        pi_split_en_i
    |->
        $onehot0({po_sampler_ntt_dv_o, po_sampler_mem_dv_o, po_sampler_state_dv_o});
    endproperty
    a_signal_sampler_dv_onehot0: assert property (disable iff (!pi_rst_b || pi_zeroize) signal_sampler_dv_onehot0_p);

    // splitter_ready is a raw, un-re-checked 2-cycle delay of splitter_en, so this
    // proves the mode can't have drifted to an NTT-path/state-path mode by the time it fires.
    property signal_splitter_ready_mode_disjoint_p;
        abr_sampler_top.splitter_ready
    |->
        pi_sampler_mode_i inside {ABR_EXP_MASK, ABR_REJ_BOUNDED, ABR_CBD_SAMPLER};
    endproperty
    a_signal_splitter_ready_mode_disjoint: assert property (disable iff (!pi_rst_b || pi_zeroize) signal_splitter_ready_mode_disjoint_p);


    // po_sampler_ntt_dv_o is only ever driven by the two REJ_SAMPLER arms
    // (mldsa_rejs_dv/mlkem_rejs_dv), so its assertion pins the mode to one of those two.
    property signal_sampler_ntt_dv_mode_disjoint_p;
        po_sampler_ntt_dv_o
    |->
        pi_sampler_mode_i inside {MLDSA_REJ_SAMPLER, MLKEM_REJ_SAMPLER};
    endproperty
    a_signal_sampler_ntt_dv_mode_disjoint: assert property (disable iff (!pi_rst_b || pi_zeroize) signal_sampler_ntt_dv_mode_disjoint_p);


    // The state-path modes (SHAKE/SHA) only ever drive sampler_state_dv_o, never
    // the memory path, so po_sampler_mem_dv_o must stay 0 for their whole duration.
    property signal_sampler_mem_dv_o_state_path_zero_p;
        pi_sampler_mode_i inside {ABR_SHAKE256, ABR_SHAKE128, ABR_SHA512, ABR_SHA256}
    |->
        po_sampler_mem_dv_o == 1'b0;
    endproperty
    a_signal_sampler_mem_dv_o_state_path_zero: assert property (disable iff (!pi_rst_b || pi_zeroize) signal_sampler_mem_dv_o_state_path_zero_p);

    // Full definition of sampler_busy_o: busy while a start is pending or the
    // FSM isn't idle, OR'd with the split pipeline still draining (splitter_en|ready).
    property sampler_busy_correctness_p;
        po_sampler_busy_o == ((pi_sampler_start_i | (abr_sampler_top.sampler_fsm_ps != abr_sampler_pkg::ABR_SAMPLER_IDLE)) | (abr_sampler_top.splitter_en | abr_sampler_top.splitter_ready));
    endproperty
    a_sampler_busy_correctness: assert property (disable iff (!pi_rst_b || pi_zeroize) sampler_busy_correctness_p);

  //a new sampler_start_i is only legal once the sampler has gone idle -- no new start can be
  // accepted while sampler_busy_o is still asserted from a prior operation.
  assert_no_start_while_busy: assert property (disable iff (!pi_rst_b || pi_zeroize)
    po_sampler_busy_o
                                     |=>
    !pi_sampler_start_i
  );



    //******************************* for coverage improvement ******************************

    // 4. The DOM recombination at abr_sampler_top: real state == share0 ^ share1
    //    (abr_sampler_top.sv gen_sha3_masking_recombine).
    property sha3_state_recombine_p;
        abr_sampler_top.sha3_state == (abr_sampler_top.sha3_state_o[0] ^ abr_sampler_top.sha3_state_o[1]);
    endproperty
    a_sha3_state_recombine: assert property (disable iff (!pi_rst_b || pi_zeroize) sha3_state_recombine_p);


    property msg_rdy_o_correctness_p;
        po_msg_rdy_o
    |->
        abr_sampler_top.sha3_inst.u_pad.sel_mux == abr_sampler_top.sha3_inst.u_pad.MuxFifo;
    endproperty
    a_msg_rdy_o_correctness: assert property (disable iff (!pi_rst_b || pi_zeroize) msg_rdy_o_correctness_p);


endmodule
