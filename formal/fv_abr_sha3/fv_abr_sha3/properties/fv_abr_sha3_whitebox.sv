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


module fv_abr_sha3_whitebox
    import abr_sha3_pkg::*;
    import abr_prim_mubi_pkg::*;
#(
    parameter ROUNDS_PER_CLOCK = 1,
    parameter EN_MASKING       = 0,
    //#$localparams
    localparam SHARE = (EN_MASKING)?2:1
    //$#//
) (
    input logic                        padding_keccak_ready_i,
    input logic                        keccak_round_ready,
    input logic                        keccak_process,
    input logic                        padding_keccak_run,
    input logic                        keccak_run,
    input abr_prim_mubi_pkg::mubi4_t   keccak_done,
    input logic                        keccak_complete,
    input logic                        keccak_start,
    input logic                        processing,
    input logic                        round_count_error,
    input logic                        msg_count_error,
    input logic                        keccak_round_state_error,
    input logic                        sha3pad_state_error,
    input logic                        keccak_storage_rst_error,
    input logic [StateW/2-1:0]         keccak_rand_data_i,
    input logic                        keccak_rand_aux_i,
    input logic                        keccak_rand_update_o,
    input logic                        keccak_rand_consumed_o,

    //#$ports
    input logic                        pi_clk_i,
    input logic                        pi_rst_b,
    input logic                        pi_zeroize,
    input logic                        pi_msg_start_i,
    input logic                        pi_msg_valid_i,
    input logic [MsgWidth-1:0]         pi_msg_data_i[SHARE],
    input logic [MsgStrbW-1:0]         pi_msg_strb_i,
    input logic                        po_msg_ready_o,
    input logic                        pi_rand_valid_i,
    input logic                        pi_rand_early_i,
    input logic [StateW/2-1:0]         pi_rand_data_i,
    input logic                        pi_rand_aux_i,
    input logic                        po_rand_update_o,
    input logic                        po_rand_consumed_o,
    //input logic [NSRegisterSize*8-1:0] pi_ns_data_i,
    input sha3_mode_e                  pi_mode_i,
    input keccak_strength_e            pi_strength_i,
    input logic                        pi_start_i,
    input logic                        pi_process_i,
    input logic                        pi_run_i,
    input abr_prim_mubi_pkg::mubi4_t   po_absorbed_o,
    input logic                        po_squeezing_o,
    input logic                        po_block_processed_o,
    input sha3_st_e                    po_sha3_fsm_o,
    input logic                        po_state_valid_o,
    input logic                        pi_state_valid_hold_i,
    input logic [StateW-1:0]           po_state_o[SHARE],
    input err_t                        po_error_o,
    input logic                        po_sparse_fsm_error_o,
    input logic                        po_count_error_o,
    input logic                        po_keccak_storage_rst_error_o
    //$#//
);

    default clocking default_clk @(posedge pi_clk_i); endclocking

    // When state_valid_o is low or the fsm is in IDLE, then state_o should all be zeros
    property assert_state_o_p;
        disable iff(!pi_rst_b || pi_zeroize)
        !po_state_valid_o ||
        po_sha3_fsm_o == StIdle
    |->
        po_state_o[0] == '0
    endproperty
    assert_state_o: assert property (assert_state_o_p);

    // After reset or zeroize, state should be flushed
    property assert_state_flush_p;
        !pi_rst_b ||
        pi_zeroize
    |->
        ##1 po_state_o[0] == '0
    endproperty
    assert_state_flush: assert property (assert_state_flush_p);

    // if there exist valid data (state_valid_o) is high, hold is high and done is not received while the FSM is in Squeeze state, then state_o and state_valid_o should stay stable
    // Note: 30.10.2025: This property is commented out due to the latest design changes. The removal of the flush state traps the design in
    // Squeeze or Run states forever. This results having the hold high while valid is high to be an impossible case, rendering this property
    // to be vacuous
    // logic [$clog2($bits(po_state_o[0])+1)-1:0] state_sym_idx;
    // sym_idx: assume property (##1 $stable(state_sym_idx) && state_sym_idx < $bits(po_state_o[0]));

    // assert_data_hold: assert property(disable iff(!pi_rst_b || pi_zeroize)
    //     pi_state_valid_hold_i &&
    //     po_state_valid_o &&
    //     !(po_sha3_fsm_o == StSqueeze)
    // |->
    //     ##1 $stable(po_state_o[0][state_sym_idx]) &&
    //         $stable(po_state_valid_o)
    // );

    // keccak_ready_i going into the padding block should be high when the keccak_round block is ready and the block is not in squeezing mode
    assert_padding_keccak_ready_i: assert property(disable iff(!pi_rst_b || pi_zeroize)
        padding_keccak_ready_i == (keccak_round_ready && !po_squeezing_o)
    );

    // keccak_process signal that is going into the padding block should be high when process_i is received for the first time and the current state is StAbsorb
    logic fv_processing;
    always_ff @(posedge(pi_clk_i) or negedge pi_rst_b) begin
        if(!pi_rst_b) begin
            fv_processing <= 1'b0;
        end else begin
            if(pi_process_i && (po_sha3_fsm_o == StAbsorb)) begin
                fv_processing <= 1'b1;
            end else if(po_absorbed_o == abr_prim_mubi_pkg::MuBi4True) begin
                fv_processing <= 1'b0;
            end
        end
    end

    assert_keccak_process: assert property(disable iff(!pi_rst_b || pi_zeroize)
        keccak_process == (pi_process_i && !fv_processing && (po_sha3_fsm_o == StAbsorb))
    );

    // keccak_run going into the keccak_round block should be set to true if the padding block sets it to true, or when at every squeeze
    assert_keccak_run: assert property(disable iff(!pi_rst_b || pi_zeroize)
        keccak_run == (padding_keccak_run || ((po_sha3_fsm_o == StSqueeze) && pi_run_i))
    );

    // keccak_done going into the keccak_round block (clear_i) should be set to true when the current state is squeezing and there is no run command coming in
    // Note: 30.10.2025: This property is commented out since keccak_done is always written to be abr_prim_mubi_pkg::MuBi4False
    // assert_keccak_done: assert property(disable iff(!pi_rst_b || pi_zeroize)
    //     keccak_done == ((po_sha3_fsm_o == StSqueeze && !pi_run_i) ? abr_prim_mubi_pkg::MuBi4True : abr_prim_mubi_pkg::MuBi4False)
    // );

    // block_processed_o is high when keccak_complete is high, low otherwise
    assert_block_processed_o: assert property(disable iff(!pi_rst_b || pi_zeroize)
        po_block_processed_o == keccak_complete
    );

    // error_o reports ErrSha3SwControl when SW drives a flow signal that is illegal in the current state:
    //   StIdle:      process_i or run_i
    //   StAbsorb:    start_i, run_i, or a repeated process_i
    //   StSqueeze:   start_i or process_i
    //   StManualRun: any of start_i, process_i, run_i
    err_t fv_sw_ctrl_err;
    assign fv_sw_ctrl_err = '{
        valid: 1'b1,
        code:  ErrSha3SwControl,
        info:  24'({pi_run_i, pi_process_i, pi_start_i})
    };

    property assert_sha3_sw_ctrl_err_idle_p;
        disable iff(!pi_rst_b || pi_zeroize)
        po_sha3_fsm_o == StIdle &&
        (pi_process_i || pi_run_i)
    |->
        po_error_o == fv_sw_ctrl_err
    endproperty
    assert_sha3_sw_ctrl_err_idle: assert property (assert_sha3_sw_ctrl_err_idle_p);

    property assert_sha3_sw_ctrl_err_absorb_p;
        disable iff(!pi_rst_b || pi_zeroize)
        po_sha3_fsm_o == StAbsorb &&
        (pi_start_i || pi_run_i || (pi_process_i && processing))
    |->
        po_error_o == fv_sw_ctrl_err
    endproperty
    assert_sha3_sw_ctrl_err_absorb: assert property (assert_sha3_sw_ctrl_err_absorb_p);

    property assert_sha3_sw_ctrl_err_squeeze_p;
        disable iff(!pi_rst_b || pi_zeroize)
        po_sha3_fsm_o == StSqueeze &&
        (pi_start_i || pi_process_i)
    |->
        po_error_o == fv_sw_ctrl_err
    endproperty
    assert_sha3_sw_ctrl_err_squeeze: assert property (assert_sha3_sw_ctrl_err_squeeze_p);

    property assert_sha3_sw_ctrl_err_run_p;
        disable iff(!pi_rst_b || pi_zeroize)
        po_sha3_fsm_o == StManualRun &&
        (pi_start_i || pi_process_i || pi_run_i)
    |->
        po_error_o == fv_sw_ctrl_err
    endproperty
    assert_sha3_sw_ctrl_err_run: assert property (assert_sha3_sw_ctrl_err_run_p);

    // Outside the illegal combinations above, no error is reported
    logic fv_sw_ctrl_err_cond;
    assign fv_sw_ctrl_err_cond =
        (po_sha3_fsm_o == StIdle      && (pi_process_i || pi_run_i)) ||
        (po_sha3_fsm_o == StAbsorb    && (pi_start_i || pi_run_i || (pi_process_i && processing))) ||
        (po_sha3_fsm_o == StSqueeze   && (pi_start_i || pi_process_i)) ||
        (po_sha3_fsm_o == StManualRun && (pi_start_i || pi_process_i || pi_run_i));

    property assert_sha3_no_sw_ctrl_err_p;
        disable iff(!pi_rst_b || pi_zeroize)
        !fv_sw_ctrl_err_cond
    |->
        po_error_o == err_t'{valid: 1'b0, code: ErrNone, info: '0}
    endproperty
    assert_sha3_no_sw_ctrl_err: assert property (assert_sha3_no_sw_ctrl_err_p);

    // Top-level error outputs aggregate the sub-block error sources
    property assert_sha3_count_error_o_p;
        disable iff(!pi_rst_b || pi_zeroize)
        po_count_error_o == (round_count_error || msg_count_error)
    endproperty
    assert_sha3_count_error_o: assert property (assert_sha3_count_error_o_p);

    // sha3 FSM contributes to sparse_fsm_error_o exactly when it is in (or decodes to) StError
    property assert_sha3_sparse_fsm_error_o_p;
        disable iff(!pi_rst_b || pi_zeroize)
        po_sparse_fsm_error_o == ((po_sha3_fsm_o == StError) || keccak_round_state_error || sha3pad_state_error)
    endproperty
    assert_sha3_sparse_fsm_error_o: assert property (assert_sha3_sparse_fsm_error_o_p);

    property assert_sha3_keccak_storage_rst_error_o_p;
        disable iff(!pi_rst_b || pi_zeroize)
        po_keccak_storage_rst_error_o == keccak_storage_rst_error
    endproperty
    assert_sha3_keccak_storage_rst_error_o: assert property (assert_sha3_keccak_storage_rst_error_o_p);

    // Entropy interface is passed through between the top ports and u_keccak
    property assert_sha3_rand_data_i_p;
        disable iff(!pi_rst_b || pi_zeroize)
        keccak_rand_data_i == pi_rand_data_i
    endproperty
    assert_sha3_rand_data_i: assert property (assert_sha3_rand_data_i_p);

    property assert_sha3_rand_aux_i_p;
        disable iff(!pi_rst_b || pi_zeroize)
        keccak_rand_aux_i == pi_rand_aux_i
    endproperty
    assert_sha3_rand_aux_i: assert property (assert_sha3_rand_aux_i_p);

    property assert_sha3_rand_update_o_p;
        disable iff(!pi_rst_b || pi_zeroize)
        po_rand_update_o == keccak_rand_update_o
    endproperty
    assert_sha3_rand_update_o: assert property (assert_sha3_rand_update_o_p);

    property assert_sha3_rand_consumed_o_p;
        disable iff(!pi_rst_b || pi_zeroize)
        po_rand_consumed_o == keccak_rand_consumed_o
    endproperty
    assert_sha3_rand_consumed_o: assert property (assert_sha3_rand_consumed_o_p);

    // keccak_start is raised exactly when start_i is accepted in StIdle
    property assert_sha3_keccak_start_p;
        disable iff(!pi_rst_b || pi_zeroize)
        keccak_start == (po_sha3_fsm_o == StIdle && pi_start_i)
    endproperty
    assert_sha3_keccak_start: assert property (assert_sha3_keccak_start_p);

    // keccak_start marks the StIdle -> StAbsorb transition
    property assert_sha3_keccak_start_to_absorb_p;
        disable iff(!pi_rst_b || pi_zeroize)
        keccak_start
    |->
        ##1 po_sha3_fsm_o == StAbsorb
    endproperty
    assert_sha3_keccak_start_to_absorb: assert property (assert_sha3_keccak_start_to_absorb_p);
endmodule

bind abr_sha3 fv_abr_sha3_whitebox #(.EN_MASKING(EnMasking)) fv_abr_sha3_whitebox_i (
    .keccak_complete(keccak_complete),
    .keccak_start(keccak_start),
    .padding_keccak_ready_i(u_pad.keccak_ready_i),
    .keccak_round_ready(u_keccak.ready_o),
    .keccak_process(keccak_process),
    .keccak_run(u_keccak.run_i),
    .keccak_done(u_keccak.clear_i),
    .padding_keccak_run(u_pad.keccak_run_o),
    .processing(processing),
    .round_count_error(round_count_error),
    .msg_count_error(msg_count_error),
    .keccak_round_state_error(keccak_round_state_error),
    .sha3pad_state_error(sha3pad_state_error),
    .keccak_storage_rst_error(keccak_storage_rst_error),
    .keccak_rand_data_i(u_keccak.rand_data_i),
    .keccak_rand_aux_i(u_keccak.rand_aux_i),
    .keccak_rand_update_o(u_keccak.rand_update_o),
    .keccak_rand_consumed_o(u_keccak.rand_consumed_o),
    .pi_clk_i(clk_i),
    .pi_rst_b(rst_b),
    .pi_zeroize(zeroize),
    .pi_msg_start_i(msg_start_i),
    .pi_msg_valid_i(msg_valid_i),
    .pi_msg_data_i(msg_data_i),
    .pi_msg_strb_i(msg_strb_i),
    .po_msg_ready_o(msg_ready_o),
    .pi_rand_valid_i(rand_valid_i),
    .pi_rand_early_i(rand_early_i),
    .pi_rand_data_i(rand_data_i),
    .pi_rand_aux_i(rand_aux_i),
    .po_rand_update_o(rand_update_o),
    .po_rand_consumed_o(rand_consumed_o),
 //   .pi_ns_data_i(ns_data_i),
    .pi_mode_i(mode_i),
    .pi_strength_i(strength_i),
    .pi_start_i(start_i),
    .pi_process_i(process_i),
    .pi_run_i(run_i),
    .po_absorbed_o(absorbed_o),
    .po_squeezing_o(squeezing_o),
    .po_block_processed_o(block_processed_o),
    .po_sha3_fsm_o(sha3_fsm_o),
    .po_state_valid_o(state_valid_o),
    .pi_state_valid_hold_i(state_valid_hold_i),
    .po_state_o(state_o),
    .po_error_o(error_o),
    .po_sparse_fsm_error_o(sparse_fsm_error_o),
    .po_count_error_o(count_error_o),
    .po_keccak_storage_rst_error_o(keccak_storage_rst_error_o)
);
