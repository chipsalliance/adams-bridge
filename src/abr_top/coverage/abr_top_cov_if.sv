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

`ifndef VERILATOR

interface abr_top_cov_if     
    (
    input logic           clk,
    input logic           rst_b,
    input logic           debugUnlock_or_scan_mode_switch

);

    logic [2 : 0] mldsa_cmd;
    logic [2 : 0] mldsa_sw_cmd;
    logic zeroize;
    logic pcr_sign_mode;
    logic ready;
    logic valid;

    logic mldsa_privkey_lock;

    logic error_flag;
    logic pcr_sign_input_invalid;
    logic skdecode_error;
    logic keygen_process;
    logic signing_process;
    logic verifying_process;
    logic keygen_signing_process;

    logic verify_failure;
    logic normcheck_failure;
    logic [2 : 0] normcheck_mode_failure;
    logic makehint_failure;
    logic invalid_hint;

   
    assign mldsa_cmd = abr_top.mldsa_ctrl_inst.cmd_reg;
    assign pcr_sign_mode = abr_top.mldsa_ctrl_inst.pcr_sign_mode;
    assign zeroize = abr_top.mldsa_ctrl_inst.zeroize;
    assign ready = abr_top.mldsa_ctrl_inst.mldsa_ready;
    assign valid = abr_top.mldsa_ctrl_inst.mldsa_valid_reg;

    always_ff @(posedge clk) begin
        if (!rst_b) begin
            mldsa_sw_cmd <= '0;
        end
        else if (abr_top.mldsa_reg_inst.decoded_reg_strb.MLDSA_CTRL && abr_top.mldsa_reg_inst.decoded_req_is_wr) begin // SW write
            mldsa_sw_cmd <= (abr_top.mldsa_reg_inst.field_storage.MLDSA_CTRL.CTRL.value & ~abr_top.mldsa_reg_inst.decoded_wr_biten[2:0]) | (abr_top.mldsa_reg_inst.decoded_wr_data[2:0] & abr_top.mldsa_reg_inst.decoded_wr_biten[2:0]);
        end
    end

    assign mldsa_privkey_lock = abr_top.mldsa_ctrl_inst.mldsa_privkey_lock;

    assign error_flag = abr_top.mldsa_ctrl_inst.error_flag;
    assign pcr_sign_input_invalid = abr_top.mldsa_ctrl_inst.pcr_sign_input_invalid;
    assign skdecode_error = abr_top.mldsa_ctrl_inst.skdecode_error_i;

    assign keygen_process = abr_top.mldsa_ctrl_inst.keygen_process;
    assign signing_process = abr_top.mldsa_ctrl_inst.signing_process;
    assign verifying_process = abr_top.mldsa_ctrl_inst.verifying_process;
    assign keygen_signing_process = abr_top.mldsa_ctrl_inst.keygen_signing_process;

    assign verify_failure = abr_top.mldsa_ctrl_inst.clear_verify_valid;
    assign normcheck_failure = abr_top.mldsa_ctrl_inst.normcheck_done_i & abr_top.mldsa_ctrl_inst.normcheck_invalid_i;
    assign normcheck_mode_failure[0] = normcheck_failure & (abr_top.mldsa_ctrl_inst.normcheck_mode_o == 2'b00);
    assign normcheck_mode_failure[1] = normcheck_failure & (abr_top.mldsa_ctrl_inst.normcheck_mode_o == 2'b01);
    assign normcheck_mode_failure[2] = normcheck_failure & (abr_top.mldsa_ctrl_inst.normcheck_mode_o == 2'b10);
    assign makehint_failure = abr_top.mldsa_ctrl_inst.makehint_done_i & abr_top.mldsa_ctrl_inst.makehint_invalid_i;
    assign invalid_hint = abr_top.mldsa_ctrl_inst.sigdecode_h_invalid_i;

    covergroup mldsa_top_cov_grp @(posedge clk);
        reset_cp: coverpoint rst_b;
        debugUnlock_or_scan_mode_switch_cp: coverpoint debugUnlock_or_scan_mode_switch;

        mldsa_cmd_cp: coverpoint mldsa_cmd;
        pcr_sign_cp: coverpoint pcr_sign_mode;
        zeroize_cp: coverpoint zeroize;
        ready_cp: coverpoint ready;
        valid_cp: coverpoint valid;

        mldsa_privkey_lock_cp: coverpoint mldsa_privkey_lock;

        error_flag_cp: coverpoint error_flag;
        pcr_sign_input_invalid_cp: coverpoint pcr_sign_input_invalid;
        skdecode_error_cp: coverpoint skdecode_error;
        verify_failure_cp: coverpoint verify_failure;
        normcheck_mode_failure_sign_cp: coverpoint normcheck_mode_failure {
            bins mode_0 = {0};
            bins mode_1 = {1};
            bins mode_2 = {2};
        }
        normcheck_mode_failure_verify_cp: coverpoint normcheck_mode_failure {
            bins mode_0 = {0};
        }
        makehint_failure_cp: coverpoint makehint_failure;
        invalid_hint_cp: coverpoint invalid_hint;

        cmd_ready_cp: cross mldsa_sw_cmd, ready;
        cmd_kv_cp: cross mldsa_cmd, mldsa_privkey_lock;
        pcr_ready_cp: cross ready, pcr_sign_mode;
        pcr_cmd_cp: cross pcr_sign_mode, mldsa_cmd;
        zeroize_pcr_cp: cross zeroize, pcr_sign_mode;
        zeroize_cmd_cp: cross zeroize, mldsa_cmd;
        zeroize_error_cp: cross zeroize, error_flag;
        zeroize_ready_cp: cross ready, zeroize;
        pcr_sign_input_invalid_cmd_cp: cross error_flag, mldsa_cmd;
        error_keygen_cp: cross error_flag, keygen_process;
        error_signing_cp: cross error_flag, signing_process;
        error_verifying_cp: cross error_flag, verifying_process;
        error_keygen_signing_cp: cross error_flag, keygen_signing_process;

        normcheck_signing_failure_cp: cross normcheck_mode_failure_sign_cp, signing_process;
        normcheck_verifying_failure_cp: cross normcheck_mode_failure_verify_cp, verifying_process;
        normcheck_pcr_failure_cp: cross normcheck_mode_failure_sign_cp, pcr_sign_mode;
        makehint_pcr_failure_cp: cross makehint_failure, pcr_sign_mode;

    endgroup




    // SIGN Z encoding
    localparam int NUM_ENC  = 4;
    localparam int GAMMA1   = 19;
    localparam int REG_SIZE = 23;
    localparam int MLDSA_GAMMA1_RANGE = 2**GAMMA1;
    localparam int MLDSA_Q  = 8380417;

    logic [(NUM_ENC*2)-1:0] eq_flags;
    logic [(NUM_ENC*2)-1:0] less_flags;
    logic [(NUM_ENC*2)-1:0] greater_flags;
    logic enc_unit_equal;
    logic enc_unit_less;
    logic enc_unit_greater;

    genvar sig_enc_i;
    generate
        for(sig_enc_i = 0; sig_enc_i < NUM_ENC; sig_enc_i++) begin : enc_loop
        // For the upper instance
        assign eq_flags[sig_enc_i*2]   = (abr_top.sigencode_z_inst.enc_unit[sig_enc_i].upper_encode.data_i == MLDSA_GAMMA1_RANGE);
        assign less_flags[sig_enc_i*2] = (abr_top.sigencode_z_inst.enc_unit[sig_enc_i].upper_encode.data_i <  MLDSA_GAMMA1_RANGE);
        assign greater_flags[sig_enc_i*2] = (abr_top.sigencode_z_inst.enc_unit[sig_enc_i].upper_encode.data_i > MLDSA_GAMMA1_RANGE);
        
        // For the lower instance
        assign eq_flags[sig_enc_i*2+1]   = (abr_top.sigencode_z_inst.enc_unit[sig_enc_i].lower_encode.data_i == MLDSA_GAMMA1_RANGE);
        assign less_flags[sig_enc_i*2+1] = (abr_top.sigencode_z_inst.enc_unit[sig_enc_i].lower_encode.data_i <  MLDSA_GAMMA1_RANGE);
        assign greater_flags[sig_enc_i*2+1] = (abr_top.sigencode_z_inst.enc_unit[sig_enc_i].lower_encode.data_i > MLDSA_GAMMA1_RANGE);
        end
    endgenerate

    // OR-reduce the flags: if any instance meets the condition, the corresponding signal is 1.
    assign enc_unit_equal   = (|eq_flags) & (abr_top.sigencode_z_inst.state != abr_top.sigencode_z_inst.IDLE);
    assign enc_unit_less    = (|less_flags) & (abr_top.sigencode_z_inst.state != abr_top.sigencode_z_inst.IDLE);
    assign enc_unit_greater = (|greater_flags) & (abr_top.sigencode_z_inst.state != abr_top.sigencode_z_inst.IDLE);
    // Sign_z to cover the aggregated conditions
    covergroup mldsa_sign_z_enc_agg_cg @(posedge clk);
        coverpoint enc_unit_equal {
            bins hit = {1'b1};
        }
        coverpoint enc_unit_less {
            bins hit = {1'b1};
        }
        coverpoint enc_unit_greater {
            bins hit = {1'b1};
        }
    endgroup

    // The FSM cases are: 'h0, 'h1, 'h2, MLDSA_Q-1, MLDSA_Q-2, and default.
    logic [(NUM_ENC*2)-1:0] skenc_state0_flags;
    logic [(NUM_ENC*2)-1:0] skenc_state1_flags;
    logic [(NUM_ENC*2)-1:0] skenc_state2_flags;
    logic [(NUM_ENC*2)-1:0] skenc_state_mq1_flags;
    logic [(NUM_ENC*2)-1:0] skenc_state_mq2_flags;
    logic skenc_state0_agg, skenc_state1_agg, skenc_state2_agg, skenc_state_mq1_agg, skenc_state_mq2_agg;

    genvar sk_enc_i;
    generate
    for (sk_enc_i = 0; sk_enc_i < NUM_ENC; sk_enc_i++) begin : sk_enc_loop
        // For mem_a_rd_data element
        assign skenc_state0_flags[sk_enc_i*2]    = (abr_top.skencode_inst.mem_a_rd_data[sk_enc_i] == 'h0);
        assign skenc_state1_flags[sk_enc_i*2]    = (abr_top.skencode_inst.mem_a_rd_data[sk_enc_i] == 'h1);
        assign skenc_state2_flags[sk_enc_i*2]    = (abr_top.skencode_inst.mem_a_rd_data[sk_enc_i] == 'h2);
        assign skenc_state_mq1_flags[sk_enc_i*2] = (abr_top.skencode_inst.mem_a_rd_data[sk_enc_i] == MLDSA_Q - 1);
        assign skenc_state_mq2_flags[sk_enc_i*2] = (abr_top.skencode_inst.mem_a_rd_data[sk_enc_i] == MLDSA_Q - 2);
        // For mem_b_rd_data element
        assign skenc_state0_flags[sk_enc_i*2+1]    = (abr_top.skencode_inst.mem_b_rd_data[sk_enc_i] == 'h0);
        assign skenc_state1_flags[sk_enc_i*2+1]    = (abr_top.skencode_inst.mem_b_rd_data[sk_enc_i] == 'h1);
        assign skenc_state2_flags[sk_enc_i*2+1]    = (abr_top.skencode_inst.mem_b_rd_data[sk_enc_i] == 'h2);
        assign skenc_state_mq1_flags[sk_enc_i*2+1] = (abr_top.skencode_inst.mem_b_rd_data[sk_enc_i] == MLDSA_Q - 1);
        assign skenc_state_mq2_flags[sk_enc_i*2+1] = (abr_top.skencode_inst.mem_b_rd_data[sk_enc_i] == MLDSA_Q - 2);
    end
    endgenerate

    // OR-reduce each set of flags and ensure the FSM is not in IDLE.
    // (Assuming abr_top.skencode_inst.state and its IDLE constant are accessible.)
    assign skenc_state0_agg    = (|skenc_state0_flags)    & (abr_top.skencode_inst.main_state != abr_top.skencode_inst.IDLE);
    assign skenc_state1_agg    = (|skenc_state1_flags)    & (abr_top.skencode_inst.main_state != abr_top.skencode_inst.IDLE);
    assign skenc_state2_agg    = (|skenc_state2_flags)    & (abr_top.skencode_inst.main_state != abr_top.skencode_inst.IDLE);
    assign skenc_state_mq1_agg = (|skenc_state_mq1_flags) & (abr_top.skencode_inst.main_state != abr_top.skencode_inst.IDLE);
    assign skenc_state_mq2_agg = (|skenc_state_mq2_flags) & (abr_top.skencode_inst.main_state != abr_top.skencode_inst.IDLE);

    // Now create a covergroup that samples these aggregated flags.
    covergroup mldsa_skencode_agg_cg @(posedge clk);
        coverpoint skenc_state0_agg    { bins hit = {1'b1}; }
        coverpoint skenc_state1_agg    { bins hit = {1'b1}; }
        coverpoint skenc_state2_agg    { bins hit = {1'b1}; }
        coverpoint skenc_state_mq1_agg { bins hit = {1'b1}; }
        coverpoint skenc_state_mq2_agg { bins hit = {1'b1}; }
    endgroup
    
    // Instantiate the covergroup
    mldsa_skencode_agg_cg mldsa_skencode_agg_cov = new();
    mldsa_sign_z_enc_agg_cg mldsa_sign_z_enc_agg_cov_grp1 = new();

    mldsa_top_cov_grp mldsa_top_cov_grp1 = new();

endinterface

`endif