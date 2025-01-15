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

interface mldsa_top_cov_if     
    (
    input logic           clk,
    input logic           rst_b

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

   
    assign mldsa_cmd = mldsa_top.mldsa_ctrl_inst.cmd_reg;
    assign pcr_sign_mode = mldsa_top.mldsa_ctrl_inst.pcr_sign_mode;
    assign zeroize = mldsa_top.mldsa_ctrl_inst.zeroize;
    assign ready = mldsa_top.mldsa_ctrl_inst.mldsa_ready;
    assign valid = mldsa_top.mldsa_ctrl_inst.mldsa_valid_reg;

    always_ff @(posedge clk) begin
        if (!reset_n) begin
            mldsa_sw_cmd <= '0;
        end
        else if (mldsa_top.mldsa_reg_inst.decoded_reg_strb.MLDSA_CTRL && mldsa_top.mldsa_reg_inst.decoded_req_is_wr) begin // SW write
            mldsa_sw_cmd <= (mldsa_top.mldsa_reg_inst.field_storage.MLDSA_CTRL.CTRL.value & ~mldsa_top.mldsa_reg_inst.decoded_wr_biten[2:0]) | (mldsa_top.mldsa_reg_inst.decoded_wr_data[2:0] & mldsa_top.mldsa_reg_inst.decoded_wr_biten[2:0]);
        end
    end

    assign mldsa_privkey_lock = mldsa_top.mldsa_ctrl_inst.mldsa_privkey_lock;

    assign error_flag = mldsa_top.mldsa_dsa_ctrl_i.error_flag;
    assign pcr_sign_input_invalid = mldsa_top.mldsa_dsa_ctrl_i.pcr_sign_input_invalid;
    assign skdecode_error = mldsa_top.mldsa_dsa_ctrl_i.skdecode_error_i;

    assign keygen_process = mldsa_top.mldsa_ctrl_inst.keygen_process;
    assign signing_process = mldsa_top.mldsa_ctrl_inst.signing_process;
    assign verifying_process = mldsa_top.mldsa_ctrl_inst.verifying_process;
    assign keygen_signing_process = mldsa_top.mldsa_ctrl_inst.keygen_signing_process;

    assign verify_failure = mldsa_top.mldsa_ctrl_inst.clear_verify_valid;
    assign normcheck_failure = mldsa_top.mldsa_ctrl_inst.normcheck_done_i & mldsa_top.mldsa_ctrl_inst.normcheck_invalid_i;
    assign normcheck_mode_failure[0] = normcheck_failure & (mldsa_top.mldsa_ctrl_inst.normcheck_mode_o == 2'b00);
    assign normcheck_mode_failure[1] = normcheck_failure & (mldsa_top.mldsa_ctrl_inst.normcheck_mode_o == 2'b01);
    assign normcheck_mode_failure[2] = normcheck_failure & (mldsa_top.mldsa_ctrl_inst.normcheck_mode_o == 2'b10);
    assign makehint_failure = mldsa_top.mldsa_ctrl_inst.makehint_done_i & mldsa_top.mldsa_ctrl_inst.makehint_invalid_i;
    assign invalid_hint = mldsa_top.mldsa_ctrl_inst.sigdecode_h_invalid_i;

    covergroup mldsa_top_cov_grp @(posedge clk);
        reset_cp: coverpoint reset_n;
        cptra_pwrgood_cp: coverpoint cptra_pwrgood;

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
        normcheck_mode_failure_cp: coverpoint normcheck_mode_failure {
            bins mode_0 = {0};
            bins mode_1 = {1};
            bins mode_2 = {2};
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

        normcheck_signing_failure_cp: cross normcheck_mode_failure_cp, signing_process;
        normcheck_verifying_failure_cp: cross normcheck_mode_failure_cp, verifying_process;
        normcheck_pcr_failure_cp: cross normcheck_mode_failure_cp, pcr_sign_mode;
        makehint_pcr_failure_cp: cross makehint_failure, pcr_sign_mode;

    endgroup

    mldsa_top_cov_grp mldsa_top_cov_grp1 = new();

endinterface

`endif