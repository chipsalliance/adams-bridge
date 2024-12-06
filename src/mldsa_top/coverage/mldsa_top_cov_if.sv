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
    input logic           reset_n,
    input logic           cptra_pwrgood

);

    logic [2 : 0] mldsa_cmd;
    logic [2 : 0] mldsa_sw_cmd;
    logic zeroize;
    // logic pcr_sign_mode;
    logic ready;
    logic valid;

    logic mldsa_privkey_lock;

    logic error_flag;
    // logic privkey_input_outofrange;
    // logic r_output_outofrange;
    // logic s_output_outofrange;
    // logic r_input_outofrange;
    // logic s_input_outofrange;
    // logic pubkeyx_input_outofrange;
    // logic pubkeyy_input_outofrange;
    // logic pubkey_input_invalid;
    // logic pcr_sign_input_invalid;
    logic keygen_process;
    logic signing_process;
    logic verifying_process;
    logic keygen_signing_process;

   
    assign mldsa_cmd = mldsa_top.mldsa_ctrl_inst.cmd_reg;
    // assign pcr_sign_mode = mldsa_top.mldsa_ctrl_inst.pcr_sign_mode;
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
    // assign privkey_input_outofrange = mldsa_top.mldsa_dsa_ctrl_i.privkey_input_outofrange;
    // assign r_output_outofrange = mldsa_top.mldsa_dsa_ctrl_i.r_output_outofrange;
    // assign s_output_outofrange = mldsa_top.mldsa_dsa_ctrl_i.s_output_outofrange;
    // assign r_input_outofrange = mldsa_top.mldsa_dsa_ctrl_i.r_input_outofrange;
    // assign s_input_outofrange = mldsa_top.mldsa_dsa_ctrl_i.s_input_outofrange;
    // assign pubkeyx_input_outofrange = mldsa_top.mldsa_dsa_ctrl_i.pubkeyx_input_outofrange;
    // assign pubkeyy_input_outofrange = mldsa_top.mldsa_dsa_ctrl_i.pubkeyy_input_outofrange;
    // assign pubkey_input_invalid = mldsa_top.mldsa_dsa_ctrl_i.pubkey_input_invalid;
    // assign pcr_sign_input_invalid = mldsa_top.mldsa_dsa_ctrl_i.pcr_sign_input_invalid;
    assign keygen_process = mldsa_top.mldsa_ctrl_inst.keygen_process;
    assign signing_process = mldsa_top.mldsa_ctrl_inst.signing_process;
    assign verifying_process = mldsa_top.mldsa_ctrl_inst.verifying_process;
    assign keygen_signing_process = mldsa_top.mldsa_ctrl_inst.keygen_signing_process;

    covergroup mldsa_top_cov_grp @(posedge clk);
        reset_cp: coverpoint reset_n;
        cptra_pwrgood_cp: coverpoint cptra_pwrgood;

        mldsa_cmd_cp: coverpoint mldsa_cmd;
        // pcr_sign_cp: coverpoint pcr_sign_mode;
        zeroize_cp: coverpoint zeroize;
        ready_cp: coverpoint ready;
        valid_cp: coverpoint valid;

        mldsa_privkey_lock_cp: coverpoint mldsa_privkey_lock;

        error_flag_cp: coverpoint error_flag;
        // privkey_input_outofrange_cp: coverpoint privkey_input_outofrange;
        // r_output_outofrange_cp: coverpoint r_output_outofrange;
        // s_output_outofrange_cp: coverpoint s_output_outofrange;
        // r_input_outofrange_cp: coverpoint r_input_outofrange;
        // s_input_outofrange_cp: coverpoint s_input_outofrange;
        // pubkeyx_input_outofrange_cp: coverpoint pubkeyx_input_outofrange;
        // pubkeyy_input_outofrange_cp: coverpoint pubkeyy_input_outofrange;
        // pubkey_input_invalid_cp: coverpoint pubkey_input_invalid;
        // pcr_sign_input_invalid_cp: coverpoint pcr_sign_input_invalid;

        // cmd_ready_cp: cross mldsa_sw_cmd, ready;
        cmd_kv_cp: cross mldsa_cmd, mldsa_privkey_lock;
        // pcr_ready_cp: cross ready, pcr_sign_mode;
        // pcr_cmd_cp: cross pcr_sign_mode, mldsa_cmd;
        // zeroize_pcr_cp: cross zeroize, pcr_sign_mode;
        zeroize_cmd_cp: cross zeroize, mldsa_cmd;
        zeroize_error_cp: cross zeroize, error_flag;
        zeroize_ready_cp: cross ready, zeroize;
        // pcr_sign_input_invalid_cmd_cp: cross error_flag, mldsa_cmd;
        error_keygen_cp: cross error_flag, keygen_process;
        error_signing_cp: cross error_flag, signing_process;
        error_verifying_cp: cross error_flag, verifying_process;
        error_keygen_signing_cp: cross error_flag, keygen_signing_process;


    endgroup

    mldsa_top_cov_grp mldsa_top_cov_grp1 = new();

endinterface

`endif