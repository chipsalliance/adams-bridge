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
// | Created on 10.03.2025 at 09:40                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


module fv_sigdecode_h_states_ref_wrapper_m
  import fv_sigdecode_h_states_pkg::*;
  import abr_params_pkg::*;
  import fv_sigdecode_h_functions::*;
  import sigdecode_h_defines_pkg::*;
#(
    parameter REG_SIZE    = 24,
    parameter MLDSA_OMEGA = 75,
    parameter MLDSA_K     = 8,
    parameter MLDSA_N     = 256,
    //#$localparams
    localparam SIG_H_NUM_DWORDS = ((MLDSA_OMEGA+MLDSA_K+1)*8)/32
    //$#//
) (
    //#$ports
    input                                  pi_clk,
    input                                  pi_reset_n,
    input                                  pi_zeroize,
    input [(MLDSA_OMEGA+MLDSA_K)-1:0][7:0] pi_encoded_h_i,
    input                                  pi_sigdecode_h_enable,
    input [ABR_MEM_ADDR_WIDTH-1:0]       pi_dest_base_addr,
    input mem_if_t                         po_mem_wr_req,
    input logic [(4*REG_SIZE)-1:0]         po_mem_wr_data,
    input logic                            po_sigdecode_h_done,
    input logic                            po_sigdecode_h_error
    //$#//
);


st_Request write_request_port;
assign write_request_port = '{address: sigdecode_h.mem_wr_req.addr, idle: sigdecode_h.mem_wr_req.rd_wr_en == RW_IDLE, read: sigdecode_h.mem_wr_req.rd_wr_en == RW_READ, write: sigdecode_h.mem_wr_req.rd_wr_en == RW_WRITE};


fv_sigdecode_h_states_m fv_sigdecode_h_states(
  .rst(!sigdecode_h.reset_n || sigdecode_h.zeroize),
  .clk(sigdecode_h.clk),

  // Ports
  .dest_address_port(sigdecode_h.dest_base_addr),

  .read_data_port(sigdecode_h.encoded_h_i),

  .start_port(sigdecode_h.sigdecode_h_enable),

  .start_write_fsm(sigdecode_h.sigdecode_h_enable),

  .done_port(sigdecode_h.sigdecode_h_done),

  .error_port(sigdecode_h.sigdecode_h_error),

  .write_data_port(sigdecode_h.mem_wr_data),

  .write_request_port(write_request_port),

  // Registers
  .bitmap(sigdecode_h.bitmap),
  .bitmap_ptr(sigdecode_h.sdh_ctrl_inst.bitmap_ptr),
  .curr_poly_map(sigdecode_h.curr_poly_map),
  .dest_address(sigdecode_h.dest_base_addr),
  .error(sigdecode_h.sigdecode_h_error),
  .first_hint(sigdecode_h.first_hint),
  .hint(sigdecode_h.hint),
  .hint_ok(sigdecode_h.hint_ok),
  .hint_rd_en_f(sigdecode_h.sdh_ctrl_inst.hint_rd_en_f),
  .hintsum(sigdecode_h.hintsum),
  .hintsum_curr_poly(sigdecode_h.hintsum_curr_poly),
  .hintsum_max_error_i(sigdecode_h.hintsum_max_error_i),
  .hintsum_prev_poly(sigdecode_h.hintsum_prev_poly),
  .mem_wr_addr(sigdecode_h.sdh_ctrl_inst.mem_wr_addr),
  .OR_remaining_encoded_h_i(sigdecode_h.OR_remaining_encoded_h_i),
  .poly_count(sigdecode_h.poly_count),
  .prev_hint(sigdecode_h.prev_hint_byte),
  .rd_ptr(sigdecode_h.sdh_ctrl_inst.rd_ptr),
  .read_data(sigdecode_h.encoded_h_i),
  .read_state(sigdecode_h.sdh_ctrl_inst.read_fsm_state_ps == SDH_RD_IDLE ? ReadIdle : (sigdecode_h.sdh_ctrl_inst.read_fsm_state_ps == SDH_RD_INIT ? ReadInit : (sigdecode_h.sdh_ctrl_inst.read_fsm_state_ps == SDH_RD_HINTSUM ? ReadHintSum : ReadExec))),
  .rem_hintsum(sigdecode_h.sdh_ctrl_inst.rem_hintsum),
  .write_state(sigdecode_h.sdh_ctrl_inst.write_fsm_state_ps == SDH_WR_IDLE ? WriteIdle : (sigdecode_h.sdh_ctrl_inst.write_fsm_state_ps == SDH_WR_INIT ? WriteInit : WriteMem)),

  // States
  .rEXEC(sigdecode_h.sdh_ctrl_inst.read_fsm_state_ps == sigdecode_h_defines_pkg::SDH_RD_EXEC),
  .rHINTSUM(sigdecode_h.sdh_ctrl_inst.read_fsm_state_ps == sigdecode_h_defines_pkg::SDH_RD_HINTSUM),
  .rIDLE(sigdecode_h.sdh_ctrl_inst.read_fsm_state_ps == sigdecode_h_defines_pkg::SDH_RD_IDLE),
  .rINIT(sigdecode_h.sdh_ctrl_inst.read_fsm_state_ps == sigdecode_h_defines_pkg::SDH_RD_INIT),
  .wIDLE(sigdecode_h.sdh_ctrl_inst.write_fsm_state_ps == sigdecode_h_defines_pkg::SDH_WR_IDLE),
  .wINIT(sigdecode_h.sdh_ctrl_inst.write_fsm_state_ps == sigdecode_h_defines_pkg::SDH_WR_INIT),
  .wMEM(sigdecode_h.sdh_ctrl_inst.write_fsm_state_ps == sigdecode_h_defines_pkg::SDH_WR_MEM)
);


endmodule

bind sigdecode_h fv_sigdecode_h_states_ref_wrapper_m #(
    .REG_SIZE    (REG_SIZE   ),
    .MLDSA_OMEGA (MLDSA_OMEGA),
    .MLDSA_K     (MLDSA_K    ),
    .MLDSA_N     (MLDSA_N    )
 ) fv_sigdecode_h_states_ref_wrapper (
    //#$bind
    .pi_clk (clk),
    .pi_reset_n (reset_n),
    .pi_zeroize (zeroize),
    .pi_encoded_h_i (encoded_h_i),
    .pi_sigdecode_h_enable (sigdecode_h_enable),
    .pi_dest_base_addr (dest_base_addr),
    .po_mem_wr_req (mem_wr_req),
    .po_mem_wr_data (mem_wr_data),
    .po_sigdecode_h_done (sigdecode_h_done),
    .po_sigdecode_h_error (sigdecode_h_error)
    //$#//
);
