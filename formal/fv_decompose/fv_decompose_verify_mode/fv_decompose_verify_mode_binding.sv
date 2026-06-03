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
// | Created on 20.01.2025 at 15:50                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import decompose_defines_pkg::*;
import decompose_verify_mode_pkg::*;
import decompose_verify_mode_functions::*;


module fv_decompose_verify_mode_ref_wrapper_m;


a_unsigned_1_4 hint_rd_data_port;
assign hint_rd_data_port = '{decompose.mem_hint_rd_data_reg[72], decompose.mem_hint_rd_data_reg[48], decompose.mem_hint_rd_data_reg[24], decompose.mem_hint_rd_data_reg[0]};

a_unsigned_23_4 rd_data_port;
assign rd_data_port = '{decompose.mem_rd_data[94:72], decompose.mem_rd_data[70:48], decompose.mem_rd_data[46:24], decompose.mem_rd_data[22:0]};

a_unsigned_16_4 w1_o_in;
assign w1_o_in = '{decompose.w1_enc_inst.r1_i, decompose.w1_o[63:48], decompose.w1_o[47:32], decompose.w1_o[31:16]};

a_unsigned_23_4 mem_wr_data;
assign mem_wr_data = '{decompose.mem_wr_data[94:72], decompose.mem_wr_data[70:48], decompose.mem_wr_data[46:24], decompose.mem_wr_data[22:0]};

a_unsigned_4_4 usehint_w1_mux;
assign usehint_w1_mux = '{decompose.genblk5[3].usehint_inst.w1_mux, decompose.genblk5[2].usehint_inst.w1_mux, decompose.genblk5[1].usehint_inst.w1_mux, decompose.genblk5[0].usehint_inst.w1_mux};

a_unsigned_1_4 z_neq_z;
assign z_neq_z = '{decompose.z_neq_z[3], decompose.z_neq_z[2], decompose.z_neq_z[1], decompose.z_neq_z[0]};


fv_decompose_verify_mode_m fv_decompose_verify_mode(
  .rst_n(decompose.reset_n && !decompose.zeroize),
  .clk(decompose.clk),

  // Ports
  .current_cnt(decompose.dcmp_ctrl_inst.mem_wr_addr - decompose.dest_base_addr),

  .hint_rd_data_port(hint_rd_data_port),

  .mod_enable_port(decompose.mod_enable),

  .mod_ready_port(decompose.mod_ready),

  .r0_in(decompose.r0),

  .r0_mod_q_port(decompose.r0_mod_q),

  .r1_reg_in(decompose.r1_reg),

  .rd_data_port(rd_data_port),

  .start_port_vld(decompose.decompose_enable),
  .start_port_rdy(1'b1),
  .start_port({decompose.src_base_addr, decompose.dest_base_addr, decompose.hint_src_base_addr}),

  .w1_o_in(w1_o_in),

  .buffer_en(decompose.buffer_en),

  .cnt_new(decompose.dcmp_ctrl_inst.mem_wr_addr - decompose.dest_base_addr),

  .decompose_done(decompose.decompose_done),

  .mem_hint_rd_req_vld(1'b1),
  .mem_hint_rd_req(decompose.mem_hint_rd_req),

  .mem_rd_req_vld(1'b1),
  .mem_rd_req(decompose.mem_rd_req),

  .mem_wr_data(mem_wr_data),

  .mem_wr_req_vld(1'b1),
  .mem_wr_req(decompose.mem_wr_req),

  .r0(decompose.r0),

  .r1_reg(decompose.r1_reg),

  .r1_usehint(decompose.r1_usehint),

  .usehint_w1_mux(usehint_w1_mux),

  .w1_o(decompose.w1_o),

  .z_mem_wr_req_vld(1'b1),
  .z_mem_wr_req(decompose.z_mem_wr_req),

  .z_neq_z(z_neq_z),

  // Registers
  .base_address({decompose.src_base_addr, decompose.dest_base_addr, decompose.hint_src_base_addr}),

  // States
  .IDLE(decompose.dcmp_ctrl_inst.read_fsm_state_ps == DCMP_RD_IDLE && decompose.dcmp_ctrl_inst.write_fsm_state_ps == DCMP_WR_IDLE && !decompose.buffer_en),
  .IDLE_BUFFER_EN(decompose.dcmp_ctrl_inst.read_fsm_state_ps == DCMP_RD_IDLE && decompose.dcmp_ctrl_inst.write_fsm_state_ps == DCMP_WR_IDLE && decompose.buffer_en),
  .RD_MEM_WR_MEM(((decompose.dcmp_ctrl_inst.read_fsm_state_ps == DCMP_RD_MEM && decompose.dcmp_ctrl_inst.mem_rd_addr - decompose.src_base_addr >= 3)  &&  (decompose.dcmp_ctrl_inst.write_fsm_state_ps == DCMP_WR_MEM && decompose.dcmp_ctrl_inst.mem_wr_addr - decompose.dest_base_addr <= 508)) 
  || ((decompose.dcmp_ctrl_inst.write_fsm_state_ps == DCMP_WR_MEM && decompose.dcmp_ctrl_inst.mem_wr_addr - decompose.dest_base_addr > 508) && (decompose.dcmp_ctrl_inst.write_fsm_state_ps == DCMP_WR_MEM && decompose.dcmp_ctrl_inst.mem_wr_addr - decompose.dest_base_addr < 511))),
  .REQ_1ST_DATA(decompose.dcmp_ctrl_inst.read_fsm_state_ps == DCMP_RD_MEM && decompose.dcmp_ctrl_inst.mem_rd_addr - decompose.src_base_addr == 0),
  .REQ_2ND_DATA(decompose.dcmp_ctrl_inst.read_fsm_state_ps == DCMP_RD_MEM && decompose.dcmp_ctrl_inst.mem_rd_addr - decompose.src_base_addr == 1),
  .REQ_3RD_DATA(decompose.dcmp_ctrl_inst.read_fsm_state_ps == DCMP_RD_MEM && decompose.dcmp_ctrl_inst.mem_rd_addr - decompose.src_base_addr == 2),
  .RESP_LAST_DATA(decompose.dcmp_ctrl_inst.write_fsm_state_ps == DCMP_WR_MEM && decompose.dcmp_ctrl_inst.mem_wr_addr - decompose.dest_base_addr == 511)
);


endmodule


bind decompose fv_decompose_verify_mode_ref_wrapper_m fv_decompose_verify_mode_ref_wrapper();
