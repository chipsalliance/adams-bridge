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
// | Created on 29.03.2025 at 21:28                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import mldsa_params_pkg::*;
import skdecode_defines_pkg::*;
import fv_skdecode_top_functions::*;
import fv_skdecode_top_pkg::*;


module fv_skdecode_top_m_m;


default clocking default_clk @(posedge (skdecode_top.clk)); endclocking


st_BaseAddress start_port;
assign start_port = '{skdecode_top.keymem_src_base_addr, skdecode_top.dest_base_addr};

st_BaseAddress base_address;
assign base_address = '{skdecode_top.keymem_src_base_addr, skdecode_top.dest_base_addr};


fv_skdecode_top_m fv_skdecode_top(
  .rst_n(skdecode_top.reset_n && !skdecode_top.zeroize),
  .clk(skdecode_top.clk),

  // Ports
  .s1s2_valid_in(skdecode_top.s1s2_data_valid),

  .start_port_vld(skdecode_top.skdecode_enable),
  .start_port_rdy(1'b1),
  .start_port(start_port),

  .t0_valid_in(skdecode_top.t0_valid),

  .keymem_a_rd_req_vld(1'b1),
  .keymem_a_rd_req(skdecode_top.keymem_a_rd_req),

  .keymem_b_rd_req_vld(1'b1),
  .keymem_b_rd_req(skdecode_top.keymem_b_rd_req),

  .mem_a_wr_data(skdecode_top.mem_a_wr_data),

  .mem_a_wr_req_vld(1'b1),
  .mem_a_wr_req(skdecode_top.mem_a_wr_req),

  .mem_b_wr_data(skdecode_top.mem_b_wr_data),

  .mem_b_wr_req_vld(1'b1),
  .mem_b_wr_req(skdecode_top.mem_b_wr_req),

  .s1_done_vld(1'b1),
  .s1_done(skdecode_top.s1_done),

  .s1s2_stall_dummy_out(skdecode_top.s1s2_buf_stall),

  .s2_done_vld(1'b1),
  .s2_done(skdecode_top.s2_done),

  .skdecode_done_vld(1'b1),
  .skdecode_done(skdecode_top.skdecode_done),

  .t0_done_vld(1'b1),
  .t0_done(skdecode_top.t0_done),
  .skdecode_error(skdecode_top.skdecode_error),

  // Registers
  .base_address(base_address),
  .counter(skdecode_top.skdecode_ctrl_inst.skdecode_count),
  .fv_kmem_rd_addr(skdecode_top.skdecode_ctrl_inst.kmem_rd_addr),
  .fv_mem_wr_addr(skdecode_top.skdecode_ctrl_inst.mem_wr_addr),
  .fv_s1s2_buf_data(skdecode_top.s1s2_buf_data),
  .fv_t0_buf_data($past(skdecode_top.t0_buf_data)),
  .s1s2_valid(skdecode_top.s1s2_data_valid),

  // States
  .IDLE(skdecode_top.skdecode_ctrl_inst.read_fsm_state_ps == SKDEC_RD_IDLE && skdecode_top.skdecode_ctrl_inst.write_fsm_state_ps == SKDEC_WR_IDLE),
  .RD_STG_WR_s1(skdecode_top.skdecode_ctrl_inst.read_fsm_state_ps == SKDEC_RD_STAGE && skdecode_top.skdecode_ctrl_inst.write_fsm_state_ps == SKDEC_WR_S1),
  .RD_STG_WR_s2(skdecode_top.skdecode_ctrl_inst.read_fsm_state_ps == SKDEC_RD_STAGE && skdecode_top.skdecode_ctrl_inst.write_fsm_state_ps == SKDEC_WR_S2),
  .RD_STG_WR_STG_1(skdecode_top.skdecode_ctrl_inst.read_fsm_state_ps == SKDEC_RD_STAGE && skdecode_top.skdecode_ctrl_inst.write_fsm_state_ps == SKDEC_WR_STAGE && $past(skdecode_top.skdecode_ctrl_inst.write_fsm_state_ps) == SKDEC_WR_S1  ),
  .RD_STG_WR_STG_2(skdecode_top.skdecode_ctrl_inst.read_fsm_state_ps == SKDEC_RD_STAGE && skdecode_top.skdecode_ctrl_inst.write_fsm_state_ps == SKDEC_WR_STAGE && $past(skdecode_top.skdecode_ctrl_inst.write_fsm_state_ps) == SKDEC_WR_S2  ),
  .RD_STG_WR_STG_3(skdecode_top.skdecode_ctrl_inst.read_fsm_state_ps == SKDEC_RD_STAGE && skdecode_top.skdecode_ctrl_inst.write_fsm_state_ps == SKDEC_WR_STAGE && $past(skdecode_top.skdecode_ctrl_inst.write_fsm_state_ps) == SKDEC_WR_T0  ),
  .RD_STG_WR_t0(skdecode_top.skdecode_ctrl_inst.read_fsm_state_ps == SKDEC_RD_STAGE && skdecode_top.skdecode_ctrl_inst.write_fsm_state_ps == SKDEC_WR_T0),
  .RD_WR_s1(skdecode_top.skdecode_ctrl_inst.read_fsm_state_ps == SKDEC_RD_S1 && skdecode_top.skdecode_ctrl_inst.write_fsm_state_ps == SKDEC_WR_S1),
  .RD_WR_s2(skdecode_top.skdecode_ctrl_inst.read_fsm_state_ps == SKDEC_RD_S2 && skdecode_top.skdecode_ctrl_inst.write_fsm_state_ps == SKDEC_WR_S2               ),
  .RD_WR_t0(skdecode_top.skdecode_ctrl_inst.read_fsm_state_ps == SKDEC_RD_T0 && skdecode_top.skdecode_ctrl_inst.write_fsm_state_ps == SKDEC_WR_T0)
);


endmodule


bind skdecode_top fv_skdecode_top_m_m fv_skdecode_top_m();
