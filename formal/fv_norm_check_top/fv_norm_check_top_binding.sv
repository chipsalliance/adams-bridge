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
// | Created on 18.02.2025 at 14:01                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import fv_norm_check_top_pkg::*;
import fv_norm_check_top_functions::*;


module fv_norm_check_top_binding;


st_mem_if_it mem_rd_req_port;
assign mem_rd_req_port = '{address: norm_check_top.mem_rd_req.addr, rd_wr_en: norm_check_top.mem_rd_req.rd_wr_en};

st_mem_if_it mem_rd_req;
assign mem_rd_req = '{address: norm_check_top.norm_check_ctrl_inst.mem_rd_req.addr, rd_wr_en: norm_check_top.norm_check_ctrl_inst.mem_rd_req.rd_wr_en};


fv_norm_check_top_m fv_norm_check_top_verif(
  .rst(!norm_check_top.reset_n || norm_check_top.zeroize),
  .clk(norm_check_top.clk),

  // Ports
  .mem_base_addr_port_vld(norm_check_top.norm_check_enable),
  .mem_base_addr_port_rdy(norm_check_top.norm_check_ready),
  .mem_base_addr_port(norm_check_top.mem_base_addr),

  .mem_rd_data_port({norm_check_top.mem_rd_data[95:72],norm_check_top.mem_rd_data[71:48],norm_check_top.mem_rd_data[47:24],norm_check_top.mem_rd_data[23:0]}),

  .norm_check_mode_port(norm_check_top.mode),

  .randomness_lsb_port(norm_check_top.randomness[0]),

  .randomness_port(norm_check_top.randomness[5:1]),

  .shuffling_enable_port(norm_check_top.shuffling_enable),

  .invalid_port(norm_check_top.invalid),

  .mem_rd_req_port(mem_rd_req_port),

  .norm_check_done_port(norm_check_top.norm_check_done),

  // Registers
  .incr_addr(norm_check_top.norm_check_ctrl_inst.increment_addr),
  .invalid(norm_check_top.invalid),
  .mem_base_addr(norm_check_top.norm_check_ctrl_inst.locked_based_addr),
  .mem_rd_addr(norm_check_top.norm_check_ctrl_inst.mem_rd_addr),
  .mem_rd_data(norm_check_top.mem_rd_data),
  .mem_rd_req(mem_rd_req),
  .neutral_cnt(norm_check_top.norm_check_ctrl_inst.neutral_cnt),
  .norm_check_mode(),
  .randomness_lsb(norm_check_top.norm_check_ctrl_inst.latched_in_randomness),
  .shuffling_enable(norm_check_top.randomness_enable),

  // States
  .DONE(norm_check_top.norm_check_ctrl_inst.read_fsm_state_ps == norm_check_top.norm_check_ctrl_inst.CHK_DONE),
  .IDLE(norm_check_top.norm_check_ctrl_inst.read_fsm_state_ps == norm_check_top.norm_check_ctrl_inst.CHK_IDLE),
  .READ_MEM(norm_check_top.norm_check_ctrl_inst.read_fsm_state_ps == norm_check_top.norm_check_ctrl_inst.CHK_RD_MEM),
  .WAIT(norm_check_top.norm_check_ctrl_inst.read_fsm_state_ps == norm_check_top.norm_check_ctrl_inst.CHK_WAIT)
);


endmodule


bind norm_check_top fv_norm_check_top_binding fv_norm_check_top();
