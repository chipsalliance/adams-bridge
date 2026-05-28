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
// | Created on 14.02.2025 at 11:54                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import fv_makehint_functions::*;


bind makehint fv_makehint_m fv_makehint(
  .rst_n(makehint.reset_n && !makehint.zeroize),
  .clk(makehint.clk),

  // Ports
  .address_port({makehint.mem_base_addr, makehint.dest_base_addr}),

  .buffer_data_o(makehint.sample_data),

  .buffer_valid_o(makehint.sample_valid),

  .makehint_enable_port_vld(makehint.makehint_enable),
  .makehint_enable_port_rdy(1'b1),
  .makehint_enable_port(makehint.makehint_enable),

  .r_port(makehint.r),

  .reg_wr_addr_port_in(makehint.reg_wr_addr),

  .z_port(makehint.z),

  .hintgen_en(makehint.hintgen_enable_reg),

  .index_count_port(makehint.index_count),

  .max_index_buffer_port(makehint.max_index_buffer),

  .mem_rd_req(makehint.mem_rd_req),

  .reg_wr_addr_port(makehint.reg_wr_addr),

  .z_rd_req(makehint.z_rd_req),

  // Registers
  .base_address({makehint.mem_base_addr, makehint.dest_base_addr}),
  .cnt(makehint.mem_rd_addr),
  .hint(makehint.hint),
  .hintsum(makehint.hintsum),
  .max_index_buffer(makehint.max_index_buffer),
  .poly_cnt(makehint.poly_count),

  // States
  .MH_FLUSH_SBUF(makehint.read_fsm_state_ps == MH_FLUSH_SBUF),
  .MH_IDLE(makehint.read_fsm_state_ps == MH_IDLE),
  .MH_RD_IBUF_HIGH(makehint.read_fsm_state_ps == MH_RD_IBUF_HIGH),
  .MH_RD_IBUF_LOW(makehint.read_fsm_state_ps == MH_RD_IBUF_LOW),
  .MH_RD_IBUF_MID(makehint.read_fsm_state_ps == MH_RD_IBUF_MID),
  .MH_RD_MEM(makehint.read_fsm_state_ps == MH_RD_MEM),
  .MH_WAIT1(makehint.read_fsm_state_ps == MH_WAIT1),
  .MH_WAIT2(makehint.read_fsm_state_ps == MH_WAIT2)
);
