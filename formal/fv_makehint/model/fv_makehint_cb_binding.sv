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
// | Created on 11.02.2025 at 11:00                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import fv_makehint_functions::*;


bind makehint fv_makehint_cb_m #(
  .BUFFER_DATA_W(BUFFER_DATA_W),
  .OMEGA(OMEGA)
)
fv_makehint_cb (
  .rst_n(makehint.reset_n && !makehint.zeroize),
  .clk(makehint.clk),

  .index_count(makehint.index_count),

  .index(makehint.index),

  .makehint_done(makehint.makehint_done),

  .invalid_h(makehint.invalid_h),

  .max_index_buffer_rd(makehint.max_index_buffer_rd),
  .sample_valid(makehint.sample_valid),
  .flush_buffer(makehint.flush_buffer),

  .incr_index_d1(makehint.incr_index_d1),

  .reg_wren(makehint.reg_wren),

  .reg_wrdata(makehint.reg_wrdata),

  .sample_data(makehint.sample_data),

  .max_index_buffer_rd_lo(makehint.max_index_buffer_rd_lo),

  .max_index_buffer_rd_mid(makehint.max_index_buffer_rd_mid),

  .max_index_buffer_rd_hi(makehint.max_index_buffer_rd_hi),

  .max_index_buffer(makehint.max_index_buffer),

  .max_index_buffer_data(makehint.max_index_buffer_data),

  .r_port(makehint.r),

  .z_port(makehint.z),

  .hintgen_en(makehint.hintgen_enable_reg),

  .hint(makehint.hint),

  .hintsum(makehint.hintsum),
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
