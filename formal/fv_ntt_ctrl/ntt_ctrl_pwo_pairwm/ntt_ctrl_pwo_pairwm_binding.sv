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
// | Created on 22.08.2025 at 11:32                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import abr_params_pkg::*;
import ntt_defines_pkg::*;
import ntt_ctrl_pwo_pairwm_functions::*;
import ntt_ctrl_pwo_pairwm_pkg::*;


module fv_ntt_ctrl_pwo_pairwm_ref_wrapper_m;


st_PwoMemAddrs pwo_mem_base_addr_in;
assign pwo_mem_base_addr_in = '{
  pw_base_addr_a: ntt_ctrl.pwo_mem_base_addr.pw_base_addr_a,
  pw_base_addr_b: ntt_ctrl.pwo_mem_base_addr.pw_base_addr_b,
  pw_base_addr_c: ntt_ctrl.pwo_mem_base_addr.pw_base_addr_c
};


fv_ntt_ctrl_pwo_pairwm_m fv_ntt_ctrl_pwo_pairwm(
  .rst_n(ntt_ctrl.reset_n),
  .clk(ntt_ctrl.clk),

  // Ports
  .accumulate_in(ntt_ctrl.accumulate),

  .buf0_valid_in(ntt_ctrl.buf0_valid),

  .butterfly_ready_in(ntt_ctrl.butterfly_ready),

  .masking_en_in(ntt_ctrl.masking_en),

  .mlkem_in(ntt_ctrl.mlkem),

  .ntt_enable_in(ntt_ctrl.ntt_enable),

  .ntt_mode_in(ntt_ctrl.ntt_mode),

  .pwo_mem_base_addr_in(pwo_mem_base_addr_in),

  .random_in(ntt_ctrl.random),

  .rst_rounds_in(ntt_ctrl.rst_rounds),

  .sampler_valid_in(ntt_ctrl.sampler_valid),

  .shuffle_en_in(ntt_ctrl.shuffle_en),

  .buf_rd_rst_count_out(ntt_ctrl.buf_rd_rst_count),

  .buf_rden_out(ntt_ctrl.buf_rden),

  .buf_rdptr_out(ntt_ctrl.buf_rdptr),

  .buf_wr_rst_count_out(ntt_ctrl.buf_wr_rst_count),

  .buf_wren_out(ntt_ctrl.buf_wren),

  .buf_wrptr_out(ntt_ctrl.buf_wrptr),

  .done_out(ntt_ctrl.done),

  .masking_en_ctrl_out(ntt_ctrl.masking_en_ctrl),

  .mem_rd_en_out(ntt_ctrl.mem_rd_en),

  .mem_wr_en_out(ntt_ctrl.mem_wr_en),

  .opcode_out(ntt_ctrl.opcode),

  .pw_mem_rd_addr_a_out(ntt_ctrl.pw_mem_rd_addr_a),

  .pw_mem_rd_addr_b_out(ntt_ctrl.pw_mem_rd_addr_b),

  .pw_mem_rd_addr_c_out(ntt_ctrl.pw_mem_rd_addr_c),

  .pw_mem_wr_addr_c_out(ntt_ctrl.pw_mem_wr_addr_c),

  // Registers
  .bf_enable_reg(ntt_ctrl.bf_enable_reg),
  .bf_enable_reg_dummy(),
  .buf_count(ntt_ctrl.buf_count),
  .buf_rdptr_reg(ntt_ctrl.buf_rdptr_reg),
  .chunk_count(ntt_ctrl.chunk_count),
  .chunk_count_reg(ntt_ctrl.chunk_count_reg),
  .chunk_rand_offset(ntt_ctrl.chunk_rand_offset),
  .incr_pw_rd_addr_reg(ntt_ctrl.incr_pw_rd_addr_reg),
  .incr_twiddle_addr_reg(ntt_ctrl.incr_twiddle_addr_reg),
  .index_count(ntt_ctrl.index_count),
  .index_rand_offset(ntt_ctrl.index_rand_offset),
  .masked_pwm_buf_rdptr_d1(ntt_ctrl.masked_pwm_buf_rdptr_d1),
  .masked_pwm_buf_rdptr_d2(ntt_ctrl.masked_pwm_buf_rdptr_d2),
  .masked_pwm_buf_rdptr_d3(ntt_ctrl.masked_pwm_buf_rdptr_d3),
  .pw_mem_rd_addr_a_reg(ntt_ctrl.pw_mem_rd_addr_a),
  .pw_mem_rd_addr_b_reg(ntt_ctrl.pw_mem_rd_addr_b),
  .pw_mem_rd_addr_c_reg(ntt_ctrl.pw_mem_rd_addr_c),
  .pw_mem_wr_addr_c_reg(ntt_ctrl.pw_mem_wr_addr_c),
  .pw_rden_fsm_reg(ntt_ctrl.pw_rden_fsm_reg),
  .pw_rden_reg(ntt_ctrl.pw_rden_reg),
  .pw_rden_reg_dummy(),
  .pw_wren_reg(ntt_ctrl.pw_wren_reg),
  .pw_wren_reg_dummy(),
  .rd_valid_count(ntt_ctrl.rd_valid_count),
  .read_state(ntt_ctrl.read_fsm_state_ps == RD_IDLE ? PwoReadIdle : (ntt_ctrl.read_fsm_state_ps == RD_STAGE ? PwoReadStage : (ntt_ctrl.read_fsm_state_ps == RD_EXEC ? PwoReadExec : PwoReadExecWait))),
  .rounds_count(ntt_ctrl.rounds_count),
  .shuffled_pw_rden_fsm_reg(ntt_ctrl.shuffled_pw_rden_fsm_reg),
  .shuffled_pw_rden_fsm_reg_dummy(),
  .twiddle_addr_reg(ntt_ctrl.twiddle_addr_reg),
  .twiddle_addr_reg_d2(ntt_ctrl.twiddle_addr_reg_d2),
  .twiddle_addr_reg_d3(ntt_ctrl.twiddle_addr_reg_d3),
  .twiddle_addr_reg_d3_dummy(),
  .wr_valid_count(ntt_ctrl.wr_valid_count),
  .write_state(ntt_ctrl.write_fsm_state_ps == WR_IDLE ? PwoWriteIdle : (ntt_ctrl.write_fsm_state_ps == WR_STAGE ? PwoWriteStage : (ntt_ctrl.write_fsm_state_ps == WR_MEM ? PwoWriteMem : PwoWriteWait))),

  // States
  .read_exec(ntt_ctrl.read_fsm_state_ps == RD_EXEC),
  .read_exec_wait(ntt_ctrl.read_fsm_state_ps == EXEC_WAIT),
  .read_idle(ntt_ctrl.read_fsm_state_ps == RD_IDLE),
  .read_stage(ntt_ctrl.read_fsm_state_ps == RD_STAGE),
  .state(1'b1),
  .write_idle(ntt_ctrl.write_fsm_state_ps == WR_IDLE),
  .write_mem(ntt_ctrl.write_fsm_state_ps == WR_MEM),
  .write_stage(ntt_ctrl.write_fsm_state_ps == WR_STAGE),
  .write_wait(ntt_ctrl.write_fsm_state_ps == WR_WAIT)
);


endmodule


bind ntt_ctrl fv_ntt_ctrl_pwo_pairwm_ref_wrapper_m fv_ntt_ctrl_pwo_pairwm_ref_wrapper();
