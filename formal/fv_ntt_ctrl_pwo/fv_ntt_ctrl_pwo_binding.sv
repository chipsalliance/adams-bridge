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
// | Contact: contact@lubis-eda.com                    |
// +---------------------------------------------------+





module fv_ntt_ctrl_pwo_ref_wrapper_m #(
  parameter SRAM_LATENCY = 1
);

import ntt_defines_pkg::*;
import fv_ntt_ctrl_pwo_pkg::*;
import fv_ntt_ctrl_pwo_functions::*;

fv_pwo_mem_addrs_type fv_pwo_mem_base_addr_in;
assign fv_pwo_mem_base_addr_in = '{
  pw_base_addr_a: ntt_ctrl.pwo_mem_base_addr.pw_base_addr_a,
  pw_base_addr_b: ntt_ctrl.pwo_mem_base_addr.pw_base_addr_b,
  pw_base_addr_c: ntt_ctrl.pwo_mem_base_addr.pw_base_addr_c
};


fv_ntt_ctrl_pwo_m #(.LATENCY(SRAM_LATENCY)) fv_ntt_ctrl_pwo(
  .rst(ntt_ctrl.reset_n ),
  .clk(ntt_ctrl.clk),

  // Ports
  .fv_accumulate_in(ntt_ctrl.accumulate),

  .fv_butterfly_ready_in(ntt_ctrl.butterfly_ready),

  .fv_ntt_enable_in(ntt_ctrl.ntt_enable),

  .fv_ntt_mode_in(ntt_ctrl.ntt_mode),

  .fv_pwo_mem_base_addr_in(fv_pwo_mem_base_addr_in),

  .fv_random_in(ntt_ctrl.random),
  .fv_mlkem_in(ntt_ctrl.mlkem),

  .fv_rst_rounds_in(ntt_ctrl.rst_rounds),

  .fv_sampler_valid_in(ntt_ctrl.sampler_valid),

  .fv_shuffle_en_in(ntt_ctrl.shuffle_en),

  .fv_buf_rd_rst_count_out(ntt_ctrl.buf_rd_rst_count),

  .fv_buf_rden_out(ntt_ctrl.buf_rden),

  .fv_buf_rdptr_out(ntt_ctrl.buf_rdptr),

  .fv_buf_wr_rst_count_out(ntt_ctrl.buf_wr_rst_count),

  .fv_buf_wren_out(ntt_ctrl.buf_wren),

  .fv_buf_wrptr_out(ntt_ctrl.buf_wrptr),

  .fv_done_out(ntt_ctrl.done),

  .fv_mem_rd_en_out(ntt_ctrl.mem_rd_en),

  .fv_mem_wr_en_out(ntt_ctrl.mem_wr_en),

  .fv_opcode_out(ntt_ctrl.opcode),

  .fv_pw_mem_rd_addr_a_out(ntt_ctrl.pw_mem_rd_addr_a),

  .fv_pw_mem_rd_addr_b_out(ntt_ctrl.pw_mem_rd_addr_b),

  .fv_pw_mem_rd_addr_c_out(ntt_ctrl.pw_mem_rd_addr_c),

  .fv_pw_mem_wr_addr_c_out(ntt_ctrl.pw_mem_wr_addr_c),

  // Write custom property, as twiddle_addr combinationally depends on shuffle_en
  // .twiddle_addr_out(ntt_ctrl.twiddle_addr),

  // Registers
  .fv_buf_rdptr_reg(ntt_ctrl.buf_rdptr_reg), /// [21:0] --> changed
  .fv_chunk_count(ntt_ctrl.chunk_count),
  .fv_chunk_count_reg(ntt_ctrl.chunk_count_reg),
  .fv_chunk_rand_offset(ntt_ctrl.chunk_rand_offset),
  .fv_incr_twiddle_addr_reg(ntt_ctrl.incr_twiddle_addr_reg),
  .fv_index_count(ntt_ctrl.index_count),
  .fv_index_rand_offset(ntt_ctrl.index_rand_offset),
  .fv_pw_mem_rd_addr_a_reg(ntt_ctrl.pw_mem_rd_addr_a),
  .fv_pw_mem_rd_addr_b_reg(ntt_ctrl.pw_mem_rd_addr_b),
  .fv_pw_mem_rd_addr_c_reg(ntt_ctrl.pw_mem_rd_addr_c),
  .fv_pw_mem_wr_addr_c_reg(ntt_ctrl.pw_mem_wr_addr_c),
  .fv_rd_valid_count(ntt_ctrl.rd_valid_count),
  .fv_read_state(ntt_ctrl.read_fsm_state_ps == RD_IDLE ? fv_pwo_read_idle_type : (ntt_ctrl.read_fsm_state_ps == RD_STAGE ? fv_pwo_read_stage_type : (ntt_ctrl.read_fsm_state_ps == RD_EXEC ? fv_pwo_read_exec_type : fv_pwo_read_exec_wait_type))),
  .fv_rounds_count(ntt_ctrl.rounds_count),
  .fv_twiddle_addr_int(ntt_ctrl.twiddle_addr_int),
   .fv_twiddle_addr_reg_d2(ntt_ctrl.twiddle_addr_reg[1]),
  // .fv_twiddle_addr_reg_d3(ntt_ctrl.twiddle_addr_reg[2]),
  .fv_wr_valid_count(ntt_ctrl.wr_valid_count),
  .fv_write_state(ntt_ctrl.write_fsm_state_ps == WR_IDLE ? fv_pwo_write_idle_type : (ntt_ctrl.write_fsm_state_ps == WR_STAGE ? fv_pwo_write_stage_type : (ntt_ctrl.write_fsm_state_ps == WR_MEM ? fv_pwo_write_mem_type : fv_pwo_write_wait_type))),

  // States
  .fv_read_exec(ntt_ctrl.read_fsm_state_ps == RD_EXEC),
  .fv_read_exec_wait(ntt_ctrl.read_fsm_state_ps == EXEC_WAIT),
  .fv_read_idle(ntt_ctrl.read_fsm_state_ps == RD_IDLE),
  .fv_read_stage(ntt_ctrl.read_fsm_state_ps == RD_STAGE),
  .state(1'b1),
  .fv_write_idle(ntt_ctrl.write_fsm_state_ps == WR_IDLE),
  .fv_write_mem(ntt_ctrl.write_fsm_state_ps == WR_MEM),
  .fv_write_stage(ntt_ctrl.write_fsm_state_ps == WR_STAGE),
  .fv_write_wait(ntt_ctrl.write_fsm_state_ps == WR_WAIT)
);


endmodule


bind ntt_ctrl fv_ntt_ctrl_pwo_ref_wrapper_m #(.SRAM_LATENCY(SRAM_LATENCY)) fv_ntt_ctrl_pwo_ref_wrapper();
