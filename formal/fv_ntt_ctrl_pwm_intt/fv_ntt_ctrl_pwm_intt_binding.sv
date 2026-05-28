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
// | Created on 16.04.2025 at 08:58                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import ntt_defines_pkg::*;
import fv_ntt_ctrl_pwm_intt_functions::*;


module fv_ntt_ctrl_pwm_intt_ref_wrapper_m;


function e_PwmInttReadStatesType read_state();
  if (ntt_ctrl.read_fsm_state_ps == RD_IDLE) begin
    return PwmInttReadIdle;
  end else if (ntt_ctrl.read_fsm_state_ps == RD_STAGE) begin
    return PwmInttReadStage;
  end else begin
    return PwmInttReadExec;
  end
endfunction

function e_PwmInttWriteStatesType write_state();
  if (ntt_ctrl.write_fsm_state_ps == WR_IDLE) begin
    return PwmInttWriteIdle;
  end else if (ntt_ctrl.write_fsm_state_ps == WR_STAGE) begin
    return PwmInttWriteStage;
  end else if (ntt_ctrl.write_fsm_state_ps == WR_BUF) begin
    return PwmInttWriteBuf;
  end else if (ntt_ctrl.write_fsm_state_ps == WR_MEM) begin
    return PwmInttWriteMem;
  end else begin
    return PwmInttWriteWait;
  end
endfunction


st_NttMemBaseAddrs ntt_mem_base_addr_in;
assign ntt_mem_base_addr_in = '{
  src_base_addr: ntt_ctrl.ntt_mem_base_addr.src_base_addr,
  interim_base_addr: ntt_ctrl.ntt_mem_base_addr.interim_base_addr,
  dest_base_addr: ntt_ctrl.ntt_mem_base_addr.dest_base_addr
};

st_NttPwBaseAddrs pwo_mem_base_addr_in;
assign pwo_mem_base_addr_in = '{
  pw_base_addr_a: ntt_ctrl.pwo_mem_base_addr.pw_base_addr_a,
  pw_base_addr_b: ntt_ctrl.pwo_mem_base_addr.pw_base_addr_b,
  pw_base_addr_c: ntt_ctrl.pwo_mem_base_addr.pw_base_addr_c
};


fv_ntt_ctrl_pwm_intt_m fv_ntt_ctrl_pwm_intt(
  .rst_n(ntt_ctrl.reset_n),
  .clk(ntt_ctrl.clk),

  // Ports
  .accumulate_in(ntt_ctrl.accumulate),

  .buf0_valid_in(ntt_ctrl.buf0_valid),

  .butterfly_ready_in(ntt_ctrl.butterfly_ready),

  .ntt_enable_in(ntt_ctrl.ntt_enable),

  .ntt_mem_base_addr_in(ntt_mem_base_addr_in),

  .pwo_mem_base_addr_in(pwo_mem_base_addr_in),

  .random_in(ntt_ctrl.random),

  .rst_rounds_in(ntt_ctrl.rst_rounds),

  .sampler_valid_in(ntt_ctrl.sampler_valid),

  .shuffle_en_in(ntt_ctrl.shuffle_en),

  .buf_rdptr_out(ntt_ctrl.buf_rdptr),

  .buf_wrptr_out(ntt_ctrl.buf_wrptr),

  .done_out(ntt_ctrl.done),

  .masking_en_ctrl_out(ntt_ctrl.masking_en_ctrl),

  .mem_rd_addr_out(ntt_ctrl.mem_rd_addr),

  .mem_wr_addr_out(ntt_ctrl.mem_wr_addr),

  .opcode_out(ntt_ctrl.opcode),

  .pw_mem_rd_addr_a_out(ntt_ctrl.pw_mem_rd_addr_a),

  .pw_mem_rd_addr_b_out(ntt_ctrl.pw_mem_rd_addr_b),

  .pw_mem_rd_addr_c_out(ntt_ctrl.pw_mem_rd_addr_c),

  .pw_wren_out(ntt_ctrl.pw_wren),

  // Registers
  .bf_enable_reg(ntt_ctrl.bf_enable_reg),
  .bf_enable_reg_d2(ntt_ctrl.bf_enable_reg_d2),
  .bf_enable_reg_d2_dummy(),
  .buf_count(ntt_ctrl.buf_count),
  .buf_wren_intt_reg(ntt_ctrl.buf_wren_intt_reg),
  .buf_wren_intt_reg_dummy(),
  .buf_wrptr(ntt_ctrl.buf_wrptr),
  .buf_wrptr_reg(ntt_ctrl.buf_wrptr_reg),
  .chunk_count(ntt_ctrl.chunk_count),
  .chunk_count_reg(ntt_ctrl.chunk_count_reg),
  .chunk_rand_offset(ntt_ctrl.chunk_rand_offset),
  .incr_twiddle_addr_reg(ntt_ctrl.incr_twiddle_addr_reg),
  .index_count(ntt_ctrl.index_count),
  .index_rand_offset(ntt_ctrl.index_rand_offset),
  .mem_rd_addr(ntt_ctrl.mem_rd_addr),
  .mem_rd_en_reg(ntt_ctrl.mem_rd_en_reg),
  .mem_rd_en_reg_dummy(),
  .mem_wr_addr(ntt_ctrl.mem_wr_addr),
  .pw_mem_rd_addr_a_reg(ntt_ctrl.pw_mem_rd_addr_a),
  .pw_mem_rd_addr_b_reg(ntt_ctrl.pw_mem_rd_addr_b),
  .pw_mem_rd_addr_c_reg(ntt_ctrl.pw_mem_rd_addr_c),
  .pw_rden_reg(ntt_ctrl.pw_rden_reg),
  .pw_rden_reg_dummy(),
  .pw_wren_reg(ntt_ctrl.pw_wren_reg),
  .pw_wren_reg_dummy(),
  .rd_valid_count(ntt_ctrl.rd_valid_count),
  .read_state(read_state()),
  .rounds_count(ntt_ctrl.rounds_count),
  .twiddle_addr_reg(ntt_ctrl.twiddle_addr_reg),
  .twiddle_addr_reg_d2(ntt_ctrl.twiddle_addr_reg_d2),
  .twiddle_addr_reg_d3(ntt_ctrl.twiddle_addr_reg_d3),
  .twiddle_addr_reg_d3_dummy(),
  .wr_valid_count(ntt_ctrl.wr_valid_count),
  .write_state(write_state()),

  // States
  .read_exec(ntt_ctrl.read_fsm_state_ps == RD_EXEC),
  .read_idle(ntt_ctrl.read_fsm_state_ps == RD_IDLE),
  .read_stage(ntt_ctrl.read_fsm_state_ps == RD_STAGE),
  .state(1'b1),
  .write_buf(ntt_ctrl.write_fsm_state_ps == WR_BUF),
  .write_idle(ntt_ctrl.write_fsm_state_ps == WR_IDLE),
  .write_mem(ntt_ctrl.write_fsm_state_ps == WR_MEM),
  .write_stage(ntt_ctrl.write_fsm_state_ps == WR_STAGE),
  .write_wait(ntt_ctrl.write_fsm_state_ps == WR_WAIT)
);


endmodule


bind ntt_ctrl fv_ntt_ctrl_pwm_intt_ref_wrapper_m fv_ntt_ctrl_pwm_intt_ref_wrapper();
