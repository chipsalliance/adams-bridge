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
// | Created on 04.08.2025 at 17:50                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import abr_params_pkg::*;
import ntt_defines_pkg::*;
import ntt_ctrl_gs_mlkem_pkg::*;
import ntt_ctrl_gs_mlkem_functions::*;


module fv_ntt_ctrl_gs_mlkem_ref_wrapper_m;


default clocking default_clk @(posedge (ntt_ctrl.clk)); endclocking


function logic unsigned [14:0] mem_rd_addr_base();
  if ($past(!ntt_ctrl.reset_n || ntt_ctrl.zeroize)) begin
    return ntt_ctrl.mem_rd_base_addr;
  end else begin
    return $past(ntt_ctrl.mem_rd_base_addr);
  end
endfunction


fv_ntt_ctrl_gs_mlkem_m fv_ntt_ctrl_gs_mlkem(
  .rst_n(ntt_ctrl.reset_n),
  .clk(ntt_ctrl.clk),

  // Ports
  .buf0_valid_in(ntt_ctrl.buf0_valid),

  .butterfly_ready_in(ntt_ctrl.butterfly_ready),

  .intt_done_in(ntt_ctrl.intt_done),

  .mlkem_in(ntt_ctrl.mlkem),

  .ntt_base_addrs_in(ntt_ctrl.ntt_mem_base_addr),

  .ntt_enable_in(ntt_ctrl.ntt_enable),

  .random_in(ntt_ctrl.random),

  .rst_rounds_in((ntt_ctrl.read_fsm_state_ps == RD_IDLE) && (ntt_ctrl.write_fsm_state_ps == WR_IDLE)),

  .shuffle_en_in(ntt_ctrl.shuffle_en),

  .bf_enable_out(ntt_ctrl.bf_enable),

  .buf_rdptr_out(ntt_ctrl.buf_rdptr),

  .buf_wrptr_out(ntt_ctrl.buf_wrptr),

  .done_out(ntt_ctrl.done),

  .intt_passthrough_out(ntt_ctrl.intt_passthrough),

  .masking_en_ctrl_out(ntt_ctrl.masking_en_ctrl),

  .mem_rd_addr_out(ntt_ctrl.mem_rd_addr),

  .mem_wr_addr_out(ntt_ctrl.mem_wr_addr),

  .opcode_out(ntt_ctrl.opcode),

  .pw_rden_out(ntt_ctrl.pw_rden),

  .pw_wren_out(ntt_ctrl.pw_wren),

  // Registers
  .bf_enable_reg(ntt_ctrl.bf_enable_reg),
  .buf_count(ntt_ctrl.buf_count),
  .buf_wrptr(ntt_ctrl.buf_wrptr),
  .buf_wrptr_reg(ntt_ctrl.buf_wrptr_reg[12:0]),
  .chunk_count(ntt_ctrl.chunk_count),
  .chunk_count_reg(ntt_ctrl.chunk_count_reg[10:0]),
  .chunk_rand_offset(ntt_ctrl.chunk_rand_offset),
  .incr_twiddle_addr_reg(ntt_ctrl.incr_twiddle_addr_reg),
  .index_count(ntt_ctrl.index_count),
  .index_rand_offset(ntt_ctrl.index_rand_offset),
  .mem_rd_addr(ntt_ctrl.mem_rd_addr),
  .mem_rd_addr_base(mem_rd_addr_base()),
  .mem_rd_en_reg(ntt_ctrl.mem_rd_en_reg),
  .mem_wr_addr(ntt_ctrl.mem_wr_addr),
  .rd_valid_count(ntt_ctrl.rd_valid_count),
  .read_state(ntt_ctrl.read_fsm_state_ps == RD_IDLE ? GsReadIdle : (ntt_ctrl.read_fsm_state_ps == RD_STAGE ? GsReadStage : GsReadExec)),
  .rounds_count(ntt_ctrl.rounds_count),
  .twiddle_addr_reg(ntt_ctrl.twiddle_addr_reg),
  .twiddle_addr_reg_d2(ntt_ctrl.twiddle_addr_reg_d2),
  .twiddle_addr_reg_d3(ntt_ctrl.twiddle_addr_reg_d3),
  .unused_mem_rd_en_reg(),
  .unused_twiddle_addr_reg_d3(),
  .wr_valid_count(ntt_ctrl.wr_valid_count),
  .write_state(ntt_ctrl.write_fsm_state_ps == WR_IDLE ? GsWriteIdle : (ntt_ctrl.write_fsm_state_ps == WR_STAGE ? GsWriteStage : (ntt_ctrl.write_fsm_state_ps == WR_BUF ? GsWriteBuf : (ntt_ctrl.write_fsm_state_ps == WR_MEM ? GsWriteMem : GsWriteWait)))),

  // States
  .read_exec(ntt_ctrl.read_fsm_state_ps == RD_EXEC),
  .read_idle(ntt_ctrl.read_fsm_state_ps == RD_IDLE),
  .read_stage(ntt_ctrl.read_fsm_state_ps == RD_STAGE),
  .write_buf(ntt_ctrl.write_fsm_state_ps == WR_BUF),
  .write_idle(ntt_ctrl.write_fsm_state_ps == WR_IDLE),
  .write_mem(ntt_ctrl.write_fsm_state_ps == WR_MEM),
  .write_stage(ntt_ctrl.write_fsm_state_ps == WR_STAGE),
  .write_wait(ntt_ctrl.write_fsm_state_ps == WR_WAIT)
);


endmodule


bind ntt_ctrl fv_ntt_ctrl_gs_mlkem_ref_wrapper_m fv_ntt_ctrl_gs_mlkem_ref_wrapper();
