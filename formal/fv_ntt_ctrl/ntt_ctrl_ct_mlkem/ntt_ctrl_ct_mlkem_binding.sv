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
// | Created on 05.08.2025 at 16:36                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import abr_params_pkg::*;
import ntt_defines_pkg::*;
import ntt_ctrl_ct_mlkem_pkg::*;
import ntt_ctrl_ct_mlkem_functions::*;


module fv_ntt_ctrl_ct_mlkem_ref_wrapper_m;


st_Request_and_Address mem_read_req_port;
assign mem_read_req_port = '{request: ntt_ctrl.mem_rd_en_reg, address: ntt_ctrl.mem_rd_addr};

st_Request_and_Address mem_write_req_port;
assign mem_write_req_port = '{request: ntt_ctrl.mem_wr_en_reg, address: ntt_ctrl.mem_wr_addr};

st_Request_and_Address read_req;
assign read_req = '{request: ntt_ctrl.mem_rd_en, address: ntt_ctrl.mem_rd_addr};

st_Request_and_Address write_req;
assign write_req = '{request: ntt_ctrl.mem_wr_en_reg, address: ntt_ctrl.mem_wr_addr};


fv_ntt_ctrl_ct_mlkem_m fv_ntt_ctrl_ct_mlkem(
  .rst_n(ntt_ctrl.reset_n),
  .clk(ntt_ctrl.clk),

  // Ports
  .base_address_port(ntt_ctrl.ntt_mem_base_addr),

  .buf0_valid_in(ntt_ctrl.buf0_valid),

  .buf_rdptr_reg_port(ntt_ctrl.buf_rdptr_reg[0]),

  .butterfly_ready_in(ntt_ctrl.butterfly_ready),

  .chunk_count_in(ntt_ctrl.chunk_count),

  .chunk_count_reg_port(ntt_ctrl.chunk_count_reg[0]),

  .chunk_rand_offset_in(ntt_ctrl.chunk_rand_offset),

  .latch_index_rand_offset_port(ntt_ctrl.latch_index_rand_offset),

  .mlkem_buf_rdptr_reg_port(ntt_ctrl.buf_rdptr_reg[4]),

  .mlkem_chunk_count_reg_port(ntt_ctrl.chunk_count_reg[4]),

  .mlkem_in(ntt_ctrl.mlkem),

  .ntt_enable_in(ntt_ctrl.ntt_enable),

  .random_in(ntt_ctrl.random),

  .rounds_count_in(ntt_ctrl.rounds_count),

  .shuffle_en_in(ntt_ctrl.shuffle_en),

  .bf_enable_out(ntt_ctrl.bf_enable_reg),

  .buf_rden_out(ntt_ctrl.buf_rden_ntt_reg),

  .buf_rdptr_f_out(ntt_ctrl.buf_rdptr_f),

  .buf_wren_out(ntt_ctrl.buf_wren_ntt_reg),

  .buf_wrptr_out(ntt_ctrl.buf_wrptr),

  .masking_en_ctrl_out(ntt_ctrl.masking_en_ctrl),

  .mem_read_req_port(mem_read_req_port),

  .mem_write_req_port(mem_write_req_port),

  .ntt_done_out(ntt_ctrl.ntt_done),

  .ntt_passthrough_out(ntt_ctrl.ntt_passthrough),

  .opcode_port(ntt_ctrl.opcode),

  .pw_rden_out(ntt_ctrl.pw_rden),

  .pw_wren_out(ntt_ctrl.pw_wren),

  .rounds_count_out(ntt_ctrl.rounds_count),

  .twiddle_addr_reg_out(ntt_ctrl.twiddle_addr_reg),

  // Registers
  .buf_count(ntt_ctrl.buf_count),
  .buf_rdptr_reg_1(ntt_ctrl.buf_rdptr_reg[10:0]),
  .chunk_count(ntt_ctrl.chunk_count),
  .chunk_count_reg_1(ntt_ctrl.chunk_count_reg[10:0]),
  .chunk_count_write(ntt_ctrl.chunk_count),
  .chunk_rand_offset_write(ntt_ctrl.chunk_rand_offset),
  .index_rand_offset(ntt_ctrl.index_rand_offset),
  .mem_rd_next_addr(ntt_ctrl.mem_rd_addr_nxt),
  .ntt_done(ntt_ctrl.ntt_done),
  .ntt_done_read(ntt_ctrl.ntt_done),
  .rd_valid_count(ntt_ctrl.rd_valid_count),
  .read_req(read_req),
  .read_state((ntt_ctrl.read_fsm_state_ps == RD_IDLE) ?CtReadIdle : ((ntt_ctrl.read_fsm_state_ps == RD_STAGE)?CtReadStage:(ntt_ctrl.read_fsm_state_ps == RD_BUF)?CtReadBuf:(ntt_ctrl.read_fsm_state_ps == RD_EXEC)?CtReadExec:CtReadExecwait)),
  .rounds_count_write(ntt_ctrl.rounds_count),
  .shuffle_en(ntt_ctrl.shuffle_en),
  .twiddle_addr_reg(ntt_ctrl.twiddle_addr_reg),
  .wr_stage_set( (ntt_ctrl.write_fsm_state_ps == WR_STAGE)),
  .wr_valid_count(ntt_ctrl.wr_valid_count),
  .write_req(write_req),
  .write_state((ntt_ctrl.write_fsm_state_ps == WR_IDLE) ? CtWriteIdle : ((ntt_ctrl.write_fsm_state_ps == WR_STAGE) ? CtWriteStage : CtWriteMem)),

  // States
  .read_buf((ntt_ctrl.read_fsm_state_ps == RD_BUF)),
  .read_exec((ntt_ctrl.read_fsm_state_ps == RD_EXEC) ),
  .read_exec_wait(ntt_ctrl.read_fsm_state_ps == EXEC_WAIT),
  .read_idle(ntt_ctrl.read_fsm_state_ps == RD_IDLE),
  .read_stage(ntt_ctrl.read_fsm_state_ps == RD_STAGE),
  .undriven_state(1'b1),
  .write_idle(ntt_ctrl.write_fsm_state_ps == WR_IDLE),
  .write_mem((ntt_ctrl.write_fsm_state_ps == WR_MEM) ),
  .write_stage((ntt_ctrl.write_fsm_state_ps == WR_STAGE) )
);


endmodule


bind ntt_ctrl fv_ntt_ctrl_ct_mlkem_ref_wrapper_m fv_ntt_ctrl_ct_mlkem_ref_wrapper();
