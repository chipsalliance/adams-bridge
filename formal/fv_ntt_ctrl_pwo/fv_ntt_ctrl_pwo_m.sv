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
// | Created on 13.03.2025 at 09:43                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import fv_ntt_ctrl_pwo_pkg::*;
import ntt_defines_pkg::*;
import fv_ntt_ctrl_pwo_functions::*;


module fv_ntt_ctrl_pwo_m(
  input logic rst_n,
  input logic clk,

  // Ports
  input logic unsigned [2:0] ntt_mode_in,

  input logic ntt_enable_in,

  input logic butterfly_ready_in,

  input logic sampler_valid_in,

  input logic accumulate_in,

  input logic shuffle_en_in,

  input st_PwoMemAddrs pwo_mem_base_addr_in,

  input logic unsigned [5:0] random_in,

  input logic unsigned [2:0] opcode_out,

  input logic masking_en_ctrl_out,

  input logic buf_wren_out,

  input logic buf_rden_out,

  input logic unsigned [1:0] buf_wrptr_out,

  input logic unsigned [1:0] buf_rdptr_out,

  input logic mem_rd_en_out,

  input logic mem_wr_en_out,

  input logic buf_wr_rst_count_out,

  input logic buf_rd_rst_count_out,

  input logic unsigned [14:0] pw_mem_rd_addr_a_out,

  input logic unsigned [14:0] pw_mem_rd_addr_b_out,

  input logic unsigned [14:0] pw_mem_rd_addr_c_out,

  input logic unsigned [14:0] pw_mem_wr_addr_c_out,

  input logic done_out,

  input logic rst_rounds_in,

  // Registers
  input logic bf_enable_reg,
  input logic bf_enable_reg_d2,
  input logic bf_enable_reg_d2_dummy,
  input logic unsigned [21:0] buf_rdptr_reg,
  input logic unsigned [3:0] chunk_count,
  input logic unsigned [43:0] chunk_count_reg,
  input logic unsigned [3:0] chunk_rand_offset,
  input logic unsigned [1:0] index_count,
  input logic unsigned [1:0] index_rand_offset,
  input logic unsigned [14:0] pw_mem_rd_addr_a_reg,
  input logic unsigned [14:0] pw_mem_rd_addr_b_reg,
  input logic unsigned [14:0] pw_mem_rd_addr_c_reg,
  input logic unsigned [14:0] pw_mem_wr_addr_c_reg,
  input logic pw_rden_reg,
  input logic pw_rden_reg_dummy,
  input logic pw_wren_reg,
  input logic pw_wren_reg_dummy,
  input logic unsigned [6:0] rd_valid_count,
  input e_PwoReadStatesType read_state,
  input logic unsigned [2:0] rounds_count,
  input logic unsigned [6:0] wr_valid_count,
  input e_PwoWriteStatesType write_state,

  // States
  input logic state,
  input logic read_idle,
  input logic read_stage,
  input logic read_exec,
  input logic read_exec_wait,
  input logic write_idle,
  input logic write_stage,
  input logic write_wait,
  input logic write_mem
);


default clocking default_clk @(posedge clk); endclocking


logic unsigned [1:0] getMemRdIndexOfst_0_i;
assign getMemRdIndexOfst_0_i = getMemRdIndexOfst(index_count, index_rand_offset);

logic unsigned [14:0] getPwAddrNxt_0_i;
assign getPwAddrNxt_0_i = getPwAddrNxt(pwo_mem_base_addr_in.pw_base_addr_a, chunk_count, 15'd1, 15'(getMemRdIndexOfst_0_i));

logic unsigned [14:0] getPwAddrNxt_1_i;
assign getPwAddrNxt_1_i = getPwAddrNxt(pwo_mem_base_addr_in.pw_base_addr_b, chunk_count, 15'd1, 15'(getMemRdIndexOfst_0_i));

logic unsigned [14:0] getPwAddrNxt_2_i;
assign getPwAddrNxt_2_i = getPwAddrNxt(pwo_mem_base_addr_in.pw_base_addr_c, chunk_count, 15'd1, 15'(getMemRdIndexOfst_0_i));

logic unsigned [14:0] getPwAddrRst_0_i;
assign getPwAddrRst_0_i = getPwAddrRst(shuffle_en_in, chunk_rand_offset, pwo_mem_base_addr_in.pw_base_addr_a);

logic unsigned [14:0] getPwAddrIncrAbcWr_0_i;
assign getPwAddrIncrAbcWr_0_i = getPwAddrIncrAbcWr(shuffle_en_in, getPwAddrNxt_0_i, pw_mem_rd_addr_a_reg, 15'd1);

logic unsigned [14:0] getPwAddrAbcWr_0_i;
assign getPwAddrAbcWr_0_i = getPwAddrAbcWr(((write_state == PwoWriteIdle) || (write_state == PwoWriteStage)), 0, getPwAddrRst_0_i, getPwAddrIncrAbcWr_0_i, pw_mem_rd_addr_a_reg);

logic unsigned [14:0] getPwAddrRst_1_i;
assign getPwAddrRst_1_i = getPwAddrRst(shuffle_en_in, chunk_rand_offset, pwo_mem_base_addr_in.pw_base_addr_b);

logic unsigned [14:0] getPwAddrIncrAbcWr_1_i;
assign getPwAddrIncrAbcWr_1_i = getPwAddrIncrAbcWr(shuffle_en_in, getPwAddrNxt_1_i, pw_mem_rd_addr_b_reg, 15'd1);

logic unsigned [14:0] getPwAddrAbcWr_1_i;
assign getPwAddrAbcWr_1_i = getPwAddrAbcWr(((write_state == PwoWriteIdle) || (write_state == PwoWriteStage)), 0, getPwAddrRst_1_i, getPwAddrIncrAbcWr_1_i, pw_mem_rd_addr_b_reg);

logic unsigned [14:0] getPwAddrRst_2_i;
assign getPwAddrRst_2_i = getPwAddrRst(shuffle_en_in, chunk_rand_offset, pwo_mem_base_addr_in.pw_base_addr_c);

logic unsigned [14:0] getPwAddrCrd_0_i;
assign getPwAddrCrd_0_i = getPwAddrCrd(shuffle_en_in, accumulate_in, ((write_state == PwoWriteIdle) || (write_state == PwoWriteStage)), 0, getPwAddrRst_2_i, getPwAddrNxt_2_i, pw_mem_rd_addr_c_reg, 15'd1);

logic unsigned [14:0] getPwAddrAbcWr_2_i;
assign getPwAddrAbcWr_2_i = getPwAddrAbcWr(((write_state == PwoWriteIdle) || (write_state == PwoWriteStage)), sampler_valid_in, getPwAddrRst_0_i, getPwAddrIncrAbcWr_0_i, pw_mem_rd_addr_a_reg);

logic unsigned [14:0] getPwAddrAbcWr_3_i;
assign getPwAddrAbcWr_3_i = getPwAddrAbcWr(((write_state == PwoWriteIdle) || (write_state == PwoWriteStage)), sampler_valid_in, getPwAddrRst_1_i, getPwAddrIncrAbcWr_1_i, pw_mem_rd_addr_b_reg);

logic unsigned [14:0] getPwAddrCrd_1_i;
assign getPwAddrCrd_1_i = getPwAddrCrd(shuffle_en_in, accumulate_in, ((write_state == PwoWriteIdle) || (write_state == PwoWriteStage)), sampler_valid_in, getPwAddrRst_2_i, getPwAddrNxt_2_i, pw_mem_rd_addr_c_reg, 15'd1);

logic unsigned [14:0] getPwAddrNxt_3_i;
assign getPwAddrNxt_3_i = getPwAddrNxt(pwo_mem_base_addr_in.pw_base_addr_c, (accumulate_in ? chunk_count_reg[15:12] : (((ntt_mode_in == 3'd3) || (ntt_mode_in == 3'd4)) ? chunk_count_reg[31:28] : chunk_count_reg[19:16])), 15'd1, 15'((accumulate_in ? buf_rdptr_reg[7:6] : (((ntt_mode_in == 3'd3) || (ntt_mode_in == 3'd4)) ? buf_rdptr_reg[15:14] : buf_rdptr_reg[9:8]))));

logic unsigned [14:0] getPwAddrIncrAbcWr_2_i;
assign getPwAddrIncrAbcWr_2_i = getPwAddrIncrAbcWr(shuffle_en_in, getPwAddrNxt_3_i, pw_mem_wr_addr_c_reg, 15'd1);

logic unsigned [14:0] getPwAddrAbcWr_4_i;
assign getPwAddrAbcWr_4_i = getPwAddrAbcWr(1, (((write_state == PwoWriteMem) && butterfly_ready_in) || ((write_state == PwoWriteWait) && (butterfly_ready_in || shuffle_en_in))), getPwAddrRst_2_i, getPwAddrIncrAbcWr_2_i, pw_mem_wr_addr_c_reg);

logic unsigned [14:0] getPwAddrAbcWr_5_i;
assign getPwAddrAbcWr_5_i = getPwAddrAbcWr(0, (((write_state == PwoWriteMem) && butterfly_ready_in) || ((write_state == PwoWriteWait) && (butterfly_ready_in || shuffle_en_in))), getPwAddrRst_2_i, getPwAddrIncrAbcWr_2_i, pw_mem_wr_addr_c_reg);


sequence reset_sequence;
  //!rst_n ##1 rst_n;
   $past(!rst_n);
endsequence


property commons_reset_p;
  reset_sequence |->
  state &&
  buf_rd_rst_count_out == 1 &&
  buf_rden_out == 0 &&
  buf_rdptr_out == 2'd0 &&
  buf_wr_rst_count_out == 1 &&
  buf_wren_out == 0 &&
  buf_wrptr_out == 2'd0 &&
  masking_en_ctrl_out == 0 &&
  mem_rd_en_out == 0 &&
  mem_wr_en_out == 0 &&
  opcode_out == 3'd0;
endproperty
commons_reset_a: assert property (commons_reset_p);


property read_reset_p;
  reset_sequence |->
  read_idle &&
  bf_enable_reg == 0 &&
  bf_enable_reg_d2 == 0 &&
  buf_rdptr_reg == 22'd0 &&
  chunk_count_reg == 44'd0 &&
  pw_mem_rd_addr_a_out == 15'd0 &&
  pw_mem_rd_addr_a_reg == 15'd0 &&
  pw_mem_rd_addr_b_out == 15'd0 &&
  pw_mem_rd_addr_b_reg == 15'd0 &&
  pw_mem_rd_addr_c_out == 15'd0 &&
  pw_mem_rd_addr_c_reg == 15'd0 &&
  pw_rden_reg == 0 &&
  rd_valid_count == 7'd0 &&
  read_state == PwoReadIdle;
endproperty
read_reset_a: assert property (read_reset_p);


property write_reset_p;
  reset_sequence |->
  write_idle &&
  chunk_count == 4'd0 &&
  chunk_rand_offset == 4'd0 &&
  done_out == 0 &&
  index_count == 2'd0 &&
  index_rand_offset == 2'd0 &&
  pw_mem_wr_addr_c_out == 15'd0 &&
  pw_mem_wr_addr_c_reg == 15'd0 &&
  pw_wren_reg == 0 &&
  rounds_count == 3'd0 &&
  wr_valid_count == 7'd0 &&
  write_state == PwoWriteIdle;
endproperty
write_reset_a: assert property (write_reset_p);


property commons_state_to_state_p;
  state
|->
  ##1 ($stable(buf_rd_rst_count_out)) and
  ##1 ($stable(buf_rden_out)) and
  ##1 ($stable(buf_rdptr_out)) and
  ##1 ($stable(buf_wr_rst_count_out)) and
  ##1 ($stable(buf_wren_out)) and
  ##1 ($stable(buf_wrptr_out)) and
  ##1 ($stable(masking_en_ctrl_out)) and
  ##1 ($stable(mem_rd_en_out)) and
  ##1 ($stable(mem_wr_en_out)) and
  ##1
  state &&
  opcode_out == $past(ntt_mode_in, 1);
endproperty
commons_state_to_state_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) commons_state_to_state_p);


property read_read_exec_to_read_exec_p;
  read_exec &&
  (sampler_valid_in || (({ 57'h0, rd_valid_count} ) >= 64'h40)) &&
  (rd_valid_count < 7'h3F)
|->
  ##1
  read_exec &&
  bf_enable_reg == ((($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait)) && $past(sampler_valid_in, 1)) &&
  bf_enable_reg_d2 == $past(bf_enable_reg, 1) &&
  buf_rdptr_reg == ({ { 22'({ $past(getMemRdIndexOfst_0_i, 1) }) }[1:0], { $past(buf_rdptr_reg, 1) }[21:2]} ) &&
  chunk_count_reg == ({ { 44'({ $past(chunk_count, 1) }) }[3:0], { $past(chunk_count_reg, 1) }[43:4]} ) &&
  pw_mem_rd_addr_a_out == $past(getPwAddrAbcWr_2_i, 1) &&
  pw_mem_rd_addr_a_reg == $past(getPwAddrAbcWr_2_i, 1) &&
  pw_mem_rd_addr_b_out == $past(getPwAddrAbcWr_3_i, 1) &&
  pw_mem_rd_addr_b_reg == $past(getPwAddrAbcWr_3_i, 1) &&
  pw_mem_rd_addr_c_out == $past(getPwAddrCrd_1_i, 1) &&
  pw_mem_rd_addr_c_reg == $past(getPwAddrCrd_1_i, 1) &&
  pw_rden_reg == ($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) &&
  rd_valid_count == 7'(((($past(read_state, 1) == PwoReadIdle) || ($past(read_state, 1) == PwoReadStage)) ? 64'd0 : 7'((64'd1 + ({ 57'd0, $past(rd_valid_count, 1)} ))))) &&
  read_state == PwoReadExec;
endproperty
read_read_exec_to_read_exec_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) read_read_exec_to_read_exec_p);


property read_read_exec_to_read_exec_wait_p;
  read_exec &&
  !sampler_valid_in &&
  (({ 57'h0, rd_valid_count} ) < 64'h40)
|->
  ##1
  read_exec_wait &&
  bf_enable_reg == ((($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait)) && $past(sampler_valid_in, 1)) &&
  bf_enable_reg_d2 == $past(bf_enable_reg, 1) &&
  buf_rdptr_reg == (($past(sampler_valid_in, 1) || $past(butterfly_ready_in, 1)) ? ({ { 22'({ $past(getMemRdIndexOfst_0_i, 1) }) }[1:0], { $past(buf_rdptr_reg, 1) }[21:2]} ) : 22'd0) &&
  chunk_count_reg == (($past(sampler_valid_in, 1) || $past(butterfly_ready_in, 1)) ? ({ { 44'({ $past(chunk_count, 1) }) }[3:0], { $past(chunk_count_reg, 1) }[43:4]} ) : $past(chunk_count_reg, 1)) &&
  pw_mem_rd_addr_a_out == $past(getPwAddrAbcWr_2_i, 1) &&
  pw_mem_rd_addr_a_reg == $past(getPwAddrAbcWr_2_i, 1) &&
  pw_mem_rd_addr_b_out == $past(getPwAddrAbcWr_3_i, 1) &&
  pw_mem_rd_addr_b_reg == $past(getPwAddrAbcWr_3_i, 1) &&
  pw_mem_rd_addr_c_out == $past(getPwAddrCrd_1_i, 1) &&
  pw_mem_rd_addr_c_reg == $past(getPwAddrCrd_1_i, 1) &&
  pw_rden_reg == ($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) &&
  rd_valid_count == ((($past(read_state, 1) == PwoReadIdle) || ($past(read_state, 1) == PwoReadStage)) ? 7'd0 : $past(rd_valid_count, 1)) &&
  read_state == PwoReadExecWait;
endproperty
read_read_exec_to_read_exec_wait_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) read_read_exec_to_read_exec_wait_p);


property read_read_exec_to_read_stage_p;
  read_exec &&
  (sampler_valid_in || (({ 57'h0, rd_valid_count} ) >= 64'h40)) &&
  (rd_valid_count >= 7'h3F)
|->
  ##1
  read_stage &&
  bf_enable_reg == ((($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait)) && $past(sampler_valid_in, 1)) &&
  bf_enable_reg_d2 == $past(bf_enable_reg, 1) &&
  buf_rdptr_reg == (($past(sampler_valid_in, 1) || $past(butterfly_ready_in, 1)) ? ({ { 22'({ $past(getMemRdIndexOfst_0_i, 1) }) }[1:0], { $past(buf_rdptr_reg, 1) }[21:2]} ) : 22'd0) &&
  chunk_count_reg == (($past(sampler_valid_in, 1) || $past(butterfly_ready_in, 1)) ? ({ { 44'({ $past(chunk_count, 1) }) }[3:0], { $past(chunk_count_reg, 1) }[43:4]} ) : $past(chunk_count_reg, 1)) &&
  pw_mem_rd_addr_a_out == $past(getPwAddrAbcWr_2_i, 1) &&
  pw_mem_rd_addr_a_reg == $past(getPwAddrAbcWr_2_i, 1) &&
  pw_mem_rd_addr_b_out == $past(getPwAddrAbcWr_3_i, 1) &&
  pw_mem_rd_addr_b_reg == $past(getPwAddrAbcWr_3_i, 1) &&
  pw_mem_rd_addr_c_out == $past(getPwAddrCrd_1_i, 1) &&
  pw_mem_rd_addr_c_reg == $past(getPwAddrCrd_1_i, 1) &&
  pw_rden_reg == ($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) &&
  rd_valid_count == 7'(((($past(read_state, 1) == PwoReadIdle) || ($past(read_state, 1) == PwoReadStage)) ? 64'd0 : ($past(sampler_valid_in, 1) ? 7'((64'd1 + ({ 57'd0, $past(rd_valid_count, 1)} ))) : ({ 57'd0, $past(rd_valid_count, 1)} )))) &&
  read_state == PwoReadStage;
endproperty
read_read_exec_to_read_stage_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) read_read_exec_to_read_stage_p);


property read_read_exec_wait_to_read_exec_p;
  read_exec_wait &&
  sampler_valid_in
|->
  ##1
  read_exec &&
  bf_enable_reg == ((($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait)) && $past(sampler_valid_in, 1)) &&
  bf_enable_reg_d2 == $past(bf_enable_reg, 1) &&
  buf_rdptr_reg == ({ { 22'({ $past(getMemRdIndexOfst_0_i, 1) }) }[1:0], { $past(buf_rdptr_reg, 1) }[21:2]} ) &&
  chunk_count_reg == ({ { 44'({ $past(chunk_count, 1) }) }[3:0], { $past(chunk_count_reg, 1) }[43:4]} ) &&
  pw_mem_rd_addr_a_out == $past(getPwAddrAbcWr_2_i, 1) &&
  pw_mem_rd_addr_a_reg == $past(getPwAddrAbcWr_2_i, 1) &&
  pw_mem_rd_addr_b_out == $past(getPwAddrAbcWr_3_i, 1) &&
  pw_mem_rd_addr_b_reg == $past(getPwAddrAbcWr_3_i, 1) &&
  pw_mem_rd_addr_c_out == $past(getPwAddrCrd_1_i, 1) &&
  pw_mem_rd_addr_c_reg == $past(getPwAddrCrd_1_i, 1) &&
  pw_rden_reg == ($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) &&
  rd_valid_count == 7'(((($past(read_state, 1) == PwoReadIdle) || ($past(read_state, 1) == PwoReadStage)) ? 64'd0 : 7'((64'd1 + ({ 57'd0, $past(rd_valid_count, 1)} ))))) &&
  read_state == PwoReadExec;
endproperty
read_read_exec_wait_to_read_exec_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) read_read_exec_wait_to_read_exec_p);


property read_read_exec_wait_to_read_exec_wait_p;
  read_exec_wait &&
  !sampler_valid_in
|->
  ##1
  read_exec_wait &&
  bf_enable_reg == ((($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait)) && $past(sampler_valid_in, 1)) &&
  bf_enable_reg_d2 == $past(bf_enable_reg, 1) &&
  buf_rdptr_reg == (($past(sampler_valid_in, 1) || $past(butterfly_ready_in, 1)) ? ({ { 22'({ $past(getMemRdIndexOfst_0_i, 1) }) }[1:0], { $past(buf_rdptr_reg, 1) }[21:2]} ) : 22'd0) &&
  chunk_count_reg == (($past(sampler_valid_in, 1) || $past(butterfly_ready_in, 1)) ? ({ { 44'({ $past(chunk_count, 1) }) }[3:0], { $past(chunk_count_reg, 1) }[43:4]} ) : $past(chunk_count_reg, 1)) &&
  pw_mem_rd_addr_a_out == $past(getPwAddrAbcWr_2_i, 1) &&
  pw_mem_rd_addr_a_reg == $past(getPwAddrAbcWr_2_i, 1) &&
  pw_mem_rd_addr_b_out == $past(getPwAddrAbcWr_3_i, 1) &&
  pw_mem_rd_addr_b_reg == $past(getPwAddrAbcWr_3_i, 1) &&
  pw_mem_rd_addr_c_out == $past(getPwAddrCrd_1_i, 1) &&
  pw_mem_rd_addr_c_reg == $past(getPwAddrCrd_1_i, 1) &&
  pw_rden_reg == ($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) &&
  rd_valid_count == ((($past(read_state, 1) == PwoReadIdle) || ($past(read_state, 1) == PwoReadStage)) ? 7'd0 : $past(rd_valid_count, 1)) &&
  read_state == PwoReadExecWait;
endproperty
read_read_exec_wait_to_read_exec_wait_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) read_read_exec_wait_to_read_exec_wait_p);


property read_read_idle_to_read_idle_p;
  read_idle &&
  !ntt_enable_in
|->
  ##1
  read_idle &&
  bf_enable_reg == ((($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait)) && $past(sampler_valid_in, 1)) &&
  bf_enable_reg_d2 == $past(bf_enable_reg, 1) &&
  buf_rdptr_reg == ($past(butterfly_ready_in, 1) ? ({ { 22'({ $past(getMemRdIndexOfst_0_i, 1) }) }[1:0], { $past(buf_rdptr_reg, 1) }[21:2]} ) : 22'd0) &&
  chunk_count_reg == ($past(butterfly_ready_in, 1) ? ({ { 44'({ $past(chunk_count, 1) }) }[3:0], { $past(chunk_count_reg, 1) }[43:4]} ) : $past(chunk_count_reg, 1)) &&
  pw_mem_rd_addr_a_out == $past(getPwAddrAbcWr_0_i, 1) &&
  pw_mem_rd_addr_a_reg == $past(getPwAddrAbcWr_0_i, 1) &&
  pw_mem_rd_addr_b_out == $past(getPwAddrAbcWr_1_i, 1) &&
  pw_mem_rd_addr_b_reg == $past(getPwAddrAbcWr_1_i, 1) &&
  pw_mem_rd_addr_c_out == $past(getPwAddrCrd_0_i, 1) &&
  pw_mem_rd_addr_c_reg == $past(getPwAddrCrd_0_i, 1) &&
  pw_rden_reg == ($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) &&
  rd_valid_count == 7'(((($past(read_state, 1) == PwoReadIdle) || ($past(read_state, 1) == PwoReadStage)) ? 64'd0 : ($past(sampler_valid_in, 1) ? 7'((64'd1 + ({ 57'd0, $past(rd_valid_count, 1)} ))) : ({ 57'd0, $past(rd_valid_count, 1)} )))) &&
  read_state == PwoReadIdle;
endproperty
read_read_idle_to_read_idle_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) read_read_idle_to_read_idle_p);


property read_read_idle_to_read_stage_p;
  read_idle &&
  ntt_enable_in
|->
  ##1
  read_stage &&
  bf_enable_reg == ((($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait)) && $past(sampler_valid_in, 1)) &&
  bf_enable_reg_d2 == $past(bf_enable_reg, 1) &&
  buf_rdptr_reg == ($past(butterfly_ready_in, 1) ? ({ { 22'({ $past(getMemRdIndexOfst_0_i, 1) }) }[1:0], { $past(buf_rdptr_reg, 1) }[21:2]} ) : 22'd0) &&
  chunk_count_reg == ($past(butterfly_ready_in, 1) ? ({ { 44'({ $past(chunk_count, 1) }) }[3:0], { $past(chunk_count_reg, 1) }[43:4]} ) : $past(chunk_count_reg, 1)) &&
  pw_mem_rd_addr_a_out == $past(getPwAddrAbcWr_0_i, 1) &&
  pw_mem_rd_addr_a_reg == $past(getPwAddrAbcWr_0_i, 1) &&
  pw_mem_rd_addr_b_out == $past(getPwAddrAbcWr_1_i, 1) &&
  pw_mem_rd_addr_b_reg == $past(getPwAddrAbcWr_1_i, 1) &&
  pw_mem_rd_addr_c_out == $past(getPwAddrCrd_0_i, 1) &&
  pw_mem_rd_addr_c_reg == $past(getPwAddrCrd_0_i, 1) &&
  pw_rden_reg == ($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) &&
  rd_valid_count == 7'(((($past(read_state, 1) == PwoReadIdle) || ($past(read_state, 1) == PwoReadStage)) ? 64'd0 : ($past(sampler_valid_in, 1) ? 7'((64'd1 + ({ 57'd0, $past(rd_valid_count, 1)} ))) : ({ 57'd0, $past(rd_valid_count, 1)} )))) &&
  read_state == PwoReadStage;
endproperty
read_read_idle_to_read_stage_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) read_read_idle_to_read_stage_p);


property read_read_stage_to_read_exec_p;
  read_stage &&
  ((rounds_count != 3'd1) || ntt_enable_in) &&
  (write_state == PwoWriteStage) &&
  (rounds_count != 3'd1)
|->
  ##1
  read_exec &&
  bf_enable_reg == ((($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait)) && $past(sampler_valid_in, 1)) &&
  bf_enable_reg_d2 == $past(bf_enable_reg, 1) &&
  buf_rdptr_reg == ($past(butterfly_ready_in, 1) ? ({ { 22'({ $past(getMemRdIndexOfst_0_i, 1) }) }[1:0], { $past(buf_rdptr_reg, 1) }[21:2]} ) : 22'd0) &&
  chunk_count_reg == ($past(butterfly_ready_in, 1) ? ({ { 44'({ $past(chunk_count, 1) }) }[3:0], { $past(chunk_count_reg, 1) }[43:4]} ) : $past(chunk_count_reg, 1)) &&
  pw_mem_rd_addr_a_out == $past(getPwAddrAbcWr_0_i, 1) &&
  pw_mem_rd_addr_a_reg == $past(getPwAddrAbcWr_0_i, 1) &&
  pw_mem_rd_addr_b_out == $past(getPwAddrAbcWr_1_i, 1) &&
  pw_mem_rd_addr_b_reg == $past(getPwAddrAbcWr_1_i, 1) &&
  pw_mem_rd_addr_c_out == $past(getPwAddrCrd_0_i, 1) &&
  pw_mem_rd_addr_c_reg == $past(getPwAddrCrd_0_i, 1) &&
  pw_rden_reg == ($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) &&
  rd_valid_count == 7'(((($past(read_state, 1) == PwoReadIdle) || ($past(read_state, 1) == PwoReadStage)) ? 64'd0 : ($past(sampler_valid_in, 1) ? 7'((64'd1 + ({ 57'd0, $past(rd_valid_count, 1)} ))) : ({ 57'd0, $past(rd_valid_count, 1)} )))) &&
  read_state == PwoReadExec;
endproperty
read_read_stage_to_read_exec_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) read_read_stage_to_read_exec_p);


property read_read_stage_to_read_idle_p;
  read_stage &&
  (rounds_count == 3'd1) &&
  !ntt_enable_in
|->
  ##1
  read_idle &&
  bf_enable_reg == ((($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait)) && $past(sampler_valid_in, 1)) &&
  bf_enable_reg_d2 == $past(bf_enable_reg, 1) &&
  buf_rdptr_reg == ($past(butterfly_ready_in, 1) ? ({ { 22'({ $past(getMemRdIndexOfst_0_i, 1) }) }[1:0], { $past(buf_rdptr_reg, 1) }[21:2]} ) : 22'd0) &&
  chunk_count_reg == ($past(butterfly_ready_in, 1) ? ({ { 44'({ $past(chunk_count, 1) }) }[3:0], { $past(chunk_count_reg, 1) }[43:4]} ) : $past(chunk_count_reg, 1)) &&
  pw_mem_rd_addr_a_out == $past(getPwAddrAbcWr_0_i, 1) &&
  pw_mem_rd_addr_a_reg == $past(getPwAddrAbcWr_0_i, 1) &&
  pw_mem_rd_addr_b_out == $past(getPwAddrAbcWr_1_i, 1) &&
  pw_mem_rd_addr_b_reg == $past(getPwAddrAbcWr_1_i, 1) &&
  pw_mem_rd_addr_c_out == $past(getPwAddrCrd_0_i, 1) &&
  pw_mem_rd_addr_c_reg == $past(getPwAddrCrd_0_i, 1) &&
  pw_rden_reg == ($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) &&
  rd_valid_count == 7'(((($past(read_state, 1) == PwoReadIdle) || ($past(read_state, 1) == PwoReadStage)) ? 64'd0 : ($past(sampler_valid_in, 1) ? 7'((64'd1 + ({ 57'd0, $past(rd_valid_count, 1)} ))) : ({ 57'd0, $past(rd_valid_count, 1)} )))) &&
  read_state == PwoReadIdle;
endproperty
read_read_stage_to_read_idle_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) read_read_stage_to_read_idle_p);


property read_read_stage_to_read_stage_p;
  read_stage &&
  ((rounds_count != 3'd1) || ntt_enable_in) &&
  !((write_state == PwoWriteStage) && (rounds_count != 3'd1))
|->
  ##1
  read_stage &&
  bf_enable_reg == ((($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait)) && $past(sampler_valid_in, 1)) &&
  bf_enable_reg_d2 == $past(bf_enable_reg, 1) &&
  buf_rdptr_reg == ($past(butterfly_ready_in, 1) ? ({ { 22'({ $past(getMemRdIndexOfst_0_i, 1) }) }[1:0], { $past(buf_rdptr_reg, 1) }[21:2]} ) : 22'd0) &&
  chunk_count_reg == ($past(butterfly_ready_in, 1) ? ({ { 44'({ $past(chunk_count, 1) }) }[3:0], { $past(chunk_count_reg, 1) }[43:4]} ) : $past(chunk_count_reg, 1)) &&
  pw_mem_rd_addr_a_out == $past(getPwAddrAbcWr_0_i, 1) &&
  pw_mem_rd_addr_a_reg == $past(getPwAddrAbcWr_0_i, 1) &&
  pw_mem_rd_addr_b_out == $past(getPwAddrAbcWr_1_i, 1) &&
  pw_mem_rd_addr_b_reg == $past(getPwAddrAbcWr_1_i, 1) &&
  pw_mem_rd_addr_c_out == $past(getPwAddrCrd_0_i, 1) &&
  pw_mem_rd_addr_c_reg == $past(getPwAddrCrd_0_i, 1) &&
  pw_rden_reg == ($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) &&
  rd_valid_count == 7'(((($past(read_state, 1) == PwoReadIdle) || ($past(read_state, 1) == PwoReadStage)) ? 64'd0 : ($past(sampler_valid_in, 1) ? 7'((64'd1 + ({ 57'd0, $past(rd_valid_count, 1)} ))) : ({ 57'd0, $past(rd_valid_count, 1)} )))) &&
  read_state == PwoReadStage;
endproperty
read_read_stage_to_read_stage_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) read_read_stage_to_read_stage_p);


property write_write_idle_to_write_idle_p;
  write_idle &&
  !ntt_enable_in
|->
  ##1
  write_idle &&
  chunk_count == ((($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) && ($past(index_count, 1) == 2'h3)) ? 4'((64'd1 + ({ 60'h0, $past(chunk_count, 1)} ))) : ({ 60'h0, $past(chunk_count, 1)} )) &&
  $stable(chunk_rand_offset) &&
  done_out == (($past(rst_rounds_in, 1) ? 3'd0 : (($past(rounds_count, 1) == 3'd1) ? 3'd0 : $past(rounds_count, 1))) == 3'd1) &&
  index_count == (($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) ? 2'((64'd1 + ({ 62'h0, $past(index_count, 1)} ))) : ({ 62'h0, $past(index_count, 1)} )) &&
  index_rand_offset == ((($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) && ($past(index_count, 1) == 2'h3)) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  pw_mem_wr_addr_c_out == $past(getPwAddrAbcWr_4_i, 1) &&
  pw_mem_wr_addr_c_reg == $past(getPwAddrAbcWr_4_i, 1) &&
  pw_wren_reg == ((($past(write_state, 1) == PwoWriteMem) && $past(butterfly_ready_in, 1)) || ((($past(write_state, 1) == PwoWriteWait) && $past(butterfly_ready_in, 1)) && !$past(shuffle_en_in, 1))) &&
  rounds_count == ($past(rst_rounds_in, 1) ? 3'd0 : (($past(rounds_count, 1) == 3'd1) ? 3'd0 : $past(rounds_count, 1))) &&
  wr_valid_count == 7'(((($past(write_state, 1) == PwoWriteIdle) || ($past(write_state, 1) == PwoWriteStage)) ? 64'd0 : ($past(butterfly_ready_in, 1) ? 7'((64'd1 + ({ 57'd0, $past(wr_valid_count, 1)} ))) : ({ 57'd0, $past(wr_valid_count, 1)} )))) &&
  write_state == PwoWriteIdle;
endproperty
write_write_idle_to_write_idle_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) write_write_idle_to_write_idle_p);


property write_write_idle_to_write_stage_p;
  write_idle &&
  ntt_enable_in
|->
  ##1
  write_stage &&
  chunk_count == { $past(random_in, 1) }[5:2] &&
  chunk_rand_offset == { $past(random_in, 1) }[5:2] &&
  done_out == (($past(rst_rounds_in, 1) ? 3'd0 : (($past(rounds_count, 1) == 3'd1) ? 3'd0 : $past(rounds_count, 1))) == 3'd1) &&
  index_count == (($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) ? 2'((64'd1 + ({ 62'h0, $past(index_count, 1)} ))) : ({ 62'h0, $past(index_count, 1)} )) &&
  index_rand_offset == ((($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) && ($past(index_count, 1) == 2'h3)) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  pw_mem_wr_addr_c_out == $past(getPwAddrAbcWr_4_i, 1) &&
  pw_mem_wr_addr_c_reg == $past(getPwAddrAbcWr_4_i, 1) &&
  pw_wren_reg == ((($past(write_state, 1) == PwoWriteMem) && $past(butterfly_ready_in, 1)) || ((($past(write_state, 1) == PwoWriteWait) && $past(butterfly_ready_in, 1)) && !$past(shuffle_en_in, 1))) &&
  rounds_count == ($past(rst_rounds_in, 1) ? 3'd0 : (($past(rounds_count, 1) == 3'd1) ? 3'd0 : $past(rounds_count, 1))) &&
  wr_valid_count == 7'(((($past(write_state, 1) == PwoWriteIdle) || ($past(write_state, 1) == PwoWriteStage)) ? 64'd0 : ($past(butterfly_ready_in, 1) ? 7'((64'd1 + ({ 57'd0, $past(wr_valid_count, 1)} ))) : ({ 57'd0, $past(wr_valid_count, 1)} )))) &&
  write_state == PwoWriteStage;
endproperty
write_write_idle_to_write_stage_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) write_write_idle_to_write_stage_p);


property write_write_mem_to_write_mem_p;
  write_mem &&
  ((shuffle_en_in || butterfly_ready_in) || (({ 57'h0, wr_valid_count} ) >= 64'h40)) &&
  !((shuffle_en_in && butterfly_ready_in) && (wr_valid_count == 7'h3F)) &&
  (shuffle_en_in || (wr_valid_count != 7'h40))
|->
  ##1
  write_mem &&
  chunk_count == ((($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) && ($past(index_count, 1) == 2'h3)) ? 4'((64'd1 + ({ 60'h0, $past(chunk_count, 1)} ))) : ({ 60'h0, $past(chunk_count, 1)} )) &&
  $stable(chunk_rand_offset) &&
  done_out == (($past(rst_rounds_in, 1) ? 3'd0 : (($past(rounds_count, 1) == 3'd1) ? 3'd0 : $past(rounds_count, 1))) == 3'd1) &&
  index_count == (($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) ? 2'((64'd1 + ({ 62'h0, $past(index_count, 1)} ))) : ({ 62'h0, $past(index_count, 1)} )) &&
  index_rand_offset == ((($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) && ($past(index_count, 1) == 2'h3)) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  pw_mem_wr_addr_c_out == $past(getPwAddrAbcWr_5_i, 1) &&
  pw_mem_wr_addr_c_reg == $past(getPwAddrAbcWr_5_i, 1) &&
  pw_wren_reg == ((($past(write_state, 1) == PwoWriteMem) && $past(butterfly_ready_in, 1)) || ((($past(write_state, 1) == PwoWriteWait) && $past(butterfly_ready_in, 1)) && !$past(shuffle_en_in, 1))) &&
  rounds_count == ($past(rst_rounds_in, 1) ? 3'd0 : (($past(rounds_count, 1) == 3'd1) ? 3'd0 : $past(rounds_count, 1))) &&
  wr_valid_count == 7'(((($past(write_state, 1) == PwoWriteIdle) || ($past(write_state, 1) == PwoWriteStage)) ? 64'd0 : ($past(butterfly_ready_in, 1) ? 7'((64'd1 + ({ 57'd0, $past(wr_valid_count, 1)} ))) : ({ 57'd0, $past(wr_valid_count, 1)} )))) &&
  write_state == PwoWriteMem;
endproperty
write_write_mem_to_write_mem_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) write_write_mem_to_write_mem_p);


property write_write_mem_to_write_stage_p;
  write_mem &&
  ((shuffle_en_in || butterfly_ready_in) || (({ 57'h0, wr_valid_count} ) >= 64'h40)) &&
  !((shuffle_en_in && butterfly_ready_in) && (wr_valid_count == 7'h3F)) &&
  !shuffle_en_in &&
  (wr_valid_count == 7'h40)
|->
  ##1
  write_stage &&
  chunk_count == { $past(random_in, 1) }[5:2] &&
  chunk_rand_offset == { $past(random_in, 1) }[5:2] &&
  done_out == (($past(rst_rounds_in, 1) ? 64'd0 : ((({ 61'd0, $past(rounds_count, 1)} ) < 64'd1) ? 3'((64'd1 + ({ 61'd0, $past(rounds_count, 1)} ))) : (($past(rounds_count, 1) == 3'd1) ? 64'd0 : ({ 61'd0, $past(rounds_count, 1)} )))) == 64'd1) &&
  index_count == (($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) ? 2'((64'd1 + ({ 62'h0, $past(index_count, 1)} ))) : ({ 62'h0, $past(index_count, 1)} )) &&
  index_rand_offset == ((($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) && ($past(index_count, 1) == 2'h3)) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  pw_mem_wr_addr_c_out == $past(getPwAddrAbcWr_5_i, 1) &&
  pw_mem_wr_addr_c_reg == $past(getPwAddrAbcWr_5_i, 1) &&
  pw_wren_reg == ((($past(write_state, 1) == PwoWriteMem) && $past(butterfly_ready_in, 1)) || ((($past(write_state, 1) == PwoWriteWait) && $past(butterfly_ready_in, 1)) && !$past(shuffle_en_in, 1))) &&
  rounds_count == 3'(($past(rst_rounds_in, 1) ? 64'd0 : ((({ 61'd0, $past(rounds_count, 1)} ) < 64'd1) ? 3'((64'd1 + ({ 61'd0, $past(rounds_count, 1)} ))) : (($past(rounds_count, 1) == 3'd1) ? 64'd0 : ({ 61'd0, $past(rounds_count, 1)} ))))) &&
  wr_valid_count == 7'(((($past(write_state, 1) == PwoWriteIdle) || ($past(write_state, 1) == PwoWriteStage)) ? 64'd0 : ($past(butterfly_ready_in, 1) ? 7'((64'd1 + ({ 57'd0, $past(wr_valid_count, 1)} ))) : ({ 57'd0, $past(wr_valid_count, 1)} )))) &&
  write_state == PwoWriteStage;
endproperty
write_write_mem_to_write_stage_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) write_write_mem_to_write_stage_p);


property write_write_mem_to_write_wait_p;
  write_mem &&
  ((!(shuffle_en_in || butterfly_ready_in) && (({ 57'h0, wr_valid_count} ) < 64'h40)) || ((shuffle_en_in && butterfly_ready_in) && (wr_valid_count == 7'h3F)))
|->
  ##1
  write_wait &&
  chunk_count == ((($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) && ($past(index_count, 1) == 2'h3)) ? 4'((64'd1 + ({ 60'h0, $past(chunk_count, 1)} ))) : ({ 60'h0, $past(chunk_count, 1)} )) &&
  $stable(chunk_rand_offset) &&
  done_out == (($past(rst_rounds_in, 1) ? 3'd0 : (($past(rounds_count, 1) == 3'd1) ? 3'd0 : $past(rounds_count, 1))) == 3'd1) &&
  index_count == (($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) ? 2'((64'd1 + ({ 62'h0, $past(index_count, 1)} ))) : ({ 62'h0, $past(index_count, 1)} )) &&
  index_rand_offset == ((($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) && ($past(index_count, 1) == 2'h3)) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  pw_mem_wr_addr_c_out == $past(getPwAddrAbcWr_5_i, 1) &&
  pw_mem_wr_addr_c_reg == $past(getPwAddrAbcWr_5_i, 1) &&
  pw_wren_reg == ((($past(write_state, 1) == PwoWriteMem) && $past(butterfly_ready_in, 1)) || ((($past(write_state, 1) == PwoWriteWait) && $past(butterfly_ready_in, 1)) && !$past(shuffle_en_in, 1))) &&
  rounds_count == ($past(rst_rounds_in, 1) ? 3'd0 : (($past(rounds_count, 1) == 3'd1) ? 3'd0 : $past(rounds_count, 1))) &&
  wr_valid_count == 7'(((($past(write_state, 1) == PwoWriteIdle) || ($past(write_state, 1) == PwoWriteStage)) ? 64'd0 : ($past(butterfly_ready_in, 1) ? 7'((64'd1 + ({ 57'd0, $past(wr_valid_count, 1)} ))) : ({ 57'd0, $past(wr_valid_count, 1)} )))) &&
  write_state == PwoWriteWait;
endproperty
write_write_mem_to_write_wait_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) write_write_mem_to_write_wait_p);


property write_write_stage_to_write_idle_p;
  write_stage &&
  (rounds_count == 3'd1)
|->
  ##1
  write_idle &&
  chunk_count == ((($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) && ($past(index_count, 1) == 2'h3)) ? 4'((64'd1 + ({ 60'h0, $past(chunk_count, 1)} ))) : ({ 60'h0, $past(chunk_count, 1)} )) &&
  $stable(chunk_rand_offset) &&
  done_out == 0 &&
  index_count == (($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) ? 2'((64'd1 + ({ 62'h0, $past(index_count, 1)} ))) : ({ 62'h0, $past(index_count, 1)} )) &&
  index_rand_offset == ((($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) && ($past(index_count, 1) == 2'h3)) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  pw_mem_wr_addr_c_out == $past(getPwAddrAbcWr_4_i, 1) &&
  pw_mem_wr_addr_c_reg == $past(getPwAddrAbcWr_4_i, 1) &&
  pw_wren_reg == ((($past(write_state, 1) == PwoWriteMem) && $past(butterfly_ready_in, 1)) || ((($past(write_state, 1) == PwoWriteWait) && $past(butterfly_ready_in, 1)) && !$past(shuffle_en_in, 1))) &&
  rounds_count == 3'd0 &&
  wr_valid_count == 7'(((($past(write_state, 1) == PwoWriteIdle) || ($past(write_state, 1) == PwoWriteStage)) ? 64'd0 : ($past(butterfly_ready_in, 1) ? 7'((64'd1 + ({ 57'd0, $past(wr_valid_count, 1)} ))) : ({ 57'd0, $past(wr_valid_count, 1)} )))) &&
  write_state == PwoWriteIdle;
endproperty
write_write_stage_to_write_idle_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) write_write_stage_to_write_idle_p);


property write_write_stage_to_write_mem_p;
  write_stage &&
  (rounds_count != 3'd1) &&
  shuffle_en_in
|->
  ##1
  write_mem &&
  chunk_count == ((($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) && ($past(index_count, 1) == 2'h3)) ? 4'((64'd1 + ({ 60'h0, $past(chunk_count, 1)} ))) : ({ 60'h0, $past(chunk_count, 1)} )) &&
  $stable(chunk_rand_offset) &&
  done_out == (($past(rst_rounds_in, 1) ? 3'd0 : $past(rounds_count, 1)) == 3'd1) &&
  index_count == (($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) ? 2'((64'd1 + ({ 62'h0, $past(index_count, 1)} ))) : ({ 62'h0, $past(index_count, 1)} )) &&
  index_rand_offset == ((($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) && ($past(index_count, 1) == 2'h3)) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  pw_mem_wr_addr_c_out == $past(getPwAddrAbcWr_4_i, 1) &&
  pw_mem_wr_addr_c_reg == $past(getPwAddrAbcWr_4_i, 1) &&
  pw_wren_reg == ((($past(write_state, 1) == PwoWriteMem) && $past(butterfly_ready_in, 1)) || ((($past(write_state, 1) == PwoWriteWait) && $past(butterfly_ready_in, 1)) && !$past(shuffle_en_in, 1))) &&
  rounds_count == ($past(rst_rounds_in, 1) ? 3'd0 : $past(rounds_count, 1)) &&
  wr_valid_count == 7'(((($past(write_state, 1) == PwoWriteIdle) || ($past(write_state, 1) == PwoWriteStage)) ? 64'd0 : ($past(butterfly_ready_in, 1) ? 7'((64'd1 + ({ 57'd0, $past(wr_valid_count, 1)} ))) : ({ 57'd0, $past(wr_valid_count, 1)} )))) &&
  write_state == PwoWriteMem;
endproperty
write_write_stage_to_write_mem_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) write_write_stage_to_write_mem_p);


property write_write_stage_to_write_wait_p;
  write_stage &&
  (rounds_count != 3'd1) &&
  !shuffle_en_in
|->
  ##1
  write_wait &&
  chunk_count == ((($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) && ($past(index_count, 1) == 2'h3)) ? 4'((64'd1 + ({ 60'h0, $past(chunk_count, 1)} ))) : ({ 60'h0, $past(chunk_count, 1)} )) &&
  $stable(chunk_rand_offset) &&
  done_out == (($past(rst_rounds_in, 1) ? 3'd0 : $past(rounds_count, 1)) == 3'd1) &&
  index_count == (($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) ? 2'((64'd1 + ({ 62'h0, $past(index_count, 1)} ))) : ({ 62'h0, $past(index_count, 1)} )) &&
  index_rand_offset == ((($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) && ($past(index_count, 1) == 2'h3)) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  pw_mem_wr_addr_c_out == $past(getPwAddrAbcWr_4_i, 1) &&
  pw_mem_wr_addr_c_reg == $past(getPwAddrAbcWr_4_i, 1) &&
  pw_wren_reg == ((($past(write_state, 1) == PwoWriteMem) && $past(butterfly_ready_in, 1)) || ((($past(write_state, 1) == PwoWriteWait) && $past(butterfly_ready_in, 1)) && !$past(shuffle_en_in, 1))) &&
  rounds_count == ($past(rst_rounds_in, 1) ? 3'd0 : $past(rounds_count, 1)) &&
  wr_valid_count == 7'(((($past(write_state, 1) == PwoWriteIdle) || ($past(write_state, 1) == PwoWriteStage)) ? 64'd0 : ($past(butterfly_ready_in, 1) ? 7'((64'd1 + ({ 57'd0, $past(wr_valid_count, 1)} ))) : ({ 57'd0, $past(wr_valid_count, 1)} )))) &&
  write_state == PwoWriteWait;
endproperty
write_write_stage_to_write_wait_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) write_write_stage_to_write_wait_p);


property write_write_wait_to_write_mem_p;
  write_wait &&
  !shuffle_en_in &&
  butterfly_ready_in
|->
  ##1
  write_mem &&
  chunk_count == ((($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) && ($past(index_count, 1) == 2'h3)) ? 4'((64'd1 + ({ 60'h0, $past(chunk_count, 1)} ))) : ({ 60'h0, $past(chunk_count, 1)} )) &&
  $stable(chunk_rand_offset) &&
  done_out == (($past(rst_rounds_in, 1) ? 3'd0 : (($past(rounds_count, 1) == 3'd1) ? 3'd0 : $past(rounds_count, 1))) == 3'd1) &&
  index_count == (($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) ? 2'((64'd1 + ({ 62'h0, $past(index_count, 1)} ))) : ({ 62'h0, $past(index_count, 1)} )) &&
  index_rand_offset == ((($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) && ($past(index_count, 1) == 2'h3)) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  pw_mem_wr_addr_c_out == $past(getPwAddrAbcWr_5_i, 1) &&
  pw_mem_wr_addr_c_reg == $past(getPwAddrAbcWr_5_i, 1) &&
  pw_wren_reg == ((($past(write_state, 1) == PwoWriteMem) && $past(butterfly_ready_in, 1)) || ((($past(write_state, 1) == PwoWriteWait) && $past(butterfly_ready_in, 1)) && !$past(shuffle_en_in, 1))) &&
  rounds_count == ($past(rst_rounds_in, 1) ? 3'd0 : (($past(rounds_count, 1) == 3'd1) ? 3'd0 : $past(rounds_count, 1))) &&
  wr_valid_count == 7'(((($past(write_state, 1) == PwoWriteIdle) || ($past(write_state, 1) == PwoWriteStage)) ? 64'd0 : 7'((64'd1 + ({ 57'd0, $past(wr_valid_count, 1)} ))))) &&
  write_state == PwoWriteMem;
endproperty
write_write_wait_to_write_mem_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) write_write_wait_to_write_mem_p);


property write_write_wait_to_write_stage_p;
  write_wait &&
  shuffle_en_in
|->
  ##1
  write_stage &&
  chunk_count == { $past(random_in, 1) }[5:2] &&
  chunk_rand_offset == { $past(random_in, 1) }[5:2] &&
  done_out == (($past(rst_rounds_in, 1) ? 64'd0 : ((({ 61'd0, $past(rounds_count, 1)} ) < 64'd1) ? 3'((64'd1 + ({ 61'd0, $past(rounds_count, 1)} ))) : (($past(rounds_count, 1) == 3'd1) ? 64'd0 : ({ 61'd0, $past(rounds_count, 1)} )))) == 64'd1) &&
  index_count == (($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) ? 2'((64'd1 + ({ 62'h0, $past(index_count, 1)} ))) : ({ 62'h0, $past(index_count, 1)} )) &&
  index_rand_offset == ((($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) && ($past(index_count, 1) == 2'h3)) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  pw_mem_wr_addr_c_out == $past(getPwAddrAbcWr_5_i, 1) &&
  pw_mem_wr_addr_c_reg == $past(getPwAddrAbcWr_5_i, 1) &&
  pw_wren_reg == ((($past(write_state, 1) == PwoWriteMem) && $past(butterfly_ready_in, 1)) || ((($past(write_state, 1) == PwoWriteWait) && $past(butterfly_ready_in, 1)) && !$past(shuffle_en_in, 1))) &&
  rounds_count == 3'(($past(rst_rounds_in, 1) ? 64'd0 : ((({ 61'd0, $past(rounds_count, 1)} ) < 64'd1) ? 3'((64'd1 + ({ 61'd0, $past(rounds_count, 1)} ))) : (($past(rounds_count, 1) == 3'd1) ? 64'd0 : ({ 61'd0, $past(rounds_count, 1)} ))))) &&
  wr_valid_count == 7'(((($past(write_state, 1) == PwoWriteIdle) || ($past(write_state, 1) == PwoWriteStage)) ? 64'd0 : ($past(butterfly_ready_in, 1) ? 7'((64'd1 + ({ 57'd0, $past(wr_valid_count, 1)} ))) : ({ 57'd0, $past(wr_valid_count, 1)} )))) &&
  write_state == PwoWriteStage;
endproperty
write_write_wait_to_write_stage_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) write_write_wait_to_write_stage_p);


property write_write_wait_to_write_wait_p;
  write_wait &&
  !shuffle_en_in &&
  !butterfly_ready_in
|->
  ##1
  write_wait &&
  chunk_count == ((($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) && ($past(index_count, 1) == 2'h3)) ? 4'((64'd1 + ({ 60'h0, $past(chunk_count, 1)} ))) : ({ 60'h0, $past(chunk_count, 1)} )) &&
  $stable(chunk_rand_offset) &&
  done_out == (($past(rst_rounds_in, 1) ? 3'd0 : (($past(rounds_count, 1) == 3'd1) ? 3'd0 : $past(rounds_count, 1))) == 3'd1) &&
  index_count == (($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) ? 2'((64'd1 + ({ 62'h0, $past(index_count, 1)} ))) : ({ 62'h0, $past(index_count, 1)} )) &&
  index_rand_offset == ((($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) && ($past(index_count, 1) == 2'h3)) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  pw_mem_wr_addr_c_out == $past(getPwAddrAbcWr_5_i, 1) &&
  pw_mem_wr_addr_c_reg == $past(getPwAddrAbcWr_5_i, 1) &&
  pw_wren_reg == ((($past(write_state, 1) == PwoWriteMem) && $past(butterfly_ready_in, 1)) || ((($past(write_state, 1) == PwoWriteWait) && $past(butterfly_ready_in, 1)) && !$past(shuffle_en_in, 1))) &&
  rounds_count == ($past(rst_rounds_in, 1) ? 3'd0 : (($past(rounds_count, 1) == 3'd1) ? 3'd0 : $past(rounds_count, 1))) &&
  wr_valid_count == ((($past(write_state, 1) == PwoWriteIdle) || ($past(write_state, 1) == PwoWriteStage)) ? 7'd0 : $past(wr_valid_count, 1)) &&
  write_state == PwoWriteWait;
endproperty
write_write_wait_to_write_wait_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) write_write_wait_to_write_wait_p);


property read_read_idle_eventually_left_p;
  read_idle && ntt_enable_in
|->
  s_eventually(!read_idle);
endproperty
read_read_idle_eventually_left_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) read_read_idle_eventually_left_p);


property read_read_stage_eventually_left_p;
  read_stage && !ntt_enable_in && done_out
|->
  s_eventually(!read_stage);
endproperty
read_read_stage_eventually_left_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) read_read_stage_eventually_left_p);


property read_read_exec_eventually_left_p;
  read_exec
|->
  s_eventually(!read_exec);
endproperty
read_read_exec_eventually_left_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) read_read_exec_eventually_left_p);


property read_read_exec_wait_eventually_left_p;
  read_exec_wait
|->
  s_eventually(!read_exec_wait);
endproperty
read_read_exec_wait_eventually_left_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) read_read_exec_wait_eventually_left_p);


property write_write_idle_eventually_left_p;
  write_idle && ntt_enable_in
|->
  s_eventually(!write_idle);
endproperty
write_write_idle_eventually_left_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) write_write_idle_eventually_left_p);


property write_write_stage_eventually_left_p;
  write_stage
|->
  s_eventually(!write_stage);
endproperty
write_write_stage_eventually_left_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) write_write_stage_eventually_left_p);


property write_write_wait_eventually_left_p;
  write_wait
|->
  s_eventually(!write_wait);
endproperty
write_write_wait_eventually_left_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) write_write_wait_eventually_left_p);


property write_write_mem_eventually_left_p;
  write_mem
|->
  s_eventually(!write_mem);
endproperty
write_write_mem_eventually_left_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) write_write_mem_eventually_left_p);


parameter CONSISTENCY = 1;
if (CONSISTENCY) begin
  // Check that no more than 1 state condition is met at the same time
  read_consistency_onehot0_state: assert property($onehot0({ read_exec, read_exec_wait, read_idle, read_stage }));
end


if (CONSISTENCY) begin
  // Check that no more than 1 state condition is met at the same time
  write_consistency_onehot0_state: assert property($onehot0({ write_idle, write_mem, write_stage, write_wait }));
end


endmodule
