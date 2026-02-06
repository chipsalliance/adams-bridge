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
// | Created on 04.08.2025 at 09:46                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import ntt_ctrl_masked_gs_mlkem_pkg::*;
import abr_params_pkg::*;
import ntt_defines_pkg::*;
import ntt_ctrl_masked_gs_mlkem_functions::*;
import ntt_ctrl_masked_gs_mlkem_pkg::*;


module fv_ntt_ctrl_masked_gs_mlkem_m(
  input logic rst_n,
  input logic clk,

  // Ports
  input logic ntt_enable_in,

  input logic butterfly_ready_in,

  input logic buf0_valid_in,

  input logic sampler_valid_in,

  input logic accumulate_in,

  input st_NttMemBaseAddrs ntt_mem_base_addr_in,

  input logic shuffle_en_in,

  input logic mlkem_in,

  input logic unsigned [5:0] random_in,

  input logic rst_rounds_in,

  input logic unsigned [2:0] opcode_out,

  input logic masking_en_ctrl_out,

  input logic unsigned [1:0] buf_wrptr_out,

  input logic unsigned [1:0] buf_rdptr_out,

  input logic unsigned [14:0] mem_rd_addr_out,

  input logic unsigned [14:0] mem_wr_addr_out,

  input logic pw_rden_out,

  input logic pw_wren_out,

  input logic pw_share_mem_rden_out,

  input logic done_out,

  input logic intt_passthrough_out,

  // Registers
  input logic unsigned [2:0] bf_enable_reg,
  input logic unsigned [2:0] bf_enable_reg_dummy,
  input logic unsigned [1:0] buf_count,
  input logic buf_wren_intt_reg,
  input logic buf_wren_intt_reg_dummy,
  input logic unsigned [1:0] buf_wrptr,
  input logic unsigned [547:0] buf_wrptr_reg,
  input logic unsigned [1:0] buf_wrptr_reg_d1,
  input logic unsigned [3:0] chunk_count,
  input logic unsigned [1087:0] chunk_count_reg,
  input logic unsigned [3:0] chunk_rand_offset,
  input logic incr_twiddle_addr_reg,
  input logic unsigned [1:0] index_count,
  input logic unsigned [1:0] index_rand_offset,
  input logic masking_en_ctrl_reg,
  input logic unsigned [14:0] mem_rd_addr,
  input logic mem_rd_en_reg,
  input logic mem_rd_en_reg_dummy,
  input logic unsigned [14:0] mem_wr_addr,
  input logic unsigned [6:0] rd_valid_count,
  input e_MaskedGsReadStatesType read_state,
  input logic unsigned [2:0] rounds_count,
  input logic unsigned [6:0] twiddle_addr_reg,
  input logic unsigned [6:0] twiddle_addr_reg_d2,
  input logic unsigned [6:0] twiddle_addr_reg_d3,
  input logic unsigned [6:0] twiddle_addr_reg_d3_dummy,
  input logic unsigned [6:0] wr_valid_count,
  input e_MaskedGsWriteStatesType write_state,

  // States
  input logic state,
  input logic read_idle,
  input logic read_stage,
  input logic read_exec,
  input logic write_idle,
  input logic write_stage,
  input logic write_buf,
  input logic write_mem,
  input logic write_wait
);


default clocking default_clk @(posedge clk); endclocking


logic getMaskingEnCtrl_0_i;
assign getMaskingEnCtrl_0_i = getMaskingEnCtrl(rounds_count, read_state, write_state, masking_en_ctrl_reg);

a_unsigned_7_8 getTwiddleRandOffsetsMaskedGS_0_i;
assign getTwiddleRandOffsetsMaskedGS_0_i = getTwiddleRandOffsetsMaskedGS(masking_en_ctrl_reg, chunk_count_reg, buf_wrptr_reg);

a_unsigned_7_8 twiddle_offset_array_0_i;
assign twiddle_offset_array_0_i = '{
  0: 7'd0,
  1: 7'd64,
  2: 7'd80,
  3: 7'd84,
  4: 7'd0,
  5: 7'd0,
  6: 7'd0,
  7: 7'd0
};

logic unsigned [6:0] getTwiddleIncrAddr_0_i;
assign getTwiddleIncrAddr_0_i = getTwiddleIncrAddr(shuffle_en_in, rounds_count, getTwiddleRandOffsetsMaskedGS_0_i, '{ 0: 7'd63, 1: 7'd15, 2: 7'd3, 3: 7'd0, 4: 7'd0, 5: 7'd0, 6: 7'd0, 7: 7'd0 }, twiddle_addr_reg);

logic unsigned [6:0] getTwiddleAddrReg_0_i;
assign getTwiddleAddrReg_0_i = getTwiddleAddrReg(incr_twiddle_addr_reg, ((read_state == MaskedGsReadIdle) || ((read_state == MaskedGsReadStage) && !butterfly_ready_in)), getTwiddleIncrAddr_0_i, twiddle_addr_reg);

logic unsigned [1087:0] getChunkCountRegMaskedGS_0_i;
assign getChunkCountRegMaskedGS_0_i = getChunkCountRegMaskedGS(masking_en_ctrl_reg, butterfly_ready_in, 0, chunk_count, chunk_count_reg);

logic unsigned [1:0] getMemRdIndexOfst_0_i;
assign getMemRdIndexOfst_0_i = getMemRdIndexOfst(index_count, index_rand_offset);

logic unsigned [14:0] getMemRdBaseAddr_0_i;
assign getMemRdBaseAddr_0_i = getMemRdBaseAddr(rounds_count, ntt_mem_base_addr_in);

logic unsigned [547:0] getBufWrptrReg_0_i;
assign getBufWrptrReg_0_i = getBufWrptrReg(0, butterfly_ready_in, masking_en_ctrl_reg, getMemRdIndexOfst_0_i, buf_wrptr_reg);

logic unsigned [6:0] getRdValidCount_0_i;
assign getRdValidCount_0_i = getRdValidCount(read_state, rounds_count, sampler_valid_in, rd_valid_count);

logic unsigned [1:0] getIndexCount_0_i;
assign getIndexCount_0_i = getIndexCount(0, index_count);

logic unsigned [1087:0] getChunkCountRegMaskedGS_1_i;
assign getChunkCountRegMaskedGS_1_i = getChunkCountRegMaskedGS(masking_en_ctrl_reg, butterfly_ready_in, 1, chunk_count, chunk_count_reg);

logic unsigned [15:0] getShuffledMemRdAddrNxt_1_i;
assign getShuffledMemRdAddrNxt_1_i = getShuffledMemRdAddrNxt(chunk_count, 15'd1, getMemRdIndexOfst_0_i, getMemRdBaseAddr_0_i);

logic unsigned [15:0] getUnshuffledMemRdAddrNxt_1_i;
assign getUnshuffledMemRdAddrNxt_1_i = getUnshuffledMemRdAddrNxt(mem_rd_addr, 15'd1);

logic unsigned [15:0] getMemRdAddrNxt_1_i;
assign getMemRdAddrNxt_1_i = getMemRdAddrNxt(shuffle_en_in, rounds_count, getShuffledMemRdAddrNxt_1_i, getUnshuffledMemRdAddrNxt_1_i);

logic unsigned [14:0] wraparoundMemAddr_1_i;
assign wraparoundMemAddr_1_i = wraparoundMemAddr(getMemRdAddrNxt_1_i, getMemRdBaseAddr_0_i);

logic unsigned [547:0] getBufWrptrReg_1_i;
assign getBufWrptrReg_1_i = getBufWrptrReg(1, butterfly_ready_in, masking_en_ctrl_reg, getMemRdIndexOfst_0_i, buf_wrptr_reg);

logic unsigned [1:0] getIndexCount_1_i;
assign getIndexCount_1_i = getIndexCount(1, index_count);

logic unsigned [14:0] getMemWrAddr_0_i;
assign getMemWrAddr_0_i = getMemWrAddr(1, 0, shuffle_en_in, ntt_mem_base_addr_in, 4'(rounds_count), chunk_rand_offset, mem_wr_addr, 15'd0);

logic unsigned [1:0] getBufWrptrMaskedGS_0_i;
assign getBufWrptrMaskedGS_0_i = getBufWrptrMaskedGS(0, shuffle_en_in, masking_en_ctrl_reg, mlkem_in, buf_wrptr_reg_d1, buf_wrptr_reg, buf_wrptr);

logic unsigned [2:0] getRoundsCount_0_i;
assign getRoundsCount_0_i = getRoundsCount(rst_rounds_in, 0, rounds_count);

logic unsigned [14:0] getMemWrAddr_1_i;
assign getMemWrAddr_1_i = getMemWrAddr(0, 1, shuffle_en_in, ntt_mem_base_addr_in, 4'(rounds_count), chunk_rand_offset, mem_wr_addr, 15'd16);

logic unsigned [1:0] getBufWrptrMaskedGS_1_i;
assign getBufWrptrMaskedGS_1_i = getBufWrptrMaskedGS(butterfly_ready_in, shuffle_en_in, masking_en_ctrl_reg, mlkem_in, buf_wrptr_reg_d1, buf_wrptr_reg, buf_wrptr);

logic unsigned [14:0] getMemWrAddr_2_i;
assign getMemWrAddr_2_i = getMemWrAddr(0, 0, shuffle_en_in, ntt_mem_base_addr_in, 4'(rounds_count), chunk_rand_offset, mem_wr_addr, 15'd16);

logic unsigned [1:0] getBufWrptrMaskedGS_2_i;
assign getBufWrptrMaskedGS_2_i = getBufWrptrMaskedGS(1, shuffle_en_in, masking_en_ctrl_reg, mlkem_in, buf_wrptr_reg_d1, buf_wrptr_reg, buf_wrptr);

logic unsigned [1:0] getBufWrptrMaskedGS_3_i;
assign getBufWrptrMaskedGS_3_i = getBufWrptrMaskedGS(!shuffle_en_in, shuffle_en_in, masking_en_ctrl_reg, mlkem_in, buf_wrptr_reg_d1, buf_wrptr_reg, buf_wrptr);

logic unsigned [2:0] getRoundsCount_1_i;
assign getRoundsCount_1_i = getRoundsCount(rst_rounds_in, 1, rounds_count);


sequence reset_sequence;
  !rst_n ##1 rst_n;
endsequence


property common_reset_p;
  $past(!ntt_ctrl.reset_n || ntt_ctrl.zeroize) |->
  state &&
  buf_count == 2'd0 &&
  buf_rdptr_out == 2'd0 &&
  masking_en_ctrl_out == 0 &&
  masking_en_ctrl_reg == 0 &&
  opcode_out == 3'd0 &&
  pw_rden_out == 0 &&
  pw_share_mem_rden_out == 0 &&
  pw_wren_out == 0;
endproperty
common_reset_a: assert property (common_reset_p);


property read_reset_p;
  $past(!ntt_ctrl.reset_n || ntt_ctrl.zeroize) |->
  read_idle &&
  bf_enable_reg == 3'd0 &&
  buf_wrptr_reg == 548'd0 &&
  buf_wrptr_reg_d1 == 2'd0 &&
  chunk_count_reg == 1088'd0 &&
  incr_twiddle_addr_reg == 0 &&
  index_count == 2'd0 &&
  index_rand_offset == 2'd0 &&
  mem_rd_addr == 15'd0 &&
  mem_rd_addr_out == 15'd0 &&
  mem_rd_en_reg == 0 &&
  rd_valid_count == 7'd0 &&
  read_state == MaskedGsReadIdle &&
  twiddle_addr_reg == 7'd0 &&
  twiddle_addr_reg_d2 == 7'd0 &&
  twiddle_addr_reg_d3 == 7'd0;
endproperty
read_reset_a: assert property (read_reset_p);


property write_reset_p;
  $past(!ntt_ctrl.reset_n || ntt_ctrl.zeroize) |->
  write_idle &&
  buf_wren_intt_reg == 0 &&
  buf_wrptr == 2'd0 &&
  buf_wrptr_out == 2'd0 &&
  chunk_count == 4'd0 &&
  chunk_rand_offset == 4'd0 &&
  done_out == 0 &&
  mem_wr_addr == 15'd0 &&
  rounds_count == 3'd0 &&
  wr_valid_count == 7'd0 &&
  write_state == MaskedGsWriteIdle;
endproperty
write_reset_a: assert property (write_reset_p);


property common_state_to_state_p;
  state
|->
  ##1
  state &&
  buf_count == (($past(buf0_valid_in, 1) || ((({ 62'd0, $past(buf_count, 1)} ) > 64'd0) && (({ 62'd0, $past(buf_count, 1)} ) < 64'd3))) ? 2'((64'd1 + ({ 62'd0, $past(buf_count, 1)} ))) : 64'd0) &&
  buf_rdptr_out == (($past(buf0_valid_in, 1) || ((({ 62'd0, $past(buf_count, 1)} ) > 64'd0) && (({ 62'd0, $past(buf_count, 1)} ) < 64'd3))) ? 2'((64'd1 + ({ 62'd0, $past(buf_count, 1)} ))) : 64'd0) &&
  masking_en_ctrl_out == $past(getMaskingEnCtrl_0_i, 1) &&
  masking_en_ctrl_reg == $past(getMaskingEnCtrl_0_i, 1) &&
  opcode_out == 3'd1 &&
  pw_rden_out == 0 &&
  pw_share_mem_rden_out == 0 &&
  pw_wren_out == 0;
endproperty
common_state_to_state_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) common_state_to_state_p);


property read_read_exec_to_read_exec_p;
  read_exec &&
  (rd_valid_count < 7'h3F)
|->
  ##1
  read_exec &&
  bf_enable_reg == (({ { $past(bf_enable_reg, 1) }[1:0], 1'd0} ) + (($past(read_state, 1) == MaskedGsReadExec) ? 3'd1 : 3'd0)) &&
  buf_wrptr_reg == $past(getBufWrptrReg_1_i, 1) &&
  buf_wrptr_reg_d1 == ($past(mlkem_in, 1) ? { $past(buf_wrptr_reg, 1) }[509:508] : { $past(buf_wrptr_reg, 1) }[1:0]) &&
  chunk_count_reg == $past(getChunkCountRegMaskedGS_1_i, 1) &&
  incr_twiddle_addr_reg == ($past(read_state, 1) == MaskedGsReadExec) &&
  index_count == $past(getIndexCount_1_i, 1) &&
  index_rand_offset == (($past(index_count, 1) == 2'd3) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  mem_rd_addr == $past(wraparoundMemAddr_1_i, 1) &&
  mem_rd_addr_out == $past(wraparoundMemAddr_1_i, 1) &&
  mem_rd_en_reg == (($past(read_state, 1) == MaskedGsReadExec) && (({ 49'h0, $past(mem_rd_addr, 1)} ) <= (64'd63 + ({ 49'h0, $past(getMemRdBaseAddr_0_i, 1)} )))) &&
  rd_valid_count == $past(getRdValidCount_0_i, 1) &&
  read_state == MaskedGsReadExec &&
  twiddle_addr_reg == $past(getTwiddleAddrReg_0_i, 1) &&
  twiddle_addr_reg_d2 == ($past(shuffle_en_in, 1) ? ($past(getTwiddleRandOffsetsMaskedGS_0_i[rounds_count], 1) + $past(twiddle_offset_array_0_i[rounds_count], 1)) : ($past(twiddle_addr_reg, 1) + $past(twiddle_offset_array_0_i[rounds_count], 1))) &&
  twiddle_addr_reg_d3 == $past(twiddle_addr_reg_d2, 1);
endproperty
read_read_exec_to_read_exec_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) read_read_exec_to_read_exec_p);


property read_read_exec_to_read_stage_p;
  read_exec &&
  (rd_valid_count >= 7'h3F)
|->
  ##1
  read_stage &&
  bf_enable_reg == (({ { $past(bf_enable_reg, 1) }[1:0], 1'd0} ) + (($past(read_state, 1) == MaskedGsReadExec) ? 3'd1 : 3'd0)) &&
  buf_wrptr_reg == $past(getBufWrptrReg_1_i, 1) &&
  buf_wrptr_reg_d1 == ($past(mlkem_in, 1) ? { $past(buf_wrptr_reg, 1) }[509:508] : { $past(buf_wrptr_reg, 1) }[1:0]) &&
  chunk_count_reg == $past(getChunkCountRegMaskedGS_1_i, 1) &&
  incr_twiddle_addr_reg == ($past(read_state, 1) == MaskedGsReadExec) &&
  index_count == $past(getIndexCount_1_i, 1) &&
  index_rand_offset == (($past(index_count, 1) == 2'd3) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  mem_rd_addr == $past(wraparoundMemAddr_1_i, 1) &&
  mem_rd_addr_out == $past(wraparoundMemAddr_1_i, 1) &&
  mem_rd_en_reg == (($past(read_state, 1) == MaskedGsReadExec) && (({ 49'h0, $past(mem_rd_addr, 1)} ) <= (64'd63 + ({ 49'h0, $past(getMemRdBaseAddr_0_i, 1)} )))) &&
  rd_valid_count == $past(getRdValidCount_0_i, 1) &&
  read_state == MaskedGsReadStage &&
  twiddle_addr_reg == $past(getTwiddleAddrReg_0_i, 1) &&
  twiddle_addr_reg_d2 == ($past(shuffle_en_in, 1) ? ($past(getTwiddleRandOffsetsMaskedGS_0_i[rounds_count], 1) + $past(twiddle_offset_array_0_i[rounds_count], 1)) : ($past(twiddle_addr_reg, 1) + $past(twiddle_offset_array_0_i[rounds_count], 1))) &&
  twiddle_addr_reg_d3 == $past(twiddle_addr_reg_d2, 1);
endproperty
read_read_exec_to_read_stage_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) read_read_exec_to_read_stage_p);


property read_read_idle_to_read_idle_p;
  read_idle &&
  !ntt_enable_in
|->
  ##1
  read_idle &&
  bf_enable_reg == (({ { $past(bf_enable_reg, 1) }[1:0], 1'd0} ) + (($past(read_state, 1) == MaskedGsReadExec) ? 3'd1 : 3'd0)) &&
  buf_wrptr_reg == $past(getBufWrptrReg_0_i, 1) &&
  buf_wrptr_reg_d1 == ($past(mlkem_in, 1) ? { $past(buf_wrptr_reg, 1) }[509:508] : { $past(buf_wrptr_reg, 1) }[1:0]) &&
  chunk_count_reg == $past(getChunkCountRegMaskedGS_0_i, 1) &&
  incr_twiddle_addr_reg == ($past(read_state, 1) == MaskedGsReadExec) &&
  index_count == $past(getIndexCount_0_i, 1) &&
  index_rand_offset == (($past(index_count, 1) == 2'd3) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  mem_rd_addr == ($past(shuffle_en_in, 1) ? 15'((({ 49'h0, $past(getMemRdBaseAddr_0_i, 1)} ) + (64'd4 * ({ 60'h0, $past(chunk_rand_offset, 1)} )))) : ({ 49'h0, $past(getMemRdBaseAddr_0_i, 1)} )) &&
  mem_rd_addr_out == ($past(shuffle_en_in, 1) ? 15'((({ 49'h0, $past(getMemRdBaseAddr_0_i, 1)} ) + (64'd4 * ({ 60'h0, $past(chunk_rand_offset, 1)} )))) : ({ 49'h0, $past(getMemRdBaseAddr_0_i, 1)} )) &&
  mem_rd_en_reg == (($past(read_state, 1) == MaskedGsReadExec) && (({ 49'h0, $past(mem_rd_addr, 1)} ) <= (64'd63 + ({ 49'h0, $past(getMemRdBaseAddr_0_i, 1)} )))) &&
  rd_valid_count == $past(getRdValidCount_0_i, 1) &&
  read_state == MaskedGsReadIdle &&
  twiddle_addr_reg == $past(getTwiddleAddrReg_0_i, 1) &&
  twiddle_addr_reg_d2 == ($past(shuffle_en_in, 1) ? ($past(getTwiddleRandOffsetsMaskedGS_0_i[rounds_count], 1) + $past(twiddle_offset_array_0_i[rounds_count], 1)) : ($past(twiddle_addr_reg, 1) + $past(twiddle_offset_array_0_i[rounds_count], 1))) &&
  twiddle_addr_reg_d3 == $past(twiddle_addr_reg_d2, 1);
endproperty
read_read_idle_to_read_idle_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) read_read_idle_to_read_idle_p);


property read_read_idle_to_read_stage_p;
  read_idle &&
  ntt_enable_in
|->
  ##1
  read_stage &&
  bf_enable_reg == (({ { $past(bf_enable_reg, 1) }[1:0], 1'd0} ) + (($past(read_state, 1) == MaskedGsReadExec) ? 3'd1 : 3'd0)) &&
  buf_wrptr_reg == $past(getBufWrptrReg_0_i, 1) &&
  buf_wrptr_reg_d1 == ($past(mlkem_in, 1) ? { $past(buf_wrptr_reg, 1) }[509:508] : { $past(buf_wrptr_reg, 1) }[1:0]) &&
  chunk_count_reg == $past(getChunkCountRegMaskedGS_0_i, 1) &&
  incr_twiddle_addr_reg == ($past(read_state, 1) == MaskedGsReadExec) &&
  index_count == $past(getIndexCount_0_i, 1) &&
  index_rand_offset == (($past(index_count, 1) == 2'd3) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  mem_rd_addr == ($past(shuffle_en_in, 1) ? 15'((({ 49'h0, $past(getMemRdBaseAddr_0_i, 1)} ) + (64'd4 * ({ 60'h0, $past(chunk_rand_offset, 1)} )))) : ({ 49'h0, $past(getMemRdBaseAddr_0_i, 1)} )) &&
  mem_rd_addr_out == ($past(shuffle_en_in, 1) ? 15'((({ 49'h0, $past(getMemRdBaseAddr_0_i, 1)} ) + (64'd4 * ({ 60'h0, $past(chunk_rand_offset, 1)} )))) : ({ 49'h0, $past(getMemRdBaseAddr_0_i, 1)} )) &&
  mem_rd_en_reg == (($past(read_state, 1) == MaskedGsReadExec) && (({ 49'h0, $past(mem_rd_addr, 1)} ) <= (64'd63 + ({ 49'h0, $past(getMemRdBaseAddr_0_i, 1)} )))) &&
  rd_valid_count == $past(getRdValidCount_0_i, 1) &&
  read_state == MaskedGsReadStage &&
  twiddle_addr_reg == $past(getTwiddleAddrReg_0_i, 1) &&
  twiddle_addr_reg_d2 == ($past(shuffle_en_in, 1) ? ($past(getTwiddleRandOffsetsMaskedGS_0_i[rounds_count], 1) + $past(twiddle_offset_array_0_i[rounds_count], 1)) : ($past(twiddle_addr_reg, 1) + $past(twiddle_offset_array_0_i[rounds_count], 1))) &&
  twiddle_addr_reg_d3 == $past(twiddle_addr_reg_d2, 1);
endproperty
read_read_idle_to_read_stage_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) read_read_idle_to_read_stage_p);


property read_read_stage_to_read_exec_p;
  read_stage &&
  (rounds_count != 3'd4) &&
  (write_state == MaskedGsWriteStage)
|->
  ##1
  read_exec &&
  bf_enable_reg == (({ { $past(bf_enable_reg, 1) }[1:0], 1'd0} ) + (($past(read_state, 1) == MaskedGsReadExec) ? 3'd1 : 3'd0)) &&
  buf_wrptr_reg == $past(getBufWrptrReg_0_i, 1) &&
  buf_wrptr_reg_d1 == ($past(mlkem_in, 1) ? { $past(buf_wrptr_reg, 1) }[509:508] : { $past(buf_wrptr_reg, 1) }[1:0]) &&
  chunk_count_reg == $past(getChunkCountRegMaskedGS_0_i, 1) &&
  incr_twiddle_addr_reg == ($past(read_state, 1) == MaskedGsReadExec) &&
  index_count == $past(getIndexCount_0_i, 1) &&
  index_rand_offset == { $past(random_in, 1) }[1:0] &&
  mem_rd_addr == ($past(shuffle_en_in, 1) ? 15'((({ 49'h0, $past(getMemRdBaseAddr_0_i, 1)} ) + (64'd4 * ({ 60'h0, $past(chunk_rand_offset, 1)} )))) : ({ 49'h0, $past(getMemRdBaseAddr_0_i, 1)} )) &&
  mem_rd_addr_out == ($past(shuffle_en_in, 1) ? 15'((({ 49'h0, $past(getMemRdBaseAddr_0_i, 1)} ) + (64'd4 * ({ 60'h0, $past(chunk_rand_offset, 1)} )))) : ({ 49'h0, $past(getMemRdBaseAddr_0_i, 1)} )) &&
  mem_rd_en_reg == (($past(read_state, 1) == MaskedGsReadExec) && (({ 49'h0, $past(mem_rd_addr, 1)} ) <= (64'd63 + ({ 49'h0, $past(getMemRdBaseAddr_0_i, 1)} )))) &&
  rd_valid_count == $past(getRdValidCount_0_i, 1) &&
  read_state == MaskedGsReadExec &&
  twiddle_addr_reg == $past(getTwiddleAddrReg_0_i, 1) &&
  twiddle_addr_reg_d2 == ($past(shuffle_en_in, 1) ? ($past(getTwiddleRandOffsetsMaskedGS_0_i[rounds_count], 1) + $past(twiddle_offset_array_0_i[rounds_count], 1)) : ($past(twiddle_addr_reg, 1) + $past(twiddle_offset_array_0_i[rounds_count], 1))) &&
  twiddle_addr_reg_d3 == $past(twiddle_addr_reg_d2, 1);
endproperty
read_read_stage_to_read_exec_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) read_read_stage_to_read_exec_p);


property read_read_stage_to_read_idle_p;
  read_stage &&
  (rounds_count == 3'd4)
|->
  ##1
  read_idle &&
  bf_enable_reg == (({ { $past(bf_enable_reg, 1) }[1:0], 1'd0} ) + (($past(read_state, 1) == MaskedGsReadExec) ? 3'd1 : 3'd0)) &&
  buf_wrptr_reg == $past(getBufWrptrReg_0_i, 1) &&
  buf_wrptr_reg_d1 == ($past(mlkem_in, 1) ? { $past(buf_wrptr_reg, 1) }[509:508] : { $past(buf_wrptr_reg, 1) }[1:0]) &&
  chunk_count_reg == $past(getChunkCountRegMaskedGS_0_i, 1) &&
  incr_twiddle_addr_reg == ($past(read_state, 1) == MaskedGsReadExec) &&
  index_count == $past(getIndexCount_0_i, 1) &&
  index_rand_offset == (($past(index_count, 1) == 2'd3) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  mem_rd_addr == ($past(shuffle_en_in, 1) ? 15'((({ 49'h0, $past(getMemRdBaseAddr_0_i, 1)} ) + (64'd4 * ({ 60'h0, $past(chunk_rand_offset, 1)} )))) : ({ 49'h0, $past(getMemRdBaseAddr_0_i, 1)} )) &&
  mem_rd_addr_out == ($past(shuffle_en_in, 1) ? 15'((({ 49'h0, $past(getMemRdBaseAddr_0_i, 1)} ) + (64'd4 * ({ 60'h0, $past(chunk_rand_offset, 1)} )))) : ({ 49'h0, $past(getMemRdBaseAddr_0_i, 1)} )) &&
  mem_rd_en_reg == (($past(read_state, 1) == MaskedGsReadExec) && (({ 49'h0, $past(mem_rd_addr, 1)} ) <= (64'd63 + ({ 49'h0, $past(getMemRdBaseAddr_0_i, 1)} )))) &&
  rd_valid_count == $past(getRdValidCount_0_i, 1) &&
  read_state == MaskedGsReadIdle &&
  twiddle_addr_reg == $past(getTwiddleAddrReg_0_i, 1) &&
  twiddle_addr_reg_d2 == ($past(shuffle_en_in, 1) ? ($past(getTwiddleRandOffsetsMaskedGS_0_i[rounds_count], 1) + $past(twiddle_offset_array_0_i[rounds_count], 1)) : ($past(twiddle_addr_reg, 1) + $past(twiddle_offset_array_0_i[rounds_count], 1))) &&
  twiddle_addr_reg_d3 == $past(twiddle_addr_reg_d2, 1);
endproperty
read_read_stage_to_read_idle_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) read_read_stage_to_read_idle_p);


property read_read_stage_to_read_stage_p;
  read_stage &&
  (rounds_count != 3'd4) &&
  (write_state != MaskedGsWriteStage)
|->
  ##1
  read_stage &&
  bf_enable_reg == (({ { $past(bf_enable_reg, 1) }[1:0], 1'd0} ) + (($past(read_state, 1) == MaskedGsReadExec) ? 3'd1 : 3'd0)) &&
  buf_wrptr_reg == $past(getBufWrptrReg_0_i, 1) &&
  buf_wrptr_reg_d1 == ($past(mlkem_in, 1) ? { $past(buf_wrptr_reg, 1) }[509:508] : { $past(buf_wrptr_reg, 1) }[1:0]) &&
  chunk_count_reg == $past(getChunkCountRegMaskedGS_0_i, 1) &&
  incr_twiddle_addr_reg == ($past(read_state, 1) == MaskedGsReadExec) &&
  index_count == $past(getIndexCount_0_i, 1) &&
  index_rand_offset == (($past(index_count, 1) == 2'd3) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  mem_rd_addr == ($past(shuffle_en_in, 1) ? 15'((({ 49'h0, $past(getMemRdBaseAddr_0_i, 1)} ) + (64'd4 * ({ 60'h0, $past(chunk_rand_offset, 1)} )))) : ({ 49'h0, $past(getMemRdBaseAddr_0_i, 1)} )) &&
  mem_rd_addr_out == ($past(shuffle_en_in, 1) ? 15'((({ 49'h0, $past(getMemRdBaseAddr_0_i, 1)} ) + (64'd4 * ({ 60'h0, $past(chunk_rand_offset, 1)} )))) : ({ 49'h0, $past(getMemRdBaseAddr_0_i, 1)} )) &&
  mem_rd_en_reg == (($past(read_state, 1) == MaskedGsReadExec) && (({ 49'h0, $past(mem_rd_addr, 1)} ) <= (64'd63 + ({ 49'h0, $past(getMemRdBaseAddr_0_i, 1)} )))) &&
  rd_valid_count == $past(getRdValidCount_0_i, 1) &&
  read_state == MaskedGsReadStage &&
  twiddle_addr_reg == $past(getTwiddleAddrReg_0_i, 1) &&
  twiddle_addr_reg_d2 == ($past(shuffle_en_in, 1) ? ($past(getTwiddleRandOffsetsMaskedGS_0_i[rounds_count], 1) + $past(twiddle_offset_array_0_i[rounds_count], 1)) : ($past(twiddle_addr_reg, 1) + $past(twiddle_offset_array_0_i[rounds_count], 1))) &&
  twiddle_addr_reg_d3 == $past(twiddle_addr_reg_d2, 1);
endproperty
read_read_stage_to_read_stage_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) read_read_stage_to_read_stage_p);


property write_write_buf_to_write_buf_p;
  write_buf &&
  !buf0_valid_in
|->
  ##1
  write_buf &&
  buf_wren_intt_reg == $past(butterfly_ready_in, 1) &&
  buf_wrptr == $past(getBufWrptrMaskedGS_1_i, 1) &&
  buf_wrptr_out == $past(getBufWrptrMaskedGS_1_i, 1) &&
  chunk_count == (($past(index_count, 1) == 2'd3) ? 4'((64'd1 + ({ 60'h0, $past(chunk_count, 1)} ))) : ({ 60'h0, $past(chunk_count, 1)} )) &&
  $stable(chunk_rand_offset) &&
  done_out == ($past(getRoundsCount_0_i, 1) == 3'd4) &&
  intt_passthrough_out == (($past(getRoundsCount_0_i, 1) == 3'd0) && $past(mlkem_in, 1)) &&
  mem_wr_addr == $past(getMemWrAddr_2_i, 1) &&
  rounds_count == $past(getRoundsCount_0_i, 1) &&
  $stable(wr_valid_count) &&
  write_state == MaskedGsWriteBuf;
endproperty
write_write_buf_to_write_buf_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) write_write_buf_to_write_buf_p);


property write_write_buf_to_write_mem_p;
  write_buf &&
  buf0_valid_in
|->
  ##1
  write_mem &&
  buf_wren_intt_reg == $past(butterfly_ready_in, 1) &&
  buf_wrptr == $past(getBufWrptrMaskedGS_1_i, 1) &&
  buf_wrptr_out == $past(getBufWrptrMaskedGS_1_i, 1) &&
  chunk_count == (($past(index_count, 1) == 2'd3) ? 4'((64'd1 + ({ 60'h0, $past(chunk_count, 1)} ))) : ({ 60'h0, $past(chunk_count, 1)} )) &&
  $stable(chunk_rand_offset) &&
  done_out == ($past(getRoundsCount_0_i, 1) == 3'd4) &&
  intt_passthrough_out == (($past(getRoundsCount_0_i, 1) == 3'd0) && $past(mlkem_in, 1)) &&
  mem_wr_addr == $past(getMemWrAddr_1_i, 1) &&
  rounds_count == $past(getRoundsCount_0_i, 1) &&
  wr_valid_count == 7'(((({ 57'd0, $past(wr_valid_count, 1)} ) > 64'h40) ? 64'd0 : 7'((64'd4 + ({ 57'd0, $past(wr_valid_count, 1)} ))))) &&
  write_state == MaskedGsWriteMem;
endproperty
write_write_buf_to_write_mem_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) write_write_buf_to_write_mem_p);


property write_write_idle_to_write_idle_p;
  write_idle &&
  !ntt_enable_in
|->
  ##1
  write_idle &&
  buf_wren_intt_reg == 0 &&
  buf_wrptr == $past(getBufWrptrMaskedGS_0_i, 1) &&
  buf_wrptr_out == $past(getBufWrptrMaskedGS_0_i, 1) &&
  chunk_count == (($past(index_count, 1) == 2'd3) ? 4'((64'd1 + ({ 60'h0, $past(chunk_count, 1)} ))) : ({ 60'h0, $past(chunk_count, 1)} )) &&
  $stable(chunk_rand_offset) &&
  done_out == ($past(getRoundsCount_0_i, 1) == 3'd4) &&
  intt_passthrough_out == (($past(getRoundsCount_0_i, 1) == 3'd0) && $past(mlkem_in, 1)) &&
  mem_wr_addr == $past(getMemWrAddr_0_i, 1) &&
  rounds_count == $past(getRoundsCount_0_i, 1) &&
  wr_valid_count == 7'd0 &&
  write_state == MaskedGsWriteIdle;
endproperty
write_write_idle_to_write_idle_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) write_write_idle_to_write_idle_p);


property write_write_idle_to_write_stage_p;
  write_idle &&
  ntt_enable_in
|->
  ##1
  write_stage &&
  buf_wren_intt_reg == 0 &&
  buf_wrptr == $past(getBufWrptrMaskedGS_0_i, 1) &&
  buf_wrptr_out == $past(getBufWrptrMaskedGS_0_i, 1) &&
  chunk_count == { $past(random_in, 1) }[5:2] &&
  chunk_rand_offset == { $past(random_in, 1) }[5:2] &&
  done_out == ($past(getRoundsCount_0_i, 1) == 3'd4) &&
  intt_passthrough_out == (($past(getRoundsCount_0_i, 1) == 3'd0) && $past(mlkem_in, 1)) &&
  mem_wr_addr == $past(getMemWrAddr_0_i, 1) &&
  rounds_count == $past(getRoundsCount_0_i, 1) &&
  wr_valid_count == 7'd0 &&
  write_state == MaskedGsWriteStage;
endproperty
write_write_idle_to_write_stage_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) write_write_idle_to_write_stage_p);


property write_write_mem_to_write_buf_p;
  write_mem &&
  !buf0_valid_in &&
  (({ 57'd0, wr_valid_count} ) < 64'h40) &&
  (buf_count == 2'd0)
|->
  ##1
  write_buf &&
  buf_wren_intt_reg == 1 &&
  buf_wrptr == $past(getBufWrptrMaskedGS_2_i, 1) &&
  buf_wrptr_out == $past(getBufWrptrMaskedGS_2_i, 1) &&
  chunk_count == (($past(index_count, 1) == 2'd3) ? 4'((64'd1 + ({ 60'h0, $past(chunk_count, 1)} ))) : ({ 60'h0, $past(chunk_count, 1)} )) &&
  $stable(chunk_rand_offset) &&
  done_out == ($past(getRoundsCount_0_i, 1) == 3'd4) &&
  intt_passthrough_out == (($past(getRoundsCount_0_i, 1) == 3'd0) && $past(mlkem_in, 1)) &&
  mem_wr_addr == $past(getMemWrAddr_1_i, 1) &&
  rounds_count == $past(getRoundsCount_0_i, 1) &&
  $stable(wr_valid_count) &&
  write_state == MaskedGsWriteBuf;
endproperty
write_write_mem_to_write_buf_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) write_write_mem_to_write_buf_p);


property write_write_mem_to_write_mem_p;
  write_mem &&
  !((!buf0_valid_in && (({ 57'd0, wr_valid_count} ) < 64'h40)) && (buf_count == 2'd0)) &&
  !(buf0_valid_in && (wr_valid_count == 7'h3C))
|->
  ##1
  write_mem &&
  buf_wren_intt_reg == 1 &&
  buf_wrptr == $past(getBufWrptrMaskedGS_2_i, 1) &&
  buf_wrptr_out == $past(getBufWrptrMaskedGS_2_i, 1) &&
  chunk_count == (($past(index_count, 1) == 2'd3) ? 4'((64'd1 + ({ 60'h0, $past(chunk_count, 1)} ))) : ({ 60'h0, $past(chunk_count, 1)} )) &&
  $stable(chunk_rand_offset) &&
  done_out == ($past(getRoundsCount_0_i, 1) == 3'd4) &&
  intt_passthrough_out == (($past(getRoundsCount_0_i, 1) == 3'd0) && $past(mlkem_in, 1)) &&
  mem_wr_addr == $past(getMemWrAddr_1_i, 1) &&
  rounds_count == $past(getRoundsCount_0_i, 1) &&
  wr_valid_count == 7'(($past(buf0_valid_in, 1) ? ((({ 57'd0, $past(wr_valid_count, 1)} ) > 64'h40) ? 64'd0 : 7'((64'd4 + ({ 57'd0, $past(wr_valid_count, 1)} )))) : ({ 57'd0, $past(wr_valid_count, 1)} ))) &&
  write_state == MaskedGsWriteMem;
endproperty
write_write_mem_to_write_mem_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) write_write_mem_to_write_mem_p);


property write_write_mem_to_write_wait_p;
  write_mem &&
  !((!buf0_valid_in && (({ 57'd0, wr_valid_count} ) < 64'h40)) && (buf_count == 2'd0)) &&
  buf0_valid_in &&
  (wr_valid_count == 7'h3C)
|->
  ##1
  write_wait &&
  buf_wren_intt_reg == 1 &&
  buf_wrptr == $past(getBufWrptrMaskedGS_2_i, 1) &&
  buf_wrptr_out == $past(getBufWrptrMaskedGS_2_i, 1) &&
  chunk_count == (($past(index_count, 1) == 2'd3) ? 4'((64'd1 + ({ 60'h0, $past(chunk_count, 1)} ))) : ({ 60'h0, $past(chunk_count, 1)} )) &&
  $stable(chunk_rand_offset) &&
  done_out == ($past(getRoundsCount_0_i, 1) == 3'd4) &&
  intt_passthrough_out == (($past(getRoundsCount_0_i, 1) == 3'd0) && $past(mlkem_in, 1)) &&
  mem_wr_addr == $past(getMemWrAddr_1_i, 1) &&
  rounds_count == $past(getRoundsCount_0_i, 1) &&
  wr_valid_count == 7'((64'd4 + ({ 57'h0, $past(wr_valid_count, 1)} ))) &&
  write_state == MaskedGsWriteWait;
endproperty
write_write_mem_to_write_wait_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) write_write_mem_to_write_wait_p);


property write_write_stage_to_write_buf_p;
  write_stage &&
  (rounds_count != 3'd4)
|->
  ##1
  write_buf &&
  buf_wren_intt_reg == 0 &&
  buf_wrptr == $past(getBufWrptrMaskedGS_0_i, 1) &&
  buf_wrptr_out == $past(getBufWrptrMaskedGS_0_i, 1) &&
  chunk_count == (($past(index_count, 1) == 2'd3) ? 4'((64'd1 + ({ 60'h0, $past(chunk_count, 1)} ))) : ({ 60'h0, $past(chunk_count, 1)} )) &&
  $stable(chunk_rand_offset) &&
  done_out == ($past(getRoundsCount_0_i, 1) == 3'd4) &&
  intt_passthrough_out == (($past(getRoundsCount_0_i, 1) == 3'd0) && $past(mlkem_in, 1)) &&
  mem_wr_addr == $past(getMemWrAddr_0_i, 1) &&
  rounds_count == $past(getRoundsCount_0_i, 1) &&
  wr_valid_count == 7'd0 &&
  write_state == MaskedGsWriteBuf;
endproperty
write_write_stage_to_write_buf_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) write_write_stage_to_write_buf_p);


property write_write_stage_to_write_idle_p;
  write_stage &&
  (rounds_count == 3'd4)
|->
  ##1
  write_idle &&
  buf_wren_intt_reg == 0 &&
  buf_wrptr == $past(getBufWrptrMaskedGS_0_i, 1) &&
  buf_wrptr_out == $past(getBufWrptrMaskedGS_0_i, 1) &&
  chunk_count == (($past(index_count, 1) == 2'd3) ? 4'((64'd1 + ({ 60'h0, $past(chunk_count, 1)} ))) : ({ 60'h0, $past(chunk_count, 1)} )) &&
  $stable(chunk_rand_offset) &&
  done_out == ($past(getRoundsCount_0_i, 1) == 3'd4) &&
  intt_passthrough_out == (($past(getRoundsCount_0_i, 1) == 3'd0) && $past(mlkem_in, 1)) &&
  mem_wr_addr == $past(getMemWrAddr_0_i, 1) &&
  rounds_count == $past(getRoundsCount_0_i, 1) &&
  wr_valid_count == 7'd0 &&
  write_state == MaskedGsWriteIdle;
endproperty
write_write_stage_to_write_idle_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) write_write_stage_to_write_idle_p);


property write_write_wait_to_write_stage_p;
  write_wait &&
  (buf_count == 2'd3)
|->
  ##1
  write_stage &&
  buf_wren_intt_reg == !$past(shuffle_en_in, 1) &&
  buf_wrptr == $past(getBufWrptrMaskedGS_3_i, 1) &&
  buf_wrptr_out == $past(getBufWrptrMaskedGS_3_i, 1) &&
  chunk_count == { $past(random_in, 1) }[5:2] &&
  chunk_rand_offset == { $past(random_in, 1) }[5:2] &&
  done_out == ($past(getRoundsCount_1_i, 1) == 3'd4) &&
  intt_passthrough_out == (($past(getRoundsCount_1_i, 1) == 3'd0) && $past(mlkem_in, 1)) &&
  mem_wr_addr == $past(getMemWrAddr_1_i, 1) &&
  rounds_count == $past(getRoundsCount_1_i, 1) &&
  wr_valid_count == 7'(($past(buf0_valid_in, 1) ? ((({ 57'd0, $past(wr_valid_count, 1)} ) > 64'h40) ? 64'd0 : 7'((64'd4 + ({ 57'd0, $past(wr_valid_count, 1)} )))) : ({ 57'd0, $past(wr_valid_count, 1)} ))) &&
  write_state == MaskedGsWriteStage;
endproperty
write_write_wait_to_write_stage_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) write_write_wait_to_write_stage_p);


property write_write_wait_to_write_wait_p;
  write_wait &&
  (buf_count != 2'd3)
|->
  ##1
  write_wait &&
  buf_wren_intt_reg == !$past(shuffle_en_in, 1) &&
  buf_wrptr == $past(getBufWrptrMaskedGS_3_i, 1) &&
  buf_wrptr_out == $past(getBufWrptrMaskedGS_3_i, 1) &&
  chunk_count == (($past(index_count, 1) == 2'd3) ? 4'((64'd1 + ({ 60'h0, $past(chunk_count, 1)} ))) : ({ 60'h0, $past(chunk_count, 1)} )) &&
  $stable(chunk_rand_offset) &&
  done_out == ($past(getRoundsCount_0_i, 1) == 3'd4) &&
  intt_passthrough_out == (($past(getRoundsCount_0_i, 1) == 3'd0) && $past(mlkem_in, 1)) &&
  mem_wr_addr == $past(getMemWrAddr_1_i, 1) &&
  rounds_count == $past(getRoundsCount_0_i, 1) &&
  wr_valid_count == 7'(($past(buf0_valid_in, 1) ? ((({ 57'd0, $past(wr_valid_count, 1)} ) > 64'h40) ? 64'd0 : 7'((64'd4 + ({ 57'd0, $past(wr_valid_count, 1)} )))) : ({ 57'd0, $past(wr_valid_count, 1)} ))) &&
  write_state == MaskedGsWriteWait;
endproperty
write_write_wait_to_write_wait_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) write_write_wait_to_write_wait_p);


property read_read_idle_eventually_left_p;
  read_idle
|->
  s_eventually(!read_idle);
endproperty
read_read_idle_eventually_left_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) read_read_idle_eventually_left_p);


property read_read_stage_eventually_left_p;
  read_stage
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


property write_write_idle_eventually_left_p;
  write_idle
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


property write_write_buf_eventually_left_p;
  write_buf
|->
  s_eventually(!write_buf);
endproperty
write_write_buf_eventually_left_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) write_write_buf_eventually_left_p);


property write_write_mem_eventually_left_p;
  write_mem
|->
  s_eventually(!write_mem);
endproperty
write_write_mem_eventually_left_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) write_write_mem_eventually_left_p);


property write_write_wait_eventually_left_p;
  write_wait
|->
  s_eventually(!write_wait);
endproperty
write_write_wait_eventually_left_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) write_write_wait_eventually_left_p);


parameter CONSISTENCY = 1;
if (CONSISTENCY) begin
  // Check that no more than 1 state condition is met at the same time
  read_consistency_onehot0_state: assert property($onehot0({ read_exec, read_idle, read_stage }));
end


if (CONSISTENCY) begin
  // Check that no more than 1 state condition is met at the same time
  write_consistency_onehot0_state: assert property($onehot0({ write_buf, write_idle, write_mem, write_stage, write_wait }));
end


endmodule
