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


import ntt_ctrl_pwo_pairwm_pkg::*;
import abr_params_pkg::*;
import ntt_defines_pkg::*;
import ntt_ctrl_pwo_pairwm_functions::*;
import ntt_ctrl_pwo_pairwm_pkg::*;


module fv_ntt_ctrl_pwo_pairwm_m(
  input logic rst_n,
  input logic clk,

  // Ports
  input logic unsigned [2:0] ntt_mode_in,

  input logic ntt_enable_in,

  input logic buf0_valid_in,

  input logic butterfly_ready_in,

  input logic sampler_valid_in,

  input logic accumulate_in,

  input logic shuffle_en_in,

  input st_PwoMemAddrs pwo_mem_base_addr_in,

  input logic unsigned [5:0] random_in,

  input logic masking_en_in,

  input logic mlkem_in,

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
  input logic unsigned [2:0] bf_enable_reg,
  input logic unsigned [2:0] bf_enable_reg_dummy,
  input logic unsigned [1:0] buf_count,
  input logic unsigned [547:0] buf_rdptr_reg,
  input logic unsigned [3:0] chunk_count,
  input logic unsigned [1087:0] chunk_count_reg,
  input logic unsigned [3:0] chunk_rand_offset,
  input logic unsigned [211:0] incr_pw_rd_addr_reg,
  input logic incr_twiddle_addr_reg,
  input logic unsigned [1:0] index_count,
  input logic unsigned [1:0] index_rand_offset,
  input logic unsigned [1:0] masked_pwm_buf_rdptr_d1,
  input logic unsigned [1:0] masked_pwm_buf_rdptr_d2,
  input logic unsigned [1:0] masked_pwm_buf_rdptr_d3,
  input logic unsigned [14:0] pw_mem_rd_addr_a_reg,
  input logic unsigned [14:0] pw_mem_rd_addr_b_reg,
  input logic unsigned [14:0] pw_mem_rd_addr_c_reg,
  input logic unsigned [14:0] pw_mem_wr_addr_c_reg,
  input logic unsigned [211:0] pw_rden_fsm_reg,
  input logic pw_rden_reg,
  input logic pw_rden_reg_dummy,
  input logic pw_wren_reg,
  input logic pw_wren_reg_dummy,
  input logic unsigned [6:0] rd_valid_count,
  input e_PwoReadStatesType read_state,
  input logic unsigned [2:0] rounds_count,
  input logic shuffled_pw_rden_fsm_reg,
  input logic shuffled_pw_rden_fsm_reg_dummy,
  input logic unsigned [6:0] twiddle_addr_reg,
  input logic unsigned [6:0] twiddle_addr_reg_d2,
  input logic unsigned [6:0] twiddle_addr_reg_d3,
  input logic unsigned [6:0] twiddle_addr_reg_d3_dummy,
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


a_unsigned_7_8 getTwiddleRandOffsets_0_i;
assign getTwiddleRandOffsets_0_i = getTwiddleRandOffsets(chunk_count_reg, chunk_count, buf_count, (mlkem_in && (ntt_mode_in == 3'd5)));

a_unsigned_7_8 twiddle_offset_array_0_i;
assign twiddle_offset_array_0_i = '{
  0: ((mlkem_in && (ntt_mode_in == 3'd5)) ? 7'd21 : 7'd0),
  1: 7'd64,
  2: 7'd80,
  3: 7'd84,
  4: 7'd0,
  5: 7'd0,
  6: 7'd0,
  7: 7'd0
};

logic unsigned [6:0] getTwiddleIncrAddr_0_i;
assign getTwiddleIncrAddr_0_i = getTwiddleIncrAddr(shuffle_en_in, rounds_count, getTwiddleRandOffsets_0_i, '{ 0: 7'd63, 1: 7'd15, 2: 7'd3, 3: 7'd0, 4: 7'd0, 5: 7'd0, 6: 7'd0, 7: 7'd0 }, twiddle_addr_reg);

logic unsigned [6:0] getTwiddleAddrReg_0_i;
assign getTwiddleAddrReg_0_i = getTwiddleAddrReg(incr_twiddle_addr_reg, ((read_state == PwoReadIdle) || ((read_state == PwoReadStage) && !butterfly_ready_in)), getTwiddleIncrAddr_0_i, twiddle_addr_reg);

logic unsigned [1:0] getMemRdIndexOfst_0_i;
assign getMemRdIndexOfst_0_i = getMemRdIndexOfst(index_count, index_rand_offset);

logic unsigned [14:0] getPwAddrNxt_0_i;
assign getPwAddrNxt_0_i = getPwAddrNxt(pwo_mem_base_addr_in.pw_base_addr_a, chunk_count, 15'd1, ({ 13'd0, getMemRdIndexOfst_0_i} ));

logic unsigned [14:0] getPwAddrNxt_1_i;
assign getPwAddrNxt_1_i = getPwAddrNxt(pwo_mem_base_addr_in.pw_base_addr_b, chunk_count, 15'd1, ({ 13'd0, getMemRdIndexOfst_0_i} ));

logic unsigned [14:0] getPwAddrCnxt_0_i;
assign getPwAddrCnxt_0_i = getPwAddrCnxt((ntt_mode_in == 3'd2), (mlkem_in && (ntt_mode_in == 3'd5)), mlkem_in, accumulate_in, shuffle_en_in, masking_en_in, pw_mem_rd_addr_c_reg, (((ntt_mode_in == 3'd2) && masking_en_in) ? ((pwo_mem_base_addr_in.pw_base_addr_c + (15'd4 * ({ 11'd0, chunk_count_reg[243:240]} ))) + ({ 13'd0, buf_rdptr_reg[107:106]} )) : 15'd0), (((mlkem_in && (ntt_mode_in == 3'd5)) && masking_en_in) ? ((pwo_mem_base_addr_in.pw_base_addr_c + (15'd4 * ({ 11'd0, chunk_count_reg[43:40]} ))) + ({ 13'd0, buf_rdptr_reg[15:14]} )) : 15'd0), ((pwo_mem_base_addr_in.pw_base_addr_c + (15'd4 * ({ 11'd0, chunk_count} ))) + ({ 13'd0, getMemRdIndexOfst_0_i} )));

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

logic unsigned [14:0] getPwAddrCrd_0_i;
assign getPwAddrCrd_0_i = getPwAddrCrd(((write_state == PwoWriteIdle) || (write_state == PwoWriteStage)), shuffle_en_in, (ntt_mode_in == 3'd2), (mlkem_in && (ntt_mode_in == 3'd5)), mlkem_in, accumulate_in, masking_en_in, incr_pw_rd_addr_reg, 0, chunk_rand_offset, pwo_mem_base_addr_in.pw_base_addr_c, getPwAddrCnxt_0_i, pw_mem_rd_addr_c_reg);

logic unsigned [211:0] getPwRdenFsmReg_0_i;
assign getPwRdenFsmReg_0_i = getPwRdenFsmReg(pw_rden_fsm_reg, 0);

logic unsigned [547:0] getBufRdptrReg_0_i;
assign getBufRdptrReg_0_i = getBufRdptrReg(masking_en_in, butterfly_ready_in, accumulate_in, 0, (ntt_mode_in == 3'd2), (mlkem_in && (ntt_mode_in == 3'd5)), ((masking_en_in && ((ntt_mode_in == 3'd2) || (mlkem_in && (ntt_mode_in == 3'd5)))) && ((!(read_state == PwoReadIdle) && !(read_state == PwoReadStage)) || (!(write_state == PwoWriteIdle) && !(write_state == PwoWriteStage)))), buf_rdptr_reg, getMemRdIndexOfst_0_i);

logic unsigned [1087:0] getChunkCountReg_0_i;
assign getChunkCountReg_0_i = getChunkCountReg((ntt_mode_in == 3'd2), (mlkem_in && (ntt_mode_in == 3'd5)), accumulate_in, masking_en_in, ((masking_en_in && ((ntt_mode_in == 3'd2) || (mlkem_in && (ntt_mode_in == 3'd5)))) && ((!(read_state == PwoReadIdle) && !(read_state == PwoReadStage)) || (!(write_state == PwoWriteIdle) && !(write_state == PwoWriteStage)))), butterfly_ready_in, 0, chunk_count_reg, chunk_count);

logic unsigned [211:0] getIncrPwRdAddrReg_0_i;
assign getIncrPwRdAddrReg_0_i = getIncrPwRdAddrReg(masking_en_in, (ntt_mode_in == 3'd2), (mlkem_in && (ntt_mode_in == 3'd5)), incr_pw_rd_addr_reg, 0);

logic unsigned [14:0] getPwAddrAbcWr_2_i;
assign getPwAddrAbcWr_2_i = getPwAddrAbcWr(((write_state == PwoWriteIdle) || (write_state == PwoWriteStage)), sampler_valid_in, getPwAddrRst_0_i, getPwAddrIncrAbcWr_0_i, pw_mem_rd_addr_a_reg);

logic unsigned [14:0] getPwAddrAbcWr_3_i;
assign getPwAddrAbcWr_3_i = getPwAddrAbcWr(((write_state == PwoWriteIdle) || (write_state == PwoWriteStage)), sampler_valid_in, getPwAddrRst_1_i, getPwAddrIncrAbcWr_1_i, pw_mem_rd_addr_b_reg);

logic unsigned [14:0] getPwAddrCrd_1_i;
assign getPwAddrCrd_1_i = getPwAddrCrd(((write_state == PwoWriteIdle) || (write_state == PwoWriteStage)), shuffle_en_in, (ntt_mode_in == 3'd2), (mlkem_in && (ntt_mode_in == 3'd5)), mlkem_in, accumulate_in, masking_en_in, incr_pw_rd_addr_reg, sampler_valid_in, chunk_rand_offset, pwo_mem_base_addr_in.pw_base_addr_c, getPwAddrCnxt_0_i, pw_mem_rd_addr_c_reg);

logic unsigned [211:0] getPwRdenFsmReg_1_i;
assign getPwRdenFsmReg_1_i = getPwRdenFsmReg(pw_rden_fsm_reg, sampler_valid_in);

logic unsigned [547:0] getBufRdptrReg_1_i;
assign getBufRdptrReg_1_i = getBufRdptrReg(masking_en_in, butterfly_ready_in, accumulate_in, sampler_valid_in, (ntt_mode_in == 3'd2), (mlkem_in && (ntt_mode_in == 3'd5)), ((masking_en_in && ((ntt_mode_in == 3'd2) || (mlkem_in && (ntt_mode_in == 3'd5)))) && ((!(read_state == PwoReadIdle) && !(read_state == PwoReadStage)) || (!(write_state == PwoWriteIdle) && !(write_state == PwoWriteStage)))), buf_rdptr_reg, getMemRdIndexOfst_0_i);

logic unsigned [1087:0] getChunkCountReg_1_i;
assign getChunkCountReg_1_i = getChunkCountReg((ntt_mode_in == 3'd2), (mlkem_in && (ntt_mode_in == 3'd5)), accumulate_in, masking_en_in, ((masking_en_in && ((ntt_mode_in == 3'd2) || (mlkem_in && (ntt_mode_in == 3'd5)))) && ((!(read_state == PwoReadIdle) && !(read_state == PwoReadStage)) || (!(write_state == PwoWriteIdle) && !(write_state == PwoWriteStage)))), butterfly_ready_in, sampler_valid_in, chunk_count_reg, chunk_count);

logic unsigned [211:0] getIncrPwRdAddrReg_1_i;
assign getIncrPwRdAddrReg_1_i = getIncrPwRdAddrReg(masking_en_in, (ntt_mode_in == 3'd2), (mlkem_in && (ntt_mode_in == 3'd5)), incr_pw_rd_addr_reg, sampler_valid_in);

logic unsigned [14:0] getMaskedShuffledPwmMemWrAddrCnxtAccumulate_0_i;
assign getMaskedShuffledPwmMemWrAddrCnxtAccumulate_0_i = getMaskedShuffledPwmMemWrAddrCnxtAccumulate(pwo_mem_base_addr_in.pw_base_addr_c, chunk_count_reg, masked_pwm_buf_rdptr_d3);

logic unsigned [14:0] getMlkemMaskedShuffledPwmMemWrAddrCnxtAccumulate_0_i;
assign getMlkemMaskedShuffledPwmMemWrAddrCnxtAccumulate_0_i = getMlkemMaskedShuffledPwmMemWrAddrCnxtAccumulate(pwo_mem_base_addr_in.pw_base_addr_c, chunk_count_reg, masked_pwm_buf_rdptr_d3);

logic unsigned [14:0] getMaskedShuffledPwmMemWrAddrCnxt_0_i;
assign getMaskedShuffledPwmMemWrAddrCnxt_0_i = getMaskedShuffledPwmMemWrAddrCnxt(pwo_mem_base_addr_in.pw_base_addr_c, chunk_count_reg, masked_pwm_buf_rdptr_d2);

logic unsigned [14:0] getMlkemMaskedShuffledPwmMemWrAddrCnxt_0_i;
assign getMlkemMaskedShuffledPwmMemWrAddrCnxt_0_i = getMlkemMaskedShuffledPwmMemWrAddrCnxt(pwo_mem_base_addr_in.pw_base_addr_c, chunk_count_reg, masked_pwm_buf_rdptr_d3);

logic unsigned [14:0] getShuffledPwMemWrAddrCnxt_0_i;
assign getShuffledPwMemWrAddrCnxt_0_i = getShuffledPwMemWrAddrCnxt((ntt_mode_in == 3'd2), (ntt_mode_in == 3'd3), (ntt_mode_in == 3'd4), (mlkem_in && (ntt_mode_in == 3'd5)), accumulate_in, pwo_mem_base_addr_in.pw_base_addr_c, chunk_count_reg, buf_rdptr_reg);

logic unsigned [14:0] getPwAddrCwr_0_i;
assign getPwAddrCwr_0_i = getPwAddrCwr(1, (((write_state == PwoWriteMem) && butterfly_ready_in) || ((write_state == PwoWriteWait) && (butterfly_ready_in || shuffle_en_in))), shuffle_en_in, masking_en_in, accumulate_in, mlkem_in, chunk_rand_offset, pwo_mem_base_addr_in.pw_base_addr_c, getMaskedShuffledPwmMemWrAddrCnxtAccumulate_0_i, getMlkemMaskedShuffledPwmMemWrAddrCnxtAccumulate_0_i, getMaskedShuffledPwmMemWrAddrCnxt_0_i, getMlkemMaskedShuffledPwmMemWrAddrCnxt_0_i, getShuffledPwMemWrAddrCnxt_0_i, pw_mem_wr_addr_c_reg);

logic unsigned [14:0] getPwAddrCwr_1_i;
assign getPwAddrCwr_1_i = getPwAddrCwr(0, (((write_state == PwoWriteMem) && butterfly_ready_in) || ((write_state == PwoWriteWait) && (butterfly_ready_in || shuffle_en_in))), shuffle_en_in, masking_en_in, accumulate_in, mlkem_in, chunk_rand_offset, pwo_mem_base_addr_in.pw_base_addr_c, getMaskedShuffledPwmMemWrAddrCnxtAccumulate_0_i, getMlkemMaskedShuffledPwmMemWrAddrCnxtAccumulate_0_i, getMaskedShuffledPwmMemWrAddrCnxt_0_i, getMlkemMaskedShuffledPwmMemWrAddrCnxt_0_i, getShuffledPwMemWrAddrCnxt_0_i, pw_mem_wr_addr_c_reg);


sequence reset_sequence;
  !rst_n ##1 rst_n;
endsequence


property commons_reset_p;
  $past(!ntt_ctrl.reset_n || ntt_ctrl.zeroize) |->
  state &&
  buf_count == 2'd0 &&
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
  $past(!ntt_ctrl.reset_n || ntt_ctrl.zeroize) |->
  read_idle &&
  bf_enable_reg == 3'd0 &&
  buf_rdptr_reg == 548'd0 &&
  chunk_count_reg == 1088'd0 &&
  incr_pw_rd_addr_reg == 212'd0 &&
  incr_twiddle_addr_reg == 0 &&
  pw_mem_rd_addr_a_out == 15'd0 &&
  pw_mem_rd_addr_a_reg == 15'd0 &&
  pw_mem_rd_addr_b_out == 15'd0 &&
  pw_mem_rd_addr_b_reg == 15'd0 &&
  pw_mem_rd_addr_c_out == 15'd0 &&
  pw_mem_rd_addr_c_reg == 15'd0 &&
  pw_rden_fsm_reg == 212'd0 &&
  pw_rden_reg == 0 &&
  rd_valid_count == 7'd0 &&
  read_state == PwoReadIdle &&
  shuffled_pw_rden_fsm_reg == 0 &&
  twiddle_addr_reg == 7'd0 &&
  twiddle_addr_reg_d2 == 7'd0 &&
  twiddle_addr_reg_d3 == 7'd0;
endproperty
read_reset_a: assert property (read_reset_p);


property write_reset_p;
  $past(!ntt_ctrl.reset_n || ntt_ctrl.zeroize) |->
  write_idle &&
  chunk_count == 4'd0 &&
  chunk_rand_offset == 4'd0 &&
  done_out == 0 &&
  index_count == 2'd0 &&
  index_rand_offset == 2'd0 &&
  masked_pwm_buf_rdptr_d1 == 2'd0 &&
  masked_pwm_buf_rdptr_d2 == 2'd0 &&
  masked_pwm_buf_rdptr_d3 == 2'd0 &&
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
  ##1 ($stable(buf_rd_rst_count_out) &&
    $stable(buf_rden_out) &&
    $stable(buf_wr_rst_count_out) &&
    $stable(buf_wren_out) &&
    $stable(buf_wrptr_out) &&
    $stable(masking_en_ctrl_out) &&
    $stable(mem_rd_en_out) &&
    $stable(mem_wr_en_out)) and
  ##1
  state &&
  buf_count == (($past(buf0_valid_in, 1) || ((({ 62'd0, $past(buf_count, 1)} ) > 64'd0) && (({ 62'd0, $past(buf_count, 1)} ) < 64'd3))) ? (2'd1 + $past(buf_count, 1)) : 2'd0) &&
  buf_rdptr_out == (($past(buf0_valid_in, 1) || ((({ 62'd0, $past(buf_count, 1)} ) > 64'd0) && (({ 62'd0, $past(buf_count, 1)} ) < 64'd3))) ? (2'd1 + $past(buf_count, 1)) : 2'd0) &&
  opcode_out == $past(ntt_mode_in, 1);
endproperty
commons_state_to_state_a: assert property (disable iff(!ntt_ctrl.reset_n || ntt_ctrl.zeroize) commons_state_to_state_p);


property read_read_exec_to_read_exec_p;
  read_exec &&
  (sampler_valid_in || (({ 57'd0, rd_valid_count} ) >= 64'h40)) &&
  (rd_valid_count < 7'h3F)
|->
  ##1
  read_exec &&
  bf_enable_reg == ({ { $past(bf_enable_reg, 1) }[1:0], 1'd1} ) &&
  buf_rdptr_reg == $past(getBufRdptrReg_1_i, 1) &&
  chunk_count_reg == $past(getChunkCountReg_1_i, 1) &&
  incr_pw_rd_addr_reg == $past(getIncrPwRdAddrReg_1_i, 1) &&
  incr_twiddle_addr_reg == ((((($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait)) && $past(mlkem_in, 1)) && ($past(ntt_mode_in, 1) == 3'd5)) && $past(sampler_valid_in, 1)) &&
  pw_mem_rd_addr_a_out == $past(getPwAddrAbcWr_2_i, 1) &&
  pw_mem_rd_addr_a_reg == $past(getPwAddrAbcWr_2_i, 1) &&
  pw_mem_rd_addr_b_out == $past(getPwAddrAbcWr_3_i, 1) &&
  pw_mem_rd_addr_b_reg == $past(getPwAddrAbcWr_3_i, 1) &&
  pw_mem_rd_addr_c_out == $past(getPwAddrCrd_1_i, 1) &&
  pw_mem_rd_addr_c_reg == $past(getPwAddrCrd_1_i, 1) &&
  pw_rden_fsm_reg == $past(getPwRdenFsmReg_1_i, 1) &&
  pw_rden_reg == $past(sampler_valid_in, 1) &&
  rd_valid_count == ((($past(read_state, 1) == PwoReadIdle) || ($past(read_state, 1) == PwoReadStage)) ? 7'd0 : ($past(sampler_valid_in, 1) ? (7'd1 + $past(rd_valid_count, 1)) : $past(rd_valid_count, 1))) &&
  read_state == PwoReadExec &&
  shuffled_pw_rden_fsm_reg == ($past(mlkem_in, 1) ? ({ $past(pw_rden_fsm_reg, 1) }[193] != 0) : ({ $past(pw_rden_fsm_reg, 1) }[0] != 0)) &&
  twiddle_addr_reg == $past(getTwiddleAddrReg_0_i, 1) &&
  twiddle_addr_reg_d2 == ($past(shuffle_en_in, 1) ? ((($past(shuffle_en_in, 1) && $past(mlkem_in, 1)) && ($past(ntt_mode_in, 1) == 3'd5)) ? (($past(getTwiddleRandOffsets_0_i[rounds_count], 1) + ({ 5'd0, 2'(($past(index_count, 1) + $past(index_rand_offset, 1)))} )) + $past(twiddle_offset_array_0_i[rounds_count], 1)) : ($past(getTwiddleRandOffsets_0_i[rounds_count], 1) + $past(twiddle_offset_array_0_i[rounds_count], 1))) : ($past(twiddle_addr_reg, 1) + $past(twiddle_offset_array_0_i[rounds_count], 1))) &&
  twiddle_addr_reg_d3 == $past(twiddle_addr_reg_d2, 1);
endproperty
read_read_exec_to_read_exec_a: assert property (disable iff(!ntt_ctrl.reset_n || ntt_ctrl.zeroize) read_read_exec_to_read_exec_p);


property read_read_exec_to_read_exec_wait_p;
  read_exec &&
  !sampler_valid_in &&
  (({ 57'd0, rd_valid_count} ) < 64'h40)
|->
  ##1
  read_exec_wait &&
  bf_enable_reg == ({ { $past(bf_enable_reg, 1) }[1:0], 1'd0} ) &&
  buf_rdptr_reg == $past(getBufRdptrReg_1_i, 1) &&
  chunk_count_reg == $past(getChunkCountReg_1_i, 1) &&
  incr_pw_rd_addr_reg == $past(getIncrPwRdAddrReg_1_i, 1) &&
  incr_twiddle_addr_reg == ((((($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait)) && $past(mlkem_in, 1)) && ($past(ntt_mode_in, 1) == 3'd5)) && $past(sampler_valid_in, 1)) &&
  pw_mem_rd_addr_a_out == $past(getPwAddrAbcWr_2_i, 1) &&
  pw_mem_rd_addr_a_reg == $past(getPwAddrAbcWr_2_i, 1) &&
  pw_mem_rd_addr_b_out == $past(getPwAddrAbcWr_3_i, 1) &&
  pw_mem_rd_addr_b_reg == $past(getPwAddrAbcWr_3_i, 1) &&
  pw_mem_rd_addr_c_out == $past(getPwAddrCrd_1_i, 1) &&
  pw_mem_rd_addr_c_reg == $past(getPwAddrCrd_1_i, 1) &&
  pw_rden_fsm_reg == $past(getPwRdenFsmReg_1_i, 1) &&
  pw_rden_reg == $past(sampler_valid_in, 1) &&
  rd_valid_count == ((($past(read_state, 1) == PwoReadIdle) || ($past(read_state, 1) == PwoReadStage)) ? 7'd0 : ($past(sampler_valid_in, 1) ? (7'd1 + $past(rd_valid_count, 1)) : $past(rd_valid_count, 1))) &&
  read_state == PwoReadExecWait &&
  shuffled_pw_rden_fsm_reg == ($past(mlkem_in, 1) ? ({ $past(pw_rden_fsm_reg, 1) }[193] != 0) : ({ $past(pw_rden_fsm_reg, 1) }[0] != 0)) &&
  twiddle_addr_reg == $past(getTwiddleAddrReg_0_i, 1) &&
  twiddle_addr_reg_d2 == ($past(shuffle_en_in, 1) ? ((($past(shuffle_en_in, 1) && $past(mlkem_in, 1)) && ($past(ntt_mode_in, 1) == 3'd5)) ? (($past(getTwiddleRandOffsets_0_i[rounds_count], 1) + ({ 5'd0, 2'(($past(index_count, 1) + $past(index_rand_offset, 1)))} )) + $past(twiddle_offset_array_0_i[rounds_count], 1)) : ($past(getTwiddleRandOffsets_0_i[rounds_count], 1) + $past(twiddle_offset_array_0_i[rounds_count], 1))) : ($past(twiddle_addr_reg, 1) + $past(twiddle_offset_array_0_i[rounds_count], 1))) &&
  twiddle_addr_reg_d3 == $past(twiddle_addr_reg_d2, 1);
endproperty
read_read_exec_to_read_exec_wait_a: assert property (disable iff(!ntt_ctrl.reset_n || ntt_ctrl.zeroize) read_read_exec_to_read_exec_wait_p);


property read_read_exec_to_read_stage_p;
  read_exec &&
  (sampler_valid_in || (({ 57'd0, rd_valid_count} ) >= 64'h40)) &&
  (rd_valid_count >= 7'h3F)
|->
  ##1
  read_stage &&
  bf_enable_reg == (({ { $past(bf_enable_reg, 1) }[1:0], 1'd0} ) | ($past(sampler_valid_in, 1) ? 3'd1 : 3'd0)) &&
  buf_rdptr_reg == $past(getBufRdptrReg_1_i, 1) &&
  chunk_count_reg == $past(getChunkCountReg_1_i, 1) &&
  incr_pw_rd_addr_reg == $past(getIncrPwRdAddrReg_1_i, 1) &&
  incr_twiddle_addr_reg == ((((($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait)) && $past(mlkem_in, 1)) && ($past(ntt_mode_in, 1) == 3'd5)) && $past(sampler_valid_in, 1)) &&
  pw_mem_rd_addr_a_out == $past(getPwAddrAbcWr_2_i, 1) &&
  pw_mem_rd_addr_a_reg == $past(getPwAddrAbcWr_2_i, 1) &&
  pw_mem_rd_addr_b_out == $past(getPwAddrAbcWr_3_i, 1) &&
  pw_mem_rd_addr_b_reg == $past(getPwAddrAbcWr_3_i, 1) &&
  pw_mem_rd_addr_c_out == $past(getPwAddrCrd_1_i, 1) &&
  pw_mem_rd_addr_c_reg == $past(getPwAddrCrd_1_i, 1) &&
  pw_rden_fsm_reg == $past(getPwRdenFsmReg_1_i, 1) &&
  pw_rden_reg == $past(sampler_valid_in, 1) &&
  rd_valid_count == ((($past(read_state, 1) == PwoReadIdle) || ($past(read_state, 1) == PwoReadStage)) ? 7'd0 : ($past(sampler_valid_in, 1) ? (7'd1 + $past(rd_valid_count, 1)) : $past(rd_valid_count, 1))) &&
  read_state == PwoReadStage &&
  shuffled_pw_rden_fsm_reg == ($past(mlkem_in, 1) ? ({ $past(pw_rden_fsm_reg, 1) }[193] != 0) : ({ $past(pw_rden_fsm_reg, 1) }[0] != 0)) &&
  twiddle_addr_reg == $past(getTwiddleAddrReg_0_i, 1) &&
  twiddle_addr_reg_d2 == ($past(shuffle_en_in, 1) ? ((($past(shuffle_en_in, 1) && $past(mlkem_in, 1)) && ($past(ntt_mode_in, 1) == 3'd5)) ? (($past(getTwiddleRandOffsets_0_i[rounds_count], 1) + ({ 5'd0, 2'(($past(index_count, 1) + $past(index_rand_offset, 1)))} )) + $past(twiddle_offset_array_0_i[rounds_count], 1)) : ($past(getTwiddleRandOffsets_0_i[rounds_count], 1) + $past(twiddle_offset_array_0_i[rounds_count], 1))) : ($past(twiddle_addr_reg, 1) + $past(twiddle_offset_array_0_i[rounds_count], 1))) &&
  twiddle_addr_reg_d3 == $past(twiddle_addr_reg_d2, 1);
endproperty
read_read_exec_to_read_stage_a: assert property (disable iff(!ntt_ctrl.reset_n || ntt_ctrl.zeroize) read_read_exec_to_read_stage_p);


property read_read_exec_wait_to_read_exec_p;
  read_exec_wait &&
  sampler_valid_in
|->
  ##1
  read_exec &&
  bf_enable_reg == ({ { $past(bf_enable_reg, 1) }[1:0], 1'd1} ) &&
  buf_rdptr_reg == $past(getBufRdptrReg_1_i, 1) &&
  chunk_count_reg == $past(getChunkCountReg_1_i, 1) &&
  incr_pw_rd_addr_reg == $past(getIncrPwRdAddrReg_1_i, 1) &&
  incr_twiddle_addr_reg == ((((($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait)) && $past(mlkem_in, 1)) && ($past(ntt_mode_in, 1) == 3'd5)) && $past(sampler_valid_in, 1)) &&
  pw_mem_rd_addr_a_out == $past(getPwAddrAbcWr_2_i, 1) &&
  pw_mem_rd_addr_a_reg == $past(getPwAddrAbcWr_2_i, 1) &&
  pw_mem_rd_addr_b_out == $past(getPwAddrAbcWr_3_i, 1) &&
  pw_mem_rd_addr_b_reg == $past(getPwAddrAbcWr_3_i, 1) &&
  pw_mem_rd_addr_c_out == $past(getPwAddrCrd_1_i, 1) &&
  pw_mem_rd_addr_c_reg == $past(getPwAddrCrd_1_i, 1) &&
  pw_rden_fsm_reg == $past(getPwRdenFsmReg_1_i, 1) &&
  pw_rden_reg == $past(sampler_valid_in, 1) &&
  rd_valid_count == ((($past(read_state, 1) == PwoReadIdle) || ($past(read_state, 1) == PwoReadStage)) ? 7'd0 : ($past(sampler_valid_in, 1) ? (7'd1 + $past(rd_valid_count, 1)) : $past(rd_valid_count, 1))) &&
  read_state == PwoReadExec &&
  shuffled_pw_rden_fsm_reg == ($past(mlkem_in, 1) ? ({ $past(pw_rden_fsm_reg, 1) }[193] != 0) : ({ $past(pw_rden_fsm_reg, 1) }[0] != 0)) &&
  twiddle_addr_reg == $past(getTwiddleAddrReg_0_i, 1) &&
  twiddle_addr_reg_d2 == ($past(shuffle_en_in, 1) ? ((($past(shuffle_en_in, 1) && $past(mlkem_in, 1)) && ($past(ntt_mode_in, 1) == 3'd5)) ? (($past(getTwiddleRandOffsets_0_i[rounds_count], 1) + ({ 5'd0, 2'(($past(index_count, 1) + $past(index_rand_offset, 1)))} )) + $past(twiddle_offset_array_0_i[rounds_count], 1)) : ($past(getTwiddleRandOffsets_0_i[rounds_count], 1) + $past(twiddle_offset_array_0_i[rounds_count], 1))) : ($past(twiddle_addr_reg, 1) + $past(twiddle_offset_array_0_i[rounds_count], 1))) &&
  twiddle_addr_reg_d3 == $past(twiddle_addr_reg_d2, 1);
endproperty
read_read_exec_wait_to_read_exec_a: assert property (disable iff(!ntt_ctrl.reset_n || ntt_ctrl.zeroize) read_read_exec_wait_to_read_exec_p);


property read_read_exec_wait_to_read_exec_wait_p;
  read_exec_wait &&
  !sampler_valid_in
|->
  ##1
  read_exec_wait &&
  bf_enable_reg == ({ { $past(bf_enable_reg, 1) }[1:0], 1'd0} ) &&
  buf_rdptr_reg == $past(getBufRdptrReg_1_i, 1) &&
  chunk_count_reg == $past(getChunkCountReg_1_i, 1) &&
  incr_pw_rd_addr_reg == $past(getIncrPwRdAddrReg_1_i, 1) &&
  incr_twiddle_addr_reg == ((((($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait)) && $past(mlkem_in, 1)) && ($past(ntt_mode_in, 1) == 3'd5)) && $past(sampler_valid_in, 1)) &&
  pw_mem_rd_addr_a_out == $past(getPwAddrAbcWr_2_i, 1) &&
  pw_mem_rd_addr_a_reg == $past(getPwAddrAbcWr_2_i, 1) &&
  pw_mem_rd_addr_b_out == $past(getPwAddrAbcWr_3_i, 1) &&
  pw_mem_rd_addr_b_reg == $past(getPwAddrAbcWr_3_i, 1) &&
  pw_mem_rd_addr_c_out == $past(getPwAddrCrd_1_i, 1) &&
  pw_mem_rd_addr_c_reg == $past(getPwAddrCrd_1_i, 1) &&
  pw_rden_fsm_reg == $past(getPwRdenFsmReg_1_i, 1) &&
  pw_rden_reg == $past(sampler_valid_in, 1) &&
  rd_valid_count == ((($past(read_state, 1) == PwoReadIdle) || ($past(read_state, 1) == PwoReadStage)) ? 7'd0 : ($past(sampler_valid_in, 1) ? (7'd1 + $past(rd_valid_count, 1)) : $past(rd_valid_count, 1))) &&
  read_state == PwoReadExecWait &&
  shuffled_pw_rden_fsm_reg == ($past(mlkem_in, 1) ? ({ $past(pw_rden_fsm_reg, 1) }[193] != 0) : ({ $past(pw_rden_fsm_reg, 1) }[0] != 0)) &&
  twiddle_addr_reg == $past(getTwiddleAddrReg_0_i, 1) &&
  twiddle_addr_reg_d2 == ($past(shuffle_en_in, 1) ? ((($past(shuffle_en_in, 1) && $past(mlkem_in, 1)) && ($past(ntt_mode_in, 1) == 3'd5)) ? (($past(getTwiddleRandOffsets_0_i[rounds_count], 1) + ({ 5'd0, 2'(($past(index_count, 1) + $past(index_rand_offset, 1)))} )) + $past(twiddle_offset_array_0_i[rounds_count], 1)) : ($past(getTwiddleRandOffsets_0_i[rounds_count], 1) + $past(twiddle_offset_array_0_i[rounds_count], 1))) : ($past(twiddle_addr_reg, 1) + $past(twiddle_offset_array_0_i[rounds_count], 1))) &&
  twiddle_addr_reg_d3 == $past(twiddle_addr_reg_d2, 1);
endproperty
read_read_exec_wait_to_read_exec_wait_a: assert property (disable iff(!ntt_ctrl.reset_n || ntt_ctrl.zeroize) read_read_exec_wait_to_read_exec_wait_p);


property read_read_idle_to_read_idle_p;
  read_idle &&
  !ntt_enable_in
|->
  ##1
  read_idle &&
  bf_enable_reg == ({ { $past(bf_enable_reg, 1) }[1:0], 1'd0} ) &&
  buf_rdptr_reg == $past(getBufRdptrReg_0_i, 1) &&
  chunk_count_reg == $past(getChunkCountReg_0_i, 1) &&
  incr_pw_rd_addr_reg == $past(getIncrPwRdAddrReg_0_i, 1) &&
  incr_twiddle_addr_reg == ((((($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait)) && $past(mlkem_in, 1)) && ($past(ntt_mode_in, 1) == 3'd5)) && $past(sampler_valid_in, 1)) &&
  pw_mem_rd_addr_a_out == $past(getPwAddrAbcWr_0_i, 1) &&
  pw_mem_rd_addr_a_reg == $past(getPwAddrAbcWr_0_i, 1) &&
  pw_mem_rd_addr_b_out == $past(getPwAddrAbcWr_1_i, 1) &&
  pw_mem_rd_addr_b_reg == $past(getPwAddrAbcWr_1_i, 1) &&
  pw_mem_rd_addr_c_out == $past(getPwAddrCrd_0_i, 1) &&
  pw_mem_rd_addr_c_reg == $past(getPwAddrCrd_0_i, 1) &&
  pw_rden_fsm_reg == $past(getPwRdenFsmReg_0_i, 1) &&
  pw_rden_reg == 0 &&
  rd_valid_count == ((($past(read_state, 1) == PwoReadIdle) || ($past(read_state, 1) == PwoReadStage)) ? 7'd0 : ($past(sampler_valid_in, 1) ? (7'd1 + $past(rd_valid_count, 1)) : $past(rd_valid_count, 1))) &&
  read_state == PwoReadIdle &&
  shuffled_pw_rden_fsm_reg == ($past(mlkem_in, 1) ? ({ $past(pw_rden_fsm_reg, 1) }[193] != 0) : ({ $past(pw_rden_fsm_reg, 1) }[0] != 0)) &&
  twiddle_addr_reg == $past(getTwiddleAddrReg_0_i, 1) &&
  twiddle_addr_reg_d2 == ($past(shuffle_en_in, 1) ? ((($past(shuffle_en_in, 1) && $past(mlkem_in, 1)) && ($past(ntt_mode_in, 1) == 3'd5)) ? (($past(getTwiddleRandOffsets_0_i[rounds_count], 1) + ({ 5'd0, 2'(($past(index_count, 1) + $past(index_rand_offset, 1)))} )) + $past(twiddle_offset_array_0_i[rounds_count], 1)) : ($past(getTwiddleRandOffsets_0_i[rounds_count], 1) + $past(twiddle_offset_array_0_i[rounds_count], 1))) : ($past(twiddle_addr_reg, 1) + $past(twiddle_offset_array_0_i[rounds_count], 1))) &&
  twiddle_addr_reg_d3 == $past(twiddle_addr_reg_d2, 1);
endproperty
read_read_idle_to_read_idle_a: assert property (disable iff(!ntt_ctrl.reset_n || ntt_ctrl.zeroize) read_read_idle_to_read_idle_p);


property read_read_idle_to_read_stage_p;
  read_idle &&
  ntt_enable_in
|->
  ##1
  read_stage &&
  bf_enable_reg == ({ { $past(bf_enable_reg, 1) }[1:0], 1'd0} ) &&
  buf_rdptr_reg == $past(getBufRdptrReg_0_i, 1) &&
  chunk_count_reg == $past(getChunkCountReg_0_i, 1) &&
  incr_pw_rd_addr_reg == $past(getIncrPwRdAddrReg_0_i, 1) &&
  incr_twiddle_addr_reg == ((((($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait)) && $past(mlkem_in, 1)) && ($past(ntt_mode_in, 1) == 3'd5)) && $past(sampler_valid_in, 1)) &&
  pw_mem_rd_addr_a_out == $past(getPwAddrAbcWr_0_i, 1) &&
  pw_mem_rd_addr_a_reg == $past(getPwAddrAbcWr_0_i, 1) &&
  pw_mem_rd_addr_b_out == $past(getPwAddrAbcWr_1_i, 1) &&
  pw_mem_rd_addr_b_reg == $past(getPwAddrAbcWr_1_i, 1) &&
  pw_mem_rd_addr_c_out == $past(getPwAddrCrd_0_i, 1) &&
  pw_mem_rd_addr_c_reg == $past(getPwAddrCrd_0_i, 1) &&
  pw_rden_fsm_reg == $past(getPwRdenFsmReg_0_i, 1) &&
  pw_rden_reg == 0 &&
  rd_valid_count == ((($past(read_state, 1) == PwoReadIdle) || ($past(read_state, 1) == PwoReadStage)) ? 7'd0 : ($past(sampler_valid_in, 1) ? (7'd1 + $past(rd_valid_count, 1)) : $past(rd_valid_count, 1))) &&
  read_state == PwoReadStage &&
  shuffled_pw_rden_fsm_reg == ($past(mlkem_in, 1) ? ({ $past(pw_rden_fsm_reg, 1) }[193] != 0) : ({ $past(pw_rden_fsm_reg, 1) }[0] != 0)) &&
  twiddle_addr_reg == $past(getTwiddleAddrReg_0_i, 1) &&
  twiddle_addr_reg_d2 == ($past(shuffle_en_in, 1) ? ((($past(shuffle_en_in, 1) && $past(mlkem_in, 1)) && ($past(ntt_mode_in, 1) == 3'd5)) ? (($past(getTwiddleRandOffsets_0_i[rounds_count], 1) + ({ 5'd0, 2'(($past(index_count, 1) + $past(index_rand_offset, 1)))} )) + $past(twiddle_offset_array_0_i[rounds_count], 1)) : ($past(getTwiddleRandOffsets_0_i[rounds_count], 1) + $past(twiddle_offset_array_0_i[rounds_count], 1))) : ($past(twiddle_addr_reg, 1) + $past(twiddle_offset_array_0_i[rounds_count], 1))) &&
  twiddle_addr_reg_d3 == $past(twiddle_addr_reg_d2, 1);
endproperty
read_read_idle_to_read_stage_a: assert property (disable iff(!ntt_ctrl.reset_n || ntt_ctrl.zeroize) read_read_idle_to_read_stage_p);


property read_read_stage_to_read_exec_p;
  read_stage &&
  (write_state == PwoWriteStage) &&
  (rounds_count != 3'd1)
|->
  ##1
  read_exec &&
  bf_enable_reg == ({ { $past(bf_enable_reg, 1) }[1:0], 1'd0} ) &&
  buf_rdptr_reg == $past(getBufRdptrReg_0_i, 1) &&
  chunk_count_reg == $past(getChunkCountReg_0_i, 1) &&
  incr_pw_rd_addr_reg == $past(getIncrPwRdAddrReg_0_i, 1) &&
  incr_twiddle_addr_reg == ((((($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait)) && $past(mlkem_in, 1)) && ($past(ntt_mode_in, 1) == 3'd5)) && $past(sampler_valid_in, 1)) &&
  pw_mem_rd_addr_a_out == $past(getPwAddrAbcWr_0_i, 1) &&
  pw_mem_rd_addr_a_reg == $past(getPwAddrAbcWr_0_i, 1) &&
  pw_mem_rd_addr_b_out == $past(getPwAddrAbcWr_1_i, 1) &&
  pw_mem_rd_addr_b_reg == $past(getPwAddrAbcWr_1_i, 1) &&
  pw_mem_rd_addr_c_out == $past(getPwAddrCrd_0_i, 1) &&
  pw_mem_rd_addr_c_reg == $past(getPwAddrCrd_0_i, 1) &&
  pw_rden_fsm_reg == $past(getPwRdenFsmReg_0_i, 1) &&
  pw_rden_reg == 0 &&
  rd_valid_count == ((($past(read_state, 1) == PwoReadIdle) || ($past(read_state, 1) == PwoReadStage)) ? 7'd0 : ($past(sampler_valid_in, 1) ? (7'd1 + $past(rd_valid_count, 1)) : $past(rd_valid_count, 1))) &&
  read_state == PwoReadExec &&
  shuffled_pw_rden_fsm_reg == ($past(mlkem_in, 1) ? ({ $past(pw_rden_fsm_reg, 1) }[193] != 0) : ({ $past(pw_rden_fsm_reg, 1) }[0] != 0)) &&
  twiddle_addr_reg == $past(getTwiddleAddrReg_0_i, 1) &&
  twiddle_addr_reg_d2 == ($past(shuffle_en_in, 1) ? ((($past(shuffle_en_in, 1) && $past(mlkem_in, 1)) && ($past(ntt_mode_in, 1) == 3'd5)) ? (($past(getTwiddleRandOffsets_0_i[rounds_count], 1) + ({ 5'd0, 2'(($past(index_count, 1) + $past(index_rand_offset, 1)))} )) + $past(twiddle_offset_array_0_i[rounds_count], 1)) : ($past(getTwiddleRandOffsets_0_i[rounds_count], 1) + $past(twiddle_offset_array_0_i[rounds_count], 1))) : ($past(twiddle_addr_reg, 1) + $past(twiddle_offset_array_0_i[rounds_count], 1))) &&
  twiddle_addr_reg_d3 == $past(twiddle_addr_reg_d2, 1);
endproperty
read_read_stage_to_read_exec_a: assert property (disable iff(!ntt_ctrl.reset_n || ntt_ctrl.zeroize) read_read_stage_to_read_exec_p);


property read_read_stage_to_read_idle_p;
  read_stage &&
  (rounds_count == 3'd1) &&
  !ntt_enable_in
|->
  ##1
  read_idle &&
  bf_enable_reg == ({ { $past(bf_enable_reg, 1) }[1:0], 1'd0} ) &&
  buf_rdptr_reg == $past(getBufRdptrReg_0_i, 1) &&
  chunk_count_reg == $past(getChunkCountReg_0_i, 1) &&
  incr_pw_rd_addr_reg == $past(getIncrPwRdAddrReg_0_i, 1) &&
  incr_twiddle_addr_reg == ((((($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait)) && $past(mlkem_in, 1)) && ($past(ntt_mode_in, 1) == 3'd5)) && $past(sampler_valid_in, 1)) &&
  pw_mem_rd_addr_a_out == $past(getPwAddrAbcWr_0_i, 1) &&
  pw_mem_rd_addr_a_reg == $past(getPwAddrAbcWr_0_i, 1) &&
  pw_mem_rd_addr_b_out == $past(getPwAddrAbcWr_1_i, 1) &&
  pw_mem_rd_addr_b_reg == $past(getPwAddrAbcWr_1_i, 1) &&
  pw_mem_rd_addr_c_out == $past(getPwAddrCrd_0_i, 1) &&
  pw_mem_rd_addr_c_reg == $past(getPwAddrCrd_0_i, 1) &&
  pw_rden_fsm_reg == $past(getPwRdenFsmReg_0_i, 1) &&
  pw_rden_reg == 0 &&
  rd_valid_count == ((($past(read_state, 1) == PwoReadIdle) || ($past(read_state, 1) == PwoReadStage)) ? 7'd0 : ($past(sampler_valid_in, 1) ? (7'd1 + $past(rd_valid_count, 1)) : $past(rd_valid_count, 1))) &&
  read_state == PwoReadIdle &&
  shuffled_pw_rden_fsm_reg == ($past(mlkem_in, 1) ? ({ $past(pw_rden_fsm_reg, 1) }[193] != 0) : ({ $past(pw_rden_fsm_reg, 1) }[0] != 0)) &&
  twiddle_addr_reg == $past(getTwiddleAddrReg_0_i, 1) &&
  twiddle_addr_reg_d2 == ($past(shuffle_en_in, 1) ? ((($past(shuffle_en_in, 1) && $past(mlkem_in, 1)) && ($past(ntt_mode_in, 1) == 3'd5)) ? (($past(getTwiddleRandOffsets_0_i[rounds_count], 1) + ({ 5'd0, 2'(($past(index_count, 1) + $past(index_rand_offset, 1)))} )) + $past(twiddle_offset_array_0_i[rounds_count], 1)) : ($past(getTwiddleRandOffsets_0_i[rounds_count], 1) + $past(twiddle_offset_array_0_i[rounds_count], 1))) : ($past(twiddle_addr_reg, 1) + $past(twiddle_offset_array_0_i[rounds_count], 1))) &&
  twiddle_addr_reg_d3 == $past(twiddle_addr_reg_d2, 1);
endproperty
read_read_stage_to_read_idle_a: assert property (disable iff(!ntt_ctrl.reset_n || ntt_ctrl.zeroize) read_read_stage_to_read_idle_p);


property read_read_stage_to_read_stage_p;
  read_stage &&
  ((rounds_count != 3'd1) || ntt_enable_in) &&
  !((write_state == PwoWriteStage) && (rounds_count != 3'd1))
|->
  ##1
  read_stage &&
  bf_enable_reg == ({ { $past(bf_enable_reg, 1) }[1:0], 1'd0} ) &&
  buf_rdptr_reg == $past(getBufRdptrReg_0_i, 1) &&
  chunk_count_reg == $past(getChunkCountReg_0_i, 1) &&
  incr_pw_rd_addr_reg == $past(getIncrPwRdAddrReg_0_i, 1) &&
  incr_twiddle_addr_reg == ((((($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait)) && $past(mlkem_in, 1)) && ($past(ntt_mode_in, 1) == 3'd5)) && $past(sampler_valid_in, 1)) &&
  pw_mem_rd_addr_a_out == $past(getPwAddrAbcWr_0_i, 1) &&
  pw_mem_rd_addr_a_reg == $past(getPwAddrAbcWr_0_i, 1) &&
  pw_mem_rd_addr_b_out == $past(getPwAddrAbcWr_1_i, 1) &&
  pw_mem_rd_addr_b_reg == $past(getPwAddrAbcWr_1_i, 1) &&
  pw_mem_rd_addr_c_out == $past(getPwAddrCrd_0_i, 1) &&
  pw_mem_rd_addr_c_reg == $past(getPwAddrCrd_0_i, 1) &&
  pw_rden_fsm_reg == $past(getPwRdenFsmReg_0_i, 1) &&
  pw_rden_reg == 0 &&
  rd_valid_count == ((($past(read_state, 1) == PwoReadIdle) || ($past(read_state, 1) == PwoReadStage)) ? 7'd0 : ($past(sampler_valid_in, 1) ? (7'd1 + $past(rd_valid_count, 1)) : $past(rd_valid_count, 1))) &&
  read_state == PwoReadStage &&
  shuffled_pw_rden_fsm_reg == ($past(mlkem_in, 1) ? ({ $past(pw_rden_fsm_reg, 1) }[193] != 0) : ({ $past(pw_rden_fsm_reg, 1) }[0] != 0)) &&
  twiddle_addr_reg == $past(getTwiddleAddrReg_0_i, 1) &&
  twiddle_addr_reg_d2 == ($past(shuffle_en_in, 1) ? ((($past(shuffle_en_in, 1) && $past(mlkem_in, 1)) && ($past(ntt_mode_in, 1) == 3'd5)) ? (($past(getTwiddleRandOffsets_0_i[rounds_count], 1) + ({ 5'd0, 2'(($past(index_count, 1) + $past(index_rand_offset, 1)))} )) + $past(twiddle_offset_array_0_i[rounds_count], 1)) : ($past(getTwiddleRandOffsets_0_i[rounds_count], 1) + $past(twiddle_offset_array_0_i[rounds_count], 1))) : ($past(twiddle_addr_reg, 1) + $past(twiddle_offset_array_0_i[rounds_count], 1))) &&
  twiddle_addr_reg_d3 == $past(twiddle_addr_reg_d2, 1);
endproperty
read_read_stage_to_read_stage_a: assert property (disable iff(!ntt_ctrl.reset_n || ntt_ctrl.zeroize) read_read_stage_to_read_stage_p);


property write_write_idle_to_write_idle_p;
  write_idle &&
  !ntt_enable_in
|->
  ##1
  write_idle &&
  chunk_count == ((($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) && ($past(index_count, 1) == 2'h3)) ? (4'd1 + $past(chunk_count, 1)) : $past(chunk_count, 1)) &&
  $stable(chunk_rand_offset) &&
  done_out == (($past(rst_rounds_in, 1) ? 3'd0 : (($past(rounds_count, 1) == 3'd1) ? 3'd0 : $past(rounds_count, 1))) == 3'd1) &&
  index_count == (($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) ? (2'd1 + $past(index_count, 1)) : $past(index_count, 1)) &&
  index_rand_offset == ((($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) && ($past(index_count, 1) == 2'h3)) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  pw_mem_wr_addr_c_out == $past(getPwAddrCwr_0_i, 1) &&
  pw_mem_wr_addr_c_reg == $past(getPwAddrCwr_0_i, 1) &&
  pw_wren_reg == ((($past(write_state, 1) == PwoWriteMem) && $past(butterfly_ready_in, 1)) || ((($past(write_state, 1) == PwoWriteWait) && $past(butterfly_ready_in, 1)) && !$past(shuffle_en_in, 1))) &&
  rounds_count == ($past(rst_rounds_in, 1) ? 3'd0 : (($past(rounds_count, 1) == 3'd1) ? 3'd0 : $past(rounds_count, 1))) &&
  wr_valid_count == ((($past(write_state, 1) == PwoWriteIdle) || ($past(write_state, 1) == PwoWriteStage)) ? 7'd0 : ($past(butterfly_ready_in, 1) ? (7'd1 + $past(wr_valid_count, 1)) : $past(wr_valid_count, 1))) &&
  write_state == PwoWriteIdle;
endproperty
write_write_idle_to_write_idle_a: assert property (disable iff(!ntt_ctrl.reset_n || ntt_ctrl.zeroize) write_write_idle_to_write_idle_p);

property write_write_idle_to_write_idle_2_p;
  write_idle &&
  !ntt_enable_in
|->
  ##1
  write_idle &&
  masked_pwm_buf_rdptr_d1 == ((((($past(ntt_mode_in, 1) == 3'd2) || ($past(mlkem_in, 1) && ($past(ntt_mode_in, 1) == 3'd5))) && $past(masking_en_in, 1)) && ((($past(read_state, 1) != PwoReadIdle) && ($past(read_state, 1) != PwoReadStage)) || (($past(write_state, 1) != PwoWriteIdle) && ($past(write_state, 1) != PwoWriteStage)))) ? { $past(buf_rdptr_reg, 1) }[1:0] : 2'd0) &&
  masked_pwm_buf_rdptr_d2 == ((((($past(ntt_mode_in, 1) == 3'd2) || ($past(mlkem_in, 1) && ($past(ntt_mode_in, 1) == 3'd5))) && $past(masking_en_in, 1)) && ((($past(read_state, 1) != PwoReadIdle) && ($past(read_state, 1) != PwoReadStage)) || (($past(write_state, 1) != PwoWriteIdle) && ($past(write_state, 1) != PwoWriteStage)))) ? $past(masked_pwm_buf_rdptr_d1, 1) : 2'd0) &&
  masked_pwm_buf_rdptr_d3 == ((((($past(ntt_mode_in, 1) == 3'd2) || ($past(mlkem_in, 1) && ($past(ntt_mode_in, 1) == 3'd5))) && $past(masking_en_in, 1)) && ((($past(read_state, 1) != PwoReadIdle) && ($past(read_state, 1) != PwoReadStage)) || (($past(write_state, 1) != PwoWriteIdle) && ($past(write_state, 1) != PwoWriteStage)))) ? $past(masked_pwm_buf_rdptr_d2, 1) : 2'd0);
endproperty
write_write_idle_to_write_idle_2_a: assert property (disable iff(!ntt_ctrl.reset_n || ntt_ctrl.zeroize) write_write_idle_to_write_idle_2_p);


property write_write_idle_to_write_stage_p;
  write_idle &&
  ntt_enable_in
|->
  ##1
  write_stage &&
  chunk_count == { $past(random_in, 1) }[5:2] &&
  chunk_rand_offset == { $past(random_in, 1) }[5:2] &&
  done_out == (($past(rst_rounds_in, 1) ? 3'd0 : (($past(rounds_count, 1) == 3'd1) ? 3'd0 : $past(rounds_count, 1))) == 3'd1) &&
  index_count == (($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) ? (2'd1 + $past(index_count, 1)) : $past(index_count, 1)) &&
  index_rand_offset == ((($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) && ($past(index_count, 1) == 2'h3)) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  pw_mem_wr_addr_c_out == $past(getPwAddrCwr_0_i, 1) &&
  pw_mem_wr_addr_c_reg == $past(getPwAddrCwr_0_i, 1) &&
  pw_wren_reg == ((($past(write_state, 1) == PwoWriteMem) && $past(butterfly_ready_in, 1)) || ((($past(write_state, 1) == PwoWriteWait) && $past(butterfly_ready_in, 1)) && !$past(shuffle_en_in, 1))) &&
  rounds_count == ($past(rst_rounds_in, 1) ? 3'd0 : (($past(rounds_count, 1) == 3'd1) ? 3'd0 : $past(rounds_count, 1))) &&
  wr_valid_count == ((($past(write_state, 1) == PwoWriteIdle) || ($past(write_state, 1) == PwoWriteStage)) ? 7'd0 : ($past(butterfly_ready_in, 1) ? (7'd1 + $past(wr_valid_count, 1)) : $past(wr_valid_count, 1))) &&
  write_state == PwoWriteStage;
endproperty
write_write_idle_to_write_stage_a: assert property (disable iff(!ntt_ctrl.reset_n || ntt_ctrl.zeroize) write_write_idle_to_write_stage_p);

property write_write_idle_to_write_stage_2_p;
  write_idle &&
  ntt_enable_in
|->
  ##1
  write_stage &&
  masked_pwm_buf_rdptr_d1 == ((((($past(ntt_mode_in, 1) == 3'd2) || ($past(mlkem_in, 1) && ($past(ntt_mode_in, 1) == 3'd5))) && $past(masking_en_in, 1)) && ((($past(read_state, 1) != PwoReadIdle) && ($past(read_state, 1) != PwoReadStage)) || (($past(write_state, 1) != PwoWriteIdle) && ($past(write_state, 1) != PwoWriteStage)))) ? { $past(buf_rdptr_reg, 1) }[1:0] : 2'd0) &&
  masked_pwm_buf_rdptr_d2 == ((((($past(ntt_mode_in, 1) == 3'd2) || ($past(mlkem_in, 1) && ($past(ntt_mode_in, 1) == 3'd5))) && $past(masking_en_in, 1)) && ((($past(read_state, 1) != PwoReadIdle) && ($past(read_state, 1) != PwoReadStage)) || (($past(write_state, 1) != PwoWriteIdle) && ($past(write_state, 1) != PwoWriteStage)))) ? $past(masked_pwm_buf_rdptr_d1, 1) : 2'd0) &&
  masked_pwm_buf_rdptr_d3 == ((((($past(ntt_mode_in, 1) == 3'd2) || ($past(mlkem_in, 1) && ($past(ntt_mode_in, 1) == 3'd5))) && $past(masking_en_in, 1)) && ((($past(read_state, 1) != PwoReadIdle) && ($past(read_state, 1) != PwoReadStage)) || (($past(write_state, 1) != PwoWriteIdle) && ($past(write_state, 1) != PwoWriteStage)))) ? $past(masked_pwm_buf_rdptr_d2, 1) : 2'd0);
endproperty
write_write_idle_to_write_stage_2_a: assert property (disable iff(!ntt_ctrl.reset_n || ntt_ctrl.zeroize) write_write_idle_to_write_stage_2_p);


property write_write_mem_to_write_mem_p;
  write_mem &&
  ((shuffle_en_in || butterfly_ready_in) || (({ 57'd0, wr_valid_count} ) >= 64'h40)) &&
  !((shuffle_en_in && butterfly_ready_in) && (wr_valid_count == 7'h3F)) &&
  (shuffle_en_in || (wr_valid_count != 7'h40))
|->
  ##1
  write_mem &&
  chunk_count == ((($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) && ($past(index_count, 1) == 2'h3)) ? (4'd1 + $past(chunk_count, 1)) : $past(chunk_count, 1)) &&
  $stable(chunk_rand_offset) &&
  done_out == (($past(rst_rounds_in, 1) ? 3'd0 : (($past(rounds_count, 1) == 3'd1) ? 3'd0 : $past(rounds_count, 1))) == 3'd1) &&
  index_count == (($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) ? (2'd1 + $past(index_count, 1)) : $past(index_count, 1)) &&
  index_rand_offset == ((($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) && ($past(index_count, 1) == 2'h3)) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  pw_mem_wr_addr_c_out == $past(getPwAddrCwr_1_i, 1) &&
  pw_mem_wr_addr_c_reg == $past(getPwAddrCwr_1_i, 1) &&
  pw_wren_reg == ((($past(write_state, 1) == PwoWriteMem) && $past(butterfly_ready_in, 1)) || ((($past(write_state, 1) == PwoWriteWait) && $past(butterfly_ready_in, 1)) && !$past(shuffle_en_in, 1))) &&
  rounds_count == ($past(rst_rounds_in, 1) ? 3'd0 : (($past(rounds_count, 1) == 3'd1) ? 3'd0 : $past(rounds_count, 1))) &&
  wr_valid_count == ((($past(write_state, 1) == PwoWriteIdle) || ($past(write_state, 1) == PwoWriteStage)) ? 7'd0 : ($past(butterfly_ready_in, 1) ? (7'd1 + $past(wr_valid_count, 1)) : $past(wr_valid_count, 1))) &&
  write_state == PwoWriteMem;
endproperty
write_write_mem_to_write_mem_a: assert property (disable iff(!ntt_ctrl.reset_n || ntt_ctrl.zeroize) write_write_mem_to_write_mem_p);

property write_write_mem_to_write_mem_2_p;
  write_mem &&
  ((shuffle_en_in || butterfly_ready_in) || (({ 57'd0, wr_valid_count} ) >= 64'h40)) &&
  !((shuffle_en_in && butterfly_ready_in) && (wr_valid_count == 7'h3F)) &&
  (shuffle_en_in || (wr_valid_count != 7'h40))
|->
  ##1
  write_mem &&
  masked_pwm_buf_rdptr_d1 == ((((($past(ntt_mode_in, 1) == 3'd2) || ($past(mlkem_in, 1) && ($past(ntt_mode_in, 1) == 3'd5))) && $past(masking_en_in, 1)) && ((($past(read_state, 1) != PwoReadIdle) && ($past(read_state, 1) != PwoReadStage)) || (($past(write_state, 1) != PwoWriteIdle) && ($past(write_state, 1) != PwoWriteStage)))) ? { $past(buf_rdptr_reg, 1) }[1:0] : 2'd0) &&
  masked_pwm_buf_rdptr_d2 == ((((($past(ntt_mode_in, 1) == 3'd2) || ($past(mlkem_in, 1) && ($past(ntt_mode_in, 1) == 3'd5))) && $past(masking_en_in, 1)) && ((($past(read_state, 1) != PwoReadIdle) && ($past(read_state, 1) != PwoReadStage)) || (($past(write_state, 1) != PwoWriteIdle) && ($past(write_state, 1) != PwoWriteStage)))) ? $past(masked_pwm_buf_rdptr_d1, 1) : 2'd0) &&
  masked_pwm_buf_rdptr_d3 == ((((($past(ntt_mode_in, 1) == 3'd2) || ($past(mlkem_in, 1) && ($past(ntt_mode_in, 1) == 3'd5))) && $past(masking_en_in, 1)) && ((($past(read_state, 1) != PwoReadIdle) && ($past(read_state, 1) != PwoReadStage)) || (($past(write_state, 1) != PwoWriteIdle) && ($past(write_state, 1) != PwoWriteStage)))) ? $past(masked_pwm_buf_rdptr_d2, 1) : 2'd0);
endproperty
write_write_mem_to_write_mem_2_a: assert property (disable iff(!ntt_ctrl.reset_n || ntt_ctrl.zeroize) write_write_mem_to_write_mem_2_p);


property write_write_mem_to_write_stage_p;
  write_mem &&
  (butterfly_ready_in || !0) &&
  !shuffle_en_in &&
  (wr_valid_count == 7'h40)
|->
  ##1
  write_stage &&
  chunk_count == { $past(random_in, 1) }[5:2] &&
  chunk_rand_offset == { $past(random_in, 1) }[5:2] &&
  done_out == (($past(rst_rounds_in, 1) ? 3'd0 : ((({ 61'd0, $past(rounds_count, 1)} ) < 64'd1) ? (3'd1 + $past(rounds_count, 1)) : (($past(rounds_count, 1) == 3'd1) ? 3'd0 : $past(rounds_count, 1)))) == 3'd1) &&
  index_count == (($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) ? (2'd1 + $past(index_count, 1)) : $past(index_count, 1)) &&
  index_rand_offset == ((($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) && ($past(index_count, 1) == 2'h3)) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  pw_mem_wr_addr_c_out == $past(getPwAddrCwr_1_i, 1) &&
  pw_mem_wr_addr_c_reg == $past(getPwAddrCwr_1_i, 1) &&
  pw_wren_reg == ((($past(write_state, 1) == PwoWriteMem) && $past(butterfly_ready_in, 1)) || ((($past(write_state, 1) == PwoWriteWait) && $past(butterfly_ready_in, 1)) && !$past(shuffle_en_in, 1))) &&
  rounds_count == ($past(rst_rounds_in, 1) ? 3'd0 : ((({ 61'd0, $past(rounds_count, 1)} ) < 64'd1) ? (3'd1 + $past(rounds_count, 1)) : (($past(rounds_count, 1) == 3'd1) ? 3'd0 : $past(rounds_count, 1)))) &&
  wr_valid_count == ((($past(write_state, 1) == PwoWriteIdle) || ($past(write_state, 1) == PwoWriteStage)) ? 7'd0 : ($past(butterfly_ready_in, 1) ? (7'd1 + $past(wr_valid_count, 1)) : $past(wr_valid_count, 1))) &&
  write_state == PwoWriteStage;
endproperty
write_write_mem_to_write_stage_a: assert property (disable iff(!ntt_ctrl.reset_n || ntt_ctrl.zeroize) write_write_mem_to_write_stage_p);

property write_write_mem_to_write_stage_2_p;
  write_mem &&
  (butterfly_ready_in || !0) &&
  !shuffle_en_in &&
  (wr_valid_count == 7'h40)
|->
  ##1
  write_stage &&
  masked_pwm_buf_rdptr_d1 == ((((($past(ntt_mode_in, 1) == 3'd2) || ($past(mlkem_in, 1) && ($past(ntt_mode_in, 1) == 3'd5))) && $past(masking_en_in, 1)) && ((($past(read_state, 1) != PwoReadIdle) && ($past(read_state, 1) != PwoReadStage)) || (($past(write_state, 1) != PwoWriteIdle) && ($past(write_state, 1) != PwoWriteStage)))) ? { $past(buf_rdptr_reg, 1) }[1:0] : 2'd0) &&
  masked_pwm_buf_rdptr_d2 == ((((($past(ntt_mode_in, 1) == 3'd2) || ($past(mlkem_in, 1) && ($past(ntt_mode_in, 1) == 3'd5))) && $past(masking_en_in, 1)) && ((($past(read_state, 1) != PwoReadIdle) && ($past(read_state, 1) != PwoReadStage)) || (($past(write_state, 1) != PwoWriteIdle) && ($past(write_state, 1) != PwoWriteStage)))) ? $past(masked_pwm_buf_rdptr_d1, 1) : 2'd0) &&
  masked_pwm_buf_rdptr_d3 == ((((($past(ntt_mode_in, 1) == 3'd2) || ($past(mlkem_in, 1) && ($past(ntt_mode_in, 1) == 3'd5))) && $past(masking_en_in, 1)) && ((($past(read_state, 1) != PwoReadIdle) && ($past(read_state, 1) != PwoReadStage)) || (($past(write_state, 1) != PwoWriteIdle) && ($past(write_state, 1) != PwoWriteStage)))) ? $past(masked_pwm_buf_rdptr_d2, 1) : 2'd0);
endproperty
write_write_mem_to_write_stage_2_a: assert property (disable iff(!ntt_ctrl.reset_n || ntt_ctrl.zeroize) write_write_mem_to_write_stage_2_p);


property write_write_mem_to_write_wait_p;
  write_mem &&
  ((!(shuffle_en_in || butterfly_ready_in) && (({ 57'd0, wr_valid_count} ) < 64'h40)) || ((shuffle_en_in && butterfly_ready_in) && (wr_valid_count == 7'h3F)))
|->
  ##1
  write_wait &&
  chunk_count == ((($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) && ($past(index_count, 1) == 2'h3)) ? (4'd1 + $past(chunk_count, 1)) : $past(chunk_count, 1)) &&
  $stable(chunk_rand_offset) &&
  done_out == (($past(rst_rounds_in, 1) ? 3'd0 : (($past(rounds_count, 1) == 3'd1) ? 3'd0 : $past(rounds_count, 1))) == 3'd1) &&
  index_count == (($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) ? (2'd1 + $past(index_count, 1)) : $past(index_count, 1)) &&
  index_rand_offset == ((($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) && ($past(index_count, 1) == 2'h3)) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  pw_mem_wr_addr_c_out == $past(getPwAddrCwr_1_i, 1) &&
  pw_mem_wr_addr_c_reg == $past(getPwAddrCwr_1_i, 1) &&
  pw_wren_reg == ((($past(write_state, 1) == PwoWriteMem) && $past(butterfly_ready_in, 1)) || ((($past(write_state, 1) == PwoWriteWait) && $past(butterfly_ready_in, 1)) && !$past(shuffle_en_in, 1))) &&
  rounds_count == ($past(rst_rounds_in, 1) ? 3'd0 : (($past(rounds_count, 1) == 3'd1) ? 3'd0 : $past(rounds_count, 1))) &&
  wr_valid_count == ((($past(write_state, 1) == PwoWriteIdle) || ($past(write_state, 1) == PwoWriteStage)) ? 7'd0 : ($past(butterfly_ready_in, 1) ? (7'd1 + $past(wr_valid_count, 1)) : $past(wr_valid_count, 1))) &&
  write_state == PwoWriteWait;
endproperty
write_write_mem_to_write_wait_a: assert property (disable iff(!ntt_ctrl.reset_n || ntt_ctrl.zeroize) write_write_mem_to_write_wait_p);

property write_write_mem_to_write_wait_2_p;
  write_mem &&
  ((!(shuffle_en_in || butterfly_ready_in) && (({ 57'd0, wr_valid_count} ) < 64'h40)) || ((shuffle_en_in && butterfly_ready_in) && (wr_valid_count == 7'h3F)))
|->
  ##1
  write_wait &&
  masked_pwm_buf_rdptr_d1 == ((((($past(ntt_mode_in, 1) == 3'd2) || ($past(mlkem_in, 1) && ($past(ntt_mode_in, 1) == 3'd5))) && $past(masking_en_in, 1)) && ((($past(read_state, 1) != PwoReadIdle) && ($past(read_state, 1) != PwoReadStage)) || (($past(write_state, 1) != PwoWriteIdle) && ($past(write_state, 1) != PwoWriteStage)))) ? { $past(buf_rdptr_reg, 1) }[1:0] : 2'd0) &&
  masked_pwm_buf_rdptr_d2 == ((((($past(ntt_mode_in, 1) == 3'd2) || ($past(mlkem_in, 1) && ($past(ntt_mode_in, 1) == 3'd5))) && $past(masking_en_in, 1)) && ((($past(read_state, 1) != PwoReadIdle) && ($past(read_state, 1) != PwoReadStage)) || (($past(write_state, 1) != PwoWriteIdle) && ($past(write_state, 1) != PwoWriteStage)))) ? $past(masked_pwm_buf_rdptr_d1, 1) : 2'd0) &&
  masked_pwm_buf_rdptr_d3 == ((((($past(ntt_mode_in, 1) == 3'd2) || ($past(mlkem_in, 1) && ($past(ntt_mode_in, 1) == 3'd5))) && $past(masking_en_in, 1)) && ((($past(read_state, 1) != PwoReadIdle) && ($past(read_state, 1) != PwoReadStage)) || (($past(write_state, 1) != PwoWriteIdle) && ($past(write_state, 1) != PwoWriteStage)))) ? $past(masked_pwm_buf_rdptr_d2, 1) : 2'd0);
endproperty
write_write_mem_to_write_wait_2_a: assert property (disable iff(!ntt_ctrl.reset_n || ntt_ctrl.zeroize) write_write_mem_to_write_wait_2_p);


property write_write_stage_to_write_idle_p;
  write_stage &&
  (rounds_count == 3'd1)
|->
  ##1
  write_idle &&
  chunk_count == ((($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) && ($past(index_count, 1) == 2'h3)) ? (4'd1 + $past(chunk_count, 1)) : $past(chunk_count, 1)) &&
  $stable(chunk_rand_offset) &&
  done_out == 0 &&
  index_count == (($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) ? (2'd1 + $past(index_count, 1)) : $past(index_count, 1)) &&
  index_rand_offset == ((($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) && ($past(index_count, 1) == 2'h3)) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  pw_mem_wr_addr_c_out == $past(getPwAddrCwr_0_i, 1) &&
  pw_mem_wr_addr_c_reg == $past(getPwAddrCwr_0_i, 1) &&
  pw_wren_reg == ((($past(write_state, 1) == PwoWriteMem) && $past(butterfly_ready_in, 1)) || ((($past(write_state, 1) == PwoWriteWait) && $past(butterfly_ready_in, 1)) && !$past(shuffle_en_in, 1))) &&
  rounds_count == 3'd0 &&
  wr_valid_count == ((($past(write_state, 1) == PwoWriteIdle) || ($past(write_state, 1) == PwoWriteStage)) ? 7'd0 : ($past(butterfly_ready_in, 1) ? (7'd1 + $past(wr_valid_count, 1)) : $past(wr_valid_count, 1))) &&
  write_state == PwoWriteIdle;
endproperty
write_write_stage_to_write_idle_a: assert property (disable iff(!ntt_ctrl.reset_n || ntt_ctrl.zeroize) write_write_stage_to_write_idle_p);

property write_write_stage_to_write_idle_2_p;
  write_stage &&
  (rounds_count == 3'd1)
|->
  ##1
  write_idle &&
  masked_pwm_buf_rdptr_d1 == ((((($past(ntt_mode_in, 1) == 3'd2) || ($past(mlkem_in, 1) && ($past(ntt_mode_in, 1) == 3'd5))) && $past(masking_en_in, 1)) && ((($past(read_state, 1) != PwoReadIdle) && ($past(read_state, 1) != PwoReadStage)) || (($past(write_state, 1) != PwoWriteIdle) && ($past(write_state, 1) != PwoWriteStage)))) ? { $past(buf_rdptr_reg, 1) }[1:0] : 2'd0) &&
  masked_pwm_buf_rdptr_d2 == ((((($past(ntt_mode_in, 1) == 3'd2) || ($past(mlkem_in, 1) && ($past(ntt_mode_in, 1) == 3'd5))) && $past(masking_en_in, 1)) && ((($past(read_state, 1) != PwoReadIdle) && ($past(read_state, 1) != PwoReadStage)) || (($past(write_state, 1) != PwoWriteIdle) && ($past(write_state, 1) != PwoWriteStage)))) ? $past(masked_pwm_buf_rdptr_d1, 1) : 2'd0) &&
  masked_pwm_buf_rdptr_d3 == ((((($past(ntt_mode_in, 1) == 3'd2) || ($past(mlkem_in, 1) && ($past(ntt_mode_in, 1) == 3'd5))) && $past(masking_en_in, 1)) && ((($past(read_state, 1) != PwoReadIdle) && ($past(read_state, 1) != PwoReadStage)) || (($past(write_state, 1) != PwoWriteIdle) && ($past(write_state, 1) != PwoWriteStage)))) ? $past(masked_pwm_buf_rdptr_d2, 1) : 2'd0);
endproperty
write_write_stage_to_write_idle_2_a: assert property (disable iff(!ntt_ctrl.reset_n || ntt_ctrl.zeroize) write_write_stage_to_write_idle_2_p);


property write_write_stage_to_write_mem_p;
  write_stage &&
  (rounds_count != 3'd1) &&
  shuffle_en_in
|->
  ##1
  write_mem &&
  chunk_count == ((($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) && ($past(index_count, 1) == 2'h3)) ? (4'd1 + $past(chunk_count, 1)) : $past(chunk_count, 1)) &&
  $stable(chunk_rand_offset) &&
  done_out == (($past(rst_rounds_in, 1) ? 3'd0 : $past(rounds_count, 1)) == 3'd1) &&
  index_count == (($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) ? (2'd1 + $past(index_count, 1)) : $past(index_count, 1)) &&
  index_rand_offset == ((($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) && ($past(index_count, 1) == 2'h3)) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  pw_mem_wr_addr_c_out == $past(getPwAddrCwr_0_i, 1) &&
  pw_mem_wr_addr_c_reg == $past(getPwAddrCwr_0_i, 1) &&
  pw_wren_reg == ((($past(write_state, 1) == PwoWriteMem) && $past(butterfly_ready_in, 1)) || ((($past(write_state, 1) == PwoWriteWait) && $past(butterfly_ready_in, 1)) && !$past(shuffle_en_in, 1))) &&
  rounds_count == ($past(rst_rounds_in, 1) ? 3'd0 : $past(rounds_count, 1)) &&
  wr_valid_count == ((($past(write_state, 1) == PwoWriteIdle) || ($past(write_state, 1) == PwoWriteStage)) ? 7'd0 : ($past(butterfly_ready_in, 1) ? (7'd1 + $past(wr_valid_count, 1)) : $past(wr_valid_count, 1))) &&
  write_state == PwoWriteMem;
endproperty
write_write_stage_to_write_mem_a: assert property (disable iff(!ntt_ctrl.reset_n || ntt_ctrl.zeroize) write_write_stage_to_write_mem_p);

property write_write_stage_to_write_mem_2_p;
  write_stage &&
  (rounds_count != 3'd1) &&
  shuffle_en_in
|->
  ##1
  write_mem &&
  masked_pwm_buf_rdptr_d1 == ((((($past(ntt_mode_in, 1) == 3'd2) || ($past(mlkem_in, 1) && ($past(ntt_mode_in, 1) == 3'd5))) && $past(masking_en_in, 1)) && ((($past(read_state, 1) != PwoReadIdle) && ($past(read_state, 1) != PwoReadStage)) || (($past(write_state, 1) != PwoWriteIdle) && ($past(write_state, 1) != PwoWriteStage)))) ? { $past(buf_rdptr_reg, 1) }[1:0] : 2'd0) &&
  masked_pwm_buf_rdptr_d2 == ((((($past(ntt_mode_in, 1) == 3'd2) || ($past(mlkem_in, 1) && ($past(ntt_mode_in, 1) == 3'd5))) && $past(masking_en_in, 1)) && ((($past(read_state, 1) != PwoReadIdle) && ($past(read_state, 1) != PwoReadStage)) || (($past(write_state, 1) != PwoWriteIdle) && ($past(write_state, 1) != PwoWriteStage)))) ? $past(masked_pwm_buf_rdptr_d1, 1) : 2'd0) &&
  masked_pwm_buf_rdptr_d3 == ((((($past(ntt_mode_in, 1) == 3'd2) || ($past(mlkem_in, 1) && ($past(ntt_mode_in, 1) == 3'd5))) && $past(masking_en_in, 1)) && ((($past(read_state, 1) != PwoReadIdle) && ($past(read_state, 1) != PwoReadStage)) || (($past(write_state, 1) != PwoWriteIdle) && ($past(write_state, 1) != PwoWriteStage)))) ? $past(masked_pwm_buf_rdptr_d2, 1) : 2'd0);
endproperty
write_write_stage_to_write_mem_2_a: assert property (disable iff(!ntt_ctrl.reset_n || ntt_ctrl.zeroize) write_write_stage_to_write_mem_2_p);

property write_write_stage_to_write_wait_p;
  write_stage &&
  (rounds_count != 3'd1) &&
  !shuffle_en_in
|->
  ##1
  write_wait &&
  chunk_count == ((($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) && ($past(index_count, 1) == 2'h3)) ? (4'd1 + $past(chunk_count, 1)) : $past(chunk_count, 1)) &&
  $stable(chunk_rand_offset) &&
  done_out == (($past(rst_rounds_in, 1) ? 3'd0 : $past(rounds_count, 1)) == 3'd1) &&
  index_count == (($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) ? (2'd1 + $past(index_count, 1)) : $past(index_count, 1)) &&
  index_rand_offset == ((($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) && ($past(index_count, 1) == 2'h3)) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  pw_mem_wr_addr_c_out == $past(getPwAddrCwr_0_i, 1) &&
  pw_mem_wr_addr_c_reg == $past(getPwAddrCwr_0_i, 1) &&
  pw_wren_reg == ((($past(write_state, 1) == PwoWriteMem) && $past(butterfly_ready_in, 1)) || ((($past(write_state, 1) == PwoWriteWait) && $past(butterfly_ready_in, 1)) && !$past(shuffle_en_in, 1))) &&
  rounds_count == ($past(rst_rounds_in, 1) ? 3'd0 : $past(rounds_count, 1)) &&
  wr_valid_count == ((($past(write_state, 1) == PwoWriteIdle) || ($past(write_state, 1) == PwoWriteStage)) ? 7'd0 : ($past(butterfly_ready_in, 1) ? (7'd1 + $past(wr_valid_count, 1)) : $past(wr_valid_count, 1))) &&
  write_state == PwoWriteWait;
endproperty
write_write_stage_to_write_wait_a: assert property (disable iff(!ntt_ctrl.reset_n || ntt_ctrl.zeroize) write_write_stage_to_write_wait_p);

property write_write_stage_to_write_wait_2_p;
  write_stage &&
  (rounds_count != 3'd1) &&
  !shuffle_en_in
|->
  ##1
  write_wait &&
  masked_pwm_buf_rdptr_d1 == ((((($past(ntt_mode_in, 1) == 3'd2) || ($past(mlkem_in, 1) && ($past(ntt_mode_in, 1) == 3'd5))) && $past(masking_en_in, 1)) && ((($past(read_state, 1) != PwoReadIdle) && ($past(read_state, 1) != PwoReadStage)) || (($past(write_state, 1) != PwoWriteIdle) && ($past(write_state, 1) != PwoWriteStage)))) ? { $past(buf_rdptr_reg, 1) }[1:0] : 2'd0) &&
  masked_pwm_buf_rdptr_d2 == ((((($past(ntt_mode_in, 1) == 3'd2) || ($past(mlkem_in, 1) && ($past(ntt_mode_in, 1) == 3'd5))) && $past(masking_en_in, 1)) && ((($past(read_state, 1) != PwoReadIdle) && ($past(read_state, 1) != PwoReadStage)) || (($past(write_state, 1) != PwoWriteIdle) && ($past(write_state, 1) != PwoWriteStage)))) ? $past(masked_pwm_buf_rdptr_d1, 1) : 2'd0) &&
  masked_pwm_buf_rdptr_d3 == ((((($past(ntt_mode_in, 1) == 3'd2) || ($past(mlkem_in, 1) && ($past(ntt_mode_in, 1) == 3'd5))) && $past(masking_en_in, 1)) && ((($past(read_state, 1) != PwoReadIdle) && ($past(read_state, 1) != PwoReadStage)) || (($past(write_state, 1) != PwoWriteIdle) && ($past(write_state, 1) != PwoWriteStage)))) ? $past(masked_pwm_buf_rdptr_d2, 1) : 2'd0);
endproperty
write_write_stage_to_write_wait_2_a: assert property (disable iff(!ntt_ctrl.reset_n || ntt_ctrl.zeroize) write_write_stage_to_write_wait_2_p);


property write_write_wait_to_write_mem_p;
  write_wait &&
  !shuffle_en_in &&
  butterfly_ready_in
|->
  ##1
  write_mem &&
  chunk_count == ((($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) && ($past(index_count, 1) == 2'h3)) ? (4'd1 + $past(chunk_count, 1)) : $past(chunk_count, 1)) &&
  $stable(chunk_rand_offset) &&
  done_out == (($past(rst_rounds_in, 1) ? 3'd0 : (($past(rounds_count, 1) == 3'd1) ? 3'd0 : $past(rounds_count, 1))) == 3'd1) &&
  index_count == (($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) ? (2'd1 + $past(index_count, 1)) : $past(index_count, 1)) &&
  index_rand_offset == ((($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) && ($past(index_count, 1) == 2'h3)) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  pw_mem_wr_addr_c_out == $past(getPwAddrCwr_1_i, 1) &&
  pw_mem_wr_addr_c_reg == $past(getPwAddrCwr_1_i, 1) &&
  pw_wren_reg == ((($past(write_state, 1) == PwoWriteMem) && $past(butterfly_ready_in, 1)) || ((($past(write_state, 1) == PwoWriteWait) && $past(butterfly_ready_in, 1)) && !$past(shuffle_en_in, 1))) &&
  rounds_count == ($past(rst_rounds_in, 1) ? 3'd0 : (($past(rounds_count, 1) == 3'd1) ? 3'd0 : $past(rounds_count, 1))) &&
  wr_valid_count == ((($past(write_state, 1) == PwoWriteIdle) || ($past(write_state, 1) == PwoWriteStage)) ? 7'd0 : ($past(butterfly_ready_in, 1) ? (7'd1 + $past(wr_valid_count, 1)) : $past(wr_valid_count, 1))) &&
  write_state == PwoWriteMem;
endproperty
write_write_wait_to_write_mem_a: assert property (disable iff(!ntt_ctrl.reset_n || ntt_ctrl.zeroize) write_write_wait_to_write_mem_p);

property write_write_wait_to_write_mem_2_p;
  write_wait &&
  !shuffle_en_in &&
  butterfly_ready_in
|->
  ##1
  write_mem &&
  masked_pwm_buf_rdptr_d1 == ((((($past(ntt_mode_in, 1) == 3'd2) || ($past(mlkem_in, 1) && ($past(ntt_mode_in, 1) == 3'd5))) && $past(masking_en_in, 1)) && ((($past(read_state, 1) != PwoReadIdle) && ($past(read_state, 1) != PwoReadStage)) || (($past(write_state, 1) != PwoWriteIdle) && ($past(write_state, 1) != PwoWriteStage)))) ? { $past(buf_rdptr_reg, 1) }[1:0] : 2'd0) &&
  masked_pwm_buf_rdptr_d2 == ((((($past(ntt_mode_in, 1) == 3'd2) || ($past(mlkem_in, 1) && ($past(ntt_mode_in, 1) == 3'd5))) && $past(masking_en_in, 1)) && ((($past(read_state, 1) != PwoReadIdle) && ($past(read_state, 1) != PwoReadStage)) || (($past(write_state, 1) != PwoWriteIdle) && ($past(write_state, 1) != PwoWriteStage)))) ? $past(masked_pwm_buf_rdptr_d1, 1) : 2'd0) &&
  masked_pwm_buf_rdptr_d3 == ((((($past(ntt_mode_in, 1) == 3'd2) || ($past(mlkem_in, 1) && ($past(ntt_mode_in, 1) == 3'd5))) && $past(masking_en_in, 1)) && ((($past(read_state, 1) != PwoReadIdle) && ($past(read_state, 1) != PwoReadStage)) || (($past(write_state, 1) != PwoWriteIdle) && ($past(write_state, 1) != PwoWriteStage)))) ? $past(masked_pwm_buf_rdptr_d2, 1) : 2'd0);
endproperty
write_write_wait_to_write_mem_2_a: assert property (disable iff(!ntt_ctrl.reset_n || ntt_ctrl.zeroize) write_write_wait_to_write_mem_2_p);


property write_write_wait_to_write_stage_p;
  write_wait &&
  shuffle_en_in
|->
  ##1
  write_stage &&
  chunk_count == { $past(random_in, 1) }[5:2] &&
  chunk_rand_offset == { $past(random_in, 1) }[5:2] &&
  done_out == (($past(rst_rounds_in, 1) ? 3'd0 : ((({ 61'd0, $past(rounds_count, 1)} ) < 64'd1) ? (3'd1 + $past(rounds_count, 1)) : (($past(rounds_count, 1) == 3'd1) ? 3'd0 : $past(rounds_count, 1)))) == 3'd1) &&
  index_count == (($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) ? (2'd1 + $past(index_count, 1)) : $past(index_count, 1)) &&
  index_rand_offset == ((($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) && ($past(index_count, 1) == 2'h3)) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  pw_mem_wr_addr_c_out == $past(getPwAddrCwr_1_i, 1) &&
  pw_mem_wr_addr_c_reg == $past(getPwAddrCwr_1_i, 1) &&
  pw_wren_reg == ((($past(write_state, 1) == PwoWriteMem) && $past(butterfly_ready_in, 1)) || ((($past(write_state, 1) == PwoWriteWait) && $past(butterfly_ready_in, 1)) && !$past(shuffle_en_in, 1))) &&
  rounds_count == ($past(rst_rounds_in, 1) ? 3'd0 : ((({ 61'd0, $past(rounds_count, 1)} ) < 64'd1) ? (3'd1 + $past(rounds_count, 1)) : (($past(rounds_count, 1) == 3'd1) ? 3'd0 : $past(rounds_count, 1)))) &&
  wr_valid_count == ((($past(write_state, 1) == PwoWriteIdle) || ($past(write_state, 1) == PwoWriteStage)) ? 7'd0 : ($past(butterfly_ready_in, 1) ? (7'd1 + $past(wr_valid_count, 1)) : $past(wr_valid_count, 1))) &&
  write_state == PwoWriteStage;
endproperty
write_write_wait_to_write_stage_a: assert property (disable iff(!ntt_ctrl.reset_n || ntt_ctrl.zeroize) write_write_wait_to_write_stage_p);

property write_write_wait_to_write_stage_2_p;
  write_wait &&
  shuffle_en_in
|->
  ##1
  write_stage &&
  masked_pwm_buf_rdptr_d1 == ((((($past(ntt_mode_in, 1) == 3'd2) || ($past(mlkem_in, 1) && ($past(ntt_mode_in, 1) == 3'd5))) && $past(masking_en_in, 1)) && ((($past(read_state, 1) != PwoReadIdle) && ($past(read_state, 1) != PwoReadStage)) || (($past(write_state, 1) != PwoWriteIdle) && ($past(write_state, 1) != PwoWriteStage)))) ? { $past(buf_rdptr_reg, 1) }[1:0] : 2'd0) &&
  masked_pwm_buf_rdptr_d2 == ((((($past(ntt_mode_in, 1) == 3'd2) || ($past(mlkem_in, 1) && ($past(ntt_mode_in, 1) == 3'd5))) && $past(masking_en_in, 1)) && ((($past(read_state, 1) != PwoReadIdle) && ($past(read_state, 1) != PwoReadStage)) || (($past(write_state, 1) != PwoWriteIdle) && ($past(write_state, 1) != PwoWriteStage)))) ? $past(masked_pwm_buf_rdptr_d1, 1) : 2'd0) &&
  masked_pwm_buf_rdptr_d3 == ((((($past(ntt_mode_in, 1) == 3'd2) || ($past(mlkem_in, 1) && ($past(ntt_mode_in, 1) == 3'd5))) && $past(masking_en_in, 1)) && ((($past(read_state, 1) != PwoReadIdle) && ($past(read_state, 1) != PwoReadStage)) || (($past(write_state, 1) != PwoWriteIdle) && ($past(write_state, 1) != PwoWriteStage)))) ? $past(masked_pwm_buf_rdptr_d2, 1) : 2'd0);
endproperty
write_write_wait_to_write_stage_2_a: assert property (disable iff(!ntt_ctrl.reset_n || ntt_ctrl.zeroize) write_write_wait_to_write_stage_2_p);


property write_write_wait_to_write_wait_p;
  write_wait &&
  !shuffle_en_in &&
  !butterfly_ready_in
|->
  ##1
  write_wait &&
  chunk_count == ((($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) && ($past(index_count, 1) == 2'h3)) ? (4'd1 + $past(chunk_count, 1)) : $past(chunk_count, 1)) &&
  $stable(chunk_rand_offset) &&
  done_out == (($past(rst_rounds_in, 1) ? 3'd0 : (($past(rounds_count, 1) == 3'd1) ? 3'd0 : $past(rounds_count, 1))) == 3'd1) &&
  index_count == (($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) ? (2'd1 + $past(index_count, 1)) : $past(index_count, 1)) &&
  index_rand_offset == ((($past(sampler_valid_in, 1) && (($past(read_state, 1) == PwoReadExec) || ($past(read_state, 1) == PwoReadExecWait))) && ($past(index_count, 1) == 2'h3)) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  pw_mem_wr_addr_c_out == $past(getPwAddrCwr_1_i, 1) &&
  pw_mem_wr_addr_c_reg == $past(getPwAddrCwr_1_i, 1) &&
  pw_wren_reg == ((($past(write_state, 1) == PwoWriteMem) && $past(butterfly_ready_in, 1)) || ((($past(write_state, 1) == PwoWriteWait) && $past(butterfly_ready_in, 1)) && !$past(shuffle_en_in, 1))) &&
  rounds_count == ($past(rst_rounds_in, 1) ? 3'd0 : (($past(rounds_count, 1) == 3'd1) ? 3'd0 : $past(rounds_count, 1))) &&
  wr_valid_count == ((($past(write_state, 1) == PwoWriteIdle) || ($past(write_state, 1) == PwoWriteStage)) ? 7'd0 : ($past(butterfly_ready_in, 1) ? (7'd1 + $past(wr_valid_count, 1)) : $past(wr_valid_count, 1))) &&
  write_state == PwoWriteWait;
endproperty
write_write_wait_to_write_wait_a: assert property (disable iff(!ntt_ctrl.reset_n || ntt_ctrl.zeroize) write_write_wait_to_write_wait_p);

property write_write_wait_to_write_wait_2_p;
  write_wait &&
  !shuffle_en_in &&
  !butterfly_ready_in
|->
  ##1
  write_wait &&
  masked_pwm_buf_rdptr_d1 == ((((($past(ntt_mode_in, 1) == 3'd2) || ($past(mlkem_in, 1) && ($past(ntt_mode_in, 1) == 3'd5))) && $past(masking_en_in, 1)) && ((($past(read_state, 1) != PwoReadIdle) && ($past(read_state, 1) != PwoReadStage)) || (($past(write_state, 1) != PwoWriteIdle) && ($past(write_state, 1) != PwoWriteStage)))) ? { $past(buf_rdptr_reg, 1) }[1:0] : 2'd0) &&
  masked_pwm_buf_rdptr_d2 == ((((($past(ntt_mode_in, 1) == 3'd2) || ($past(mlkem_in, 1) && ($past(ntt_mode_in, 1) == 3'd5))) && $past(masking_en_in, 1)) && ((($past(read_state, 1) != PwoReadIdle) && ($past(read_state, 1) != PwoReadStage)) || (($past(write_state, 1) != PwoWriteIdle) && ($past(write_state, 1) != PwoWriteStage)))) ? $past(masked_pwm_buf_rdptr_d1, 1) : 2'd0) &&
  masked_pwm_buf_rdptr_d3 == ((((($past(ntt_mode_in, 1) == 3'd2) || ($past(mlkem_in, 1) && ($past(ntt_mode_in, 1) == 3'd5))) && $past(masking_en_in, 1)) && ((($past(read_state, 1) != PwoReadIdle) && ($past(read_state, 1) != PwoReadStage)) || (($past(write_state, 1) != PwoWriteIdle) && ($past(write_state, 1) != PwoWriteStage)))) ? $past(masked_pwm_buf_rdptr_d2, 1) : 2'd0);
endproperty
write_write_wait_to_write_wait_2_a: assert property (disable iff(!ntt_ctrl.reset_n || ntt_ctrl.zeroize) write_write_wait_to_write_wait_2_p);


property read_read_idle_eventually_left_p;
  read_idle 
|->
  s_eventually(!read_idle);
endproperty
read_read_idle_eventually_left_a: assert property (disable iff(!ntt_ctrl.reset_n || ntt_ctrl.zeroize) read_read_idle_eventually_left_p);


property read_read_stage_eventually_left_p;
  read_stage
|->
  s_eventually(!read_stage);
endproperty
read_read_stage_eventually_left_a: assert property (disable iff(!ntt_ctrl.reset_n || ntt_ctrl.zeroize) read_read_stage_eventually_left_p);


property read_read_exec_eventually_left_p;
  read_exec
|->
  s_eventually(!read_exec);
endproperty
read_read_exec_eventually_left_a: assert property (disable iff(!ntt_ctrl.reset_n || ntt_ctrl.zeroize) read_read_exec_eventually_left_p);


property read_read_exec_wait_eventually_left_p;
  read_exec_wait
|->
  s_eventually(!read_exec_wait);
endproperty
read_read_exec_wait_eventually_left_a: assert property (disable iff(!ntt_ctrl.reset_n || ntt_ctrl.zeroize) read_read_exec_wait_eventually_left_p);


property write_write_idle_eventually_left_p;
  write_idle 
|->
  s_eventually(!write_idle);
endproperty
write_write_idle_eventually_left_a: assert property (disable iff(!ntt_ctrl.reset_n || ntt_ctrl.zeroize) write_write_idle_eventually_left_p);


property write_write_stage_eventually_left_p;
  write_stage
|->
  s_eventually(!write_stage);
endproperty
write_write_stage_eventually_left_a: assert property (disable iff(!ntt_ctrl.reset_n || ntt_ctrl.zeroize) write_write_stage_eventually_left_p);


property write_write_wait_eventually_left_p;
  write_wait
|->
  s_eventually(!write_wait);
endproperty
write_write_wait_eventually_left_a: assert property (disable iff(!ntt_ctrl.reset_n || ntt_ctrl.zeroize) write_write_wait_eventually_left_p);


property write_write_mem_eventually_left_p;
  write_mem
|->
  s_eventually(!write_mem);
endproperty
write_write_mem_eventually_left_a: assert property (disable iff(!ntt_ctrl.reset_n || ntt_ctrl.zeroize) write_write_mem_eventually_left_p);


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
