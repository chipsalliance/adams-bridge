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


import ntt_ctrl_gs_mlkem_pkg::*;
import abr_params_pkg::*;
import ntt_defines_pkg::*;
import ntt_ctrl_gs_mlkem_pkg::*;
import ntt_ctrl_gs_mlkem_functions::*;


module fv_ntt_ctrl_gs_mlkem_m(
  input logic rst_n,
  input logic clk,

  // Ports
  input logic ntt_enable_in,

  input logic buf0_valid_in,

  input logic shuffle_en_in,

  input logic mlkem_in,

  input logic intt_done_in,

  input logic rst_rounds_in,

  input logic butterfly_ready_in,

  input st_NttBaseAddrs ntt_base_addrs_in,

  input logic unsigned [5:0] random_in,

  input logic bf_enable_out,

  input logic unsigned [2:0] opcode_out,

  input logic masking_en_ctrl_out,

  input logic unsigned [1:0] buf_wrptr_out,

  input logic unsigned [1:0] buf_rdptr_out,

  input logic unsigned [14:0] mem_rd_addr_out,

  input logic unsigned [14:0] mem_wr_addr_out,

  input logic pw_rden_out,

  input logic pw_wren_out,

  input logic done_out,

  input logic intt_passthrough_out,

  // Registers
  input logic bf_enable_reg,
  input logic unsigned [1:0] buf_count,
  input logic unsigned [1:0] buf_wrptr,
  input logic unsigned [25:0] buf_wrptr_reg,
  input logic unsigned [3:0] chunk_count,
  input logic unsigned [43:0] chunk_count_reg,
  input logic unsigned [3:0] chunk_rand_offset,
  input logic incr_twiddle_addr_reg,
  input logic unsigned [1:0] index_count,
  input logic unsigned [1:0] index_rand_offset,
  input logic unsigned [14:0] mem_rd_addr,
  input logic unsigned [14:0] mem_rd_addr_base,
  input logic mem_rd_en_reg,
  input logic unsigned [14:0] mem_wr_addr,
  input logic unsigned [6:0] rd_valid_count,
  input e_GsReadStatesType read_state,
  input logic unsigned [2:0] rounds_count,
  input logic unsigned [6:0] twiddle_addr_reg,
  input logic unsigned [6:0] twiddle_addr_reg_d2,
  input logic unsigned [6:0] twiddle_addr_reg_d3,
  input logic unused_mem_rd_en_reg,
  input logic unsigned [6:0] unused_twiddle_addr_reg_d3,
  input logic unsigned [6:0] wr_valid_count,
  input e_GsWriteStatesType write_state,

  // States
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


logic unsigned [14:0] getMemRdAddrBase_0_i;
assign getMemRdAddrBase_0_i = getMemRdAddrBase(rounds_count, ntt_base_addrs_in);

a_unsigned_7_8 twiddle_rand_offsets_1_i;
assign twiddle_rand_offsets_1_i = '{
  0: ((64'd4 * 4'(({ 40'h0, chunk_count_reg[43:40]} ))) + 2'(({ 24'h0, buf_wrptr_reg[25:24]} ))),
  1: ((64'd4 * ({ 62'h0, { 4'(({ 40'h0, chunk_count_reg[43:40]} )) }[1:0]} )) + 2'(({ 24'h0, buf_wrptr_reg[25:24]} ))),
  2: 2'(({ 24'h0, buf_wrptr_reg[25:24]} )),
  3: 7'd0,
  4: 7'd0,
  5: 7'd0,
  6: 7'd0,
  7: 7'd0
};

logic unsigned [6:0] getTwiddleAddrIncr_0_i;
assign getTwiddleAddrIncr_0_i = getTwiddleAddrIncr(shuffle_en_in, twiddle_rand_offsets_1_i[rounds_count], twiddle_addr_reg, '{ 0: 7'd63, 1: 7'd15, 2: 7'd3, 3: 7'd0, 4: 7'd0, 5: 7'd0, 6: 7'd0, 7: 7'd0 }, rounds_count);

logic unsigned [6:0] getTwiddleAddrReg_0_i;
assign getTwiddleAddrReg_0_i = getTwiddleAddrReg(incr_twiddle_addr_reg, 1, getTwiddleAddrIncr_0_i, twiddle_addr_reg);

logic unsigned [6:0] getTwiddleAddrReg_1_i;
assign getTwiddleAddrReg_1_i = getTwiddleAddrReg(incr_twiddle_addr_reg, !butterfly_ready_in, getTwiddleAddrIncr_0_i, twiddle_addr_reg);

logic unsigned [14:0] get_rd_addr_shuffle_0_i;
assign get_rd_addr_shuffle_0_i = get_rd_addr_shuffle(mem_rd_addr, 15'd1, mem_rd_addr_base, chunk_count, (index_count + index_rand_offset));

logic unsigned [14:0] incr_addr_0_i;
assign incr_addr_0_i = incr_addr(mem_rd_addr, 15'd1, mem_rd_addr_base);

logic unsigned [6:0] getTwiddleAddrReg_2_i;
assign getTwiddleAddrReg_2_i = getTwiddleAddrReg(incr_twiddle_addr_reg, 0, getTwiddleAddrIncr_0_i, twiddle_addr_reg);

logic unsigned [14:0] getMemWrAddrBase_0_i;
assign getMemWrAddrBase_0_i = getMemWrAddrBase(rounds_count, ntt_base_addrs_in);

logic unsigned [1:0] getBufWrptr_0_i;
assign getBufWrptr_0_i = getBufWrptr(shuffle_en_in, mlkem_in, 0, buf_wrptr, buf_wrptr_reg);

logic unsigned [6:0] getWrValidCount_0_i;
assign getWrValidCount_0_i = getWrValidCount(buf0_valid_in, write_state, wr_valid_count);

logic unsigned [14:0] incr_addr_1_i;
assign incr_addr_1_i = incr_addr(mem_wr_addr, 15'd16, getMemWrAddrBase_0_i);

logic unsigned [1:0] getBufWrptr_1_i;
assign getBufWrptr_1_i = getBufWrptr(shuffle_en_in, mlkem_in, butterfly_ready_in, buf_wrptr, buf_wrptr_reg);

logic unsigned [1:0] getBufWrptr_2_i;
assign getBufWrptr_2_i = getBufWrptr(shuffle_en_in, mlkem_in, 1, buf_wrptr, buf_wrptr_reg);

logic unsigned [1:0] getBufWrptr_3_i;
assign getBufWrptr_3_i = getBufWrptr(shuffle_en_in, mlkem_in, !shuffle_en_in, buf_wrptr, buf_wrptr_reg);


sequence reset_sequence;
  !rst_n ##1 rst_n;
endsequence


property read_reset_p;
  $past(!ntt_ctrl.reset_n || ntt_ctrl.zeroize) |->
  read_idle &&
  bf_enable_out == 0 &&
  bf_enable_reg == 0 &&
  buf_wrptr_reg == 26'd0 &&
  chunk_count_reg == 44'd0 &&
  incr_twiddle_addr_reg == 0 &&
  index_count == 2'd0 &&
  index_rand_offset == 2'd0 &&
  masking_en_ctrl_out == 0 &&
  mem_rd_addr == 15'd0 &&
  mem_rd_addr_base == 15'(ntt_base_addrs_in.src_base_addr) &&
  mem_rd_addr_out == 15'd0 &&
  mem_rd_en_reg == 0 &&
  opcode_out == 3'd0 &&
  pw_rden_out == 0 &&
  rd_valid_count == 7'd0 &&
  read_state == GsReadIdle &&
  twiddle_addr_reg == 7'd0 &&
  twiddle_addr_reg_d2 == 7'd0 &&
  twiddle_addr_reg_d3 == 7'd0;
endproperty
read_reset_a: assert property (read_reset_p);


property write_reset_p;
  $past(!ntt_ctrl.reset_n || ntt_ctrl.zeroize) |->
  write_idle &&
  buf_count == 2'd0 &&
  buf_rdptr_out == 2'd0 &&
  buf_wrptr == 2'd0 &&
  buf_wrptr_out == 2'd0 &&
  chunk_count == 4'd0 &&
  chunk_rand_offset == 4'd0 &&
  done_out == 0 &&
  mem_wr_addr == 15'd0 &&
  mem_wr_addr_out == 15'd0 &&
  pw_wren_out == 0 &&
  rounds_count == 3'd0 &&
  wr_valid_count == 7'd0 &&
  write_state == GsWriteIdle;
endproperty
write_reset_a: assert property (write_reset_p);


property read_read_exec_to_read_exec_p;
  read_exec &&
  (rd_valid_count != 7'h3F)
|->
  ##1 ($stable(masking_en_ctrl_out)) and
  ##1 ($stable(pw_rden_out)) and
  ##1
  read_exec &&
  bf_enable_out == ($past(shuffle_en_in, 1) ? $past(bf_enable_reg, 1) : ($past(read_state, 1) == GsReadExec)) &&
  bf_enable_reg == ($past(read_state, 1) == GsReadExec) &&
  buf_wrptr_reg == ((($past(read_state, 1) == GsReadExec) || $past(butterfly_ready_in, 1)) ? ({ 2'(({ 26'({ $past(index_count, 1) }) }[1:0] + { 26'({ $past(index_rand_offset, 1) }) }[1:0])), { $past(buf_wrptr_reg, 1) }[25:2]} ) : 26'd0) &&
  chunk_count_reg == (($past(butterfly_ready_in, 1) || ($past(read_state, 1) == GsReadExec)) ? ({ { 44'({ $past(chunk_count, 1) }) }[3:0], { $past(chunk_count_reg, 1) }[43:4]} ) : $past(chunk_count_reg, 1)) &&
  incr_twiddle_addr_reg == 1 &&
  index_count == 2'((64'd1 + ({ 62'h0, $past(index_count, 1)} ))) &&
  index_rand_offset == (($past(index_count, 1) == 2'd3) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  mem_rd_addr == ($past(shuffle_en_in, 1) ? $past(get_rd_addr_shuffle_0_i, 1) : $past(incr_addr_0_i, 1)) &&
  $stable(mem_rd_addr_base) &&
  mem_rd_addr_out == ($past(shuffle_en_in, 1) ? $past(get_rd_addr_shuffle_0_i, 1) : $past(incr_addr_0_i, 1)) &&
  mem_rd_en_reg == (({ 49'h0, $past(mem_rd_addr, 1)} ) <= (64'd63 + ({ 49'h0, $past(mem_rd_addr_base, 1)} ))) &&
  opcode_out == 3'd1 &&
  rd_valid_count == 7'((64'd1 + ({ 57'h0, $past(rd_valid_count, 1)} ))) &&
  read_state == GsReadExec &&
  twiddle_addr_reg == $past(getTwiddleAddrReg_2_i, 1) &&
  twiddle_addr_reg_d2 == ($past(shuffle_en_in, 1) ? ($past(twiddle_rand_offsets_1_i[rounds_count], 1) + $past(twiddle_offsets[rounds_count], 1)) : ($past(twiddle_addr_reg, 1) + $past(twiddle_offsets[rounds_count], 1))) &&
  twiddle_addr_reg_d3 == $past(twiddle_addr_reg_d2, 1);
endproperty
read_read_exec_to_read_exec_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) read_read_exec_to_read_exec_p);


property read_read_exec_to_read_stage_p;
  read_exec &&
  (rd_valid_count == 7'h3F)
|->
  ##1 ($stable(masking_en_ctrl_out)) and
  ##1 ($stable(pw_rden_out)) and
  ##1
  read_stage &&
  bf_enable_out == ($past(shuffle_en_in, 1) ? $past(bf_enable_reg, 1) : ($past(read_state, 1) == GsReadExec)) &&
  bf_enable_reg == ($past(read_state, 1) == GsReadExec) &&
  buf_wrptr_reg == ((($past(read_state, 1) == GsReadExec) || $past(butterfly_ready_in, 1)) ? ({ 2'(({ 26'({ $past(index_count, 1) }) }[1:0] + { 26'({ $past(index_rand_offset, 1) }) }[1:0])), { $past(buf_wrptr_reg, 1) }[25:2]} ) : 26'd0) &&
  chunk_count_reg == (($past(butterfly_ready_in, 1) || ($past(read_state, 1) == GsReadExec)) ? ({ { 44'({ $past(chunk_count, 1) }) }[3:0], { $past(chunk_count_reg, 1) }[43:4]} ) : $past(chunk_count_reg, 1)) &&
  incr_twiddle_addr_reg == 1 &&
  index_count == 2'((64'd1 + ({ 62'h0, $past(index_count, 1)} ))) &&
  index_rand_offset == (($past(index_count, 1) == 2'd3) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  mem_rd_addr == ($past(shuffle_en_in, 1) ? $past(get_rd_addr_shuffle_0_i, 1) : $past(incr_addr_0_i, 1)) &&
  $stable(mem_rd_addr_base) &&
  mem_rd_addr_out == ($past(shuffle_en_in, 1) ? $past(get_rd_addr_shuffle_0_i, 1) : $past(incr_addr_0_i, 1)) &&
  mem_rd_en_reg == (({ 49'h0, $past(mem_rd_addr, 1)} ) <= (64'd63 + ({ 49'h0, $past(mem_rd_addr_base, 1)} ))) &&
  opcode_out == 3'd1 &&
  rd_valid_count == 7'((64'd1 + ({ 57'h0, $past(rd_valid_count, 1)} ))) &&
  read_state == GsReadStage &&
  twiddle_addr_reg == $past(getTwiddleAddrReg_2_i, 1) &&
  twiddle_addr_reg_d2 == ($past(shuffle_en_in, 1) ? ($past(twiddle_rand_offsets_1_i[rounds_count], 1) + $past(twiddle_offsets[rounds_count], 1)) : ($past(twiddle_addr_reg, 1) + $past(twiddle_offsets[rounds_count], 1))) &&
  twiddle_addr_reg_d3 == $past(twiddle_addr_reg_d2, 1);
endproperty
read_read_exec_to_read_stage_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) read_read_exec_to_read_stage_p);


property read_read_idle_to_read_idle_p;
  read_idle &&
  !ntt_enable_in
|->
  ##1 ($stable(masking_en_ctrl_out)) and
  ##1 ($stable(pw_rden_out)) and
  ##1
  read_idle &&
  bf_enable_out == ($past(shuffle_en_in, 1) ? $past(bf_enable_reg, 1) : ($past(read_state, 1) == GsReadExec)) &&
  bf_enable_reg == ($past(read_state, 1) == GsReadExec) &&
  buf_wrptr_reg == ((($past(read_state, 1) == GsReadExec) || $past(butterfly_ready_in, 1)) ? ({ 2'(({ 26'({ $past(index_count, 1) }) }[1:0] + { 26'({ $past(index_rand_offset, 1) }) }[1:0])), { $past(buf_wrptr_reg, 1) }[25:2]} ) : 26'd0) &&
  chunk_count_reg == (($past(butterfly_ready_in, 1) || ($past(read_state, 1) == GsReadExec)) ? ({ { 44'({ $past(chunk_count, 1) }) }[3:0], { $past(chunk_count_reg, 1) }[43:4]} ) : $past(chunk_count_reg, 1)) &&
  incr_twiddle_addr_reg == 0 &&
  $stable(index_count) &&
  index_rand_offset == (($past(index_count, 1) == 2'd3) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  mem_rd_addr == ($past(shuffle_en_in, 1) ? ($past(getMemRdAddrBase_0_i, 1) + ({ ({ 9'h0, $past(chunk_rand_offset, 1)} ), 2'h0} )) : $past(getMemRdAddrBase_0_i, 1)) &&
  mem_rd_addr_base == $past(getMemRdAddrBase_0_i, 1) &&
  mem_rd_addr_out == ($past(shuffle_en_in, 1) ? ($past(getMemRdAddrBase_0_i, 1) + ({ ({ 9'h0, $past(chunk_rand_offset, 1)} ), 2'h0} )) : $past(getMemRdAddrBase_0_i, 1)) &&
  mem_rd_en_reg == 0 &&
  opcode_out == 3'd1 &&
  rd_valid_count == 7'd0 &&
  read_state == GsReadIdle &&
  twiddle_addr_reg == $past(getTwiddleAddrReg_0_i, 1) &&
  twiddle_addr_reg_d2 == ($past(shuffle_en_in, 1) ? ($past(twiddle_rand_offsets_1_i[rounds_count], 1) + $past(twiddle_offsets[rounds_count], 1)) : ($past(twiddle_addr_reg, 1) + $past(twiddle_offsets[rounds_count], 1))) &&
  twiddle_addr_reg_d3 == $past(twiddle_addr_reg_d2, 1);
endproperty
read_read_idle_to_read_idle_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) read_read_idle_to_read_idle_p);


property read_read_idle_to_read_stage_p;
  read_idle &&
  ntt_enable_in
|->
  ##1 ($stable(masking_en_ctrl_out)) and
  ##1 ($stable(pw_rden_out)) and
  ##1
  read_stage &&
  bf_enable_out == ($past(shuffle_en_in, 1) ? $past(bf_enable_reg, 1) : ($past(read_state, 1) == GsReadExec)) &&
  bf_enable_reg == ($past(read_state, 1) == GsReadExec) &&
  buf_wrptr_reg == ((($past(read_state, 1) == GsReadExec) || $past(butterfly_ready_in, 1)) ? ({ 2'(({ 26'({ $past(index_count, 1) }) }[1:0] + { 26'({ $past(index_rand_offset, 1) }) }[1:0])), { $past(buf_wrptr_reg, 1) }[25:2]} ) : 26'd0) &&
  chunk_count_reg == (($past(butterfly_ready_in, 1) || ($past(read_state, 1) == GsReadExec)) ? ({ { 44'({ $past(chunk_count, 1) }) }[3:0], { $past(chunk_count_reg, 1) }[43:4]} ) : $past(chunk_count_reg, 1)) &&
  incr_twiddle_addr_reg == 0 &&
  $stable(index_count) &&
  index_rand_offset == (($past(index_count, 1) == 2'd3) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  mem_rd_addr == ($past(shuffle_en_in, 1) ? ($past(getMemRdAddrBase_0_i, 1) + ({ ({ 9'h0, $past(chunk_rand_offset, 1)} ), 2'h0} )) : $past(getMemRdAddrBase_0_i, 1)) &&
  mem_rd_addr_base == $past(getMemRdAddrBase_0_i, 1) &&
  mem_rd_addr_out == ($past(shuffle_en_in, 1) ? ($past(getMemRdAddrBase_0_i, 1) + ({ ({ 9'h0, $past(chunk_rand_offset, 1)} ), 2'h0} )) : $past(getMemRdAddrBase_0_i, 1)) &&
  mem_rd_en_reg == 0 &&
  opcode_out == 3'd1 &&
  rd_valid_count == 7'd0 &&
  read_state == GsReadStage &&
  twiddle_addr_reg == $past(getTwiddleAddrReg_0_i, 1) &&
  twiddle_addr_reg_d2 == ($past(shuffle_en_in, 1) ? ($past(twiddle_rand_offsets_1_i[rounds_count], 1) + $past(twiddle_offsets[rounds_count], 1)) : ($past(twiddle_addr_reg, 1) + $past(twiddle_offsets[rounds_count], 1))) &&
  twiddle_addr_reg_d3 == $past(twiddle_addr_reg_d2, 1);
endproperty
read_read_idle_to_read_stage_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) read_read_idle_to_read_stage_p);


property read_read_stage_to_read_exec_p;
  read_stage &&
  (rounds_count != 3'd4) &&
  (write_state == GsWriteStage) &&
  !intt_done_in
|->
  ##1 ($stable(masking_en_ctrl_out)) and
  ##1 ($stable(pw_rden_out)) and
  ##1
  read_exec &&
  bf_enable_out == ($past(shuffle_en_in, 1) ? $past(bf_enable_reg, 1) : ($past(read_state, 1) == GsReadExec)) &&
  bf_enable_reg == ($past(read_state, 1) == GsReadExec) &&
  buf_wrptr_reg == ((($past(read_state, 1) == GsReadExec) || $past(butterfly_ready_in, 1)) ? ({ 2'(({ 26'({ $past(index_count, 1) }) }[1:0] + { 26'({ $past(index_rand_offset, 1) }) }[1:0])), { $past(buf_wrptr_reg, 1) }[25:2]} ) : 26'd0) &&
  chunk_count_reg == (($past(butterfly_ready_in, 1) || ($past(read_state, 1) == GsReadExec)) ? ({ { 44'({ $past(chunk_count, 1) }) }[3:0], { $past(chunk_count_reg, 1) }[43:4]} ) : $past(chunk_count_reg, 1)) &&
  incr_twiddle_addr_reg == 0 &&
  $stable(index_count) &&
  index_rand_offset == { $past(random_in, 1) }[1:0] &&
  mem_rd_addr == ($past(shuffle_en_in, 1) ? ($past(getMemRdAddrBase_0_i, 1) + ({ ({ 9'h0, $past(chunk_rand_offset, 1)} ), 2'h0} )) : $past(getMemRdAddrBase_0_i, 1)) &&
  mem_rd_addr_base == $past(getMemRdAddrBase_0_i, 1) &&
  mem_rd_addr_out == ($past(shuffle_en_in, 1) ? ($past(getMemRdAddrBase_0_i, 1) + ({ ({ 9'h0, $past(chunk_rand_offset, 1)} ), 2'h0} )) : $past(getMemRdAddrBase_0_i, 1)) &&
  mem_rd_en_reg == 0 &&
  opcode_out == 3'd1 &&
  rd_valid_count == 7'd0 &&
  read_state == GsReadExec &&
  twiddle_addr_reg == $past(getTwiddleAddrReg_1_i, 1) &&
  twiddle_addr_reg_d2 == ($past(shuffle_en_in, 1) ? ($past(twiddle_rand_offsets_1_i[rounds_count], 1) + $past(twiddle_offsets[rounds_count], 1)) : ($past(twiddle_addr_reg, 1) + $past(twiddle_offsets[rounds_count], 1))) &&
  twiddle_addr_reg_d3 == $past(twiddle_addr_reg_d2, 1);
endproperty
read_read_stage_to_read_exec_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) read_read_stage_to_read_exec_p);


property read_read_stage_to_read_idle_p;
  read_stage &&
  (rounds_count == 3'd4)
|->
  ##1 ($stable(masking_en_ctrl_out)) and
  ##1 ($stable(pw_rden_out)) and
  ##1
  read_idle &&
  bf_enable_out == ($past(shuffle_en_in, 1) ? $past(bf_enable_reg, 1) : ($past(read_state, 1) == GsReadExec)) &&
  bf_enable_reg == ($past(read_state, 1) == GsReadExec) &&
  buf_wrptr_reg == ((($past(read_state, 1) == GsReadExec) || $past(butterfly_ready_in, 1)) ? ({ 2'(({ 26'({ $past(index_count, 1) }) }[1:0] + { 26'({ $past(index_rand_offset, 1) }) }[1:0])), { $past(buf_wrptr_reg, 1) }[25:2]} ) : 26'd0) &&
  chunk_count_reg == (($past(butterfly_ready_in, 1) || ($past(read_state, 1) == GsReadExec)) ? ({ { 44'({ $past(chunk_count, 1) }) }[3:0], { $past(chunk_count_reg, 1) }[43:4]} ) : $past(chunk_count_reg, 1)) &&
  incr_twiddle_addr_reg == 0 &&
  $stable(index_count) &&
  index_rand_offset == (($past(index_count, 1) == 2'd3) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  mem_rd_addr == ($past(shuffle_en_in, 1) ? ($past(getMemRdAddrBase_0_i, 1) + ({ ({ 9'h0, $past(chunk_rand_offset, 1)} ), 2'h0} )) : $past(getMemRdAddrBase_0_i, 1)) &&
  mem_rd_addr_base == $past(getMemRdAddrBase_0_i, 1) &&
  mem_rd_addr_out == ($past(shuffle_en_in, 1) ? ($past(getMemRdAddrBase_0_i, 1) + ({ ({ 9'h0, $past(chunk_rand_offset, 1)} ), 2'h0} )) : $past(getMemRdAddrBase_0_i, 1)) &&
  mem_rd_en_reg == 0 &&
  opcode_out == 3'd1 &&
  rd_valid_count == 7'd0 &&
  read_state == GsReadIdle &&
  twiddle_addr_reg == $past(getTwiddleAddrReg_1_i, 1) &&
  twiddle_addr_reg_d2 == ($past(shuffle_en_in, 1) ? ($past(twiddle_rand_offsets_1_i[rounds_count], 1) + $past(twiddle_offsets[rounds_count], 1)) : ($past(twiddle_addr_reg, 1) + $past(twiddle_offsets[rounds_count], 1))) &&
  twiddle_addr_reg_d3 == $past(twiddle_addr_reg_d2, 1);
endproperty
read_read_stage_to_read_idle_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) read_read_stage_to_read_idle_p);


property read_read_stage_to_read_stage_p;
  read_stage &&
  (rounds_count != 3'd4) &&
  ((write_state != GsWriteStage) || intt_done_in) &&
  (read_state == GsReadStage)
|->
  ##1 ($stable(masking_en_ctrl_out)) and
  ##1 ($stable(pw_rden_out)) and
  ##1
  read_stage &&
  bf_enable_out == ($past(shuffle_en_in, 1) ? $past(bf_enable_reg, 1) : ($past(read_state, 1) == GsReadExec)) &&
  bf_enable_reg == ($past(read_state, 1) == GsReadExec) &&
  buf_wrptr_reg == ((($past(read_state, 1) == GsReadExec) || $past(butterfly_ready_in, 1)) ? ({ 2'(({ 26'({ $past(index_count, 1) }) }[1:0] + { 26'({ $past(index_rand_offset, 1) }) }[1:0])), { $past(buf_wrptr_reg, 1) }[25:2]} ) : 26'd0) &&
  chunk_count_reg == (($past(butterfly_ready_in, 1) || ($past(read_state, 1) == GsReadExec)) ? ({ { 44'({ $past(chunk_count, 1) }) }[3:0], { $past(chunk_count_reg, 1) }[43:4]} ) : $past(chunk_count_reg, 1)) &&
  incr_twiddle_addr_reg == 0 &&
  $stable(index_count) &&
  index_rand_offset == (($past(index_count, 1) == 2'd3) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  mem_rd_addr == ($past(shuffle_en_in, 1) ? ($past(getMemRdAddrBase_0_i, 1) + ({ ({ 9'h0, $past(chunk_rand_offset, 1)} ), 2'h0} )) : $past(getMemRdAddrBase_0_i, 1)) &&
  mem_rd_addr_base == $past(getMemRdAddrBase_0_i, 1) &&
  mem_rd_addr_out == ($past(shuffle_en_in, 1) ? ($past(getMemRdAddrBase_0_i, 1) + ({ ({ 9'h0, $past(chunk_rand_offset, 1)} ), 2'h0} )) : $past(getMemRdAddrBase_0_i, 1)) &&
  mem_rd_en_reg == 0 &&
  opcode_out == 3'd1 &&
  rd_valid_count == 7'd0 &&
  $stable(read_state) &&
  twiddle_addr_reg == $past(getTwiddleAddrReg_1_i, 1) &&
  twiddle_addr_reg_d2 == ($past(shuffle_en_in, 1) ? ($past(twiddle_rand_offsets_1_i[rounds_count], 1) + $past(twiddle_offsets[rounds_count], 1)) : ($past(twiddle_addr_reg, 1) + $past(twiddle_offsets[rounds_count], 1))) &&
  twiddle_addr_reg_d3 == $past(twiddle_addr_reg_d2, 1);
endproperty
read_read_stage_to_read_stage_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) read_read_stage_to_read_stage_p);


property write_write_buf_to_write_buf_p;
  write_buf &&
  !buf0_valid_in
|->
  ##1 ($stable(pw_wren_out)) and
  ##1
  write_buf &&
  buf_count == (($past(buf0_valid_in, 1) || ((({ 62'd0, $past(buf_count, 1)} ) > 64'd0) && (({ 62'd0, $past(buf_count, 1)} ) < 64'd3))) ? 2'((64'd1 + ({ 62'd0, $past(buf_count, 1)} ))) : 64'd0) &&
  buf_rdptr_out == (($past(buf0_valid_in, 1) || ((({ 62'd0, $past(buf_count, 1)} ) > 64'd0) && (({ 62'd0, $past(buf_count, 1)} ) < 64'd3))) ? 2'((64'd1 + ({ 62'd0, $past(buf_count, 1)} ))) : 64'd0) &&
  buf_wrptr == $past(getBufWrptr_1_i, 1) &&
  buf_wrptr_out == $past(getBufWrptr_1_i, 1) &&
  chunk_count == (($past(index_count, 1) == 2'd3) ? 4'((64'd1 + ({ 60'h0, $past(chunk_count, 1)} ))) : ({ 60'h0, $past(chunk_count, 1)} )) &&
  $stable(chunk_rand_offset) &&
  done_out == ((($past(rst_rounds_in, 1) || ($past(rounds_count, 1) == 3'd4)) ? 3'd0 : $past(rounds_count, 1)) == 3'd4) &&
  intt_passthrough_out == (((($past(rst_rounds_in, 1) || ($past(rounds_count, 1) == 3'd4)) ? 3'd0 : $past(rounds_count, 1)) == 3'd0) && $past(mlkem_in, 1)) &&
  $stable(mem_wr_addr) &&
  mem_wr_addr_out == $past(mem_wr_addr, 1) &&
  rounds_count == (($past(rst_rounds_in, 1) || ($past(rounds_count, 1) == 3'd4)) ? 3'd0 : $past(rounds_count, 1)) &&
  wr_valid_count == $past(getWrValidCount_0_i, 1) &&
  write_state == GsWriteBuf;
endproperty
write_write_buf_to_write_buf_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) write_write_buf_to_write_buf_p);


property write_write_buf_to_write_mem_p;
  write_buf &&
  buf0_valid_in
|->
  ##1 ($stable(pw_wren_out)) and
  ##1
  write_mem &&
  buf_count == 2'((64'd1 + ({ 62'h0, $past(buf_count, 1)} ))) &&
  buf_rdptr_out == 2'((64'd1 + ({ 62'h0, $past(buf_count, 1)} ))) &&
  buf_wrptr == $past(getBufWrptr_1_i, 1) &&
  buf_wrptr_out == $past(getBufWrptr_1_i, 1) &&
  chunk_count == (($past(index_count, 1) == 2'd3) ? 4'((64'd1 + ({ 60'h0, $past(chunk_count, 1)} ))) : ({ 60'h0, $past(chunk_count, 1)} )) &&
  $stable(chunk_rand_offset) &&
  done_out == ((($past(rst_rounds_in, 1) || ($past(rounds_count, 1) == 3'd4)) ? 3'd0 : $past(rounds_count, 1)) == 3'd4) &&
  intt_passthrough_out == (((($past(rst_rounds_in, 1) || ($past(rounds_count, 1) == 3'd4)) ? 3'd0 : $past(rounds_count, 1)) == 3'd0) && $past(mlkem_in, 1)) &&
  mem_wr_addr == (($past(shuffle_en_in, 1) && (({ 49'h0, $past(mem_wr_addr, 1)} ) == (64'd63 + ({ 49'h0, $past(getMemWrAddrBase_0_i, 1)} )))) ? $past(getMemWrAddrBase_0_i, 1) : $past(incr_addr_1_i, 1)) &&
  mem_wr_addr_out == (($past(shuffle_en_in, 1) && (({ 49'h0, $past(mem_wr_addr, 1)} ) == (64'd63 + ({ 49'h0, $past(getMemWrAddrBase_0_i, 1)} )))) ? $past(getMemWrAddrBase_0_i, 1) : $past(incr_addr_1_i, 1)) &&
  rounds_count == (($past(rst_rounds_in, 1) || ($past(rounds_count, 1) == 3'd4)) ? 3'd0 : $past(rounds_count, 1)) &&
  wr_valid_count == $past(getWrValidCount_0_i, 1) &&
  write_state == GsWriteMem;
endproperty
write_write_buf_to_write_mem_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) write_write_buf_to_write_mem_p);


property write_write_idle_to_write_idle_p;
  write_idle &&
  !ntt_enable_in
|->
  ##1 ($stable(pw_wren_out)) and
  ##1
  write_idle &&
  buf_count == (($past(buf0_valid_in, 1) || ((({ 62'd0, $past(buf_count, 1)} ) > 64'd0) && (({ 62'd0, $past(buf_count, 1)} ) < 64'd3))) ? 2'((64'd1 + ({ 62'd0, $past(buf_count, 1)} ))) : 64'd0) &&
  buf_rdptr_out == (($past(buf0_valid_in, 1) || ((({ 62'd0, $past(buf_count, 1)} ) > 64'd0) && (({ 62'd0, $past(buf_count, 1)} ) < 64'd3))) ? 2'((64'd1 + ({ 62'd0, $past(buf_count, 1)} ))) : 64'd0) &&
  buf_wrptr == $past(getBufWrptr_0_i, 1) &&
  buf_wrptr_out == $past(getBufWrptr_0_i, 1) &&
  chunk_count == (($past(index_count, 1) == 2'd3) ? 4'((64'd1 + ({ 60'h0, $past(chunk_count, 1)} ))) : ({ 60'h0, $past(chunk_count, 1)} )) &&
  $stable(chunk_rand_offset) &&
  done_out == ((($past(rst_rounds_in, 1) || ($past(rounds_count, 1) == 3'd4)) ? 3'd0 : $past(rounds_count, 1)) == 3'd4) &&
  intt_passthrough_out == (((($past(rst_rounds_in, 1) || ($past(rounds_count, 1) == 3'd4)) ? 3'd0 : $past(rounds_count, 1)) == 3'd0) && $past(mlkem_in, 1)) &&
  mem_wr_addr == ($past(shuffle_en_in, 1) ? ($past(getMemWrAddrBase_0_i, 1) + ({ 11'h0, $past(chunk_rand_offset, 1)} )) : $past(getMemWrAddrBase_0_i, 1)) &&
  mem_wr_addr_out == ($past(shuffle_en_in, 1) ? ($past(getMemWrAddrBase_0_i, 1) + ({ 11'h0, $past(chunk_rand_offset, 1)} )) : $past(getMemWrAddrBase_0_i, 1)) &&
  rounds_count == (($past(rst_rounds_in, 1) || ($past(rounds_count, 1) == 3'd4)) ? 3'd0 : $past(rounds_count, 1)) &&
  wr_valid_count == $past(getWrValidCount_0_i, 1) &&
  write_state == GsWriteIdle;
endproperty
write_write_idle_to_write_idle_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) write_write_idle_to_write_idle_p);


property write_write_idle_to_write_stage_p;
  write_idle &&
  ntt_enable_in
|->
  ##1 ($stable(pw_wren_out)) and
  ##1
  write_stage &&
  buf_count == (($past(buf0_valid_in, 1) || ((({ 62'd0, $past(buf_count, 1)} ) > 64'd0) && (({ 62'd0, $past(buf_count, 1)} ) < 64'd3))) ? 2'((64'd1 + ({ 62'd0, $past(buf_count, 1)} ))) : 64'd0) &&
  buf_rdptr_out == (($past(buf0_valid_in, 1) || ((({ 62'd0, $past(buf_count, 1)} ) > 64'd0) && (({ 62'd0, $past(buf_count, 1)} ) < 64'd3))) ? 2'((64'd1 + ({ 62'd0, $past(buf_count, 1)} ))) : 64'd0) &&
  buf_wrptr == $past(getBufWrptr_0_i, 1) &&
  buf_wrptr_out == $past(getBufWrptr_0_i, 1) &&
  chunk_count == { $past(random_in, 1) }[5:2] &&
  chunk_rand_offset == { $past(random_in, 1) }[5:2] &&
  done_out == ((($past(rst_rounds_in, 1) || ($past(rounds_count, 1) == 3'd4)) ? 64'd0 : (($past(write_state, 1) == GsWriteWait) ? 3'((64'd1 + ({ 61'd0, $past(rounds_count, 1)} ))) : ({ 61'd0, $past(rounds_count, 1)} ))) == 64'd4) &&
  intt_passthrough_out == (((($past(rst_rounds_in, 1) || ($past(rounds_count, 1) == 3'd4)) ? 64'd0 : (($past(write_state, 1) == GsWriteWait) ? 3'((64'd1 + ({ 61'd0, $past(rounds_count, 1)} ))) : ({ 61'd0, $past(rounds_count, 1)} ))) == 64'd0) && $past(mlkem_in, 1)) &&
  mem_wr_addr == ($past(shuffle_en_in, 1) ? ($past(getMemWrAddrBase_0_i, 1) + ({ 11'h0, $past(chunk_rand_offset, 1)} )) : $past(getMemWrAddrBase_0_i, 1)) &&
  mem_wr_addr_out == ($past(shuffle_en_in, 1) ? ($past(getMemWrAddrBase_0_i, 1) + ({ 11'h0, $past(chunk_rand_offset, 1)} )) : $past(getMemWrAddrBase_0_i, 1)) &&
  rounds_count == 3'((($past(rst_rounds_in, 1) || ($past(rounds_count, 1) == 3'd4)) ? 64'd0 : (($past(write_state, 1) == GsWriteWait) ? 3'((64'd1 + ({ 61'd0, $past(rounds_count, 1)} ))) : ({ 61'd0, $past(rounds_count, 1)} )))) &&
  wr_valid_count == $past(getWrValidCount_0_i, 1) &&
  write_state == GsWriteStage;
endproperty
write_write_idle_to_write_stage_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) write_write_idle_to_write_stage_p);


property write_write_mem_to_write_buf_p;
  write_mem &&
  !buf0_valid_in &&
  (buf_count == 2'd0) &&
  (({ 57'd0, wr_valid_count} ) < 64'h40)
|->
  ##1 ($stable(pw_wren_out)) and
  ##1
  write_buf &&
  buf_count == 2'd0 &&
  buf_rdptr_out == 2'd0 &&
  buf_wrptr == $past(getBufWrptr_2_i, 1) &&
  buf_wrptr_out == $past(getBufWrptr_2_i, 1) &&
  chunk_count == (($past(index_count, 1) == 2'd3) ? 4'((64'd1 + ({ 60'h0, $past(chunk_count, 1)} ))) : ({ 60'h0, $past(chunk_count, 1)} )) &&
  $stable(chunk_rand_offset) &&
  done_out == ((($past(rst_rounds_in, 1) || ($past(rounds_count, 1) == 3'd4)) ? 3'd0 : $past(rounds_count, 1)) == 3'd4) &&
  intt_passthrough_out == (((($past(rst_rounds_in, 1) || ($past(rounds_count, 1) == 3'd4)) ? 3'd0 : $past(rounds_count, 1)) == 3'd0) && $past(mlkem_in, 1)) &&
  mem_wr_addr == (($past(shuffle_en_in, 1) && (({ 49'h0, $past(mem_wr_addr, 1)} ) == (64'd63 + ({ 49'h0, $past(getMemWrAddrBase_0_i, 1)} )))) ? $past(getMemWrAddrBase_0_i, 1) : $past(incr_addr_1_i, 1)) &&
  mem_wr_addr_out == (($past(shuffle_en_in, 1) && (({ 49'h0, $past(mem_wr_addr, 1)} ) == (64'd63 + ({ 49'h0, $past(getMemWrAddrBase_0_i, 1)} )))) ? $past(getMemWrAddrBase_0_i, 1) : $past(incr_addr_1_i, 1)) &&
  rounds_count == (($past(rst_rounds_in, 1) || ($past(rounds_count, 1) == 3'd4)) ? 3'd0 : $past(rounds_count, 1)) &&
  wr_valid_count == $past(getWrValidCount_0_i, 1) &&
  write_state == GsWriteBuf;
endproperty
write_write_mem_to_write_buf_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) write_write_mem_to_write_buf_p);


property write_write_mem_to_write_mem_p;
  write_mem &&
  !((!buf0_valid_in && (buf_count == 2'd0)) && (({ 57'd0, wr_valid_count} ) < 64'h40)) &&
  !(buf0_valid_in && (wr_valid_count == 7'h3C))
|->
  ##1 ($stable(pw_wren_out)) and
  ##1
  write_mem &&
  buf_count == (($past(buf0_valid_in, 1) || ((({ 62'd0, $past(buf_count, 1)} ) > 64'd0) && (({ 62'd0, $past(buf_count, 1)} ) < 64'd3))) ? 2'((64'd1 + ({ 62'd0, $past(buf_count, 1)} ))) : 64'd0) &&
  buf_rdptr_out == (($past(buf0_valid_in, 1) || ((({ 62'd0, $past(buf_count, 1)} ) > 64'd0) && (({ 62'd0, $past(buf_count, 1)} ) < 64'd3))) ? 2'((64'd1 + ({ 62'd0, $past(buf_count, 1)} ))) : 64'd0) &&
  buf_wrptr == $past(getBufWrptr_2_i, 1) &&
  buf_wrptr_out == $past(getBufWrptr_2_i, 1) &&
  chunk_count == (($past(index_count, 1) == 2'd3) ? 4'((64'd1 + ({ 60'h0, $past(chunk_count, 1)} ))) : ({ 60'h0, $past(chunk_count, 1)} )) &&
  $stable(chunk_rand_offset) &&
  done_out == ((($past(rst_rounds_in, 1) || ($past(rounds_count, 1) == 3'd4)) ? 3'd0 : $past(rounds_count, 1)) == 3'd4) &&
  intt_passthrough_out == (((($past(rst_rounds_in, 1) || ($past(rounds_count, 1) == 3'd4)) ? 3'd0 : $past(rounds_count, 1)) == 3'd0) && $past(mlkem_in, 1)) &&
  mem_wr_addr == (($past(shuffle_en_in, 1) && (({ 49'h0, $past(mem_wr_addr, 1)} ) == (64'd63 + ({ 49'h0, $past(getMemWrAddrBase_0_i, 1)} )))) ? $past(getMemWrAddrBase_0_i, 1) : $past(incr_addr_1_i, 1)) &&
  mem_wr_addr_out == (($past(shuffle_en_in, 1) && (({ 49'h0, $past(mem_wr_addr, 1)} ) == (64'd63 + ({ 49'h0, $past(getMemWrAddrBase_0_i, 1)} )))) ? $past(getMemWrAddrBase_0_i, 1) : $past(incr_addr_1_i, 1)) &&
  rounds_count == (($past(rst_rounds_in, 1) || ($past(rounds_count, 1) == 3'd4)) ? 3'd0 : $past(rounds_count, 1)) &&
  wr_valid_count == $past(getWrValidCount_0_i, 1) &&
  write_state == GsWriteMem;
endproperty
write_write_mem_to_write_mem_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) write_write_mem_to_write_mem_p);


property write_write_mem_to_write_wait_p;
  write_mem &&
  !((!buf0_valid_in && (buf_count == 2'd0)) && (({ 57'd0, wr_valid_count} ) < 64'h40)) &&
  buf0_valid_in &&
  (wr_valid_count == 7'h3C)
|->
  ##1 ($stable(pw_wren_out)) and
  ##1
  write_wait &&
  buf_count == 2'((64'd1 + ({ 62'h0, $past(buf_count, 1)} ))) &&
  buf_rdptr_out == 2'((64'd1 + ({ 62'h0, $past(buf_count, 1)} ))) &&
  buf_wrptr == $past(getBufWrptr_2_i, 1) &&
  buf_wrptr_out == $past(getBufWrptr_2_i, 1) &&
  chunk_count == (($past(index_count, 1) == 2'd3) ? 4'((64'd1 + ({ 60'h0, $past(chunk_count, 1)} ))) : ({ 60'h0, $past(chunk_count, 1)} )) &&
  $stable(chunk_rand_offset) &&
  done_out == ((($past(rst_rounds_in, 1) || ($past(rounds_count, 1) == 3'd4)) ? 3'd0 : $past(rounds_count, 1)) == 3'd4) &&
  intt_passthrough_out == (((($past(rst_rounds_in, 1) || ($past(rounds_count, 1) == 3'd4)) ? 3'd0 : $past(rounds_count, 1)) == 3'd0) && $past(mlkem_in, 1)) &&
  mem_wr_addr == (($past(shuffle_en_in, 1) && (({ 49'h0, $past(mem_wr_addr, 1)} ) == (64'd63 + ({ 49'h0, $past(getMemWrAddrBase_0_i, 1)} )))) ? $past(getMemWrAddrBase_0_i, 1) : $past(incr_addr_1_i, 1)) &&
  mem_wr_addr_out == (($past(shuffle_en_in, 1) && (({ 49'h0, $past(mem_wr_addr, 1)} ) == (64'd63 + ({ 49'h0, $past(getMemWrAddrBase_0_i, 1)} )))) ? $past(getMemWrAddrBase_0_i, 1) : $past(incr_addr_1_i, 1)) &&
  rounds_count == (($past(rst_rounds_in, 1) || ($past(rounds_count, 1) == 3'd4)) ? 3'd0 : $past(rounds_count, 1)) &&
  wr_valid_count == $past(getWrValidCount_0_i, 1) &&
  write_state == GsWriteWait;
endproperty
write_write_mem_to_write_wait_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) write_write_mem_to_write_wait_p);


property write_write_stage_to_write_buf_p;
  write_stage &&
  (rounds_count != 3'd4)
|->
  ##1 ($stable(pw_wren_out)) and
  ##1
  write_buf &&
  buf_count == (($past(buf0_valid_in, 1) || ((({ 62'd0, $past(buf_count, 1)} ) > 64'd0) && (({ 62'd0, $past(buf_count, 1)} ) < 64'd3))) ? 2'((64'd1 + ({ 62'd0, $past(buf_count, 1)} ))) : 64'd0) &&
  buf_rdptr_out == (($past(buf0_valid_in, 1) || ((({ 62'd0, $past(buf_count, 1)} ) > 64'd0) && (({ 62'd0, $past(buf_count, 1)} ) < 64'd3))) ? 2'((64'd1 + ({ 62'd0, $past(buf_count, 1)} ))) : 64'd0) &&
  buf_wrptr == $past(getBufWrptr_0_i, 1) &&
  buf_wrptr_out == $past(getBufWrptr_0_i, 1) &&
  chunk_count == (($past(index_count, 1) == 2'd3) ? 4'((64'd1 + ({ 60'h0, $past(chunk_count, 1)} ))) : ({ 60'h0, $past(chunk_count, 1)} )) &&
  $stable(chunk_rand_offset) &&
  done_out == ((($past(rst_rounds_in, 1) || ($past(rounds_count, 1) == 3'd4)) ? 3'd0 : $past(rounds_count, 1)) == 3'd4) &&
  intt_passthrough_out == (((($past(rst_rounds_in, 1) || ($past(rounds_count, 1) == 3'd4)) ? 3'd0 : $past(rounds_count, 1)) == 3'd0) && $past(mlkem_in, 1)) &&
  mem_wr_addr == ($past(shuffle_en_in, 1) ? ($past(getMemWrAddrBase_0_i, 1) + ({ 11'h0, $past(chunk_rand_offset, 1)} )) : $past(getMemWrAddrBase_0_i, 1)) &&
  mem_wr_addr_out == ($past(shuffle_en_in, 1) ? ($past(getMemWrAddrBase_0_i, 1) + ({ 11'h0, $past(chunk_rand_offset, 1)} )) : $past(getMemWrAddrBase_0_i, 1)) &&
  rounds_count == (($past(rst_rounds_in, 1) || ($past(rounds_count, 1) == 3'd4)) ? 3'd0 : $past(rounds_count, 1)) &&
  wr_valid_count == $past(getWrValidCount_0_i, 1) &&
  write_state == GsWriteBuf;
endproperty
write_write_stage_to_write_buf_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) write_write_stage_to_write_buf_p);


property write_write_stage_to_write_idle_p;
  write_stage &&
  (rounds_count == 3'd4)
|->
  ##1 ($stable(pw_wren_out)) and
  ##1
  write_idle &&
  buf_count == (($past(buf0_valid_in, 1) || ((({ 62'd0, $past(buf_count, 1)} ) > 64'd0) && (({ 62'd0, $past(buf_count, 1)} ) < 64'd3))) ? 2'((64'd1 + ({ 62'd0, $past(buf_count, 1)} ))) : 64'd0) &&
  buf_rdptr_out == (($past(buf0_valid_in, 1) || ((({ 62'd0, $past(buf_count, 1)} ) > 64'd0) && (({ 62'd0, $past(buf_count, 1)} ) < 64'd3))) ? 2'((64'd1 + ({ 62'd0, $past(buf_count, 1)} ))) : 64'd0) &&
  buf_wrptr == $past(getBufWrptr_0_i, 1) &&
  buf_wrptr_out == $past(getBufWrptr_0_i, 1) &&
  chunk_count == (($past(index_count, 1) == 2'd3) ? 4'((64'd1 + ({ 60'h0, $past(chunk_count, 1)} ))) : ({ 60'h0, $past(chunk_count, 1)} )) &&
  $stable(chunk_rand_offset) &&
  done_out == 0 &&
  intt_passthrough_out == $past(mlkem_in, 1) &&
  mem_wr_addr == ($past(shuffle_en_in, 1) ? ($past(getMemWrAddrBase_0_i, 1) + ({ 11'h0, $past(chunk_rand_offset, 1)} )) : $past(getMemWrAddrBase_0_i, 1)) &&
  mem_wr_addr_out == ($past(shuffle_en_in, 1) ? ($past(getMemWrAddrBase_0_i, 1) + ({ 11'h0, $past(chunk_rand_offset, 1)} )) : $past(getMemWrAddrBase_0_i, 1)) &&
  rounds_count == 3'd0 &&
  wr_valid_count == $past(getWrValidCount_0_i, 1) &&
  write_state == GsWriteIdle;
endproperty
write_write_stage_to_write_idle_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) write_write_stage_to_write_idle_p);


property write_write_wait_to_write_stage_p;
  write_wait &&
  (buf_count == 2'd3)
|->
  ##1 ($stable(pw_wren_out)) and
  ##1
  write_stage &&
  buf_count == (($past(buf0_valid_in, 1) || ((({ 62'd0, $past(buf_count, 1)} ) > 64'd0) && (({ 62'd0, $past(buf_count, 1)} ) < 64'd3))) ? 2'((64'd1 + ({ 62'd0, $past(buf_count, 1)} ))) : 64'd0) &&
  buf_rdptr_out == (($past(buf0_valid_in, 1) || ((({ 62'd0, $past(buf_count, 1)} ) > 64'd0) && (({ 62'd0, $past(buf_count, 1)} ) < 64'd3))) ? 2'((64'd1 + ({ 62'd0, $past(buf_count, 1)} ))) : 64'd0) &&
  buf_wrptr == $past(getBufWrptr_3_i, 1) &&
  buf_wrptr_out == $past(getBufWrptr_3_i, 1) &&
  chunk_count == { $past(random_in, 1) }[5:2] &&
  chunk_rand_offset == { $past(random_in, 1) }[5:2] &&
  done_out == ((($past(rst_rounds_in, 1) || ($past(rounds_count, 1) == 3'd4)) ? 64'd0 : (($past(write_state, 1) == GsWriteWait) ? 3'((64'd1 + ({ 61'd0, $past(rounds_count, 1)} ))) : ({ 61'd0, $past(rounds_count, 1)} ))) == 64'd4) &&
  intt_passthrough_out == (((($past(rst_rounds_in, 1) || ($past(rounds_count, 1) == 3'd4)) ? 64'd0 : (($past(write_state, 1) == GsWriteWait) ? 3'((64'd1 + ({ 61'd0, $past(rounds_count, 1)} ))) : ({ 61'd0, $past(rounds_count, 1)} ))) == 64'd0) && $past(mlkem_in, 1)) &&
  mem_wr_addr == (($past(shuffle_en_in, 1) && (({ 49'h0, $past(mem_wr_addr, 1)} ) == (64'd63 + ({ 49'h0, $past(getMemWrAddrBase_0_i, 1)} )))) ? $past(getMemWrAddrBase_0_i, 1) : $past(incr_addr_1_i, 1)) &&
  mem_wr_addr_out == (($past(shuffle_en_in, 1) && (({ 49'h0, $past(mem_wr_addr, 1)} ) == (64'd63 + ({ 49'h0, $past(getMemWrAddrBase_0_i, 1)} )))) ? $past(getMemWrAddrBase_0_i, 1) : $past(incr_addr_1_i, 1)) &&
  rounds_count == 3'((($past(rst_rounds_in, 1) || ($past(rounds_count, 1) == 3'd4)) ? 64'd0 : (($past(write_state, 1) == GsWriteWait) ? 3'((64'd1 + ({ 61'd0, $past(rounds_count, 1)} ))) : ({ 61'd0, $past(rounds_count, 1)} )))) &&
  wr_valid_count == $past(getWrValidCount_0_i, 1) &&
  write_state == GsWriteStage;
endproperty
write_write_wait_to_write_stage_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) write_write_wait_to_write_stage_p);


property write_write_wait_to_write_wait_p;
  write_wait &&
  (buf_count != 2'd3)
|->
  ##1 ($stable(pw_wren_out)) and
  ##1
  write_wait &&
  buf_count == (($past(buf0_valid_in, 1) || ((({ 62'd0, $past(buf_count, 1)} ) > 64'd0) && (({ 62'd0, $past(buf_count, 1)} ) < 64'd3))) ? 2'((64'd1 + ({ 62'd0, $past(buf_count, 1)} ))) : 64'd0) &&
  buf_rdptr_out == (($past(buf0_valid_in, 1) || ((({ 62'd0, $past(buf_count, 1)} ) > 64'd0) && (({ 62'd0, $past(buf_count, 1)} ) < 64'd3))) ? 2'((64'd1 + ({ 62'd0, $past(buf_count, 1)} ))) : 64'd0) &&
  buf_wrptr == $past(getBufWrptr_3_i, 1) &&
  buf_wrptr_out == $past(getBufWrptr_3_i, 1) &&
  chunk_count == (($past(index_count, 1) == 2'd3) ? 4'((64'd1 + ({ 60'h0, $past(chunk_count, 1)} ))) : ({ 60'h0, $past(chunk_count, 1)} )) &&
  $stable(chunk_rand_offset) &&
  done_out == ((($past(rst_rounds_in, 1) || ($past(rounds_count, 1) == 3'd4)) ? 3'd0 : $past(rounds_count, 1)) == 3'd4) &&
  intt_passthrough_out == (((($past(rst_rounds_in, 1) || ($past(rounds_count, 1) == 3'd4)) ? 3'd0 : $past(rounds_count, 1)) == 3'd0) && $past(mlkem_in, 1)) &&
  mem_wr_addr == (($past(shuffle_en_in, 1) && (({ 49'h0, $past(mem_wr_addr, 1)} ) == (64'd63 + ({ 49'h0, $past(getMemWrAddrBase_0_i, 1)} )))) ? $past(getMemWrAddrBase_0_i, 1) : $past(incr_addr_1_i, 1)) &&
  mem_wr_addr_out == (($past(shuffle_en_in, 1) && (({ 49'h0, $past(mem_wr_addr, 1)} ) == (64'd63 + ({ 49'h0, $past(getMemWrAddrBase_0_i, 1)} )))) ? $past(getMemWrAddrBase_0_i, 1) : $past(incr_addr_1_i, 1)) &&
  rounds_count == (($past(rst_rounds_in, 1) || ($past(rounds_count, 1) == 3'd4)) ? 3'd0 : $past(rounds_count, 1)) &&
  wr_valid_count == $past(getWrValidCount_0_i, 1) &&
  write_state == GsWriteWait;
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
