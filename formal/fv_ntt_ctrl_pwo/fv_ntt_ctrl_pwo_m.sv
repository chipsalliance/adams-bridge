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


import fv_ntt_ctrl_pwo_pkg::*;
import fv_ntt_ctrl_pwo_functions::*;


module fv_ntt_ctrl_pwo_m #(
  parameter LATENCY = 1
)(
  input logic rst,
  input logic clk,

  // Ports
  input logic unsigned [2:0] fv_ntt_mode_in,

  input logic fv_ntt_enable_in,

  input logic fv_butterfly_ready_in,

  input logic fv_sampler_valid_in,

  input logic fv_accumulate_in,

  input logic fv_shuffle_en_in,

  input fv_pwo_mem_addrs_type fv_pwo_mem_base_addr_in,

  input logic unsigned [5:0] fv_random_in,

  input logic unsigned [0:0] fv_mlkem_in,

  input logic unsigned [2:0] fv_opcode_out,

  input logic fv_buf_wren_out,

  input logic fv_buf_rden_out,

  input logic unsigned [1:0] fv_buf_wrptr_out,

  input logic unsigned [1:0] fv_buf_rdptr_out,

  input logic fv_mem_rd_en_out,

  input logic fv_mem_wr_en_out,

  input logic fv_buf_wr_rst_count_out,

  input logic fv_buf_rd_rst_count_out,

  input logic unsigned [14:0] fv_pw_mem_rd_addr_a_out,

  input logic unsigned [14:0] fv_pw_mem_rd_addr_b_out,

  input logic unsigned [14:0] fv_pw_mem_rd_addr_c_out,

  input logic unsigned [14:0] fv_pw_mem_wr_addr_c_out,

  input logic fv_done_out,

  input logic fv_rst_rounds_in,

  // Registers
  input logic unsigned [22+2*(LATENCY-1)-1:0] fv_buf_rdptr_reg,
  input logic unsigned [3:0] fv_chunk_count,
  input logic unsigned [44+4*(LATENCY-1)-1:0] fv_chunk_count_reg,
  input logic unsigned [3:0] fv_chunk_rand_offset,
  input logic fv_incr_twiddle_addr_reg,
  input logic unsigned [1:0] fv_index_count,
  input logic unsigned [1:0] fv_index_rand_offset,
  input logic unsigned [14:0] fv_pw_mem_rd_addr_a_reg,
  input logic unsigned [14:0] fv_pw_mem_rd_addr_b_reg,
  input logic unsigned [14:0] fv_pw_mem_rd_addr_c_reg,
  input logic unsigned [14:0] fv_pw_mem_wr_addr_c_reg,
  input logic unsigned [6:0] fv_rd_valid_count,
  input pwoReadStatesType fv_read_state,
  input logic unsigned [2:0] fv_rounds_count,
  input logic unsigned [6:0] fv_twiddle_addr_int,
  input logic unsigned [6:0] fv_twiddle_addr_reg_d2,
  input logic unsigned [6:0] fv_wr_valid_count,
  input pwoWriteStatesType fv_write_state,

  // States
  input logic state,
  input logic fv_read_idle,
  input logic fv_read_stage,
  input logic fv_read_exec,
  input logic fv_read_exec_wait,
  input logic fv_write_idle,
  input logic fv_write_stage,
  input logic fv_write_wait,
  input logic fv_write_mem
);


// SRAM_LATENCY-dependent sizing of ntt_ctrl's buf_rdptr_reg/chunk_count_reg (see
// ntt_ctrl.sv: SRAM_DELAY = SRAM_LATENCY-1, MAX_RDPTR_REG_DEPTH/MAX_CHUNK_REG_DEPTH
// grow by SRAM_DELAY). LATENCY here must be bound to the DUT's SRAM_LATENCY.
localparam SRAM_DELAY = LATENCY - 1;
localparam BUF_RDPTR_REG_SIZE            = 22 + 2*SRAM_DELAY;
localparam BUF_RDPTR_REG_SIZE_NONPAIRWM  = 14 + 2*SRAM_DELAY;
localparam CHUNK_COUNT_REG_SIZE           = 44 + 4*SRAM_DELAY;
localparam CHUNK_COUNT_REG_SIZE_NONPAIRWM = 28 + 4*SRAM_DELAY;

// Local overrides of the fv_ntt_ctrl_pwo_functions package versions (which are fixed
// at the SRAM_LATENCY=1 width). A same-named function declared in this module scope
// shadows the wildcard-imported package function, so every call site below picks these
// up automatically. Also fixes get_chunk_count_reg_next_nonpairwm's pre-existing bug:
// the package version concatenates chunk_count(4b)+chunk_count_reg[43:4](40b)=44b into
// a 28-bit return, silently truncating chunk_count out of the result entirely.
function automatic logic unsigned [BUF_RDPTR_REG_SIZE-1:0] get_buf_rdptr_reg_next_pairwm(logic unsigned [BUF_RDPTR_REG_SIZE-1:0] buf_rdptr_reg, logic unsigned [1:0] mem_rd_index_ofst);
  return { mem_rd_index_ofst, buf_rdptr_reg[BUF_RDPTR_REG_SIZE-1:2] };
endfunction

function automatic logic unsigned [BUF_RDPTR_REG_SIZE_NONPAIRWM-1:0] get_buf_rdptr_reg_next_nonpairwm(logic unsigned [BUF_RDPTR_REG_SIZE-1:0] buf_rdptr_reg, logic unsigned [1:0] mem_rd_index_ofst);
  return { mem_rd_index_ofst, buf_rdptr_reg[BUF_RDPTR_REG_SIZE_NONPAIRWM-1:2] };
endfunction

function automatic logic unsigned [CHUNK_COUNT_REG_SIZE-1:0] get_chunk_count_reg_next_pairwm(logic unsigned [CHUNK_COUNT_REG_SIZE-1:0] chunk_count_reg, logic unsigned [3:0] chunk_count);
  return { chunk_count, chunk_count_reg[CHUNK_COUNT_REG_SIZE-1:4] };
endfunction

function automatic logic unsigned [CHUNK_COUNT_REG_SIZE_NONPAIRWM-1:0] get_chunk_count_reg_next_nonpairwm(logic unsigned [CHUNK_COUNT_REG_SIZE-1:0] chunk_count_reg, logic unsigned [3:0] chunk_count);
  return { chunk_count, chunk_count_reg[CHUNK_COUNT_REG_SIZE_NONPAIRWM-1:4] };
endfunction


default clocking default_clk @(posedge clk); endclocking


logic unsigned [1:0] fv_get_mem_rd_index_ofst_0_i;
assign fv_get_mem_rd_index_ofst_0_i = get_mem_rd_index_ofst(fv_index_count, fv_index_rand_offset);

logic unsigned [14:0] fv_get_pw_addr_nxt_0_i;
assign fv_get_pw_addr_nxt_0_i = get_pw_addr_nxt(fv_pwo_mem_base_addr_in.pw_base_addr_a, fv_chunk_count, 15'd1, ({ 13'd0, fv_get_mem_rd_index_ofst_0_i} ));

logic unsigned [14:0] fv_get_pw_addr_nxt_1_i;
assign fv_get_pw_addr_nxt_1_i = get_pw_addr_nxt(fv_pwo_mem_base_addr_in.pw_base_addr_b, fv_chunk_count, 15'd1, ({ 13'd0, fv_get_mem_rd_index_ofst_0_i} ));

logic unsigned [14:0] fv_get_pw_addr_nxt_2_i;
assign fv_get_pw_addr_nxt_2_i = get_pw_addr_nxt(fv_pwo_mem_base_addr_in.pw_base_addr_c, fv_chunk_count, 15'd1, ({ 13'd0, fv_get_mem_rd_index_ofst_0_i} ));

logic unsigned [14:0] fv_get_pw_addr_rst_0_i;
assign fv_get_pw_addr_rst_0_i = get_pw_addr_rst(fv_shuffle_en_in, fv_chunk_rand_offset, fv_pwo_mem_base_addr_in.pw_base_addr_a);

logic unsigned [14:0] fv_get_pw_addr_incr_abc_wr_0_i;
assign fv_get_pw_addr_incr_abc_wr_0_i = get_pw_addr_incr_abc_wr(fv_shuffle_en_in, fv_get_pw_addr_nxt_0_i, fv_pw_mem_rd_addr_a_reg, 15'd1);

logic unsigned [14:0] fv_get_pw_addr_abc_wr_0_i;
assign fv_get_pw_addr_abc_wr_0_i = get_pw_addr_abc_wr(((fv_write_state == fv_pwo_write_idle_type) || (fv_write_state == fv_pwo_write_stage_type)), 0, fv_get_pw_addr_rst_0_i, fv_get_pw_addr_incr_abc_wr_0_i, fv_pw_mem_rd_addr_a_reg);

logic unsigned [14:0] fv_get_pw_addr_rst_1_i;
assign fv_get_pw_addr_rst_1_i = get_pw_addr_rst(fv_shuffle_en_in, fv_chunk_rand_offset, fv_pwo_mem_base_addr_in.pw_base_addr_b);

logic unsigned [14:0] fv_get_pw_addr_incr_abc_wr_1_i;
assign fv_get_pw_addr_incr_abc_wr_1_i = get_pw_addr_incr_abc_wr(fv_shuffle_en_in, fv_get_pw_addr_nxt_1_i, fv_pw_mem_rd_addr_b_reg, 15'd1);

logic unsigned [14:0] fv_get_pw_addr_abc_wr_1_i;
assign fv_get_pw_addr_abc_wr_1_i = get_pw_addr_abc_wr(((fv_write_state == fv_pwo_write_idle_type) || (fv_write_state == fv_pwo_write_stage_type)), 0, fv_get_pw_addr_rst_1_i, fv_get_pw_addr_incr_abc_wr_1_i, fv_pw_mem_rd_addr_b_reg);

logic unsigned [14:0] fv_get_pw_addr_rst_2_i;
assign fv_get_pw_addr_rst_2_i = get_pw_addr_rst(fv_shuffle_en_in, fv_chunk_rand_offset, fv_pwo_mem_base_addr_in.pw_base_addr_c);

logic unsigned [14:0] fv_get_pw_addr_crd_0_i;
assign fv_get_pw_addr_crd_0_i = get_pw_addr_crd(fv_shuffle_en_in, ((fv_ntt_mode_in == 3'd2) || (!(fv_mlkem_in == 1'd0) && (fv_ntt_mode_in == 3'd5))), fv_accumulate_in, ((fv_write_state == fv_pwo_write_idle_type) || (fv_write_state == fv_pwo_write_stage_type)), 0, fv_get_pw_addr_rst_2_i, fv_get_pw_addr_nxt_2_i, fv_pw_mem_rd_addr_c_reg, 15'd1);

logic unsigned [BUF_RDPTR_REG_SIZE-1:0] fv_get_buf_rdptr_reg_next_pairwm_0_i;
assign fv_get_buf_rdptr_reg_next_pairwm_0_i = get_buf_rdptr_reg_next_pairwm(fv_buf_rdptr_reg, fv_get_mem_rd_index_ofst_0_i);

logic unsigned [BUF_RDPTR_REG_SIZE_NONPAIRWM-1:0] fv_get_buf_rdptr_reg_next_nonpairwm_0_i;
assign fv_get_buf_rdptr_reg_next_nonpairwm_0_i = get_buf_rdptr_reg_next_nonpairwm(fv_buf_rdptr_reg, fv_get_mem_rd_index_ofst_0_i);

fv_unsigned_7_8_type fv_get_twiddle_rand_offsets_0_i;
assign fv_get_twiddle_rand_offsets_0_i = get_twiddle_rand_offsets(fv_chunk_count_reg, fv_chunk_count, 2'd0, ((fv_mlkem_in != 1'd0) && (fv_ntt_mode_in == 3'd5)));

logic unsigned [CHUNK_COUNT_REG_SIZE-1:0] fv_get_chunk_count_reg_next_pairwm_0_i;
assign fv_get_chunk_count_reg_next_pairwm_0_i = get_chunk_count_reg_next_pairwm(fv_chunk_count_reg, fv_chunk_count);

logic unsigned [CHUNK_COUNT_REG_SIZE_NONPAIRWM-1:0] fv_get_chunk_count_reg_next_nonpairwm_0_i;
assign fv_get_chunk_count_reg_next_nonpairwm_0_i = get_chunk_count_reg_next_nonpairwm(fv_chunk_count_reg, fv_chunk_count);

fv_unsigned_7_8_type fv_twiddle_offset_array_0_i;
assign fv_twiddle_offset_array_0_i = '{
  0: ((!(fv_mlkem_in == 1'd0) && (fv_ntt_mode_in == 3'd5)) ? 7'd21 : 7'd0),
  1: 7'd64,
  2: 7'd80,
  3: 7'd84,
  4: 7'd0,
  5: 7'd0,
  6: 7'd0,
  7: 7'd0
};

logic unsigned [6:0] fv_get_twiddle_incr_addr_0_i;
assign fv_get_twiddle_incr_addr_0_i = get_twiddle_incr_addr(fv_shuffle_en_in, fv_rounds_count, fv_get_twiddle_rand_offsets_0_i, '{ 0: 7'd63, 1: 7'd15, 2: 7'd3, 3: 7'd0, 4: 7'd0, 5: 7'd0, 6: 7'd0, 7: 7'd0 }, fv_twiddle_addr_int);

logic unsigned [6:0] fv_get_twiddle_addr_reg_0_i;
assign fv_get_twiddle_addr_reg_0_i = get_twiddle_addr_reg(fv_incr_twiddle_addr_reg, ((fv_read_state == fv_pwo_read_idle_type) || ((fv_read_state == fv_pwo_read_stage_type) && !fv_butterfly_ready_in)), fv_get_twiddle_incr_addr_0_i, fv_twiddle_addr_int);

logic unsigned [14:0] fv_get_pw_addr_abc_wr_2_i;
assign fv_get_pw_addr_abc_wr_2_i = get_pw_addr_abc_wr(((fv_write_state == fv_pwo_write_idle_type) || (fv_write_state == fv_pwo_write_stage_type)), fv_sampler_valid_in, fv_get_pw_addr_rst_0_i, fv_get_pw_addr_incr_abc_wr_0_i, fv_pw_mem_rd_addr_a_reg);

logic unsigned [14:0] fv_get_pw_addr_abc_wr_3_i;
assign fv_get_pw_addr_abc_wr_3_i = get_pw_addr_abc_wr(((fv_write_state == fv_pwo_write_idle_type) || (fv_write_state == fv_pwo_write_stage_type)), fv_sampler_valid_in, fv_get_pw_addr_rst_1_i, fv_get_pw_addr_incr_abc_wr_1_i, fv_pw_mem_rd_addr_b_reg);

logic unsigned [14:0] fv_get_pw_addr_crd_1_i;
assign fv_get_pw_addr_crd_1_i = get_pw_addr_crd(fv_shuffle_en_in, ((fv_ntt_mode_in == 3'd2) || (!(fv_mlkem_in == 1'd0) && (fv_ntt_mode_in == 3'd5))), fv_accumulate_in, ((fv_write_state == fv_pwo_write_idle_type) || (fv_write_state == fv_pwo_write_stage_type)), fv_sampler_valid_in, fv_get_pw_addr_rst_2_i, fv_get_pw_addr_nxt_2_i, fv_pw_mem_rd_addr_c_reg, 15'd1);

logic unsigned [14:0] fv_get_pw_addr_abc_wr_4_i;
assign fv_get_pw_addr_abc_wr_4_i = get_pw_addr_abc_wr(((fv_write_state == fv_pwo_write_idle_type) || (fv_write_state == fv_pwo_write_stage_type)), (fv_sampler_valid_in && ((fv_read_state == fv_pwo_read_exec_type) || (fv_read_state == fv_pwo_read_exec_wait_type))), fv_get_pw_addr_rst_0_i, fv_get_pw_addr_incr_abc_wr_0_i, fv_pw_mem_rd_addr_a_reg);

logic unsigned [14:0] fv_get_pw_addr_abc_wr_5_i;
assign fv_get_pw_addr_abc_wr_5_i = get_pw_addr_abc_wr(((fv_write_state == fv_pwo_write_idle_type) || (fv_write_state == fv_pwo_write_stage_type)), (fv_sampler_valid_in && ((fv_read_state == fv_pwo_read_exec_type) || (fv_read_state == fv_pwo_read_exec_wait_type))), fv_get_pw_addr_rst_1_i, fv_get_pw_addr_incr_abc_wr_1_i, fv_pw_mem_rd_addr_b_reg);

logic unsigned [14:0] fv_get_pw_addr_crd_2_i;
assign fv_get_pw_addr_crd_2_i = get_pw_addr_crd(fv_shuffle_en_in, ((fv_ntt_mode_in == 3'd2) || (!(fv_mlkem_in == 1'd0) && (fv_ntt_mode_in == 3'd5))), fv_accumulate_in, ((fv_write_state == fv_pwo_write_idle_type) || (fv_write_state == fv_pwo_write_stage_type)), (fv_sampler_valid_in && ((fv_read_state == fv_pwo_read_exec_type) || (fv_read_state == fv_pwo_read_exec_wait_type))), fv_get_pw_addr_rst_2_i, fv_get_pw_addr_nxt_2_i, fv_pw_mem_rd_addr_c_reg, 15'd1);

logic unsigned [3:0] fv_get_chunk_rand_offset_from_random_0_i;
assign fv_get_chunk_rand_offset_from_random_0_i = get_chunk_rand_offset_from_random(fv_random_in);

logic unsigned [1:0] fv_get_index_rand_offset_from_random_0_i;
assign fv_get_index_rand_offset_from_random_0_i = get_index_rand_offset_from_random(fv_random_in);

logic unsigned [14:0] fv_get_pw_addr_wr_nxt_0_i;
assign fv_get_pw_addr_wr_nxt_0_i = get_pw_addr_wr_nxt(fv_pwo_mem_base_addr_in.pw_base_addr_c, fv_chunk_count_reg, 15'd1, fv_buf_rdptr_reg, fv_accumulate_in, fv_ntt_mode_in);

logic unsigned [14:0] fv_get_pw_addr_cwr_0_i;
assign fv_get_pw_addr_cwr_0_i = get_pw_addr_cwr(1, (((fv_write_state == fv_pwo_write_mem_type) && fv_butterfly_ready_in) || ((fv_write_state == fv_pwo_write_wait_type) && (fv_butterfly_ready_in || fv_shuffle_en_in))), fv_shuffle_en_in, fv_chunk_rand_offset, fv_pwo_mem_base_addr_in.pw_base_addr_c, fv_get_pw_addr_wr_nxt_0_i, fv_pw_mem_wr_addr_c_reg);

logic unsigned [14:0] fv_get_pw_addr_cwr_1_i;
assign fv_get_pw_addr_cwr_1_i = get_pw_addr_cwr(0, (((fv_write_state == fv_pwo_write_mem_type) && fv_butterfly_ready_in) || ((fv_write_state == fv_pwo_write_wait_type) && (fv_butterfly_ready_in || fv_shuffle_en_in))), fv_shuffle_en_in, fv_chunk_rand_offset, fv_pwo_mem_base_addr_in.pw_base_addr_c, fv_get_pw_addr_wr_nxt_0_i, fv_pw_mem_wr_addr_c_reg);


sequence reset_sequence;
  $past(!ntt_ctrl.reset_n || ntt_ctrl.zeroize);
endsequence


property commons_reset_p;
  reset_sequence
|->
  state &&
  fv_buf_rd_rst_count_out == 1 &&
  fv_buf_rden_out == 0 &&
  fv_buf_rdptr_out == 2'd0 &&
  fv_buf_wr_rst_count_out == 1 &&
  fv_buf_wren_out == 0 &&
  fv_buf_wrptr_out == 2'd0 &&
  fv_mem_rd_en_out == 0 &&
  fv_mem_wr_en_out == 0 &&
  fv_opcode_out == 3'd0;
endproperty
a_commons_reset: assert property (commons_reset_p);


property read_reset_p;
  reset_sequence
|->
  fv_read_idle &&
  fv_buf_rdptr_reg == '0 &&
  fv_chunk_count_reg == '0 &&
  fv_incr_twiddle_addr_reg == 0 &&
  fv_pw_mem_rd_addr_a_out == 15'd0 &&
  fv_pw_mem_rd_addr_a_reg == 15'd0 &&
  fv_pw_mem_rd_addr_b_out == 15'd0 &&
  fv_pw_mem_rd_addr_b_reg == 15'd0 &&
  fv_pw_mem_rd_addr_c_out == 15'd0 &&
  fv_pw_mem_rd_addr_c_reg == 15'd0 &&
  fv_rd_valid_count == 7'd0 &&
  fv_read_state == fv_pwo_read_idle_type &&
  fv_twiddle_addr_int == 7'd0 &&
  fv_twiddle_addr_reg_d2 == 7'd0;
endproperty
a_read_reset: assert property (read_reset_p);


property write_reset_p;
  reset_sequence
|->
  fv_write_idle &&
  fv_chunk_count == 4'd0 &&
  fv_chunk_rand_offset == 4'd0 &&
  fv_done_out == 0 &&
  fv_index_count == 2'd0 &&
  fv_index_rand_offset == 2'd0 &&
  fv_pw_mem_wr_addr_c_out == 15'd0 &&
  fv_pw_mem_wr_addr_c_reg == 15'd0 &&
  fv_rounds_count == 3'd0 &&
  fv_wr_valid_count == 7'd0 &&
  fv_write_state == fv_pwo_write_idle_type;
endproperty
a_write_reset: assert property (write_reset_p);


property commons_state_to_state_p;
  state
|->
  ##1 ($stable(fv_buf_rd_rst_count_out) &&
    $stable(fv_buf_rden_out) &&
    $stable(fv_buf_rdptr_out) &&
    $stable(fv_buf_wr_rst_count_out) &&
    $stable(fv_buf_wren_out) &&
    $stable(fv_buf_wrptr_out) &&
    $stable(fv_mem_rd_en_out) &&
    $stable(fv_mem_wr_en_out)) and
  ##1
  state &&
  fv_opcode_out == $past(fv_ntt_mode_in, 1);
endproperty
a_commons_state_to_state: assert property (disable iff(!rst || ntt_ctrl.zeroize) commons_state_to_state_p);


property read_fv_read_exec_to_fv_read_exec_p;
  fv_read_exec &&
  (fv_sampler_valid_in || (({ 57'd0, fv_rd_valid_count} ) >= 64'h40)) &&
  (fv_rd_valid_count < 7'h3F)
|->
  ##1
  fv_read_exec &&
  fv_buf_rdptr_reg == ((($past(fv_mlkem_in, 1) != 1'd0) && ($past(fv_ntt_mode_in, 1) == 3'd5)) ? $past(fv_get_buf_rdptr_reg_next_pairwm_0_i, 1) : ({ 8'd0, $past(fv_get_buf_rdptr_reg_next_nonpairwm_0_i, 1)} )) &&
  fv_chunk_count_reg == ((($past(fv_mlkem_in, 1) != 1'd0) && ($past(fv_ntt_mode_in, 1) == 3'd5)) ? $past(fv_get_chunk_count_reg_next_pairwm_0_i, 1) : ({ 16'd0, $past(fv_get_chunk_count_reg_next_nonpairwm_0_i, 1)} )) &&
  fv_incr_twiddle_addr_reg == ((((($past(fv_read_state, 1) == fv_pwo_read_exec_type) || ($past(fv_read_state, 1) == fv_pwo_read_exec_wait_type)) && ($past(fv_mlkem_in, 1) != 1'd0)) && ($past(fv_ntt_mode_in, 1) == 3'd5)) && $past(fv_sampler_valid_in, 1)) &&
  fv_pw_mem_rd_addr_a_out == $past(fv_get_pw_addr_abc_wr_2_i, 1) &&
  fv_pw_mem_rd_addr_a_reg == $past(fv_get_pw_addr_abc_wr_2_i, 1) &&
  fv_pw_mem_rd_addr_b_out == $past(fv_get_pw_addr_abc_wr_3_i, 1) &&
  fv_pw_mem_rd_addr_b_reg == $past(fv_get_pw_addr_abc_wr_3_i, 1) &&
  fv_pw_mem_rd_addr_c_out == $past(fv_get_pw_addr_crd_1_i, 1) &&
  fv_pw_mem_rd_addr_c_reg == $past(fv_get_pw_addr_crd_1_i, 1) &&
  fv_rd_valid_count == ((($past(fv_read_state, 1) == fv_pwo_read_idle_type) || ($past(fv_read_state, 1) == fv_pwo_read_stage_type)) ? 7'd0 : ($past(fv_sampler_valid_in, 1) ? (7'd1 + $past(fv_rd_valid_count, 1)) : $past(fv_rd_valid_count, 1))) &&
  fv_read_state == fv_pwo_read_exec_type &&
  fv_twiddle_addr_int == $past(fv_get_twiddle_addr_reg_0_i, 1) &&
  fv_twiddle_addr_reg_d2 == ($past(fv_shuffle_en_in, 1) ? ((($past(fv_shuffle_en_in, 1) && ($past(fv_mlkem_in, 1) != 1'd0)) && ($past(fv_ntt_mode_in, 1) == 3'd5)) ? (($past(fv_get_twiddle_rand_offsets_0_i[fv_rounds_count], 1) + ({ 5'd0, 2'(($past(fv_index_count, 1) + $past(fv_index_rand_offset, 1)))} )) + $past(fv_twiddle_offset_array_0_i[fv_rounds_count], 1)) : ($past(fv_get_twiddle_rand_offsets_0_i[fv_rounds_count], 1) + $past(fv_twiddle_offset_array_0_i[fv_rounds_count], 1))) : ($past(fv_twiddle_addr_int, 1) + $past(fv_twiddle_offset_array_0_i[fv_rounds_count], 1)));
endproperty
a_read_fv_read_exec_to_fv_read_exec: assert property (disable iff(!rst || ntt_ctrl.zeroize) read_fv_read_exec_to_fv_read_exec_p);


property read_fv_read_exec_to_fv_read_exec_wait_p;
  fv_read_exec &&
  !fv_sampler_valid_in &&
  (({ 57'd0, fv_rd_valid_count} ) < 64'h40)
|->
  ##1
  fv_read_exec_wait &&
  fv_buf_rdptr_reg == (($past(fv_sampler_valid_in, 1) || $past(fv_butterfly_ready_in, 1)) ? ((($past(fv_mlkem_in, 1) != 1'd0) && ($past(fv_ntt_mode_in, 1) == 3'd5)) ? $past(fv_get_buf_rdptr_reg_next_pairwm_0_i, 1) : ({ 8'd0, $past(fv_get_buf_rdptr_reg_next_nonpairwm_0_i, 1)} )) : '0) &&
  fv_chunk_count_reg == (($past(fv_sampler_valid_in, 1) || $past(fv_butterfly_ready_in, 1)) ? ((($past(fv_mlkem_in, 1) != 1'd0) && ($past(fv_ntt_mode_in, 1) == 3'd5)) ? $past(fv_get_chunk_count_reg_next_pairwm_0_i, 1) : ({ 16'd0, $past(fv_get_chunk_count_reg_next_nonpairwm_0_i, 1)} )) : $past(fv_chunk_count_reg, 1)) &&
  fv_incr_twiddle_addr_reg == ((((($past(fv_read_state, 1) == fv_pwo_read_exec_type) || ($past(fv_read_state, 1) == fv_pwo_read_exec_wait_type)) && ($past(fv_mlkem_in, 1) != 1'd0)) && ($past(fv_ntt_mode_in, 1) == 3'd5)) && $past(fv_sampler_valid_in, 1)) &&
  fv_pw_mem_rd_addr_a_out == $past(fv_get_pw_addr_abc_wr_2_i, 1) &&
  fv_pw_mem_rd_addr_a_reg == $past(fv_get_pw_addr_abc_wr_2_i, 1) &&
  fv_pw_mem_rd_addr_b_out == $past(fv_get_pw_addr_abc_wr_3_i, 1) &&
  fv_pw_mem_rd_addr_b_reg == $past(fv_get_pw_addr_abc_wr_3_i, 1) &&
  fv_pw_mem_rd_addr_c_out == $past(fv_get_pw_addr_crd_1_i, 1) &&
  fv_pw_mem_rd_addr_c_reg == $past(fv_get_pw_addr_crd_1_i, 1) &&
  fv_rd_valid_count == ((($past(fv_read_state, 1) == fv_pwo_read_idle_type) || ($past(fv_read_state, 1) == fv_pwo_read_stage_type)) ? 7'd0 : ($past(fv_sampler_valid_in, 1) ? (7'd1 + $past(fv_rd_valid_count, 1)) : $past(fv_rd_valid_count, 1))) &&
  fv_read_state == fv_pwo_read_exec_wait_type &&
  fv_twiddle_addr_int == $past(fv_get_twiddle_addr_reg_0_i, 1) &&
  fv_twiddle_addr_reg_d2 == ($past(fv_shuffle_en_in, 1) ? ((($past(fv_shuffle_en_in, 1) && ($past(fv_mlkem_in, 1) != 1'd0)) && ($past(fv_ntt_mode_in, 1) == 3'd5)) ? (($past(fv_get_twiddle_rand_offsets_0_i[fv_rounds_count], 1) + ({ 5'd0, 2'(($past(fv_index_count, 1) + $past(fv_index_rand_offset, 1)))} )) + $past(fv_twiddle_offset_array_0_i[fv_rounds_count], 1)) : ($past(fv_get_twiddle_rand_offsets_0_i[fv_rounds_count], 1) + $past(fv_twiddle_offset_array_0_i[fv_rounds_count], 1))) : ($past(fv_twiddle_addr_int, 1) + $past(fv_twiddle_offset_array_0_i[fv_rounds_count], 1)));
endproperty
a_read_fv_read_exec_to_fv_read_exec_wait: assert property (disable iff(!rst || ntt_ctrl.zeroize) read_fv_read_exec_to_fv_read_exec_wait_p);


property read_fv_read_exec_to_fv_read_stage_p;
  fv_read_exec &&
  (fv_sampler_valid_in || (({ 57'd0, fv_rd_valid_count} ) >= 64'h40)) &&
  (fv_rd_valid_count >= 7'h3F)
|->
  ##1
  fv_read_stage &&
  fv_buf_rdptr_reg == (($past(fv_sampler_valid_in, 1) || $past(fv_butterfly_ready_in, 1)) ? ((($past(fv_mlkem_in, 1) != 1'd0) && ($past(fv_ntt_mode_in, 1) == 3'd5)) ? $past(fv_get_buf_rdptr_reg_next_pairwm_0_i, 1) : ({ 8'd0, $past(fv_get_buf_rdptr_reg_next_nonpairwm_0_i, 1)} )) : '0) &&
  fv_chunk_count_reg == (($past(fv_sampler_valid_in, 1) || $past(fv_butterfly_ready_in, 1)) ? ((($past(fv_mlkem_in, 1) != 1'd0) && ($past(fv_ntt_mode_in, 1) == 3'd5)) ? $past(fv_get_chunk_count_reg_next_pairwm_0_i, 1) : ({ 16'd0, $past(fv_get_chunk_count_reg_next_nonpairwm_0_i, 1)} )) : $past(fv_chunk_count_reg, 1)) &&
  fv_incr_twiddle_addr_reg == ((((($past(fv_read_state, 1) == fv_pwo_read_exec_type) || ($past(fv_read_state, 1) == fv_pwo_read_exec_wait_type)) && ($past(fv_mlkem_in, 1) != 1'd0)) && ($past(fv_ntt_mode_in, 1) == 3'd5)) && $past(fv_sampler_valid_in, 1)) &&
  fv_pw_mem_rd_addr_a_out == $past(fv_get_pw_addr_abc_wr_2_i, 1) &&
  fv_pw_mem_rd_addr_a_reg == $past(fv_get_pw_addr_abc_wr_2_i, 1) &&
  fv_pw_mem_rd_addr_b_out == $past(fv_get_pw_addr_abc_wr_3_i, 1) &&
  fv_pw_mem_rd_addr_b_reg == $past(fv_get_pw_addr_abc_wr_3_i, 1) &&
  fv_pw_mem_rd_addr_c_out == $past(fv_get_pw_addr_crd_1_i, 1) &&
  fv_pw_mem_rd_addr_c_reg == $past(fv_get_pw_addr_crd_1_i, 1) &&
  fv_rd_valid_count == ((($past(fv_read_state, 1) == fv_pwo_read_idle_type) || ($past(fv_read_state, 1) == fv_pwo_read_stage_type)) ? 7'd0 : ($past(fv_sampler_valid_in, 1) ? (7'd1 + $past(fv_rd_valid_count, 1)) : $past(fv_rd_valid_count, 1))) &&
  fv_read_state == fv_pwo_read_stage_type &&
  fv_twiddle_addr_int == $past(fv_get_twiddle_addr_reg_0_i, 1) &&
  fv_twiddle_addr_reg_d2 == ($past(fv_shuffle_en_in, 1) ? ((($past(fv_shuffle_en_in, 1) && ($past(fv_mlkem_in, 1) != 1'd0)) && ($past(fv_ntt_mode_in, 1) == 3'd5)) ? (($past(fv_get_twiddle_rand_offsets_0_i[fv_rounds_count], 1) + ({ 5'd0, 2'(($past(fv_index_count, 1) + $past(fv_index_rand_offset, 1)))} )) + $past(fv_twiddle_offset_array_0_i[fv_rounds_count], 1)) : ($past(fv_get_twiddle_rand_offsets_0_i[fv_rounds_count], 1) + $past(fv_twiddle_offset_array_0_i[fv_rounds_count], 1))) : ($past(fv_twiddle_addr_int, 1) + $past(fv_twiddle_offset_array_0_i[fv_rounds_count], 1)));
endproperty
a_read_fv_read_exec_to_fv_read_stage: assert property (disable iff(!rst || ntt_ctrl.zeroize) read_fv_read_exec_to_fv_read_stage_p);


property read_fv_read_exec_wait_to_fv_read_exec_p;
  fv_read_exec_wait &&
  fv_sampler_valid_in
  //(({ 57'd0, fv_rd_valid_count} ) < 64'h40)
|->
  ##1
  fv_read_exec &&
  fv_buf_rdptr_reg == ((($past(fv_sampler_valid_in, 1) && (($past(fv_read_state, 1) == fv_pwo_read_exec_type) || ($past(fv_read_state, 1) == fv_pwo_read_exec_wait_type))) || $past(fv_butterfly_ready_in, 1)) ? ((($past(fv_mlkem_in, 1) != 1'd0) && ($past(fv_ntt_mode_in, 1) == 3'd5)) ? $past(fv_get_buf_rdptr_reg_next_pairwm_0_i, 1) : ({ 8'd0, $past(fv_get_buf_rdptr_reg_next_nonpairwm_0_i, 1)} )) : '0) &&
  fv_chunk_count_reg == ((($past(fv_sampler_valid_in, 1) && (($past(fv_read_state, 1) == fv_pwo_read_exec_type) || ($past(fv_read_state, 1) == fv_pwo_read_exec_wait_type))) || $past(fv_butterfly_ready_in, 1)) ? ((($past(fv_mlkem_in, 1) != 1'd0) && ($past(fv_ntt_mode_in, 1) == 3'd5)) ? $past(fv_get_chunk_count_reg_next_pairwm_0_i, 1) : ({ 16'd0, $past(fv_get_chunk_count_reg_next_nonpairwm_0_i, 1)} )) : $past(fv_chunk_count_reg, 1)) &&
  fv_incr_twiddle_addr_reg == ((((($past(fv_read_state, 1) == fv_pwo_read_exec_type) || ($past(fv_read_state, 1) == fv_pwo_read_exec_wait_type)) && ($past(fv_mlkem_in, 1) != 1'd0)) && ($past(fv_ntt_mode_in, 1) == 3'd5)) && $past(fv_sampler_valid_in, 1)) &&
  fv_pw_mem_rd_addr_a_out == $past(fv_get_pw_addr_abc_wr_4_i, 1) &&
  fv_pw_mem_rd_addr_a_reg == $past(fv_get_pw_addr_abc_wr_4_i, 1) &&
  fv_pw_mem_rd_addr_b_out == $past(fv_get_pw_addr_abc_wr_5_i, 1) &&
  fv_pw_mem_rd_addr_b_reg == $past(fv_get_pw_addr_abc_wr_5_i, 1) &&
  fv_pw_mem_rd_addr_c_out == $past(fv_get_pw_addr_crd_2_i, 1) &&
  fv_pw_mem_rd_addr_c_reg == $past(fv_get_pw_addr_crd_2_i, 1) &&
  fv_rd_valid_count == ((($past(fv_read_state, 1) == fv_pwo_read_idle_type) || ($past(fv_read_state, 1) == fv_pwo_read_stage_type)) ? 7'd0 : ($past(fv_sampler_valid_in, 1) ? (7'd1 + $past(fv_rd_valid_count, 1)) : $past(fv_rd_valid_count, 1))) &&
  fv_read_state == fv_pwo_read_exec_type &&
  fv_twiddle_addr_int == $past(fv_get_twiddle_addr_reg_0_i, 1) &&
  fv_twiddle_addr_reg_d2 == ($past(fv_shuffle_en_in, 1) ? ((($past(fv_shuffle_en_in, 1) && ($past(fv_mlkem_in, 1) != 1'd0)) && ($past(fv_ntt_mode_in, 1) == 3'd5)) ? (($past(fv_get_twiddle_rand_offsets_0_i[fv_rounds_count], 1) + ({ 5'd0, 2'(($past(fv_index_count, 1) + $past(fv_index_rand_offset, 1)))} )) + $past(fv_twiddle_offset_array_0_i[fv_rounds_count], 1)) : ($past(fv_get_twiddle_rand_offsets_0_i[fv_rounds_count], 1) + $past(fv_twiddle_offset_array_0_i[fv_rounds_count], 1))) : ($past(fv_twiddle_addr_int, 1) + $past(fv_twiddle_offset_array_0_i[fv_rounds_count], 1)));
endproperty
a_read_fv_read_exec_wait_to_fv_read_exec: assert property (disable iff(!rst || ntt_ctrl.zeroize) read_fv_read_exec_wait_to_fv_read_exec_p);


property read_fv_read_exec_wait_to_fv_read_exec_wait_p;
  fv_read_exec_wait &&
  !(fv_sampler_valid_in && (({ 57'd0, fv_rd_valid_count} ) < 64'h40))
|->
  ##1
  fv_read_exec_wait &&
  fv_buf_rdptr_reg == ((($past(fv_sampler_valid_in, 1) && (($past(fv_read_state, 1) == fv_pwo_read_exec_type) || ($past(fv_read_state, 1) == fv_pwo_read_exec_wait_type))) || $past(fv_butterfly_ready_in, 1)) ? ((($past(fv_mlkem_in, 1) != 1'd0) && ($past(fv_ntt_mode_in, 1) == 3'd5)) ? $past(fv_get_buf_rdptr_reg_next_pairwm_0_i, 1) : ({ 8'd0, $past(fv_get_buf_rdptr_reg_next_nonpairwm_0_i, 1)} )) : '0) &&
  fv_chunk_count_reg == ((($past(fv_sampler_valid_in, 1) && (($past(fv_read_state, 1) == fv_pwo_read_exec_type) || ($past(fv_read_state, 1) == fv_pwo_read_exec_wait_type))) || $past(fv_butterfly_ready_in, 1)) ? ((($past(fv_mlkem_in, 1) != 1'd0) && ($past(fv_ntt_mode_in, 1) == 3'd5)) ? $past(fv_get_chunk_count_reg_next_pairwm_0_i, 1) : ({ 16'd0, $past(fv_get_chunk_count_reg_next_nonpairwm_0_i, 1)} )) : $past(fv_chunk_count_reg, 1)) &&
  fv_incr_twiddle_addr_reg == ((((($past(fv_read_state, 1) == fv_pwo_read_exec_type) || ($past(fv_read_state, 1) == fv_pwo_read_exec_wait_type)) && ($past(fv_mlkem_in, 1) != 1'd0)) && ($past(fv_ntt_mode_in, 1) == 3'd5)) && $past(fv_sampler_valid_in, 1)) &&
  fv_pw_mem_rd_addr_a_out == $past(fv_get_pw_addr_abc_wr_4_i, 1) &&
  fv_pw_mem_rd_addr_a_reg == $past(fv_get_pw_addr_abc_wr_4_i, 1) &&
  fv_pw_mem_rd_addr_b_out == $past(fv_get_pw_addr_abc_wr_5_i, 1) &&
  fv_pw_mem_rd_addr_b_reg == $past(fv_get_pw_addr_abc_wr_5_i, 1) &&
  fv_pw_mem_rd_addr_c_out == $past(fv_get_pw_addr_crd_2_i, 1) &&
  fv_pw_mem_rd_addr_c_reg == $past(fv_get_pw_addr_crd_2_i, 1) &&
  fv_rd_valid_count == ((($past(fv_read_state, 1) == fv_pwo_read_idle_type) || ($past(fv_read_state, 1) == fv_pwo_read_stage_type)) ? 7'd0 : ($past(fv_sampler_valid_in, 1) ? (7'd1 + $past(fv_rd_valid_count, 1)) : $past(fv_rd_valid_count, 1))) &&
  fv_read_state == fv_pwo_read_exec_wait_type &&
  fv_twiddle_addr_int == $past(fv_get_twiddle_addr_reg_0_i, 1) &&
  fv_twiddle_addr_reg_d2 == ($past(fv_shuffle_en_in, 1) ? ((($past(fv_shuffle_en_in, 1) && ($past(fv_mlkem_in, 1) != 1'd0)) && ($past(fv_ntt_mode_in, 1) == 3'd5)) ? (($past(fv_get_twiddle_rand_offsets_0_i[fv_rounds_count], 1) + ({ 5'd0, 2'(($past(fv_index_count, 1) + $past(fv_index_rand_offset, 1)))} )) + $past(fv_twiddle_offset_array_0_i[fv_rounds_count], 1)) : ($past(fv_get_twiddle_rand_offsets_0_i[fv_rounds_count], 1) + $past(fv_twiddle_offset_array_0_i[fv_rounds_count], 1))) : ($past(fv_twiddle_addr_int, 1) + $past(fv_twiddle_offset_array_0_i[fv_rounds_count], 1)));
endproperty
a_read_fv_read_exec_wait_to_fv_read_exec_wait: assert property (disable iff(!rst || ntt_ctrl.zeroize) read_fv_read_exec_wait_to_fv_read_exec_wait_p);


property read_fv_read_idle_to_fv_read_idle_p;
  fv_read_idle &&
  !fv_ntt_enable_in
|->
  ##1
  fv_read_idle &&
  fv_buf_rdptr_reg == ($past(fv_butterfly_ready_in, 1) ? ((($past(fv_mlkem_in, 1) != 1'd0) && ($past(fv_ntt_mode_in, 1) == 3'd5)) ? $past(fv_get_buf_rdptr_reg_next_pairwm_0_i, 1) : ({ 8'd0, $past(fv_get_buf_rdptr_reg_next_nonpairwm_0_i, 1)} )) : '0) &&
  fv_chunk_count_reg == ($past(fv_butterfly_ready_in, 1) ? ((($past(fv_mlkem_in, 1) != 1'd0) && ($past(fv_ntt_mode_in, 1) == 3'd5)) ? $past(fv_get_chunk_count_reg_next_pairwm_0_i, 1) : ({ 16'd0, $past(fv_get_chunk_count_reg_next_nonpairwm_0_i, 1)} )) : $past(fv_chunk_count_reg, 1)) &&
  fv_incr_twiddle_addr_reg == ((((($past(fv_read_state, 1) == fv_pwo_read_exec_type) || ($past(fv_read_state, 1) == fv_pwo_read_exec_wait_type)) && ($past(fv_mlkem_in, 1) != 1'd0)) && ($past(fv_ntt_mode_in, 1) == 3'd5)) && $past(fv_sampler_valid_in, 1)) &&
  fv_pw_mem_rd_addr_a_out == $past(fv_get_pw_addr_abc_wr_0_i, 1) &&
  fv_pw_mem_rd_addr_a_reg == $past(fv_get_pw_addr_abc_wr_0_i, 1) &&
  fv_pw_mem_rd_addr_b_out == $past(fv_get_pw_addr_abc_wr_1_i, 1) &&
  fv_pw_mem_rd_addr_b_reg == $past(fv_get_pw_addr_abc_wr_1_i, 1) &&
  fv_pw_mem_rd_addr_c_out == $past(fv_get_pw_addr_crd_0_i, 1) &&
  fv_pw_mem_rd_addr_c_reg == $past(fv_get_pw_addr_crd_0_i, 1) &&
  fv_rd_valid_count == ((($past(fv_read_state, 1) == fv_pwo_read_idle_type) || ($past(fv_read_state, 1) == fv_pwo_read_stage_type)) ? 7'd0 : ($past(fv_sampler_valid_in, 1) ? (7'd1 + $past(fv_rd_valid_count, 1)) : $past(fv_rd_valid_count, 1))) &&
  fv_read_state == fv_pwo_read_idle_type &&
  fv_twiddle_addr_int == $past(fv_get_twiddle_addr_reg_0_i, 1) &&
  fv_twiddle_addr_reg_d2 == ($past(fv_shuffle_en_in, 1) ? ((($past(fv_shuffle_en_in, 1) && ($past(fv_mlkem_in, 1) != 1'd0)) && ($past(fv_ntt_mode_in, 1) == 3'd5)) ? (($past(fv_get_twiddle_rand_offsets_0_i[fv_rounds_count], 1) + ({ 5'd0, 2'(($past(fv_index_count, 1) + $past(fv_index_rand_offset, 1)))} )) + $past(fv_twiddle_offset_array_0_i[fv_rounds_count], 1)) : ($past(fv_get_twiddle_rand_offsets_0_i[fv_rounds_count], 1) + $past(fv_twiddle_offset_array_0_i[fv_rounds_count], 1))) : ($past(fv_twiddle_addr_int, 1) + $past(fv_twiddle_offset_array_0_i[fv_rounds_count], 1)));
endproperty
a_read_fv_read_idle_to_fv_read_idle: assert property (disable iff(!rst || ntt_ctrl.zeroize) read_fv_read_idle_to_fv_read_idle_p);


property read_fv_read_idle_to_fv_read_stage_p;
  fv_read_idle &&
  fv_ntt_enable_in
|->
  ##1
  fv_read_stage &&
  fv_buf_rdptr_reg == ($past(fv_butterfly_ready_in, 1) ? ((($past(fv_mlkem_in, 1) != 1'd0) && ($past(fv_ntt_mode_in, 1) == 3'd5)) ? $past(fv_get_buf_rdptr_reg_next_pairwm_0_i, 1) : ({ 8'd0, $past(fv_get_buf_rdptr_reg_next_nonpairwm_0_i, 1)} )) : '0) &&
  fv_chunk_count_reg == ($past(fv_butterfly_ready_in, 1) ? ((($past(fv_mlkem_in, 1) != 1'd0) && ($past(fv_ntt_mode_in, 1) == 3'd5)) ? $past(fv_get_chunk_count_reg_next_pairwm_0_i, 1) : ({ 16'd0, $past(fv_get_chunk_count_reg_next_nonpairwm_0_i, 1)} )) : $past(fv_chunk_count_reg, 1)) &&
  fv_incr_twiddle_addr_reg == ((((($past(fv_read_state, 1) == fv_pwo_read_exec_type) || ($past(fv_read_state, 1) == fv_pwo_read_exec_wait_type)) && ($past(fv_mlkem_in, 1) != 1'd0)) && ($past(fv_ntt_mode_in, 1) == 3'd5)) && $past(fv_sampler_valid_in, 1)) &&
  fv_pw_mem_rd_addr_a_out == $past(fv_get_pw_addr_abc_wr_0_i, 1) &&
  fv_pw_mem_rd_addr_a_reg == $past(fv_get_pw_addr_abc_wr_0_i, 1) &&
  fv_pw_mem_rd_addr_b_out == $past(fv_get_pw_addr_abc_wr_1_i, 1) &&
  fv_pw_mem_rd_addr_b_reg == $past(fv_get_pw_addr_abc_wr_1_i, 1) &&
  fv_pw_mem_rd_addr_c_out == $past(fv_get_pw_addr_crd_0_i, 1) &&
  fv_pw_mem_rd_addr_c_reg == $past(fv_get_pw_addr_crd_0_i, 1) &&
  fv_rd_valid_count == ((($past(fv_read_state, 1) == fv_pwo_read_idle_type) || ($past(fv_read_state, 1) == fv_pwo_read_stage_type)) ? 7'd0 : ($past(fv_sampler_valid_in, 1) ? (7'd1 + $past(fv_rd_valid_count, 1)) : $past(fv_rd_valid_count, 1))) &&
  fv_read_state == fv_pwo_read_stage_type &&
  fv_twiddle_addr_int == $past(fv_get_twiddle_addr_reg_0_i, 1) &&
  fv_twiddle_addr_reg_d2 == ($past(fv_shuffle_en_in, 1) ? ((($past(fv_shuffle_en_in, 1) && ($past(fv_mlkem_in, 1) != 1'd0)) && ($past(fv_ntt_mode_in, 1) == 3'd5)) ? (($past(fv_get_twiddle_rand_offsets_0_i[fv_rounds_count], 1) + ({ 5'd0, 2'(($past(fv_index_count, 1) + $past(fv_index_rand_offset, 1)))} )) + $past(fv_twiddle_offset_array_0_i[fv_rounds_count], 1)) : ($past(fv_get_twiddle_rand_offsets_0_i[fv_rounds_count], 1) + $past(fv_twiddle_offset_array_0_i[fv_rounds_count], 1))) : ($past(fv_twiddle_addr_int, 1) + $past(fv_twiddle_offset_array_0_i[fv_rounds_count], 1)));
endproperty
a_read_fv_read_idle_to_fv_read_stage: assert property (disable iff(!rst || ntt_ctrl.zeroize) read_fv_read_idle_to_fv_read_stage_p);


property read_fv_read_stage_to_fv_read_exec_p;
  fv_read_stage &&
  (fv_write_state == fv_pwo_write_stage_type) &&
  (fv_rounds_count != 3'd1)
|->
  ##1
  fv_read_exec &&
  fv_buf_rdptr_reg == ($past(fv_butterfly_ready_in, 1) ? ((($past(fv_mlkem_in, 1) != 1'd0) && ($past(fv_ntt_mode_in, 1) == 3'd5)) ? $past(fv_get_buf_rdptr_reg_next_pairwm_0_i, 1) : ({ 8'd0, $past(fv_get_buf_rdptr_reg_next_nonpairwm_0_i, 1)} )) : '0) &&
  fv_chunk_count_reg == ($past(fv_butterfly_ready_in, 1) ? ((($past(fv_mlkem_in, 1) != 1'd0) && ($past(fv_ntt_mode_in, 1) == 3'd5)) ? $past(fv_get_chunk_count_reg_next_pairwm_0_i, 1) : ({ 16'd0, $past(fv_get_chunk_count_reg_next_nonpairwm_0_i, 1)} )) : $past(fv_chunk_count_reg, 1)) &&
  fv_incr_twiddle_addr_reg == ((((($past(fv_read_state, 1) == fv_pwo_read_exec_type) || ($past(fv_read_state, 1) == fv_pwo_read_exec_wait_type)) && ($past(fv_mlkem_in, 1) != 1'd0)) && ($past(fv_ntt_mode_in, 1) == 3'd5)) && $past(fv_sampler_valid_in, 1)) &&
  fv_pw_mem_rd_addr_a_out == $past(fv_get_pw_addr_abc_wr_0_i, 1) &&
  fv_pw_mem_rd_addr_a_reg == $past(fv_get_pw_addr_abc_wr_0_i, 1) &&
  fv_pw_mem_rd_addr_b_out == $past(fv_get_pw_addr_abc_wr_1_i, 1) &&
  fv_pw_mem_rd_addr_b_reg == $past(fv_get_pw_addr_abc_wr_1_i, 1) &&
  fv_pw_mem_rd_addr_c_out == $past(fv_get_pw_addr_crd_0_i, 1) &&
  fv_pw_mem_rd_addr_c_reg == $past(fv_get_pw_addr_crd_0_i, 1) &&
  fv_rd_valid_count == ((($past(fv_read_state, 1) == fv_pwo_read_idle_type) || ($past(fv_read_state, 1) == fv_pwo_read_stage_type)) ? 7'd0 : ($past(fv_sampler_valid_in, 1) ? (7'd1 + $past(fv_rd_valid_count, 1)) : $past(fv_rd_valid_count, 1))) &&
  fv_read_state == fv_pwo_read_exec_type &&
  fv_twiddle_addr_int == $past(fv_get_twiddle_addr_reg_0_i, 1) &&
  fv_twiddle_addr_reg_d2 == ($past(fv_shuffle_en_in, 1) ? ((($past(fv_shuffle_en_in, 1) && ($past(fv_mlkem_in, 1) != 1'd0)) && ($past(fv_ntt_mode_in, 1) == 3'd5)) ? (($past(fv_get_twiddle_rand_offsets_0_i[fv_rounds_count], 1) + ({ 5'd0, 2'(($past(fv_index_count, 1) + $past(fv_index_rand_offset, 1)))} )) + $past(fv_twiddle_offset_array_0_i[fv_rounds_count], 1)) : ($past(fv_get_twiddle_rand_offsets_0_i[fv_rounds_count], 1) + $past(fv_twiddle_offset_array_0_i[fv_rounds_count], 1))) : ($past(fv_twiddle_addr_int, 1) + $past(fv_twiddle_offset_array_0_i[fv_rounds_count], 1)));
endproperty
a_read_fv_read_stage_to_fv_read_exec: assert property (disable iff(!rst || ntt_ctrl.zeroize) read_fv_read_stage_to_fv_read_exec_p);


property read_fv_read_stage_to_fv_read_idle_p;
  fv_read_stage &&
  (fv_rounds_count == 3'd1) &&
  !fv_ntt_enable_in
|->
  ##1
  fv_read_idle &&
  fv_buf_rdptr_reg == ($past(fv_butterfly_ready_in, 1) ? ((($past(fv_mlkem_in, 1) != 1'd0) && ($past(fv_ntt_mode_in, 1) == 3'd5)) ? $past(fv_get_buf_rdptr_reg_next_pairwm_0_i, 1) : ({ 8'd0, $past(fv_get_buf_rdptr_reg_next_nonpairwm_0_i, 1)} )) : '0) &&
  fv_chunk_count_reg == ($past(fv_butterfly_ready_in, 1) ? ((($past(fv_mlkem_in, 1) != 1'd0) && ($past(fv_ntt_mode_in, 1) == 3'd5)) ? $past(fv_get_chunk_count_reg_next_pairwm_0_i, 1) : ({ 16'd0, $past(fv_get_chunk_count_reg_next_nonpairwm_0_i, 1)} )) : $past(fv_chunk_count_reg, 1)) &&
  fv_incr_twiddle_addr_reg == ((((($past(fv_read_state, 1) == fv_pwo_read_exec_type) || ($past(fv_read_state, 1) == fv_pwo_read_exec_wait_type)) && ($past(fv_mlkem_in, 1) != 1'd0)) && ($past(fv_ntt_mode_in, 1) == 3'd5)) && $past(fv_sampler_valid_in, 1)) &&
  fv_pw_mem_rd_addr_a_out == $past(fv_get_pw_addr_abc_wr_0_i, 1) &&
  fv_pw_mem_rd_addr_a_reg == $past(fv_get_pw_addr_abc_wr_0_i, 1) &&
  fv_pw_mem_rd_addr_b_out == $past(fv_get_pw_addr_abc_wr_1_i, 1) &&
  fv_pw_mem_rd_addr_b_reg == $past(fv_get_pw_addr_abc_wr_1_i, 1) &&
  fv_pw_mem_rd_addr_c_out == $past(fv_get_pw_addr_crd_0_i, 1) &&
  fv_pw_mem_rd_addr_c_reg == $past(fv_get_pw_addr_crd_0_i, 1) &&
  fv_rd_valid_count == ((($past(fv_read_state, 1) == fv_pwo_read_idle_type) || ($past(fv_read_state, 1) == fv_pwo_read_stage_type)) ? 7'd0 : ($past(fv_sampler_valid_in, 1) ? (7'd1 + $past(fv_rd_valid_count, 1)) : $past(fv_rd_valid_count, 1))) &&
  fv_read_state == fv_pwo_read_idle_type &&
  fv_twiddle_addr_int == $past(fv_get_twiddle_addr_reg_0_i, 1) &&
  fv_twiddle_addr_reg_d2 == ($past(fv_shuffle_en_in, 1) ? ((($past(fv_shuffle_en_in, 1) && ($past(fv_mlkem_in, 1) != 1'd0)) && ($past(fv_ntt_mode_in, 1) == 3'd5)) ? (($past(fv_get_twiddle_rand_offsets_0_i[fv_rounds_count], 1) + ({ 5'd0, 2'(($past(fv_index_count, 1) + $past(fv_index_rand_offset, 1)))} )) + $past(fv_twiddle_offset_array_0_i[fv_rounds_count], 1)) : ($past(fv_get_twiddle_rand_offsets_0_i[fv_rounds_count], 1) + $past(fv_twiddle_offset_array_0_i[fv_rounds_count], 1))) : ($past(fv_twiddle_addr_int, 1) + $past(fv_twiddle_offset_array_0_i[fv_rounds_count], 1)));
endproperty
a_read_fv_read_stage_to_fv_read_idle: assert property (disable iff(!rst || ntt_ctrl.zeroize) read_fv_read_stage_to_fv_read_idle_p);


property read_fv_read_stage_to_fv_read_stage_p;
  fv_read_stage &&
  ((fv_rounds_count != 3'd1) || fv_ntt_enable_in) &&
  !((fv_write_state == fv_pwo_write_stage_type) && (fv_rounds_count != 3'd1))
|->
  ##1
  fv_read_stage &&
  fv_buf_rdptr_reg == ($past(fv_butterfly_ready_in, 1) ? ((($past(fv_mlkem_in, 1) != 1'd0) && ($past(fv_ntt_mode_in, 1) == 3'd5)) ? $past(fv_get_buf_rdptr_reg_next_pairwm_0_i, 1) : ({ 8'd0, $past(fv_get_buf_rdptr_reg_next_nonpairwm_0_i, 1)} )) : '0) &&
  fv_chunk_count_reg == ($past(fv_butterfly_ready_in, 1) ? ((($past(fv_mlkem_in, 1) != 1'd0) && ($past(fv_ntt_mode_in, 1) == 3'd5)) ? $past(fv_get_chunk_count_reg_next_pairwm_0_i, 1) : ({ 16'd0, $past(fv_get_chunk_count_reg_next_nonpairwm_0_i, 1)} )) : $past(fv_chunk_count_reg, 1)) &&
  fv_incr_twiddle_addr_reg == ((((($past(fv_read_state, 1) == fv_pwo_read_exec_type) || ($past(fv_read_state, 1) == fv_pwo_read_exec_wait_type)) && ($past(fv_mlkem_in, 1) != 1'd0)) && ($past(fv_ntt_mode_in, 1) == 3'd5)) && $past(fv_sampler_valid_in, 1)) &&
  fv_pw_mem_rd_addr_a_out == $past(fv_get_pw_addr_abc_wr_0_i, 1) &&
  fv_pw_mem_rd_addr_a_reg == $past(fv_get_pw_addr_abc_wr_0_i, 1) &&
  fv_pw_mem_rd_addr_b_out == $past(fv_get_pw_addr_abc_wr_1_i, 1) &&
  fv_pw_mem_rd_addr_b_reg == $past(fv_get_pw_addr_abc_wr_1_i, 1) &&
  fv_pw_mem_rd_addr_c_out == $past(fv_get_pw_addr_crd_0_i, 1) &&
  fv_pw_mem_rd_addr_c_reg == $past(fv_get_pw_addr_crd_0_i, 1) &&
  fv_rd_valid_count == ((($past(fv_read_state, 1) == fv_pwo_read_idle_type) || ($past(fv_read_state, 1) == fv_pwo_read_stage_type)) ? 7'd0 : ($past(fv_sampler_valid_in, 1) ? (7'd1 + $past(fv_rd_valid_count, 1)) : $past(fv_rd_valid_count, 1))) &&
  fv_read_state == fv_pwo_read_stage_type &&
  fv_twiddle_addr_int == $past(fv_get_twiddle_addr_reg_0_i, 1) &&
  fv_twiddle_addr_reg_d2 == ($past(fv_shuffle_en_in, 1) ? ((($past(fv_shuffle_en_in, 1) && ($past(fv_mlkem_in, 1) != 1'd0)) && ($past(fv_ntt_mode_in, 1) == 3'd5)) ? (($past(fv_get_twiddle_rand_offsets_0_i[fv_rounds_count], 1) + ({ 5'd0, 2'(($past(fv_index_count, 1) + $past(fv_index_rand_offset, 1)))} )) + $past(fv_twiddle_offset_array_0_i[fv_rounds_count], 1)) : ($past(fv_get_twiddle_rand_offsets_0_i[fv_rounds_count], 1) + $past(fv_twiddle_offset_array_0_i[fv_rounds_count], 1))) : ($past(fv_twiddle_addr_int, 1) + $past(fv_twiddle_offset_array_0_i[fv_rounds_count], 1)));
endproperty
a_read_fv_read_stage_to_fv_read_stage: assert property (disable iff(!rst || ntt_ctrl.zeroize) read_fv_read_stage_to_fv_read_stage_p);


property write_fv_write_idle_to_fv_write_idle_p;
  fv_write_idle &&
  !fv_ntt_enable_in
|->
  ##1
  fv_write_idle &&
  fv_chunk_count == ((($past(fv_sampler_valid_in, 1) && (($past(fv_read_state, 1) == fv_pwo_read_exec_type) || ($past(fv_read_state, 1) == fv_pwo_read_exec_wait_type))) && ($past(fv_index_count, 1) == 2'h3)) ? (4'd1 + $past(fv_chunk_count, 1)) : $past(fv_chunk_count, 1)) &&
  $stable(fv_chunk_rand_offset) &&
  fv_done_out == (($past(fv_rst_rounds_in, 1) ? 3'd0 : (($past(fv_rounds_count, 1) == 3'd1) ? 3'd0 : $past(fv_rounds_count, 1))) == 3'd1) &&
  fv_index_count == (($past(fv_sampler_valid_in, 1) && (($past(fv_read_state, 1) == fv_pwo_read_exec_type) || ($past(fv_read_state, 1) == fv_pwo_read_exec_wait_type))) ? (2'd1 + $past(fv_index_count, 1)) : $past(fv_index_count, 1)) &&
  fv_index_rand_offset == ((($past(fv_sampler_valid_in, 1) && (($past(fv_read_state, 1) == fv_pwo_read_exec_type) || ($past(fv_read_state, 1) == fv_pwo_read_exec_wait_type))) && ($past(fv_index_count, 1) == 2'h3)) ? $past(fv_get_index_rand_offset_from_random_0_i, 1) : $past(fv_index_rand_offset, 1)) &&
  fv_pw_mem_wr_addr_c_out == $past(fv_get_pw_addr_cwr_0_i, 1) &&
  fv_pw_mem_wr_addr_c_reg == $past(fv_get_pw_addr_cwr_0_i, 1) &&
  fv_rounds_count == ($past(fv_rst_rounds_in, 1) ? 3'd0 : (($past(fv_rounds_count, 1) == 3'd1) ? 3'd0 : $past(fv_rounds_count, 1))) &&
  fv_wr_valid_count == ((($past(fv_write_state, 1) == fv_pwo_write_idle_type) || ($past(fv_write_state, 1) == fv_pwo_write_stage_type)) ? 7'd0 : ($past(fv_butterfly_ready_in, 1) ? (7'd1 + $past(fv_wr_valid_count, 1)) : $past(fv_wr_valid_count, 1))) &&
  fv_write_state == fv_pwo_write_idle_type;
endproperty
a_write_fv_write_idle_to_fv_write_idle: assert property (disable iff(!rst || ntt_ctrl.zeroize) write_fv_write_idle_to_fv_write_idle_p);


property write_fv_write_idle_to_fv_write_stage_p;
  fv_write_idle &&
  fv_ntt_enable_in
|->
  ##1
  fv_write_stage &&
  fv_chunk_count == $past(fv_get_chunk_rand_offset_from_random_0_i, 1) &&
  fv_chunk_rand_offset == $past(fv_get_chunk_rand_offset_from_random_0_i, 1) &&
  fv_done_out == (($past(fv_rst_rounds_in, 1) ? 3'd0 : (($past(fv_rounds_count, 1) == 3'd1) ? 3'd0 : $past(fv_rounds_count, 1))) == 3'd1) &&
  fv_index_count == (($past(fv_sampler_valid_in, 1) && (($past(fv_read_state, 1) == fv_pwo_read_exec_type) || ($past(fv_read_state, 1) == fv_pwo_read_exec_wait_type))) ? (2'd1 + $past(fv_index_count, 1)) : $past(fv_index_count, 1)) &&
  fv_index_rand_offset == ((($past(fv_sampler_valid_in, 1) && (($past(fv_read_state, 1) == fv_pwo_read_exec_type) || ($past(fv_read_state, 1) == fv_pwo_read_exec_wait_type))) && ($past(fv_index_count, 1) == 2'h3)) ? $past(fv_get_index_rand_offset_from_random_0_i, 1) : $past(fv_index_rand_offset, 1)) &&
  fv_pw_mem_wr_addr_c_out == $past(fv_get_pw_addr_cwr_0_i, 1) &&
  fv_pw_mem_wr_addr_c_reg == $past(fv_get_pw_addr_cwr_0_i, 1) &&
  fv_rounds_count == ($past(fv_rst_rounds_in, 1) ? 3'd0 : (($past(fv_rounds_count, 1) == 3'd1) ? 3'd0 : $past(fv_rounds_count, 1))) &&
  fv_wr_valid_count == ((($past(fv_write_state, 1) == fv_pwo_write_idle_type) || ($past(fv_write_state, 1) == fv_pwo_write_stage_type)) ? 7'd0 : ($past(fv_butterfly_ready_in, 1) ? (7'd1 + $past(fv_wr_valid_count, 1)) : $past(fv_wr_valid_count, 1))) &&
  fv_write_state == fv_pwo_write_stage_type;
endproperty
a_write_fv_write_idle_to_fv_write_stage: assert property (disable iff(!rst || ntt_ctrl.zeroize) write_fv_write_idle_to_fv_write_stage_p);


property write_fv_write_mem_to_fv_write_mem_p;
  fv_write_mem &&
  ((fv_shuffle_en_in || fv_butterfly_ready_in) || (({ 57'd0, fv_wr_valid_count} ) >= 64'h40)) &&
  !((fv_shuffle_en_in && fv_butterfly_ready_in) && (fv_wr_valid_count == 7'h3F)) &&
  (fv_shuffle_en_in || (fv_wr_valid_count != 7'h40))
|->
  ##1
  fv_write_mem &&
  fv_chunk_count == ((($past(fv_sampler_valid_in, 1) && (($past(fv_read_state, 1) == fv_pwo_read_exec_type) || ($past(fv_read_state, 1) == fv_pwo_read_exec_wait_type))) && ($past(fv_index_count, 1) == 2'h3)) ? (4'd1 + $past(fv_chunk_count, 1)) : $past(fv_chunk_count, 1)) &&
  $stable(fv_chunk_rand_offset) &&
  fv_done_out == (($past(fv_rst_rounds_in, 1) ? 3'd0 : (($past(fv_rounds_count, 1) == 3'd1) ? 3'd0 : $past(fv_rounds_count, 1))) == 3'd1) &&
  fv_index_count == (($past(fv_sampler_valid_in, 1) && (($past(fv_read_state, 1) == fv_pwo_read_exec_type) || ($past(fv_read_state, 1) == fv_pwo_read_exec_wait_type))) ? (2'd1 + $past(fv_index_count, 1)) : $past(fv_index_count, 1)) &&
  fv_index_rand_offset == ((($past(fv_sampler_valid_in, 1) && (($past(fv_read_state, 1) == fv_pwo_read_exec_type) || ($past(fv_read_state, 1) == fv_pwo_read_exec_wait_type))) && ($past(fv_index_count, 1) == 2'h3)) ? $past(fv_get_index_rand_offset_from_random_0_i, 1) : $past(fv_index_rand_offset, 1)) &&
  fv_pw_mem_wr_addr_c_out == $past(fv_get_pw_addr_cwr_1_i, 1) &&
  fv_pw_mem_wr_addr_c_reg == $past(fv_get_pw_addr_cwr_1_i, 1) &&
  fv_rounds_count == ($past(fv_rst_rounds_in, 1) ? 3'd0 : (($past(fv_rounds_count, 1) == 3'd1) ? 3'd0 : $past(fv_rounds_count, 1))) &&
  fv_wr_valid_count == ((($past(fv_write_state, 1) == fv_pwo_write_idle_type) || ($past(fv_write_state, 1) == fv_pwo_write_stage_type)) ? 7'd0 : ($past(fv_butterfly_ready_in, 1) ? (7'd1 + $past(fv_wr_valid_count, 1)) : $past(fv_wr_valid_count, 1))) &&
  fv_write_state == fv_pwo_write_mem_type;
endproperty
a_write_fv_write_mem_to_fv_write_mem: assert property (disable iff(!rst || ntt_ctrl.zeroize) write_fv_write_mem_to_fv_write_mem_p);


property write_fv_write_mem_to_fv_write_stage_p;
  fv_write_mem &&
  (fv_butterfly_ready_in || 1) &&
  !fv_shuffle_en_in &&
  (fv_wr_valid_count == 7'h40)
|->
  ##1
  fv_write_stage &&
  fv_chunk_count == $past(fv_get_chunk_rand_offset_from_random_0_i, 1) &&
  fv_chunk_rand_offset == $past(fv_get_chunk_rand_offset_from_random_0_i, 1) &&
  fv_done_out == (($past(fv_rst_rounds_in, 1) ? 3'd0 : ((({ 61'd0, $past(fv_rounds_count, 1)} ) < 64'd1) ? (3'd1 + $past(fv_rounds_count, 1)) : (($past(fv_rounds_count, 1) == 3'd1) ? 3'd0 : $past(fv_rounds_count, 1)))) == 3'd1) &&
  fv_index_count == (($past(fv_sampler_valid_in, 1) && (($past(fv_read_state, 1) == fv_pwo_read_exec_type) || ($past(fv_read_state, 1) == fv_pwo_read_exec_wait_type))) ? (2'd1 + $past(fv_index_count, 1)) : $past(fv_index_count, 1)) &&
  fv_index_rand_offset == ((($past(fv_sampler_valid_in, 1) && (($past(fv_read_state, 1) == fv_pwo_read_exec_type) || ($past(fv_read_state, 1) == fv_pwo_read_exec_wait_type))) && ($past(fv_index_count, 1) == 2'h3)) ? $past(fv_get_index_rand_offset_from_random_0_i, 1) : $past(fv_index_rand_offset, 1)) &&
  fv_pw_mem_wr_addr_c_out == $past(fv_get_pw_addr_cwr_1_i, 1) &&
  fv_pw_mem_wr_addr_c_reg == $past(fv_get_pw_addr_cwr_1_i, 1) &&
  fv_rounds_count == ($past(fv_rst_rounds_in, 1) ? 3'd0 : ((({ 61'd0, $past(fv_rounds_count, 1)} ) < 64'd1) ? (3'd1 + $past(fv_rounds_count, 1)) : (($past(fv_rounds_count, 1) == 3'd1) ? 3'd0 : $past(fv_rounds_count, 1)))) &&
  fv_wr_valid_count == ((($past(fv_write_state, 1) == fv_pwo_write_idle_type) || ($past(fv_write_state, 1) == fv_pwo_write_stage_type)) ? 7'd0 : ($past(fv_butterfly_ready_in, 1) ? (7'd1 + $past(fv_wr_valid_count, 1)) : $past(fv_wr_valid_count, 1))) &&
  fv_write_state == fv_pwo_write_stage_type;
endproperty
a_write_fv_write_mem_to_fv_write_stage: assert property (disable iff(!rst || ntt_ctrl.zeroize) write_fv_write_mem_to_fv_write_stage_p);


property write_fv_write_mem_to_fv_write_wait_p;
  fv_write_mem &&
  ((!(fv_shuffle_en_in || fv_butterfly_ready_in) && (({ 57'd0, fv_wr_valid_count} ) < 64'h40)) || ((fv_shuffle_en_in && fv_butterfly_ready_in) && (fv_wr_valid_count == 7'h3F)))
|->
  ##1
  fv_write_wait &&
  fv_chunk_count == ((($past(fv_sampler_valid_in, 1) && (($past(fv_read_state, 1) == fv_pwo_read_exec_type) || ($past(fv_read_state, 1) == fv_pwo_read_exec_wait_type))) && ($past(fv_index_count, 1) == 2'h3)) ? (4'd1 + $past(fv_chunk_count, 1)) : $past(fv_chunk_count, 1)) &&
  $stable(fv_chunk_rand_offset) &&
  fv_done_out == (($past(fv_rst_rounds_in, 1) ? 3'd0 : (($past(fv_rounds_count, 1) == 3'd1) ? 3'd0 : $past(fv_rounds_count, 1))) == 3'd1) &&
  fv_index_count == (($past(fv_sampler_valid_in, 1) && (($past(fv_read_state, 1) == fv_pwo_read_exec_type) || ($past(fv_read_state, 1) == fv_pwo_read_exec_wait_type))) ? (2'd1 + $past(fv_index_count, 1)) : $past(fv_index_count, 1)) &&
  fv_index_rand_offset == ((($past(fv_sampler_valid_in, 1) && (($past(fv_read_state, 1) == fv_pwo_read_exec_type) || ($past(fv_read_state, 1) == fv_pwo_read_exec_wait_type))) && ($past(fv_index_count, 1) == 2'h3)) ? $past(fv_get_index_rand_offset_from_random_0_i, 1) : $past(fv_index_rand_offset, 1)) &&
  fv_pw_mem_wr_addr_c_out == $past(fv_get_pw_addr_cwr_1_i, 1) &&
  fv_pw_mem_wr_addr_c_reg == $past(fv_get_pw_addr_cwr_1_i, 1) &&
  fv_rounds_count == ($past(fv_rst_rounds_in, 1) ? 3'd0 : (($past(fv_rounds_count, 1) == 3'd1) ? 3'd0 : $past(fv_rounds_count, 1))) &&
  fv_wr_valid_count == ((($past(fv_write_state, 1) == fv_pwo_write_idle_type) || ($past(fv_write_state, 1) == fv_pwo_write_stage_type)) ? 7'd0 : ($past(fv_butterfly_ready_in, 1) ? (7'd1 + $past(fv_wr_valid_count, 1)) : $past(fv_wr_valid_count, 1))) &&
  fv_write_state == fv_pwo_write_wait_type;
endproperty
a_write_fv_write_mem_to_fv_write_wait: assert property (disable iff(!rst || ntt_ctrl.zeroize) write_fv_write_mem_to_fv_write_wait_p);


property write_fv_write_stage_to_fv_write_idle_p;
  fv_write_stage &&
  (fv_rounds_count == 3'd1)
|->
  ##1
  fv_write_idle &&
  fv_chunk_count == ((($past(fv_sampler_valid_in, 1) && (($past(fv_read_state, 1) == fv_pwo_read_exec_type) || ($past(fv_read_state, 1) == fv_pwo_read_exec_wait_type))) && ($past(fv_index_count, 1) == 2'h3)) ? (4'd1 + $past(fv_chunk_count, 1)) : $past(fv_chunk_count, 1)) &&
  $stable(fv_chunk_rand_offset) &&
  fv_done_out == 0 &&
  fv_index_count == (($past(fv_sampler_valid_in, 1) && (($past(fv_read_state, 1) == fv_pwo_read_exec_type) || ($past(fv_read_state, 1) == fv_pwo_read_exec_wait_type))) ? (2'd1 + $past(fv_index_count, 1)) : $past(fv_index_count, 1)) &&
  fv_index_rand_offset == ((($past(fv_sampler_valid_in, 1) && (($past(fv_read_state, 1) == fv_pwo_read_exec_type) || ($past(fv_read_state, 1) == fv_pwo_read_exec_wait_type))) && ($past(fv_index_count, 1) == 2'h3)) ? $past(fv_get_index_rand_offset_from_random_0_i, 1) : $past(fv_index_rand_offset, 1)) &&
  fv_pw_mem_wr_addr_c_out == $past(fv_get_pw_addr_cwr_0_i, 1) &&
  fv_pw_mem_wr_addr_c_reg == $past(fv_get_pw_addr_cwr_0_i, 1) &&
  fv_rounds_count == 3'd0 &&
  fv_wr_valid_count == ((($past(fv_write_state, 1) == fv_pwo_write_idle_type) || ($past(fv_write_state, 1) == fv_pwo_write_stage_type)) ? 7'd0 : ($past(fv_butterfly_ready_in, 1) ? (7'd1 + $past(fv_wr_valid_count, 1)) : $past(fv_wr_valid_count, 1))) &&
  fv_write_state == fv_pwo_write_idle_type;
endproperty
a_write_fv_write_stage_to_fv_write_idle: assert property (disable iff(!rst || ntt_ctrl.zeroize) write_fv_write_stage_to_fv_write_idle_p);


property write_fv_write_stage_to_fv_write_mem_p;
  fv_write_stage &&
  (fv_rounds_count != 3'd1) &&
  fv_shuffle_en_in
|->
  ##1
  fv_write_mem &&
  fv_chunk_count == ((($past(fv_sampler_valid_in, 1) && (($past(fv_read_state, 1) == fv_pwo_read_exec_type) || ($past(fv_read_state, 1) == fv_pwo_read_exec_wait_type))) && ($past(fv_index_count, 1) == 2'h3)) ? (4'd1 + $past(fv_chunk_count, 1)) : $past(fv_chunk_count, 1)) &&
  $stable(fv_chunk_rand_offset) &&
  fv_done_out == (($past(fv_rst_rounds_in, 1) ? 3'd0 : $past(fv_rounds_count, 1)) == 3'd1) &&
  fv_index_count == (($past(fv_sampler_valid_in, 1) && (($past(fv_read_state, 1) == fv_pwo_read_exec_type) || ($past(fv_read_state, 1) == fv_pwo_read_exec_wait_type))) ? (2'd1 + $past(fv_index_count, 1)) : $past(fv_index_count, 1)) &&
  fv_index_rand_offset == ((($past(fv_sampler_valid_in, 1) && (($past(fv_read_state, 1) == fv_pwo_read_exec_type) || ($past(fv_read_state, 1) == fv_pwo_read_exec_wait_type))) && ($past(fv_index_count, 1) == 2'h3)) ? $past(fv_get_index_rand_offset_from_random_0_i, 1) : $past(fv_index_rand_offset, 1)) &&
  fv_pw_mem_wr_addr_c_out == $past(fv_get_pw_addr_cwr_0_i, 1) &&
  fv_pw_mem_wr_addr_c_reg == $past(fv_get_pw_addr_cwr_0_i, 1) &&
  fv_rounds_count == ($past(fv_rst_rounds_in, 1) ? 3'd0 : $past(fv_rounds_count, 1)) &&
  fv_wr_valid_count == ((($past(fv_write_state, 1) == fv_pwo_write_idle_type) || ($past(fv_write_state, 1) == fv_pwo_write_stage_type)) ? 7'd0 : ($past(fv_butterfly_ready_in, 1) ? (7'd1 + $past(fv_wr_valid_count, 1)) : $past(fv_wr_valid_count, 1))) &&
  fv_write_state == fv_pwo_write_mem_type;
endproperty
a_write_fv_write_stage_to_fv_write_mem: assert property (disable iff(!rst || ntt_ctrl.zeroize) write_fv_write_stage_to_fv_write_mem_p);


property write_fv_write_stage_to_fv_write_wait_p;
  fv_write_stage &&
  (fv_rounds_count != 3'd1) &&
  !fv_shuffle_en_in
|->
  ##1
  fv_write_wait &&
  fv_chunk_count == ((($past(fv_sampler_valid_in, 1) && (($past(fv_read_state, 1) == fv_pwo_read_exec_type) || ($past(fv_read_state, 1) == fv_pwo_read_exec_wait_type))) && ($past(fv_index_count, 1) == 2'h3)) ? (4'd1 + $past(fv_chunk_count, 1)) : $past(fv_chunk_count, 1)) &&
  $stable(fv_chunk_rand_offset) &&
  fv_done_out == (($past(fv_rst_rounds_in, 1) ? 3'd0 : $past(fv_rounds_count, 1)) == 3'd1) &&
  fv_index_count == (($past(fv_sampler_valid_in, 1) && (($past(fv_read_state, 1) == fv_pwo_read_exec_type) || ($past(fv_read_state, 1) == fv_pwo_read_exec_wait_type))) ? (2'd1 + $past(fv_index_count, 1)) : $past(fv_index_count, 1)) &&
  fv_index_rand_offset == ((($past(fv_sampler_valid_in, 1) && (($past(fv_read_state, 1) == fv_pwo_read_exec_type) || ($past(fv_read_state, 1) == fv_pwo_read_exec_wait_type))) && ($past(fv_index_count, 1) == 2'h3)) ? $past(fv_get_index_rand_offset_from_random_0_i, 1) : $past(fv_index_rand_offset, 1)) &&
  fv_pw_mem_wr_addr_c_out == $past(fv_get_pw_addr_cwr_0_i, 1) &&
  fv_pw_mem_wr_addr_c_reg == $past(fv_get_pw_addr_cwr_0_i, 1) &&
  fv_rounds_count == ($past(fv_rst_rounds_in, 1) ? 3'd0 : $past(fv_rounds_count, 1)) &&
  fv_wr_valid_count == ((($past(fv_write_state, 1) == fv_pwo_write_idle_type) || ($past(fv_write_state, 1) == fv_pwo_write_stage_type)) ? 7'd0 : ($past(fv_butterfly_ready_in, 1) ? (7'd1 + $past(fv_wr_valid_count, 1)) : $past(fv_wr_valid_count, 1))) &&
  fv_write_state == fv_pwo_write_wait_type;
endproperty
a_write_fv_write_stage_to_fv_write_wait: assert property (disable iff(!rst || ntt_ctrl.zeroize) write_fv_write_stage_to_fv_write_wait_p);


property write_fv_write_wait_to_fv_write_mem_p;
  fv_write_wait &&
  !fv_shuffle_en_in &&
  fv_butterfly_ready_in
|->
  ##1
  fv_write_mem &&
  fv_chunk_count == ((($past(fv_sampler_valid_in, 1) && (($past(fv_read_state, 1) == fv_pwo_read_exec_type) || ($past(fv_read_state, 1) == fv_pwo_read_exec_wait_type))) && ($past(fv_index_count, 1) == 2'h3)) ? (4'd1 + $past(fv_chunk_count, 1)) : $past(fv_chunk_count, 1)) &&
  $stable(fv_chunk_rand_offset) &&
  fv_done_out == (($past(fv_rst_rounds_in, 1) ? 3'd0 : (($past(fv_rounds_count, 1) == 3'd1) ? 3'd0 : $past(fv_rounds_count, 1))) == 3'd1) &&
  fv_index_count == (($past(fv_sampler_valid_in, 1) && (($past(fv_read_state, 1) == fv_pwo_read_exec_type) || ($past(fv_read_state, 1) == fv_pwo_read_exec_wait_type))) ? (2'd1 + $past(fv_index_count, 1)) : $past(fv_index_count, 1)) &&
  fv_index_rand_offset == ((($past(fv_sampler_valid_in, 1) && (($past(fv_read_state, 1) == fv_pwo_read_exec_type) || ($past(fv_read_state, 1) == fv_pwo_read_exec_wait_type))) && ($past(fv_index_count, 1) == 2'h3)) ? $past(fv_get_index_rand_offset_from_random_0_i, 1) : $past(fv_index_rand_offset, 1)) &&
  fv_pw_mem_wr_addr_c_out == $past(fv_get_pw_addr_cwr_1_i, 1) &&
  fv_pw_mem_wr_addr_c_reg == $past(fv_get_pw_addr_cwr_1_i, 1) &&
  fv_rounds_count == ($past(fv_rst_rounds_in, 1) ? 3'd0 : (($past(fv_rounds_count, 1) == 3'd1) ? 3'd0 : $past(fv_rounds_count, 1))) &&
  fv_wr_valid_count == ((($past(fv_write_state, 1) == fv_pwo_write_idle_type) || ($past(fv_write_state, 1) == fv_pwo_write_stage_type)) ? 7'd0 : ($past(fv_butterfly_ready_in, 1) ? (7'd1 + $past(fv_wr_valid_count, 1)) : $past(fv_wr_valid_count, 1))) &&
  fv_write_state == fv_pwo_write_mem_type;
endproperty
a_write_fv_write_wait_to_fv_write_mem: assert property (disable iff(!rst || ntt_ctrl.zeroize) write_fv_write_wait_to_fv_write_mem_p);


property write_fv_write_wait_to_fv_write_stage_p;
  fv_write_wait &&
  fv_shuffle_en_in
|->
  ##1
  fv_write_stage &&
  fv_chunk_count == $past(fv_get_chunk_rand_offset_from_random_0_i, 1) &&
  fv_chunk_rand_offset == $past(fv_get_chunk_rand_offset_from_random_0_i, 1) &&
  fv_done_out == (($past(fv_rst_rounds_in, 1) ? 3'd0 : ((({ 61'd0, $past(fv_rounds_count, 1)} ) < 64'd1) ? (3'd1 + $past(fv_rounds_count, 1)) : (($past(fv_rounds_count, 1) == 3'd1) ? 3'd0 : $past(fv_rounds_count, 1)))) == 3'd1) &&
  fv_index_count == (($past(fv_sampler_valid_in, 1) && (($past(fv_read_state, 1) == fv_pwo_read_exec_type) || ($past(fv_read_state, 1) == fv_pwo_read_exec_wait_type))) ? (2'd1 + $past(fv_index_count, 1)) : $past(fv_index_count, 1)) &&
  fv_index_rand_offset == ((($past(fv_sampler_valid_in, 1) && (($past(fv_read_state, 1) == fv_pwo_read_exec_type) || ($past(fv_read_state, 1) == fv_pwo_read_exec_wait_type))) && ($past(fv_index_count, 1) == 2'h3)) ? $past(fv_get_index_rand_offset_from_random_0_i, 1) : $past(fv_index_rand_offset, 1)) &&
  fv_pw_mem_wr_addr_c_out == $past(fv_get_pw_addr_cwr_1_i, 1) &&
  fv_pw_mem_wr_addr_c_reg == $past(fv_get_pw_addr_cwr_1_i, 1) &&
  fv_rounds_count == ($past(fv_rst_rounds_in, 1) ? 3'd0 : ((({ 61'd0, $past(fv_rounds_count, 1)} ) < 64'd1) ? (3'd1 + $past(fv_rounds_count, 1)) : (($past(fv_rounds_count, 1) == 3'd1) ? 3'd0 : $past(fv_rounds_count, 1)))) &&
  fv_wr_valid_count == ((($past(fv_write_state, 1) == fv_pwo_write_idle_type) || ($past(fv_write_state, 1) == fv_pwo_write_stage_type)) ? 7'd0 : ($past(fv_butterfly_ready_in, 1) ? (7'd1 + $past(fv_wr_valid_count, 1)) : $past(fv_wr_valid_count, 1))) &&
  fv_write_state == fv_pwo_write_stage_type;
endproperty
a_write_fv_write_wait_to_fv_write_stage: assert property (disable iff(!rst || ntt_ctrl.zeroize) write_fv_write_wait_to_fv_write_stage_p);


property write_fv_write_wait_to_fv_write_wait_p;
  fv_write_wait &&
  !fv_shuffle_en_in &&
  !fv_butterfly_ready_in
|->
  ##1
  fv_write_wait &&
  fv_chunk_count == ((($past(fv_sampler_valid_in, 1) && (($past(fv_read_state, 1) == fv_pwo_read_exec_type) || ($past(fv_read_state, 1) == fv_pwo_read_exec_wait_type))) && ($past(fv_index_count, 1) == 2'h3)) ? (4'd1 + $past(fv_chunk_count, 1)) : $past(fv_chunk_count, 1)) &&
  $stable(fv_chunk_rand_offset) &&
  fv_done_out == (($past(fv_rst_rounds_in, 1) ? 3'd0 : (($past(fv_rounds_count, 1) == 3'd1) ? 3'd0 : $past(fv_rounds_count, 1))) == 3'd1) &&
  fv_index_count == (($past(fv_sampler_valid_in, 1) && (($past(fv_read_state, 1) == fv_pwo_read_exec_type) || ($past(fv_read_state, 1) == fv_pwo_read_exec_wait_type))) ? (2'd1 + $past(fv_index_count, 1)) : $past(fv_index_count, 1)) &&
  fv_index_rand_offset == ((($past(fv_sampler_valid_in, 1) && (($past(fv_read_state, 1) == fv_pwo_read_exec_type) || ($past(fv_read_state, 1) == fv_pwo_read_exec_wait_type))) && ($past(fv_index_count, 1) == 2'h3)) ? $past(fv_get_index_rand_offset_from_random_0_i, 1) : $past(fv_index_rand_offset, 1)) &&
  fv_pw_mem_wr_addr_c_out == $past(fv_get_pw_addr_cwr_1_i, 1) &&
  fv_pw_mem_wr_addr_c_reg == $past(fv_get_pw_addr_cwr_1_i, 1) &&
  fv_rounds_count == ($past(fv_rst_rounds_in, 1) ? 3'd0 : (($past(fv_rounds_count, 1) == 3'd1) ? 3'd0 : $past(fv_rounds_count, 1))) &&
  fv_wr_valid_count == ((($past(fv_write_state, 1) == fv_pwo_write_idle_type) || ($past(fv_write_state, 1) == fv_pwo_write_stage_type)) ? 7'd0 : ($past(fv_butterfly_ready_in, 1) ? (7'd1 + $past(fv_wr_valid_count, 1)) : $past(fv_wr_valid_count, 1))) &&
  fv_write_state == fv_pwo_write_wait_type;
endproperty
a_write_fv_write_wait_to_fv_write_wait: assert property (disable iff(!rst || ntt_ctrl.zeroize) write_fv_write_wait_to_fv_write_wait_p);


property read_fv_read_idle_eventually_left_p;
  fv_read_idle && fv_ntt_enable_in
|->
  s_eventually(!fv_read_idle);
endproperty
a_read_fv_read_idle_eventually_left: assert property (disable iff(!rst || ntt_ctrl.zeroize) read_fv_read_idle_eventually_left_p);


property read_fv_read_stage_eventually_left_p;
  fv_read_stage && !fv_ntt_enable_in && fv_rounds_count==1
|->
  s_eventually(!fv_read_stage);
endproperty
a_read_fv_read_stage_eventually_left: assert property (disable iff(!rst || ntt_ctrl.zeroize) read_fv_read_stage_eventually_left_p);


property read_fv_read_exec_eventually_left_p;
  fv_read_exec
|->
  s_eventually(!fv_read_exec);
endproperty
a_read_fv_read_exec_eventually_left: assert property (disable iff(!rst || ntt_ctrl.zeroize) read_fv_read_exec_eventually_left_p);


property read_fv_read_exec_wait_eventually_left_p;
  fv_read_exec_wait
|->
  s_eventually(!fv_read_exec_wait);
endproperty
a_read_fv_read_exec_wait_eventually_left: assert property (disable iff(!rst || ntt_ctrl.zeroize) read_fv_read_exec_wait_eventually_left_p);


property write_fv_write_idle_eventually_left_p;
  fv_write_idle && fv_ntt_enable_in
|->
  s_eventually(!fv_write_idle);
endproperty
a_write_fv_write_idle_eventually_left: assert property (disable iff(!rst || ntt_ctrl.zeroize) write_fv_write_idle_eventually_left_p);


property write_fv_write_stage_eventually_left_p;
  fv_write_stage && !fv_ntt_enable_in
|->
  s_eventually(!fv_write_stage);
endproperty
a_write_fv_write_stage_eventually_left: assert property (disable iff(!rst || ntt_ctrl.zeroize) write_fv_write_stage_eventually_left_p);


property write_fv_write_wait_eventually_left_p;
  fv_write_wait
|->
  s_eventually(!fv_write_wait);
endproperty
a_write_fv_write_wait_eventually_left: assert property (disable iff(!rst || ntt_ctrl.zeroize) write_fv_write_wait_eventually_left_p);


property write_fv_write_mem_eventually_left_p;
  fv_write_mem
|->
  s_eventually(!fv_write_mem);
endproperty
a_write_fv_write_mem_eventually_left: assert property (disable iff(!rst || ntt_ctrl.zeroize) write_fv_write_mem_eventually_left_p);


localparam CONSISTENCY = 1;
if (CONSISTENCY) begin : gen_read_consistency
  // Check that no more than 1 state condition is met at the same time
  a_read_consistency_onehot0_state: assert property($onehot0({ fv_read_exec, fv_read_exec_wait, fv_read_idle, fv_read_stage }));
end


if (CONSISTENCY) begin : gen_write_consistency
  // Check that no more than 1 state condition is met at the same time
  a_write_consistency_onehot0_state: assert property($onehot0({ fv_write_idle, fv_write_mem, fv_write_stage, fv_write_wait }));
end
 //###### just for check

endmodule
