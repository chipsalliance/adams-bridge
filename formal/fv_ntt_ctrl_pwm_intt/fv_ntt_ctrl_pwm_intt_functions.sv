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


package fv_ntt_ctrl_pwm_intt_functions;


import fv_ntt_ctrl_pwm_intt_pkg::*;


function logic unsigned [14:0] getMemRdBaseAddr(logic unsigned [2:0] rounds_count, st_NttMemBaseAddrs ntt_mem_base_addrs);
  if (rounds_count == 64'd0) begin
    return 15'd0;
  end

  if ((rounds_count & 64'd1) != 64'd0) begin
    return ntt_mem_base_addrs.interim_base_addr;
  end

  return ntt_mem_base_addrs.dest_base_addr;
endfunction


function logic unsigned [15:0] getShuffledMemRdAddrNxt(logic unsigned [3:0] chunk_count, logic unsigned [14:0] rd_addr_step, logic unsigned [1:0] mem_rd_index_ofst, logic unsigned [14:0] mem_rd_base_addr);
  return 16'(((64'd4 * chunk_count) + (rd_addr_step * mem_rd_index_ofst)) + mem_rd_base_addr);
endfunction


function logic unsigned [15:0] getUnshuffledMemRdAddrNxt(logic unsigned [14:0] mem_rd_addr, logic unsigned [14:0] rd_addr_step);
  return 16'(mem_rd_addr + rd_addr_step);
endfunction


function logic unsigned [15:0] getMemRdAddrNxt(logic shuffle_en, logic unsigned [2:0] rounds_count, logic unsigned [15:0] shuffled_nxt, logic unsigned [15:0] unshuffled_nxt);
  if (shuffle_en && (rounds_count > 64'd0)) begin
    return shuffled_nxt;
  end

  return unshuffled_nxt;
endfunction


function logic unsigned [14:0] getPwMemRdAddrNxt(logic unsigned [14:0] base_addr, logic unsigned [3:0] chunk_count, logic unsigned [14:0] rd_addr_step, logic unsigned [1:0] mem_rd_index_ofst);
  return 15'((base_addr + (64'd4 * chunk_count)) + (rd_addr_step * mem_rd_index_ofst));
endfunction


function logic unsigned [14:0] getPwMemRdRstAddr(logic shuffle_en, logic unsigned [3:0] chunk_rand_offset, logic unsigned [14:0] base_addr);
  if (shuffle_en) begin
    return 15'((64'd4 * chunk_rand_offset) + base_addr);
  end

  return base_addr;
endfunction


function logic unsigned [14:0] getPwMemRdIncrAddrAb(logic shuffle_en, logic unsigned [14:0] addr_nxt, logic unsigned [14:0] default_addr, logic unsigned [14:0] addr_step);
  if (shuffle_en) begin
    return addr_nxt;
  end

  return 15'(default_addr + addr_step);
endfunction


function logic unsigned [14:0] getPwMemRdAddrAb(logic rst_pw_addr, logic incr_pw_addr, logic unsigned [14:0] rst_addr, logic unsigned [14:0] incr_addr, logic unsigned [14:0] default_addr);
  if (rst_pw_addr) begin
    return rst_addr;
  end

  if (incr_pw_addr) begin
    return incr_addr;
  end

  return default_addr;
endfunction


function logic unsigned [14:0] getPwMemRdShuffledIncrAddrC(logic accumulate, logic unsigned [14:0] addr_nxt);
  if (accumulate) begin
    return addr_nxt;
  end

  return 15'd0;
endfunction


function logic unsigned [14:0] getPwMemRdUnshuffledIncrAddrC(logic accumulate, logic unsigned [14:0] default_addr, logic unsigned [14:0] addr_step);
  if (accumulate) begin
    return 15'(default_addr + addr_step);
  end

  return 15'd0;
endfunction


function logic unsigned [14:0] getPwMemRdAddrC(logic rst_pw_addr, logic incr_pw_addr, logic shuffle_en, logic unsigned [14:0] rst_addr, logic unsigned [14:0] incr_shuffled_addr, logic unsigned [14:0] incr_unshuffled_addr, logic unsigned [14:0] default_addr);
  if (rst_pw_addr) begin
    return rst_addr;
  end

  if (incr_pw_addr) begin
    if (shuffle_en) begin
      return incr_shuffled_addr;
    end

    return incr_unshuffled_addr;
  end

  return default_addr;
endfunction


localparam chunk_count_reg_idx_0 = 32'd4 * ((32'd22 - 32'd5) - 32'd3);
localparam buf_wrptr_reg_idx_0 = 32'd2 * ((32'd22 - 32'd5) - 32'd1);
localparam chunk_count_reg_idx_1 = 32'd4 * 32'd8;
localparam buf_wrptr_reg_idx_1 = 32'd2 * (32'd3 - 32'd1);
localparam buf_wrptr_reg_idx_2 = 32'd2 * (32'd3 - 32'd1);

function logic unsigned [7:0][6:0] getTwiddleRandOffsets(logic unsigned [79:0] chunk_count_reg, logic unsigned [43:0] buf_wrptr_reg);
  return '{ 0: (32'd4 * chunk_count_reg[(chunk_count_reg_idx_0 + 32'd3):chunk_count_reg_idx_0]) + buf_wrptr_reg[(buf_wrptr_reg_idx_0 + 32'd1):buf_wrptr_reg_idx_0], 1: ((chunk_count_reg[(chunk_count_reg_idx_1 + 32'd3):chunk_count_reg_idx_1] & 32'h3) * 32'd4) + buf_wrptr_reg[(buf_wrptr_reg_idx_1 + 32'd1):buf_wrptr_reg_idx_1], 2: buf_wrptr_reg[(buf_wrptr_reg_idx_2 + 32'd1):buf_wrptr_reg_idx_2], 3: 7'd0, 4: 7'd0, 5: 7'd0, 6: 7'd0, 7: 7'd0 };
endfunction


function logic unsigned [6:0] getTwiddleIncrAddr(logic shuffle_en, logic unsigned [2:0] rounds_count, logic unsigned [7:0][6:0] rand_offsets, logic unsigned [7:0][6:0] end_addrs, logic unsigned [6:0] default_addr);
  if (shuffle_en) begin
    return rand_offsets[rounds_count];
  end

  if (default_addr == end_addrs[rounds_count]) begin
    return 7'd0;
  end

  return 7'(default_addr + 64'd1);
endfunction


function logic unsigned [6:0] getTwiddleAddrReg(logic incr, logic rst, logic unsigned [6:0] incr_addr, logic unsigned [6:0] default_addr);
  if (incr) begin
    return incr_addr;
  end

  if (rst) begin
    return 7'd0;
  end

  return default_addr;
endfunction


function logic unsigned [6:0] getRdValidCount(e_PwmInttReadStatesType read_state, logic unsigned [2:0] rounds_count, logic sampler_valid, logic unsigned [6:0] rd_valid_count);
  logic rst_rd_valid_count; // @ ntt_ctrl_pwm_intt.h:200:3
  logic rd_data_valid;      // @ ntt_ctrl_pwm_intt.h:202:3

  rst_rd_valid_count = (read_state == PwmInttReadIdle) || (read_state == PwmInttReadStage);
  rd_data_valid = (rounds_count > 64'd0) ? (read_state == PwmInttReadExec) : sampler_valid;
  return rst_rd_valid_count ? 7'd0 : (rd_data_valid ? 7'(rd_valid_count + 64'd1) : rd_valid_count);
endfunction


function logic unsigned [1:0] getIndexCount(e_PwmInttReadStatesType read_state, logic unsigned [2:0] rounds_count, logic sampler_valid, logic unsigned [1:0] index_count);
  if ((read_state == PwmInttReadExec) && ((rounds_count > 64'd0) || sampler_valid)) begin
    return 2'(index_count + 64'd1);
  end

  return index_count;
endfunction


function logic unsigned [79:0] concatChunkCountReg2(logic unsigned [79:0] op_0, logic signed [31:0] offset_0, logic unsigned [79:0] op_1);
  logic unsigned [79:0] result; // @ ntt_ctrl_pwm_intt.h:220:3

  result = 80'd0;
  result = op_0 << offset_0;
  result = result | op_1;
  return result;
endfunction


function logic unsigned [79:0] getChunkCountReg(e_PwmInttReadStatesType read_state, logic butterfly_ready, logic unsigned [2:0] rounds_count, logic unsigned [3:0] chunk_count, logic unsigned [79:0] chunk_count_reg);
  if (rounds_count == 64'd0) begin
    return concatChunkCountReg2(chunk_count, 32'd80 - 32'd4, chunk_count_reg[(32'd80 - 32'd1):32'd4]);
  end

  if (butterfly_ready || ((rounds_count > 64'd0) && (read_state == PwmInttReadExec))) begin
    return concatChunkCountReg2(chunk_count, 32'd4 * 32'd8, chunk_count_reg[((32'd4 * 32'd8) + 32'd3):32'd4]);
  end

  return chunk_count_reg;
endfunction


function logic unsigned [43:0] concatBufWrptrReg2(logic unsigned [43:0] op_0, logic signed [31:0] offset_0, logic unsigned [43:0] op_1);
  logic unsigned [43:0] result; // @ ntt_ctrl_pwm_intt.h:247:3

  result = 44'd0;
  result = op_0 << offset_0;
  result = result | op_1;
  return result;
endfunction


function logic unsigned [43:0] getBufWrptrReg(e_PwmInttReadStatesType read_state, logic butterfly_ready, logic unsigned [2:0] rounds_count, logic unsigned [1:0] mem_rd_index_ofst, logic unsigned [43:0] buf_wrptr_reg);
  if ((rounds_count > 64'd0) && ((read_state == PwmInttReadExec) || butterfly_ready)) begin
    return concatBufWrptrReg2(mem_rd_index_ofst, (32'd2 * 32'd3) - 32'd2, buf_wrptr_reg[((32'd2 * 32'd3) - 32'd1):32'd2]);
  end

  if (rounds_count == 64'd0) begin
    return concatBufWrptrReg2(mem_rd_index_ofst, 32'd44 - 32'd2, buf_wrptr_reg[(32'd44 - 32'd1):32'd2]);
  end

  return 44'd0;
endfunction


function logic unsigned [1:0] getMemRdIndexOfst(logic unsigned [1:0] index_count, logic unsigned [1:0] index_rand_offset);
  return 2'(index_count + index_rand_offset);
endfunction


function logic unsigned [14:0] wraparoundMemAddr(logic unsigned [15:0] new_addr, logic unsigned [14:0] base_addr);
  if (new_addr > (base_addr + 64'd63)) begin
    return 15'(new_addr - 64'd63);
  end

  return 15'(new_addr);
endfunction


function logic unsigned [1:0] getBufWrptr(logic shuffle_en, logic buf_wren_intt, logic unsigned [1:0] buf_wrptr, logic unsigned [43:0] buf_wrptr_reg);
  if (buf_wren_intt) begin
    if (shuffle_en) begin
      return buf_wrptr_reg[32'd1:32'd0];
    end

    return 2'(buf_wrptr + 64'd1);
  end

  return buf_wrptr;
endfunction


function logic unsigned [14:0] getMemWrAddr(logic rst_wr_addr, logic incr_mem_wr_addr, logic shuffle_en, st_NttMemBaseAddrs ntt_mem_base_addrs, logic unsigned [3:0] rounds_count, logic unsigned [3:0] chunk_rand_offset, logic unsigned [14:0] mem_wr_addr, logic unsigned [14:0] wr_addr_step);
  logic unsigned [14:0] mem_wr_base_addr; // @ ntt_ctrl_pwm_intt.h:299:3
  logic last_wr_addr;                     // @ ntt_ctrl_pwm_intt.h:303:3
  logic unsigned [15:0] mem_wr_addr_nxt;  // @ ntt_ctrl_pwm_intt.h:305:3

  mem_wr_base_addr = ((rounds_count & 64'd1) == 64'd1) ? ntt_mem_base_addrs.dest_base_addr : ntt_mem_base_addrs.interim_base_addr;
  last_wr_addr = mem_wr_addr == (mem_wr_base_addr + 64'd63);
  mem_wr_addr_nxt = 16'(mem_wr_addr + wr_addr_step);

  if (rst_wr_addr) begin
    if (shuffle_en) begin
      return 15'(mem_wr_base_addr + chunk_rand_offset);
    end

    return mem_wr_base_addr;
  end

  if (incr_mem_wr_addr) begin
    if (shuffle_en && last_wr_addr) begin
      return mem_wr_base_addr;
    end

    return wraparoundMemAddr(mem_wr_addr_nxt, mem_wr_base_addr);
  end

  return mem_wr_addr;
endfunction


function logic unsigned [2:0] getRoundsCount(logic rst_rounds, logic incr_rounds, logic unsigned [2:0] rounds_count);
  if (rst_rounds) begin
    return 3'd0;
  end

  if (incr_rounds) begin
    return 3'(rounds_count + 64'd1);
  end

  if (rounds_count == 64'd4) begin
    return 3'd0;
  end

  return rounds_count;
endfunction


endpackage
