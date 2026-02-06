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


package ntt_ctrl_pwo_pairwm_functions;


function logic unsigned [1:0] getMemRdIndexOfst(logic unsigned [1:0] index_count, logic unsigned [1:0] index_rand_offset);
  return 2'(index_count + index_rand_offset);
endfunction


function logic unsigned [14:0] getPwAddrRst(logic shuffle_en, logic unsigned [3:0] chunk_rand_offset, logic unsigned [14:0] base_addr);
  if (shuffle_en) begin
    return 15'((64'd4 * chunk_rand_offset) + base_addr);
  end

  return base_addr;
endfunction


function logic unsigned [14:0] getPwAddrIncrAbcWr(logic shuffle_en, logic unsigned [14:0] addr_nxt, logic unsigned [14:0] current_addr, logic unsigned [14:0] addr_step);
  if (shuffle_en) begin
    return addr_nxt;
  end

  return 15'(current_addr + addr_step);
endfunction


function logic unsigned [14:0] getPwAddrAbcWr(logic rst_addr, logic incr_addr, logic unsigned [14:0] addr_rst, logic unsigned [14:0] addr_incr, logic unsigned [14:0] addr_default);
  if (rst_addr) begin
    return addr_rst;
  end

  if (incr_addr) begin
    return addr_incr;
  end

  return addr_default;
endfunction


function logic unsigned [14:0] getPwAddrCrd(logic rst_pw_addr, logic shuffle_en, logic pwm_mode, logic pairwm_mode, logic mlkem, logic accumulate, logic masking_en, logic unsigned [211:0] incr_pw_rd_addr_reg, logic incr_pw_rd_addr, logic unsigned [3:0] chunk_rand_offset, logic unsigned [14:0] pw_base_addr_c, logic unsigned [14:0] pw_mem_rd_addr_c_nxt, logic unsigned [14:0] pw_mem_rd_addr_c);
  if (rst_pw_addr) begin
    return shuffle_en ? 15'(pw_base_addr_c + (64'd4 * chunk_rand_offset)) : pw_base_addr_c;
  end

  if ((pwm_mode || pairwm_mode) && accumulate) begin
    if ((masking_en && ((mlkem ? (shuffle_en ? incr_pw_rd_addr_reg[32'd211 - (32'd23 - 32'd6)] : incr_pw_rd_addr_reg[32'd211 - ((32'd23 - 32'd6) + 32'd1)]) : incr_pw_rd_addr_reg[32'd0]) != 64'd0)) || ((!masking_en) && incr_pw_rd_addr)) begin
      return pw_mem_rd_addr_c_nxt;
    end

    return pw_mem_rd_addr_c;
  end

  return 15'd0;
endfunction


function logic unsigned [14:0] getMaskedShuffledPwmMemWrAddrCnxtAccumulate(logic unsigned [14:0] pw_base_addr_c, logic unsigned [1087:0] chunk_count_reg, logic unsigned [1:0] masked_pwm_buf_rdptr_d3);
  return (pw_base_addr_c + (32'd4 * chunk_count_reg[((32'd4 * ((32'd271 - 32'd264) - 32'd3)) + 32'd3):(32'd4 * ((32'd271 - 32'd264) - 32'd3))])) + (64'd1 * masked_pwm_buf_rdptr_d3);
endfunction


function logic unsigned [14:0] getMlkemMaskedShuffledPwmMemWrAddrCnxtAccumulate(logic unsigned [14:0] pw_base_addr_c, logic unsigned [1087:0] chunk_count_reg, logic unsigned [1:0] masked_pwm_buf_rdptr_d3);
  return (pw_base_addr_c + (32'd4 * chunk_count_reg[((32'd4 * 32'd0) + 32'd3):(32'd4 * 32'd0)])) + (64'd1 * masked_pwm_buf_rdptr_d3);
endfunction


function logic unsigned [14:0] getMaskedShuffledPwmMemWrAddrCnxt(logic unsigned [14:0] pw_base_addr_c, logic unsigned [1087:0] chunk_count_reg, logic unsigned [1:0] masked_pwm_buf_rdptr_d2);
  return (pw_base_addr_c + (32'd4 * chunk_count_reg[((32'd4 * ((32'd271 - 32'd211) - 32'd2)) + 32'd3):(32'd4 * ((32'd271 - 32'd211) - 32'd2))])) + (64'd1 * masked_pwm_buf_rdptr_d2);
endfunction


function logic unsigned [14:0] getMlkemMaskedShuffledPwmMemWrAddrCnxt(logic unsigned [14:0] pw_base_addr_c, logic unsigned [1087:0] chunk_count_reg, logic unsigned [1:0] masked_pwm_buf_rdptr_d3);
  return (pw_base_addr_c + (32'd4 * chunk_count_reg[((32'd4 * 32'd0) + 32'd3):(32'd4 * 32'd0)])) + (64'd1 * masked_pwm_buf_rdptr_d3);
endfunction


function logic unsigned [14:0] getShuffledPwMemWrAddrCnxt(logic pwm_mode, logic pwa_mode, logic pws_mode, logic pairwm_mode, logic accumulate, logic unsigned [14:0] pw_base_addr_c, logic unsigned [1087:0] chunk_count_reg, logic unsigned [547:0] buf_rdptr_reg);
  if (pwm_mode && accumulate) begin
    return (pw_base_addr_c + (15'd4 * chunk_count_reg[((32'd4 * (32'd5 - 32'd2)) + 32'd3):(32'd4 * (32'd5 - 32'd2))])) + (15'd1 * buf_rdptr_reg[((32'd2 * (32'd5 - 32'd2)) + 32'd1):(32'd2 * (32'd5 - 32'd2))]);
  end

  if (pwm_mode) begin
    return (pw_base_addr_c + (15'd4 * chunk_count_reg[((32'd4 * (32'd5 - 32'd1)) + 32'd3):(32'd4 * (32'd5 - 32'd1))])) + (15'd1 * buf_rdptr_reg[((32'd2 * (32'd5 - 32'd1)) + 32'd1):(32'd2 * (32'd5 - 32'd1))]);
  end

  if (pairwm_mode && accumulate) begin
    return (pw_base_addr_c + (15'd4 * chunk_count_reg[((32'd4 * (32'd4 - 32'd1)) + 32'd3):(32'd4 * (32'd4 - 32'd1))])) + (15'd1 * buf_rdptr_reg[((32'd2 * (32'd4 - 32'd1)) + 32'd1):(32'd2 * (32'd4 - 32'd1))]);
  end

  if (pairwm_mode) begin
    return (pw_base_addr_c + (15'd4 * chunk_count_reg[((32'd4 * 32'd4) + 32'd3):(32'd4 * 32'd4)])) + (15'd1 * buf_rdptr_reg[((32'd2 * 32'd4) + 32'd1):(32'd2 * 32'd4)]);
  end

  if (pwa_mode || pws_mode) begin
    return (pw_base_addr_c + (15'd4 * chunk_count_reg[32'd31:32'd28])) + (15'd1 * buf_rdptr_reg[32'd15:32'd14]);
  end

  return 15'd0;
endfunction


function logic unsigned [14:0] getPwAddrCwr(logic rst_pw_addr, logic incr_pw_wr_addr, logic shuffle_en, logic masking_en, logic accumulate, logic mlkem, logic unsigned [3:0] chunk_rand_offset, logic unsigned [14:0] pw_base_addr_c, logic unsigned [14:0] masked_shuffled_pw_mem_wr_addr_c_nxt_accumulate, logic unsigned [14:0] mlkem_masked_shuffled_pw_mem_wr_addr_c_nxt_accumulate, logic unsigned [14:0] masked_shuffled_pw_mem_wr_addr_c_nxt, logic unsigned [14:0] mlkem_masked_shuffled_pw_mem_wr_addr_c_nxt, logic unsigned [14:0] shuffled_pw_mem_wr_addr_c_nxt, logic unsigned [14:0] pw_mem_wr_addr_c);
  if (rst_pw_addr) begin
    if (shuffle_en) begin
      return 15'((64'd4 * chunk_rand_offset) + pw_base_addr_c);
    end

    return pw_base_addr_c;
  end

  if (incr_pw_wr_addr) begin
    if (masking_en && shuffle_en) begin
      if (accumulate) begin
        if (mlkem) begin
          return mlkem_masked_shuffled_pw_mem_wr_addr_c_nxt_accumulate;
        end

        return masked_shuffled_pw_mem_wr_addr_c_nxt_accumulate;
      end

      if (mlkem) begin
        return mlkem_masked_shuffled_pw_mem_wr_addr_c_nxt;
      end

      return masked_shuffled_pw_mem_wr_addr_c_nxt;
    end

    if (shuffle_en) begin
      return shuffled_pw_mem_wr_addr_c_nxt;
    end

    return 15'(pw_mem_wr_addr_c + 64'd1);
  end

  return pw_mem_wr_addr_c;
endfunction


function logic unsigned [14:0] getPwAddrNxt(logic unsigned [14:0] base_addr, logic unsigned [3:0] chunk_count, logic unsigned [14:0] step, logic unsigned [14:0] offset);
  return 15'((base_addr + (64'd4 * chunk_count)) + (step * offset));
endfunction


function logic unsigned [14:0] getPwAddrCnxt(logic pwm_mode, logic pairwm_mode, logic mlkem, logic accumulate, logic shuffle_en, logic masking_en, logic unsigned [14:0] rd_addr_c, logic unsigned [14:0] masked_shuffled_pw_mem_rd_addr_c_nxt_accumulate, logic unsigned [14:0] mlkem_masked_shuffled_pw_mem_rd_addr_c_nxt_accumulate, logic unsigned [14:0] shuffled_pw_mem_rd_addr_c_nxt_accumulate);
  if ((pwm_mode || pairwm_mode) && accumulate) begin
    if (shuffle_en) begin
      if (masking_en) begin
        if (mlkem) begin
          return mlkem_masked_shuffled_pw_mem_rd_addr_c_nxt_accumulate;
        end

        return masked_shuffled_pw_mem_rd_addr_c_nxt_accumulate;
      end

      return shuffled_pw_mem_rd_addr_c_nxt_accumulate;
    end

    return 15'(rd_addr_c + 64'd1);
  end

  return 15'd0;
endfunction


function logic unsigned [547:0] getBufRdptrReg(logic masking_en, logic butterfly_ready, logic accumulate, logic incr_pw_rd_addr, logic pwm_mode, logic pairwm_mode, logic masked_pwm_exec_in_progres, logic unsigned [547:0] buf_rdptr_reg, logic unsigned [1:0] mem_rd_index_ofst);
  logic unsigned [547:0] new_buf_rdptr_reg; // @ ntt_ctrl_pwo_pairwm.h:263:3

  new_buf_rdptr_reg = 548'd0;

  if ((!masking_en) && (butterfly_ready || incr_pw_rd_addr)) begin
    new_buf_rdptr_reg = (mem_rd_index_ofst << (32'd2 * 32'd10)) | buf_rdptr_reg[((32'd2 * 32'd10) + 32'd1):32'd2];
  end else if ((pwm_mode && masking_en) && masked_pwm_exec_in_progres) begin
    if (accumulate) begin
      new_buf_rdptr_reg = (mem_rd_index_ofst << (32'd2 * 32'd264)) | buf_rdptr_reg[((32'd2 * 32'd264) + 32'd1):32'd2];
    end else begin
      new_buf_rdptr_reg = (mem_rd_index_ofst << (32'd2 * 32'd211)) | buf_rdptr_reg[((32'd2 * 32'd211) + 32'd1):32'd2];
    end
  end else if ((pairwm_mode && masking_en) && masked_pwm_exec_in_progres) begin
    if (accumulate) begin
      new_buf_rdptr_reg = (mem_rd_index_ofst << (32'd2 * 32'd24)) | buf_rdptr_reg[((32'd2 * 32'd24) + 32'd1):32'd2];
    end else begin
      new_buf_rdptr_reg = (mem_rd_index_ofst << (32'd2 * 32'd23)) | buf_rdptr_reg[((32'd2 * 32'd23) + 32'd1):32'd2];
    end
  end else begin
    new_buf_rdptr_reg = 32'd0;
  end

  return new_buf_rdptr_reg;
endfunction


function logic unsigned [211:0] getIncrPwRdAddrReg(logic masking_en, logic pwm_mode, logic pairwm_mode, logic unsigned [211:0] incr_pw_rd_addr_reg, logic incr_pw_rd_addr);
  logic unsigned [211:0] result; // @ ntt_ctrl_pwo_pairwm.h:295:3

  result = 212'd0;

  if (masking_en && (pwm_mode || pairwm_mode)) begin
    result = incr_pw_rd_addr_reg[(32'd212 - 32'd1):32'd1];

    if (incr_pw_rd_addr) begin
      result = result | (212'd1 << (32'd212 - 32'd1));
    end else begin
      result = result | (212'd0 << (32'd212 - 32'd1));
    end
  end else begin
    result = incr_pw_rd_addr_reg;
  end

  return result;
endfunction


function logic unsigned [1087:0] getChunkCountReg(logic pwm_mode, logic pairwm_mode, logic accumulate, logic masking_en, logic masked_pwm_exec_in_progress, logic butterfly_ready, logic incr_pw_rd_addr, logic unsigned [1087:0] chunk_count_reg, logic unsigned [3:0] chunk_count);
  logic unsigned [1087:0] result; // @ ntt_ctrl_pwo_pairwm.h:315:3

  result = 1088'd0;

  if ((pwm_mode && masking_en) && masked_pwm_exec_in_progress) begin
    result = (chunk_count << (32'd4 * (32'd274 - 32'd3))) | chunk_count_reg[((32'd4 * (32'd274 - 32'd3)) + 32'd3):32'd4];
  end else if ((pairwm_mode && masking_en) && masked_pwm_exec_in_progress) begin
    if (accumulate) begin
      result = (chunk_count << (32'd4 * (32'd24 + 32'd3))) | chunk_count_reg[((32'd4 * (32'd24 + 32'd3)) + 32'd3):32'd4];
    end else begin
      result = (chunk_count << (32'd4 * (32'd23 + 32'd3))) | chunk_count_reg[((32'd4 * (32'd23 + 32'd3)) + 32'd3):32'd4];
    end
  end else if (butterfly_ready || incr_pw_rd_addr) begin
    result = (chunk_count << (32'd4 * 32'd10)) | chunk_count_reg[((32'd4 * 32'd10) + 32'd3):32'd4];
  end else begin
    result = chunk_count_reg;
  end

  return result;
endfunction


function logic unsigned [211:0] getPwRdenFsmReg(logic unsigned [211:0] pw_rden_fsm_reg, logic pw_rden_fsm);
  return (unsigned'(pw_rden_fsm ? 32'd1 : 32'd0) << (32'd212 - 32'd1)) | pw_rden_fsm_reg[(32'd212 - 32'd1):32'd1];
endfunction


function logic unsigned [7:0][6:0] getTwiddleRandOffsets(logic unsigned [1087:0] chunk_count_reg, logic unsigned [3:0] chunk_count, logic unsigned [1:0] buf_count, logic pairwm_mode);
  return '{ 0: pairwm_mode ? 7'((chunk_count * 64'd4) + buf_count) : 7'((chunk_count_reg[32'd43:32'd40] * 64'd4) + 64'd0), 1: 7'(((chunk_count_reg[32'd43:32'd40] & 64'h3) * 64'd4) + 64'd0), 2: 7'd0, 3: 7'd0, 4: 7'd0, 5: 7'd0, 6: 7'd0, 7: 7'd0 };
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


function logic unsigned [6:0] getTwiddleIncrAddr(logic shuffle_en, logic unsigned [2:0] rounds_count, logic unsigned [7:0][6:0] rand_offsets, logic unsigned [7:0][6:0] end_addrs, logic unsigned [6:0] default_addr);
  if (shuffle_en) begin
    return rand_offsets[rounds_count];
  end

  if (default_addr == end_addrs[rounds_count]) begin
    return 7'd0;
  end

  return 7'(default_addr + 64'd1);
endfunction


endpackage
