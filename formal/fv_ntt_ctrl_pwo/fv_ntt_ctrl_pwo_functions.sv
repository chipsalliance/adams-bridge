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


package fv_ntt_ctrl_pwo_functions;


function automatic logic unsigned [1:0] get_mem_rd_index_ofst(logic unsigned [1:0] index_count, logic unsigned [1:0] index_rand_offset);
  return 2'(index_count + index_rand_offset);
endfunction


function automatic logic unsigned [3:0] get_chunk_rand_offset_from_random(logic unsigned [5:0] random);
  return random[5:2];
endfunction

function automatic logic unsigned [1:0] get_index_rand_offset_from_random(logic unsigned [5:0] random);
  return random[1:0];
endfunction

function automatic logic unsigned [21:0] get_buf_rdptr_reg_next_pairwm(logic unsigned [21:0] buf_rdptr_reg, logic unsigned [1:0] mem_rd_index_ofst);
  return { mem_rd_index_ofst, buf_rdptr_reg[21:2] };
endfunction

function automatic logic unsigned [13:0] get_buf_rdptr_reg_next_nonpairwm(logic unsigned [21:0] buf_rdptr_reg, logic unsigned [1:0] mem_rd_index_ofst);
  return { mem_rd_index_ofst, buf_rdptr_reg[13:2] };
endfunction

function automatic logic unsigned [43:0] get_chunk_count_reg_next_pairwm(logic unsigned [43:0] chunk_count_reg, logic unsigned [3:0] chunk_count);
  return { chunk_count, chunk_count_reg[43:4] };
endfunction

function automatic logic unsigned [27:0] get_chunk_count_reg_next_nonpairwm(logic unsigned [43:0] chunk_count_reg, logic unsigned [3:0] chunk_count);
  return { chunk_count, chunk_count_reg[27:4] };
endfunction


function automatic logic unsigned [14:0] get_pw_addr_rst(logic shuffle_en, logic unsigned [3:0] chunk_rand_offset, logic unsigned [14:0] base_addr);
  if (shuffle_en) begin
    return (64'd4 * chunk_rand_offset) + base_addr;
  end

  return base_addr;
endfunction


function automatic logic unsigned [14:0] get_pw_addr_incr_abc_wr(logic shuffle_en, logic unsigned [14:0] addr_nxt, logic unsigned [14:0] current_addr, logic unsigned [14:0] addr_step);
  if (shuffle_en) begin
    return addr_nxt;
  end

  return 15'(current_addr + addr_step);
endfunction


function automatic logic unsigned [14:0] get_pw_addr_abc_wr(logic rst_addr, logic incr_addr, logic unsigned [14:0] addr_rst, logic unsigned [14:0] addr_incr, logic unsigned [14:0] addr_default);
  if (rst_addr) begin
    return addr_rst;
  end

  if (incr_addr) begin
    return addr_incr;
  end

  return addr_default;
endfunction


function automatic logic unsigned [14:0] get_pw_addr_crd(logic shuffle_en, logic mode, logic accumulate, logic rst_pw_addr, logic incr_pw_rd_addr, logic unsigned [14:0] addr_rst, logic unsigned [14:0] addr_nxt, logic unsigned [14:0] addr_default, logic unsigned [14:0] addr_step);
  if (rst_pw_addr) begin
    return addr_rst;
  end
if (mode && accumulate) begin
    if(incr_pw_rd_addr)
    begin
    if (shuffle_en)begin
        return addr_nxt;
    end
      return addr_default + addr_step;
end
  return addr_default;
end
  return 15'd0;
endfunction


function automatic logic unsigned [14:0] get_pw_addr_nxt(logic unsigned [14:0] base_addr, logic unsigned [3:0] chunk_count, logic unsigned [14:0] step, logic unsigned [14:0] offset);
  return 15'((base_addr + (64'd4 * chunk_count)) + (step * offset));
endfunction

function automatic logic unsigned [14:0] get_pw_addr_wr_nxt(logic unsigned [14:0] base_addr, logic unsigned [43:0] chunk_count_reg, logic unsigned [14:0] step,
 logic unsigned [21:0] buf_rdptr_reg, logic accumulate, logic unsigned [2:0] mode);
  if (mode == 3'd3 || mode == 3'd4) begin

    return base_addr + 4 * chunk_count_reg[15:12]
      + step * buf_rdptr_reg[7:6];
  end
  else if (mode == 3'd2) begin
    if (accumulate) begin
      return base_addr + 4 * chunk_count_reg[7:4]
        + step * buf_rdptr_reg[3:2];
    end

    return base_addr + 4 * chunk_count_reg[11:8]
      + step * buf_rdptr_reg[5:4];
  end

  if (accumulate) begin
    return base_addr + 4 * chunk_count_reg[15:12]
      + step * buf_rdptr_reg[7:6];
  end

  return base_addr + 4 * chunk_count_reg[19:16]
    + step * buf_rdptr_reg[9:8];

endfunction

function automatic logic unsigned [14:0] get_pw_addr_cwr(logic rst_pw_addr, logic incr_pw_wr_addr, logic shuffle_en, logic unsigned [3:0] chunk_rand_offset,
  logic unsigned [14:0] pw_base_addr_c, logic unsigned [14:0] shuffled_pw_mem_wr_addr_c_nxt, logic unsigned [14:0] pw_mem_wr_addr_c);
  if (rst_pw_addr) begin
    if (shuffle_en) begin
      return 4 * chunk_rand_offset + pw_base_addr_c;
    end

    return pw_base_addr_c;
  end

  if (incr_pw_wr_addr) begin
    if (shuffle_en) begin
      return shuffled_pw_mem_wr_addr_c_nxt;
    end

    return pw_mem_wr_addr_c + 1;
  end

  return pw_mem_wr_addr_c;

endfunction

// Mirrors ntt_ctrl_pwo.h's get_twiddle_rand_offsets: rounds_count is only ever 0 or 1 in
// this unit, so only entries 0 and 1 are non-zero. buf_rdptr_int (pairwm's buf_count
// term) and buf_wrptr_reg (the non-pairwm term) are both provably 0 in this unit and
// dropped -- see the model's comments on assume_ntt_mode (gs_mode/ct_mode always 0)
// and the buf_wren/pwo_mode tie-off.
function automatic logic unsigned [7:0][6:0] get_twiddle_rand_offsets(logic unsigned [43:0] chunk_count_reg, logic unsigned [3:0] chunk_count, logic unsigned [1:0] buf_count, logic pairwm_mode);
  return '{ 0: pairwm_mode ? 7'((64'd4 * chunk_count) + buf_count) : 7'(64'd4 * chunk_count_reg[27:24]), 1: 7'(64'd4 * (chunk_count_reg[27:24] & 4'h3)), 2: 7'd0, 3: 7'd0, 4: 7'd0, 5: 7'd0, 6: 7'd0, 7: 7'd0 };
endfunction

function automatic logic unsigned [6:0] get_twiddle_addr_reg(logic incr, logic rst, logic unsigned [6:0] incr_addr, logic unsigned [6:0] default_addr);
  if (incr) begin
    return incr_addr;
  end

  if (rst) begin
    return 7'd0;
  end

  return default_addr;
endfunction

function automatic logic unsigned [6:0] get_twiddle_incr_addr(logic shuffle_en, logic unsigned [2:0] rounds_count, logic unsigned [7:0][6:0] rand_offsets, logic unsigned [7:0][6:0] end_addrs, logic unsigned [6:0] default_addr);
  if (shuffle_en) begin
    return rand_offsets[rounds_count];
  end

  if (default_addr == end_addrs[rounds_count]) begin
    return 7'd0;
  end

  return 7'(default_addr + 64'd1);
endfunction

function automatic logic unsigned [6:0] get_twiddle_addr_out(logic shuffle_en, logic pairwm_mode, logic unsigned [2:0] rounds_count, logic unsigned [6:0] twiddle_addr_int,
  logic unsigned [7:0][6:0] twiddle_rand_offset_array, logic unsigned [7:0][6:0] twiddle_offset_array,
  logic unsigned [1:0] index_count, logic unsigned [1:0] index_rand_offset, logic unsigned [6:0] twiddle_addr_reg_d2);
  return (shuffle_en && pairwm_mode)
      ? twiddle_addr_reg_d2
      : (!shuffle_en ? 7'(twiddle_addr_int + twiddle_offset_array[rounds_count])
        : (shuffle_en && pairwm_mode) ? 7'(twiddle_rand_offset_array[rounds_count] + 7'(2'(index_count + index_rand_offset)) + twiddle_offset_array[rounds_count])
        : 7'(twiddle_rand_offset_array[rounds_count] + twiddle_offset_array[rounds_count]));
endfunction

endpackage
