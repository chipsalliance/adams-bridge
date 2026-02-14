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


package ntt_ctrl_gs_mlkem_functions;

import ntt_ctrl_gs_mlkem_pkg::*;

function logic unsigned [14:0] incr_addr(logic unsigned [14:0] addr, logic unsigned [14:0] step, logic unsigned [14:0] base);
  logic unsigned [15:0] new_addr; // @ ntt_ctrl_gs_mlkem.h:51:3

  new_addr = 16'(addr + step);

  if (new_addr > (base + 64'd63)) begin
    new_addr = new_addr - 64'd63;
  end

  return 15'(new_addr);
endfunction


function logic unsigned [14:0] get_rd_addr_shuffle(logic unsigned [14:0] addr, logic unsigned [14:0] step, logic unsigned [14:0] base, logic unsigned [3:0] chunk_count, logic unsigned [1:0] mem_rd_index_ofst);
  logic unsigned [15:0] new_addr; // @ ntt_ctrl_gs_mlkem.h:65:3

  new_addr = 16'(((64'd4 * chunk_count) + (step * mem_rd_index_ofst)) + base);

  if (new_addr > (base + 64'd63)) begin
    new_addr = new_addr - 64'd63;
  end

  return 15'(new_addr);
endfunction


function logic unsigned [6:0] getTwiddleAddrIncr(logic shuffle_en, logic unsigned [6:0] twiddle_rand_offset, logic unsigned [6:0] current_addr, logic unsigned [7:0][6:0] twiddle_end_addrs, logic unsigned [2:0] rounds_count);
  if (shuffle_en) begin
    return twiddle_rand_offset;
  end

  if (current_addr == twiddle_end_addrs[rounds_count]) begin
    return 7'd0;
  end

  return 7'(current_addr + 64'd1);
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


function logic unsigned [14:0] getMemRdAddrBase(logic unsigned [2:0] rounds_count, st_NttBaseAddrs base_addrs);
  if (rounds_count == 64'd0) begin
    return base_addrs.src_base_addr;
  end

  if ((rounds_count & 64'd1) != 64'd0) begin
    return base_addrs.interim_base_addr;
  end

  return base_addrs.dest_base_addr;
endfunction


function logic unsigned [1:0] getBufWrptr(logic shuffle_en, logic mlkem, logic buf_wren_intt, logic unsigned [1:0] buf_wrptr, logic unsigned [25:0] buf_wrptr_reg);
  if (buf_wren_intt) begin
    if (shuffle_en) begin
      if (mlkem) begin
        return buf_wrptr_reg[((32'd2 * (32'd13 - 32'd9)) + 32'd1):(32'd2 * (32'd13 - 32'd9))];
      end

      return buf_wrptr_reg[32'd1:32'd0];
    end

    return 2'(buf_wrptr + 64'd1);
  end

  return buf_wrptr;
endfunction


function logic unsigned [6:0] getWrValidCount(logic buf0_valid, e_GsWriteStatesType write_state, logic unsigned [6:0] wr_valid_count);
  if (((buf0_valid && (wr_valid_count > 64'h40)) || (write_state == GsWriteIdle)) || (write_state == GsWriteStage)) begin
    return 7'd0;
  end

  if (buf0_valid) begin
    return 7'(wr_valid_count + 64'd4);
  end

  return wr_valid_count;
endfunction


function logic unsigned [14:0] getMemWrAddrBase(logic unsigned [2:0] rounds_count, st_NttBaseAddrs base_addrs);
  if ((rounds_count & 64'd1) != 64'd0) begin
    return base_addrs.dest_base_addr;
  end

  return base_addrs.interim_base_addr;
endfunction


endpackage
