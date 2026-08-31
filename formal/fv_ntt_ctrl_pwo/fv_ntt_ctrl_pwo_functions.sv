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
// | Created on 13.03.2025 at 09:44                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


package fv_ntt_ctrl_pwo_functions;


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


function logic unsigned [14:0] getPwAddrCrd(logic shuffle_en, logic accumulate, logic rst_pw_addr, logic incr_pw_rd_addr, logic unsigned [14:0] addr_rst, logic unsigned [14:0] addr_nxt, logic unsigned [14:0] addr_default, logic unsigned [14:0] addr_step);
  if (rst_pw_addr) begin
    return addr_rst;
  end

  if (incr_pw_rd_addr) begin
    if (shuffle_en) begin
      if (accumulate) begin
        return addr_nxt;
      end

      return 15'd0;
    end

    if (accumulate) begin
      return 15'(addr_default + addr_step);
    end

    return 15'd0;
  end

  return addr_default;
endfunction


function logic unsigned [14:0] getPwAddrNxt(logic unsigned [14:0] base_addr, logic unsigned [3:0] chunk_count, logic unsigned [14:0] step, logic unsigned [14:0] offset);
  return 15'((base_addr + (64'd4 * chunk_count)) + (step * offset));
endfunction


endpackage
