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
// | Created on 18.02.2025 at 14:01                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


package fv_norm_check_top_functions;


function logic return_invalid(logic unsigned [1:0] mode, logic unsigned [22:0] operand);
  logic unsigned [22:0] bound;
  logic unsigned [22:0] q_minus_bound;
  logic invalid;
  localparam  MLDSA_Q = 8380417; 

  case (mode)
    2'd0: bound = 23'h7FF88;
    2'd1: bound = 23'h3FE88;
    2'd2: bound = 23'h3FF00;
    default: bound = 23'd0;
  endcase

  q_minus_bound = MLDSA_Q - bound; 

  invalid = (operand >= bound) & (operand <= q_minus_bound);
  return invalid;
endfunction



function logic unsigned [13:0] return_idle_mem_rd_req(logic unsigned [4:0] randomness, logic unsigned [0:0] randomness_lsb);
  logic unsigned [13:0] mem_rd_addr; // @ norm_check_top.h:97:13

  mem_rd_addr = 14'd0;
  mem_rd_addr[32'd13:32'd6] = 8'd0;
  mem_rd_addr[32'd5:32'd1] = randomness;
  mem_rd_addr[32'd0:32'd0] = randomness_lsb;
  return mem_rd_addr;
endfunction


function logic unsigned [13:0] return_read_mem_mem_rd_req(logic unsigned [13:0] mem_rd_addr_0, logic unsigned [0:0] randomness_lsb);
  logic unsigned [13:0] mem_rd_addr; // @ norm_check_top.h:110:9

  mem_rd_addr = 14'd0;
  mem_rd_addr[32'd13:32'd1] = mem_rd_addr_0[32'd13:32'd1];
  mem_rd_addr[32'd0:32'd0] = ~randomness_lsb;
  return mem_rd_addr;
endfunction


function logic unsigned [13:0] return_wait_mem_mem_rd_req(logic unsigned [13:0] mem_rd_addr_0, logic unsigned [4:0] incr_addr, logic unsigned [0:0] randomness_lsb);
  logic unsigned [13:0] mem_rd_addr; // @ norm_check_top.h:121:13

  mem_rd_addr = 14'd0;
  mem_rd_addr[32'd13:32'd6] = mem_rd_addr_0[32'd13:32'd6];
  mem_rd_addr[32'd5:32'd1] = incr_addr;
  mem_rd_addr[32'd0:32'd0] = randomness_lsb;
  return mem_rd_addr;
endfunction


endpackage
