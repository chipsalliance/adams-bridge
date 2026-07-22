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

module fv_constraints_wip

import decompose_sign_mode_pkg::*;
import decompose_defines_pkg::*;

(
input     pi_rst_n,
  input   pi_clk,

  // Ports
  
  input   pi_decompose_enable,

  input   pi_dcmp_mode_t,

  input   unsigned [13:0] pi_src_base_addr,

  input   unsigned [13:0] pi_dest_base_addr,

  input   unsigned [13:0] pi_hint_src_base_addr,

  input   unsigned [95:0] pi_mem_rd_data,

  input   unsigned [95:0] pi_mem_hint_rd_data,

  input st_mem_if_t po_mem_rd_req,

  input st_mem_if_t po_mem_wr_req,

  input st_mem_if_t po_mem_hint_rd_req,

  input st_mem_if_t po_z_mem_wr_req,

  input logic  unsigned [95:0] po_mem_wr_data,

  input logic  unsigned [3:0] po_z_neq_z,

  input logic unsigned [63:0] po_w1_o,

  input logic po_buffer_en,

  input logic po_decompose_done,

  input logic po_w1_encode_done
);

default clocking default_clk @(posedge pi_clk); endclocking

property base_address_constraint; 
  	  ##0 pi_src_base_addr == 'h1380
      &&  pi_hint_src_base_addr == 'h840
      &&  pi_dest_base_addr == 'h1380;
endproperty
assume_base_address_constraint: assume property(disable iff (!pi_rst_n) base_address_constraint);

property not_dcmp_enable_while_not_done;
        !po_decompose_done
      |->
        !pi_decompose_enable;
endproperty
assume_not_dcmp_enable_while_not_done: assume property(disable iff (!pi_rst_n) not_dcmp_enable_while_not_done);

property not_verify;
    pi_dcmp_mode_t == 'h0;
endproperty
assume_not_verify: assume property(disable iff (!pi_rst_n) not_verify);

endmodule
