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

module fv_decompose_verify_mode

import decompose_verify_mode_pkg::*;
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

fv_constraints_wip fv_constraints_wip_i(.*);

endmodule

bind decompose fv_decompose_verify_mode fv_decompose_verify_mode_i(
    .pi_clk (clk),
    .pi_rst_n (reset_n && !zeroize),
    .pi_decompose_enable (decompose_enable),
    .pi_dcmp_mode_t (dcmp_mode),
    .pi_src_base_addr(src_base_addr),
    .pi_dest_base_addr(dest_base_addr),
    .pi_hint_src_base_addr(hint_src_base_addr),
    .pi_mem_rd_data(mem_rd_data),
    .pi_mem_hint_rd_data(mem_hint_rd_data),
    .po_buffer_en(buffer_en),
    .po_decompose_done(decompose_done)
);