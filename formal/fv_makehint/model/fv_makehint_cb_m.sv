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
// | Created on 11.02.2025 at 11:00                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import fv_makehint_pkg::*;
import fv_makehint_functions::*;


module fv_makehint_cb_m #(
  parameter BUFFER_DATA_W = 8,
  parameter OMEGA         = 75
)(
  input logic rst_n,
  input logic clk,

  // Ports
  input logic unsigned [7:0]                        index_count,
  input logic unsigned [3:0][7:0]                   index,
  input logic                                       makehint_done,
  input logic                                       invalid_h,
  input logic                                       max_index_buffer_rd,
  input logic                                       sample_valid,
  input logic                                       flush_buffer,
  input logic                                       incr_index_d1,
  input logic                                       reg_wren,
  input logic unsigned [3:0][7:0]                   reg_wrdata,
  input logic unsigned [3:0][BUFFER_DATA_W - 1 : 0] sample_data,
  input logic                                       max_index_buffer_rd_lo,
  input logic                                       max_index_buffer_rd_mid,
  input logic                                       max_index_buffer_rd_hi,
  input logic unsigned [7:0][7:0]                   max_index_buffer,
  input logic unsigned [31:0]                       max_index_buffer_data,

  input logic unsigned [95:0]                       r_port,
  input a_unsigned_1_4                              z_port,
  input logic                                       hintgen_en,
  input a_unsigned_1_4                              hint,
  input logic unsigned [7:0]                        hintsum,

  // States
  input logic MH_IDLE,
  input logic MH_RD_MEM,
  input logic MH_WAIT1,
  input logic MH_WAIT2,
  input logic MH_FLUSH_SBUF,
  input logic MH_RD_IBUF_LOW,
  input logic MH_RD_IBUF_MID,
  input logic MH_RD_IBUF_HIGH
);


default clocking default_clk @(posedge clk); endclocking

a_unsigned_1_4 hintgen_comp_0_i;
assign hintgen_comp_0_i = hintgen_comp(r_port, z_port);

typedef logic unsigned [3:0][7:0] a_unsigned_8_4;
a_unsigned_8_4 max_index_buffer_data_comp_0_i, max_index_buffer_data_comp_1_i, max_index_buffer_data_comp_2_i;
assign max_index_buffer_data_comp_0_i = max_index_buffer_data_comp(max_index_buffer, 0);
assign max_index_buffer_data_comp_1_i = max_index_buffer_data_comp(max_index_buffer, 1);
assign max_index_buffer_data_comp_2_i = max_index_buffer_data_comp(max_index_buffer, 2);

a_unsigned_8_4 index_comp_0_i;
assign index_comp_0_i = index_comp(index_count);


sequence makehint_done_seq;
  !(MH_FLUSH_SBUF && makehint_done);
endsequence

property run_makehint_done_p;
  MH_IDLE
|->
  ##0 makehint_done;
endproperty
run_makehint_done_a: assert property (disable iff(!rst_n) run_makehint_done_p);

property run_invalid_h_p;
  hintsum > OMEGA
|->
  ##0 invalid_h;
endproperty
run_invalid_h_a: assert property (disable iff(!rst_n) run_invalid_h_p);

property run_po_reg_wr_1_p;
  !max_index_buffer_rd
  &&
  (sample_valid || flush_buffer)
|->
  ##0 reg_wrdata == sample_data
  &&  reg_wren == 1'b1;
endproperty
run_po_reg_wr_1_a: assert property (disable iff(!rst_n) run_po_reg_wr_1_p);

property run_po_reg_wr_2_p;
  !max_index_buffer_rd
  &&
  !(sample_valid || flush_buffer)
|->
  ##0 reg_wrdata == 'h0
  &&  reg_wren == 1'b0;
endproperty
run_po_reg_wr_2_a: assert property (disable iff(!rst_n) run_po_reg_wr_2_p);

property run_po_reg_wr_3_p;
  max_index_buffer_rd
|->
  ##0 reg_wrdata == max_index_buffer_data
  &&  reg_wren == 1'b1;
endproperty
run_po_reg_wr_3_a: assert property (disable iff(!rst_n) run_po_reg_wr_3_p);

property run_flush_buf_p;
  MH_FLUSH_SBUF
|->
  ##1 sample_data == 'h0;
endproperty
run_flush_buf_a: assert property (disable iff(!rst_n) run_flush_buf_p);

property run_hintcomp_1_p;
  !hintgen_en
|->
  ##0 hint == 'h0;
endproperty
run_hintcomp_1_a: assert property (disable iff(!rst_n) run_hintcomp_1_p);

property run_hintcomp_2_p;
  hintgen_en
|->
  ##0 hint == hintgen_comp_0_i;
endproperty
run_hintcomp_2_a: assert property (disable iff(!rst_n) run_hintcomp_2_p);

property run_indexcomp_1_p;
  incr_index_d1
|->
  ##0 index == index_comp_0_i;
endproperty
run_indexcomp_1_a: assert property (disable iff(!rst_n) run_indexcomp_1_p);

property run_indexcomp_2_p;
  !incr_index_d1
|->
  ##0 index == 'h0;
endproperty
run_indexcomp_2_a: assert property (disable iff(!rst_n) run_indexcomp_2_p);

property run_max_index_buffer_data_1_p;
  MH_RD_IBUF_LOW
|->
  ##0 
  max_index_buffer_rd_lo == 1'b1    &&
  max_index_buffer_rd    == 1'b1    &&
  max_index_buffer_data  ==  max_index_buffer_data_comp_0_i;
endproperty
run_max_index_buffer_data_1_a: assert property (disable iff(!rst_n) run_max_index_buffer_data_1_p);

property run_max_index_buffer_data_2_p;
  MH_RD_IBUF_MID
|->
  ##0 
  max_index_buffer_rd_mid == 1'b1    &&
  max_index_buffer_rd     == 1'b1    &&
  max_index_buffer_data   ==  max_index_buffer_data_comp_1_i;
endproperty
run_max_index_buffer_data_2_a: assert property (disable iff(!rst_n) run_max_index_buffer_data_2_p);

property run_max_index_buffer_data_3_p;
  MH_RD_IBUF_HIGH
|->
  ##0 
  max_index_buffer_rd_hi  == 1'b1    &&
  max_index_buffer_rd     == 1'b1    &&
  max_index_buffer_data   ==  max_index_buffer_data_comp_2_i;
endproperty
run_max_index_buffer_data_3_a: assert property (disable iff(!rst_n) run_max_index_buffer_data_3_p);


endmodule
