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
// | Created on 14.02.2025 at 11:54                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import fv_makehint_pkg::*;
import fv_makehint_functions::*;


module fv_makehint_m(
  input logic rst_n,
  input logic clk,

  // Ports
  input logic makehint_enable_port_vld,
  input logic makehint_enable_port_rdy,
  input logic makehint_enable_port,

  input logic unsigned [95:0] r_port,

  input a_unsigned_1_4 z_port,

  input st_BaseAddress_makehint address_port,

  input st_mem_if_t_makehint mem_rd_req,

  input st_mem_if_t_makehint z_rd_req,

  input logic buffer_valid_o,

  input a_unsigned_8_4 buffer_data_o,

  input logic hintgen_en,

  input logic unsigned [13:0] reg_wr_addr_port_in,

  input logic unsigned [13:0] reg_wr_addr_port,

  input logic unsigned [7:0] index_count_port,

  input a_unsigned_8_8 max_index_buffer_port,

  // Registers
  input st_BaseAddress_makehint base_address,
  input logic unsigned [13:0] cnt,
  input a_unsigned_1_4 hint,
  input logic unsigned [7:0] hintsum,
  input a_unsigned_8_8 max_index_buffer,
  input logic unsigned [2:0] poly_cnt,

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


st_BaseAddress_makehint base_address_0_i;
assign base_address_0_i = '{
  mem_base_addr: 14'd0,
  dest_base_addr: 14'd0
};

a_unsigned_1_4 hint_0_i;
assign hint_0_i = '{
  0: 1'd0,
  1: 1'd0,
  2: 1'd0,
  3: 1'd0
};

a_unsigned_8_8 max_index_buffer_0_i;
assign max_index_buffer_0_i = '{
  0: 8'd0,
  1: 8'd0,
  2: 8'd0,
  3: 8'd0,
  4: 8'd0,
  5: 8'd0,
  6: 8'd0,
  7: 8'd0
};

st_mem_if_t_makehint mem_rd_req_0_i;
assign mem_rd_req_0_i = '{
  rd_wr_en: RW_IDLE,
  addr: 14'd0
};

st_mem_if_t_makehint mem_rd_req_1_i;
assign mem_rd_req_1_i = '{
  rd_wr_en: RW_READ,
  addr: address_port.mem_base_addr
};

st_mem_if_t_makehint z_rd_req_0_i;
assign z_rd_req_0_i = '{
  rd_wr_en: RW_READ,
  addr: (address_port.mem_base_addr - address_port.mem_base_addr)
};

a_unsigned_1_4 hintgen_comp_0_i;
assign hintgen_comp_0_i = hintgen_comp(r_port, z_port);

st_mem_if_t_makehint mem_rd_req_2_i;
assign mem_rd_req_2_i = '{
  rd_wr_en: RW_READ,
  addr: 14'((64'd1 + ({ 50'h0, cnt} )))
};

st_mem_if_t_makehint z_rd_req_1_i;
assign z_rd_req_1_i = '{
  rd_wr_en: RW_READ,
  addr: (14'((64'd1 + ({ 50'h0, cnt} ))) - ({ 50'h0, base_address.mem_base_addr} ))
};

st_mem_if_t_makehint mem_rd_req_3_i;
assign mem_rd_req_3_i = '{
  rd_wr_en: RW_IDLE,
  addr: base_address.mem_base_addr
};

st_mem_if_t_makehint z_rd_req_2_i;
assign z_rd_req_2_i = '{
  rd_wr_en: RW_IDLE,
  addr: (base_address.mem_base_addr - base_address.mem_base_addr)
};

st_mem_if_t_makehint mem_rd_req_4_i;
assign mem_rd_req_4_i = '{
  rd_wr_en: RW_IDLE,
  addr: 14'((64'd1 + ({ 50'h0, cnt} )))
};

st_mem_if_t_makehint z_rd_req_3_i;
assign z_rd_req_3_i = '{
  rd_wr_en: RW_IDLE,
  addr: (14'((64'd1 + ({ 50'h0, cnt} ))) - ({ 50'h0, base_address.mem_base_addr} ))
};

a_unsigned_8_8 max_index_buffer_comp_0_i;
assign max_index_buffer_comp_0_i = max_index_buffer_comp(max_index_buffer, hintsum);

st_mem_if_t_makehint mem_rd_req_5_i;
assign mem_rd_req_5_i = '{
  rd_wr_en: RW_READ,
  addr: cnt
};

st_mem_if_t_makehint z_rd_req_4_i;
assign z_rd_req_4_i = '{
  rd_wr_en: RW_READ,
  addr: (cnt - base_address.mem_base_addr)
};

st_mem_if_t_makehint mem_rd_req_6_i;
assign mem_rd_req_6_i = '{
  rd_wr_en: RW_IDLE,
  addr: cnt
};


sequence reset_sequence;
  !$past(rst_n) && rst_n;
endsequence


property run_reset_p;
  reset_sequence |->
  MH_IDLE &&
  cnt == 14'd0 &&
  hintgen_en == 0 &&
  hintsum == 8'd0 &&
  index_count_port == 8'd0 &&
  max_index_buffer == max_index_buffer_0_i &&
  max_index_buffer_port == max_index_buffer_0_i &&
  mem_rd_req == mem_rd_req_0_i &&
  poly_cnt == 3'd0 &&
  reg_wr_addr_port == 14'd0 &&
  z_rd_req == mem_rd_req_0_i;
endproperty
run_reset_a: assert property (run_reset_p);


property run_MH_FLUSH_SBUF_to_MH_RD_IBUF_LOW_p;
  MH_FLUSH_SBUF
|->
  ##1 ($stable(hintgen_en)) and
  ##1 ($stable(index_count_port)) and
  ##1 ($stable(max_index_buffer_port)) and
  ##1 ($stable(mem_rd_req)) and
  ##1 ($stable(z_rd_req)) and
  ##1
  MH_RD_IBUF_LOW &&
  $stable(cnt) &&
  $stable(hintsum) &&
  $stable(max_index_buffer) &&
  $stable(poly_cnt) &&
  reg_wr_addr_port == 14'((64'd18 + ({ 50'h0, $past(base_address.dest_base_addr, 1)} )));
endproperty
run_MH_FLUSH_SBUF_to_MH_RD_IBUF_LOW_a: assert property (disable iff(!rst_n) run_MH_FLUSH_SBUF_to_MH_RD_IBUF_LOW_p);


property run_MH_IDLE_to_MH_RD_MEM_p;
  MH_IDLE &&
  makehint_enable_port_vld
|->
  ##1
  MH_RD_MEM &&
  cnt == $past(address_port.mem_base_addr, 1) &&
  hintgen_en == 0 &&
  hintsum == 8'd0 &&
  index_count_port == 8'd0 &&
  max_index_buffer == $past(max_index_buffer_0_i, 1) &&
  max_index_buffer_port == $past(max_index_buffer_0_i, 1) &&
  mem_rd_req == $past(mem_rd_req_1_i, 1) &&
  poly_cnt == 3'd0 &&
  reg_wr_addr_port == 14'd0 &&
  z_rd_req == $past(z_rd_req_0_i, 1);
endproperty
run_MH_IDLE_to_MH_RD_MEM_a: assert property (disable iff(!rst_n) run_MH_IDLE_to_MH_RD_MEM_p);


property run_MH_RD_IBUF_HIGH_to_MH_IDLE_p;
  MH_RD_IBUF_HIGH
|->
  ##1 ($stable(hintgen_en)) and
  ##1 ($stable(index_count_port)) and
  ##1 ($stable(max_index_buffer_port)) and
  ##1
  MH_IDLE &&
  $stable(cnt) &&
  $stable(hintsum) &&
  $stable(max_index_buffer) &&
  mem_rd_req == $past(mem_rd_req_6_i, 1) &&
  $stable(poly_cnt) &&
  reg_wr_addr_port == 14'(((64'd1 + ({ 50'h0, $past(base_address.dest_base_addr, 1)} )) + $past(reg_wr_addr_port_in, 1))) &&
  z_rd_req == $past(mem_rd_req_0_i, 1);
endproperty
run_MH_RD_IBUF_HIGH_to_MH_IDLE_a: assert property (disable iff(!rst_n) run_MH_RD_IBUF_HIGH_to_MH_IDLE_p);


property run_MH_RD_IBUF_LOW_to_MH_RD_IBUF_MID_p;
  MH_RD_IBUF_LOW
|->
  ##1 ($stable(hintgen_en)) and
  ##1 ($stable(index_count_port)) and
  ##1 ($stable(max_index_buffer_port)) and
  ##1 ($stable(mem_rd_req)) and
  ##1 ($stable(z_rd_req)) and
  ##1
  MH_RD_IBUF_MID &&
  $stable(cnt) &&
  $stable(hintsum) &&
  $stable(max_index_buffer) &&
  $stable(poly_cnt) &&
  reg_wr_addr_port == 14'(((64'd1 + ({ 50'h0, $past(base_address.dest_base_addr, 1)} )) + $past(reg_wr_addr_port_in, 1)));
endproperty
run_MH_RD_IBUF_LOW_to_MH_RD_IBUF_MID_a: assert property (disable iff(!rst_n) run_MH_RD_IBUF_LOW_to_MH_RD_IBUF_MID_p);


property run_MH_RD_IBUF_MID_to_MH_RD_IBUF_HIGH_p;
  MH_RD_IBUF_MID
|->
  ##1 ($stable(hintgen_en)) and
  ##1 ($stable(index_count_port)) and
  ##1 ($stable(max_index_buffer_port)) and
  ##1 ($stable(mem_rd_req)) and
  ##1 ($stable(z_rd_req)) and
  ##1
  MH_RD_IBUF_HIGH &&
  $stable(cnt) &&
  $stable(hintsum) &&
  $stable(max_index_buffer) &&
  $stable(poly_cnt) &&
  reg_wr_addr_port == 14'(((64'd1 + ({ 50'h0, $past(base_address.dest_base_addr, 1)} )) + $past(reg_wr_addr_port_in, 1)));
endproperty
run_MH_RD_IBUF_MID_to_MH_RD_IBUF_HIGH_a: assert property (disable iff(!rst_n) run_MH_RD_IBUF_MID_to_MH_RD_IBUF_HIGH_p);


property run_MH_RD_MEM_to_MH_RD_MEM_p;
  MH_RD_MEM &&
  buffer_valid_o &&
  (14'((cnt + 64'd1)) <= 14'(((64'd64 + (64'd64 * ({ 61'h0, poly_cnt} ))) - 64'd1) + ({ 50'h0, base_address.mem_base_addr} )))
|->
  ##1 ($stable(max_index_buffer_port)) and
  ##1
  MH_RD_MEM &&
  cnt == 14'((64'd1 + ({ 50'h0, $past(cnt, 1)} ))) &&
  hintgen_en == 1 &&
  hintsum == (((($past(hintsum, 1) + $past(hint[64'd0], 1)) + $past(hint[64'd1], 1)) + $past(hint[64'd2], 1)) + $past(hint[64'd3], 1)) &&
  index_count_port == 8'((64'd4 * (({ 50'h0, $past(cnt, 1)} ) - ({ 50'h0, $past(base_address.mem_base_addr, 1)} )))) &&
  $stable(max_index_buffer) &&
  mem_rd_req == $past(mem_rd_req_2_i, 1) &&
  $stable(poly_cnt) &&
  reg_wr_addr_port == 14'(((64'd1 + ({ 50'h0, $past(base_address.dest_base_addr, 1)} )) + $past(reg_wr_addr_port_in, 1))) &&
  z_rd_req == $past(z_rd_req_1_i, 1);
endproperty
run_MH_RD_MEM_to_MH_RD_MEM_a: assert property (disable iff(!rst_n) run_MH_RD_MEM_to_MH_RD_MEM_p);


property run_MH_RD_MEM_to_MH_RD_MEM_1_p;
  MH_RD_MEM &&
  !buffer_valid_o &&
  (14'((cnt + 64'd1)) <= 14'(((64'd64 + (64'd64 * ({ 61'h0, poly_cnt} ))) - 64'd1) + ({ 50'h0, base_address.mem_base_addr} )))
|->
  ##1 ($stable(max_index_buffer_port)) and
  ##1 ($stable(reg_wr_addr_port)) and
  ##1
  MH_RD_MEM &&
  cnt == 14'((64'd1 + ({ 50'h0, $past(cnt, 1)} ))) &&
  hintgen_en == 1 &&
  hintsum == (((($past(hintsum, 1) + $past(hint[64'd0], 1)) + $past(hint[64'd1], 1)) + $past(hint[64'd2], 1)) + $past(hint[64'd3], 1)) &&
  index_count_port == 8'((64'd4 * (({ 50'h0, $past(cnt, 1)} ) - ({ 50'h0, $past(base_address.mem_base_addr, 1)} )))) &&
  $stable(max_index_buffer) &&
  mem_rd_req == $past(mem_rd_req_2_i, 1) &&
  $stable(poly_cnt) &&
  z_rd_req == $past(z_rd_req_1_i, 1);
endproperty
run_MH_RD_MEM_to_MH_RD_MEM_1_a: assert property (disable iff(!rst_n) run_MH_RD_MEM_to_MH_RD_MEM_1_p);


property run_MH_RD_MEM_to_MH_WAIT1_p;
  MH_RD_MEM &&
  buffer_valid_o &&
  (14'((cnt + 64'd1)) > 14'(((64'd64 + (64'd64 * ({ 61'h0, poly_cnt} ))) - 64'd1) + ({ 50'h0, base_address.mem_base_addr} ))) &&
  (poly_cnt == 3'h7) &&
  buffer_valid_o
|->
  ##1 ($stable(max_index_buffer_port)) and
  ##1
  MH_WAIT1 &&
  cnt == $past(base_address.mem_base_addr, 1) &&
  hintgen_en == 1 &&
  hintsum == (((($past(hintsum, 1) + $past(hint[64'd0], 1)) + $past(hint[64'd1], 1)) + $past(hint[64'd2], 1)) + $past(hint[64'd3], 1)) &&
  index_count_port == 8'((64'd4 * (({ 50'h0, $past(cnt, 1)} ) - ({ 50'h0, $past(base_address.mem_base_addr, 1)} )))) &&
  $stable(max_index_buffer) &&
  mem_rd_req == $past(mem_rd_req_3_i, 1) &&
  $stable(poly_cnt) &&
  reg_wr_addr_port == 14'(((64'd1 + ({ 50'h0, $past(base_address.dest_base_addr, 1)} )) + $past(reg_wr_addr_port_in, 1))) &&
  z_rd_req == $past(z_rd_req_2_i, 1);
endproperty
run_MH_RD_MEM_to_MH_WAIT1_a: assert property (disable iff(!rst_n) run_MH_RD_MEM_to_MH_WAIT1_p);


property run_MH_RD_MEM_to_MH_WAIT1_1_p;
  MH_RD_MEM &&
  buffer_valid_o &&
  (14'((cnt + 64'd1)) > 14'(((64'd64 + (64'd64 * ({ 61'h0, poly_cnt} ))) - 64'd1) + ({ 50'h0, base_address.mem_base_addr} ))) &&
  (poly_cnt != 3'h7) &&
  buffer_valid_o
|->
  ##1 ($stable(max_index_buffer_port)) and
  ##1
  MH_WAIT1 &&
  cnt == 14'((64'd1 + ({ 50'h0, $past(cnt, 1)} ))) &&
  hintgen_en == 1 &&
  hintsum == (((($past(hintsum, 1) + $past(hint[64'd0], 1)) + $past(hint[64'd1], 1)) + $past(hint[64'd2], 1)) + $past(hint[64'd3], 1)) &&
  index_count_port == 8'((64'd4 * (({ 50'h0, $past(cnt, 1)} ) - ({ 50'h0, $past(base_address.mem_base_addr, 1)} )))) &&
  $stable(max_index_buffer) &&
  mem_rd_req == $past(mem_rd_req_4_i, 1) &&
  $stable(poly_cnt) &&
  reg_wr_addr_port == 14'(((64'd1 + ({ 50'h0, $past(base_address.dest_base_addr, 1)} )) + $past(reg_wr_addr_port_in, 1))) &&
  z_rd_req == $past(z_rd_req_3_i, 1);
endproperty
run_MH_RD_MEM_to_MH_WAIT1_1_a: assert property (disable iff(!rst_n) run_MH_RD_MEM_to_MH_WAIT1_1_p);


property run_MH_RD_MEM_to_MH_WAIT1_2_p;
  MH_RD_MEM &&
  !buffer_valid_o &&
  (14'((cnt + 64'd1)) > (((64'd64 + (64'd64 * ({ 61'h0, poly_cnt} ))) - 64'd1) + ({ 50'h0, base_address.mem_base_addr} ))) &&
  (poly_cnt == 3'h7) &&
  !buffer_valid_o
|->
  ##1 ($stable(max_index_buffer_port)) and
  ##1 ($stable(reg_wr_addr_port)) and
  ##1
  MH_WAIT1 &&
  cnt == $past(base_address.mem_base_addr, 1) &&
  hintgen_en == 1 &&
  hintsum == (((($past(hintsum, 1) + $past(hint[64'd0], 1)) + $past(hint[64'd1], 1)) + $past(hint[64'd2], 1)) + $past(hint[64'd3], 1)) &&
  index_count_port == 8'((64'd4 * (({ 50'h0, $past(cnt, 1)} ) - ({ 50'h0, $past(base_address.mem_base_addr, 1)} )))) &&
  $stable(max_index_buffer) &&
  mem_rd_req == $past(mem_rd_req_3_i, 1) &&
  $stable(poly_cnt) &&
  z_rd_req == $past(z_rd_req_2_i, 1);
endproperty
run_MH_RD_MEM_to_MH_WAIT1_2_a: assert property (disable iff(!rst_n) run_MH_RD_MEM_to_MH_WAIT1_2_p);


property run_MH_RD_MEM_to_MH_WAIT1_3_p;
  MH_RD_MEM &&
  !buffer_valid_o &&
  (14'((cnt + 64'd1)) > (((64'd64 + (64'd64 * ({ 61'h0, poly_cnt} ))) - 64'd1) + ({ 50'h0, base_address.mem_base_addr} ))) &&
  (poly_cnt != 3'h7) &&
  !buffer_valid_o
|->
  ##1 ($stable(max_index_buffer_port)) and
  ##1 ($stable(reg_wr_addr_port)) and
  ##1
  MH_WAIT1 &&
  cnt == 14'((64'd1 + ({ 50'h0, $past(cnt, 1)} ))) &&
  hintgen_en == 1 &&
  hintsum == (((($past(hintsum, 1) + $past(hint[64'd0], 1)) + $past(hint[64'd1], 1)) + $past(hint[64'd2], 1)) + $past(hint[64'd3], 1)) &&
  index_count_port == 8'((64'd4 * (({ 50'h0, $past(cnt, 1)} ) - ({ 50'h0, $past(base_address.mem_base_addr, 1)} )))) &&
  $stable(max_index_buffer) &&
  mem_rd_req == $past(mem_rd_req_4_i, 1) &&
  $stable(poly_cnt) &&
  z_rd_req == $past(z_rd_req_3_i, 1);
endproperty
run_MH_RD_MEM_to_MH_WAIT1_3_a: assert property (disable iff(!rst_n) run_MH_RD_MEM_to_MH_WAIT1_3_p);


property run_MH_WAIT1_to_MH_WAIT2_p;
  MH_WAIT1 &&
  buffer_valid_o
|->
  ##1 ($stable(max_index_buffer_port)) and
  ##1 ($stable(mem_rd_req)) and
  ##1 ($stable(z_rd_req)) and
  ##1
  MH_WAIT2 &&
  $stable(cnt) &&
  hintgen_en == 0 &&
  hintsum == (((($past(hintsum, 1) + $past(hint[64'd0], 1)) + $past(hint[64'd1], 1)) + $past(hint[64'd2], 1)) + $past(hint[64'd3], 1)) &&
  index_count_port == 8'((64'd4 * (({ 50'h0, $past(cnt, 1)} ) - ({ 50'h0, $past(base_address.mem_base_addr, 1)} )))) &&
  $stable(max_index_buffer) &&
  $stable(poly_cnt) &&
  reg_wr_addr_port == 14'(((64'd1 + ({ 50'h0, $past(base_address.dest_base_addr, 1)} )) + $past(reg_wr_addr_port_in, 1)));
endproperty
run_MH_WAIT1_to_MH_WAIT2_a: assert property (disable iff(!rst_n) run_MH_WAIT1_to_MH_WAIT2_p);


property run_MH_WAIT1_to_MH_WAIT2_1_p;
  MH_WAIT1 &&
  !buffer_valid_o
|->
  ##1 ($stable(max_index_buffer_port)) and
  ##1 ($stable(mem_rd_req)) and
  ##1 ($stable(reg_wr_addr_port)) and
  ##1 ($stable(z_rd_req)) and
  ##1
  MH_WAIT2 &&
  $stable(cnt) &&
  hintgen_en == 0 &&
  hintsum == (((($past(hintsum, 1) + $past(hint[64'd0], 1)) + $past(hint[64'd1], 1)) + $past(hint[64'd2], 1)) + $past(hint[64'd3], 1)) &&
  index_count_port == 8'((64'd4 * (({ 50'h0, $past(cnt, 1)} ) - ({ 50'h0, $past(base_address.mem_base_addr, 1)} )))) &&
  $stable(max_index_buffer) &&
  $stable(poly_cnt);
endproperty
run_MH_WAIT1_to_MH_WAIT2_1_a: assert property (disable iff(!rst_n) run_MH_WAIT1_to_MH_WAIT2_1_p);


property run_MH_WAIT2_to_MH_FLUSH_SBUF_p;
  MH_WAIT2 &&
  buffer_valid_o &&
  (poly_cnt == 3'h7)
|->
  ##1 ($stable(hintgen_en)) and
  ##1 ($stable(index_count_port)) and
  ##1 ($stable(mem_rd_req)) and
  ##1 ($stable(z_rd_req)) and
  ##1
  MH_FLUSH_SBUF &&
  $stable(cnt) &&
  $stable(hintsum) &&
  max_index_buffer == $past(max_index_buffer_comp_0_i, 1) &&
  max_index_buffer_port == $past(max_index_buffer_comp_0_i, 1) &&
  poly_cnt == 3'd0 &&
  reg_wr_addr_port == 14'(((64'd1 + ({ 50'h0, $past(base_address.dest_base_addr, 1)} )) + $past(reg_wr_addr_port_in, 1)));
endproperty
run_MH_WAIT2_to_MH_FLUSH_SBUF_a: assert property (disable iff(!rst_n) run_MH_WAIT2_to_MH_FLUSH_SBUF_p);


property run_MH_WAIT2_to_MH_FLUSH_SBUF_1_p;
  MH_WAIT2 &&
  !buffer_valid_o &&
  (poly_cnt == 3'h7)
|->
  ##1 ($stable(hintgen_en)) and
  ##1 ($stable(index_count_port)) and
  ##1 ($stable(mem_rd_req)) and
  ##1 ($stable(reg_wr_addr_port)) and
  ##1 ($stable(z_rd_req)) and
  ##1
  MH_FLUSH_SBUF &&
  $stable(cnt) &&
  $stable(hintsum) &&
  max_index_buffer == $past(max_index_buffer_comp_0_i, 1) &&
  max_index_buffer_port == $past(max_index_buffer_comp_0_i, 1) &&
  poly_cnt == 3'd0;
endproperty
run_MH_WAIT2_to_MH_FLUSH_SBUF_1_a: assert property (disable iff(!rst_n) run_MH_WAIT2_to_MH_FLUSH_SBUF_1_p);


property run_MH_WAIT2_to_MH_RD_MEM_p;
  MH_WAIT2 &&
  buffer_valid_o &&
  (poly_cnt != 3'h7)
|->
  ##1 ($stable(hintgen_en)) and
  ##1 ($stable(index_count_port)) and
  ##1
  MH_RD_MEM &&
  $stable(cnt) &&
  $stable(hintsum) &&
  max_index_buffer == $past(max_index_buffer_comp_0_i, 1) &&
  max_index_buffer_port == $past(max_index_buffer_comp_0_i, 1) &&
  mem_rd_req == $past(mem_rd_req_5_i, 1) &&
  poly_cnt == 3'((64'd1 + ({ 61'h0, $past(poly_cnt, 1)} ))) &&
  reg_wr_addr_port == 14'(((64'd1 + ({ 50'h0, $past(base_address.dest_base_addr, 1)} )) + $past(reg_wr_addr_port_in, 1))) &&
  z_rd_req == $past(z_rd_req_4_i, 1);
endproperty
run_MH_WAIT2_to_MH_RD_MEM_a: assert property (disable iff(!rst_n) run_MH_WAIT2_to_MH_RD_MEM_p);


property run_MH_WAIT2_to_MH_RD_MEM_1_p;
  MH_WAIT2 &&
  !buffer_valid_o &&
  (poly_cnt != 3'h7)
|->
  ##1 ($stable(hintgen_en)) and
  ##1 ($stable(index_count_port)) and
  ##1 ($stable(reg_wr_addr_port)) and
  ##1
  MH_RD_MEM &&
  $stable(cnt) &&
  $stable(hintsum) &&
  max_index_buffer == $past(max_index_buffer_comp_0_i, 1) &&
  max_index_buffer_port == $past(max_index_buffer_comp_0_i, 1) &&
  mem_rd_req == $past(mem_rd_req_5_i, 1) &&
  poly_cnt == 3'((64'd1 + ({ 61'h0, $past(poly_cnt, 1)} ))) &&
  z_rd_req == $past(z_rd_req_4_i, 1);
endproperty
run_MH_WAIT2_to_MH_RD_MEM_1_a: assert property (disable iff(!rst_n) run_MH_WAIT2_to_MH_RD_MEM_1_p);


// These registers can change during the MH_IDLE state, but it seems they do not cause functional problems.
// That's why registers in the property were removed out.
 property run_MH_IDLE_wait_p;
   MH_IDLE &&
   !makehint_enable_port_vld
 |->
  
   ##1
   MH_IDLE &&
  mem_rd_req.rd_wr_en == mem_rd_req_0_i.rd_wr_en && // After first MH_IDLE state, mem_rd addr is updated, so it can not be stable.
  max_index_buffer == max_index_buffer_0_i &&
  max_index_buffer_port == max_index_buffer_0_i &&
  cnt == $past(address_port.mem_base_addr) &&
  hintsum == '0 &&
  hintgen_en == 0 &&
  index_count_port == 8'd0 &&
  poly_cnt == 3'd0 &&
  reg_wr_addr_port == 14'd0 &&
  z_rd_req.rd_wr_en == mem_rd_req_0_i.rd_wr_en;
 endproperty
 run_MH_IDLE_wait_a: assert property (disable iff(!rst_n) run_MH_IDLE_wait_p);


property run_MH_IDLE_eventually_left_p;
  MH_IDLE &&
  makehint_enable_port_vld
|->
  s_eventually(!MH_IDLE);
endproperty
run_MH_IDLE_eventually_left_a: assert property (disable iff(!rst_n) run_MH_IDLE_eventually_left_p);


property run_MH_RD_MEM_eventually_left_p;
  MH_RD_MEM
|->
  s_eventually(!MH_RD_MEM);
endproperty
run_MH_RD_MEM_eventually_left_a: assert property (disable iff(!rst_n) run_MH_RD_MEM_eventually_left_p);


property run_MH_WAIT1_eventually_left_p;
  MH_WAIT1
|->
  s_eventually(!MH_WAIT1);
endproperty
run_MH_WAIT1_eventually_left_a: assert property (disable iff(!rst_n) run_MH_WAIT1_eventually_left_p);


property run_MH_WAIT2_eventually_left_p;
  MH_WAIT2
|->
  s_eventually(!MH_WAIT2);
endproperty
run_MH_WAIT2_eventually_left_a: assert property (disable iff(!rst_n) run_MH_WAIT2_eventually_left_p);


property run_MH_FLUSH_SBUF_eventually_left_p;
  MH_FLUSH_SBUF
|->
  s_eventually(!MH_FLUSH_SBUF);
endproperty
run_MH_FLUSH_SBUF_eventually_left_a: assert property (disable iff(!rst_n) run_MH_FLUSH_SBUF_eventually_left_p);


property run_MH_RD_IBUF_LOW_eventually_left_p;
  MH_RD_IBUF_LOW
|->
  s_eventually(!MH_RD_IBUF_LOW);
endproperty
run_MH_RD_IBUF_LOW_eventually_left_a: assert property (disable iff(!rst_n) run_MH_RD_IBUF_LOW_eventually_left_p);


property run_MH_RD_IBUF_MID_eventually_left_p;
  MH_RD_IBUF_MID
|->
  s_eventually(!MH_RD_IBUF_MID);
endproperty
run_MH_RD_IBUF_MID_eventually_left_a: assert property (disable iff(!rst_n) run_MH_RD_IBUF_MID_eventually_left_p);


property run_MH_RD_IBUF_HIGH_eventually_left_p;
  MH_RD_IBUF_HIGH
|->
  s_eventually(!MH_RD_IBUF_HIGH);
endproperty
run_MH_RD_IBUF_HIGH_eventually_left_a: assert property (disable iff(!rst_n) run_MH_RD_IBUF_HIGH_eventually_left_p);


parameter SANITY = 1;
if (SANITY) begin
// Check that no more than 1 state condition is met at the same time
  run_sanity_onehot0_state: assert property ( $onehot0({MH_FLUSH_SBUF, MH_IDLE, MH_RD_IBUF_HIGH, MH_RD_IBUF_LOW, MH_RD_IBUF_MID, MH_RD_MEM, MH_WAIT1, MH_WAIT2}) );
end


endmodule
