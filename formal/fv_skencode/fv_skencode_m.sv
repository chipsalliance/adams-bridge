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
// | Created on 05.04.2025 at 12:39                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import fv_skencode_pkg::*;
import fv_skencode_functions::*;


module fv_skencode_m(
  input logic rst_n,
  input logic clk,

  // Ports
  input logic start_port_vld,
  input logic start_port_rdy,
  input st_BaseAddress start_port,

  input a_unsigned_24_8 mem_rd_data_prev,

  input a_unsigned_24_8 mem_rd_data_curr,

  input a_unsigned_24_8 mem_rd_data_prev_3,

  input a_unsigned_24_8 mem_rd_data_prev_4,

  input a_unsigned_24_8 mem_rd_data_prev_5,

  input logic unsigned [31:0] keymem_a_wr_data,

  input logic mem_a_rd_req_vld,
  input st_mem_if_t mem_a_rd_req,

  input logic mem_b_rd_req_vld,
  input st_mem_if_t mem_b_rd_req,

  input logic keymem_a_wr_req_vld,
  input st_mem_if_t keymem_a_wr_req,

  input logic unsigned [13:0] num_api_operands_new,

  input logic unsigned [13:0] num_mem_operands_new,

  input logic unsigned [1:0] buffer_new,

  input logic skencode_done_vld,
  input logic skencode_done,

  input logic unsigned [31:0] top_bits,

  // Registers
  input st_BaseAddress base_address,
  input logic unsigned [1:0] consumer_selector,
  input logic unsigned [13:0] num_api_operands,
  input logic unsigned [13:0] num_mem_operands,
  input logic unsigned [1:0] producer_selector,

  // States
  input logic IDLE,
  input logic READ_and_ENC,
  input logic READ_ENC_and_CONSUME___IDLE,
  input logic READ_ENC_and_CONSUME___WAIT_BUFFER,
  input logic READ_ENC_and_CONSUME___looped,
  input logic CONSUME___WRITE,
  input logic CONSUME_LAST___STALL,
  input logic DONE___GET_LAST
);


default clocking default_clk @(posedge clk); endclocking


st_BaseAddress base_address_0_i;
assign base_address_0_i = '{
  source: 15'd0,
  destination: 15'd0
};

st_mem_if_t keymem_a_wr_req_0_i;
assign keymem_a_wr_req_0_i = '{
  rd_wr_en: RW_IDLE,
  addr: 14'd0
};

st_mem_if_t mem_a_rd_req_0_i;
assign mem_a_rd_req_0_i = '{
  rd_wr_en: RW_READ,
  addr: start_port.source
};

st_mem_if_t mem_b_rd_req_0_i;
assign mem_b_rd_req_0_i = '{
  rd_wr_en: RW_READ,
  addr: (15'd1 + start_port.source)
};

st_mem_if_t mem_a_rd_req_1_i;
assign mem_a_rd_req_1_i = '{
  rd_wr_en: RW_READ,
  addr: (15'd2 + base_address.source)
};

st_mem_if_t mem_b_rd_req_1_i;
assign mem_b_rd_req_1_i = '{
  rd_wr_en: RW_READ,
  addr: (15'd3 + base_address.source)
};

logic unsigned [31:0] encode_0_i;
assign encode_0_i = encode(mem_rd_data_curr);

logic unsigned [31:0] bitwise_or_0_i;
assign bitwise_or_0_i = bitwise_or(32'(({ ({ 'h0, top_bits[31:24]} ), 24'h0} )), encode_0_i);

logic unsigned [0:0] encode_error_0_i;
assign encode_error_0_i = encode_error(mem_rd_data_curr);

st_mem_if_t mem_a_rd_req_2_i;
assign mem_a_rd_req_2_i = '{
  rd_wr_en: RW_READ,
  addr: (15'd4 + base_address.source)
};

st_mem_if_t mem_b_rd_req_2_i;
assign mem_b_rd_req_2_i = '{
  rd_wr_en: RW_READ,
  addr: (15'd5 + base_address.source)
};

logic unsigned [31:0] encode_1_i;
assign encode_1_i = encode(mem_rd_data_prev);

logic unsigned [31:0] bitwise_or_1_i;
assign bitwise_or_1_i = bitwise_or(({ encode_0_i[7:0], 24'h0} ), encode_1_i);

logic unsigned [0:0] encode_error_1_i;
assign encode_error_1_i = encode_error(mem_rd_data_prev);

st_mem_if_t keymem_a_wr_req_1_i;
assign keymem_a_wr_req_1_i = '{
  rd_wr_en: RW_WRITE,
  addr: base_address.destination
};

st_mem_if_t mem_a_rd_req_3_i;
assign mem_a_rd_req_3_i = '{
  rd_wr_en: RW_READ,
  addr: (15'd6 + base_address.source)
};

st_mem_if_t mem_b_rd_req_3_i;
assign mem_b_rd_req_3_i = '{
  rd_wr_en: RW_READ,
  addr: (15'd7 + base_address.source)
};

logic unsigned [13:0] shift_amount_first_0_i;
assign shift_amount_first_0_i = shift_amount_first(num_api_operands);

logic unsigned [13:0] shift_amount_0_i;
assign shift_amount_0_i = shift_amount(num_api_operands);

logic unsigned [31:0] bitwise_or_2_i;
assign bitwise_or_2_i = bitwise_or((encode_0_i << ({ 18'h0, shift_amount_first_0_i} )), (encode_1_i >> ({ 18'h0, shift_amount_0_i} )));

st_mem_if_t keymem_a_wr_req_2_i;
assign keymem_a_wr_req_2_i = '{
  rd_wr_en: RW_WRITE,
  addr: (base_address.destination + ({ 1'h0, num_api_operands} ))
};

st_mem_if_t mem_a_rd_req_4_i;
assign mem_a_rd_req_4_i = '{
  rd_wr_en: RW_READ,
  addr: (base_address.source + ({ 1'h0, num_mem_operands} ))
};

st_mem_if_t mem_b_rd_req_4_i;
assign mem_b_rd_req_4_i = '{
  rd_wr_en: RW_READ,
  addr: ((15'd1 + base_address.source) + ({ 1'h0, num_mem_operands} ))
};

logic unsigned [31:0] encode_2_i;
assign encode_2_i = encode(mem_rd_data_prev_3);

logic unsigned [31:0] bitwise_or_3_i;
assign bitwise_or_3_i = bitwise_or(({ encode_2_i[7:0], 24'h0} ), encode_0_i);

logic unsigned [0:0] encode_error_2_i;
assign encode_error_2_i = encode_error(mem_rd_data_prev_3);

logic unsigned [31:0] bitwise_or_4_i;
assign bitwise_or_4_i = bitwise_or(({ encode_0_i[23:0], 8'h0} ), ({ 16'h0, encode_1_i[31:16]} ));

logic unsigned [31:0] encode_3_i;
assign encode_3_i = encode(mem_rd_data_prev_4);

logic unsigned [31:0] bitwise_or_5_i;
assign bitwise_or_5_i = bitwise_or(({ encode_2_i[7:0], 24'h0} ), encode_3_i);

logic unsigned [0:0] encode_error_3_i;
assign encode_error_3_i = encode_error(mem_rd_data_prev_4);

logic unsigned [31:0] encode_4_i;
assign encode_4_i = encode(mem_rd_data_prev_5);

logic unsigned [31:0] bitwise_or_6_i;
assign bitwise_or_6_i = bitwise_or(({ encode_3_i[7:0], 24'h0} ), encode_4_i);


sequence reset_sequence;
  !rst_n ##1 rst_n;
endsequence


property run_reset_p;
  reset_sequence |->
  IDLE &&
  base_address == base_address_0_i &&
  consumer_selector == 2'd0 &&
  keymem_a_wr_data == 0 &&
  keymem_a_wr_req == keymem_a_wr_req_0_i &&
  mem_a_rd_req == keymem_a_wr_req_0_i &&
  mem_b_rd_req == keymem_a_wr_req_0_i &&
  num_api_operands == 14'd0 &&
  num_mem_operands == 14'd0 &&
  producer_selector == 2'd0 &&
  skencode_done == 0;
endproperty
run_reset_a: assert property (run_reset_p);


property run_CONSUME_LAST___STALL_to_DONE___GET_LAST_p;
  CONSUME_LAST___STALL &&
  (encode_error_2_i != 1'd1) &&
  (encode_error_3_i != 1'd1) &&
  (encode_error_1_i != 1'd1) && 
  (encode_error_0_i != 1'd1)
|->
  ##1
  DONE___GET_LAST &&
  $stable(base_address) &&
  consumer_selector == 2'd0 &&
  keymem_a_wr_data == $past(bitwise_or_5_i, 1) &&
  keymem_a_wr_req == keymem_a_wr_req_0_i &&
  mem_a_rd_req == keymem_a_wr_req_0_i &&
  mem_b_rd_req == keymem_a_wr_req_0_i &&
  $stable(num_api_operands) &&
  num_mem_operands == 14'd0 &&
  producer_selector == 2'd0 &&
  skencode_done == 0;
endproperty
run_CONSUME_LAST___STALL_to_DONE___GET_LAST_a: assert property (disable iff(!rst_n) run_CONSUME_LAST___STALL_to_DONE___GET_LAST_p);


property run_CONSUME_LAST___STALL_to_IDLE_p;
  CONSUME_LAST___STALL &&
  ((encode_error_2_i == 1'd1) || (encode_error_3_i == 1'd1) || (encode_error_1_i == 1'd1) || (encode_error_0_i == 1'd1))
|->
  ##1
  IDLE &&
  $stable(base_address) &&
  consumer_selector == 2'd0 &&
  keymem_a_wr_data == $past(bitwise_or_5_i, 1) &&
  keymem_a_wr_req == keymem_a_wr_req_0_i &&
  mem_a_rd_req == keymem_a_wr_req_0_i &&
  mem_b_rd_req == keymem_a_wr_req_0_i &&
  $stable(num_api_operands) &&
  num_mem_operands == 14'd0 &&
  producer_selector == 2'd0 &&
  skencode_done == 0;
endproperty
run_CONSUME_LAST___STALL_to_IDLE_a: assert property (disable iff(!rst_n) run_CONSUME_LAST___STALL_to_IDLE_p);


property run_CONSUME___WRITE_to_CONSUME_LAST___STALL_p;
  CONSUME___WRITE &&
  (encode_error_1_i != 1'd1) &&
  (encode_error_0_i != 1'd1)
|->
  ##1
  CONSUME_LAST___STALL &&
  $stable(base_address) &&
  consumer_selector == 2'((64'd1 + ({ 62'h0, $past(consumer_selector, 1)} ))) &&
  keymem_a_wr_data == $past(bitwise_or_4_i, 1) &&
  keymem_a_wr_req == $past(keymem_a_wr_req_2_i, 1) &&
  mem_a_rd_req == keymem_a_wr_req_0_i &&
  mem_b_rd_req == keymem_a_wr_req_0_i &&
  num_api_operands == 14'((64'd1 + ({ 50'h0, $past(num_api_operands, 1)} ))) &&
  num_mem_operands == 14'd0 &&
  producer_selector == 2'd0 &&
  skencode_done == 0;
endproperty
run_CONSUME___WRITE_to_CONSUME_LAST___STALL_a: assert property (disable iff(!rst_n) run_CONSUME___WRITE_to_CONSUME_LAST___STALL_p);


property run_CONSUME___WRITE_to_IDLE_p;
  CONSUME___WRITE &&
  ((encode_error_1_i == 1'd1) || (encode_error_0_i == 1'd1))
|->
  ##1
  IDLE &&
  $stable(base_address) &&
  consumer_selector == 2'((64'd1 + ({ 62'h0, $past(consumer_selector, 1)} ))) &&
  keymem_a_wr_data == $past(bitwise_or_4_i, 1) &&
  keymem_a_wr_req == $past(keymem_a_wr_req_2_i, 1) &&
  mem_a_rd_req == keymem_a_wr_req_0_i &&
  mem_b_rd_req == keymem_a_wr_req_0_i &&
  num_api_operands == 14'((64'd1 + ({ 50'h0, $past(num_api_operands, 1)} ))) &&
  num_mem_operands == 14'd0 &&
  producer_selector == 2'd0 &&
  skencode_done == 0;
endproperty
run_CONSUME___WRITE_to_IDLE_a: assert property (disable iff(!rst_n) run_CONSUME___WRITE_to_IDLE_p);


property run_DONE___GET_LAST_to_IDLE_p;
  DONE___GET_LAST
|->
  ##1
  IDLE &&
  $stable(base_address) &&
  $stable(consumer_selector) &&
  keymem_a_wr_data == $past(bitwise_or_6_i, 1) &&
  keymem_a_wr_req == keymem_a_wr_req_0_i &&
  mem_a_rd_req == keymem_a_wr_req_0_i &&
  mem_b_rd_req == keymem_a_wr_req_0_i &&
  $stable(num_api_operands) &&
  $stable(num_mem_operands) &&
  $stable(producer_selector) &&
  skencode_done == 1;
endproperty
run_DONE___GET_LAST_to_IDLE_a: assert property (disable iff(!rst_n) run_DONE___GET_LAST_to_IDLE_p);


property run_IDLE_to_READ_and_ENC_p;
  IDLE &&
  start_port_vld
|->
  ##1 ($stable(keymem_a_wr_data))[*2] and
  ##2
  READ_and_ENC &&
  base_address == $past(start_port, 2) &&
  consumer_selector == 2'd0 &&
  keymem_a_wr_req == keymem_a_wr_req_0_i &&
  mem_a_rd_req == $past(mem_a_rd_req_0_i, 2) &&
  mem_b_rd_req == $past(mem_b_rd_req_0_i, 2) &&
  num_api_operands == 14'd0 &&
  num_mem_operands == 14'((64'd2 + ({ 50'h0, $past(num_mem_operands, 2)} ))) &&
  producer_selector == 2'd0 &&
  skencode_done == 0;
endproperty
run_IDLE_to_READ_and_ENC_a: assert property (disable iff(!rst_n) run_IDLE_to_READ_and_ENC_p);


property run_READ_ENC_and_CONSUME___IDLE_to_IDLE_p;
  READ_ENC_and_CONSUME___IDLE &&
  (encode_error_0_i == 1'd1)
|->
  ##1
  IDLE &&
  $stable(base_address) &&
  consumer_selector == 2'd0 &&
  keymem_a_wr_data == $past(bitwise_or_0_i, 1) &&
  keymem_a_wr_req == keymem_a_wr_req_0_i &&
  mem_a_rd_req == $past(mem_a_rd_req_2_i, 1) &&
  mem_b_rd_req == $past(mem_b_rd_req_2_i, 1) &&
  num_api_operands == 14'd0 &&
  num_mem_operands == 14'((64'd2 + ({ 50'h0, $past(num_mem_operands, 1)} ))) &&
  producer_selector == 2'((64'd1 + ({ 62'h0, $past(producer_selector, 1)} ))) &&
  skencode_done == 0;
endproperty
run_READ_ENC_and_CONSUME___IDLE_to_IDLE_a: assert property (disable iff(!rst_n) run_READ_ENC_and_CONSUME___IDLE_to_IDLE_p);


property run_READ_ENC_and_CONSUME___IDLE_to_READ_ENC_and_CONSUME___WAIT_BUFFER_p;
  READ_ENC_and_CONSUME___IDLE &&
  (encode_error_0_i != 1'd1)
|->
  ##1
  READ_ENC_and_CONSUME___WAIT_BUFFER &&
  $stable(base_address) &&
  consumer_selector == 2'd0 &&
  keymem_a_wr_data == $past(bitwise_or_0_i, 1) &&
  keymem_a_wr_req == keymem_a_wr_req_0_i &&
  mem_a_rd_req == $past(mem_a_rd_req_2_i, 1) &&
  mem_b_rd_req == $past(mem_b_rd_req_2_i, 1) &&
  num_api_operands == 14'd0 &&
  num_mem_operands == 14'((64'd2 + ({ 50'h0, $past(num_mem_operands, 1)} ))) &&
  producer_selector == 2'((64'd1 + ({ 62'h0, $past(producer_selector, 1)} ))) &&
  skencode_done == 0;
endproperty
run_READ_ENC_and_CONSUME___IDLE_to_READ_ENC_and_CONSUME___WAIT_BUFFER_a: assert property (disable iff(!rst_n) run_READ_ENC_and_CONSUME___IDLE_to_READ_ENC_and_CONSUME___WAIT_BUFFER_p);


property run_READ_ENC_and_CONSUME___WAIT_BUFFER_to_IDLE_p;
  READ_ENC_and_CONSUME___WAIT_BUFFER &&
  (producer_selector == 2'd1) &&
  ((encode_error_0_i == 1'd1) || (encode_error_1_i == 1'd1))
|->
  ##1
  IDLE &&
  $stable(base_address) &&
  consumer_selector == 2'd0 &&
  keymem_a_wr_data == $past(bitwise_or_1_i, 1) &&
  keymem_a_wr_req == $past(keymem_a_wr_req_1_i, 1) &&
  mem_a_rd_req == $past(mem_a_rd_req_3_i, 1) &&
  mem_b_rd_req == $past(mem_b_rd_req_3_i, 1) &&
  num_api_operands == 14'((64'd1 + ({ 50'h0, $past(num_api_operands, 1)} ))) &&
  num_mem_operands == 14'((64'd2 + ({ 50'h0, $past(num_mem_operands, 1)} ))) &&
  producer_selector == 2'((64'd1 + ({ 62'h0, $past(producer_selector, 1)} ))) &&
  skencode_done == 0;
endproperty
run_READ_ENC_and_CONSUME___WAIT_BUFFER_to_IDLE_a: assert property (disable iff(!rst_n) run_READ_ENC_and_CONSUME___WAIT_BUFFER_to_IDLE_p);


property run_READ_ENC_and_CONSUME___WAIT_BUFFER_to_READ_ENC_and_CONSUME___WAIT_BUFFER_p;
  READ_ENC_and_CONSUME___WAIT_BUFFER &&
  (producer_selector != 2'd1)
|->
  ##1 ($stable(keymem_a_wr_data)) and
  ##1
  READ_ENC_and_CONSUME___WAIT_BUFFER &&
  $stable(base_address) &&
  $stable(consumer_selector) &&
  $stable(num_api_operands) &&
  $stable(num_mem_operands) &&
  $stable(producer_selector);
endproperty
run_READ_ENC_and_CONSUME___WAIT_BUFFER_to_READ_ENC_and_CONSUME___WAIT_BUFFER_a: assert property (disable iff(!rst_n) run_READ_ENC_and_CONSUME___WAIT_BUFFER_to_READ_ENC_and_CONSUME___WAIT_BUFFER_p);


property run_READ_ENC_and_CONSUME___WAIT_BUFFER_to_READ_ENC_and_CONSUME___looped_p;
  READ_ENC_and_CONSUME___WAIT_BUFFER &&
  (producer_selector == 2'd1) &&
  (encode_error_0_i != 1'd1) &&
  (encode_error_1_i != 1'd1)
|->
  ##1
  READ_ENC_and_CONSUME___looped &&
  $stable(base_address) &&
  consumer_selector == 2'd0 &&
  keymem_a_wr_data == $past(bitwise_or_1_i, 1) &&
  keymem_a_wr_req == $past(keymem_a_wr_req_1_i, 1) &&
  mem_a_rd_req == $past(mem_a_rd_req_3_i, 1) &&
  mem_b_rd_req == $past(mem_b_rd_req_3_i, 1) &&
  num_api_operands == 14'((64'd1 + ({ 50'h0, $past(num_api_operands, 1)} ))) &&
  num_mem_operands == 14'((64'd2 + ({ 50'h0, $past(num_mem_operands, 1)} ))) &&
  producer_selector == 2'((64'd1 + ({ 62'h0, $past(producer_selector, 1)} ))) &&
  skencode_done == 0;
endproperty
run_READ_ENC_and_CONSUME___WAIT_BUFFER_to_READ_ENC_and_CONSUME___looped_a: assert property (disable iff(!rst_n) run_READ_ENC_and_CONSUME___WAIT_BUFFER_to_READ_ENC_and_CONSUME___looped_p);


property run_READ_ENC_and_CONSUME___looped_to_CONSUME___WRITE_p;
  READ_ENC_and_CONSUME___looped &&
  ((({ 50'd0, num_api_operands} ) % 64'd3) != 64'd0) &&
  (({ 62'd0, consumer_selector} ) < 64'd2) &&
  (14'((num_api_operands + 64'd1)) >= 64'd359) &&
  (encode_error_0_i != 1'd1) &&
  (encode_error_1_i != 1'd1)
|->
  ##1
  CONSUME___WRITE &&
  $stable(base_address) &&
  consumer_selector == 2'((64'd1 + ({ 62'h0, $past(consumer_selector, 1)} ))) &&
  keymem_a_wr_data == $past(bitwise_or_2_i, 1) &&
  keymem_a_wr_req == $past(keymem_a_wr_req_2_i, 1) &&
  mem_a_rd_req == keymem_a_wr_req_0_i &&
  mem_b_rd_req == keymem_a_wr_req_0_i &&
  num_api_operands == 14'((64'd1 + ({ 50'h0, $past(num_api_operands, 1)} ))) &&
  num_mem_operands == 14'd0 &&
  producer_selector == 2'((64'd1 + ({ 62'h0, $past(producer_selector, 1)} ))) &&
  skencode_done == 0;
endproperty
run_READ_ENC_and_CONSUME___looped_to_CONSUME___WRITE_a: assert property (disable iff(!rst_n) run_READ_ENC_and_CONSUME___looped_to_CONSUME___WRITE_p);


property impossible_READ_ENC_and_CONSUME___looped_to_CONSUME___WRITE_1_p;
  READ_ENC_and_CONSUME___looped &&
  !(((({ 50'd0, num_api_operands} ) % 64'd3) != 64'd0) && (({ 62'd0, consumer_selector} ) < 64'd2)) &&
  !(((({ 50'd0, num_api_operands} ) % 64'd3) == 64'd0) && (consumer_selector == 2'd2)) &&
  (14'((num_api_operands + 64'd1)) >= 64'd359) &&
  (encode_error_1_i != 1'd1) &&
  (encode_error_0_i != 1'd1)
|->
  ##1
  CONSUME___WRITE &&
  $stable(base_address) &&
  consumer_selector == 2'd0 &&
  keymem_a_wr_data == $past(bitwise_or_2_i, 1) &&
  keymem_a_wr_req == $past(keymem_a_wr_req_2_i, 1) &&
  mem_a_rd_req == keymem_a_wr_req_0_i &&
  mem_b_rd_req == keymem_a_wr_req_0_i &&
  num_api_operands == 14'((64'd1 + ({ 50'h0, $past(num_api_operands, 1)} ))) &&
  num_mem_operands == 14'd0 &&
  producer_selector == 2'((64'd1 + ({ 62'h0, $past(producer_selector, 1)} ))) &&
  skencode_done == 0;
endproperty
impossible_READ_ENC_and_CONSUME___looped_to_CONSUME___WRITE_1_a: assert property (disable iff(!rst_n) impossible_READ_ENC_and_CONSUME___looped_to_CONSUME___WRITE_1_p);


property run_READ_ENC_and_CONSUME___looped_to_IDLE_p;
  READ_ENC_and_CONSUME___looped &&
  ((({ 50'd0, num_api_operands} ) % 64'd3) != 64'd0) &&
  (({ 62'd0, consumer_selector} ) < 64'd2) &&
  (14'((num_api_operands + 64'd1)) < 64'd359) &&
  ((encode_error_0_i == 1'd1) || (encode_error_1_i == 1'd1))
|->
  ##1
  IDLE &&
  $stable(base_address) &&
  consumer_selector == 2'((64'd1 + ({ 62'h0, $past(consumer_selector, 1)} ))) &&
  keymem_a_wr_data == $past(bitwise_or_2_i, 1) &&
  keymem_a_wr_req == $past(keymem_a_wr_req_2_i, 1) &&
  mem_a_rd_req == $past(mem_a_rd_req_4_i, 1) &&
  mem_b_rd_req == $past(mem_b_rd_req_4_i, 1) &&
  num_api_operands == 14'((64'd1 + ({ 50'h0, $past(num_api_operands, 1)} ))) &&
  num_mem_operands == 14'((64'd2 + ({ 50'h0, $past(num_mem_operands, 1)} ))) &&
  producer_selector == 2'((64'd1 + ({ 62'h0, $past(producer_selector, 1)} )));
endproperty
run_READ_ENC_and_CONSUME___looped_to_IDLE_a: assert property (disable iff(!rst_n) run_READ_ENC_and_CONSUME___looped_to_IDLE_p);


property run_READ_ENC_and_CONSUME___looped_to_IDLE_1_p;
  READ_ENC_and_CONSUME___looped &&
  ((({ 50'd0, num_api_operands} ) % 64'd3) != 64'd0) &&
  (({ 62'd0, consumer_selector} ) < 64'd2) &&
  (14'((num_api_operands + 64'd1)) >= 64'd359) &&
  ((encode_error_0_i == 1'd1) || (encode_error_1_i == 1'd1))
|->
  ##1
  IDLE &&
  $stable(base_address) &&
  consumer_selector == 2'((64'd1 + ({ 62'h0, $past(consumer_selector, 1)} ))) &&
  keymem_a_wr_data == $past(bitwise_or_2_i, 1) &&
  keymem_a_wr_req == $past(keymem_a_wr_req_2_i, 1) &&
  mem_a_rd_req == keymem_a_wr_req_0_i &&
  mem_b_rd_req == keymem_a_wr_req_0_i &&
  num_api_operands == 14'((64'd1 + ({ 50'h0, $past(num_api_operands, 1)} ))) &&
  num_mem_operands == 14'd0 &&
  producer_selector == 2'((64'd1 + ({ 62'h0, $past(producer_selector, 1)} )));
endproperty
run_READ_ENC_and_CONSUME___looped_to_IDLE_1_a: assert property (disable iff(!rst_n) run_READ_ENC_and_CONSUME___looped_to_IDLE_1_p);


property run_READ_ENC_and_CONSUME___looped_to_IDLE_2_p;
  READ_ENC_and_CONSUME___looped &&
  ((({ 50'd0, num_api_operands} ) % 64'd3) == 64'd0) &&
  (consumer_selector == 2'd2) &&
  (({ 50'd0, num_api_operands} ) < 64'd359) &&
  ((encode_error_2_i == 1'd1) || (encode_error_0_i == 1'd1))
|->
  ##1
  IDLE &&
  $stable(base_address) &&
  consumer_selector == 2'd0 &&
  keymem_a_wr_data == $past(bitwise_or_3_i, 1) &&
  keymem_a_wr_req == keymem_a_wr_req_0_i &&
  mem_a_rd_req == $past(mem_a_rd_req_4_i, 1) &&
  mem_b_rd_req == $past(mem_b_rd_req_4_i, 1) &&
  $stable(num_api_operands) &&
  num_mem_operands == 14'((64'd2 + ({ 50'h0, $past(num_mem_operands, 1)} ))) &&
  producer_selector == 2'((64'd1 + ({ 62'h0, $past(producer_selector, 1)} )));
endproperty
run_READ_ENC_and_CONSUME___looped_to_IDLE_2_a: assert property (disable iff(!rst_n) run_READ_ENC_and_CONSUME___looped_to_IDLE_2_p);


property run_READ_ENC_and_CONSUME___looped_to_IDLE_3_p;
  READ_ENC_and_CONSUME___looped &&
  !(((({ 50'd0, num_api_operands} ) % 64'd3) != 64'd0) && (({ 62'd0, consumer_selector} ) < 64'd2)) &&
  !(((({ 50'd0, num_api_operands} ) % 64'd3) == 64'd0) && (consumer_selector == 2'd2)) &&
  (14'((num_api_operands + 64'd1)) < 64'd359) &&
  ((encode_error_1_i == 1'd1) || (encode_error_0_i == 1'd1))
|->
  ##1
  IDLE &&
  $stable(base_address) &&
  consumer_selector == 2'd0 &&
  keymem_a_wr_data == $past(bitwise_or_2_i, 1) &&
  keymem_a_wr_req == $past(keymem_a_wr_req_2_i, 1) &&
  mem_a_rd_req == $past(mem_a_rd_req_4_i, 1) &&
  mem_b_rd_req == $past(mem_b_rd_req_4_i, 1) &&
  num_api_operands == 14'((64'd1 + ({ 50'h0, $past(num_api_operands, 1)} ))) &&
  num_mem_operands == 14'((64'd2 + ({ 50'h0, $past(num_mem_operands, 1)} ))) &&
  producer_selector == 2'((64'd1 + ({ 62'h0, $past(producer_selector, 1)} )));
endproperty
run_READ_ENC_and_CONSUME___looped_to_IDLE_3_a: assert property (disable iff(!rst_n) run_READ_ENC_and_CONSUME___looped_to_IDLE_3_p);


property run_READ_ENC_and_CONSUME___looped_to_IDLE_4_p;
  READ_ENC_and_CONSUME___looped &&
  !(((({ 50'd0, num_api_operands} ) % 64'd3) != 64'd0) && (({ 62'd0, consumer_selector} ) < 64'd2)) &&
  !(((({ 50'd0, num_api_operands} ) % 64'd3) == 64'd0) && (consumer_selector == 2'd2)) &&
  (14'((num_api_operands + 64'd1)) >= 64'd359) &&
  ((encode_error_1_i == 1'd1) || (encode_error_0_i == 1'd1))
|->
  ##1
  IDLE &&
  $stable(base_address) &&
  consumer_selector == 2'd0 &&
  keymem_a_wr_data == $past(bitwise_or_2_i, 1) &&
  keymem_a_wr_req == $past(keymem_a_wr_req_2_i, 1) &&
  mem_a_rd_req == keymem_a_wr_req_0_i &&
  mem_b_rd_req == keymem_a_wr_req_0_i &&
  num_api_operands == 14'((64'd1 + ({ 50'h0, $past(num_api_operands, 1)} ))) &&
  num_mem_operands == 14'd0 &&
  producer_selector == 2'((64'd1 + ({ 62'h0, $past(producer_selector, 1)} )));
endproperty
run_READ_ENC_and_CONSUME___looped_to_IDLE_4_a: assert property (disable iff(!rst_n) run_READ_ENC_and_CONSUME___looped_to_IDLE_4_p);


property run_READ_ENC_and_CONSUME___looped_to_READ_ENC_and_CONSUME___looped_p;
  READ_ENC_and_CONSUME___looped &&
  ((({ 50'd0, num_api_operands} ) % 64'd3) != 64'd0) &&
  (({ 62'd0, consumer_selector} ) < 64'd2) &&
  (14'((num_api_operands + 64'd1)) < 64'd359) &&
  (encode_error_0_i != 1'd1) &&
  (encode_error_1_i != 1'd1)
|->
  ##1
  READ_ENC_and_CONSUME___looped &&
  $stable(base_address) &&
  consumer_selector == 2'((64'd1 + ({ 62'h0, $past(consumer_selector, 1)} ))) &&
  keymem_a_wr_data == $past(bitwise_or_2_i, 1) &&
  keymem_a_wr_req == $past(keymem_a_wr_req_2_i, 1) &&
  mem_a_rd_req == $past(mem_a_rd_req_4_i, 1) &&
  mem_b_rd_req == $past(mem_b_rd_req_4_i, 1) &&
  num_api_operands == 14'((64'd1 + ({ 50'h0, $past(num_api_operands, 1)} ))) &&
  num_mem_operands == 14'((64'd2 + ({ 50'h0, $past(num_mem_operands, 1)} ))) &&
  producer_selector == 2'((64'd1 + ({ 62'h0, $past(producer_selector, 1)} ))) &&
  skencode_done == 0;
endproperty
run_READ_ENC_and_CONSUME___looped_to_READ_ENC_and_CONSUME___looped_a: assert property (disable iff(!rst_n) run_READ_ENC_and_CONSUME___looped_to_READ_ENC_and_CONSUME___looped_p);


property run_READ_ENC_and_CONSUME___looped_to_READ_ENC_and_CONSUME___looped_1_p;
  READ_ENC_and_CONSUME___looped &&
  ((({ 50'd0, num_api_operands} ) % 64'd3) == 64'd0) &&
  (consumer_selector == 2'd2) &&
  (({ 50'd0, num_api_operands} ) < 64'd359) &&
  (encode_error_2_i != 1'd1) &&
  (encode_error_0_i != 1'd1)
|->
  ##1
  READ_ENC_and_CONSUME___looped &&
  $stable(base_address) &&
  consumer_selector == 2'd0 &&
  keymem_a_wr_data == $past(bitwise_or_3_i, 1) &&
  keymem_a_wr_req == keymem_a_wr_req_0_i &&
  mem_a_rd_req == $past(mem_a_rd_req_4_i, 1) &&
  mem_b_rd_req == $past(mem_b_rd_req_4_i, 1) &&
  $stable(num_api_operands) &&
  num_mem_operands == 14'((64'd2 + ({ 50'h0, $past(num_mem_operands, 1)} ))) &&
  producer_selector == 2'((64'd1 + ({ 62'h0, $past(producer_selector, 1)} ))) &&
  skencode_done == 0;
endproperty
run_READ_ENC_and_CONSUME___looped_to_READ_ENC_and_CONSUME___looped_1_a: assert property (disable iff(!rst_n) run_READ_ENC_and_CONSUME___looped_to_READ_ENC_and_CONSUME___looped_1_p);


property run_READ_ENC_and_CONSUME___looped_to_READ_ENC_and_CONSUME___looped_2_p;
  READ_ENC_and_CONSUME___looped &&
  !(((({ 50'd0, num_api_operands} ) % 64'd3) != 64'd0) && (({ 62'd0, consumer_selector} ) < 64'd2)) &&
  !(((({ 50'd0, num_api_operands} ) % 64'd3) == 64'd0) && (consumer_selector == 2'd2)) &&
  (14'((num_api_operands + 64'd1)) < 64'd359) &&
  (encode_error_1_i != 1'd1) &&
  (encode_error_0_i != 1'd1)
|->
  ##1
  READ_ENC_and_CONSUME___looped &&
  $stable(base_address) &&
  consumer_selector == 2'd0 &&
  keymem_a_wr_data == $past(bitwise_or_2_i, 1) &&
  keymem_a_wr_req == $past(keymem_a_wr_req_2_i, 1) &&
  mem_a_rd_req == $past(mem_a_rd_req_4_i, 1) &&
  mem_b_rd_req == $past(mem_b_rd_req_4_i, 1) &&
  num_api_operands == 14'((64'd1 + ({ 50'h0, $past(num_api_operands, 1)} ))) &&
  num_mem_operands == 14'((64'd2 + ({ 50'h0, $past(num_mem_operands, 1)} ))) &&
  producer_selector == 2'((64'd1 + ({ 62'h0, $past(producer_selector, 1)} ))) &&
  skencode_done == 0;
endproperty
run_READ_ENC_and_CONSUME___looped_to_READ_ENC_and_CONSUME___looped_2_a: assert property (disable iff(!rst_n) run_READ_ENC_and_CONSUME___looped_to_READ_ENC_and_CONSUME___looped_2_p);


property run_READ_and_ENC_to_READ_ENC_and_CONSUME___IDLE_p;
  READ_and_ENC
|->
  ##1 ($stable(keymem_a_wr_data)) and
  ##1
  READ_ENC_and_CONSUME___IDLE &&
  $stable(base_address) &&
  consumer_selector == 2'd0 &&
  keymem_a_wr_req == keymem_a_wr_req_0_i &&
  mem_a_rd_req == $past(mem_a_rd_req_1_i, 1) &&
  mem_b_rd_req == $past(mem_b_rd_req_1_i, 1) &&
  num_api_operands == 14'd0 &&
  num_mem_operands == 14'((64'd2 + ({ 50'h0, $past(num_mem_operands, 1)} ))) &&
  producer_selector == 2'd0 &&
  skencode_done == 0;
endproperty
run_READ_and_ENC_to_READ_ENC_and_CONSUME___IDLE_a: assert property (disable iff(!rst_n) run_READ_and_ENC_to_READ_ENC_and_CONSUME___IDLE_p);


property run_IDLE_wait_p;
IDLE &&
 !start_port_vld
|->
 ##1 
 IDLE &&
 // $stable(keymem_a_wr_data) &&
 keymem_a_wr_req == '0 &&
 mem_a_rd_req == '0 &&
 mem_b_rd_req == '0 &&
 $stable(base_address) &&
 consumer_selector == '0 &&
 num_api_operands == ($past(skencode.write_state == '0) ? 0 : $past(num_api_operands)) &&
 num_mem_operands == '0 &&
 producer_selector == '0;
endproperty
run_IDLE_wait_a: assert property (disable iff(!rst_n) run_IDLE_wait_p);


property run_IDLE_eventually_left_p;
  IDLE
|->
  s_eventually(!IDLE);
endproperty
run_IDLE_eventually_left_a: assert property (disable iff(!rst_n) run_IDLE_eventually_left_p);


property run_READ_and_ENC_eventually_left_p;
  READ_and_ENC
|->
  s_eventually(!READ_and_ENC);
endproperty
run_READ_and_ENC_eventually_left_a: assert property (disable iff(!rst_n) run_READ_and_ENC_eventually_left_p);


property run_READ_ENC_and_CONSUME___IDLE_eventually_left_p;
  READ_ENC_and_CONSUME___IDLE
|->
  s_eventually(!READ_ENC_and_CONSUME___IDLE);
endproperty
run_READ_ENC_and_CONSUME___IDLE_eventually_left_a: assert property (disable iff(!rst_n) run_READ_ENC_and_CONSUME___IDLE_eventually_left_p);


property run_READ_ENC_and_CONSUME___WAIT_BUFFER_eventually_left_p;
  READ_ENC_and_CONSUME___WAIT_BUFFER
|->
  s_eventually(!READ_ENC_and_CONSUME___WAIT_BUFFER);
endproperty
run_READ_ENC_and_CONSUME___WAIT_BUFFER_eventually_left_a: assert property (disable iff(!rst_n) run_READ_ENC_and_CONSUME___WAIT_BUFFER_eventually_left_p);


property run_READ_ENC_and_CONSUME___looped_eventually_left_p;
  READ_ENC_and_CONSUME___looped
|->
  s_eventually(!READ_ENC_and_CONSUME___looped);
endproperty
run_READ_ENC_and_CONSUME___looped_eventually_left_a: assert property (disable iff(!rst_n) run_READ_ENC_and_CONSUME___looped_eventually_left_p);


property run_CONSUME___WRITE_eventually_left_p;
  CONSUME___WRITE
|->
  s_eventually(!CONSUME___WRITE);
endproperty
run_CONSUME___WRITE_eventually_left_a: assert property (disable iff(!rst_n) run_CONSUME___WRITE_eventually_left_p);


property run_CONSUME_LAST___STALL_eventually_left_p;
  CONSUME_LAST___STALL
|->
  s_eventually(!CONSUME_LAST___STALL);
endproperty
run_CONSUME_LAST___STALL_eventually_left_a: assert property (disable iff(!rst_n) run_CONSUME_LAST___STALL_eventually_left_p);


property run_DONE___GET_LAST_eventually_left_p;
  DONE___GET_LAST
|->
  s_eventually(!DONE___GET_LAST);
endproperty
run_DONE___GET_LAST_eventually_left_a: assert property (disable iff(!rst_n) run_DONE___GET_LAST_eventually_left_p);


parameter CONSISTENCY = 1;
if (CONSISTENCY) begin
  // Check that no more than 1 state condition is met at the same time
  run_consistency_onehot0_state: assert property($onehot0({ CONSUME_LAST___STALL, CONSUME___WRITE, DONE___GET_LAST, IDLE, READ_ENC_and_CONSUME___IDLE, READ_ENC_and_CONSUME___WAIT_BUFFER, READ_ENC_and_CONSUME___looped, READ_and_ENC }));
end


endmodule
