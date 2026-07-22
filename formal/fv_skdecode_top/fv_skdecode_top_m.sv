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
// | Created on 29.03.2025 at 21:28                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import fv_skdecode_top_pkg::*;
import mldsa_params_pkg::*;
import skdecode_defines_pkg::*;
import fv_skdecode_top_functions::*;


module fv_skdecode_top_m(
  input logic rst_n,
  input logic clk,

  // Ports
  input logic start_port_vld,
  input logic start_port_rdy,
  input st_BaseAddress start_port,

  input logic s1s2_valid_in,

  input logic t0_valid_in,

  input logic keymem_a_rd_req_vld,
  input st_mem_if_t keymem_a_rd_req,

  input logic keymem_b_rd_req_vld,
  input st_mem_if_t keymem_b_rd_req,

  input logic mem_a_wr_req_vld,
  input st_mem_if_t mem_a_wr_req,

  input logic mem_b_wr_req_vld,
  input st_mem_if_t mem_b_wr_req,

  input logic skdecode_done_vld,
  input logic skdecode_done,

  input logic s1_done_vld,
  input logic s1_done,

  input logic s2_done_vld,
  input logic s2_done,

  input logic t0_done_vld,
  input logic t0_done,
  input logic skdecode_error,

  input a_unsigned_24_4 mem_a_wr_data,

  input a_unsigned_24_4 mem_b_wr_data,

  input logic s1s2_stall_dummy_out,

  // Registers
  input st_BaseAddress base_address,
  input logic unsigned [9:0] counter,
  input logic unsigned [13:0] fv_kmem_rd_addr,
  input logic unsigned [13:0] fv_mem_wr_addr,
  input a_unsigned_3_8 fv_s1s2_buf_data,
  input a_unsigned_13_4 fv_t0_buf_data,
  input logic s1s2_valid,

  // States
  input logic IDLE,
  input logic RD_WR_s1,
  input logic RD_STG_WR_s1,
  input logic RD_STG_WR_STG_1,
  input logic RD_WR_s2,
  input logic RD_STG_WR_s2,
  input logic RD_STG_WR_STG_2,
  input logic RD_WR_t0,
  input logic RD_STG_WR_t0,
  input logic RD_STG_WR_STG_3
);


default clocking default_clk @(posedge clk); endclocking

logic fv_error_reg;
always_ff @(posedge clk,negedge rst_n) begin
  if (!rst_n) begin
    // Reset logic
    fv_error_reg <= '0;
  end else begin
    // Normal operation
    if(skdecode_error)
      fv_error_reg <= 1'b1;
  end
end
st_BaseAddress base_address_0_i;
assign base_address_0_i = '{
  source: 14'd0,
  destination: 14'd0
};

a_unsigned_3_8 fv_s1s2_buf_data_0_i;
assign fv_s1s2_buf_data_0_i = '{
  0: 3'd0,
  1: 3'd0,
  2: 3'd0,
  3: 3'd0,
  4: 3'd0,
  5: 3'd0,
  6: 3'd0,
  7: 3'd0
};

a_unsigned_13_4 fv_t0_buf_data_0_i;
assign fv_t0_buf_data_0_i = '{
  0: 13'd0,
  1: 13'd0,
  2: 13'd0,
  3: 13'd0
};

st_mem_if_t keymem_a_rd_req_0_i;
assign keymem_a_rd_req_0_i = '{
  rd_wr_en: fv_RW_IDLE,
  addr: 14'd0
};

a_unsigned_24_4 mem_a_wr_data_0_i;
assign mem_a_wr_data_0_i = '{
  0: 24'd0,
  1: 24'd0,
  2: 24'd0,
  3: 24'd0
};

st_mem_if_t keymem_a_rd_req_1_i;
assign keymem_a_rd_req_1_i = '{
  rd_wr_en: fv_RW_READ,
  addr: start_port.source
};

st_mem_if_t keymem_b_rd_req_0_i;
assign keymem_b_rd_req_0_i = '{
  rd_wr_en: fv_RW_IDLE,
  addr: start_port.source
};

a_unsigned_24_4 decode_s1s2_a_0_i;
assign decode_s1s2_a_0_i = decode_s1s2_a(fv_s1s2_buf_data);

a_unsigned_24_4 decode_s1s2_b_0_i;
assign decode_s1s2_b_0_i = decode_s1s2_b(fv_s1s2_buf_data);

st_mem_if_t keymem_a_rd_req_2_i;
assign keymem_a_rd_req_2_i = '{
  rd_wr_en: fv_RW_READ,
  addr: (14'd1 + fv_kmem_rd_addr)
};

st_mem_if_t keymem_b_rd_req_1_i;
assign keymem_b_rd_req_1_i = '{
  rd_wr_en: fv_RW_IDLE,
  addr: (14'd1 + fv_kmem_rd_addr)
};

st_mem_if_t mem_a_wr_req_0_i;
assign mem_a_wr_req_0_i = '{
  rd_wr_en: fv_RW_WRITE,
  addr: (64'd2 * ({ 50'h0, fv_mem_wr_addr} ))
};

st_mem_if_t mem_b_wr_req_0_i;
assign mem_b_wr_req_0_i = '{
  rd_wr_en: fv_RW_WRITE,
  addr: (64'd1 + (64'd2 * ({ 50'h0, fv_mem_wr_addr} )))
};

st_mem_if_t mem_a_wr_req_1_i;
assign mem_a_wr_req_1_i = '{
  rd_wr_en: fv_RW_IDLE,
  addr: (64'd2 * ({ 50'h0, fv_mem_wr_addr} ))
};

st_mem_if_t mem_b_wr_req_1_i;
assign mem_b_wr_req_1_i = '{
  rd_wr_en: fv_RW_IDLE,
  addr: (64'd1 + (64'd2 * ({ 50'h0, fv_mem_wr_addr} )))
};

st_mem_if_t keymem_a_rd_req_3_i;
assign keymem_a_rd_req_3_i = '{
  rd_wr_en: fv_RW_READ,
  addr: (fv_kmem_rd_addr + 14'd0)
};

st_mem_if_t keymem_b_rd_req_2_i;
assign keymem_b_rd_req_2_i = '{
  rd_wr_en: fv_RW_IDLE,
  addr: (fv_kmem_rd_addr + 14'd0)
};

st_mem_if_t keymem_a_rd_req_4_i;
assign keymem_a_rd_req_4_i = '{
  rd_wr_en: fv_RW_READ,
  addr: fv_kmem_rd_addr
};

st_mem_if_t keymem_b_rd_req_3_i;
assign keymem_b_rd_req_3_i = '{
  rd_wr_en: fv_RW_IDLE,
  addr: fv_kmem_rd_addr
};

a_unsigned_24_4 decode_t0_0_i;
assign decode_t0_0_i = decode_t0(fv_t0_buf_data);

st_mem_if_t mem_a_wr_req_2_i;
assign mem_a_wr_req_2_i = '{
  rd_wr_en: fv_RW_WRITE,
  addr: fv_mem_wr_addr
};

st_mem_if_t mem_b_wr_req_2_i;
assign mem_b_wr_req_2_i = '{
  rd_wr_en: fv_RW_IDLE,
  addr: fv_mem_wr_addr
};


sequence reset_sequence;
  !rst_n ##1 rst_n;
endsequence


property run_reset_p;
  reset_sequence |->
  IDLE &&
  counter == 10'd0 &&
  keymem_a_rd_req == keymem_a_rd_req_0_i &&
  keymem_b_rd_req == keymem_a_rd_req_0_i &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_a_wr_req == keymem_a_rd_req_0_i &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_req == keymem_a_rd_req_0_i &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 1 &&
  t0_done == 0;
endproperty
run_reset_a: assert property (run_reset_p);


property run_IDLE_to_RD_WR_s1_p;
  IDLE &&
  start_port_vld &&
  (start_port.source[0] == 0)
|->
  ##1
  RD_WR_s1 &&
  $stable(counter) &&
  keymem_a_rd_req == $past(keymem_a_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(keymem_b_rd_req_0_i, 1) &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_a_wr_req == keymem_a_rd_req_0_i &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_req == keymem_a_rd_req_0_i &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_IDLE_to_RD_WR_s1_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_IDLE_to_RD_WR_s1_p);


property run_IDLE_to_RD_WR_s1_1_p;
  IDLE &&
  start_port_vld &&
  (start_port.source[0] != 0)
|->
  ##1
  RD_WR_s1 &&
  $stable(counter) &&
  keymem_a_rd_req == $past(keymem_b_rd_req_0_i, 1) &&
  keymem_b_rd_req == $past(keymem_a_rd_req_1_i, 1) &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_a_wr_req == keymem_a_rd_req_0_i &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_req == keymem_a_rd_req_0_i &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_IDLE_to_RD_WR_s1_1_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_IDLE_to_RD_WR_s1_1_p);


property run_RD_STG_WR_STG_1_to_RD_WR_s2_p;
  RD_STG_WR_STG_1 &&
  (base_address.source[0] == 0)
|->
  ##1
  RD_WR_s2 &&
  $stable(counter) &&
  keymem_a_rd_req == $past(keymem_a_rd_req_4_i, 1) &&
  keymem_b_rd_req == $past(keymem_b_rd_req_3_i, 1) &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(mem_b_wr_req_1_i, 1) &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_STG_WR_STG_1_to_RD_WR_s2_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_STG_WR_STG_1_to_RD_WR_s2_p);


property run_RD_STG_WR_STG_1_to_RD_WR_s2_1_p;
  RD_STG_WR_STG_1 &&
  (base_address.source[0] != 0)
|->
  ##1
  RD_WR_s2 &&
  $stable(counter) &&
  keymem_a_rd_req == $past(keymem_b_rd_req_3_i, 1) &&
  keymem_b_rd_req == $past(keymem_a_rd_req_4_i, 1) &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(mem_b_wr_req_1_i, 1) &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_STG_WR_STG_1_to_RD_WR_s2_1_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_STG_WR_STG_1_to_RD_WR_s2_1_p);


property run_RD_STG_WR_STG_2_to_RD_WR_t0_p;
  RD_STG_WR_STG_2
|->
  ##1
  RD_WR_t0 &&
  $stable(counter) &&
  keymem_a_rd_req == $past(keymem_a_rd_req_4_i, 1) &&
  keymem_b_rd_req == $past(keymem_a_rd_req_2_i, 1) &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(mem_b_wr_req_1_i, 1) &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 1 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_STG_WR_STG_2_to_RD_WR_t0_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_STG_WR_STG_2_to_RD_WR_t0_p);


property run_RD_STG_WR_STG_3_to_IDLE_p;
  RD_STG_WR_STG_3
|->
  ##1
  IDLE &&
  $stable(counter) &&
  keymem_a_rd_req == $past(keymem_b_rd_req_3_i, 1) &&
  keymem_b_rd_req == $past(keymem_b_rd_req_3_i, 1) &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(mem_b_wr_req_2_i, 1) &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(mem_b_wr_req_2_i, 1) &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 1 &&
  skdecode_done == 1 &&
  t0_done == 1;
endproperty
run_RD_STG_WR_STG_3_to_IDLE_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_STG_WR_STG_3_to_IDLE_p);


property run_RD_STG_WR_s1_to_RD_STG_WR_STG_1_p;
  RD_STG_WR_s1 &&
  !s1s2_valid_in
|->
  ##1
  RD_STG_WR_STG_1 &&
  $stable(counter) &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_STG_WR_s1_to_RD_STG_WR_STG_1_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_STG_WR_s1_to_RD_STG_WR_STG_1_p);


property run_RD_STG_WR_s1_to_RD_STG_WR_s1_p;
  RD_STG_WR_s1 &&
  s1s2_valid_in
|->
  ##1
  RD_STG_WR_s1 &&
  $stable(counter) &&
  mem_a_wr_data == $past(decode_s1s2_a_0_i, 1) &&
  mem_b_wr_data == $past(decode_s1s2_b_0_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_STG_WR_s1_to_RD_STG_WR_s1_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_STG_WR_s1_to_RD_STG_WR_s1_p);


property run_RD_STG_WR_s2_to_RD_STG_WR_STG_2_p;
  RD_STG_WR_s2 &&
  !s1s2_valid_in
|->
  ##1
  RD_STG_WR_STG_2 &&
  $stable(counter) &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 1 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_STG_WR_s2_to_RD_STG_WR_STG_2_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_STG_WR_s2_to_RD_STG_WR_STG_2_p);


property run_RD_STG_WR_s2_to_RD_STG_WR_s2_p;
  RD_STG_WR_s2 &&
  s1s2_valid_in
|->
  ##1
  RD_STG_WR_s2 &&
  $stable(counter) &&
  mem_a_wr_data == $past(decode_s1s2_a_0_i, 1) &&
  mem_b_wr_data == $past(decode_s1s2_b_0_i, 1) &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_STG_WR_s2_to_RD_STG_WR_s2_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_STG_WR_s2_to_RD_STG_WR_s2_p);


property run_RD_STG_WR_t0_to_RD_STG_WR_STG_3_p;
  RD_STG_WR_t0 &&
  !t0_valid_in
|->
  ##1
  RD_STG_WR_STG_3 &&
  $stable(counter) &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 1 &&
  skdecode_done == 0 &&
  t0_done == 1;
endproperty
run_RD_STG_WR_t0_to_RD_STG_WR_STG_3_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_STG_WR_t0_to_RD_STG_WR_STG_3_p);


property run_RD_STG_WR_t0_to_RD_STG_WR_t0_p;
  RD_STG_WR_t0 &&
  t0_valid_in
|->
  ##1 ($stable(s1s2_stall_dummy_out)) and
  ##1
  RD_STG_WR_t0 &&
  $stable(counter) &&
  mem_a_wr_data == $past(decode_t0_0_i, 1) &&
  mem_b_wr_data == $past(decode_t0_0_i, 1) &&
  s1_done == 1 &&
  s2_done == 1 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_STG_WR_t0_to_RD_STG_WR_t0_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_STG_WR_t0_to_RD_STG_WR_t0_p);


property run_RD_WR_s1_to_RD_STG_WR_s1_p;
  RD_WR_s1 &&
  (counter[1:0] != 3) &&
  (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
  (counter != 10'hDF) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) >= 10'd224)
|->
  ##1
  RD_STG_WR_s1 &&
  counter == 10'd0 &&
  keymem_a_rd_req == $past(keymem_a_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data == $past(decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data == $past(decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(mem_b_wr_req_0_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s1_to_RD_STG_WR_s1_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_STG_WR_s1_p);


property run_RD_WR_s1_to_RD_STG_WR_s1_1_p;
  RD_WR_s1 &&
  (counter[1:0] != 3) &&
  (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
  (counter != 10'hDF) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) >= 10'd224)
|->
  ##1
  RD_STG_WR_s1 &&
  counter == 10'd0 &&
  keymem_a_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(keymem_a_rd_req_2_i, 1) &&
  mem_a_wr_data == $past(decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data == $past(decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(mem_b_wr_req_0_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s1_to_RD_STG_WR_s1_1_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_STG_WR_s1_1_p);


property run_RD_WR_s1_to_RD_STG_WR_s1_10_p;
  RD_WR_s1 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hDF)) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  !s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) >= 10'd224)
|->
  ##1
  RD_STG_WR_s1 &&
  counter == 10'd0 &&
  keymem_a_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(mem_b_wr_req_1_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s1_to_RD_STG_WR_s1_10_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_STG_WR_s1_10_p);


property run_RD_WR_s1_to_RD_STG_WR_s1_11_p;
  RD_WR_s1 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hDF)) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  !s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) >= 10'd224)
|->
  ##1
  RD_STG_WR_s1 &&
  counter == 10'd0 &&
  keymem_a_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(mem_b_wr_req_1_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s1_to_RD_STG_WR_s1_11_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_STG_WR_s1_11_p);


property run_RD_WR_s1_to_RD_STG_WR_s1_12_p;
  RD_WR_s1 &&
  (counter[1:0] == 3) &&
  (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
  (counter != 10'hDF) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) >= 10'd224)
|->
  ##1
  RD_STG_WR_s1 &&
  counter == 10'd0 &&
  keymem_a_rd_req == $past(keymem_a_rd_req_3_i, 1) &&
  keymem_b_rd_req == $past(keymem_b_rd_req_2_i, 1) &&
  mem_a_wr_data == $past(decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data == $past(decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(mem_b_wr_req_0_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s1_to_RD_STG_WR_s1_12_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_STG_WR_s1_12_p);


property run_RD_WR_s1_to_RD_STG_WR_s1_13_p;
  RD_WR_s1 &&
  (counter[1:0] == 3) &&
  (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
  (counter != 10'hDF) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) >= 10'd224)
|->
  ##1
  RD_STG_WR_s1 &&
  counter == 10'd0 &&
  keymem_a_rd_req == $past(keymem_b_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(keymem_a_rd_req_3_i, 1) &&
  mem_a_wr_data == $past(decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data == $past(decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(mem_b_wr_req_0_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s1_to_RD_STG_WR_s1_13_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_STG_WR_s1_13_p);


property run_RD_WR_s1_to_RD_STG_WR_s1_14_p;
  RD_WR_s1 &&
  (counter[1:0] == 3) &&
  (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
  (counter != 10'hDF) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  !s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) >= 10'd224)
|->
  ##1
  RD_STG_WR_s1 &&
  counter == 10'd0 &&
  keymem_a_rd_req == $past(keymem_a_rd_req_3_i, 1) &&
  keymem_b_rd_req == $past(keymem_b_rd_req_2_i, 1) &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(mem_b_wr_req_1_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s1_to_RD_STG_WR_s1_14_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_STG_WR_s1_14_p);


property run_RD_WR_s1_to_RD_STG_WR_s1_15_p;
  RD_WR_s1 &&
  (counter[1:0] == 3) &&
  (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
  (counter != 10'hDF) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  !s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) >= 10'd224)
|->
  ##1
  RD_STG_WR_s1 &&
  counter == 10'd0 &&
  keymem_a_rd_req == $past(keymem_b_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(keymem_a_rd_req_3_i, 1) &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(mem_b_wr_req_1_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s1_to_RD_STG_WR_s1_15_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_STG_WR_s1_15_p);


property run_RD_WR_s1_to_RD_STG_WR_s1_16_p;
  RD_WR_s1 &&
  (counter[1:0] == 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hDF)) &&
  (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
  s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) >= 10'd224)
|->
  ##1
  RD_STG_WR_s1 &&
  counter == 10'd0 &&
  keymem_a_rd_req == $past(keymem_b_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(keymem_a_rd_req_3_i, 1) &&
  mem_a_wr_data == $past(decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data == $past(decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(mem_b_wr_req_0_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s1_to_RD_STG_WR_s1_16_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_STG_WR_s1_16_p);


property run_RD_WR_s1_to_RD_STG_WR_s1_17_p;
  RD_WR_s1 &&
  (counter[1:0] == 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hDF)) &&
  (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
  s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) >= 10'd224)
|->
  ##1
  RD_STG_WR_s1 &&
  counter == 10'd0 &&
  keymem_a_rd_req == $past(keymem_a_rd_req_3_i, 1) &&
  keymem_b_rd_req == $past(keymem_b_rd_req_2_i, 1) &&
  mem_a_wr_data == $past(decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data == $past(decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(mem_b_wr_req_0_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s1_to_RD_STG_WR_s1_17_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_STG_WR_s1_17_p);


property run_RD_WR_s1_to_RD_STG_WR_s1_18_p;
  RD_WR_s1 &&
  (counter[1:0] == 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hDF)) &&
  (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
  !s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) >= 10'd224)
|->
  ##1
  RD_STG_WR_s1 &&
  counter == 10'd0 &&
  keymem_a_rd_req == $past(keymem_b_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(keymem_a_rd_req_3_i, 1) &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(mem_b_wr_req_1_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s1_to_RD_STG_WR_s1_18_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_STG_WR_s1_18_p);


property run_RD_WR_s1_to_RD_STG_WR_s1_19_p;
  RD_WR_s1 &&
  (counter[1:0] == 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hDF)) &&
  (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
  !s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) >= 10'd224)
|->
  ##1
  RD_STG_WR_s1 &&
  counter == 10'd0 &&
  keymem_a_rd_req == $past(keymem_a_rd_req_3_i, 1) &&
  keymem_b_rd_req == $past(keymem_b_rd_req_2_i, 1) &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(mem_b_wr_req_1_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s1_to_RD_STG_WR_s1_19_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_STG_WR_s1_19_p);


property run_RD_WR_s1_to_RD_STG_WR_s1_2_p;
  RD_WR_s1 &&
  (counter[1:0] != 3) &&
  (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
  (counter != 10'hDF) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  !s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) >= 10'd224)
|->
  ##1
  RD_STG_WR_s1 &&
  counter == 10'd0 &&
  keymem_a_rd_req == $past(keymem_a_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(mem_b_wr_req_1_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s1_to_RD_STG_WR_s1_2_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_STG_WR_s1_2_p);


property run_RD_WR_s1_to_RD_STG_WR_s1_20_p;
  RD_WR_s1 &&
  (counter[1:0] == 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hDF)) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) >= 10'd224)
|->
  ##1
  RD_STG_WR_s1 &&
  counter == 10'd0 &&
  keymem_a_rd_req == $past(keymem_b_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(keymem_b_rd_req_2_i, 1) &&
  mem_a_wr_data == $past(decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data == $past(decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(mem_b_wr_req_0_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s1_to_RD_STG_WR_s1_20_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_STG_WR_s1_20_p);


property run_RD_WR_s1_to_RD_STG_WR_s1_21_p;
  RD_WR_s1 &&
  (counter[1:0] == 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hDF)) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) >= 10'd224)
|->
  ##1
  RD_STG_WR_s1 &&
  counter == 10'd0 &&
  keymem_a_rd_req == $past(keymem_b_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(keymem_b_rd_req_2_i, 1) &&
  mem_a_wr_data == $past(decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data == $past(decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(mem_b_wr_req_0_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s1_to_RD_STG_WR_s1_21_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_STG_WR_s1_21_p);


property run_RD_WR_s1_to_RD_STG_WR_s1_22_p;
  RD_WR_s1 &&
  (counter[1:0] == 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hDF)) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  !s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) >= 10'd224)
|->
  ##1
  RD_STG_WR_s1 &&
  counter == 10'd0 &&
  keymem_a_rd_req == $past(keymem_b_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(keymem_b_rd_req_2_i, 1) &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(mem_b_wr_req_1_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s1_to_RD_STG_WR_s1_22_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_STG_WR_s1_22_p);


property run_RD_WR_s1_to_RD_STG_WR_s1_23_p;
  RD_WR_s1 &&
  (counter[1:0] == 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hDF)) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  !s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) >= 10'd224)
|->
  ##1
  RD_STG_WR_s1 &&
  counter == 10'd0 &&
  keymem_a_rd_req == $past(keymem_b_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(keymem_b_rd_req_2_i, 1) &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(mem_b_wr_req_1_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s1_to_RD_STG_WR_s1_23_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_STG_WR_s1_23_p);


property run_RD_WR_s1_to_RD_STG_WR_s1_3_p;
  RD_WR_s1 &&
  (counter[1:0] != 3) &&
  (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
  (counter != 10'hDF) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  !s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) >= 10'd224)
|->
  ##1
  RD_STG_WR_s1 &&
  counter == 10'd0 &&
  keymem_a_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(keymem_a_rd_req_2_i, 1) &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(mem_b_wr_req_1_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s1_to_RD_STG_WR_s1_3_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_STG_WR_s1_3_p);


property run_RD_WR_s1_to_RD_STG_WR_s1_4_p;
  RD_WR_s1 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hDF)) &&
  (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
  s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) >= 10'd224)
|->
  ##1
  RD_STG_WR_s1 &&
  counter == 10'd0 &&
  keymem_a_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(keymem_a_rd_req_2_i, 1) &&
  mem_a_wr_data == $past(decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data == $past(decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(mem_b_wr_req_0_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s1_to_RD_STG_WR_s1_4_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_STG_WR_s1_4_p);


property run_RD_WR_s1_to_RD_STG_WR_s1_5_p;
  RD_WR_s1 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hDF)) &&
  (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
  s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) >= 10'd224)
|->
  ##1
  RD_STG_WR_s1 &&
  counter == 10'd0 &&
  keymem_a_rd_req == $past(keymem_a_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data == $past(decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data == $past(decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(mem_b_wr_req_0_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s1_to_RD_STG_WR_s1_5_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_STG_WR_s1_5_p);


property run_RD_WR_s1_to_RD_STG_WR_s1_6_p;
  RD_WR_s1 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hDF)) &&
  (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
  !s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) >= 10'd224)
|->
  ##1
  RD_STG_WR_s1 &&
  counter == 10'd0 &&
  keymem_a_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(keymem_a_rd_req_2_i, 1) &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(mem_b_wr_req_1_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s1_to_RD_STG_WR_s1_6_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_STG_WR_s1_6_p);


property run_RD_WR_s1_to_RD_STG_WR_s1_7_p;
  RD_WR_s1 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hDF)) &&
  (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
  !s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) >= 10'd224)
|->
  ##1
  RD_STG_WR_s1 &&
  counter == 10'd0 &&
  keymem_a_rd_req == $past(keymem_a_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(mem_b_wr_req_1_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s1_to_RD_STG_WR_s1_7_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_STG_WR_s1_7_p);


property run_RD_WR_s1_to_RD_STG_WR_s1_8_p;
  RD_WR_s1 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hDF)) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) >= 10'd224)
|->
  ##1
  RD_STG_WR_s1 &&
  counter == 10'd0 &&
  keymem_a_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data == $past(decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data == $past(decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(mem_b_wr_req_0_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s1_to_RD_STG_WR_s1_8_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_STG_WR_s1_8_p);


property run_RD_WR_s1_to_RD_STG_WR_s1_9_p;
  RD_WR_s1 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hDF)) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) >= 10'd224)
|->
  ##1
  RD_STG_WR_s1 &&
  counter == 10'd0 &&
  keymem_a_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data == $past(decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data == $past(decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(mem_b_wr_req_0_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s1_to_RD_STG_WR_s1_9_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_STG_WR_s1_9_p);


property run_RD_WR_s1_to_RD_WR_s1_p;
  RD_WR_s1 &&
  (counter[1:0] != 3) &&
  (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
  (counter != 10'hDF) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) < 10'd224)
|->
  ##1
  RD_WR_s1 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(keymem_a_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data == $past(decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data == $past(decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(mem_b_wr_req_0_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s1_to_RD_WR_s1_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_p);


property run_RD_WR_s1_to_RD_WR_s1_1_p;
  RD_WR_s1 &&
  (counter[1:0] != 3) &&
  (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
  (counter != 10'hDF) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) < 10'd224)
|->
  ##1
  RD_WR_s1 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(keymem_a_rd_req_2_i, 1) &&
  mem_a_wr_data == $past(decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data == $past(decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(mem_b_wr_req_0_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s1_to_RD_WR_s1_1_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_1_p);


property run_RD_WR_s1_to_RD_WR_s1_10_p;
  RD_WR_s1 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hDF)) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  !s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) < 10'd224)
|->
  ##1
  RD_WR_s1 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(mem_b_wr_req_1_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s1_to_RD_WR_s1_10_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_10_p);


property run_RD_WR_s1_to_RD_WR_s1_11_p;
  RD_WR_s1 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hDF)) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  !s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) < 10'd224)
|->
  ##1
  RD_WR_s1 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(mem_b_wr_req_1_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s1_to_RD_WR_s1_11_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_11_p);


property run_RD_WR_s1_to_RD_WR_s1_12_p;
  RD_WR_s1 &&
  (counter[1:0] == 3) &&
  (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
  (counter != 10'hDF) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) < 10'd224)
|->
  ##1
  RD_WR_s1 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(keymem_a_rd_req_3_i, 1) &&
  keymem_b_rd_req == $past(keymem_b_rd_req_2_i, 1) &&
  mem_a_wr_data == $past(decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data == $past(decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(mem_b_wr_req_0_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s1_to_RD_WR_s1_12_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_12_p);


property run_RD_WR_s1_to_RD_WR_s1_13_p;
  RD_WR_s1 &&
  (counter[1:0] == 3) &&
  (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
  (counter != 10'hDF) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) < 10'd224)
|->
  ##1
  RD_WR_s1 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(keymem_b_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(keymem_a_rd_req_3_i, 1) &&
  mem_a_wr_data == $past(decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data == $past(decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(mem_b_wr_req_0_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s1_to_RD_WR_s1_13_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_13_p);


property run_RD_WR_s1_to_RD_WR_s1_14_p;
  RD_WR_s1 &&
  (counter[1:0] == 3) &&
  (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
  (counter != 10'hDF) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  !s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) < 10'd224)
|->
  ##1
  RD_WR_s1 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(keymem_a_rd_req_3_i, 1) &&
  keymem_b_rd_req == $past(keymem_b_rd_req_2_i, 1) &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(mem_b_wr_req_1_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s1_to_RD_WR_s1_14_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_14_p);


property run_RD_WR_s1_to_RD_WR_s1_15_p;
  RD_WR_s1 &&
  (counter[1:0] == 3) &&
  (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
  (counter != 10'hDF) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  !s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) < 10'd224)
|->
  ##1
  RD_WR_s1 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(keymem_b_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(keymem_a_rd_req_3_i, 1) &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(mem_b_wr_req_1_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s1_to_RD_WR_s1_15_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_15_p);


property run_RD_WR_s1_to_RD_WR_s1_16_p;
  RD_WR_s1 &&
  (counter[1:0] == 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hDF)) &&
  (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
  s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) < 10'd224)
|->
  ##1
  RD_WR_s1 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(keymem_b_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(keymem_a_rd_req_3_i, 1) &&
  mem_a_wr_data == $past(decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data == $past(decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(mem_b_wr_req_0_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s1_to_RD_WR_s1_16_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_16_p);


property run_RD_WR_s1_to_RD_WR_s1_17_p;
  RD_WR_s1 &&
  (counter[1:0] == 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hDF)) &&
  (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
  s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) < 10'd224)
|->
  ##1
  RD_WR_s1 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(keymem_a_rd_req_3_i, 1) &&
  keymem_b_rd_req == $past(keymem_b_rd_req_2_i, 1) &&
  mem_a_wr_data == $past(decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data == $past(decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(mem_b_wr_req_0_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s1_to_RD_WR_s1_17_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_17_p);


property run_RD_WR_s1_to_RD_WR_s1_18_p;
  RD_WR_s1 &&
  (counter[1:0] == 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hDF)) &&
  (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
  !s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) < 10'd224)
|->
  ##1
  RD_WR_s1 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(keymem_b_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(keymem_a_rd_req_3_i, 1) &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(mem_b_wr_req_1_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s1_to_RD_WR_s1_18_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_18_p);


property run_RD_WR_s1_to_RD_WR_s1_19_p;
  RD_WR_s1 &&
  (counter[1:0] == 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hDF)) &&
  (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
  !s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) < 10'd224)
|->
  ##1
  RD_WR_s1 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(keymem_a_rd_req_3_i, 1) &&
  keymem_b_rd_req == $past(keymem_b_rd_req_2_i, 1) &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(mem_b_wr_req_1_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s1_to_RD_WR_s1_19_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_19_p);


property run_RD_WR_s1_to_RD_WR_s1_2_p;
  RD_WR_s1 &&
  (counter[1:0] != 3) &&
  (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
  (counter != 10'hDF) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  !s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) < 10'd224)
|->
  ##1
  RD_WR_s1 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(keymem_a_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(mem_b_wr_req_1_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s1_to_RD_WR_s1_2_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_2_p);


property run_RD_WR_s1_to_RD_WR_s1_3_p;
  RD_WR_s1 &&
  (counter[1:0] != 3) &&
  (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
  (counter != 10'hDF) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  !s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) < 10'd224)
|->
  ##1
  RD_WR_s1 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(keymem_a_rd_req_2_i, 1) &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(mem_b_wr_req_1_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s1_to_RD_WR_s1_3_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_3_p);


property run_RD_WR_s1_to_RD_WR_s1_4_p;
  RD_WR_s1 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hDF)) &&
  (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
  s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) < 10'd224)
|->
  ##1
  RD_WR_s1 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(keymem_a_rd_req_2_i, 1) &&
  mem_a_wr_data == $past(decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data == $past(decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(mem_b_wr_req_0_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s1_to_RD_WR_s1_4_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_4_p);


property run_RD_WR_s1_to_RD_WR_s1_5_p;
  RD_WR_s1 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hDF)) &&
  (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
  s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) < 10'd224)
|->
  ##1
  RD_WR_s1 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(keymem_a_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data == $past(decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data == $past(decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(mem_b_wr_req_0_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s1_to_RD_WR_s1_5_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_5_p);


property run_RD_WR_s1_to_RD_WR_s1_6_p;
  RD_WR_s1 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hDF)) &&
  (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
  !s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) < 10'd224)
|->
  ##1
  RD_WR_s1 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(keymem_a_rd_req_2_i, 1) &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(mem_b_wr_req_1_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s1_to_RD_WR_s1_6_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_6_p);


property run_RD_WR_s1_to_RD_WR_s1_7_p;
  RD_WR_s1 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hDF)) &&
  (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
  !s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) < 10'd224)
|->
  ##1
  RD_WR_s1 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(keymem_a_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(mem_b_wr_req_1_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s1_to_RD_WR_s1_7_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_7_p);


property run_RD_WR_s1_to_RD_WR_s1_8_p;
  RD_WR_s1 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hDF)) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) < 10'd224)
|->
  ##1
  RD_WR_s1 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data == $past(decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data == $past(decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(mem_b_wr_req_0_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s1_to_RD_WR_s1_8_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_8_p);


property run_RD_WR_s1_to_RD_WR_s1_9_p;
  RD_WR_s1 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hDF)) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) < 10'd224)
|->
  ##1
  RD_WR_s1 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data == $past(decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data == $past(decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(mem_b_wr_req_0_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s1_to_RD_WR_s1_9_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_9_p);


property run_RD_WR_s2_to_RD_STG_WR_s2_p;
  RD_WR_s2 &&
  (counter[1:0] != 3) &&
  (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
  (counter != 10'hFF) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  !s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) >= 10'd256)
|->
  ##1
  RD_STG_WR_s2 &&
  counter == 10'd0 &&
  keymem_a_rd_req == $past(keymem_a_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(mem_b_wr_req_1_i, 1) &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s2_to_RD_STG_WR_s2_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_STG_WR_s2_p);


property run_RD_WR_s2_to_RD_STG_WR_s2_1_p;
  RD_WR_s2 &&
  (counter[1:0] != 3) &&
  (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
  (counter != 10'hFF) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  !s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) >= 10'd256)
|->
  ##1
  RD_STG_WR_s2 &&
  counter == 10'd0 &&
  keymem_a_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(keymem_a_rd_req_2_i, 1) &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(mem_b_wr_req_1_i, 1) &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s2_to_RD_STG_WR_s2_1_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_STG_WR_s2_1_p);


property run_RD_WR_s2_to_RD_STG_WR_s2_10_p;
  RD_WR_s2 &&
  (counter[1:0] == 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hFF)) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) >= 10'd256)
|->
  ##1
  RD_STG_WR_s2 &&
  counter == 10'd0 &&
  keymem_a_rd_req == $past(keymem_b_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(keymem_b_rd_req_2_i, 1) &&
  mem_a_wr_data == $past(decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data == $past(decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(mem_b_wr_req_0_i, 1) &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s2_to_RD_STG_WR_s2_10_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_STG_WR_s2_10_p);


property run_RD_WR_s2_to_RD_STG_WR_s2_11_p;
  RD_WR_s2 &&
  (counter[1:0] == 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hFF)) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) >= 10'd256)
|->
  ##1
  RD_STG_WR_s2 &&
  counter == 10'd0 &&
  keymem_a_rd_req == $past(keymem_b_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(keymem_b_rd_req_2_i, 1) &&
  mem_a_wr_data == $past(decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data == $past(decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(mem_b_wr_req_0_i, 1) &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s2_to_RD_STG_WR_s2_11_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_STG_WR_s2_11_p);


property run_RD_WR_s2_to_RD_STG_WR_s2_12_p;
  RD_WR_s2 &&
  (counter[1:0] == 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hFF)) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  !s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) >= 10'd256)
|->
  ##1
  RD_STG_WR_s2 &&
  counter == 10'd0 &&
  keymem_a_rd_req == $past(keymem_b_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(keymem_b_rd_req_2_i, 1) &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(mem_b_wr_req_1_i, 1) &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s2_to_RD_STG_WR_s2_12_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_STG_WR_s2_12_p);


property run_RD_WR_s2_to_RD_STG_WR_s2_13_p;
  RD_WR_s2 &&
  (counter[1:0] == 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hFF)) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  !s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) >= 10'd256)
|->
  ##1
  RD_STG_WR_s2 &&
  counter == 10'd0 &&
  keymem_a_rd_req == $past(keymem_b_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(keymem_b_rd_req_2_i, 1) &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(mem_b_wr_req_1_i, 1) &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s2_to_RD_STG_WR_s2_13_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_STG_WR_s2_13_p);


property run_RD_WR_s2_to_RD_STG_WR_s2_2_p;
  RD_WR_s2 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hFF)) &&
  (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
  !s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) >= 10'd256)
|->
  ##1
  RD_STG_WR_s2 &&
  counter == 10'd0 &&
  keymem_a_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(keymem_a_rd_req_2_i, 1) &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(mem_b_wr_req_1_i, 1) &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s2_to_RD_STG_WR_s2_2_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_STG_WR_s2_2_p);


property run_RD_WR_s2_to_RD_STG_WR_s2_3_p;
  RD_WR_s2 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hFF)) &&
  (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
  !s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) >= 10'd256)
|->
  ##1
  RD_STG_WR_s2 &&
  counter == 10'd0 &&
  keymem_a_rd_req == $past(keymem_a_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(mem_b_wr_req_1_i, 1) &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s2_to_RD_STG_WR_s2_3_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_STG_WR_s2_3_p);


property run_RD_WR_s2_to_RD_STG_WR_s2_4_p;
  RD_WR_s2 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hFF)) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  !s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) >= 10'd256)
|->
  ##1
  RD_STG_WR_s2 &&
  counter == 10'd0 &&
  keymem_a_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(mem_b_wr_req_1_i, 1) &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s2_to_RD_STG_WR_s2_4_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_STG_WR_s2_4_p);


property run_RD_WR_s2_to_RD_STG_WR_s2_5_p;
  RD_WR_s2 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hFF)) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  !s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) >= 10'd256)
|->
  ##1
  RD_STG_WR_s2 &&
  counter == 10'd0 &&
  keymem_a_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(mem_b_wr_req_1_i, 1) &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s2_to_RD_STG_WR_s2_5_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_STG_WR_s2_5_p);


property run_RD_WR_s2_to_RD_STG_WR_s2_6_p;
  RD_WR_s2 &&
  (counter[1:0] == 3) &&
  (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
  (counter != 10'hFF) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  !s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) >= 10'd256)
|->
  ##1
  RD_STG_WR_s2 &&
  counter == 10'd0 &&
  keymem_a_rd_req == $past(keymem_a_rd_req_3_i, 1) &&
  keymem_b_rd_req == $past(keymem_b_rd_req_2_i, 1) &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(mem_b_wr_req_1_i, 1) &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s2_to_RD_STG_WR_s2_6_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_STG_WR_s2_6_p);


property run_RD_WR_s2_to_RD_STG_WR_s2_7_p;
  RD_WR_s2 &&
  (counter[1:0] == 3) &&
  (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
  (counter != 10'hFF) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  !s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) >= 10'd256)
|->
  ##1
  RD_STG_WR_s2 &&
  counter == 10'd0 &&
  keymem_a_rd_req == $past(keymem_b_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(keymem_a_rd_req_3_i, 1) &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(mem_b_wr_req_1_i, 1) &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s2_to_RD_STG_WR_s2_7_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_STG_WR_s2_7_p);


property run_RD_WR_s2_to_RD_STG_WR_s2_8_p;
  RD_WR_s2 &&
  (counter[1:0] == 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hFF)) &&
  (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
  !s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) >= 10'd256)
|->
  ##1
  RD_STG_WR_s2 &&
  counter == 10'd0 &&
  keymem_a_rd_req == $past(keymem_b_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(keymem_a_rd_req_3_i, 1) &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(mem_b_wr_req_1_i, 1) &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s2_to_RD_STG_WR_s2_8_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_STG_WR_s2_8_p);


property run_RD_WR_s2_to_RD_STG_WR_s2_9_p;
  RD_WR_s2 &&
  (counter[1:0] == 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hFF)) &&
  (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
  !s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) >= 10'd256)
|->
  ##1
  RD_STG_WR_s2 &&
  counter == 10'd0 &&
  keymem_a_rd_req == $past(keymem_a_rd_req_3_i, 1) &&
  keymem_b_rd_req == $past(keymem_b_rd_req_2_i, 1) &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(mem_b_wr_req_1_i, 1) &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s2_to_RD_STG_WR_s2_9_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_STG_WR_s2_9_p);


property run_RD_WR_s2_to_RD_WR_s2_p;
  RD_WR_s2 &&
  (counter[1:0] != 3) &&
  (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
  (counter != 10'hFF) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) < 10'd256)
|->
  ##1
  RD_WR_s2 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(keymem_a_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data == $past(decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data == $past(decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(mem_b_wr_req_0_i, 1) &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s2_to_RD_WR_s2_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_p);


property run_RD_WR_s2_to_RD_WR_s2_1_p;
  RD_WR_s2 &&
  (counter[1:0] != 3) &&
  (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
  (counter != 10'hFF) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) < 10'd256)
|->
  ##1
  RD_WR_s2 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(keymem_a_rd_req_2_i, 1) &&
  mem_a_wr_data == $past(decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data == $past(decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(mem_b_wr_req_0_i, 1) &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s2_to_RD_WR_s2_1_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_1_p);


property run_RD_WR_s2_to_RD_WR_s2_10_p;
  RD_WR_s2 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hFF)) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  !s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) < 10'd256)
|->
  ##1
  RD_WR_s2 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(mem_b_wr_req_1_i, 1) &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s2_to_RD_WR_s2_10_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_10_p);


property run_RD_WR_s2_to_RD_WR_s2_11_p;
  RD_WR_s2 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hFF)) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  !s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) < 10'd256)
|->
  ##1
  RD_WR_s2 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(mem_b_wr_req_1_i, 1) &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s2_to_RD_WR_s2_11_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_11_p);


property run_RD_WR_s2_to_RD_WR_s2_12_p;
  RD_WR_s2 &&
  (counter[1:0] == 3) &&
  (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
  (counter != 10'hFF) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) < 10'd256)
|->
  ##1
  RD_WR_s2 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(keymem_a_rd_req_3_i, 1) &&
  keymem_b_rd_req == $past(keymem_b_rd_req_2_i, 1) &&
  mem_a_wr_data == $past(decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data == $past(decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(mem_b_wr_req_0_i, 1) &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s2_to_RD_WR_s2_12_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_12_p);


property run_RD_WR_s2_to_RD_WR_s2_13_p;
  RD_WR_s2 &&
  (counter[1:0] == 3) &&
  (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
  (counter != 10'hFF) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) < 10'd256)
|->
  ##1
  RD_WR_s2 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(keymem_b_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(keymem_a_rd_req_3_i, 1) &&
  mem_a_wr_data == $past(decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data == $past(decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(mem_b_wr_req_0_i, 1) &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s2_to_RD_WR_s2_13_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_13_p);


property run_RD_WR_s2_to_RD_WR_s2_14_p;
  RD_WR_s2 &&
  (counter[1:0] == 3) &&
  (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
  (counter != 10'hFF) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  !s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) < 10'd256)
|->
  ##1
  RD_WR_s2 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(keymem_a_rd_req_3_i, 1) &&
  keymem_b_rd_req == $past(keymem_b_rd_req_2_i, 1) &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(mem_b_wr_req_1_i, 1) &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s2_to_RD_WR_s2_14_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_14_p);


property run_RD_WR_s2_to_RD_WR_s2_15_p;
  RD_WR_s2 &&
  (counter[1:0] == 3) &&
  (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
  (counter != 10'hFF) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  !s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) < 10'd256)
|->
  ##1
  RD_WR_s2 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(keymem_b_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(keymem_a_rd_req_3_i, 1) &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(mem_b_wr_req_1_i, 1) &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s2_to_RD_WR_s2_15_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_15_p);


property run_RD_WR_s2_to_RD_WR_s2_16_p;
  RD_WR_s2 &&
  (counter[1:0] == 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hFF)) &&
  (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
  s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) < 10'd256)
|->
  ##1
  RD_WR_s2 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(keymem_b_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(keymem_a_rd_req_3_i, 1) &&
  mem_a_wr_data == $past(decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data == $past(decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(mem_b_wr_req_0_i, 1) &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s2_to_RD_WR_s2_16_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_16_p);


property run_RD_WR_s2_to_RD_WR_s2_17_p;
  RD_WR_s2 &&
  (counter[1:0] == 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hFF)) &&
  (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
  s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) < 10'd256)
|->
  ##1
  RD_WR_s2 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(keymem_a_rd_req_3_i, 1) &&
  keymem_b_rd_req == $past(keymem_b_rd_req_2_i, 1) &&
  mem_a_wr_data == $past(decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data == $past(decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(mem_b_wr_req_0_i, 1) &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s2_to_RD_WR_s2_17_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_17_p);


property run_RD_WR_s2_to_RD_WR_s2_18_p;
  RD_WR_s2 &&
  (counter[1:0] == 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hFF)) &&
  (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
  !s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) < 10'd256)
|->
  ##1
  RD_WR_s2 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(keymem_b_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(keymem_a_rd_req_3_i, 1) &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(mem_b_wr_req_1_i, 1) &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s2_to_RD_WR_s2_18_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_18_p);


property run_RD_WR_s2_to_RD_WR_s2_19_p;
  RD_WR_s2 &&
  (counter[1:0] == 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hFF)) &&
  (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
  !s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) < 10'd256)
|->
  ##1
  RD_WR_s2 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(keymem_a_rd_req_3_i, 1) &&
  keymem_b_rd_req == $past(keymem_b_rd_req_2_i, 1) &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(mem_b_wr_req_1_i, 1) &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s2_to_RD_WR_s2_19_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_19_p);


property run_RD_WR_s2_to_RD_WR_s2_2_p;
  RD_WR_s2 &&
  (counter[1:0] != 3) &&
  (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
  (counter != 10'hFF) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  !s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) < 10'd256)
|->
  ##1
  RD_WR_s2 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(keymem_a_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(mem_b_wr_req_1_i, 1) &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s2_to_RD_WR_s2_2_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_2_p);


property run_RD_WR_s2_to_RD_WR_s2_3_p;
  RD_WR_s2 &&
  (counter[1:0] != 3) &&
  (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
  (counter != 10'hFF) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  !s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) < 10'd256)
|->
  ##1
  RD_WR_s2 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(keymem_a_rd_req_2_i, 1) &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(mem_b_wr_req_1_i, 1) &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s2_to_RD_WR_s2_3_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_3_p);


property run_RD_WR_s2_to_RD_WR_s2_4_p;
  RD_WR_s2 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hFF)) &&
  (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
  s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) < 10'd256)
|->
  ##1
  RD_WR_s2 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(keymem_a_rd_req_2_i, 1) &&
  mem_a_wr_data == $past(decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data == $past(decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(mem_b_wr_req_0_i, 1) &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s2_to_RD_WR_s2_4_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_4_p);


property run_RD_WR_s2_to_RD_WR_s2_5_p;
  RD_WR_s2 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hFF)) &&
  (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
  s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) < 10'd256)
|->
  ##1
  RD_WR_s2 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(keymem_a_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data == $past(decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data == $past(decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(mem_b_wr_req_0_i, 1) &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s2_to_RD_WR_s2_5_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_5_p);


property run_RD_WR_s2_to_RD_WR_s2_6_p;
  RD_WR_s2 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hFF)) &&
  (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
  !s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) < 10'd256)
|->
  ##1
  RD_WR_s2 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(keymem_a_rd_req_2_i, 1) &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(mem_b_wr_req_1_i, 1) &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s2_to_RD_WR_s2_6_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_6_p);


property run_RD_WR_s2_to_RD_WR_s2_7_p;
  RD_WR_s2 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hFF)) &&
  (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
  !s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) < 10'd256)
|->
  ##1
  RD_WR_s2 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(keymem_a_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(mem_b_wr_req_1_i, 1) &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s2_to_RD_WR_s2_7_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_7_p);


property run_RD_WR_s2_to_RD_WR_s2_8_p;
  RD_WR_s2 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hFF)) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) < 10'd256)
|->
  ##1
  RD_WR_s2 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data == $past(decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data == $past(decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(mem_b_wr_req_0_i, 1) &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s2_to_RD_WR_s2_8_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_8_p);


property run_RD_WR_s2_to_RD_WR_s2_9_p;
  RD_WR_s2 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hFF)) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) < 10'd256)
|->
  ##1
  RD_WR_s2 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data == $past(decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data == $past(decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(mem_b_wr_req_0_i, 1) &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_s2_to_RD_WR_s2_9_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_9_p);


property run_RD_WR_t0_to_RD_STG_WR_t0_p;
  RD_WR_t0 &&
  t0_valid_in &&
  (fv_mem_wr_addr[0] == 0) &&
  ((10'd1 + counter) >= 10'd512)
|->
  ##1 ($stable(s1s2_stall_dummy_out)) and
  ##1
  RD_STG_WR_t0 &&
  counter == 10'd0 &&
  mem_a_wr_data == $past(decode_t0_0_i, 1) &&
  mem_a_wr_req == $past(mem_a_wr_req_2_i, 1) &&
  mem_b_wr_data == $past(decode_t0_0_i, 1) &&
  mem_b_wr_req == $past(mem_b_wr_req_2_i, 1) &&
  s1_done == 1 &&
  s2_done == 1 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_t0_to_RD_STG_WR_t0_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_t0_to_RD_STG_WR_t0_p);


property run_RD_WR_t0_to_RD_STG_WR_t0_1_p;
  RD_WR_t0 &&
  t0_valid_in &&
  (fv_mem_wr_addr[0] != 0) &&
  ((10'd1 + counter) >= 10'd512)
|->
  ##1 ($stable(s1s2_stall_dummy_out)) and
  ##1
  RD_STG_WR_t0 &&
  counter == 10'd0 &&
  mem_a_wr_data == $past(decode_t0_0_i, 1) &&
  mem_a_wr_req == $past(mem_b_wr_req_2_i, 1) &&
  mem_b_wr_data == $past(decode_t0_0_i, 1) &&
  mem_b_wr_req == $past(mem_a_wr_req_2_i, 1) &&
  s1_done == 1 &&
  s2_done == 1 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_t0_to_RD_STG_WR_t0_1_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_t0_to_RD_STG_WR_t0_1_p);


property run_RD_WR_t0_to_RD_STG_WR_t0_2_p;
  RD_WR_t0 &&
  !t0_valid_in &&
  ((10'd1 + counter) >= 10'd512)
|->
  ##1 ($stable(s1s2_stall_dummy_out)) and
  ##1
  RD_STG_WR_t0 &&
  counter == 10'd0 &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(mem_b_wr_req_2_i, 1) &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(mem_b_wr_req_2_i, 1) &&
  s1_done == 1 &&
  s2_done == 1 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_t0_to_RD_STG_WR_t0_2_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_t0_to_RD_STG_WR_t0_2_p);


property run_RD_WR_t0_to_RD_WR_t0_p;
  RD_WR_t0 &&
  t0_valid_in &&
  (fv_mem_wr_addr[0] == 0) &&
  ((10'd1 + counter) < 10'd512)
|->
  ##1 ($stable(s1s2_stall_dummy_out)) and
  ##1
  RD_WR_t0 &&
  counter == (10'd1 + $past(counter, 1)) &&
  mem_a_wr_data == $past(decode_t0_0_i, 1) &&
  mem_a_wr_req == $past(mem_a_wr_req_2_i, 1) &&
  mem_b_wr_data == $past(decode_t0_0_i, 1) &&
  mem_b_wr_req == $past(mem_b_wr_req_2_i, 1) &&
  s1_done == 1 &&
  s2_done == 1 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_t0_to_RD_WR_t0_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_t0_to_RD_WR_t0_p);


property run_RD_WR_t0_to_RD_WR_t0_1_p;
  RD_WR_t0 &&
  t0_valid_in &&
  (fv_mem_wr_addr[0] != 0) &&
  ((10'd1 + counter) < 10'd512)
|->
  ##1 ($stable(s1s2_stall_dummy_out)) and
  ##1
  RD_WR_t0 &&
  counter == (10'd1 + $past(counter, 1)) &&
  mem_a_wr_data == $past(decode_t0_0_i, 1) &&
  mem_a_wr_req == $past(mem_b_wr_req_2_i, 1) &&
  mem_b_wr_data == $past(decode_t0_0_i, 1) &&
  mem_b_wr_req == $past(mem_a_wr_req_2_i, 1) &&
  s1_done == 1 &&
  s2_done == 1 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_t0_to_RD_WR_t0_1_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_t0_to_RD_WR_t0_1_p);


property run_RD_WR_t0_to_RD_WR_t0_2_p;
  RD_WR_t0 &&
  !t0_valid_in &&
  ((10'd1 + counter) < 10'd512)
|->
  ##1 ($stable(s1s2_stall_dummy_out)) and
  ##1
  RD_WR_t0 &&
  counter == (10'd1 + $past(counter, 1)) &&
  mem_a_wr_data == mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(mem_b_wr_req_2_i, 1) &&
  mem_b_wr_data == mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(mem_b_wr_req_2_i, 1) &&
  s1_done == 1 &&
  s2_done == 1 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
run_RD_WR_t0_to_RD_WR_t0_2_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_t0_to_RD_WR_t0_2_p);


property run_IDLE_wait_p;
  IDLE &&
  !start_port_vld
|->
  ##1 ($stable(mem_a_wr_data)) and
  ##1 ($stable(mem_b_wr_data)) and
  ##1 ($stable(s1s2_stall_dummy_out)) and
  ##1
  IDLE &&
  $stable(counter);
endproperty
run_IDLE_wait_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_IDLE_wait_p);

property s1s2_enable_p;
  (RD_WR_s1 || RD_WR_s2) 
  |=>
  skdecode_top.s1s2_enable
;endproperty
run_s1s2_enable_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) s1s2_enable_p);

property s1s2_no_enable_p;
  !(RD_WR_s1 || RD_WR_s2) 
  |=>
  !skdecode_top.s1s2_enable
;endproperty
run_s1s2_no_enable_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) s1s2_no_enable_p);

property t0_enable_p;
  (RD_WR_t0) 
  |=>
  skdecode_top.t0_enable
;endproperty
run_t0_enable_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) t0_enable_p);

property t0_no_enable_p;
  !(RD_WR_t0) 
  |=>
  !skdecode_top.t0_enable
;endproperty
run_t0_no_enable_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) t0_no_enable_p);

property run_IDLE_eventually_left_p;
  IDLE
|->
  s_eventually(!IDLE);
endproperty
run_IDLE_eventually_left_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_IDLE_eventually_left_p);


property run_RD_WR_s1_eventually_left_p;
  RD_WR_s1
|->
  s_eventually(!RD_WR_s1);
endproperty
run_RD_WR_s1_eventually_left_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_eventually_left_p);


property run_RD_STG_WR_s1_eventually_left_p;
  RD_STG_WR_s1
|->
  s_eventually(!RD_STG_WR_s1);
endproperty
run_RD_STG_WR_s1_eventually_left_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_STG_WR_s1_eventually_left_p);


property run_RD_STG_WR_STG_1_eventually_left_p;
  RD_STG_WR_STG_1
|->
  s_eventually(!RD_STG_WR_STG_1);
endproperty
run_RD_STG_WR_STG_1_eventually_left_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_STG_WR_STG_1_eventually_left_p);


property run_RD_WR_s2_eventually_left_p;
  RD_WR_s2
|->
  s_eventually(!RD_WR_s2);
endproperty
run_RD_WR_s2_eventually_left_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_eventually_left_p);


property run_RD_STG_WR_s2_eventually_left_p;
  RD_STG_WR_s2
|->
  s_eventually(!RD_STG_WR_s2);
endproperty
run_RD_STG_WR_s2_eventually_left_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_STG_WR_s2_eventually_left_p);


property run_RD_STG_WR_STG_2_eventually_left_p;
  RD_STG_WR_STG_2
|->
  s_eventually(!RD_STG_WR_STG_2);
endproperty
run_RD_STG_WR_STG_2_eventually_left_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_STG_WR_STG_2_eventually_left_p);


property run_RD_WR_t0_eventually_left_p;
  RD_WR_t0
|->
  s_eventually(!RD_WR_t0);
endproperty
run_RD_WR_t0_eventually_left_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_t0_eventually_left_p);


property run_RD_STG_WR_t0_eventually_left_p;
  RD_STG_WR_t0
|->
  s_eventually(!RD_STG_WR_t0);
endproperty
run_RD_STG_WR_t0_eventually_left_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_STG_WR_t0_eventually_left_p);


property run_RD_STG_WR_STG_3_eventually_left_p;
  RD_STG_WR_STG_3
|->
  s_eventually(!RD_STG_WR_STG_3);
endproperty
run_RD_STG_WR_STG_3_eventually_left_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_STG_WR_STG_3_eventually_left_p);


parameter CONSISTENCY = 1;
if (CONSISTENCY) begin
  // Check that no more than 1 state condition is met at the same time
  run_consistency_onehot0_state: assert property($onehot0({ IDLE, RD_STG_WR_STG_1, RD_STG_WR_STG_2, RD_STG_WR_STG_3, RD_STG_WR_s1, RD_STG_WR_s2, RD_STG_WR_t0, RD_WR_s1, RD_WR_s2, RD_WR_t0 }));
end


endmodule
