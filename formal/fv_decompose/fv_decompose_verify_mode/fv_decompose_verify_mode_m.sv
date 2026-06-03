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
// | Created on 14.01.2025 at 10:17                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import decompose_verify_mode_pkg::*;
import decompose_defines_pkg::*;
import decompose_verify_mode_pkg::*;
import decompose_verify_mode_functions::*;


module fv_decompose_verify_mode_m(
  input logic rst_n,
  input logic clk,

  // Ports
  input logic start_port_vld,
  input logic start_port_rdy,
  input st_BaseAddress start_port,

  input logic unsigned [13:0] cnt_new,

  input logic mem_rd_req_vld,
  input st_mem_if_t mem_rd_req,

  input logic mem_wr_req_vld,
  input st_mem_if_t mem_wr_req,

  input logic mem_hint_rd_req_vld,
  input st_mem_if_t mem_hint_rd_req,

  input logic z_mem_wr_req_vld,
  input st_mem_if_t z_mem_wr_req,

  input logic unsigned [13:0] current_cnt,

  input logic unsigned [3:0] mod_ready_port,

  input logic mod_enable_port,

  input a_unsigned_23_4 r0_mod_q_port,

  input a_unsigned_23_4 rd_data_port,

  input a_unsigned_1_4 hint_rd_data_port,

  input a_unsigned_23_4 r0_in,

  input a_unsigned_23_4 r0,

  input a_unsigned_4_4 r1_reg_in,

  input a_unsigned_4_4 r1_reg,

  input a_unsigned_23_4 mem_wr_data,

  input a_unsigned_1_4 z_neq_z,

  input a_unsigned_4_4 r1_usehint,

  input a_unsigned_4_4 usehint_w1_mux,

  input a_unsigned_16_4 w1_o,

  input a_unsigned_16_4 w1_o_in,

  input logic buffer_en,

  input logic decompose_done,

  // Registers
  input st_BaseAddress base_address,

  // States
  input logic IDLE,
  input logic REQ_1ST_DATA,
  input logic REQ_2ND_DATA,
  input logic REQ_3RD_DATA,
  input logic RD_MEM_WR_MEM,
  input logic RESP_LAST_DATA,
  input logic IDLE_BUFFER_EN
);


default clocking default_clk @(posedge clk); endclocking


st_BaseAddress base_address_0_i;
assign base_address_0_i = '{
  source: 14'd0,
  destination: 14'd0,
  hint_source: 14'd0
};

a_unsigned_1_4 h_0_i;
assign h_0_i = '{
  0: 1'd0,
  1: 1'd0,
  2: 1'd0,
  3: 1'd0
};

st_mem_if_t hint_rd_req_IDLE_34C0;
assign hint_rd_req_IDLE_34C0 = '{
  rd_wr_en: RW_IDLE,
  addr: 14'h34C0
};

st_mem_if_t req_IDLE_0;
assign req_IDLE_0 = '{
  rd_wr_en: RW_IDLE,
  addr: 14'd0
};

a_unsigned_23_4 mem_wr_data_0_i;
assign mem_wr_data_0_i = '{
  0: 23'd0,
  1: 23'd0,
  2: 23'd0,
  3: 23'd0
};

a_unsigned_4_4 r1_0_i;
assign r1_0_i = '{
  0: 4'd0,
  1: 4'd0,
  2: 4'd0,
  3: 4'd0
};

a_unsigned_16_4 w1_o_0_i;
assign w1_o_0_i = '{
  0: 16'd0,
  1: 16'd0,
  2: 16'd0,
  3: 16'd0
};

a_unsigned_23_4 compute_r0_2_0_i;
assign compute_r0_2_0_i = compute_r0_2(rd_data_port, mod_ready_port, r0_mod_q_port);

a_unsigned_4_4 compute_r1_0_i;
assign compute_r1_0_i = compute_r1(rd_data_port);

st_mem_if_t hint_rd_req_READ_base_hint_src;
assign hint_rd_req_READ_base_hint_src = '{
  rd_wr_en: RW_READ,
  addr: start_port.hint_source
};

st_mem_if_t rd_req_READ_base_src;
assign rd_req_READ_base_src = '{
  rd_wr_en: RW_READ,
  addr: start_port.source
};

st_mem_if_t hint_rd_req_READ_base_hint_src_plus_1;
assign hint_rd_req_READ_base_hint_src_plus_1 = '{
  rd_wr_en: RW_READ,
  addr: (64'd1 + ({ 50'h0, base_address.hint_source} ))
};

st_mem_if_t rd_req_READ_base_src_plus_1;
assign rd_req_READ_base_src_plus_1 = '{
  rd_wr_en: RW_READ,
  addr: (64'd1 + ({ 50'h0, base_address.source} ))
};

a_unsigned_23_4 compute_r0_0_i;
assign compute_r0_0_i = compute_r0(rd_data_port);

st_mem_if_t hint_rd_req_READ_base_hint_src_plus_2;
assign hint_rd_req_READ_base_hint_src_plus_2 = '{
  rd_wr_en: RW_READ,
  addr: (64'd2 + ({ 50'h0, base_address.hint_source} ))
};

st_mem_if_t rd_req_READ_base_src_plus_2;
assign rd_req_READ_base_src_plus_2 = '{
  rd_wr_en: RW_READ,
  addr: (64'd2 + ({ 50'h0, base_address.source} ))
};

a_unsigned_4_4 compute_r1_usehint_0_i;
assign compute_r1_usehint_0_i = compute_r1_usehint(r1_reg_in, r0_in, '{ 0: 1'd1, 1: 1'd1, 2: 1'd1, 3: 1'd1 });

a_unsigned_4_4 compute_r1_usehint_1_i;
assign compute_r1_usehint_1_i = compute_r1_usehint(r1_reg_in, r0_in, hint_rd_data_port);

st_mem_if_t hint_rd_req_READ_base_hint_src_plus_3;
assign hint_rd_req_READ_base_hint_src_plus_3 = '{
  rd_wr_en: RW_READ,
  addr: (64'd3 + ({ 50'h0, base_address.hint_source} ))
};

st_mem_if_t rd_req_READ_base_src_plus_3;
assign rd_req_READ_base_src_plus_3 = '{
  rd_wr_en: RW_READ,
  addr: (64'd3 + ({ 50'h0, base_address.source} ))
};

st_mem_if_t hint_rd_req_READ_base_hint_src_plus_cnt_plus_4;
assign hint_rd_req_READ_base_hint_src_plus_cnt_plus_4 = '{
  rd_wr_en: RW_READ,
  addr: ((64'd4 + ({ 50'h0, base_address.hint_source} )) + current_cnt)
};

st_mem_if_t rd_req_READ_base_src_plus_cnt_plus_4;
assign rd_req_READ_base_src_plus_cnt_plus_4 = '{
  rd_wr_en: RW_READ,
  addr: ((64'd4 + ({ 50'h0, base_address.source} )) + current_cnt)
};

a_unsigned_23_4 compute_r0_3_0_i;
assign compute_r0_3_0_i = compute_r0_3(rd_data_port, mod_enable_port, r0_mod_q_port);

st_mem_if_t compute_mem_rd_req_IDLE_0;
assign compute_mem_rd_req_IDLE_0 = '{
  rd_wr_en: RW_IDLE,
  addr: $stable(decompose.dcmp_ctrl_inst.read_fsm_state_ns) ? base_address.source : '0
};

st_mem_if_t compute_mem_hint_rd_req_IDLE_0;
assign compute_mem_hint_rd_req_IDLE_0 = '{
  rd_wr_en: RW_IDLE,
  addr: $stable(decompose.dcmp_ctrl_inst.read_fsm_state_ns) ? base_address.hint_source : 'h34c0
};

st_mem_if_t hint_rd_req_IDLE_base_hint_src;
assign hint_rd_req_IDLE_base_hint_src = '{
  rd_wr_en: RW_IDLE,
  addr: base_address.hint_source
};

st_mem_if_t rd_req_IDLE_base_src;
assign rd_req_IDLE_base_src = '{
  rd_wr_en: RW_IDLE,
  addr: base_address.source
};


sequence reset_sequence;
  !rst_n ##1 rst_n;
endsequence


property run_reset_p;
  $past(!decompose.reset_n || decompose.zeroize) |->
  IDLE &&
  buffer_en == 0 &&
  cnt_new == 14'h2C80 &&
  decompose_done == 1 &&
  mem_hint_rd_req == hint_rd_req_IDLE_34C0 &&
  mem_rd_req == req_IDLE_0 &&
  mem_wr_data == mem_wr_data_0_i &&
  mem_wr_req == req_IDLE_0 &&
  r0 == mem_wr_data_0_i &&
  r1_reg == r1_0_i &&
  r1_usehint == r1_0_i &&
  usehint_w1_mux == r1_0_i &&
  w1_o == w1_o_0_i &&
  z_mem_wr_req == req_IDLE_0 &&
  z_neq_z == h_0_i;
endproperty
run_reset_a: assert property (run_reset_p);


property run_IDLE_BUFFER_EN_to_IDLE_p;
  IDLE_BUFFER_EN
|->
  ##1 ($stable(w1_o)) and
  ##1
  IDLE &&
  buffer_en == 0 &&
  cnt_new == 14'd0 &&
  decompose_done == 1 &&
  mem_hint_rd_req == hint_rd_req_IDLE_base_hint_src &&
  mem_rd_req == rd_req_IDLE_base_src &&
  mem_wr_data == mem_wr_data_0_i &&
  mem_wr_req == req_IDLE_0 &&
  r0 == $past(compute_r0_2_0_i, 1) &&
  r1_reg == $past(compute_r1_0_i, 1) &&
  r1_usehint == r1_0_i &&
  usehint_w1_mux == r1_0_i &&
  z_mem_wr_req == req_IDLE_0 &&
  z_neq_z == h_0_i;
endproperty
run_IDLE_BUFFER_EN_to_IDLE_a: assert property (disable iff(!rst_n) run_IDLE_BUFFER_EN_to_IDLE_p);


property run_IDLE_to_REQ_1ST_DATA_p;
  IDLE &&
  start_port_vld
|->
  ##1 ($stable(w1_o)) and
  ##1
  REQ_1ST_DATA &&
  buffer_en == 0 &&
  cnt_new == 14'd0 &&
  decompose_done == 0 &&
  mem_hint_rd_req == hint_rd_req_READ_base_hint_src &&
  mem_rd_req == rd_req_READ_base_src &&
  mem_wr_data == mem_wr_data_0_i &&
  mem_wr_req == req_IDLE_0 &&
  r0 == $past(compute_r0_2_0_i, 1) &&
  r1_reg == $past(compute_r1_0_i, 1) &&
  r1_usehint == r1_0_i &&
  usehint_w1_mux == r1_0_i &&
  z_mem_wr_req == req_IDLE_0 &&
  z_neq_z == h_0_i;
endproperty
run_IDLE_to_REQ_1ST_DATA_a: assert property (disable iff(!rst_n) run_IDLE_to_REQ_1ST_DATA_p);


property run_RD_MEM_WR_MEM_to_RD_MEM_WR_MEM_p;
  RD_MEM_WR_MEM &&
  ((64'd3 + current_cnt) < 64'd511) &&
  (current_cnt < 64'd510)
|->
  ##1
  RD_MEM_WR_MEM &&
  buffer_en == is_buffer($past(current_cnt, 1)) &&
  cnt_new == 14'((64'd1 + $past(current_cnt, 1))) &&
  decompose_done == 0 &&
  mem_hint_rd_req == $past(hint_rd_req_READ_base_hint_src_plus_cnt_plus_4, 1) &&
  mem_rd_req == $past(rd_req_READ_base_src_plus_cnt_plus_4, 1) &&
  mem_wr_data == mem_wr_data_0_i &&
  mem_wr_req == req_IDLE_0 &&
  r0 == $past(compute_r0_0_i, 1) &&
  r1_reg == $past(compute_r1_0_i, 1) &&
  r1_usehint == $past(compute_r1_usehint_1_i, 1) &&
  usehint_w1_mux == $past(compute_r1_usehint_0_i, 1) &&
  w1_o == $past(w1_o_in, 1) &&
  z_mem_wr_req == req_IDLE_0 &&
  z_neq_z == h_0_i;
endproperty
run_RD_MEM_WR_MEM_to_RD_MEM_WR_MEM_a: assert property (disable iff(!rst_n) run_RD_MEM_WR_MEM_to_RD_MEM_WR_MEM_p);


property run_RD_MEM_WR_MEM_to_RD_MEM_WR_MEM_1_p;
  RD_MEM_WR_MEM &&
  ((64'd3 + current_cnt) >= 64'd511) &&
  (current_cnt < 64'd510)
|->
  ##1
  RD_MEM_WR_MEM &&
  buffer_en == is_buffer($past(current_cnt, 1)) &&
  cnt_new == 14'((64'd1 + $past(current_cnt, 1))) &&
  decompose_done == 0 &&
  mem_wr_data == mem_wr_data_0_i &&
  mem_hint_rd_req == $past(compute_mem_hint_rd_req_IDLE_0, 1) &&
  mem_rd_req == $past(compute_mem_rd_req_IDLE_0, 1) &&
  mem_wr_req == req_IDLE_0 &&
  r0 == $past(compute_r0_0_i, 1) &&
  r1_reg == $past(compute_r1_0_i, 1) &&
  r1_usehint == $past(compute_r1_usehint_1_i, 1) &&
  usehint_w1_mux == $past(compute_r1_usehint_0_i, 1) &&
  w1_o == $past(w1_o_in, 1) &&
  z_mem_wr_req == req_IDLE_0 &&
  z_neq_z == h_0_i;
endproperty
run_RD_MEM_WR_MEM_to_RD_MEM_WR_MEM_1_a: assert property (disable iff(!rst_n) run_RD_MEM_WR_MEM_to_RD_MEM_WR_MEM_1_p);


property run_RD_MEM_WR_MEM_to_RESP_LAST_DATA_p;
  RD_MEM_WR_MEM &&
  ((64'd3 + current_cnt) < 64'd511) &&
  (current_cnt >= 64'd510)
|->
  ##1
  RESP_LAST_DATA &&
  buffer_en == is_buffer($past(current_cnt, 1)) &&
  cnt_new == 14'((64'd1 + $past(current_cnt, 1))) &&
  decompose_done == 0 &&
  mem_hint_rd_req == $past(hint_rd_req_READ_base_hint_src_plus_cnt_plus_4, 1) &&
  mem_rd_req == $past(rd_req_READ_base_src_plus_cnt_plus_4, 1) &&
  mem_wr_data == mem_wr_data_0_i &&
  mem_wr_req == req_IDLE_0 &&
  r0 == $past(compute_r0_3_0_i, 1) &&
  r1_reg == $past(compute_r1_0_i, 1) &&
  r1_usehint == $past(compute_r1_usehint_1_i, 1) &&
  usehint_w1_mux == $past(compute_r1_usehint_0_i, 1) &&
  w1_o == $past(w1_o_in, 1) &&
  z_mem_wr_req == req_IDLE_0 &&
  z_neq_z == h_0_i;
endproperty
run_RD_MEM_WR_MEM_to_RESP_LAST_DATA_a: assert property (disable iff(!rst_n) run_RD_MEM_WR_MEM_to_RESP_LAST_DATA_p);


property run_RD_MEM_WR_MEM_to_RESP_LAST_DATA_1_p;
  RD_MEM_WR_MEM &&
  ((64'd3 + current_cnt) >= 64'd511) &&
  (current_cnt >= 64'd510)
|->
  ##1
  RESP_LAST_DATA &&
  buffer_en == is_buffer($past(current_cnt, 1)) &&
  cnt_new == 14'((64'd1 + $past(current_cnt, 1))) &&
  decompose_done == 0 &&
  mem_wr_data == mem_wr_data_0_i &&
  mem_hint_rd_req == hint_rd_req_IDLE_base_hint_src &&
  mem_rd_req == rd_req_IDLE_base_src &&
  mem_wr_req == req_IDLE_0 &&
  r0 == $past(compute_r0_3_0_i, 1) &&
  r1_reg == $past(compute_r1_0_i, 1) &&
  r1_usehint == $past(compute_r1_usehint_1_i, 1) &&
  usehint_w1_mux == $past(compute_r1_usehint_0_i, 1) &&
  w1_o == $past(w1_o_in, 1) &&
  z_mem_wr_req == req_IDLE_0 &&
  z_neq_z == h_0_i;
endproperty
run_RD_MEM_WR_MEM_to_RESP_LAST_DATA_1_a: assert property (disable iff(!rst_n) run_RD_MEM_WR_MEM_to_RESP_LAST_DATA_1_p);


property run_REQ_1ST_DATA_to_REQ_2ND_DATA_p;
  REQ_1ST_DATA
|->
  ##1 ($stable(cnt_new)) and
  ##1 ($stable(w1_o)) and
  ##1
  REQ_2ND_DATA &&
  buffer_en == 0 &&
  decompose_done == 0 &&
  mem_hint_rd_req == hint_rd_req_READ_base_hint_src_plus_1 &&
  mem_rd_req == rd_req_READ_base_src_plus_1 &&
  mem_wr_data == mem_wr_data_0_i &&
  mem_wr_req == req_IDLE_0 &&
  r0 == $past(compute_r0_2_0_i, 1) &&
  r1_reg == $past(compute_r1_0_i, 1) &&
  r1_usehint == r1_0_i &&
  usehint_w1_mux == r1_0_i &&
  z_mem_wr_req == req_IDLE_0 &&
  z_neq_z == h_0_i;
endproperty
run_REQ_1ST_DATA_to_REQ_2ND_DATA_a: assert property (disable iff(!rst_n) run_REQ_1ST_DATA_to_REQ_2ND_DATA_p);


property run_REQ_2ND_DATA_to_REQ_3RD_DATA_p;
  REQ_2ND_DATA
|->
  ##1 ($stable(cnt_new)) and
  ##1 ($stable(w1_o)) and
  ##1
  REQ_3RD_DATA &&
  buffer_en == 0 &&
  decompose_done == 0 &&
  mem_hint_rd_req == hint_rd_req_READ_base_hint_src_plus_2 &&
  mem_rd_req == rd_req_READ_base_src_plus_2 &&
  mem_wr_data == mem_wr_data_0_i &&
  mem_wr_req == req_IDLE_0 &&
  r0 == $past(compute_r0_0_i, 1) &&
  r1_reg == $past(compute_r1_0_i, 1) &&
  r1_usehint == r1_0_i &&
  usehint_w1_mux == r1_0_i &&
  z_mem_wr_req == req_IDLE_0 &&
  z_neq_z == h_0_i;
endproperty
run_REQ_2ND_DATA_to_REQ_3RD_DATA_a: assert property (disable iff(!rst_n) run_REQ_2ND_DATA_to_REQ_3RD_DATA_p);


property run_REQ_3RD_DATA_to_RD_MEM_WR_MEM_p;
  REQ_3RD_DATA
|->
  ##1 ($stable(cnt_new)) and
  ##1 ($stable(w1_o)) and
  ##1
  RD_MEM_WR_MEM &&
  buffer_en == 0 &&
  decompose_done == 0 &&
  mem_hint_rd_req == hint_rd_req_READ_base_hint_src_plus_3 &&
  mem_rd_req == rd_req_READ_base_src_plus_3 &&
  mem_wr_data == mem_wr_data_0_i &&
  mem_wr_req == req_IDLE_0 &&
  r0 == $past(compute_r0_0_i, 1) &&
  r1_reg == $past(compute_r1_0_i, 1) &&
  r1_usehint == $past(compute_r1_usehint_1_i, 1) &&
  usehint_w1_mux == $past(compute_r1_usehint_0_i, 1) &&
  z_mem_wr_req == req_IDLE_0 &&
  z_neq_z == h_0_i;
endproperty
run_REQ_3RD_DATA_to_RD_MEM_WR_MEM_a: assert property (disable iff(!rst_n) run_REQ_3RD_DATA_to_RD_MEM_WR_MEM_p);


property run_RESP_LAST_DATA_to_IDLE_BUFFER_EN_p;
  RESP_LAST_DATA
|->
  ##1
  IDLE_BUFFER_EN &&
  buffer_en == 1 &&
  cnt_new == 14'h2C80 &&
  decompose_done == 1 &&
  mem_wr_data == mem_wr_data_0_i &&
  mem_hint_rd_req == hint_rd_req_IDLE_base_hint_src &&
  mem_rd_req == rd_req_IDLE_base_src &&
  mem_wr_req == req_IDLE_0 &&
  r0 == $past(compute_r0_2_0_i, 1) &&
  r1_reg == $past(compute_r1_0_i, 1) &&
  r1_usehint == r1_0_i &&
  usehint_w1_mux == r1_0_i &&
  w1_o == $past(w1_o_in, 1) &&
  z_mem_wr_req == req_IDLE_0 &&
  z_neq_z == h_0_i;
endproperty
run_RESP_LAST_DATA_to_IDLE_BUFFER_EN_a: assert property (disable iff(!rst_n) run_RESP_LAST_DATA_to_IDLE_BUFFER_EN_p);


property run_IDLE_wait_p;
  IDLE &&
  !start_port_vld
|->
  ##1 ($stable(buffer_en)) and
  ##1 cnt_new == 0 and
  ##1 ($stable(decompose_done)) and
  ##1 ($stable(mem_wr_data)) and
  ##1 r0 == $past(compute_r0_2_0_i, 1) and
  ##1 r1_reg == $past(compute_r1_0_i, 1) and
  ##1 ($stable(r1_usehint)) and
  ##1 ($stable(usehint_w1_mux)) and
  ##1 ($stable(w1_o)) and
  ##1 ($stable(z_neq_z)) and
  ##1 ($stable(mem_wr_req)) and
  ##1 mem_rd_req == rd_req_IDLE_base_src and
  ##1 ($stable(z_mem_wr_req)) and
  ##1 mem_hint_rd_req == hint_rd_req_IDLE_base_hint_src and
  ##1
  IDLE;
endproperty
run_IDLE_wait_a: assert property (disable iff(!rst_n) run_IDLE_wait_p);


property run_IDLE_eventually_left_p;
  IDLE &&
  start_port_vld
|->
  s_eventually(!IDLE);
endproperty
run_IDLE_eventually_left_a: assert property (disable iff(!rst_n) run_IDLE_eventually_left_p);


property run_REQ_1ST_DATA_eventually_left_p;
  REQ_1ST_DATA
|->
  s_eventually(!REQ_1ST_DATA);
endproperty
run_REQ_1ST_DATA_eventually_left_a: assert property (disable iff(!rst_n) run_REQ_1ST_DATA_eventually_left_p);


property run_REQ_2ND_DATA_eventually_left_p;
  REQ_2ND_DATA
|->
  s_eventually(!REQ_2ND_DATA);
endproperty
run_REQ_2ND_DATA_eventually_left_a: assert property (disable iff(!rst_n) run_REQ_2ND_DATA_eventually_left_p);


property run_REQ_3RD_DATA_eventually_left_p;
  REQ_3RD_DATA
|->
  s_eventually(!REQ_3RD_DATA);
endproperty
run_REQ_3RD_DATA_eventually_left_a: assert property (disable iff(!rst_n) run_REQ_3RD_DATA_eventually_left_p);


property run_RD_MEM_WR_MEM_eventually_left_p;
  RD_MEM_WR_MEM
|->
  s_eventually(!RD_MEM_WR_MEM);
endproperty
run_RD_MEM_WR_MEM_eventually_left_a: assert property (disable iff(!rst_n) run_RD_MEM_WR_MEM_eventually_left_p);


property run_RESP_LAST_DATA_eventually_left_p;
  RESP_LAST_DATA
|->
  s_eventually(!RESP_LAST_DATA);
endproperty
run_RESP_LAST_DATA_eventually_left_a: assert property (disable iff(!rst_n) run_RESP_LAST_DATA_eventually_left_p);


property run_IDLE_BUFFER_EN_eventually_left_p;
  IDLE_BUFFER_EN
|->
  s_eventually(!IDLE_BUFFER_EN);
endproperty
run_IDLE_BUFFER_EN_eventually_left_a: assert property (disable iff(!rst_n) run_IDLE_BUFFER_EN_eventually_left_p);


parameter CONSISTENCY = 1;
if (CONSISTENCY) begin
// Check that no more than 1 state condition is met at the same time
  run_consistency_onehot0_state: assert property (disable iff(!rst_n) $onehot0({IDLE, IDLE_BUFFER_EN, RD_MEM_WR_MEM, REQ_1ST_DATA, REQ_2ND_DATA, REQ_3RD_DATA, RESP_LAST_DATA}) );
end


endmodule