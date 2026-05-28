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
// | Created on 02.05.2025 at 09:42                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


module fv_power2round_top_m
  import fv_power2round_top_pkg::*;
  import abr_params_pkg::*;
  import power2round_defines_pkg::*;
  import fv_power2round_top_functions::*;
(
  input logic rst,
  input logic clk,

  // Ports
  input logic start_port_vld,
  input logic start_port_rdy,
  input st_BaseAddress start_port,

  input logic rd_req_out_vld,
  input st_Request rd_req_out,

  input logic wr_req_out_vld,
  input st_Request wr_req_out,

  input logic pk_wr_req_out_vld,
  input st_PkRequest pk_wr_req_out,

  input logic unsigned [13:0] rd_cnt_new,

  input logic unsigned [13:0] wr_cnt_new,

  input logic unsigned [7:0] buffer_new,

  input a_unsigned_24_8 rd_data_port,

  input a_unsigned_32_2 wr_data_port,

  input a_unsigned_10_8 pk_wr_data_port,

  input logic done_port,

  input logic enable_port,

  input logic unsigned [13:0] current_rd_cnt,

  input logic unsigned [13:0] current_wr_cnt,

  input logic unsigned [7:0] current_buffer,

  // Registers
  input st_BaseAddress base_address,
  input logic unsigned [7:0] buffer,
  input logic unsigned [167:0] buffer_data,
  input logic enable,
  input a_unsigned_13_8 r0_packed,
  input a_unsigned_13_8 r0_packed_reg,
  input a_unsigned_10_8 r1,
  input a_unsigned_10_8 r1_reg,
  input logic unsigned [13:0] rd_cnt,
  input logic unsigned [13:0] wr_cnt,

  // States
  input logic IDLE,
  input logic REQ_1ST_DATA,
  input logic REQ_2ND_DATA,
  input logic REQ_3RD_DATA,
  input logic LOOP,
  input logic LAST_READ,
  input logic ONLY_WRITE1,
  input logic ONLY_WRITE2,
  input logic ONLY_WRITE3,
  input logic ONLY_WRITE4,
  input logic ONLY_WRITE5,
  input logic ONLY_WRITE6,
  input logic DONE
);


default clocking default_clk @(posedge clk); endclocking


a_unsigned_13_8 compute_r0_0_i;
assign compute_r0_0_i = compute_r0(rd_data_port);

a_unsigned_10_8 compute_r1_0_i;
assign compute_r1_0_i = compute_r1(rd_data_port);

a_unsigned_13_8 skencode_0_i;
assign skencode_0_i = skencode(compute_r0_0_i);

st_BaseAddress base_address_0_i;
assign base_address_0_i = '{
  source: 14'd0,
  destination: 14'd0
};

a_unsigned_10_8 pk_wr_data_port_0_i;
assign pk_wr_data_port_0_i = '{
  0: 10'd0,
  1: 10'd0,
  2: 10'd0,
  3: 10'd0,
  4: 10'd0,
  5: 10'd0,
  6: 10'd0,
  7: 10'd0
};

st_PkRequest pk_wr_req_0_i;
assign pk_wr_req_0_i = '{
  address: 8'd0,
  enable: 0
};

a_unsigned_13_8 r0_packed_reg_0_i;
assign r0_packed_reg_0_i = '{
  0: 13'd0,
  1: 13'd0,
  2: 13'd0,
  3: 13'd0,
  4: 13'd0,
  5: 13'd0,
  6: 13'd0,
  7: 13'd0
};

st_Request rd_req_0_i;
assign rd_req_0_i = '{
  addresses: '{ 0: 14'd1, 1: 14'd0 },
  idle: 1,
  read: 0,
  write: 0
};

a_unsigned_32_2 sk_data_output_0_i;
assign sk_data_output_0_i = '{
  0: 0,
  1: 0
};

st_Request rd_req_1_i;
assign rd_req_1_i = '{
  addresses: '{ 0: (14'd1 + start_port.source), 1: start_port.source },
  idle: 0,
  read: 1,
  write: 0
};

st_Request wr_req_0_i;
assign wr_req_0_i = '{
  addresses: '{ 0: (14'd1 + start_port.destination), 1: start_port.destination },
  idle: 1,
  read: 0,
  write: 0
};

st_Request rd_req_2_i;
assign rd_req_2_i = '{
  addresses: '{ 0: (14'd3 + base_address.source), 1: (14'd2 + base_address.source) },
  idle: 0,
  read: 1,
  write: 0
};

st_Request wr_req_1_i;
assign wr_req_1_i = '{
  addresses: '{ 0: (14'd1 + base_address.destination), 1: (base_address.destination + 14'd0) },
  idle: 1,
  read: 0,
  write: 0
};

st_Request rd_req_3_i;
assign rd_req_3_i = '{
  addresses: '{ 0: (14'd5 + base_address.source), 1: (14'd4 + base_address.source) },
  idle: 0,
  read: 1,
  write: 0
};

logic unsigned [167:0] compute_buffer_0_i;
assign compute_buffer_0_i = compute_buffer(r0_packed, buffer_data, 8'd0, 0);

st_PkRequest pk_wr_req_1_i;
assign pk_wr_req_1_i = '{
  address: 8'd0,
  enable: 1
};

st_Request rd_req_4_i;
assign rd_req_4_i = '{
  addresses: '{ 0: (14'd7 + base_address.source), 1: (14'd6 + base_address.source) },
  idle: 0,
  read: 1,
  write: 0
};

a_unsigned_32_2 get_sk_data_output_0_i;
assign get_sk_data_output_0_i = get_sk_data_output(buffer_data);

logic unsigned [167:0] compute_buffer_1_i;
assign compute_buffer_1_i = compute_buffer(r0_packed, buffer_data, current_buffer, 0);

st_PkRequest pk_wr_req_2_i;
assign pk_wr_req_2_i = '{
  address: ((current_rd_cnt - 64'd4) / 64'd2),
  enable: ((current_buffer < 64'd8) ? !(((64'd13 + current_buffer) > 64'd16) && ((64'd13 + current_buffer) < 64'd22)) : !(((64'd5 + current_buffer) > 64'd16) && ((64'd5 + current_buffer) < 64'd22)))
};

st_Request rd_req_5_i;
assign rd_req_5_i = '{
  addresses: '{ 0: ((14'd1 + base_address.source) + current_rd_cnt), 1: (base_address.source + current_rd_cnt) },
  idle: 0,
  read: 1,
  write: 0
};

st_Request wr_req_2_i;
assign wr_req_2_i = '{
  addresses: '{ 0: ((14'd3 + base_address.destination) + current_wr_cnt), 1: ((14'd2 + base_address.destination) + current_wr_cnt) },
  idle: 0,
  read: 0,
  write: 1
};

logic unsigned [167:0] compute_buffer_2_i;
assign compute_buffer_2_i = compute_buffer(r0_packed_reg, buffer_data, current_buffer, 1);

st_PkRequest pk_wr_req_3_i;
assign pk_wr_req_3_i = '{
  address: ((current_wr_cnt == 14'd818) ? ((current_rd_cnt - 64'd4) / 64'd2) : ((current_rd_cnt - 64'd6) / 64'd2)),
  enable: ((current_wr_cnt == 14'd0) ? !(((64'd13 + current_buffer) > 64'd16) && ((64'd13 + current_buffer) < 64'd22)) : !(((64'd5 + current_buffer) > 64'd16) && ((64'd5 + current_buffer) < 64'd22)))
};

st_Request rd_req_6_i;
assign rd_req_6_i = '{
  addresses: '{ 0: ((base_address.source + current_rd_cnt) + ((((64'd13 + current_buffer) > 64'd16) && ((64'd13 + current_buffer) < 64'd22)) ? 14'd1 : 14'd3)), 1: ((base_address.source + current_rd_cnt) + ((((64'd13 + current_buffer) > 64'd16) && ((64'd13 + current_buffer) < 64'd22)) ? 14'd0 : 14'd2)) },
  idle: 0,
  read: 1,
  write: 0
};

st_Request wr_req_3_i;
assign wr_req_3_i = '{
  addresses: '{ 0: ((base_address.destination + current_wr_cnt) + ((current_wr_cnt == 14'd0) ? 14'd1 : 14'd3)), 1: ((base_address.destination + current_wr_cnt) + ((current_wr_cnt == 14'd0) ? 14'd0 : 14'd2)) },
  idle: 0,
  read: 0,
  write: 1
};

logic unsigned [167:0] compute_buffer_3_i;
assign compute_buffer_3_i = compute_buffer(r0_packed, buffer_data, buffer, 0);

st_PkRequest pk_wr_req_4_i;
assign pk_wr_req_4_i = '{
  address: ((({ 50'h0, rd_cnt} ) - 64'd2) / 64'd2),
  enable: !(((64'd5 + ({ 56'h0, buffer} )) > 64'd16) && ((64'd5 + ({ 56'h0, buffer} )) < 64'd22))
};

st_Request rd_req_7_i;
assign rd_req_7_i = '{
  addresses: (((64'd5 + current_buffer) > 64'd16) && ((64'd5 + current_buffer) < 64'd22)) ? '{ 0: ((14'd1 + base_address.source) + rd_cnt), 1: (base_address.source + rd_cnt) } : '{ 0: (14'd1 + base_address.source), 1: (base_address.source + 14'd0) },
  idle: 1,
  read: 0,
  write: 0
};

st_Request wr_req_4_i;
assign wr_req_4_i = '{
  addresses: '{ 0: ((14'd3 + base_address.destination) + wr_cnt), 1: ((14'd2 + base_address.destination) + wr_cnt) },
  idle: 0,
  read: 0,
  write: 1
};

logic unsigned [167:0] compute_buffer_4_i;
assign compute_buffer_4_i = compute_buffer(r0_packed, buffer_data, buffer, 1);

st_PkRequest pk_wr_req_5_i;
assign pk_wr_req_5_i = '{
  address: (((64'd5 + current_buffer) > 64'd16) && ((64'd5 + current_buffer) < 64'd22)) ? ({ 50'h0, rd_cnt} / 64'd2) : ((({ 50'h0, rd_cnt} ) - 64'd2) / 64'd2),
  enable: ((current_buffer < 64'd8) ? !(((64'd13 + current_buffer) > 64'd16) && ((64'd13 + current_buffer) < 64'd22)) : !(((64'd5 + current_buffer) > 64'd16) && ((64'd5 + current_buffer) < 64'd22)))
};

st_PkRequest pk_wr_req_6_i;
assign pk_wr_req_6_i = '{
  address: 8'd255,
  enable: 1
};

st_PkRequest pk_wr_req_7_i;
assign pk_wr_req_7_i = '{
  address: 8'd255,
  enable: 0
};

st_Request rd_req_8_i;
assign rd_req_8_i = '{
  addresses: '{ 0: (14'd1 + base_address.source), 1: (base_address.source + 14'd0) },
  idle: 1,
  read: 0,
  write: 0
};

st_Request wr_req_5_i;
assign wr_req_5_i = '{
  addresses: '{ 0: ((14'd1 + base_address.destination) + wr_cnt), 1: (base_address.destination + wr_cnt) },
  idle: 1,
  read: 0,
  write: 0
};

st_Request rd_req_9_i;
assign rd_req_9_i = '{
  addresses: '{ 0: (14'd1 + base_address.source), 1: (base_address.source + 14'd0) },
  idle: 0,
  read: 1,
  write: 0
};

st_Request rd_req_10_i;
assign rd_req_10_i = '{
  addresses: '{ 0: ((14'd1 + base_address.source) + rd_cnt), 1: (base_address.source + rd_cnt) },
  idle: 1,
  read: 0,
  write: 0
};


sequence reset_sequence;
  rst ##1 !rst;
endsequence


property run_reset_p;
  reset_sequence |->
  IDLE &&
  done_port == 0 &&
  pk_wr_data_port == pk_wr_data_port_0_i &&
  pk_wr_req_out == pk_wr_req_0_i &&
  r0_packed_reg == r0_packed_reg_0_i &&
  r1_reg == pk_wr_data_port_0_i &&
  rd_cnt == (14'd0-base_address.source) &&
  rd_req_out == rd_req_0_i &&
  wr_cnt == 14'd0 &&
  wr_data_port == sk_data_output_0_i &&
  wr_req_out == rd_req_0_i;
endproperty
run_reset_a: assert property (run_reset_p);


property run_DONE_to_IDLE_p;
  DONE &&
  !enable
|->
  ##1 ($stable(wr_data_port)) and
  ##1
  IDLE &&
  done_port == 0 &&
  pk_wr_data_port == $past(r1, 1) &&
  r0_packed_reg == $past(skencode_0_i, 1) &&
  r1_reg == $past(compute_r1_0_i, 1) &&
  $stable(rd_cnt) &&
  wr_cnt == 14'd0;
endproperty
run_DONE_to_IDLE_a: assert property (disable iff(rst) run_DONE_to_IDLE_p);


property run_DONE_to_REQ_1ST_DATA_p;
  DONE &&
  enable
|->
  ##1 ($stable(wr_data_port)) and
  ##1
  REQ_1ST_DATA &&
  done_port == 0 &&
  pk_wr_data_port == $past(r1, 1) &&
  pk_wr_req_out == pk_wr_req_0_i &&
  r0_packed_reg == $past(skencode_0_i, 1) &&
  r1_reg == $past(compute_r1_0_i, 1) &&
  $stable(rd_cnt) &&
  rd_req_out == $past(rd_req_9_i, 1) &&
  wr_cnt == 14'd0 &&
  wr_req_out == $past(wr_req_1_i, 1);
endproperty
run_DONE_to_REQ_1ST_DATA_a: assert property (disable iff(rst) run_DONE_to_REQ_1ST_DATA_p);


property run_IDLE_to_REQ_1ST_DATA_p;
  IDLE &&
  start_port_vld
|->
  ##1 ($stable(done_port)) and
  ##1 ($stable(wr_data_port)) and
  ##1
  REQ_1ST_DATA &&
  pk_wr_data_port == $past(r1, 1) &&
  pk_wr_req_out == pk_wr_req_0_i &&
  r0_packed_reg == $past(skencode_0_i, 1) &&
  r1_reg == $past(compute_r1_0_i, 1) &&
  rd_cnt == 14'd0 &&
  rd_req_out == $past(rd_req_1_i, 1) &&
  $stable(wr_cnt) &&
  wr_req_out == $past(wr_req_0_i, 1);
endproperty
run_IDLE_to_REQ_1ST_DATA_a: assert property (disable iff(rst) run_IDLE_to_REQ_1ST_DATA_p);


property run_LAST_READ_to_ONLY_WRITE1_p;
  LAST_READ
|->
  ##1 ($stable(done_port)) and
  ##1
  ONLY_WRITE1 &&
  pk_wr_data_port == $past(r1, 1) &&
  pk_wr_req_out == $past(pk_wr_req_4_i, 1) &&
  r0_packed_reg == $past(skencode_0_i, 1) &&
  r1_reg == $past(compute_r1_0_i, 1) &&
  $stable(rd_cnt) &&
  wr_cnt == $past(current_wr_cnt, 1) + 14'd2 &&
  rd_req_out == $past(rd_req_10_i, 1) &&
  wr_data_port == $past(get_sk_data_output_0_i, 1) &&
  wr_req_out == $past(wr_req_4_i, 1);
endproperty
run_LAST_READ_to_ONLY_WRITE1_a: assert property (disable iff(rst) run_LAST_READ_to_ONLY_WRITE1_p);


property run_LOOP_to_LAST_READ_p;
  LOOP &&
  ((64'd5 + current_buffer) > 64'd16) &&
  ((64'd5 + current_buffer) < 64'd22) &&
  (current_wr_cnt >= 64'd818)
|->
  ##1 ($stable(done_port)) and
  ##1
  LAST_READ &&
  pk_wr_data_port == $past(r1, 1) &&
  pk_wr_req_out == $past(pk_wr_req_2_i, 1) &&
  r0_packed_reg == $past(skencode_0_i, 1) &&
  r1_reg == $past(compute_r1_0_i, 1) &&
  rd_cnt == $past(current_rd_cnt, 1) &&
  rd_req_out == $past(rd_req_5_i, 1) &&
  wr_cnt == $past(current_wr_cnt, 1) &&
  wr_data_port == $past(get_sk_data_output_0_i, 1) &&
  wr_req_out == $past(wr_req_2_i, 1);
endproperty
run_LOOP_to_LAST_READ_a: assert property (disable iff(rst) run_LOOP_to_LAST_READ_p);


property run_LOOP_to_LAST_READ_1_p;
  LOOP &&
  !(((64'd5 + current_buffer) > 64'd16) && ((64'd5 + current_buffer) < 64'd22)) &&
  ((64'd5 + current_buffer) >= 64'd22) &&
  (current_wr_cnt >= 64'd818)
|->
  ##1 ($stable(done_port)) and
  ##1
  LAST_READ &&
  pk_wr_data_port == $past(r1_reg, 1) &&
  pk_wr_req_out == $past(pk_wr_req_3_i, 1) &&
  $stable(r0_packed_reg) &&
  $stable(r1_reg) &&
  rd_cnt == $past(current_rd_cnt, 1) &&
  rd_req_out == $past(rd_req_5_i, 1) &&
  wr_cnt == $past(current_wr_cnt, 1) + 14'd2 &&
  wr_data_port == $past(get_sk_data_output_0_i, 1) &&
  wr_req_out == $past(wr_req_2_i, 1);
endproperty
run_LOOP_to_LAST_READ_1_a: assert property (disable iff(rst) run_LOOP_to_LAST_READ_1_p);


property run_LOOP_to_LAST_READ_2_p;
  LOOP &&
  !(((64'd5 + current_buffer) > 64'd16) && ((64'd5 + current_buffer) < 64'd22)) &&
  ((64'd5 + current_buffer) < 64'd22) &&
  (current_wr_cnt >= 64'd818)
|->
  ##1 ($stable(done_port)) and
  ##1
  LAST_READ &&
  pk_wr_data_port == $past(r1, 1) &&
  pk_wr_req_out == $past(pk_wr_req_2_i, 1) &&
  r0_packed_reg == $past(skencode_0_i, 1) &&
  r1_reg == $past(compute_r1_0_i, 1) &&
  rd_cnt == $past(current_rd_cnt, 1) &&
  rd_req_out == $past(rd_req_6_i, 1) &&
  wr_cnt == $past(current_wr_cnt, 1) &&
  wr_data_port == $past(get_sk_data_output_0_i, 1) &&
  wr_req_out == $past(wr_req_3_i, 1);
endproperty
run_LOOP_to_LAST_READ_2_a: assert property (disable iff(rst) run_LOOP_to_LAST_READ_2_p);


property run_LOOP_to_LOOP_p;
  LOOP &&
  ((64'd5 + current_buffer) > 64'd16) &&
  ((64'd5 + current_buffer) < 64'd22) &&
  (current_wr_cnt < 64'd818)
|->
  ##1 ($stable(done_port)) and
  ##1
  LOOP &&
  pk_wr_data_port == $past(r1, 1) &&
  pk_wr_req_out == $past(pk_wr_req_2_i, 1) &&
  r0_packed_reg == $past(skencode_0_i, 1) &&
  r1_reg == $past(compute_r1_0_i, 1) &&
  rd_cnt == current_rd_cnt==14'd510 ? 14'd510 : $past(current_rd_cnt, 1) + 14'd2 &&
  rd_req_out == $past(rd_req_5_i, 1) &&
  wr_cnt == $past(current_wr_cnt, 1) + 14'd2 &&
  wr_data_port == $past(get_sk_data_output_0_i, 1) &&
  wr_req_out == $past(wr_req_2_i, 1);
endproperty
run_LOOP_to_LOOP_a: assert property (disable iff(rst) run_LOOP_to_LOOP_p);


property run_LOOP_to_LOOP_1_p;
  LOOP &&
  !(((64'd5 + current_buffer) > 64'd16) && ((64'd5 + current_buffer) < 64'd22)) &&
  ((64'd5 + current_buffer) >= 64'd22) &&
  (current_wr_cnt < 64'd818)
|->
  ##1 ($stable(done_port)) and
  ##1
  LOOP &&
  pk_wr_data_port == $past(r1_reg, 1) &&
  pk_wr_req_out == $past(pk_wr_req_3_i, 1) &&
  $stable(r0_packed_reg) &&
  $stable(r1_reg) &&
  rd_cnt == $past(current_rd_cnt, 1) &&
  rd_req_out == $past(rd_req_5_i, 1) &&
  wr_cnt == $past(current_wr_cnt, 1) + 14'd2 &&
  wr_data_port == $past(get_sk_data_output_0_i, 1) &&
  wr_req_out == $past(wr_req_2_i, 1);
endproperty
run_LOOP_to_LOOP_1_a: assert property (disable iff(rst) run_LOOP_to_LOOP_1_p);


property run_LOOP_to_LOOP_2_p;
  LOOP &&
  !(((64'd5 + current_buffer) > 64'd16) && ((64'd5 + current_buffer) < 64'd22)) &&
  ((64'd5 + current_buffer) < 64'd22) &&
  (current_wr_cnt < 64'd818)
|->
  ##1 ($stable(done_port)) and
  ##1
  LOOP &&
  pk_wr_data_port == $past(r1, 1) &&
  pk_wr_req_out == $past(pk_wr_req_2_i, 1) &&
  r0_packed_reg == $past(skencode_0_i, 1) &&
  r1_reg == $past(compute_r1_0_i, 1) &&
  rd_cnt == $past(current_rd_cnt, 1) + 14'd2 &&
  rd_req_out == $past(rd_req_6_i, 1) &&
  wr_cnt == $past(current_wr_cnt, 1) + ($past(rd_cnt, 1) == 14'd6 ? 14'd0 : 14'd2) &&
  wr_data_port == $past(get_sk_data_output_0_i, 1) &&
  wr_req_out == $past(wr_req_3_i, 1);
endproperty
run_LOOP_to_LOOP_2_a: assert property (disable iff(rst) run_LOOP_to_LOOP_2_p);


property run_ONLY_WRITE1_to_ONLY_WRITE2_p;
  ONLY_WRITE1
|->
  ##1 ($stable(done_port)) and
  ##1
  ONLY_WRITE2 &&
  pk_wr_data_port == (((64'd5 + current_buffer) >= 64'd22) ? $past(compute_r1_0_i, 1) : $past(r1_reg, 1)) &&
  pk_wr_req_out == $past(pk_wr_req_5_i, 1) &&
  r0_packed_reg == (((64'd5 + current_buffer) >= 64'd22) ? $past(skencode_0_i, 1) : $past(r0_packed_reg, 1)) &&
  r1_reg == (((64'd5 + current_buffer) >= 64'd22) ? $past(compute_r1_0_i, 1) : $past(r1_reg, 1)) &&
  rd_cnt == 14'd0 &&
  rd_req_out == $past(rd_req_7_i, 1) &&
  wr_cnt == $past(current_wr_cnt, 1) + 14'd2 &&
  wr_data_port == $past(get_sk_data_output_0_i, 1) &&
  wr_req_out == $past(wr_req_4_i, 1);
endproperty
run_ONLY_WRITE1_to_ONLY_WRITE2_a: assert property (disable iff(rst) run_ONLY_WRITE1_to_ONLY_WRITE2_p);


property run_ONLY_WRITE2_to_ONLY_WRITE3_p;
  ONLY_WRITE2
|->
  ##1 ($stable(done_port)) and
  ##1
  ONLY_WRITE3 &&
  pk_wr_data_port == (((64'd5 + $past(current_buffer, 1)) >= 64'd22) ? $past(r1_reg, 1) : $past(compute_r1_0_i, 1)) &&
  pk_wr_req_out == pk_wr_req_6_i &&
  r0_packed_reg == (((64'd5 + $past(current_buffer, 1)) >= 64'd22) ? $past(r0_packed_reg, 1) : $past(skencode_0_i, 1)) &&
  r1_reg == (((64'd5 + $past(current_buffer, 1)) >= 64'd22) ? $past(r1_reg, 1) : $past(compute_r1_0_i, 1)) &&
  $stable(rd_cnt) &&
  rd_req_out == $past(rd_req_7_i, 1) &&
  wr_cnt == $past(current_wr_cnt, 1) + 14'd2 &&
  wr_data_port == $past(get_sk_data_output_0_i, 1) &&
  wr_req_out == $past(wr_req_4_i, 1);
endproperty
run_ONLY_WRITE2_to_ONLY_WRITE3_a: assert property (disable iff(rst) run_ONLY_WRITE2_to_ONLY_WRITE3_p);


property run_ONLY_WRITE3_to_ONLY_WRITE4_p;
  ONLY_WRITE3
|->
  ##1 ($stable(done_port)) and
  ##1
  ONLY_WRITE4 &&
  pk_wr_data_port == $past(r1, 1) &&
  pk_wr_req_out == pk_wr_req_7_i &&
  r0_packed_reg == $past(skencode_0_i, 1) &&
  r1_reg == $past(compute_r1_0_i, 1) &&
  $stable(rd_cnt) &&
  rd_req_out == $past(rd_req_8_i, 1) &&
  wr_cnt == $past(current_wr_cnt, 1) + 14'd2 &&
  wr_data_port == $past(get_sk_data_output_0_i, 1) &&
  wr_req_out == $past(wr_req_4_i, 1);
endproperty
run_ONLY_WRITE3_to_ONLY_WRITE4_a: assert property (disable iff(rst) run_ONLY_WRITE3_to_ONLY_WRITE4_p);


property run_ONLY_WRITE4_to_ONLY_WRITE5_p;
  ONLY_WRITE4
|->
  ##1 ($stable(done_port)) and
  ##1
  ONLY_WRITE5 &&
  pk_wr_data_port == (((64'd5 + current_buffer) >= 64'd22) ? $past(compute_r1_0_i, 1) : $past(r1_reg, 1)) &&
  pk_wr_req_out == pk_wr_req_7_i &&
  r0_packed_reg == (((64'd5 + current_buffer) >= 64'd22) ? $past(skencode_0_i, 1) : $past(r0_packed_reg, 1)) &&
  r1_reg == (((64'd5 + current_buffer) >= 64'd22) ? $past(compute_r1_0_i, 1) : $past(r1_reg, 1)) &&
  $stable(rd_cnt) &&
  rd_req_out == $past(rd_req_8_i, 1) &&
  wr_cnt == $past(current_wr_cnt, 1) + 14'd2 &&
  wr_data_port == $past(get_sk_data_output_0_i, 1) &&
  wr_req_out == $past(wr_req_4_i, 1);
endproperty
run_ONLY_WRITE4_to_ONLY_WRITE5_a: assert property (disable iff(rst) run_ONLY_WRITE4_to_ONLY_WRITE5_p);


property run_ONLY_WRITE5_to_ONLY_WRITE6_p;
  ONLY_WRITE5
|->
  ##1 ($stable(done_port)) and
  ##1
  ONLY_WRITE6 &&
  pk_wr_req_out.enable == pk_wr_req_0_i.enable &&
  r0_packed_reg == ((((64'd5 + current_buffer) > 64'd16) && ((64'd5 + current_buffer) < 64'd22)) ? $past(r0_packed_reg, 1) : $past(skencode_0_i, 1)) &&
  $stable(rd_cnt) &&
  rd_req_out == $past(rd_req_8_i, 1) &&
  $stable(wr_cnt) &&
  wr_data_port == $past(get_sk_data_output_0_i, 1) &&
  wr_req_out == $past(wr_req_5_i, 1);
endproperty
run_ONLY_WRITE5_to_ONLY_WRITE6_a: assert property (disable iff(rst) run_ONLY_WRITE5_to_ONLY_WRITE6_p);


property run_ONLY_WRITE6_to_DONE_p;
  ONLY_WRITE6
|->
  ##1
  DONE &&
  done_port == 1 &&
  pk_wr_req_out.enable == pk_wr_req_0_i.enable &&
  r0_packed_reg == $past(skencode_0_i, 1) &&
  r1_reg == $past(compute_r1_0_i, 1) &&
  $stable(rd_cnt) &&
  rd_req_out == $past(rd_req_8_i, 1) &&
  $stable(wr_cnt) &&
  wr_data_port == $past(get_sk_data_output_0_i, 1) &&
  wr_req_out == $past(wr_req_5_i, 1);
endproperty
run_ONLY_WRITE6_to_DONE_a: assert property (disable iff(rst) run_ONLY_WRITE6_to_DONE_p);


property run_REQ_1ST_DATA_to_REQ_2ND_DATA_p;
  REQ_1ST_DATA
|->
  ##1 ($stable(done_port)) and
  ##1 ($stable(wr_data_port)) and
  ##1
  REQ_2ND_DATA &&
  pk_wr_data_port == $past(r1, 1) &&
  pk_wr_req_out == pk_wr_req_0_i &&
  r0_packed_reg == $past(skencode_0_i, 1) &&
  r1_reg == $past(compute_r1_0_i, 1) &&
  rd_cnt == $past(rd_cnt, 1) + 14'd2 &&
  rd_req_out == $past(rd_req_2_i, 1) &&
  $stable(wr_cnt) &&
  wr_req_out == $past(wr_req_1_i, 1);
endproperty
run_REQ_1ST_DATA_to_REQ_2ND_DATA_a: assert property (disable iff(rst) run_REQ_1ST_DATA_to_REQ_2ND_DATA_p);


property run_REQ_2ND_DATA_to_REQ_3RD_DATA_p;
  REQ_2ND_DATA
|->
  ##1 ($stable(done_port)) and
  ##1 ($stable(wr_data_port)) and
  ##1
  REQ_3RD_DATA &&
  pk_wr_data_port == $past(r1, 1) &&
  pk_wr_req_out == pk_wr_req_0_i &&
  r0_packed_reg == $past(skencode_0_i, 1) &&
  r1_reg == $past(compute_r1_0_i, 1) &&
  rd_cnt == $past(rd_cnt, 1) + 14'd2 &&
  rd_req_out == $past(rd_req_3_i, 1) &&
  $stable(wr_cnt) &&
  wr_req_out == $past(wr_req_1_i, 1);
endproperty
run_REQ_2ND_DATA_to_REQ_3RD_DATA_a: assert property (disable iff(rst) run_REQ_2ND_DATA_to_REQ_3RD_DATA_p);


property run_REQ_3RD_DATA_to_LOOP_p;
  REQ_3RD_DATA
|->
  ##1 ($stable(done_port)) and
  ##1 ($stable(wr_data_port)) and
  ##1
  LOOP &&
  pk_wr_data_port == $past(r1, 1) &&
  pk_wr_req_out == pk_wr_req_1_i &&
  r0_packed_reg == $past(skencode_0_i, 1) &&
  r1_reg == $past(compute_r1_0_i, 1) &&
  rd_cnt == $past(rd_cnt, 1) + 14'd2 &&
  rd_req_out == $past(rd_req_4_i, 1) &&
  $stable(wr_cnt) &&
  wr_req_out == $past(wr_req_1_i, 1);
endproperty
run_REQ_3RD_DATA_to_LOOP_a: assert property (disable iff(rst) run_REQ_3RD_DATA_to_LOOP_p);


property run_IDLE_wait_p;
  IDLE &&
  !start_port_vld
|->
  ##1 ($stable(done_port)) and
  ##1 ($stable(wr_data_port)) and
  ##1
  IDLE &&
  pk_wr_data_port == $past(r1, 1) &&
  r0_packed_reg == $past(skencode_0_i, 1) &&
  r1_reg == $past(compute_r1_0_i, 1) &&
  rd_cnt == 14'd0 &&
  $stable(wr_cnt);
endproperty
run_IDLE_wait_a: assert property (disable iff(rst) run_IDLE_wait_p);


property run_IDLE_eventually_left_p;
  IDLE &&
  enable_port
|->
  s_eventually(!IDLE);
endproperty
run_IDLE_eventually_left_a: assert property (disable iff(rst) run_IDLE_eventually_left_p);


property run_REQ_1ST_DATA_eventually_left_p;
  REQ_1ST_DATA
|->
  s_eventually(!REQ_1ST_DATA);
endproperty
run_REQ_1ST_DATA_eventually_left_a: assert property (disable iff(rst) run_REQ_1ST_DATA_eventually_left_p);


property run_REQ_2ND_DATA_eventually_left_p;
  REQ_2ND_DATA
|->
  s_eventually(!REQ_2ND_DATA);
endproperty
run_REQ_2ND_DATA_eventually_left_a: assert property (disable iff(rst) run_REQ_2ND_DATA_eventually_left_p);


property run_REQ_3RD_DATA_eventually_left_p;
  REQ_3RD_DATA
|->
  s_eventually(!REQ_3RD_DATA);
endproperty
run_REQ_3RD_DATA_eventually_left_a: assert property (disable iff(rst) run_REQ_3RD_DATA_eventually_left_p);


property run_LOOP_eventually_left_p;
  LOOP
|->
  s_eventually(!LOOP);
endproperty
run_LOOP_eventually_left_a: assert property (disable iff(rst) run_LOOP_eventually_left_p);


property run_LAST_READ_eventually_left_p;
  LAST_READ
|->
  s_eventually(!LAST_READ);
endproperty
run_LAST_READ_eventually_left_a: assert property (disable iff(rst) run_LAST_READ_eventually_left_p);


property run_ONLY_WRITE1_eventually_left_p;
  ONLY_WRITE1
|->
  s_eventually(!ONLY_WRITE1);
endproperty
run_ONLY_WRITE1_eventually_left_a: assert property (disable iff(rst) run_ONLY_WRITE1_eventually_left_p);


property run_ONLY_WRITE2_eventually_left_p;
  ONLY_WRITE2
|->
  s_eventually(!ONLY_WRITE2);
endproperty
run_ONLY_WRITE2_eventually_left_a: assert property (disable iff(rst) run_ONLY_WRITE2_eventually_left_p);


property run_ONLY_WRITE3_eventually_left_p;
  ONLY_WRITE3
|->
  s_eventually(!ONLY_WRITE3);
endproperty
run_ONLY_WRITE3_eventually_left_a: assert property (disable iff(rst) run_ONLY_WRITE3_eventually_left_p);


property run_ONLY_WRITE4_eventually_left_p;
  ONLY_WRITE4
|->
  s_eventually(!ONLY_WRITE4);
endproperty
run_ONLY_WRITE4_eventually_left_a: assert property (disable iff(rst) run_ONLY_WRITE4_eventually_left_p);


property run_ONLY_WRITE5_eventually_left_p;
  ONLY_WRITE5
|->
  s_eventually(!ONLY_WRITE5);
endproperty
run_ONLY_WRITE5_eventually_left_a: assert property (disable iff(rst) run_ONLY_WRITE5_eventually_left_p);


property run_ONLY_WRITE6_eventually_left_p;
  ONLY_WRITE6
|->
  s_eventually(!ONLY_WRITE6);
endproperty
run_ONLY_WRITE6_eventually_left_a: assert property (disable iff(rst) run_ONLY_WRITE6_eventually_left_p);


property run_DONE_eventually_left_p;
  DONE
|->
  s_eventually(!DONE);
endproperty
run_DONE_eventually_left_a: assert property (disable iff(rst) run_DONE_eventually_left_p);


parameter CONSISTENCY = 1;
if (CONSISTENCY) begin
  // Check that no more than 1 state condition is met at the same time
  run_consistency_onehot0_state: assert property($onehot0({ DONE, IDLE, LAST_READ, LOOP, ONLY_WRITE1, ONLY_WRITE2, ONLY_WRITE3, ONLY_WRITE4, ONLY_WRITE5, ONLY_WRITE6, REQ_1ST_DATA, REQ_2ND_DATA, REQ_3RD_DATA }));
end


endmodule
