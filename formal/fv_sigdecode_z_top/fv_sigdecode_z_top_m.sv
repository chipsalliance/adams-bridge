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
// | Created on 21.11.2024 at 16:31                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+

module fv_sigdecode_z_top_m
  import abr_params_pkg::*;
  import sigdecode_z_defines_pkg::*;
  import fv_sigdecode_z_top_pkg::*;
  import fv_sigdecode_z_top_functions::*;
(
  input logic rst,
  input logic clk,

  // Ports
  input logic start_port_vld,
  input logic start_port_rdy,
  input logic start_port,

  input st_BaseAddress base_address_port,

  input st_Request read_request_port,

  input a_unsigned_20_8 read_data_port,

  input st_Request write_request_port,

  input a_unsigned_24_8 write_data_port,

  input logic done_port,

  // Registers
  input st_BaseAddress base_address,
  input logic unsigned [8:0] operands,

  // States
  input logic IDLE,
  input logic READ_EXEC,
  input logic READ_EXEC_WRITE,
  input logic EXEC_WRITE,
  input logic WRITE,
  input logic DONE
);


default clocking default_clk @(posedge clk); endclocking


st_BaseAddress base_address_zero;
assign base_address_zero = '{
  source: 14'd0,
  destination: 14'd0
};

st_Request no_operation;
assign no_operation = '{
  addresses: '{ 0: 14'd0, 1: 14'd0 },
  idle: 1,
  read: 0,
  write: 0
};

a_unsigned_24_8 result_zero;
assign result_zero = '{
  0: 24'd0,
  1: 24'd0,
  2: 24'd0,
  3: 24'd0,
  4: 24'd0,
  5: 24'd0,
  6: 24'd0,
  7: 24'd0
};

a_unsigned_24_8 decode_0_i;
assign decode_0_i = decode(read_data_port);

st_Request read_request_1_i;
assign read_request_1_i = '{
  addresses: '{ 0: (14'd1 + base_address_port.source), 1: base_address_port.source },
  idle: 0,
  read: 1,
  write: 0
};

st_Request read_request_2_i;
assign read_request_2_i = '{
  addresses: '{ 0: ((14'd1 + base_address.source) + 14'(operands)), 1: (base_address.source + 14'(operands)) },
  idle: 0,
  read: 1,
  write: 0
};

st_Request write_request_0_i;
assign write_request_0_i = '{
  addresses: '{ 0: (64'd1 + ((({ 50'h0, base_address.destination} ) + 14'(operands)) - 64'd4)), 1: ((base_address.destination + 14'(operands)) - 14'd4) },
  idle: 0,
  read: 0,
  write: 1
};

st_Request write_request_1_i;
assign write_request_1_i = '{
  addresses: '{ 0: (14'd445 + base_address.destination), 1: (14'd444 + base_address.destination) },
  idle: 0,
  read: 0,
  write: 1
};

st_Request write_request_2_i;
assign write_request_2_i = '{
  addresses: '{ 0: (14'd447 + base_address.destination), 1: (14'd446 + base_address.destination) },
  idle: 0,
  read: 0,
  write: 1
};


sequence reset_sequence;
  rst ##1 !rst;
endsequence


property reset_p;
  reset_sequence |->
  IDLE &&
  base_address == base_address_zero &&
  done_port == 0 &&
  operands == 9'd0 &&
  read_request_port == no_operation &&
  write_data_port == result_zero &&
  write_request_port == no_operation;
endproperty
reset_a: assert property (reset_p);


property DONE_to_IDLE_p;
  DONE
|->
  ##1
  IDLE &&
  $stable(base_address) &&
  done_port == 1 &&
  operands == 9'd0 &&
  read_request_port == $past(no_operation, 1) &&
  write_data_port == $past(decode_0_i, 1) &&
  write_request_port == $past(no_operation, 1);
endproperty
DONE_to_IDLE_a: assert property (disable iff(rst) DONE_to_IDLE_p);


property EXEC_WRITE_to_WRITE_p;
  EXEC_WRITE
|->
  ##1 ($stable(done_port)) and
  ##1
  WRITE &&
  $stable(base_address) &&
  operands == 9'd0 &&
  read_request_port == $past(no_operation, 1) &&
  write_data_port == $past(decode_0_i, 1) &&
  write_request_port == $past(write_request_1_i, 1);
endproperty
EXEC_WRITE_to_WRITE_a: assert property (disable iff(rst) EXEC_WRITE_to_WRITE_p);


property IDLE_to_READ_EXEC_p;
  IDLE &&
  start_port_vld
|->
  ##1  done_port == 0 and
  ##1 ($stable(read_request_port)) and
  ##1  write_data_port == $past(decode_0_i, 1) and
  ##1 ($stable(write_request_port)) and
  ##2 ($stable(done_port)) and
  ##2
  READ_EXEC &&
  base_address == $past(base_address_port, 2) &&
  operands == (9'd2 + $past(operands, 2)) &&
  read_request_port == $past(read_request_1_i, 2) &&
  write_data_port == $past(decode_0_i, 1) &&
  write_request_port == $past(no_operation, 2);
endproperty
IDLE_to_READ_EXEC_a: assert property (disable iff(rst) IDLE_to_READ_EXEC_p);


property READ_EXEC_WRITE_to_EXEC_WRITE_p;
  READ_EXEC_WRITE &&
  (operands >= 9'd446)
|->
  ##1 ($stable(done_port)) and
  ##1
  EXEC_WRITE &&
  $stable(base_address) &&
  operands == (9'd2 + $past(operands, 1)) &&
  read_request_port == $past(read_request_2_i, 1) &&
  write_data_port == $past(decode_0_i, 1) &&
  write_request_port == $past(write_request_0_i, 1);
endproperty
READ_EXEC_WRITE_to_EXEC_WRITE_a: assert property (disable iff(rst) READ_EXEC_WRITE_to_EXEC_WRITE_p);


property READ_EXEC_WRITE_to_READ_EXEC_WRITE_p;
  READ_EXEC_WRITE &&
  (operands < 9'd446)
|->
  ##1 ($stable(done_port)) and
  ##1
  READ_EXEC_WRITE &&
  $stable(base_address) &&
  operands == (9'd2 + $past(operands, 1)) &&
  read_request_port == $past(read_request_2_i, 1) &&
  write_data_port == $past(decode_0_i, 1) &&
  write_request_port == $past(write_request_0_i, 1);
endproperty
READ_EXEC_WRITE_to_READ_EXEC_WRITE_a: assert property (disable iff(rst) READ_EXEC_WRITE_to_READ_EXEC_WRITE_p);


property READ_EXEC_to_READ_EXEC_WRITE_p;
  READ_EXEC
|->
  ##1 ($stable(done_port)) and
  ##1
  READ_EXEC_WRITE &&
  $stable(base_address) &&
  operands == (9'd2 + $past(operands, 1)) &&
  read_request_port == $past(read_request_2_i, 1) &&
  write_data_port == $past(decode_0_i, 1) &&
  write_request_port == $past(no_operation, 1);
endproperty
READ_EXEC_to_READ_EXEC_WRITE_a: assert property (disable iff(rst) READ_EXEC_to_READ_EXEC_WRITE_p);


property WRITE_to_DONE_p;
  WRITE
|->
  ##1 ($stable(done_port)) and
  ##1
  DONE &&
  $stable(base_address) &&
  $stable(operands) &&
  read_request_port == $past(no_operation, 1) &&
  write_data_port == $past(decode_0_i, 1) &&
  write_request_port == $past(write_request_2_i, 1);
endproperty
WRITE_to_DONE_a: assert property (disable iff(rst) WRITE_to_DONE_p);


property IDLE_wait_p;
  IDLE &&
  !start_port_vld
|->
  ##1 done_port == 0 and
  ##1 ($stable(read_request_port)) and
  ##1 write_data_port == $past(decode_0_i, 1) and
  ##1 ($stable(write_request_port)) and
  ##1
  IDLE &&
  $stable(base_address) &&
  $stable(operands);
endproperty
IDLE_wait_a: assert property (disable iff(rst) IDLE_wait_p);


property DONE_eventually_left_p;
  DONE
|->
  s_eventually(!DONE);
endproperty
DONE_eventually_left_a: assert property (disable iff(rst) DONE_eventually_left_p);


property EXEC_WRITE_eventually_left_p;
  EXEC_WRITE
|->
  s_eventually(!EXEC_WRITE);
endproperty
EXEC_WRITE_eventually_left_a: assert property (disable iff(rst) EXEC_WRITE_eventually_left_p);


property IDLE_eventually_left_p;
  IDLE &&
  start_port_vld
|->
  s_eventually(!IDLE);
endproperty
IDLE_eventually_left_a: assert property (disable iff(rst) IDLE_eventually_left_p);


property READ_EXEC_eventually_left_p;
  READ_EXEC
|->
  s_eventually(!READ_EXEC);
endproperty
READ_EXEC_eventually_left_a: assert property (disable iff(rst) READ_EXEC_eventually_left_p);


property READ_EXEC_WRITE_eventually_left_p;
  READ_EXEC_WRITE
|->
  s_eventually(!READ_EXEC_WRITE);
endproperty
READ_EXEC_WRITE_eventually_left_a: assert property (disable iff(rst) READ_EXEC_WRITE_eventually_left_p);


property WRITE_eventually_left_p;
  WRITE
|->
  s_eventually(!WRITE);
endproperty
WRITE_eventually_left_a: assert property (disable iff(rst) WRITE_eventually_left_p);

parameter CONSISTENCY = 1;
if (CONSISTENCY) begin
// Check that no more than 1 state condition is met at the same time
  consistency_onehot0_state: assert property ( $onehot0({DONE, EXEC_WRITE, IDLE, READ_EXEC, READ_EXEC_WRITE, WRITE}) );
end


endmodule
