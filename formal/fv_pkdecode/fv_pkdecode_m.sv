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
// | Created on 07.01.2025 at 18:20                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import fv_pkdecode_pkg::*;
import abr_params_pkg::*;
import fv_pkdecode_functions::*;


module fv_pkdecode_m(
  input logic rst,
  input logic clk,

  // Ports
  input logic start_port_vld,
  input logic start_port_rdy,
  input logic start_port,

  input st_BaseAddress base_address_port,

  input logic unsigned [15:0] read_address_port,

  input logic unsigned [79:0] read_data_port,

  input st_Request write_request_port,

  input a_unsigned_24_8 write_data_port,

  input logic done_port,

  // Registers
  input logic unsigned [31:0] api_operands,
  input st_BaseAddress base_address,
  input logic unsigned [31:0] mem_operands,

  // States
  input logic IDLE,
  input logic READ,
  input logic READ_EXEC,
  input logic READ_WRITE,
  input logic WRITE,
  input logic DONE
);


default clocking default_clk @(posedge clk); endclocking

a_unsigned_24_8 write_data_port_on_reset;
assign write_data_port_on_reset = '{
  0: 24'd0,
  1: 24'd0,
  2: 24'd0,
  3: 24'd0,
  4: 24'd0,
  5: 24'd0,
  6: 24'd0,
  7: 24'd0
};

st_Request idle_write_request;
assign idle_write_request = '{
  addresses: '{ 0: 14'd0, 1: 14'd0 },
  idle: 1,
  read: 0,
  write: 0
};

a_unsigned_24_8 encoded_coeffs_0_i;
assign encoded_coeffs_0_i = encoded_coeffs(read_data_port);

st_Request write_request_1_i;
assign write_request_1_i = '{
  addresses: '{ 0: (({ 50'h0, base_address.destination} ) + 14'((64'd1 + ({ 'h0, mem_operands} )))), 1: (({ 18'h0, base_address.destination} ) + 14'(mem_operands)) },
  idle: 0,
  read: 0,
  write: 1
};


sequence reset_sequence;
  rst ##1 !rst;
endsequence

till_done: cover property (pkdecode.pkdecode_enable ##1 pkdecode.pkdecode_done [->1]);

property run_reset_p;
  reset_sequence |->
  IDLE &&
  api_operands == 0 &&
  done_port == 0 &&
  base_address == '0 &&
  mem_operands == 0 &&
  read_address_port == 16'd0 &&
  write_data_port == write_data_port_on_reset &&
  write_request_port == idle_write_request;
endproperty
run_reset_a: assert property (run_reset_p);


property run_DONE_to_IDLE_p;
  DONE
|->
  ##1
  IDLE &&
  api_operands == 0 &&
  done_port == 1 &&
  $stable(base_address) &&
  mem_operands == 0 &&
  read_address_port == 16'd0 &&
  write_data_port == $past(encoded_coeffs_0_i, 1) &&
  write_request_port == idle_write_request;
endproperty
run_DONE_to_IDLE_a: assert property (disable iff(rst) run_DONE_to_IDLE_p);


property run_IDLE_to_READ_p;
  IDLE &&
  start_port_vld
|->
  ##1
  READ &&
  $stable(api_operands) &&
  done_port == 0 &&
  base_address == $past(base_address_port, 1) &&
  $stable(mem_operands) &&
  read_address_port == '0 &&
  write_data_port == $past(encoded_coeffs_0_i, 1) &&
  write_request_port == idle_write_request;
endproperty
run_IDLE_to_READ_a: assert property (disable iff(rst) run_IDLE_to_READ_p);


property run_READ_EXEC_to_READ_WRITE_p;
  READ_EXEC
|->
  ##1 ($stable(done_port)) and
  ##1
  READ_WRITE &&
  api_operands == (1 + $past(api_operands, 1)) &&
  $stable(mem_operands) &&
  $stable(base_address) &&
  read_address_port == 16'((({ 16'h0, $past(base_address.source, 1)} ) + 14'($past(api_operands, 1)))) &&
  write_data_port == $past(encoded_coeffs_0_i, 1) &&
  write_request_port == idle_write_request;
endproperty
run_READ_EXEC_to_READ_WRITE_a: assert property (disable iff(rst) run_READ_EXEC_to_READ_WRITE_p);


property run_READ_WRITE_to_READ_WRITE_p;
  READ_WRITE &&
  (api_operands < 256) // Change to parameter.
|->
  ##1 ($stable(done_port)) and
  ##1
  READ_WRITE &&
  api_operands == (1 + $past(api_operands, 1)) &&
  mem_operands == (2 + $past(mem_operands, 1)) &&
  $stable(base_address) &&
  read_address_port == 16'((({ 16'h0, $past(base_address.source, 1)} ) + 14'($past(api_operands, 1)))) &&
  write_data_port == $past(encoded_coeffs_0_i, 1) &&
  write_request_port == $past(write_request_1_i, 1);
endproperty
run_READ_WRITE_to_READ_WRITE_a: assert property (disable iff(rst) run_READ_WRITE_to_READ_WRITE_p);


property run_READ_WRITE_to_WRITE_p;
  READ_WRITE &&
  (api_operands >= 256)
|->
  ##1 ($stable(done_port)) and
  ##1
  WRITE &&
  api_operands == (1 + $past(api_operands, 1)) &&
  mem_operands == (2 + $past(mem_operands, 1)) &&
  $stable(base_address) &&
  read_address_port == 16'((({ 16'h0, $past(base_address.source, 1)} ) + 14'($past(api_operands, 1)))) &&
  write_data_port == $past(encoded_coeffs_0_i, 1) &&
  write_request_port == $past(write_request_1_i, 1);
endproperty
run_READ_WRITE_to_WRITE_a: assert property (disable iff(rst) run_READ_WRITE_to_WRITE_p);


property run_READ_to_READ_EXEC_p;
  READ
|->
  ##1 ($stable(done_port)) and
  ##1
  READ_EXEC &&
  api_operands == (1 + $past(api_operands, 1)) &&
  $stable(mem_operands) &&
  $stable(base_address) &&
  read_address_port == 16'((({ 16'h0, $past(base_address.source, 1)} ) + 14'($past(api_operands, 1)))) &&
  write_data_port == $past(encoded_coeffs_0_i, 1) &&
  write_request_port == idle_write_request;
endproperty
run_READ_to_READ_EXEC_a: assert property (disable iff(rst) run_READ_to_READ_EXEC_p);


property run_WRITE_to_DONE_p;
  WRITE
|->
  ##1 ($stable(done_port)) and
  ##1
  DONE &&
  api_operands == 0 &&
  mem_operands == (2 + $past(mem_operands, 1)) &&
  $stable(base_address) &&
  read_address_port == 16'd0 &&
  write_data_port == $past(encoded_coeffs_0_i, 1) &&
  write_request_port == $past(write_request_1_i, 1);
endproperty
run_WRITE_to_DONE_a: assert property (disable iff(rst) run_WRITE_to_DONE_p);


property run_IDLE_wait_p;
  IDLE &&
  !start_port_vld
|->
  ##1 ($stable(read_address_port)) and
  ##1  $stable(base_address) and
  ##1 ($stable(write_request_port)) and
  ##1
  IDLE &&
  done_port == 0 &&
  $stable(api_operands) &&
  $stable(mem_operands);
endproperty
run_IDLE_wait_a: assert property (disable iff(rst) run_IDLE_wait_p);


property run_IDLE_eventually_left_p;
  IDLE &&
  start_port_vld
|->
  s_eventually(!IDLE);
endproperty
run_IDLE_eventually_left_a: assert property (disable iff(rst) run_IDLE_eventually_left_p);


property run_READ_eventually_left_p;
  READ
|->
  s_eventually(!READ);
endproperty
run_READ_eventually_left_a: assert property (disable iff(rst) run_READ_eventually_left_p);


property run_READ_EXEC_eventually_left_p;
  READ_EXEC
|->
  s_eventually(!READ_EXEC);
endproperty
run_READ_EXEC_eventually_left_a: assert property (disable iff(rst) run_READ_EXEC_eventually_left_p);


property run_READ_WRITE_eventually_left_p;
  READ_WRITE
|->
  s_eventually(!READ_WRITE);
endproperty
run_READ_WRITE_eventually_left_a: assert property (disable iff(rst) run_READ_WRITE_eventually_left_p);


property run_WRITE_eventually_left_p;
  WRITE
|->
  s_eventually(!WRITE);
endproperty
run_WRITE_eventually_left_a: assert property (disable iff(rst) run_WRITE_eventually_left_p);


property run_DONE_eventually_left_p;
  DONE
|->
  s_eventually(!DONE);
endproperty
run_DONE_eventually_left_a: assert property (disable iff(rst) run_DONE_eventually_left_p);


parameter CONSISTENCY = 1;
if (CONSISTENCY) begin
// Check that no more than 1 state condition is met at the same time
  run_consistency_onehot0_state: assert property ( $onehot0({DONE, IDLE, READ, READ_EXEC, READ_WRITE, WRITE}) );
end


endmodule
