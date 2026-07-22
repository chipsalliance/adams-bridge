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
// | Created on 19.12.2024 at 18:34                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import fv_rej_bounded_ctrl_pkg::*;
import fv_rej_bounded_ctrl_functions::*;


module fv_rej_bounded_ctrl_m(
  input logic rst_n,
  input logic clk,

  // Ports
  input logic data_valid_i,

  input logic data_hold_o_vld,
  input logic data_hold_o,

  input logic data_valid_o_vld,
  input logic data_valid_o,

  input a_unsigned_4_8 data_i,

  input a_unsigned_24_4 data_o,

  input a_unsigned_3_8 fifo_data_i,

  input a_unsigned_3_4 fifo_data_o,

  input logic unsigned [7:0] fifo_valid_i,

  // States
  input logic buffer_full_state,
  input logic regular_state,
  input logic no_valid_data_state
);


default clocking default_clk @(posedge clk); endclocking


a_unsigned_3_8 rejBoundedData_0_i;
assign rejBoundedData_0_i = rejBoundedData(data_i);

logic unsigned [7:0] rejBoundedValid_0_i;
assign rejBoundedValid_0_i = rejBoundedValid(data_i, data_valid_i);

a_unsigned_24_4 modMux_0_i;
assign modMux_0_i = modMux(fifo_data_o);


sequence reset_sequence;
  !rst_n ##1 rst_n;
endsequence


property run_reset_p;
  $past(!rst_n) |->
  no_valid_data_state &&
  data_hold_o == 0 &&
  data_o == modMux_0_i &&
  data_valid_o == 0 &&
  fifo_data_i == rejBoundedData_0_i &&
  fifo_valid_i == rejBoundedValid_0_i;
endproperty
run_reset_a: assert property (run_reset_p);


property run_buffer_full_state_to_buffer_full_state_p;
  buffer_full_state
|->
  buffer_full_state &&
  data_hold_o == 1 &&
  data_o == modMux_0_i &&
  data_valid_o == 1 &&
  fifo_data_i == rejBoundedData_0_i &&
  fifo_valid_i == rejBoundedValid_0_i;
endproperty
run_buffer_full_state_to_buffer_full_state_a: assert property (disable iff(!rst_n) run_buffer_full_state_to_buffer_full_state_p);


property run_no_valid_data_state_to_no_valid_data_state_p;
  no_valid_data_state
|->
  no_valid_data_state &&
  data_hold_o == 0 &&
  data_o == modMux_0_i &&
  data_valid_o == 0 &&
  fifo_data_i == rejBoundedData_0_i &&
  fifo_valid_i == rejBoundedValid_0_i;
endproperty
run_no_valid_data_state_to_no_valid_data_state_a: assert property (disable iff(!rst_n) run_no_valid_data_state_to_no_valid_data_state_p);


property run_regular_state_to_regular_state_p;
  regular_state
|->
  regular_state &&
  data_hold_o == 0 &&
  data_o == modMux_0_i &&
  data_valid_o == 1 &&
  fifo_data_i == rejBoundedData_0_i &&
  fifo_valid_i == rejBoundedValid_0_i;
endproperty
run_regular_state_to_regular_state_a: assert property (disable iff(!rst_n) run_regular_state_to_regular_state_p);


property run_buffer_full_state_eventually_left_p;
  buffer_full_state
|->
  s_eventually(!buffer_full_state);
endproperty
run_buffer_full_state_eventually_left_a: assert property (disable iff(!rst_n) run_buffer_full_state_eventually_left_p);


parameter CONSISTENCY = 1;
if (CONSISTENCY) begin
// Check that no more than 1 state condition is met at the same time
  run_CONSISTENCY_onehot0_state: assert property ( $onehot0({buffer_full_state, no_valid_data_state, regular_state}) );
end


endmodule
