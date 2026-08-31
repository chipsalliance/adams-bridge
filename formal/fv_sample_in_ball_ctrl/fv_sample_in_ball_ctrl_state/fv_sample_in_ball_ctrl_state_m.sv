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
// | Created on 20.02.2025 at 18:38                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import fv_sample_in_ball_ctrl_pkg::*;
import fv_sample_in_ball_ctrl_state_functions::*;


module fv_sample_in_ball_ctrl_state_m(
  input logic rst_n,
  input logic clk,

  // Ports
  input logic data_i_port_vld,
  input logic data_i_port_rdy,
  input logic unsigned [31:0] data_i_port,

  input logic data_valid_i,

  input logic unsigned [59:0] sign_buffer,

  input logic unsigned [59:0] sign_buffer_in,

  input logic unsigned [7:0] rej_value_in,

  input logic rej_value_en,

  input logic unsigned [7:0] rej_value,

  input logic read_valid,

  input logic read_valid_in,

  input logic index_found,

  // States
  input logic IDLE,
  input logic SIGN_BUFFER,
  input logic ACTIVE,
  input logic DONE
);


default clocking default_clk @(posedge clk); endclocking


sequence reset_sequence;
  !rst_n ##1 rst_n;
endsequence


property run_reset_p;
  reset_sequence |->
  IDLE &&
  read_valid == 0 &&
  rej_value == 8'hC4 &&
  sign_buffer == 60'd0;
endproperty
run_reset_a: assert property (run_reset_p);


property run_ACTIVE_to_ACTIVE_p;
  ACTIVE &&
  rej_value_en &&
  (rej_value_in < 64'd255)
|->
  ##1
  ACTIVE &&
  read_valid == ($past(index_found, 1) && !$past(read_valid_in, 1)) &&
  rej_value == 8'((64'd1 + $past(rej_value_in, 1))) &&
  sign_buffer == ({ 1'h0, { $past(sign_buffer_in, 1) }[59:1]} );
endproperty
run_ACTIVE_to_ACTIVE_a: assert property (disable iff(!rst_n) run_ACTIVE_to_ACTIVE_p);


property run_ACTIVE_to_ACTIVE_1_p;
  ACTIVE &&
  !rej_value_en &&
  (rej_value_in < 64'd255)
|->
  ##1 ($stable(rej_value)) and
  ##1 ($stable(sign_buffer)) and
  ##1
  ACTIVE &&
  read_valid == ($past(index_found, 1) && !$past(read_valid_in, 1));
endproperty
run_ACTIVE_to_ACTIVE_1_a: assert property (disable iff(!rst_n) run_ACTIVE_to_ACTIVE_1_p);


property run_ACTIVE_to_DONE_p;
  ACTIVE &&
  rej_value_en &&
  (rej_value_in >= 64'd255)
|->
  ##1
  DONE &&
  read_valid == ($past(index_found, 1) && !$past(read_valid_in, 1)) &&
  rej_value == 8'((64'd1 + $past(rej_value_in, 1))) &&
  sign_buffer == ({ 1'h0, { $past(sign_buffer_in, 1) }[59:1]} );
endproperty
run_ACTIVE_to_DONE_a: assert property (disable iff(!rst_n) run_ACTIVE_to_DONE_p);


property run_ACTIVE_to_DONE_1_p;
  ACTIVE &&
  !rej_value_en &&
  (rej_value_in >= 64'd255)
|->
  ##1 ($stable(rej_value)) and
  ##1 ($stable(sign_buffer)) and
  ##1
  DONE &&
  read_valid == ($past(index_found, 1) && !$past(read_valid_in, 1));
endproperty
//run_ACTIVE_to_DONE_1_a: assert property (disable iff(!rst_n) run_ACTIVE_to_DONE_1_p); 
//not a valid assertion as it presents unrealistic condition (it will never reach DONE state if **rej_value_en** is not asserted).


property run_DONE_to_IDLE_p;
  DONE
|->
  ##1
  IDLE &&
  read_valid == 0 &&
  rej_value == 8'hC4 &&
  sign_buffer == 60'd0;
endproperty
//run_DONE_to_IDLE_a: assert property (disable iff(!rst_n) run_DONE_to_IDLE_p);
//commented because DONE to IDLE transition doesn't exist as per design

property run_IDLE_to_SIGN_BUFFER_p;
  IDLE &&
  data_i_port_vld
|->
  ##1
  SIGN_BUFFER &&
  read_valid == 0 &&
  rej_value == 8'hC4 &&
  sign_buffer == 60'($past(data_i_port, 1));
endproperty
run_IDLE_to_SIGN_BUFFER_a: assert property (disable iff(!rst_n) run_IDLE_to_SIGN_BUFFER_p);


property run_SIGN_BUFFER_to_ACTIVE_p;
  SIGN_BUFFER &&
  data_i_port_vld
|->
  ##1
  ACTIVE &&
  read_valid == 0 &&
  rej_value == 8'hC4 &&
  sign_buffer == ($past(sign_buffer_in, 1) | 60'(({ { 64'({ $past(data_i_port, 1) }) }[31:0], 'h0} )));
endproperty
run_SIGN_BUFFER_to_ACTIVE_a: assert property (disable iff(!rst_n) run_SIGN_BUFFER_to_ACTIVE_p);


property run_IDLE_wait_p;
  IDLE &&
  !data_i_port_vld
|->
  ##1 ($stable(read_valid)) and
  ##1 ($stable(rej_value)) and
  ##1 ($stable(sign_buffer)) and
  ##1
  IDLE;
endproperty
run_IDLE_wait_a: assert property (disable iff(!rst_n) run_IDLE_wait_p);


property run_SIGN_BUFFER_wait_p;
  SIGN_BUFFER &&
  !data_i_port_vld
|->
  ##1 ($stable(read_valid)) and
  ##1 ($stable(rej_value)) and
  ##1 ($stable(sign_buffer)) and
  ##1
  SIGN_BUFFER;
endproperty
run_SIGN_BUFFER_wait_a: assert property (disable iff(!rst_n) run_SIGN_BUFFER_wait_p);


property run_IDLE_eventually_left_p;
  IDLE
|->
  s_eventually(!IDLE);
endproperty
run_IDLE_eventually_left_a: assert property (disable iff(!rst_n) run_IDLE_eventually_left_p);


property run_SIGN_BUFFER_eventually_left_p;
  SIGN_BUFFER
|->
  s_eventually(!SIGN_BUFFER);
endproperty
run_SIGN_BUFFER_eventually_left_a: assert property (disable iff(!rst_n) run_SIGN_BUFFER_eventually_left_p);


property run_ACTIVE_eventually_left_p;
  ACTIVE
|->
  s_eventually(!ACTIVE);
endproperty
run_ACTIVE_eventually_left_a: assert property (disable iff(!rst_n) run_ACTIVE_eventually_left_p);


property run_DONE_eventually_left_p;
  DONE
|->
  s_eventually(!DONE);
endproperty
//run_DONE_eventually_left_a: assert property (disable iff(!rst_n) run_DONE_eventually_left_p);
////commented because DONE to IDLE transition doesn't exist as per design

parameter CONSISTENCY = 1;
if (CONSISTENCY) begin
  // Check that no more than 1 state condition is met at the same time
  run_consistency_onehot0_state: assert property($onehot0({ ACTIVE, DONE, IDLE, SIGN_BUFFER }));
end


endmodule
