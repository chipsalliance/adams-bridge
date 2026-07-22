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
// | Created on 04.02.2025 at 10:58                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import fv_abr_keccak_round_pkg::*;
import fv_abr_keccak_round_functions::*;


module fv_abr_keccak_round_top(
  input logic rst,
  input logic clk,

  // Ports
  input logic data_in_vld,
  input logic data_in_rdy,
  input logic unsigned [1599:0] data_in,

  input logic clear_in,

  input logic squeezing_in,

  input logic unsigned [1599:0] state_out,

  input logic complete_out,

  input logic rand_consumed_out,

  input logic sparse_fsm_error_out,

  input logic round_count_error_out,

  input logic rst_storage_error_out,

  // Registers
  input logic signed [31:0] round_idx,
  input logic unsigned [1599:0] storage,

  // States
  input logic waiting_for_input,
  input logic round_state
);


default clocking default_clk @(posedge clk); endclocking


a_a_unsigned_64_5_5 stringToState_0_i;
assign stringToState_0_i = stringToState(storage);

a_a_unsigned_64_5_5 theta_0_i;
assign theta_0_i = theta(stringToState_0_i);

a_a_unsigned_64_5_5 rho_0_i;
assign rho_0_i = rho(theta_0_i);

a_a_unsigned_64_5_5 pi_0_i;
assign pi_0_i = pi(rho_0_i);

a_a_unsigned_64_5_5 chi_0_i;
assign chi_0_i = chi(pi_0_i);

a_a_unsigned_64_5_5 iota_0_i;
assign iota_0_i = iota(chi_0_i, (round_idx + 0));

a_a_unsigned_64_5_5 theta_1_i;
assign theta_1_i = theta(iota_0_i);

a_a_unsigned_64_5_5 rho_1_i;
assign rho_1_i = rho(theta_1_i);

a_a_unsigned_64_5_5 pi_1_i;
assign pi_1_i = pi(rho_1_i);

a_a_unsigned_64_5_5 chi_1_i;
assign chi_1_i = chi(pi_1_i);

a_a_unsigned_64_5_5 iota_1_i;
assign iota_1_i = iota(chi_1_i, (round_idx + 1));

logic unsigned [1599:0] stateToString_0_i;
assign stateToString_0_i = stateToString(iota_1_i);


property fsm_reset_p;
  $past(rst) |->
  waiting_for_input &&
  complete_out == 0 &&
  rand_consumed_out == 0 &&
  round_count_error_out == 0 &&
  round_idx == 0 &&
  rst_storage_error_out == 0 &&
  sparse_fsm_error_out == 0 &&
  state_out == 1600'd0 &&
  storage == 1600'd0 &&
  data_in_rdy == 1;
endproperty
fsm_reset_a: assert property (fsm_reset_p);


property fsm_round_state_to_round_state_p;
  round_state &&
  ((2 + round_idx) < 24)
|->
  ##1 ($stable(complete_out)) and
  ##1 ($stable(rand_consumed_out)) and
  ##1 ($stable(round_count_error_out)) and
  ##1 ($stable(rst_storage_error_out)) and
  ##1 ($stable(sparse_fsm_error_out)) and
  ##1 (data_in_rdy == 0) and
  ##1
  round_state &&
  round_idx == (2 + $past(round_idx, 1)) &&
  state_out == $past(stateToString_0_i, 1) &&
  storage == $past(stateToString_0_i, 1);
endproperty
fsm_round_state_to_round_state_a: assert property (disable iff(rst) fsm_round_state_to_round_state_p);


property fsm_round_state_to_waiting_for_input_p;
  round_state &&
  ((2 + round_idx) >= 24)
|->
  ##1 ($stable(rand_consumed_out)) and
  ##1 ($stable(round_count_error_out)) and
  ##1 ($stable(rst_storage_error_out)) and
  ##1 ($stable(sparse_fsm_error_out)) and
  ##1
  waiting_for_input &&
  complete_out == 1 &&
  round_idx == 0 &&
  state_out == $past(stateToString_0_i, 1) &&
  storage == $past(stateToString_0_i, 1) &&
  data_in_rdy == 1;
endproperty
fsm_round_state_to_waiting_for_input_a: assert property (disable iff(rst) fsm_round_state_to_waiting_for_input_p);


property fsm_waiting_for_input_to_round_state_p;
  waiting_for_input &&
  !clear_in &&
  data_in_vld &&
  !squeezing_in
|->
  ##1 ($stable(rand_consumed_out)) and
  ##1 ($stable(round_count_error_out)) and
  ##1 ($stable(rst_storage_error_out)) and
  ##1 ($stable(sparse_fsm_error_out)) and
  ##1 (data_in_rdy == 0) and
  ##1
  round_state &&
  complete_out == 0 &&
  round_idx == 0 &&
  state_out == ($past(storage, 1) ^ $past(data_in, 1)) &&
  storage == ($past(storage, 1) ^ $past(data_in, 1));
endproperty
fsm_waiting_for_input_to_round_state_a: assert property (disable iff(rst) fsm_waiting_for_input_to_round_state_p);


property fsm_waiting_for_input_to_round_state_1_p;
  waiting_for_input &&
  !clear_in &&
  data_in_vld &&
  squeezing_in
|->
  ##1 ($stable(rand_consumed_out)) and
  ##1 ($stable(round_count_error_out)) and
  ##1 ($stable(rst_storage_error_out)) and
  ##1 ($stable(sparse_fsm_error_out)) and
  ##1 ($stable(state_out)) and
  ##1 (data_in_rdy == 0) and
  ##1
  round_state &&
  complete_out == 0 &&
  round_idx == 0 &&
  $stable(storage);
endproperty
fsm_waiting_for_input_to_round_state_1_a: assert property (disable iff(rst) fsm_waiting_for_input_to_round_state_1_p);


property fsm_waiting_for_input_to_waiting_for_input_p;
  waiting_for_input &&
  clear_in
|->
  ##1 ($stable(rand_consumed_out)) and
  ##1 ($stable(round_count_error_out)) and
  ##1 ($stable(rst_storage_error_out)) and
  ##1 ($stable(sparse_fsm_error_out)) and
  ##1
  waiting_for_input &&
  complete_out == 0 &&
  $stable(round_idx) &&
  state_out == 1600'd0 &&
  storage == 1600'd0 &&
  data_in_rdy == 1;
endproperty
fsm_waiting_for_input_to_waiting_for_input_a: assert property (disable iff(rst) fsm_waiting_for_input_to_waiting_for_input_p);


property fsm_waiting_for_input_to_waiting_for_input_1_p;
  waiting_for_input &&
  !clear_in &&
  !data_in_vld
|->
  ##1 ($stable(rand_consumed_out)) and
  ##1 ($stable(round_count_error_out)) and
  ##1 ($stable(rst_storage_error_out)) and
  ##1 ($stable(sparse_fsm_error_out)) and
  ##1 ($stable(state_out)) and
  ##1
  waiting_for_input &&
  complete_out == 0 &&
  $stable(round_idx) &&
  $stable(storage) &&
  data_in_rdy == 1;
endproperty
fsm_waiting_for_input_to_waiting_for_input_1_a: assert property (disable iff(rst) fsm_waiting_for_input_to_waiting_for_input_1_p);


property fsm_waiting_for_input_eventually_left_p;
  waiting_for_input
|->
  s_eventually(!waiting_for_input);
endproperty
fsm_waiting_for_input_eventually_left_a: assert property (disable iff(rst) fsm_waiting_for_input_eventually_left_p);


property fsm_round_state_eventually_left_p;
  round_state
|->
  s_eventually(!round_state);
endproperty
fsm_round_state_eventually_left_a: assert property (disable iff(rst) fsm_round_state_eventually_left_p);


parameter CONSISTENCY = 1;
if (CONSISTENCY) begin
  // Check that no more than 1 state condition is met at the same time
  fsm_consistency_onehot0_state: assert property($onehot0({ round_state, waiting_for_input }));
end


endmodule
