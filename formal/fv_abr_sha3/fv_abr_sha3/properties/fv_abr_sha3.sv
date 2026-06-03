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
// | Created on 30.10.2025 at 09:24                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import fv_abr_sha3_pkg::*;
import abr_sha3_pkg::*;
import fv_abr_sha3_pkg::*;


module fv_fv_abr_sha3_m(
  input logic rst,
  input logic clk,

  // Ports
  input logic fv_start_i,

  input logic fv_keccak_complete_i_vld,
  input logic fv_keccak_complete_i_rdy,
  input logic fv_keccak_complete_i,

  input logic fv_run_i,

  input logic fv_state_valid_hold_i,

  input logic fv_absorbed_i,

  input logic fv_squeezing_o,

  input logic fv_absorbed_o,

  input e_state fv_sha3_fsm_o,

  input logic fv_state_valid_o,

  // States
  input logic IDLE,
  input logic ABSORB,
  input logic SQUEEZE,
  input logic RUN
);


default clocking default_clk @(posedge clk); endclocking


sequence reset_sequence;
  rst ##1 !rst;
endsequence


property process_reset_p;
  reset_sequence |->
  IDLE &&
  fv_absorbed_o == 0 &&
  fv_sha3_fsm_o == IDLE_ST &&
  fv_squeezing_o == 0 &&
  fv_state_valid_o == 0;
endproperty
process_reset_a: assert property (process_reset_p);


property process_ABSORB_to_ABSORB_p;
  ABSORB &&
  !fv_absorbed_i &&
  !fv_state_valid_hold_i
|->
  ##1 ($stable(fv_absorbed_o) &&
    $stable(fv_squeezing_o)) and
  ##1
  ABSORB &&
  fv_sha3_fsm_o == ABSORB_ST &&
  fv_state_valid_o == 0;
endproperty
process_ABSORB_to_ABSORB_a: assert property (disable iff(rst) process_ABSORB_to_ABSORB_p);


property process_ABSORB_to_ABSORB_1_p;
  ABSORB &&
  !fv_absorbed_i &&
  fv_state_valid_hold_i
|->
  ##1 ($stable(fv_absorbed_o) &&
    $stable(fv_squeezing_o) &&
    $stable(fv_state_valid_o)) and
  ##1
  ABSORB &&
  fv_sha3_fsm_o == ABSORB_ST;
endproperty
process_ABSORB_to_ABSORB_1_a: assert property (disable iff(rst) process_ABSORB_to_ABSORB_1_p);


property process_ABSORB_to_SQUEEZE_p;
  ABSORB &&
  fv_absorbed_i
|->
  ##1
  SQUEEZE &&
  fv_absorbed_o == 1 &&
  fv_sha3_fsm_o == SQUEEZE_ST &&
  fv_squeezing_o == 1 &&
  fv_state_valid_o == 1;
endproperty
process_ABSORB_to_SQUEEZE_a: assert property (disable iff(rst) process_ABSORB_to_SQUEEZE_p);


property process_IDLE_to_ABSORB_p;
  IDLE &&
  !fv_state_valid_hold_i &&
  fv_start_i
|->
  ##1 ($stable(fv_absorbed_o) &&
    $stable(fv_squeezing_o)) and
  ##1
  ABSORB &&
  fv_sha3_fsm_o == ABSORB_ST &&
  fv_state_valid_o == 0;
endproperty
process_IDLE_to_ABSORB_a: assert property (disable iff(rst) process_IDLE_to_ABSORB_p);


property process_IDLE_to_ABSORB_1_p;
  IDLE &&
  fv_state_valid_hold_i &&
  fv_start_i
|->
  ##1 ($stable(fv_absorbed_o) &&
    $stable(fv_squeezing_o) &&
    $stable(fv_state_valid_o)) and
  ##1
  ABSORB &&
  fv_sha3_fsm_o == ABSORB_ST;
endproperty
process_IDLE_to_ABSORB_1_a: assert property (disable iff(rst) process_IDLE_to_ABSORB_1_p);


property process_IDLE_to_IDLE_p;
  IDLE &&
  !fv_state_valid_hold_i &&
  !fv_start_i
|->
  ##1 ($stable(fv_absorbed_o) &&
    $stable(fv_sha3_fsm_o) &&
    $stable(fv_squeezing_o)) and
  ##1
  IDLE &&
  fv_state_valid_o == 0;
endproperty
process_IDLE_to_IDLE_a: assert property (disable iff(rst) process_IDLE_to_IDLE_p);


property process_IDLE_to_IDLE_1_p;
  IDLE &&
  fv_state_valid_hold_i &&
  !fv_start_i
|->
  ##1 ($stable(fv_absorbed_o) &&
    $stable(fv_sha3_fsm_o) &&
    $stable(fv_squeezing_o) &&
    $stable(fv_state_valid_o)) and
  ##1
  IDLE;
endproperty
process_IDLE_to_IDLE_1_a: assert property (disable iff(rst) process_IDLE_to_IDLE_1_p);


property process_RUN_to_SQUEEZE_p;
  RUN &&
  fv_keccak_complete_i_vld
|->
  ##1 ($stable(fv_absorbed_o)) and
  ##1
  SQUEEZE &&
  fv_sha3_fsm_o == SQUEEZE_ST &&
  fv_squeezing_o == 1 &&
  fv_state_valid_o == 1;
endproperty
process_RUN_to_SQUEEZE_a: assert property (disable iff(rst) process_RUN_to_SQUEEZE_p);


property process_SQUEEZE_to_RUN_p;
  SQUEEZE &&
  !fv_state_valid_hold_i &&
  fv_run_i
|->
  ##1
  RUN &&
  fv_absorbed_o == 0 &&
  fv_sha3_fsm_o == RUN_ST &&
  fv_squeezing_o == 1 &&
  fv_state_valid_o == 0;
endproperty
process_SQUEEZE_to_RUN_a: assert property (disable iff(rst) process_SQUEEZE_to_RUN_p);


property process_SQUEEZE_to_RUN_1_p;
  SQUEEZE &&
  fv_state_valid_hold_i &&
  fv_run_i
|->
  ##1 ($stable(fv_state_valid_o)) and
  ##1
  RUN &&
  fv_absorbed_o == 0 &&
  fv_sha3_fsm_o == RUN_ST &&
  fv_squeezing_o == 1;
endproperty
process_SQUEEZE_to_RUN_1_a: assert property (disable iff(rst) process_SQUEEZE_to_RUN_1_p);


property process_SQUEEZE_to_SQUEEZE_p;
  SQUEEZE &&
  !fv_state_valid_hold_i &&
  !fv_run_i
|->
  ##1
  SQUEEZE &&
  fv_absorbed_o == 0 &&
  fv_sha3_fsm_o == SQUEEZE_ST &&
  fv_squeezing_o == 1 &&
  fv_state_valid_o == 0;
endproperty
process_SQUEEZE_to_SQUEEZE_a: assert property (disable iff(rst) process_SQUEEZE_to_SQUEEZE_p);


property process_SQUEEZE_to_SQUEEZE_1_p;
  SQUEEZE &&
  fv_state_valid_hold_i &&
  !fv_run_i
|->
  ##1 ($stable(fv_state_valid_o)) and
  ##1
  SQUEEZE &&
  fv_absorbed_o == 0 &&
  fv_sha3_fsm_o == SQUEEZE_ST &&
  fv_squeezing_o == 1;
endproperty
process_SQUEEZE_to_SQUEEZE_1_a: assert property (disable iff(rst) process_SQUEEZE_to_SQUEEZE_1_p);


property process_RUN_wait_p;
  RUN &&
  !fv_keccak_complete_i_vld
|->
  ##1 ($stable(fv_absorbed_o) &&
    $stable(fv_sha3_fsm_o) &&
    $stable(fv_squeezing_o) &&
    $stable(fv_state_valid_o)) and
  ##1
  RUN;
endproperty
process_RUN_wait_a: assert property (disable iff(rst) process_RUN_wait_p);


property process_IDLE_eventually_left_p;
  IDLE &&
  fv_start_i
|->
  ##1 !IDLE;
endproperty
process_IDLE_eventually_left_a: assert property (disable iff(rst) process_IDLE_eventually_left_p);


property process_ABSORB_eventually_left_p;
  ABSORB
|->
  s_eventually(!ABSORB);
endproperty
process_ABSORB_eventually_left_a: assert property (disable iff(rst) process_ABSORB_eventually_left_p);


property process_SQUEEZE_eventually_left_p;
  SQUEEZE &&
  fv_run_i
|->
  ##1 !SQUEEZE;
endproperty
process_SQUEEZE_eventually_left_a: assert property (disable iff(rst) process_SQUEEZE_eventually_left_p);


property process_RUN_eventually_left_p;
  RUN
|->
  s_eventually(!RUN);
endproperty
process_RUN_eventually_left_a: assert property (disable iff(rst) process_RUN_eventually_left_p);


parameter CONSISTENCY = 1;
if (CONSISTENCY) begin
  // Check that no more than 1 state condition is met at the same time
  process_consistency_onehot0_state: assert property($onehot0({ ABSORB, IDLE, RUN, SQUEEZE }));
end


endmodule
