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
// | Created on 06.02.2025 at 10:55                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


module fv_mldsa_sampler_top_m(
  input logic rst_n,
  input logic clk,

  // Ports
  input logic sha3_done_vld,
  input logic unsigned [3:0] sha3_done,

  input logic sha3_process_vld,
  input logic sha3_process,

  input logic sha3_run_vld,
  input logic sha3_run,

  input logic sampler_start_i,

  input logic sampler_done,

  input logic sha3_state_dv,

  input logic sha3_state_hold,

  input logic sha3_squeezing,

  // Registers
  input logic unsigned [2:0] cur_st,
  input logic sampler_done_temp,
  input logic sampler_start_i_temp,
  input logic unsigned [2:0] sha3_fsm_temp,
  input logic sha3_squeezing_temp,
  input logic sha3_state_dv_temp,
  input logic sha3_state_hold_temp,

  // States
  input logic IDLE,
  input logic PROC,
  input logic WAIT,
  input logic RUN,
  input logic DONE
);


default clocking default_clk @(posedge clk); endclocking


sequence reset_sequence;
  !rst_n ##1 rst_n;
endsequence


property run_reset_p;
  $past(!rst_n) |->
  IDLE &&
  sha3_done == 4'h9 &&
  sha3_process == 0 &&
  sha3_run == 0
  ;
endproperty
run_reset_a: assert property (run_reset_p);


property run_DONE_to_DONE_p;
  DONE &&
  sha3_squeezing_temp
|->
  ##1
  DONE &&
  sha3_done == ((sha3_fsm_temp == 3'h2) ? 4'd6 : 4'd9) &&
  sha3_process == 0 &&
  sha3_run == 0;
endproperty
run_DONE_to_DONE_a: assert property (disable iff(!rst_n) run_DONE_to_DONE_p);


property run_DONE_to_IDLE_p;
  DONE &&
  !sha3_squeezing_temp
|->
  ##1
  IDLE &&
  sha3_done == 4'h9 &&
  sha3_process == 0 &&
  sha3_run == 0;
endproperty
run_DONE_to_IDLE_a: assert property (disable iff(!rst_n) run_DONE_to_IDLE_p);


property run_IDLE_to_IDLE_p;
  IDLE &&
  !sampler_start_i_temp &&
  (cur_st != 3'h1) &&
  (cur_st != 3'h2) &&
  (cur_st != 3'h3) &&
  (cur_st != 3'h4)
|->
  ##1
  IDLE &&
  sha3_done == 4'h9 &&
  sha3_process == 0 &&
  sha3_run == 0;
endproperty
run_IDLE_to_IDLE_a: assert property (disable iff(!rst_n) run_IDLE_to_IDLE_p);


property run_IDLE_to_PROC_p;
  IDLE &&
  sampler_start_i_temp &&
  (cur_st != 3'h1) &&
  (cur_st != 3'h2) &&
  (cur_st != 3'h3) &&
  (cur_st != 3'h4)
|->
  ##1
  PROC &&
  sha3_done == 4'h9 &&
  sha3_process == 1 &&
  sha3_run == 0;
endproperty
run_IDLE_to_PROC_a: assert property (disable iff(!rst_n) run_IDLE_to_PROC_p);


property run_PROC_to_WAIT_p;
  PROC &&
  (cur_st != 3'h2) &&
  (cur_st != 3'h3) &&
  (cur_st != 3'h4)
|->
  ##1
  WAIT &&
  sha3_done == 4'h9 &&
  sha3_process == 0 &&
  sha3_run == 0;
endproperty
run_PROC_to_WAIT_a: assert property (disable iff(!rst_n) run_PROC_to_WAIT_p);


property run_RUN_to_DONE_p;
  RUN &&
  sampler_done_temp &&
  (cur_st != 3'h4)
|->
  ##1
  DONE &&
  sha3_done == ((sha3_fsm_temp == 3'h2) ? 4'd6 : 4'd9) &&
  sha3_process == 0 &&
  sha3_run == 0;
endproperty
run_RUN_to_DONE_a: assert property (disable iff(!rst_n) run_RUN_to_DONE_p);


property run_RUN_to_WAIT_p;
  RUN &&
  !sampler_done_temp &&
  (cur_st != 3'h4)
|->
  ##1
  WAIT &&
  sha3_done == 4'h9 &&
  sha3_process == 0 &&
  sha3_run == 0;
endproperty
run_RUN_to_WAIT_a: assert property (disable iff(!rst_n) run_RUN_to_WAIT_p);


property run_WAIT_to_DONE_p;
  WAIT &&
  sampler_done_temp &&
  (cur_st != 3'h3) &&
  (cur_st != 3'h4)
|->
  ##1
  DONE &&
  sha3_done == ((sha3_fsm_temp == 3'h2) ? 4'd6 : 4'd9) &&
  sha3_process == 0 &&
  sha3_run == 0;
endproperty
run_WAIT_to_DONE_a: assert property (disable iff(!rst_n) run_WAIT_to_DONE_p);


property run_WAIT_to_RUN_p;
  WAIT &&
  !sampler_done_temp &&
  sha3_state_dv_temp &&
  !sha3_state_hold_temp &&
  (cur_st != 3'h3) &&
  (cur_st != 3'h4)
|->
  ##1
  RUN &&
  sha3_done == 4'h9 &&
  sha3_process == 0 &&
  sha3_run == !sampler_done;
endproperty
run_WAIT_to_RUN_a: assert property (disable iff(!rst_n) run_WAIT_to_RUN_p);


property run_WAIT_to_WAIT_p;
  WAIT &&
  !sampler_done_temp &&
  (!sha3_state_dv_temp || sha3_state_hold_temp) &&
  (cur_st != 3'h3) &&
  (cur_st != 3'h4)
|->
  ##1
  WAIT &&
  sha3_done == 4'h9 &&
  sha3_process == 0 &&
  sha3_run == 0;
endproperty
run_WAIT_to_WAIT_a: assert property (disable iff(!rst_n) run_WAIT_to_WAIT_p);


property run_IDLE_eventually_left_p;
  IDLE
|->
  s_eventually(!IDLE);
endproperty
run_IDLE_eventually_left_a: assert property (disable iff(!rst_n) run_IDLE_eventually_left_p);


property run_PROC_eventually_left_p;
  PROC
|->
  s_eventually(!PROC);
endproperty
run_PROC_eventually_left_a: assert property (disable iff(!rst_n) run_PROC_eventually_left_p);


property run_WAIT_eventually_left_p;
  WAIT
|->
  s_eventually(!WAIT);
endproperty
run_WAIT_eventually_left_a: assert property (disable iff(!rst_n) run_WAIT_eventually_left_p);


property run_RUN_eventually_left_p;
  RUN
|->
  s_eventually(!RUN);
endproperty
run_RUN_eventually_left_a: assert property (disable iff(!rst_n) run_RUN_eventually_left_p);


property run_DONE_eventually_left_p;
  DONE
|->
  s_eventually(!DONE);
endproperty
run_DONE_eventually_left_a: assert property (disable iff(!rst_n) run_DONE_eventually_left_p);


parameter CONSISTENCY = 1;
if (CONSISTENCY) begin
  // Check that no more than 1 state condition is met at the same time
  run_consistency_onehot0_state: assert property($onehot0({ DONE, IDLE, PROC, RUN, WAIT }));
end


endmodule
