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
// | Contact: contact@lubis-eda.com                    |
// +---------------------------------------------------+


module fv_sampler_top_m (
  input logic rst,
  input logic clk,

  // Ports
  input logic sha3_process_vld,
  input logic sha3_process,

  input logic sha3_run_vld,
  input logic sha3_run,

  input logic sampler_start_i,

  input logic unsigned [2:0] sha3_fsm,

  input logic sampler_done,

  input logic sha3_state_dv,

  input logic sha3_state_hold,

  input logic sha3_squeezing,

  // Registers
  input logic unsigned [2:0] cur_st,
  input logic sampler_done_temp,
  input logic sampler_start_i_temp,
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
    rst ##1!rst;
  endsequence


  property run_reset_p;
    $past(rst)
  |->
    IDLE &&
    sha3_process == 0 &&
    sha3_run == 0 &&
    sha3_process_vld == 1 &&
    sha3_run_vld == 1;
  endproperty
  a_run_reset: assert property (run_reset_p);

  //squeezing signal will never set during MLDSA_SAMPLER_DONE
  /*property run_DONE_to_DONE_p;
    DONE &&
    sha3_squeezing_temp
  |->
    ##1
    DONE &&
    sha3_process == 0 &&
    sha3_run == 0 &&
    sha3_process_vld == 1 &&
    sha3_run_vld == 1;
  endproperty
  a_run_done_to_done: assert property (disable iff (rst) run_DONE_to_DONE_p); */


  property run_DONE_to_IDLE_p;
    DONE &&
    !sha3_squeezing_temp
  |->
    ##1
    IDLE &&
    sha3_process == 0 &&
    sha3_run == 0 &&
    sha3_process_vld == 1 &&
    sha3_run_vld == 1;
  endproperty
  a_run_done_to_idle: assert property (disable iff (rst) run_DONE_to_IDLE_p);

  property mask_mode;
    ##1 DONE
    && abr_sampler_top.sampler_mode_i == abr_sampler_pkg::ABR_EXP_MASK
  |->
    $past(sha3_squeezing_temp);
  endproperty
  a_mask_mode: assert property (mask_mode);



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
    sha3_process == 0 &&
    sha3_run == 0 &&
    sha3_process_vld == 1 &&
    sha3_run_vld == 1;
  endproperty
  a_run_idle_to_idle: assert property (disable iff (rst) run_IDLE_to_IDLE_p);


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
    sha3_process == 1 &&
    sha3_run == 0 &&
    sha3_process_vld == 1 &&
    sha3_run_vld == 1;
  endproperty
  a_run_idle_to_proc: assert property (disable iff (rst) run_IDLE_to_PROC_p);


  property run_PROC_to_WAIT_p;
    PROC &&
    (cur_st != 3'h2) &&
    (cur_st != 3'h3) &&
    (cur_st != 3'h4)
  |->
    ##1
    WAIT &&
    sha3_process == 0 &&
    sha3_run == 0 &&
    sha3_process_vld == 1 &&
    sha3_run_vld == 1;
  endproperty
  a_run_proc_to_wait: assert property (disable iff (rst) run_PROC_to_WAIT_p);


  property run_RUN_to_DONE_p;
    RUN &&
    sampler_done_temp &&
    (cur_st != 3'h4)
  |->
    ##1
    DONE &&
    sha3_process == 0 &&
    sha3_run == 0 &&
    sha3_process_vld == 1 &&
    sha3_run_vld == 1;
  endproperty
  a_run_run_to_done: assert property (disable iff (rst) run_RUN_to_DONE_p);


  property run_RUN_to_WAIT_p;
    RUN &&
    !sampler_done_temp &&
    (cur_st != 3'h4)
  |->
    ##1
    WAIT &&
    sha3_process == 0 &&
    sha3_run == 0 &&
    sha3_process_vld == 1 &&
    sha3_run_vld == 1;
  endproperty
  a_run_run_to_wait: assert property (disable iff (rst) run_RUN_to_WAIT_p);


  property run_WAIT_to_DONE_p;
    WAIT &&
    sampler_done_temp &&
    (cur_st != 3'h3) &&
    (cur_st != 3'h4)
  |->
    ##1
    DONE &&
    sha3_process == 0 &&
    sha3_run == 0 &&
    sha3_process_vld == 1 &&
    sha3_run_vld == 1;
  endproperty
  a_run_wait_to_done: assert property (disable iff (rst) run_WAIT_to_DONE_p);


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
    sha3_process == 0 &&
    sha3_run == !sampler_done &&
    sha3_process_vld == 1 &&
    sha3_run_vld == 1;
  endproperty
  a_run_wait_to_run: assert property (disable iff (rst) run_WAIT_to_RUN_p);


  property run_WAIT_to_WAIT_p;
    WAIT &&
    !sampler_done_temp &&
    (!sha3_state_dv_temp || sha3_state_hold_temp) &&
    (cur_st != 3'h3) &&
    (cur_st != 3'h4)
  |->
    ##1
    WAIT &&
    sha3_process == 0 &&
    sha3_run == 0 &&
    sha3_process_vld == 1 &&
    sha3_run_vld == 1;
  endproperty
  a_run_wait_to_wait: assert property (disable iff (rst) run_WAIT_to_WAIT_p);


  property run_IDLE_eventually_left_p;
    IDLE
  |->
    s_eventually(!IDLE);
  endproperty
  a_run_idle_eventually_left: assert property (disable iff (rst) run_IDLE_eventually_left_p);


  property run_PROC_eventually_left_p;
    PROC
  |->
    s_eventually(!PROC);
  endproperty
  a_run_proc_eventually_left: assert property (disable iff (rst) run_PROC_eventually_left_p);


  property run_WAIT_eventually_left_p;
    WAIT
  |->
    s_eventually(!WAIT);
  endproperty
  a_run_wait_eventually_left: assert property (disable iff (rst) run_WAIT_eventually_left_p);


  property run_RUN_eventually_left_p;
    RUN
  |->
    s_eventually(!RUN);
  endproperty
  a_run_run_eventually_left: assert property (disable iff (rst) run_RUN_eventually_left_p);


  property run_DONE_eventually_left_p;
    DONE
  |->
    s_eventually(!DONE);
  endproperty
  a_run_done_eventually_left: assert property (disable iff (rst) run_DONE_eventually_left_p);




endmodule
