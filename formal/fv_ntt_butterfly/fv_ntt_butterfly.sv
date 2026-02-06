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
// | Created on 19.03.2025 at 18:17                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import ntt_defines_pkg::*;
import ntt_butterfly_functions::*;


module fv_ntt_butterfly_m(
  input logic rst_n,
  input logic clk,

  // Ports
  input logic unsigned [22:0] opu_i,

  input logic unsigned [22:0] opv_i,

  input logic unsigned [22:0] opw_i,

  input logic unsigned [2:0] mode,

  input logic unsigned [0:0] accumulate,

  input logic unsigned [22:0] u_o,

  input logic unsigned [22:0] v_o,

  input logic unsigned [22:0] pwm_res_o,

  input logic unsigned [22:0] u_reg,

  input logic unsigned [22:0] u_reg_d2,

  input logic unsigned [22:0] u_reg_d3,

  input logic unsigned [22:0] u_reg_d4,

  input logic unsigned [22:0] w_reg,

  input logic unsigned [22:0] w_reg_d2,

  input logic unsigned [22:0] w_reg_d3,

  input logic unsigned [22:0] w_reg_d4,

  input logic unsigned [22:0] add_res,

  input logic unsigned [22:0] add_res_d1,

  input logic unsigned [22:0] add_res_d2,

  input logic unsigned [22:0] mul_opa,

  input logic unsigned [22:0] mul_opb,

  // States
  input logic INIT,
  input logic PWA_PWS,
  input logic CT,
  input logic GS,
  input logic PWM_ACC,
  input logic PWM_NOT_ACC
);


default clocking default_clk @(posedge clk); endclocking


logic unsigned [22:0] compute_u_0_i;
assign compute_u_0_i = compute_u(opu_i, opv_i, opw_i, mode, accumulate);

logic unsigned [22:0] compute_v_0_i;
assign compute_v_0_i = compute_v(opu_i, opv_i, opw_i, mode);

logic unsigned [22:0] compute_pwm_0_i;
assign compute_pwm_0_i = compute_pwm(opu_i, opv_i, opw_i, mode, accumulate);

logic unsigned [22:0] compute_a_min_b_0_i;
assign compute_a_min_b_0_i = compute_a_min_b(opu_i, opv_i);

logic unsigned [22:0] div2_0_i;
assign div2_0_i = div2(compute_a_min_b_0_i);


sequence reset_sequence;
  !rst_n ##1 rst_n;
endsequence

//Reset property
property run_reset_p;
  $past(!rst_n) |->
  INIT &&
  add_res_d1 == 23'd0 &&
  add_res_d2 == 23'd0 &&
  pwm_res_o == 23'd0 &&
  u_o == 23'd0 &&
  u_reg == 23'd0 &&
  u_reg_d2 == 23'd0 &&
  u_reg_d3 == 23'd0 &&
  u_reg_d4 == 23'd0 &&
  v_o == 23'd0 &&
  w_reg == 23'd0 &&
  w_reg_d2 == 23'd0 &&
  w_reg_d3 == 23'd0 &&
  w_reg_d4 == 23'd0;
endproperty
run_reset_a: assert property (run_reset_p);

//Property to check the outputs and registers of ntt_butterfly module in CT mode
property run_INIT_to_CT_p;
  INIT &&
  (mode <= 64'd2) &&
  (mode == 3'd0)
|->
  ##1 
  u_reg == $past(opu_i, 1) &&
  w_reg == $past(opw_i, 1) &&
  add_res_d1 == $past(add_res, 1)
  ##1
  u_reg_d2 == $past(opu_i, 2) &&
  w_reg_d2 == $past(opw_i, 2) &&
  add_res_d2 == $past(add_res, 2)
  ##1
  u_reg_d3 == $past(opu_i, 3) &&
  w_reg_d3 == $past(opw_i, 3)
  ##1
  u_reg_d4 == $past(opu_i, 4) &&
  w_reg_d4 == $past(opw_i, 4)
  ##1
  CT &&
  mul_opa == opv_i &&
  mul_opb == opw_i &&
  pwm_res_o == $past(compute_pwm_0_i, 5) &&
  u_o == $past(compute_u_0_i, 5) &&
  v_o == $past(compute_v_0_i, 5);
endproperty
run_INIT_to_CT_a: assert property (disable iff(!rst_n) run_INIT_to_CT_p);


//Property to check the outputs and registers of ntt_butterfly module in GS mode
property run_INIT_to_GS_p;
  INIT &&
  (mode != 3'd2) &&
  (mode <= 64'd2) &&
  (mode != 3'd0)
|->
  ##1 
  u_reg == $past(opu_i, 1) &&
  w_reg == $past(opw_i, 1) &&
  add_res_d1 == $past(add_res, 1)
  ##1
  u_reg_d2 == $past(opu_i, 2) &&
  w_reg_d2 == $past(opw_i, 2) &&
  add_res_d2 == $past(add_res, 2)
  ##1
  u_reg_d3 == $past(opu_i, 3) &&
  w_reg_d3 == $past(opw_i, 3)
  ##1
  u_reg_d4 == $past(opu_i, 4) &&
  w_reg_d4 == $past(opw_i, 4)
  ##1
  GS &&
  mul_opa == $past(div2_0_i, 1) &&
  mul_opb == $past(opw_i, 1) &&
  pwm_res_o == $past(compute_pwm_0_i, 5) &&
  u_o == $past(compute_u_0_i, 5) &&
  v_o == $past(compute_v_0_i, 5);
endproperty
run_INIT_to_GS_a: assert property (disable iff(!rst_n) run_INIT_to_GS_p);

//Property to check the outputs and registers of ntt_butterfly module in PWA & PWS mode
property run_INIT_to_PWA_PWS_p;
  INIT &&
  (mode != 3'd2) &&
  (mode > 64'd2)
|->
  ##1
  PWA_PWS &&
  mul_opa == 23'd0 &&
  mul_opb == 23'd0 &&
  pwm_res_o == $past(compute_pwm_0_i, 1) &&
  //u_o == $past(compute_u_0_i, 1) &&
  //v_o == $past(compute_v_0_i, 1);
  u_o == 23'd0 &&
  v_o == 23'd0;
endproperty
run_INIT_to_PWA_PWS_a: assert property (disable iff(!rst_n) run_INIT_to_PWA_PWS_p);


//Property to check the outputs and registers of ntt_butterfly module in PWM Accumulate mode
property run_INIT_to_PWM_ACC_p;
  INIT &&
  (mode == 3'd2) &&
  (accumulate != 1'd0)
|->
  ##1 
  u_reg == $past(opu_i, 1) &&
  w_reg == $past(opw_i, 1) &&
  add_res_d1 == $past(add_res, 1)
  ##1
  u_reg_d2 == $past(opu_i, 2) &&
  w_reg_d2 == $past(opw_i, 2) &&
  add_res_d2 == $past(add_res, 2)
  ##1
  u_reg_d3 == $past(opu_i, 3) &&
  w_reg_d3 == $past(opw_i, 3)
  ##1
  u_reg_d4 == $past(opu_i, 4) &&
  w_reg_d4 == $past(opw_i, 4)
  ##1
  PWM_ACC &&
  mul_opa == opu_i &&
  mul_opb == opv_i &&
  pwm_res_o == $past(compute_pwm_0_i, 5) &&
  //u_o == $past(compute_u_0_i, 5) &&
  //v_o == $past(compute_v_0_i, 5);
  u_o == 23'd0 &&
  v_o == 23'd0;
endproperty
run_INIT_to_PWM_ACC_a: assert property (disable iff(!rst_n) run_INIT_to_PWM_ACC_p);


//Property to check the outputs and registers of ntt_butterfly module in PWM not accumulate mode
property run_INIT_to_PWM_NOT_ACC_p;
  INIT &&
  (mode == 3'd2) &&
  (accumulate == 1'd0)
|->
  ##1 
  u_reg == $past(opu_i, 1) &&
  w_reg == $past(opw_i, 1) &&
  add_res_d1 == $past(add_res, 1)
  ##1
  u_reg_d2 == $past(opu_i, 2) &&
  w_reg_d2 == $past(opw_i, 2) &&
  add_res_d2 == $past(add_res, 2)
  ##1
  u_reg_d3 == $past(opu_i, 3) &&
  w_reg_d3 == $past(opw_i, 3)
  ##1
  PWM_NOT_ACC &&
  mul_opa == opu_i &&
  mul_opb == opv_i &&
  pwm_res_o == $past(compute_pwm_0_i, 4) &&
  //u_o == $past(compute_u_0_i, 4) &&
  //v_o == $past(compute_v_0_i, 4) &&
  u_o == 23'd0 &&
  v_o == 23'd0 &&
  u_reg_d4 == $past(opu_i, 4) &&
  w_reg_d4 == $past(opw_i, 4);
endproperty
run_INIT_to_PWM_NOT_ACC_a: assert property (disable iff(!rst_n) run_INIT_to_PWM_NOT_ACC_p);


endmodule
