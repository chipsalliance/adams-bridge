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


import ntt_defines_pkg::*;
import fv_ntt_butterfly_functions::*;


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

  input logic unsigned [0:0] mlkem,

  input logic unsigned [22:0] pairwm_mul_red_o,

  // Internal multiplication pipeline
  input logic unsigned [45:0] mul_res,
  input logic unsigned [23:0] mul_res_reg,
  input logic unsigned [45:0] mldsa_mul_res_reg,
  input logic unsigned [11:0] mlkem_mul_res_reduced,
  input logic unsigned [22:0] mldsa_mul_res_reduced_comb,
  input logic unsigned [11:0] mlkem_mul_res_reduced_reg,
  input logic unsigned [22:0] mldsa_mul_res_reduced,

  // Internal adder/subtracter signals
  input logic unsigned [22:0] add_opa,
  input logic unsigned [22:0] add_opb,
  input logic unsigned [22:0] sub_res,
  input logic unsigned [22:0] u_minus_v,

  // States
  input logic INIT,
  input logic PWA_PWS,
  input logic CT,
  input logic GS,
  input logic PWM_ACC,
  input logic PWM_NOT_ACC,

  // Barrett reduction internals — mldsa_mul_redux_inst_0 (REG_SIZE=23, prime=8380417)
  // K=46, m=floor(2^46/8380417)=8396806
  input logic unsigned [69:0] mldsa_mult_full,      // x * m  (3*23+1 bits)
  input logic unsigned [23:0] mldsa_u_est,           // mult_full >> 46
  input logic unsigned [46:0] mldsa_u_prime,         // u_est * prime
  input logic unsigned [46:0] mldsa_r_est,           // {0,x} - u_prime
  input logic unsigned [46:0] mldsa_r_sub_prime,     // r_est - prime
  input logic unsigned [23:0] mldsa_u_plus_one,      // u_est + 1
  input logic                 mldsa_additional_red,  // r_est >= prime

  // Barrett reduction internals — mlkem_mul_redux_inst_0 (REG_SIZE=12, prime=3329)
  // K=24, m=floor(2^24/3329)=5039
  input logic unsigned [36:0] mlkem_mult_full,       // x * m  (3*12+1 bits)
  input logic unsigned [12:0] mlkem_u_est,           // mult_full >> 24
  input logic unsigned [24:0] mlkem_u_prime,         // u_est * prime
  input logic unsigned [24:0] mlkem_r_est,           // {0,x} - u_prime
  input logic unsigned [24:0] mlkem_r_sub_prime,     // r_est - prime
  input logic unsigned [12:0] mlkem_u_plus_one,      // u_est + 1
  input logic                 mlkem_additional_red   // r_est >= prime
);


default clocking default_clk @(posedge clk); endclocking


logic unsigned [22:0] fv_compute_u_0_i;
assign fv_compute_u_0_i = compute_u(opu_i, opv_i, opw_i, mode, accumulate, mlkem);

logic unsigned [22:0] fv_compute_v_0_i;
assign fv_compute_v_0_i = compute_v(opu_i, opv_i, opw_i, mode, mlkem);

logic unsigned [22:0] fv_compute_pwm_0_i;
assign fv_compute_pwm_0_i = compute_pwm(opu_i, opv_i, opw_i, mode, accumulate, mlkem);

logic unsigned [22:0] fv_compute_a_min_b_0_i;
assign fv_compute_a_min_b_0_i = compute_a_min_b(opu_i, opv_i, mlkem);

logic unsigned [22:0] fv_div2_0_i;
assign fv_div2_0_i = div2(fv_compute_a_min_b_0_i, mlkem);

logic unsigned [22:0] fv_compute_pairwm_0_i;
assign fv_compute_pairwm_0_i = 23'((opu_i * opv_i) % 64'd3329);


sequence reset_sequence;
  !rst_n ##1 rst_n;
endsequence

//Reset property
property run_reset_p;
  $past(!rst_n)
|->
  INIT &&
  add_res_d1 == 23'd0 &&
  add_res_d2 == 23'd0 &&
  pwm_res_o == 23'd0 &&
  u_o == 23'd0 &&
  u_reg == 23'd0 &&
  u_reg_d2 == 23'd0 &&
  v_o == 23'd0 &&
  w_reg == 23'd0 &&
  w_reg_d2 == 23'd0;
endproperty
a_run_reset: assert property (run_reset_p);

//Property to check the outputs and registers of ntt_butterfly module in CT mode
property run_INIT_to_CT_p;
  INIT &&
  (mode <= 64'd2) &&
  (mode == 3'd0)
|->
  ##1
  mul_opa == opv_i &&
  mul_opb == opw_i &&
  u_reg == $past(opu_i, 1) &&
  w_reg == $past(opw_i, 1) &&
  add_res_d1 == $past(add_res, 1)
  ##1
  u_reg_d2 == $past(opu_i, 2) &&
  w_reg_d2 == $past(opw_i, 2) &&
  add_res_d2 == $past(add_res, 2)
  ##1
  CT &&
  pwm_res_o == 23'd0 &&
  u_o == $past(fv_compute_u_0_i, 3) &&
  v_o == $past(fv_compute_v_0_i, 3);
endproperty
a_run_init_to_ct: assert property (disable iff(!rst_n) run_INIT_to_CT_p);


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
  mul_opa == $past(fv_div2_0_i, 1) &&
  mul_opb == $past(opw_i, 1) &&
  u_reg_d2 == $past(opu_i, 2) &&
  w_reg_d2 == $past(opw_i, 2) &&
  add_res_d2 == $past(add_res, 2)
  ##1
  GS &&
  pwm_res_o == 23'd0 &&
  pairwm_mul_red_o == 23'd0 &&
  u_o == $past(fv_compute_u_0_i, 3) &&
  v_o == $past(fv_compute_v_0_i, 3);
endproperty
a_run_init_to_gs: assert property (disable iff(!rst_n) run_INIT_to_GS_p);

//Property to check the outputs and registers of ntt_butterfly module in PWA & PWS mode
property run_INIT_to_PWA_PWS_p;
  INIT &&
  (mode == 3'd3 || mode == 3'd4)
|->
  ##1
  PWA_PWS &&
  mul_opa == 23'd0 &&
  mul_opb == 23'd0 &&
  pairwm_mul_red_o == 23'd0 &&
  pwm_res_o == $past(fv_compute_pwm_0_i, 1) &&
  //u_o == $past(fv_compute_u_0_i, 1) &&
  //v_o == $past(fv_compute_v_0_i, 1);
  u_o == 23'd0 &&
  v_o == 23'd0;
endproperty
a_run_init_to_pwa_pws: assert property (disable iff(!rst_n) run_INIT_to_PWA_PWS_p);


//Property to check the outputs and multiplier inputs of ntt_butterfly module in PAIRWM mode (MLKEM only)
//pairwm_mul_red_o has 2-cycle latency: mul_res -> registered -> barrett (comb) -> registered
property run_INIT_to_PAIRWM_p;
  INIT &&
  (mode == 3'd5) &&
  mlkem
|->
  ##1
  mul_opa == opu_i &&
  mul_opb == opv_i
  ##1
  pairwm_mul_red_o == $past(fv_compute_pairwm_0_i, 2) &&
  u_o == 23'd0 &&
  v_o == 23'd0&&
  pwm_res_o==23'd0;
endproperty
a_run_init_to_pairwm: assert property (disable iff(!rst_n) run_INIT_to_PAIRWM_p);


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
  PWM_ACC &&
  mul_opa == opu_i &&
  mul_opb == opv_i &&
  pwm_res_o == $past(fv_compute_pwm_0_i, 3) &&
  pairwm_mul_red_o == 23'd0 &&
  u_o == 23'd0 &&
  v_o == 23'd0;
endproperty
a_run_init_to_pwm_acc: assert property (disable iff(!rst_n) run_INIT_to_PWM_ACC_p);


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
  &&
  PWM_NOT_ACC &&
  mul_opa == opu_i &&
  mul_opb == opv_i &&
  pwm_res_o == $past(fv_compute_pwm_0_i, 2) &&
  pairwm_mul_red_o == 23'd0 &&
  u_o == 23'd0 &&
  v_o == 23'd0;
endproperty
a_run_init_to_pwm_not_acc: assert property (disable iff(!rst_n) run_INIT_to_PWM_NOT_ACC_p);


// =====================================================================
// Whitebox: multiplication pipeline
// =====================================================================

// DSP always computes the product of its two operands (combinational)
property mul_res_product_p;
    mul_res == 46'(mul_opa) * 46'(mul_opb);
endproperty
a_mul_res_product: assert property (mul_res_product_p);

// mul_res_reg captures the low 24 bits (2*MLKEM_REG_SIZE) of mul_res each cycle
property mul_res_reg_p;
    ##1 mul_res_reg == 24'($past(mul_res, 1));
endproperty
a_mul_res_reg: assert property (disable iff(!rst_n) mul_res_reg_p);

// mldsa_mul_res_reg captures the full 46-bit product when !mlkem, else 0
property mldsa_mul_res_reg_p;
  !mlkem
|->
  ##1 mldsa_mul_res_reg == 46'($past(mul_res, 1));
endproperty
a_mldsa_mul_res_reg: assert property (disable iff(!rst_n) mldsa_mul_res_reg_p);

property mldsa_mul_res_reg_zero_p;
  mlkem
|->
  ##1 mldsa_mul_res_reg == 46'd0;
endproperty
a_mldsa_mul_res_reg_zero: assert property (disable iff(!rst_n) mldsa_mul_res_reg_zero_p);

// MLKEM barrett output is always in range [0, MLKEM_Q)
property mlkem_mul_reduced_range_p;
    mlkem_mul_res_reduced < 12'd3329;
endproperty
a_mlkem_mul_reduced_range: assert property (mlkem_mul_reduced_range_p);

// MLDSA combinational barrett output is always in range [0, MLDSA_Q)
property mldsa_mul_reduced_comb_range_p;
    mldsa_mul_res_reduced_comb < 23'd8380417;
endproperty
a_mldsa_mul_reduced_comb_range: assert property (mldsa_mul_reduced_comb_range_p);

// MLKEM: mlkem_mul_res_reduced_reg captures the combinational reduced value each cycle
property mlkem_mul_res_reduced_reg_p;
  mlkem
|->
  ##1 mlkem_mul_res_reduced_reg == 12'($past(mlkem_mul_res_reduced, 1));
endproperty
a_mlkem_mul_res_reduced_reg: assert property (disable iff(!rst_n) mlkem_mul_res_reduced_reg_p);

// MLDSA: mldsa_mul_res_reduced captures the combinational barrett output each cycle
property mldsa_mul_res_reduced_reg_p;
  !mlkem
|->
  ##1 mldsa_mul_res_reduced == $past(mldsa_mul_res_reduced_comb, 1);
endproperty
a_mldsa_mul_res_reduced_reg: assert property (disable iff(!rst_n) mldsa_mul_res_reduced_reg_p);

// Whitebox: mul_res reduction result flows into u_o via the adder in CT mode.
// CT: add_opa = u_reg_d2, add_opb = mlkem_mul_res_reduced_reg (MLKEM) or
//     mldsa_mul_res_reduced (MLDSA); u_o = add_res = (add_opa + add_opb) % Q.
// These checks close the final link in the chain:
//   mul_res -> mul_res_reg -> reduced -> reduced_reg -> add_opb -> u_o

property mul_res_to_u_o_ct_mlkem_p;
  CT && mlkem
|=>
  u_o == 23'(($past(u_reg_d2) + 23'($past(mlkem_mul_res_reduced_reg))) % 64'd3329);
endproperty
a_mul_res_to_u_o_ct_mlkem: assert property (mul_res_to_u_o_ct_mlkem_p);

property mul_res_to_u_o_ct_mldsa_p;
  CT && !mlkem
|=>
  u_o == 23'(($past(u_reg_d2) + $past(mldsa_mul_res_reduced)) % 64'd8380417);
endproperty
a_mul_res_to_u_o_ct_mldsa: assert property (mul_res_to_u_o_ct_mldsa_p);


// =====================================================================
// Whitebox: add_res correctness (add_inst_0: add_res = (add_opa + add_opb) % Q)
// =====================================================================

// Generic check: holds for every mode because add_opa/add_opb are always
// driven to the correct mode-specific values before add_inst_0 computes.
property add_res_correct_p;
    ##1 add_res == 23'((64'($past(add_opa)) + 64'($past(add_opb))) % (mlkem ? 64'd3329 : 64'd8380417));
endproperty
a_add_res_correct: assert property (add_res_correct_p);

// sub_inst_1 is hardwired (not mode-muxed): opa=u_reg_d2, opb=reduced mul result.
// Written as (u_reg_d2 + Q - opb) % Q to stay unsigned across both primes.
property sub_res_correct_p;
    ##1 sub_res == 23'((64'($past(u_reg_d2)) + (mlkem ? 64'd3329 : 64'd8380417) -
        (mlkem ? 64'($past(mlkem_mul_res_reduced_reg)) : 64'($past(mldsa_mul_res_reduced)))) %
        (mlkem ? 64'd3329 : 64'd8380417));
endproperty
a_sub_res_correct: assert property (sub_res_correct_p);

property add_Res_range_p;
  mlkem
|=>
  add_res < 12'd3329;
endproperty
a_add_res_range: assert property (add_Res_range_p);

// MLDSA combinational barrett output is always in range [0, MLDSA_Q)
property u_minus_v_range_p;
    u_minus_v < 23'd8380417;
endproperty
a_u_minus_v_range: assert property (u_minus_v_range_p);


// =====================================================================
// Whitebox: u_minus_v (sub_inst_0: u_minus_v = (opu_i - opv_i) % Q)
// =====================================================================

// Mathematical correctness: modular subtraction of primary inputs
// Expressed as (a + Q - b) % Q to stay unsigned across both primes.
property u_minus_v_correct_mlkem_p;
  mlkem
|=>
  u_minus_v == 23'((64'($past(opu_i)) + 64'd3329 - 64'($past(opv_i))) % 64'd3329);
endproperty
a_u_minus_v_correct_mlkem: assert property (u_minus_v_correct_mlkem_p);

property u_minus_v_correct_mldsa_p;
  !mlkem
|=>
  u_minus_v == 23'((64'(opu_i) + 64'd8380417 - 64'(opv_i)) % 64'd8380417);
endproperty
//u_minus_v_correct_mldsa_a: assert property (u_minus_v_correct_mldsa_p);


// =====================================================================
// Output range checks: all primary outputs must stay in [0, Q)
// =====================================================================

// u_o
property u_o_range_mlkem_p;
  mlkem
|=>
  u_o < 23'd3329;
endproperty
a_u_o_range_mlkem: assert property (u_o_range_mlkem_p);

property u_o_range_mldsa_p;
  !mlkem
|=>
  u_o < 23'd8380417;
endproperty
a_u_o_range_mldsa: assert property (u_o_range_mldsa_p);

// v_o
property v_o_range_mlkem_p;
  mlkem
|=>
  v_o < 23'd3329;
endproperty
a_v_o_range_mlkem: assert property (v_o_range_mlkem_p);

property v_o_range_mldsa_p;
  !mlkem
|=>
  v_o < 23'd8380417;
endproperty
a_v_o_range_mldsa: assert property (v_o_range_mldsa_p);

// pwm_res_o
property pwm_res_o_range_mlkem_p;
  mlkem
|=>
  pwm_res_o < 23'd3329;
endproperty
a_pwm_res_o_range_mlkem: assert property (pwm_res_o_range_mlkem_p);

property pwm_res_o_range_mldsa_p;
  !mlkem
|=>
  pwm_res_o < 23'd8380417;
endproperty
a_pwm_res_o_range_mldsa: assert property (pwm_res_o_range_mldsa_p);

// pairwm_mul_red_o — MLKEM only, driven to 0 otherwise
property pairwm_mul_red_o_range_mlkem_p;
  mlkem
|=>
  pairwm_mul_red_o < 23'd3329;
endproperty
a_pairwm_mul_red_o_range_mlkem: assert property (pairwm_mul_red_o_range_mlkem_p);



// =====================================================================
// Whitebox: MLDSA barrett reduction (mldsa_mul_redux_inst_0)
// Parameters: REG_SIZE=23, prime=8380417, K=46, m=8396806
// Pipeline is purely combinational; all checks are same-cycle.
// =====================================================================

// Step 1: mult_full = mldsa_mul_res_reg * m
property mldsa_mult_full_p;
    mldsa_mult_full == 70'(mldsa_mul_res_reg) * 70'd8396807;
endproperty
a_mldsa_mult_full: assert property (mldsa_mult_full_p);

property mldsa_u_est_p;
    mldsa_u_est == 24'(mldsa_mult_full >> 46);
endproperty
a_mldsa_u_est: assert property (mldsa_u_est_p);

// Step 3: u_prime = u_est * prime
property mldsa_u_prime_p;
    mldsa_u_prime == 47'(mldsa_u_est) * 47'd8380417;
endproperty
a_mldsa_u_prime: assert property (mldsa_u_prime_p);

// Step 4: r_est = {0,x} - u_prime  (x = mldsa_mul_res_reg)
property mldsa_r_est_p;
    mldsa_r_est == {1'b0, mldsa_mul_res_reg} - mldsa_u_prime;
endproperty
a_mldsa_r_est: assert property (mldsa_r_est_p);

// Step 5a: r_sub_prime = r_est - prime  (candidate after additional reduction)
property mldsa_r_sub_prime_p;
    mldsa_r_sub_prime == mldsa_r_est - 47'd8380417;
endproperty
a_mldsa_r_sub_prime: assert property (mldsa_r_sub_prime_p);

// Step 5b: u_plus_one = u_est + 1
property mldsa_u_plus_one_p;
    mldsa_u_plus_one == mldsa_u_est + 24'd1;
endproperty
a_mldsa_u_plus_one: assert property (mldsa_u_plus_one_p);

// Step 6: additional_reduction flag
property mldsa_additional_red_p;
    mldsa_additional_red == (mldsa_r_est >= 47'd8380417);
endproperty
a_mldsa_additional_red: assert property (mldsa_additional_red_p);

// Step 7: output mux — mldsa_mul_res_reduced_comb
property mldsa_reduced_comb_mux_p;
    mldsa_mul_res_reduced_comb ==
        (mldsa_additional_red ? mldsa_r_sub_prime[22:0] : mldsa_r_est[22:0]);
endproperty
a_mldsa_reduced_comb_mux: assert property (mldsa_reduced_comb_mux_p);


// =====================================================================
// Whitebox: MLKEM barrett reduction (mlkem_mul_redux_inst_0)
// Parameters: REG_SIZE=12, prime=3329, K=24, m=5039
// Input x = mlkem ? mul_res_reg : 0  (gated at the instantiation site)
// =====================================================================

// Step 1: mult_full = x * m
property mlkem_mult_full_p;
    mlkem_mult_full == 37'(mlkem ? mul_res_reg : 24'd0) * 37'd5039;
endproperty
a_mlkem_mult_full: assert property (mlkem_mult_full_p);

// Step 2: u_est = mult_full >> K  (K=24)
property mlkem_u_est_p;
    mlkem_u_est == 13'(mlkem_mult_full >> 24);
endproperty
a_mlkem_u_est: assert property (mlkem_u_est_p);

// Step 3: u_prime = u_est * prime
property mlkem_u_prime_p;
    mlkem_u_prime == 25'(mlkem_u_est) * 25'd3329;
endproperty
a_mlkem_u_prime: assert property (mlkem_u_prime_p);

// Step 4: r_est = {0,x} - u_prime  (x gated by mlkem)
property mlkem_r_est_p;
    mlkem_r_est == {1'b0, mlkem ? mul_res_reg : 24'd0} - mlkem_u_prime;
endproperty
a_mlkem_r_est: assert property (mlkem_r_est_p);

// Step 5a: r_sub_prime = r_est - prime
property mlkem_r_sub_prime_p;
    mlkem_r_sub_prime == mlkem_r_est - 25'd3329;
endproperty
a_mlkem_r_sub_prime: assert property (mlkem_r_sub_prime_p);

// Step 5b: u_plus_one = u_est + 1
property mlkem_u_plus_one_p;
    mlkem_u_plus_one == mlkem_u_est + 13'd1;
endproperty
a_mlkem_u_plus_one: assert property (mlkem_u_plus_one_p);

// Step 6: additional_reduction flag
property mlkem_additional_red_p;
    mlkem_additional_red == (mlkem_r_est >= 25'd3329);
endproperty
a_mlkem_additional_red: assert property (mlkem_additional_red_p);

// Step 7: output mux — mlkem_mul_res_reduced
property mlkem_reduced_mux_p;
    mlkem_mul_res_reduced ==
        (mlkem_additional_red ? mlkem_r_sub_prime[11:0] : mlkem_r_est[11:0]);
endproperty
a_mlkem_reduced_mux: assert property (mlkem_reduced_mux_p);


endmodule
