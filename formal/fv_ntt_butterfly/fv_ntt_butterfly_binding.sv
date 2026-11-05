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


bind ntt_butterfly fv_ntt_butterfly_m fv_ntt_butterfly(
  .rst_n(ntt_butterfly.reset_n && !ntt_butterfly.zeroize),
  .clk(ntt_butterfly.clk),

  // Ports
  .accumulate(ntt_butterfly.accumulate),

  .add_res(ntt_butterfly.add_res),

  .mode(ntt_butterfly.mode),

  .opu_i(ntt_butterfly.opu_i),

  .opv_i(ntt_butterfly.opv_i),

  .opw_i(ntt_butterfly.opw_i),

  .add_res_d1(ntt_butterfly.add_res_d1),

  .add_res_d2(ntt_butterfly.add_res_d2),

  .mul_opa(ntt_butterfly.mul_opa),

  .mul_opb(ntt_butterfly.mul_opb),

  .mlkem(ntt_butterfly.mlkem),

  .pairwm_mul_red_o(ntt_butterfly.pairwm_mul_red_o),

  .pwm_res_o(ntt_butterfly.pwm_res_o),

  .u_o(ntt_butterfly.u_o),

  .u_reg(ntt_butterfly.u_reg),

  .u_reg_d2(ntt_butterfly.u_reg_d2),

  //.u_reg_d3(ntt_butterfly.u_reg_d3),

 // .u_reg_d4(ntt_butterfly.u_reg_d4),

  .v_o(ntt_butterfly.v_o),

  .w_reg(ntt_butterfly.w_reg),

  .w_reg_d2(ntt_butterfly.w_reg_d2),

 // .w_reg_d3(ntt_butterfly.w_reg_d3),

  //.w_reg_d4(ntt_butterfly.w_reg_d4),

  // Internal adder/subtracter signals
  .add_opa(ntt_butterfly.add_opa),
  .add_opb(ntt_butterfly.add_opb),
  .sub_res(ntt_butterfly.sub_res),
  .u_minus_v(ntt_butterfly.u_minus_v),

  // Internal multiplication pipeline
  .mul_res(ntt_butterfly.mul_res),
  .mul_res_reg(ntt_butterfly.mul_res_reg),
  .mldsa_mul_res_reg(ntt_butterfly.mldsa_mul_res_reg),
  .mlkem_mul_res_reduced(ntt_butterfly.mlkem_mul_res_reduced),
  .mldsa_mul_res_reduced_comb(ntt_butterfly.mldsa_mul_res_reduced_comb),
  .mlkem_mul_res_reduced_reg(ntt_butterfly.mlkem_mul_res_reduced_reg),
  .mldsa_mul_res_reduced(ntt_butterfly.mldsa_mul_res_reduced),

  // States
  .CT(ntt_butterfly.mode  == 'd0),
  .GS(ntt_butterfly.mode  == 'd1),
  .INIT(1'b1),
  .PWA_PWS(ntt_butterfly.mode > 'd2),
  .PWM_ACC((ntt_butterfly.mode  == 'd2) && (ntt_butterfly.accumulate)),
  .PWM_NOT_ACC((ntt_butterfly.mode  == 'd2) && (!ntt_butterfly.accumulate)),

  // Barrett internals — mldsa_mul_redux_inst_0
  .mldsa_mult_full      (ntt_butterfly.mldsa_mul_redux_inst_0.mult_full),
  .mldsa_u_est          (ntt_butterfly.mldsa_mul_redux_inst_0.u_est),
  .mldsa_u_prime        (ntt_butterfly.mldsa_mul_redux_inst_0.u_prime),
  .mldsa_r_est          (ntt_butterfly.mldsa_mul_redux_inst_0.r_est),
  .mldsa_r_sub_prime    (ntt_butterfly.mldsa_mul_redux_inst_0.r_sub_prime),
  .mldsa_u_plus_one     (ntt_butterfly.mldsa_mul_redux_inst_0.u_plus_one),
  .mldsa_additional_red (ntt_butterfly.mldsa_mul_redux_inst_0.additional_reduction),

  // Barrett internals — mlkem_mul_redux_inst_0
  .mlkem_mult_full      (ntt_butterfly.mlkem_mul_redux_inst_0.mult_full),
  .mlkem_u_est          (ntt_butterfly.mlkem_mul_redux_inst_0.u_est),
  .mlkem_u_prime        (ntt_butterfly.mlkem_mul_redux_inst_0.u_prime),
  .mlkem_r_est          (ntt_butterfly.mlkem_mul_redux_inst_0.r_est),
  .mlkem_r_sub_prime    (ntt_butterfly.mlkem_mul_redux_inst_0.r_sub_prime),
  .mlkem_u_plus_one     (ntt_butterfly.mlkem_mul_redux_inst_0.u_plus_one),
  .mlkem_additional_red (ntt_butterfly.mlkem_mul_redux_inst_0.additional_reduction)
);
