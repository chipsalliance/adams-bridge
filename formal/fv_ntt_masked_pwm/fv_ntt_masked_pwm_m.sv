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
// | Created on 06.02.2025 at 15:23                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import fv_ntt_masked_pwm_pkg::*;
import fv_ntt_masked_pwm_pkg::*;
import ntt_defines_pkg::*;
import fv_ntt_masked_pwm_functions::*;


module fv_ntt_masked_pwm_m(
  input logic rst_n,
  input logic clk,

  // Ports
  input a_unsigned_46_2 u,

  input a_unsigned_46_2 v,

  input a_unsigned_46_2 w,

  input logic unsigned [0:0] accumulate,

  input logic unsigned [45:0] res_sum,

  // States
  input logic INIT,
  input logic PWMA,
  input logic PWM
);


default clocking default_clk @(posedge clk); endclocking


logic unsigned [45:0] compute_pwm_0_i;
assign compute_pwm_0_i = compute_pwm(u, v, w, accumulate);


sequence reset_sequence;
  !rst_n ##1 rst_n;
endsequence

//Reset property
property run_reset_p;
  $past(!rst_n || ntt_masked_pwm.zeroize)  |->
  INIT &&
  res_sum == 46'd0;
endproperty
run_reset_a: assert property (run_reset_p);

//Property to check the output of ntt_masked_pwm (not accumulate mode)
property run_INIT_to_PWM_p;
  INIT &&
  (accumulate == 1'd0)
|->
  ##210
  PWM &&
  res_sum == $past(compute_pwm_0_i, 210);
endproperty
run_INIT_to_PWM_a: assert property (disable iff(!rst_n) run_INIT_to_PWM_p);

//Property to check the output of ntt_masked_pwm (accumulate mode)
property run_INIT_to_PWMA_p;
  INIT &&
  (accumulate != 1'd0)
|->
  ##264
  PWMA &&
  res_sum == ($past(((u[0] + u[1]) * (v[0] + v[1])) % 'h7FE001, 264) + $past((w[0] + w[1]), 53)) % 'h7FE001;
endproperty
run_INIT_to_PWMA_a: assert property (disable iff(!rst_n) run_INIT_to_PWMA_p);



endmodule
