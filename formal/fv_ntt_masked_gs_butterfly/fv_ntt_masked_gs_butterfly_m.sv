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
// | Created on 12.05.2025 at 19:55                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import fv_ntt_masked_gs_butterfly_pkg::*;
import ntt_defines_pkg::*;
import fv_ntt_masked_gs_butterfly_pkg::*;
import fv_ntt_masked_gs_butterfly_functions::*;


module fv_ntt_masked_gs_butterfly_m(
  input logic rst_n,
  input logic clk,

  // Ports
  input a_unsigned_46_2 u,

  input a_unsigned_46_2 v,

  input a_unsigned_46_2 w,

  input logic unsigned [2:0] mode,

  input logic unsigned [0:0] accumulate,

  input logic unsigned [45:0] u_0,

  input logic unsigned [45:0] v_0,

  // States
  input logic INIT,
  input logic PWMA,
  input logic PWM,
  input logic NON_PWM
);


default clocking default_clk @(posedge clk); endclocking


logic unsigned [45:0] compute_u_0_i;
assign compute_u_0_i = compute_u(u, v, w, mode, accumulate);

logic unsigned [45:0] compute_v_0_i;
assign compute_v_0_i = compute_v(u, v, w, mode);


sequence reset_sequence;
  !rst_n ##1 rst_n;
endsequence

//Reset property
property run_reset_p;
  $past(!rst_n || ntt_masked_gs_butterfly.zeroize)  |->
  INIT &&
  u_0 == 46'd0 &&
  v_0 == 46'd0;
endproperty
run_reset_a: assert property (run_reset_p);

//Property to check GS butterfly output when mode is not PWM
property run_INIT_to_NON_PWM_p;
  INIT &&
  (mode != 3'd2)
|->
  ##264
  NON_PWM &&
  u_0 == $past(compute_u_0_i, 264) &&
  v_0 == $past(compute_v_0_i, 264);
endproperty
run_INIT_to_NON_PWM_a: assert property (disable iff(!rst_n) run_INIT_to_NON_PWM_p);

//Property to check GS butterfly output when mode is PWM but not ACC
property run_INIT_to_PWM_p;
  INIT &&
  (mode == 3'd2) &&
  (accumulate == 1'd0)
|->
  ##210
  PWM &&
  u_0 == $past(compute_u_0_i, 210) &&
  v_0 == 46'd0;
endproperty
run_INIT_to_PWM_a: assert property (disable iff(!rst_n) run_INIT_to_PWM_p);

//Property to check GS butterfly output when mode is PWM and ACC
property run_INIT_to_PWMA_p;
  INIT &&
  (mode == 3'd2) &&
  (accumulate != 1'd0)
|->
  ##264
  PWMA &&
  u_0 == ($past(((u[0] + u[1]) * (v[0] + v[1])) % 'h7FE001, 264) + $past((w[0] + w[1]), 53)) % 'h7FE001 &&
  v_0 == 46'd0;
endproperty
run_INIT_to_PWMA_a: assert property (disable iff(!rst_n) run_INIT_to_PWMA_p);


endmodule
