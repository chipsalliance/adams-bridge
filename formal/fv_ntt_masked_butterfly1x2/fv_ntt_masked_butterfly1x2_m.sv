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
// | Created on 06.02.2025 at 13:51                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import fv_ntt_masked_butterfly1x2_pkg::*;
import ntt_defines_pkg::*;
import fv_ntt_masked_butterfly1x2_pkg::*;
import fv_ntt_masked_butterfly1x2_functions::*;


module fv_ntt_masked_butterfly1x2_m(
  input logic rst_n,
  input logic clk,

  // Ports
  input a_unsigned_46_2 u00,

  input a_unsigned_46_2 v00,

  input a_unsigned_46_2 w00,

  input a_unsigned_46_2 u01,

  input a_unsigned_46_2 v01,

  input a_unsigned_46_2 w01,

  input logic unsigned [22:0] uv_0_u20,

  input logic unsigned [22:0] uv_0_u21,

  input logic unsigned [22:0] uv_0_v20,

  input logic unsigned [22:0] uv_0_v21,

  // States
  input logic COMPUTE
);


default clocking default_clk @(posedge clk); endclocking


logic unsigned [22:0] compute_u_0_i;
assign compute_u_0_i = compute_u(u00, v00);

logic unsigned [22:0] div2_0_i;
assign div2_0_i = div2(compute_u_0_i);

logic unsigned [22:0] compute_v_0_i;
assign compute_v_0_i = compute_v(u00, v00, w00);

logic unsigned [22:0] div2_1_i;
assign div2_1_i = div2(compute_v_0_i);

logic unsigned [22:0] compute_u_1_i;
assign compute_u_1_i = compute_u(u01, v01);

logic unsigned [22:0] div2_2_i;
assign div2_2_i = div2(compute_u_1_i);

logic unsigned [22:0] compute_v_1_i;
assign compute_v_1_i = compute_v(u01, v01, w01);

logic unsigned [22:0] div2_3_i;
assign div2_3_i = div2(compute_v_1_i);


sequence reset_sequence;
  !rst_n ##1 rst_n;
endsequence

//Reset property
property run_reset_p;
  $past(!rst_n || ntt_masked_butterfly1x2.zeroize)  |->
  COMPUTE &&
  uv_0_u20 == 0 &&
  uv_0_u21 == 0 &&
  uv_0_v20 == 0 &&
  uv_0_v21 == 0;
endproperty
run_reset_a: assert property (run_reset_p);


//Property to check the primary outputs after cutting the output signals (v11_int,u11_int,u10_int,v10_int) of ntt_masked_gs_butterfly.
property run_COMPUTE_to_COMPUTE_CUT_p;
  COMPUTE
|->
  ##1
  COMPUTE &&
  ntt_masked_butterfly1x2.bf_pwm_uv_o.uv0 == 0 &&
  ntt_masked_butterfly1x2.bf_pwm_uv_o.uv1 == 0 &&
  ntt_masked_butterfly1x2.bf_pwm_uv_o.uv2 == ntt_masked_butterfly1x2.u10_packed &&
  ntt_masked_butterfly1x2.bf_pwm_uv_o.uv3 == ntt_masked_butterfly1x2.u11_packed &&
  uv_0_u20 == ((ntt_masked_butterfly1x2.pwm_mode) ? (23'd0) : (div2(23'($past(ntt_masked_butterfly1x2.u10_packed[0], 1) + $past(ntt_masked_butterfly1x2.u10_packed[1], 1))))) &&
  uv_0_u21 == ((ntt_masked_butterfly1x2.pwm_mode) ? (23'd0) : (div2(23'($past(ntt_masked_butterfly1x2.v10_packed[0], 1) + $past(ntt_masked_butterfly1x2.v10_packed[1], 1))))) &&
  uv_0_v20 == ((ntt_masked_butterfly1x2.pwm_mode) ? (23'd0) : (div2(23'($past(ntt_masked_butterfly1x2.u11_packed[0], 1) + $past(ntt_masked_butterfly1x2.u11_packed[1], 1))))) &&
  uv_0_v21 == ((ntt_masked_butterfly1x2.pwm_mode) ? (23'd0) : (div2(23'($past(ntt_masked_butterfly1x2.v11_packed[0], 1) + $past(ntt_masked_butterfly1x2.v11_packed[1], 1)))))
  ;
endproperty
run_COMPUTE_to_COMPUTE_CUT_a: assert property (disable iff(!rst_n) run_COMPUTE_to_COMPUTE_CUT_p);


endmodule
