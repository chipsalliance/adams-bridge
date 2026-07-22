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
// | Created on 04.02.2025 at 22:03                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import fv_ntt_masked_BFU_mult_pkg::*;
import ntt_defines_pkg::*;
import fv_ntt_masked_BFU_mult_functions::*;


module fv_ntt_masked_BFU_mult_m(
  input logic rst_n,
  input logic clk,

  // Ports
  input a_unsigned_46_2 u,

  input a_unsigned_46_2 v,

  input a_unsigned_2_46 res,

  // States
  input logic COMPUTE
);


default clocking default_clk @(posedge clk); endclocking


function logic [1:0][45:0] make_packed(logic [1:0] arr [45:0]);
  for (int i = 0; i < 46; i++) begin
    make_packed[0][i] = arr[i][0];
    make_packed[1][i] = arr[i][1];
  end
endfunction


sequence reset_sequence;
  !rst_n ##1 rst_n;
endsequence

//reset property
property run_reset_p;
  $past(!rst_n || ntt_masked_BFU_mult.zeroize) |->
  COMPUTE &&
  make_packed(ntt_masked_BFU_mult.res[45:0]) == 0;
endproperty
run_reset_a: assert property (run_reset_p);

//Property to check the output of the complete ntt_masked_BFU_mult module (with truncation)
property run_COMPUTE_to_COMPUTE_p;
  COMPUTE
|->
  ##210
  COMPUTE &&
  (ntt_masked_BFU_mult.final_res[0] + ntt_masked_BFU_mult.final_res[1])
   == $past(46'(46'(u[0] * v[0]) + 46'(u[0] * v[1]) + 46'(u[1] * v[0]) + 46'(u[1] * v[1])) % 'h7FE001, 210);
endproperty
run_COMPUTE_to_COMPUTE_a: assert property (disable iff(!rst_n) run_COMPUTE_to_COMPUTE_p);

//Property to check the output of the complete ntt_masked_BFU_mult module (without truncation)
property run_COMPUTE_to_COMPUTE_1_p;
  COMPUTE
|->
  ##210
  COMPUTE &&
  (ntt_masked_BFU_mult.final_res[0] + ntt_masked_BFU_mult.final_res[1]) 
   == $past(((u[0] + u[1]) * (v[0] + v[1])) % 'h7FE001, 210);
endproperty
run_COMPUTE_to_COMPUTE_1_a: assert property (disable iff(!rst_n) run_COMPUTE_to_COMPUTE_1_p);

// add two different versions one with truncation other without

//Property to check the abr_masked_N_bit_mult_two_share submodule used in ntt_masked_BFU_mult (with truncation)
property run_COMPUTE_to_COMPUTE_mult_two_share_p;
  COMPUTE
|->
  ##2
  COMPUTE &&
  46'(ntt_masked_BFU_mult.mul_res0 + ntt_masked_BFU_mult.mul_res1)
  == $past(46'(46'(u[0] * v[0]) + 46'(u[0] * v[1]) + 46'(u[1] * v[0]) + 46'(u[1] * v[1])), 2);
endproperty
run_COMPUTE_to_COMPUTE_mult_two_share_a: assert property (disable iff(!rst_n) run_COMPUTE_to_COMPUTE_mult_two_share_p);

//Property to check the abr_masked_N_bit_mult_two_share submodule used in ntt_masked_BFU_mult (without truncation)
property run_COMPUTE_to_COMPUTE_mult_two_share_1_p;
  COMPUTE
|->
  ##2
  COMPUTE &&
  46'(ntt_masked_BFU_mult.mul_res0 + ntt_masked_BFU_mult.mul_res1)
  == $past(((u[0] * v[0]) + (u[0] * v[1]) + (u[1] * v[0]) + (u[1] * v[1])), 2);
endproperty
run_COMPUTE_to_COMPUTE_mult_two_share_1_a: assert property (disable iff(!rst_n) run_COMPUTE_to_COMPUTE_mult_two_share_1_p);


function logic [22:0] xor_mult_res_reduced(logic [1:0] arr [22:0]);
  for (int i = 0; i < 23; i++) begin
    xor_mult_res_reduced[i] = arr[i][0] ^ arr[i][1];
  end
endfunction

function logic [45:0] xor_mult_res(logic [1:0] arr [45:0]);
  for (int i = 0; i < 46; i++) begin
    xor_mult_res[i] = arr[i][0] ^ arr[i][1];
  end
endfunction

//Property to check ntt_masked_mult_redux46 submodule used in ntt_masked_BFU_mult
property run_COMPUTE_to_COMPUTE_mult_redux46_p;
  COMPUTE |->
    ##157 COMPUTE &&
    (xor_mult_res_reduced(ntt_masked_BFU_mult.mul_res_bool_reduced[22:0]) == 
     $past(xor_mult_res(ntt_masked_BFU_mult.mul_res_bool[45:0]) % 'h7FE001, 157));
endproperty
run_COMPUTE_to_COMPUTE_mult_redux46_a: assert property (disable iff(!rst_n) run_COMPUTE_to_COMPUTE_mult_redux46_p);

//Property to check abr_masked_B2Aconv submodule used in ntt_masked_BFU_mult
property run_COMPUTE_to_COMPUTE_b2a_p;
  COMPUTE
|->
  ##2
  COMPUTE &&
  46'(ntt_masked_BFU_mult.mul_res_redux0 + ntt_masked_BFU_mult.mul_res_redux1)
  == $past(xor_mult_res(ntt_masked_BFU_mult.mul_res_bool_reduced_padded[45:0]), 2);
endproperty
run_COMPUTE_to_COMPUTE_b2a_a: assert property (disable iff(!rst_n) run_COMPUTE_to_COMPUTE_b2a_p);

//Property to check abr_masked_A2Bconv submodule used in ntt_masked_BFU_mult
property run_COMPUTE_to_COMPUTE_a2b_p;
  COMPUTE
|->
  ##48
  COMPUTE &&
  xor_mult_res(ntt_masked_BFU_mult.mul_res_bool[45:0])
  == $past(46'(ntt_masked_BFU_mult.mul_res0 + ntt_masked_BFU_mult.mul_res1), 48);
endproperty
run_COMPUTE_to_COMPUTE_a2b_a: assert property (disable iff(!rst_n) run_COMPUTE_to_COMPUTE_a2b_p);

function logic [10:0] xor_add_sub_11(logic [1:0] arr [10:0]);
  for (int i = 0; i < 11; i++) begin
    xor_add_sub_11[i] = arr[i][0] ^ arr[i][1];
  end
endfunction

function logic [23:0] xor_add_sub_24(logic [1:0] arr [23:0]);
  for (int i = 0; i < 24; i++) begin
    xor_add_sub_24[i] = arr[i][0] ^ arr[i][1];
  end
endfunction

function logic [22:0] xor_add_sub_23(logic [1:0] arr [22:0]);
  for (int i = 0; i < 23; i++) begin
    xor_add_sub_23[i] = arr[i][0] ^ arr[i][1];
  end
endfunction

//Property to check abr_masked_N_bit_Boolean_adder submodule used in ntt_masked_mult_redux46 
property run_COMPUTE_to_COMPUTE_masked_adder_11_p;
  COMPUTE
|->
  ##13
  COMPUTE &&
  xor_add_sub_11(ntt_masked_BFU_mult.mult_redux46_inst.tmp[10:0])
  == $past(11'(xor_add_sub_11(ntt_masked_BFU_mult.mult_redux46_inst.z_22_13[10:0]) 
             + xor_add_sub_11(ntt_masked_BFU_mult.mult_redux46_inst.z_32_23[10:0])), 13);
endproperty
run_COMPUTE_to_COMPUTE_masked_adder_11_a: assert property (disable iff(!rst_n) run_COMPUTE_to_COMPUTE_masked_adder_11_p);

//Property to check abr_delay_masked_shares submodule used in ntt_masked_mult_redux46 
property run_COMPUTE_to_COMPUTE_masked_delay_p;
  COMPUTE
|->
  ##40
  COMPUTE &&
  ntt_masked_BFU_mult.mult_redux46_inst.z_12_0_delayed 
  == $past(ntt_masked_BFU_mult.mult_redux46_inst.z_12_0, 40);
endproperty
run_COMPUTE_to_COMPUTE_masked_delay_a: assert property (disable iff(!rst_n) run_COMPUTE_to_COMPUTE_masked_delay_p);


//Property to check abr_masked_add_sub_mod_Boolean submodule used in ntt_masked_mult_redux46 (sub = 0)
property run_COMPUTE_to_COMPUTE_add_sub_boolean_1_p;
  COMPUTE
|->
  ##54
  COMPUTE &&
  xor_add_sub_23(ntt_masked_BFU_mult.mult_redux46_inst.e22_0[22:0])
  == $past((xor_add_sub_23(ntt_masked_BFU_mult.mult_redux46_inst.z_45_23_delayed[22:0]) 
          + xor_add_sub_23(ntt_masked_BFU_mult.mult_redux46_inst.f13_0_padded_9[22:0])) % 'h7FE001, 54);
endproperty
run_COMPUTE_to_COMPUTE_add_sub_boolean_1_a: assert property (disable iff(!rst_n) run_COMPUTE_to_COMPUTE_add_sub_boolean_1_p);

//Property to check abr_masked_add_sub_mod_Boolean submodule used in ntt_masked_mult_redux46 (sub = 1)
property run_COMPUTE_to_COMPUTE_add_sub_boolean_2_p;
  COMPUTE
|->
  ##54
  COMPUTE &&
  xor_add_sub_23(ntt_masked_BFU_mult.mult_redux46_inst.y[22:0])
  == ($past(xor_add_sub_23(ntt_masked_BFU_mult.mult_redux46_inst.d22_0_delayed[22:0]), 54) >= $past(xor_add_sub_23(ntt_masked_BFU_mult.mult_redux46_inst.e22_0[22:0]), 54)) ?
    $past((xor_add_sub_23(ntt_masked_BFU_mult.mult_redux46_inst.d22_0_delayed[22:0]) 
          - xor_add_sub_23(ntt_masked_BFU_mult.mult_redux46_inst.e22_0[22:0])), 54):
    $past((xor_add_sub_23(ntt_masked_BFU_mult.mult_redux46_inst.d22_0_delayed[22:0]) 
          - xor_add_sub_23(ntt_masked_BFU_mult.mult_redux46_inst.e22_0[22:0])) + 'h7FE001, 54)
endproperty
run_COMPUTE_to_COMPUTE_add_sub_boolean_2_a: assert property (disable iff(!rst_n) run_COMPUTE_to_COMPUTE_add_sub_boolean_2_p);

endmodule
