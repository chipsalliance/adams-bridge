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
// | Created on 03.02.2025 at 18:02                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import fv_ntt_masked_BFU_add_sub_pkg::*;
import ntt_defines_pkg::*;
import fv_ntt_masked_BFU_add_sub_functions::*;


module fv_ntt_masked_BFU_add_sub_m(
  input logic rst_n,
  input logic clk,

  // Ports
  input a_unsigned_46_2 u,

  input a_unsigned_46_2 v,

  input logic unsigned [0:0] sub,

  input a_unsigned_2_46 res,

  // States
  input logic COMPUTE
);


default clocking default_clk @(posedge clk); endclocking



sequence reset_sequence;
  !rst_n ##1 rst_n;
endsequence

property run_reset_p;
  $past(!rst_n) |->
  COMPUTE &&
  make_packed(ntt_masked_BFU_add_sub.res[45:0]) == 0;
endproperty
run_reset_a: assert property (run_reset_p);

//Property to check the output of module in sub mode (sub == 1)
property run_COMPUTE_to_COMPUTE_sub_p;
  COMPUTE &&
  sub
|->
  ##52
  COMPUTE &&
  (ntt_masked_BFU_add_sub.add_res_reduced[0] + ntt_masked_BFU_add_sub.add_res_reduced[1]) == ($past(u[0] + u[1], 52) >= $past(v[0] + v[1], 52)) ? 
      $past((u[0] + u[1] - v[0] - v[1]) , 52) : $past((u[0] + u[1] - v[0] - v[1]) + 'h7FE001, 52);
endproperty
run_COMPUTE_to_COMPUTE_sub_a: assert property (disable iff(!rst_n) run_COMPUTE_to_COMPUTE_sub_p);


//Property to check the output of module in add mode (sub == 0)
property run_COMPUTE_to_COMPUTE_add_p;
  COMPUTE &&
  !sub
|->
  ##52
  COMPUTE &&
  (ntt_masked_BFU_add_sub.add_res_reduced[0] + ntt_masked_BFU_add_sub.add_res_reduced[1])  == $past((u[0] + u[1] + v[0] + v[1]) % 'h7FE001, 52);
endproperty
run_COMPUTE_to_COMPUTE_add_a: assert property (disable iff(!rst_n) run_COMPUTE_to_COMPUTE_add_p);

function logic [45:0] xor_add_sub(logic [1:0] arr [45:0]);
  for (int i = 0; i < 46; i++) begin
    xor_add_sub[i] = arr[i][0] ^ arr[i][1];
  end
endfunction

function logic [1:0][45:0] make_packed(logic [1:0] arr [45:0]);
  for (int i = 0; i < 46; i++) begin
    make_packed[0][i] = arr[i][0];
    make_packed[1][i] = arr[i][1];
  end
endfunction

//Property to check a2bconv submodule used in ntt_masked_BFU_add_sub
property run_COMPUTE_to_COMPUTE_a2b_p;
  COMPUTE
|->
  ##48
  COMPUTE &&
  xor_add_sub(ntt_masked_BFU_add_sub.add_res_bool[45:0])
  == $past(46'(ntt_masked_BFU_add_sub.add_res_rolled0 + ntt_masked_BFU_add_sub.add_res_rolled1), 48);
endproperty
run_COMPUTE_to_COMPUTE_a2b_a: assert property (disable iff(!rst_n) run_COMPUTE_to_COMPUTE_a2b_p);

//Property to check b2aconv submodule used in ntt_masked_BFU_add_sub
property run_COMPUTE_to_COMPUTE_b2a_p;
  COMPUTE
|->
  ##2
  COMPUTE &&
  46'(ntt_masked_BFU_add_sub.add_res_arith0 + ntt_masked_BFU_add_sub.add_res_arith1)
  == $past(xor_add_sub(ntt_masked_BFU_add_sub.temp0[45:0]), 2);
endproperty
run_COMPUTE_to_COMPUTE_b2a_a: assert property (disable iff(!rst_n) run_COMPUTE_to_COMPUTE_b2a_p);

//Property to check the unpacked version of output (res) is equal to the unpacked version (add_res_reduced)
property run_COMPUTE_to_COMPUTE_1_p;
  COMPUTE
|->
  ##1
  COMPUTE &&
  make_packed(ntt_masked_BFU_add_sub.res[45:0])
  == {$past(ntt_masked_BFU_add_sub.add_res_reduced[1], 1), $past(ntt_masked_BFU_add_sub.add_res_reduced[0], 1)};
endproperty
run_COMPUTE_to_COMPUTE_1_a: assert property (disable iff(!rst_n) run_COMPUTE_to_COMPUTE_1_p);


endmodule
