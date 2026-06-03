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
// | Created on 03.12.2024 at 15:32                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import fv_exp_mask_ctrl_pkg::*;

// Functions
// 2^19 - a mod q change to actual modulo operator
function logic unsigned [22:0] expand_mask(logic unsigned [19:0] data);
  if ((data > 24'h80000))
    return 23'((64'd8380417 + 23'((24'h80000 - data))));
  else
    return 23'((24'h80000 - data));
endfunction

function a_unsigned_23_4 expand_mask_coeff(a_unsigned_20_4 data);
  logic unsigned [22:0] expand_mask_0_i;
  logic unsigned [22:0] expand_mask_1_i;
  logic unsigned [22:0] expand_mask_2_i;
  logic unsigned [22:0] expand_mask_3_i;

  expand_mask_0_i = expand_mask(data[0]);
  expand_mask_1_i = expand_mask(data[1]);
  expand_mask_2_i = expand_mask(data[2]);
  expand_mask_3_i = expand_mask(data[3]);

  return '{ 0: expand_mask_0_i, 1: expand_mask_1_i, 2: expand_mask_2_i, 3: expand_mask_3_i };
endfunction


module fv_exp_mask_ctrl_m(
  input logic rst_n,
  input logic zeroize,
  input logic clk,

  // Ports
  input a_unsigned_20_4 input_data_port,

  input a_unsigned_23_4 output_data_port,

  input logic input_data_valid_port,

  input logic output_data_hold_o,

  input logic output_data_valid_port

);


default clocking default_clk @(posedge clk); endclocking



a_unsigned_23_4 expand_mask_coeff_0_i;
assign expand_mask_coeff_0_i = expand_mask_coeff(input_data_port);



property COMPUTE_to_COMPUTE_p;
  (output_data_port == expand_mask_coeff_0_i) &&
  (output_data_hold_o == '0) &&
  (output_data_valid_port == (input_data_valid_port && !zeroize));

endproperty
COMPUTE_to_COMPUTE_a: assert property (COMPUTE_to_COMPUTE_p);



endmodule
