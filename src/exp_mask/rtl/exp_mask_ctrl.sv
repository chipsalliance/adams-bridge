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


module exp_mask_ctrl
  import abr_params_pkg::*;
  #(
   parameter EXP_NUM_SAMPLERS = 4
  ,parameter EXP_SAMPLE_W     = 20
  ,parameter EXP_VLD_SAMPLES  = 4
  ,parameter EXP_VLD_SAMPLE_W = 23
  )
  (
  input logic clk,
  input logic rst_b,
  input logic zeroize,
  //input data
  input  logic                                          data_valid_i,
  output logic                                          data_hold_o,
  input  logic [EXP_NUM_SAMPLERS-1:0][EXP_SAMPLE_W-1:0] data_i,

  //output data
  output logic                                             data_valid_o,
  output logic [EXP_VLD_SAMPLES-1:0][EXP_VLD_SAMPLE_W-1:0] data_o

  );

  //No hold here, remove this
  always_comb data_hold_o = '0;

  generate
    for (genvar inst_g = 0; inst_g < EXP_NUM_SAMPLERS; inst_g++) begin : exp_mask_inst
      exp_mask #(
        .EXP_SAMPLE_W(EXP_SAMPLE_W),
        .EXP_VLD_SAMPLE_W(EXP_VLD_SAMPLE_W)
      ) exp_mask_i (
        .data_i(data_i[inst_g]),
        .data_o(data_o[inst_g])
      );
    end
  endgenerate

always_comb data_valid_o = data_valid_i & ~zeroize;

endmodule
