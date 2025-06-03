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


module cbd_sampler_ctrl
  import abr_params_pkg::*;
  #(
   localparam CBD_NUM_SAMPLERS = COEFF_PER_CLK
  ,localparam CBD_SAMPLE_W     = 2*MLKEM_ETA
  ,localparam CBD_VLD_SAMPLES  = CBD_NUM_SAMPLERS
  ,localparam CBD_VLD_SAMPLES_W = MLKEM_Q_WIDTH
  )
  (
  input logic clk,
  input logic rst_b,
  input logic zeroize,
  //input data
  input  logic                                          data_valid_i,
  output logic                                          data_hold_o,
  input  logic [CBD_NUM_SAMPLERS-1:0][CBD_SAMPLE_W-1:0] data_i,

  //output data
  output logic                                              data_valid_o,
  output logic [CBD_VLD_SAMPLES-1:0][CBD_VLD_SAMPLES_W-1:0] data_o

  );

  logic [CBD_NUM_SAMPLERS-1:0][2:0] sample_data;

  //Hold if the buffer is full
  always_comb data_hold_o = 0;

  generate
    for (genvar inst_g = 0; inst_g < CBD_NUM_SAMPLERS; inst_g++) begin : cbd_sampler_inst
      cbd_sampler
      cbd_sampler_i (
        .data_i(data_i[inst_g]),
        .data_o(sample_data[inst_g])
      );
    end
  endgenerate

 
  //No rejection, so data is valid when we have valid input data
  always_comb data_valid_o = data_valid_i & ~zeroize;
  //CBD buffer value selects between 5 possible outputs (x - y mod q)
  always_comb begin
    for (int sample = 0; sample < CBD_VLD_SAMPLES; sample++) begin
      unique case (sample_data[sample])
        3'd0 : data_o[sample] = 0;
        3'd1 : data_o[sample] = 1;
        3'd2 : data_o[sample] = 2;
        3'd7 : data_o[sample] = MLKEM_Q-1;
        3'd6 : data_o[sample] = MLKEM_Q-2;
        default : data_o[sample] = '0;
      endcase
    end
  end

endmodule
