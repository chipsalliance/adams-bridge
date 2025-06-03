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


module rej_sampler_ctrl
  import abr_params_pkg::*;
  #(
   parameter REJ_NUM_SAMPLERS = 5
  ,parameter REJ_SAMPLE_W     = 24
  ,parameter REJ_VLD_SAMPLES  = 4
  ,parameter REJ_VLD_SAMPLES_W = 24
  ,parameter REJ_VALUE = 8380417
  ,parameter OPT_REJ_BUFFER_DEPTH = 0
  ,parameter REJ_BUFFER_W = $clog2(REJ_VALUE)
  )
  (
  input logic clk,
  input logic rst_b,

  input logic zeroize,

  //input data
  input  logic                                          data_valid_i,
  output logic                                          data_hold_o,
  input  logic [REJ_NUM_SAMPLERS-1:0][REJ_SAMPLE_W-1:0] data_i,

  //output data
  output logic                                              data_valid_o,
  output logic [REJ_VLD_SAMPLES-1:0][REJ_VLD_SAMPLES_W-1:0] data_o

  );

  logic [REJ_NUM_SAMPLERS-1:0] sample_valid;
  logic [REJ_NUM_SAMPLERS-1:0][REJ_BUFFER_W-1:0] buffer_data;

  logic                                         rej_buffer_valid;
  logic [REJ_VLD_SAMPLES-1:0][REJ_BUFFER_W-1:0] rej_buffer;

  logic buffer_full;

  //Hold if the buffer is full
  always_comb data_hold_o = buffer_full;

  generate
    for (genvar inst_g = 0; inst_g < REJ_NUM_SAMPLERS; inst_g++) begin : rej_sampler_inst
      //Check sample validity
      rej_sampler #(
        .REJ_SAMPLE_W(REJ_SAMPLE_W),
        .REJ_VALUE(REJ_VALUE)
      ) rej_sampler_i (
        .valid_i(data_valid_i),
        .data_i(data_i[inst_g]),

        .valid_o(sample_valid[inst_g]),
        .data_o(buffer_data[inst_g])
      );
    end
  endgenerate

  //Buffer valid samples
  abr_sample_buffer #(
    .NUM_WR(REJ_NUM_SAMPLERS),
    .NUM_RD(REJ_VLD_SAMPLES),
    .BUFFER_DATA_W(REJ_BUFFER_W)
  ) mldsa_sample_buffer_i (
    .clk(clk),
    .rst_b(rst_b),
    .zeroize(zeroize),
    //input data
    .data_valid_i(sample_valid),
    .data_i(buffer_data),
    .buffer_full_o(buffer_full),
    //output data
    .data_valid_o(rej_buffer_valid),
    .data_o(rej_buffer)
  );

  //Output is valid when we have REJ_VLD_SAMPLES worth of valid data
  always_comb data_valid_o = rej_buffer_valid;
  //Need to concat the zeros back for diff between sample w and the valid sample bits
  always_comb begin
    for (int sample = 0; sample < REJ_VLD_SAMPLES; sample++) begin
      data_o[sample] = { {REJ_SAMPLE_W-REJ_BUFFER_W{1'b0}} , rej_buffer[sample] };
    end
  end

endmodule
