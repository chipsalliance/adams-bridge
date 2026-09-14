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


module rej_bounded_ctrl
  import abr_params_pkg::*;
  #(
   parameter REJ_NUM_SAMPLERS = 8
  ,parameter REJ_SAMPLE_W     = 4
  ,parameter REJ_VLD_SAMPLES  = 4
  ,parameter REJ_VLD_SAMPLES_W = 24
  ,parameter REJ_VALUE = 15        //eta=2 threshold (FIPS 204 Alg 15)
  ,parameter REJ_VALUE_ETA4 = 9    //eta=4 threshold (FIPS 204 Alg 15)
  ,parameter REJ_BUFFER_W = ABR_NEED_ETA4 ? 4 : 3
  )
  (
  input logic clk,
  input logic rst_b,
  input logic zeroize,
  //eta select: 0 => eta=2, 1 => eta=4 (ML-DSA-65). Public, never secret.
  input logic eta4_i,
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
    for (genvar inst_g = 0; inst_g < REJ_NUM_SAMPLERS; inst_g++) begin : rej_bounded_inst
      logic       eta2_valid;
      logic [2:0] eta2_data;

      rej_bounded2 #(
        .REJ_SAMPLE_W(REJ_SAMPLE_W),
        .REJ_VALUE(REJ_VALUE)
      ) rej_bounded_i (
        .valid_i(data_valid_i),
        .data_i(data_i[inst_g]),

        .valid_o(eta2_valid),
        .data_o(eta2_data)
      );

      if (ABR_NEED_ETA4) begin : g_eta4
        logic       eta4_valid;
        logic [3:0] eta4_data;

        rej_bounded4 #(
          .REJ_SAMPLE_W(REJ_SAMPLE_W),
          .REJ_VALUE(REJ_VALUE_ETA4)
        ) rej_bounded4_i (
          .valid_i(data_valid_i),
          .data_i(data_i[inst_g]),

          .valid_o(eta4_valid),
          .data_o(eta4_data)
        );

        always_comb begin
          sample_valid[inst_g] = eta4_i ? eta4_valid : eta2_valid;
          buffer_data[inst_g]  = eta4_i ? REJ_BUFFER_W'(eta4_data)
                                        : REJ_BUFFER_W'(eta2_data);
        end
      end else begin : g_no_eta4
        always_comb begin
          sample_valid[inst_g] = eta2_valid;
          buffer_data[inst_g]  = REJ_BUFFER_W'(eta2_data);
        end
      end
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
  //Map the buffered half-byte to a coefficient mod q.
  //  eta=2: 5 outcomes,  2 - (a % 5)   (FIPS 204 Alg 15)
  //  eta=4: 9 outcomes,  4 - b         (FIPS 204 Alg 15)
  always_comb begin
    for (int sample = 0; sample < REJ_VLD_SAMPLES; sample++) begin
      if (ABR_NEED_ETA4 && eta4_i) begin
        unique case (rej_buffer[sample])
          'd0 : data_o[sample] = 4;
          'd1 : data_o[sample] = 3;
          'd2 : data_o[sample] = 2;
          'd3 : data_o[sample] = 1;
          'd4 : data_o[sample] = 0;
          'd5 : data_o[sample] = MLDSA_Q-1;
          'd6 : data_o[sample] = MLDSA_Q-2;
          'd7 : data_o[sample] = MLDSA_Q-3;
          'd8 : data_o[sample] = MLDSA_Q-4;
          default : data_o[sample] = '0;
        endcase
      end else begin
        unique case (rej_buffer[sample][2:0])
          3'd0 : data_o[sample] = 2;
          3'd1 : data_o[sample] = 1;
          3'd2 : data_o[sample] = 0;
          3'd3 : data_o[sample] = MLDSA_Q-1;
          3'd4 : data_o[sample] = MLDSA_Q-2;
          default : data_o[sample] = '0;
        endcase
      end
    end
  end

endmodule
