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
  //Lane count for the eta = 4 bank. Sized in abr_sampler_pkg and passed in so
  //this module stays free of a dependency on the sampler package.
  ,parameter REJ_NUM_SAMPLERS_ETA4 = 20
  ,localparam REJ_NUM_SAMPLERS_MAX  = ABR_NEED_ETA4 ? REJ_NUM_SAMPLERS_ETA4
                                                    : REJ_NUM_SAMPLERS
  )
  (
  input logic clk,
  input logic rst_b,
  input logic zeroize,
  //eta select: 0 => eta=2, 1 => eta=4 (ML-DSA-65). Public, never secret.
  input logic eta4_i,
  //input data
  input  logic                                              data_valid_i,
  output logic                                              data_hold_o,
  input  logic [REJ_NUM_SAMPLERS_MAX-1:0][REJ_SAMPLE_W-1:0] data_i,

  //output data
  output logic                                              data_valid_o,
  output logic [REJ_VLD_SAMPLES-1:0][REJ_VLD_SAMPLES_W-1:0] data_o

  );

  //--------------------------------------------------------------------------
  // eta = 2 bank (ML-DSA-44 / -87). Bit- and cycle-identical to the
  // category-5 design: REJ_NUM_SAMPLERS lanes, 3-bit buffer entries.
  //--------------------------------------------------------------------------
  localparam ETA2_BUFFER_W = 3;

  logic                                            eta2_valid_i;
  logic [REJ_NUM_SAMPLERS-1:0]                     eta2_sample_valid;
  logic [REJ_NUM_SAMPLERS-1:0][ETA2_BUFFER_W-1:0]  eta2_buffer_data;
  logic                                            eta2_buffer_full;
  logic                                            eta2_buffer_valid;
  logic [REJ_VLD_SAMPLES-1:0][ETA2_BUFFER_W-1:0]   eta2_buffer;

  always_comb eta2_valid_i = data_valid_i & (ABR_NEED_ETA4 ? ~eta4_i : 1'b1);

  for (genvar inst_g = 0; inst_g < REJ_NUM_SAMPLERS; inst_g++) begin : rej_bounded_inst
    rej_bounded2 #(
      .REJ_SAMPLE_W(REJ_SAMPLE_W),
      .REJ_VALUE(REJ_VALUE)
    ) rej_bounded_i (
      .valid_i(eta2_valid_i),
      .data_i(data_i[inst_g]),

      .valid_o(eta2_sample_valid[inst_g]),
      .data_o(eta2_buffer_data[inst_g])
    );
  end

  abr_sample_buffer #(
    .NUM_WR(REJ_NUM_SAMPLERS),
    .NUM_RD(REJ_VLD_SAMPLES),
    .BUFFER_DATA_W(ETA2_BUFFER_W)
  ) mldsa_sample_buffer_i (
    .clk(clk),
    .rst_b(rst_b),
    .zeroize(zeroize),
    //input data
    .data_valid_i(eta2_sample_valid),
    .data_i(eta2_buffer_data),
    .buffer_full_o(eta2_buffer_full),
    //output data
    .data_valid_o(eta2_buffer_valid),
    .data_o(eta2_buffer)
  );

  //--------------------------------------------------------------------------
  // eta = 4 bank (ML-DSA-65), elaborated only when the set is enabled.
  //
  // FIPS 204 Alg. 15 accepts a half byte only when it is < 9, so the
  // acceptance probability is 9/16 rather than 15/16. Eight lanes would
  // deliver 4.5 accepts per cycle against a fixed downstream demand of
  // REJ_VLD_SAMPLES = 4, which is not enough margin to keep the drain
  // demand limited - the loop length would then track the number of
  // rejections, i.e. leak s1/s2 through timing. REJB_NUM_SAMPLERS_ETA4
  // lanes restore a margin wider than the category-5 path has.
  //
  // A separate bank (rather than widening the shared one) keeps the
  // category-5 sampler count, buffer depth and buffer width untouched.
  //--------------------------------------------------------------------------
  localparam ETA4_BUFFER_W = 4;

  logic                                            eta4_buffer_full;
  logic                                            eta4_buffer_valid;
  logic [REJ_VLD_SAMPLES-1:0][ETA4_BUFFER_W-1:0]   eta4_buffer;

  if (ABR_NEED_ETA4) begin : g_eta4_bank
    logic                                                 eta4_valid_i;
    logic [REJ_NUM_SAMPLERS_ETA4-1:0]                     eta4_sample_valid;
    logic [REJ_NUM_SAMPLERS_ETA4-1:0][ETA4_BUFFER_W-1:0]  eta4_buffer_data;

    always_comb eta4_valid_i = data_valid_i & eta4_i;

    for (genvar inst_g = 0; inst_g < REJ_NUM_SAMPLERS_ETA4; inst_g++) begin : rej_bounded4_inst
      rej_bounded4 #(
        .REJ_SAMPLE_W(REJ_SAMPLE_W),
        .REJ_VALUE(REJ_VALUE_ETA4)
      ) rej_bounded4_i (
        .valid_i(eta4_valid_i),
        .data_i(data_i[inst_g]),

        .valid_o(eta4_sample_valid[inst_g]),
        .data_o(eta4_buffer_data[inst_g])
      );
    end

    abr_sample_buffer #(
      .NUM_WR(REJ_NUM_SAMPLERS_ETA4),
      .NUM_RD(REJ_VLD_SAMPLES),
      .BUFFER_DATA_W(ETA4_BUFFER_W)
    ) mldsa_sample_buffer_eta4_i (
      .clk(clk),
      .rst_b(rst_b),
      .zeroize(zeroize),
      //input data
      .data_valid_i(eta4_sample_valid),
      .data_i(eta4_buffer_data),
      .buffer_full_o(eta4_buffer_full),
      //output data
      .data_valid_o(eta4_buffer_valid),
      .data_o(eta4_buffer)
    );
  end else begin : g_no_eta4_bank
    always_comb eta4_buffer_full  = 1'b0;
    always_comb eta4_buffer_valid = 1'b0;
    always_comb eta4_buffer       = '0;
  end

  //--------------------------------------------------------------------------
  // Bank select. eta4_i is the public parameter set, never secret material,
  // so muxing on it introduces no data dependent control flow.
  //--------------------------------------------------------------------------
  logic                                          rej_buffer_valid;
  logic [REJ_VLD_SAMPLES-1:0][ETA4_BUFFER_W-1:0] rej_buffer;

  always_comb begin
    if (ABR_NEED_ETA4 & eta4_i) begin
      data_hold_o      = eta4_buffer_full;
      rej_buffer_valid = eta4_buffer_valid;
      for (int sample = 0; sample < REJ_VLD_SAMPLES; sample++)
        rej_buffer[sample] = eta4_buffer[sample];
    end else begin
      data_hold_o      = eta2_buffer_full;
      rej_buffer_valid = eta2_buffer_valid;
      for (int sample = 0; sample < REJ_VLD_SAMPLES; sample++)
        rej_buffer[sample] = ETA4_BUFFER_W'(eta2_buffer[sample]);
    end
  end

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
