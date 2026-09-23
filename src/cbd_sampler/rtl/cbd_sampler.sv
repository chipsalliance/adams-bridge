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

//Computes the centered binomial distribution for ML-KEM

module cbd_sampler
  import abr_params_pkg::*;
  #(
   parameter  CBD_ETA      = MLKEM_ETA1_MAX
  ,localparam CBD_SAMPLE_W = 2*CBD_ETA
  )
  (
  //input data
  input  logic [CBD_SAMPLE_W-1:0] data_i,
  //eta1 = 3 (ML-KEM-512). CBD_ETA above only sizes the lane.
  input  logic                    eta3_i,

  //output data
  output logic [2:0] data_o

  );

  logic [CBD_SAMPLE_W-1:0] a;
  logic [2:0] b;
  logic [2:0] c;
  logic [2:0] eta_active;

  assign a = data_i;

  //FIPS 203 Alg. 8 (SamplePolyCBD): b = sum of the first eta bits, c = sum of
  //the next eta bits, sample = b - c. eta moves the split point, so when more
  //than one ML-KEM parameter set is enabled it has to be a runtime value.
  always_comb eta_active = eta3_i ? 3'd3 : 3'd2;

  //Check sample validity
  always_comb begin
    //Perform x - y
    b = 0;
    c = 0;
    for (int i = 0; i < CBD_ETA; i++) begin
      if (3'(i) < eta_active) begin
        b += a[i];
        c += a[3'(i) + eta_active];
      end
    end
    data_o  = b - c;
  end

endmodule
