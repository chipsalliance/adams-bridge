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
   localparam CBD_SAMPLE_W = 2*MLKEM_ETA
  )
  (
  //input data
  input  logic [CBD_SAMPLE_W-1:0] data_i,

  //output data
  output logic [2:0] data_o

  );

  logic [CBD_SAMPLE_W-1:0] a;
  logic [MLKEM_ETA-1:0] b;
  logic [MLKEM_ETA-1:0] c;

  assign a = data_i;

  //Check sample validity
  always_comb begin
    //Perform x - y
    b = 0;
    c = 0;
    for (int i = 0; i < MLKEM_ETA; i++) begin
      b += a[i];
      c += a[i+MLKEM_ETA];
    end
    data_o  = b - c; 
  end

endmodule
