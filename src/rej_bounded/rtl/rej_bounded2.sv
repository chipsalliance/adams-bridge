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

//Rej Bounded function computes % 5 of the input sample
//Samples must be < REJ_VALUE to be valid

module rej_bounded2
  //    import ::*;
  #(
   parameter REJ_SAMPLE_W = 24
  ,parameter REJ_VALUE    = 15
  )
  (
  //input data
  input  logic       valid_i,
  input  logic [3:0] data_i,

  //output data
  output logic       valid_o,
  output logic [2:0] data_o

  );

  logic [3:0] a;
  logic [2:0] b;

  assign a = data_i;

  //Check sample validity
  always_comb begin
    valid_o = valid_i & (a < REJ_VALUE);
    //Perform data_i % 5
    b = a[1:0] - a[3:2];
    data_o  = b[2] ? 'd5 + b[2:0] : {1'b0, b[1:0]}; 
  end

endmodule
