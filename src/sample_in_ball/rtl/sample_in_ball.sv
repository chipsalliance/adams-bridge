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
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either sibress or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//Sample In Ball function tests each sample for validitiy
//Valid samples must be <= rej_value_i

module sample_in_ball
  //    import ::*;
  #(
    parameter SIB_SAMPLE_W = 8
  )
  (
  //input data
  input  logic                    valid_i,
  input  logic [SIB_SAMPLE_W-1:0] data_i,
  input  logic [SIB_SAMPLE_W-1:0] rej_value_i,

  //output data
  output logic                    valid_o

  );

  always_comb valid_o = valid_i & (data_i <= rej_value_i);

endmodule
