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

//Rej sampler function tests each sample for validity
//Valid samples must be < REJ_VALUE

module rej_sampler
  //    import ::*;
  #(
   parameter REJ_SAMPLE_W      = 24
  ,parameter REJ_VALUE         = 8380417
  ,localparam REJ_VLD_SAMPLE_W = $clog2(REJ_VALUE)
  )
  (
  //input data
  input  logic                    valid_i,
  input  logic [REJ_SAMPLE_W-1:0] data_i,

  //output data
  output logic                        valid_o,
  output logic [REJ_VLD_SAMPLE_W-1:0] data_o

  );

  //Check sample validity
  always_comb begin
    valid_o = valid_i & (data_i[REJ_VLD_SAMPLE_W-1:0] < REJ_VALUE[REJ_VLD_SAMPLE_W-1:0]);
    data_o  = data_i[REJ_VLD_SAMPLE_W-1:0];
  end

endmodule