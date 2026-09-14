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
//
//======================================================================
//
// rej_bounded4.sv
// --------
// CoeffFromHalfByte for eta = 4 (ML-DSA-65), FIPS 204 Algorithm 15.
//
//   if b < 9:  return 4 - b
//   else:      reject
//
// Unlike the eta = 2 case there is no mod-5 reduction, so the accepted
// half-byte passes through untouched and the "4 - b" mapping is applied
// once per output coefficient in rej_bounded_ctrl. Keeping this separate
// from rej_bounded2 leaves the SCA-reviewed eta = 2 datapath unmodified.
//
//======================================================================

module rej_bounded4
  #(
   parameter REJ_SAMPLE_W = 24
  ,parameter REJ_VALUE    = 9
  )
  (
  //input data
  input  logic       valid_i,
  input  logic [3:0] data_i,

  //output data
  output logic       valid_o,
  output logic [3:0] data_o

  );

  //Check sample validity: b < 9
  always_comb begin
    valid_o = valid_i & (data_i < REJ_VALUE);
    //No reduction for eta = 4; 4 - b is applied downstream
    data_o  = data_i;
  end

endmodule
