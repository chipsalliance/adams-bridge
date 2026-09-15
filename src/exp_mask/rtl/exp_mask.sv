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

//Expand Mask function takes in a sample from the Keccak core
//and returns a coefficient calculated by the function 2^19-a%q

module exp_mask
  import abr_params_pkg::*;
  #(
    parameter EXP_SAMPLE_W     = 20
   ,parameter EXP_VLD_SAMPLE_W = 23
  )
  (
  //Selects gamma1 = 2^17 (ML-DSA-44) instead of 2^19. Public control, never secret.
  input  logic gamma1_17_i,

  //input data
  input  logic [EXP_SAMPLE_W-1:0] data_i,

  //output data
  output logic [EXP_VLD_SAMPLE_W-1:0] data_o

  );

  logic [22:0] r0, r1;
  logic c0, c1;

  //compute gamma1 - a. gamma1 is 2^19 for ML-DSA-65/87 and 2^17 for ML-DSA-44
  //(FIPS 204 Alg. 34, ExpandMask).
  logic [23:0] gamma1;
  always_comb gamma1 = (ABR_NEED_GAMMA1_17 & gamma1_17_i) ? (24'd1 << 17) : (24'd1 << 19);
  always_comb {c0,r0} = gamma1 - data_i;
  //compute potential % q value
  always_comb {c1,r1} = r0 + MLDSA_Q;
  //determine if we can take 2^19-a or need to take + q value
  always_comb data_o  = (c0 & c1) ? {1'b0,r1} : {1'b0,r0};

endmodule
