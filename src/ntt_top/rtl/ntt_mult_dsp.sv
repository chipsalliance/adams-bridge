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
// ntt_mult_dsp.sv
// --------
// General multiplier to perform P = A*B.
//
//
//======================================================================

module ntt_mult_dsp #(
    parameter RADIX = 32
)
(
    // DATA PORT
    input  wire  [RADIX-1 : 0]        A_i,
    input  wire  [RADIX-1 : 0]        B_i,
    
    output logic [(2*RADIX)-1 : 0]    P_o
);

    always_comb begin
        P_o = A_i * B_i;
    end

endmodule
