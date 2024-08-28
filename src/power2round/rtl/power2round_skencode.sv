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
//======================================================================
//
// power2round_skencode.sv
// --------
// Breaks down input coefficient 
//======================================================================

module power2round_skencode
    #(
        parameter REG_SIZE = 23,
        parameter MLDSA_Q = 23'd8380417,
        parameter MLDSA_D = 13
    )
    (
        input logic  [MLDSA_D-1:0] r0,
        output logic [MLDSA_D-1:0] r0_packed
    );

    localparam power2_d_minus_one = (1 << (MLDSA_D-1));

    logic [MLDSA_D-1 : 0] r0_packed_temp;

    always_comb begin
        r0_packed_temp = power2_d_minus_one - r0;
    end

    assign r0_packed = r0_packed_temp;
endmodule