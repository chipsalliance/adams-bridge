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
// power2round_core.sv
// --------
// Breaks down input coefficient 
//======================================================================

module power2round_core
    #(
        parameter REG_SIZE = 23,
        parameter MLDSA_Q = 23'd8380417,
        parameter MLDSA_D = 13
    )
    (
        input wire [REG_SIZE-1:0] r,
        output logic [MLDSA_D-1:0] r0,
        output logic [REG_SIZE-MLDSA_D-1:0] r1
    );

    localparam power2_d_minus_one = (1 << (MLDSA_D-1)) - 1;

    logic [REG_SIZE : 0] sum0;
    logic [REG_SIZE : 0] sum1;
    logic [REG_SIZE-MLDSA_D-1:0] r1_temp;
    logic [MLDSA_D-1 : 0] r0_temp;

    always_comb begin
        sum0 = r + power2_d_minus_one;
        r1_temp = sum0[REG_SIZE-1:MLDSA_D];
        sum1 = r - (r1_temp << MLDSA_D);
        r0_temp = sum1[MLDSA_D-1 : 0];
    end

    assign r0 = r0_temp;
    assign r1 = r1_temp;
endmodule