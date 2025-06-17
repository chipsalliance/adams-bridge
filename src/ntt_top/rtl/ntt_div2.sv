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
// ntt_div2.sv
// --------
// This unit performs division by 2 on butterfly outputs
//======================================================================

module ntt_div2
    #(
        parameter REG_SIZE      = 23,
        parameter PRIME   = 23'd8380417,
        parameter PRIME_DIV2_ODD = (PRIME + 1) / 2
    )
    (
        input  wire  [REG_SIZE-1:0] op_i,
        output logic [REG_SIZE-1:0] res_o
    );

    //No need to perform reduction for the addition here. 
    //If op_i = Q-1 (which is max even value allowed), op_i >> 1 is less than Q. 
    //If op_i = Q-2 (which is max odd value allowed), (op_i >> 1) + DIITHIUM_Q_DIV2_ODD is also less than Q.
    always_comb res_o = op_i[0] ? REG_SIZE'((op_i >> 1) + PRIME_DIV2_ODD)
                                             : REG_SIZE'(op_i >> 1);

endmodule