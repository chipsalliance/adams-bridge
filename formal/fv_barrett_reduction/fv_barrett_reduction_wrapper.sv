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

module fv_barrett_reduction_wrapper
#(
    parameter prime    = 3329,
    parameter REG_SIZE = $clog2(prime)
) (
    //#$ports
    input  logic clk,
    input  logic rst,
    input  logic [2*REG_SIZE-1:0] pi_x,
    output logic [REG_SIZE-1:0]   po_inv,
    output logic [REG_SIZE-1:0]   po_r
    //$#//
);

barrett_reduction #(
    .prime(prime),
    .REG_SIZE(REG_SIZE)
) barrett_reduction_i (
    .x(pi_x),
    .inv(po_inv),
    .r(po_r));

endmodule
