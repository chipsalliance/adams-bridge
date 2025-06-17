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
// Module: abr_masked_OR
// Description: This module implements a masked OR gate with domain-oriented masking.
//              The masking technique enhances security by using a random bit to obscure
//              intermediate values, reducing vulnerability to side-channel attacks.
// 
// 
// Functionality:
//  - The module calculates the OR operation between bits of inputs x and y.
//  - Intermediate results are masked using a random bit to prevent side-channel leakage.
//  - Final output is obtained by combining the reshared and masked intermediate results.
//  - It requires 1-bit fresh randomness for each execution.
//  - It has one cycle latency and can accept a new input set at the every clock.
//
//======================================================================

module abr_masked_OR
(
    input wire clk,
    input wire rst_n,
    input wire zeroize,
    input wire rnd,
    input wire [1:0] x,
    input wire [1:0] y,
    output logic [1:0] z
);

    logic inv_x0, inv_y0;
    logic [1:0] z_int;

    always_comb begin
        inv_x0 = x[0] ^ 1'b1;
        inv_y0 = y[0] ^ 1'b1;    
    end

    abr_masked_AND and_inst0 (
        .clk(clk),
        .rst_n(rst_n),
        .zeroize(zeroize),
        .x({x[1], inv_x0}),
        .y({y[1], inv_y0}),
        .rnd(rnd),
        .c(z_int)
    );

    always_comb z[0] = z_int[0];
    always_comb z[1] = z_int[1] ^ 1'b1;

endmodule