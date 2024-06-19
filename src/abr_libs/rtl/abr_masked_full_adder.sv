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
// Module: abr_masked_full_adder
// Description: This module implements a full adder using domain-oriented masking
//              to enhance security by using a random bit to obscure intermediate values.
//              It uses a masked AND gate and performs addition of three 2-bit operands.
// 
// Functionality:
//  - The module calculates the sum and carry of the inputs x, y, and c_in.
//  - Intermediate results are masked using a random bit to prevent side-channel leakage.
//  - The final output is obtained by combining the reshared and masked intermediate results.
//  - It requires 1-bit fresh randomness for each execution.
//
//======================================================================

 module abr_masked_full_adder (
    input wire clk,             // Clock signal
    input wire rst_n,           // Active low reset signal
    input wire zeroize,         // Zeroize signal
    input wire [1:0] x,         // 2-share of input x
    input wire [1:0] y,         // 2-share of input y
    input wire [1:0] c_in,      // 2-share of carry input
    input wire rnd,             // Random bit for masking
    output logic [1:0] s,       // 2-share of sum output
    output logic [1:0] c_out    // 2-share of carry output
);

    // Internal signals for intermediate operations
    logic [1:0] sum_comb;
    logic [1:0] and_opr1;
    logic [1:0] and_opr2;
    logic [1:0] and_out;

    // Calculate intermediate values for sum and AND operations
    always_comb begin : calculate_sum
        for (int i = 0; i < 2; i++) begin
            and_opr1[i] = x[i] ^ y[i];
            and_opr2[i] = x[i] ^ c_in[i];
            sum_comb[i] = and_opr1[i] ^ c_in[i];
        end
    end

    // Instance of abr_masked_AND
    // It takes one cycle
    abr_masked_AND u_abr_masked_AND (
        .clk(clk),        // Connect clk to clk
        .rst_n(rst_n),    // Connect rst_n to rst_n
        .zeroize(zeroize),// Connect zeroize to zeroize
        .x(and_opr1),     // Connect x to and_opr1
        .y(and_opr2),     // Connect y to and_opr2
        .rnd(rnd),        // Connect rnd to rnd
        .c(and_out)       // Connect c to and_out
    );

    // Pipeline registers to buffer inputs and intermediate sum
    logic [1:0] buffered_x;
    logic [1:0] buffered_sum;
    always_ff @(posedge clk or negedge rst_n) begin : pipeline_inputs
        if (!rst_n) begin
            for (int i = 0; i < 2; i++) begin
                buffered_x[i] <= 1'b0;
                buffered_sum[i] <= 1'b0;
            end
        end
        else if (zeroize) begin
            for (int i = 0; i < 2; i++) begin
                buffered_x[i] <= 1'b0;
                buffered_sum[i] <= 1'b0;
            end
        end
        else begin
            for (int i = 0; i < 2; i++) begin
                buffered_x[i] <= x[i];
                buffered_sum[i] <= sum_comb[i];
            end
        end
    end

    // Calculate and assign the buffered sum and carry outputs
    always_comb begin : calculate_carry
        for (int i = 0; i < 2; i++) begin
            s[i] = buffered_sum[i];
            c_out[i] = buffered_x[i] ^ and_out[i];
        end
    end

endmodule : abr_masked_full_adder
