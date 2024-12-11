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
// Module: abr_masked_N_bit_mult_two_share
// Description: This module implements a masked N-bit multiplier with two-share masking.
//              The masking technique enhances security by using a random bit to obscure
//              intermediate values, reducing vulnerability to side-channel attacks.
// 
// Functionality:
//  - The module calculates the multiplication operation between WIDTH-bit inputs x and y.
//  - Intermediate results are masked since two shares are masked.
//  - Final output is obtained by combining the reshared and masked intermediate results.
//  - It requires fresh randomness.
//  - This design assumes that both x and y are secret, although y input from top level is usually public 
//  - It has two cycle latency and can accept a new input set at every clock.
//
//======================================================================

 module abr_masked_N_bit_mult_two_share
    #(parameter WIDTH = 8)  // Parameter to define the width of the operands
    (
        input wire clk,                         // Clock signal
        input wire rst_n,                       // Active low reset signal
        input wire zeroize,                     // Zeroize signal
        input wire        [WIDTH-1:0] random,   // Intermediate randomness
        input wire   [1:0][WIDTH-1:0] x,        // WIDTH-bit arithmetic shares operand x
        input wire   [1:0][WIDTH-1:0] y,        // WIDTH-bit arithmetic shares operand y
        output logic [1:0] z [WIDTH-1:0]        // WIDTH-bit arithmetic shares output z
    );

    // Intermediate calculation logic for multiplication operations
    logic [WIDTH-1:0] calculation [3:0];
    logic [WIDTH-1:0] calculation_reg [1:0];
    logic [WIDTH-1:0] calculation_rand [1:0];
    logic [WIDTH-1:0] final_res [1:0];
    logic [WIDTH-1:0] x0, x1, y0, y1;

    // Calculation stage
    always_comb begin
        calculation[0] = WIDTH'(x[0] * y[0]); // Multiplication of the first share x and first share y
        calculation[1] = WIDTH'(x[1] * y[0]); // Multiplication of the second share x and first share y
        calculation[2] = WIDTH'(x[0] * y[1]); // Multiplication of the first share x and second share y
        calculation[3] = WIDTH'(x[1] * y[1]); // Multiplication of the second share x and second share y
    end
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int i = 0; i < 2; i++) begin
                calculation_rand[i] <= 'h0;
                calculation_reg[i] <= 'h0;
            end
        end
        else if (zeroize) begin
            for (int i = 0; i < 2; i++) begin
                calculation_rand[i] <= 'h0;
                calculation_reg[i] <= 'h0;
            end
        end
        else begin
            calculation_rand[0] <= calculation[2] + random;
            calculation_rand[1] <= calculation[1] - random;
            calculation_reg[0]  <= calculation[0];
            calculation_reg[1]  <= calculation[3];
        end
    end
    always_comb begin
        final_res[0] = calculation_reg[0] + calculation_rand[0];
        final_res[1] = calculation_reg[1] + calculation_rand[1];
    end

    // Final output assignment
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int i = 0; i < WIDTH; i++)
                z[i] <= 2'h0;
        end
        else if (zeroize) begin
            for (int i = 0; i < WIDTH; i++)
                z[i] <= 2'h0;
        end
        else begin
            for (int i = 0; i < WIDTH; i++) begin
                z[i][0] <= final_res[0][i];
                z[i][1] <= final_res[1][i];
            end
        end
    end

 endmodule: abr_masked_N_bit_mult_two_share
