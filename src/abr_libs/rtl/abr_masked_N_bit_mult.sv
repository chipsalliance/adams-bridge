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
// Module: abr_masked_N_bit_mult
// Description: This module implements a masked N-bit multiplier with one-share masking.
//              The masking technique enhances security by using a random bit to obscure
//              intermediate values, reducing vulnerability to side-channel attacks.
// 
// Functionality:
//  - The module calculates the multiplication operation between WIDTH-bit inputs x and WIDTH/2-bit y.
//  - Intermediate results are not masked since one share is only masked.
//  - Final output is obtained by combining the reshared and masked intermediate results.
//  - It does not require fresh randomness.
//  - This design assumes that x is the secret, while y is the public operands.
//  - It has one cycle latency and can accept a new input set at the every clock.
//
//======================================================================

 module abr_masked_N_bit_mult
    #(parameter WIDTH = 8, parameter HALF_WIDTH = WIDTH/2)  // Parameter to define the width of the operands
    (
        input wire clk,                      // Clock signal
        input wire rst_n,                    // Active low reset signal
        input wire zeroize,                  // Zeroize signal
        input wire [1:0] x [WIDTH-1:0],      // WIDTH-bit arithmetic shares operand x
        input wire [HALF_WIDTH-1:0] y ,      // WIDTH/2-bit unmasked operand y
        output logic [1:0] z [WIDTH-1:0]     // WIDTH-bit arithmetic shares output z
    );

    // Intermediate calculation logic for multiplication operations
    logic  [WIDTH-1:0] calculation [1:0];
    logic [WIDTH-1:0] x0, x1;

    // Format organization stage
    always_comb begin
        for (int i = 0; i < WIDTH; i++) begin
            x0[i] = x[i][0];
            x1[i] = x[i][1];
        end
    end

    // Calculation stage
    always_comb begin
        calculation[0] = x0 * y; // Multiplication of the first share x and y
        calculation[1] = x1 * y; // Multiplication of the second share x and y
    end

    // Final output assignment
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int i = 0; i < WIDTH; i++) begin
                z[i] <= 2'b0;
            end
        end
        else if (zeroize) begin
            for (int i = 0; i < WIDTH; i++) begin
                z[i] <= 2'b0;
            end
        end
        else begin
            for (int i = 0; i < WIDTH; i++) begin
                z[i][0] <= calculation[0][i]; // Pass-through without masking
                z[i][1] <= calculation[1][i]; // Pass-through without masking
            end
        end
    end

endmodule: abr_masked_N_bit_mult
