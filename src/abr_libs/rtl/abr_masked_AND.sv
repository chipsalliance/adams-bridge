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
// Module: abr_masked_AND
// Description: This module implements a masked AND gate with domain-oriented masking.
//              The masking technique enhances security by using a random bit to obscure
//              intermediate values, reducing vulnerability to side-channel attacks.
// 
// 
// Functionality:
//  - The module calculates the AND operation between bits of inputs x and y.
//  - Intermediate results are masked using a random bit to prevent side-channel leakage.
//  - Final output is obtained by combining the reshared and masked intermediate results.
//  - It requires 1-bit fresh randomness for each execution.
//  - It has one cycle latency and can accept a new input set at the every clock.
//
//======================================================================

 module abr_masked_AND
    (
        input wire clk,             // Clock signal
        input wire rst_n,           // Active low reset signal
        input wire zeroize,         // Zeroize signal
        input wire [1:0] x,         // 2-bit input x
        input wire [1:0] y,         // 2-bit input y
        input wire rnd,             // Random bit for masking
        output logic [1:0] c        // 2-bit output c
    );

    // Intermediate calculation logic for AND operations
    logic [3:0] calculation;
    logic [3:0] resharing;
    always_comb begin
        calculation[0] = x[0] & y[0]; // AND of lower bits of x and y
        calculation[1] = x[0] & y[1]; // AND of lower bit of x and upper bit of y
        calculation[2] = x[1] & y[0]; // AND of upper bit of x and lower bit of y
        calculation[3] = x[1] & y[1]; // AND of upper bits of x and y
    end

    // Resharing logic to apply masking
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int i = 0; i < 4; i++) begin
                resharing[i] <= 1'b0;
            end
        end
        else if (zeroize) begin
            for (int i = 0; i < 4; i++) begin
                resharing[i] <= 1'b0;
            end
        end
        else begin
            resharing[0] <= calculation[0];         // Pass-through without masking
            resharing[1] <= calculation[1] ^ rnd;   // Masking with random bit
            resharing[2] <= calculation[2] ^ rnd;   // Masking with random bit
            resharing[3] <= calculation[3];         // Pass-through without masking
        end
    end

    // Final output calculation
    always_comb begin
        c[0] = resharing[0] ^ resharing[1];     // Combining reshared values for c[0]
        c[1] = resharing[2] ^ resharing[3];     // Combining reshared values for c[1]
    end

endmodule: abr_masked_AND
