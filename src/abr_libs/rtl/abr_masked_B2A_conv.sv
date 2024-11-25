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
// Module: abr_masked_B2A_conv
// Description: This module implements a masked B2A (Boolean to Arithmetic) conversion
//              based on the Goblin B2A masking conversion technique. The purpose of this
//              technique is to enhance security by obscuring intermediate values using
//              random bits, thereby reducing vulnerability to side-channel attacks.
// 
// Functionality:
//  - The module takes input x (first-order masked) and rnd (Gamma), and computes masked intermediate values.
//  - It uses a pipelined architecture to ensure high throughput and efficiency.
//  - Intermediate results are stored in a 2-D array for organized pipeline stages.
//  - The module includes zeroize and asynchronous reset functionality to ensure secure and
//    reliable operation.
//  - Final output values are calculated after three pipeline stages and provided at the
//    outputs A and r.
//
//======================================================================
`define DEBUG_MASKING 1
 module abr_masked_B2A_conv #(
    parameter WIDTH = 8 // Default width is 8 bits
)(
    input wire               clk,
    input wire               rst_n,
    input wire               zeroize,

    input wire [WIDTH-1:0]   rnd,
    input wire [1:0]         x_boolean [WIDTH-1:0], // First-order masked input
    
    output logic [1:0]       x_arith [WIDTH-1:0]  // Output A and r
);
    
    logic unsigned [WIDTH-1:0] T0, T1, T2, A0, A1, A2, Gamma_reg, Gamma_reg2, x0, x1;
    logic unsigned [1:0]       x_arith_next [WIDTH-1:0];
    wire [WIDTH-1:0]   Gamma;
    assign Gamma = rnd;

     // Register inputs
    always_ff @ (posedge clk or negedge rst_n) begin            
        if (!rst_n) begin
            for (int i = 0; i < WIDTH; i++) begin
                Gamma_reg[i]    <= 'h0;
                x0[i]           <= 'h0;
                x1[i]           <= 'h0;
                x_arith[i]      <= 'h0;
            end
        end
        else if (zeroize) begin
            for (int i = 0; i < WIDTH; i++) begin
                Gamma_reg[i]    <= 'h0;
                x0[i]           <= 'h0;
                x1[i]           <= 'h0;
                x_arith[i]      <= 'h0;
            end
        end
        else begin
            for (int i = 0; i < WIDTH; i++) begin
                Gamma_reg[i]    <= Gamma[i];
                x0[i]           <= x_boolean[i][0];
                x1[i]           <= x_boolean[i][1];
                x_arith[i]      <= x_arith_next[i];
            end
        end
    end

    // Combinational logic
    always_comb begin
        
            T0               = x0 ^ Gamma_reg;              // T = x' ⊕ Γ
            T1               = T0 - Gamma_reg;              // T = T - Γ
            T2               = T1 ^ x0;                     // T = T ⊕ x'
            Gamma_reg2       = Gamma_reg ^ x1;              // Γ = Γ ⊕ r
            A0               = x0 ^ Gamma_reg2;             // A = x' ⊕ Γ
            A1               = A0 - Gamma_reg2;             // A = A - Γ
            A2               = A1 ^ T2;                     // A = A ⊕ T
        for (int i = 0; i < WIDTH; i++) begin
            x_arith_next[i][0]  = A2[i];                    // Assign A to the output
            x_arith_next[i][1]  = x1[i];                    // Assign r to the output
        end
    end

endmodule
