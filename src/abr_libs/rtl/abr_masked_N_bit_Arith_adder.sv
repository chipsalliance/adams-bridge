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
// Module: abr_masked_N_bit_Arith_adder
// Description: This module performs addition of two arithmetic shared inputs, producing an arithmetic shared output.
// 
// 
// Functionality:
//  - It takes 1 cycle latency (due to output flop)
//  - It does not require fresh randomness for every execution since inputs are already split
//
//======================================================================

 module abr_masked_N_bit_Arith_adder #(
    parameter WIDTH = 8 // Default width is 8 bits
)(
    input wire clk,                    // Clock signal
    input wire rst_n,                  // Active low reset signal
    input wire zeroize,                // Zeroize signal
    input wire [1:0][WIDTH-1:0] x,     // WIDTH-bit input operand x
    input wire [1:0][WIDTH-1:0] y,     // WIDTH-bit input operand y

    output logic [1:0][WIDTH-1:0] s 
);

    logic [1:0][WIDTH-1:0] add_res;
    logic [1:0] s_reg [WIDTH-1:0];

    always_comb begin
        add_res[0] = x[0] + y[0];
        add_res[1] = x[1] + y[1];
    end

    // Final output assignment
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            s <= 'h0;
        end
        else if (zeroize) begin
            s <= 'h0;
        end
        else begin
            s <= add_res;
        end
    end


endmodule : abr_masked_N_bit_Arith_adder
