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
// abr_delay_masked_shares
// Buffers the masked shares for the N cycle
//======================================================================

module abr_delay_masked_shares
#(
    parameter WIDTH = 46,  // Width of the input array
    parameter N = 5        // Number of cycles to delay
)
(
    input  wire clk,
    input  wire rst_n,
    input  wire zeroize,
    input  wire [1:0] input_reg [WIDTH-1:0], // Input signal
    output logic [1:0] delayed_reg [WIDTH-1:0] // Delayed output
);

    // Create an array of shift registers to store the delayed values
    logic [N-1:0][WIDTH-1:0][1:0] shift_reg ;

    // Use an always_ff block to implement the shift register
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            // Reset all shift register values to 0
            for (int j = 0; j < N; j = j + 1) begin
                shift_reg[j] <= '0;
            end
        end
        else if (zeroize) begin
            // Reset all shift register values to 0
            for (int j = 0; j < N; j = j + 1) begin
                shift_reg[j] <= '0;
            end
        end
        else begin
            // Shift the values through the registers
            for (int j = 0; j < N-1; j = j + 1) begin
                shift_reg[j+1] <= shift_reg[j];
            end

            // Load the input values into the first shift register stage
            for (int i = 0; i < WIDTH; i = i + 1) begin
                shift_reg[0][i] <= input_reg[i];
            end
        end
    end

    // Assign the output to the last stage of the shift register
    always_comb begin
        for (int i = 0; i < WIDTH; i = i + 1) begin
            delayed_reg[i] = shift_reg[N-1][i];
        end
    end

endmodule: abr_delay_masked_shares