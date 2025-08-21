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
// abr_masked_N_bit_Boolean_sub
// Performs Boolean subtraction and check abr_masked_N_bit_Boolean_adder
// for more information about the implementation details
//======================================================================

module abr_masked_N_bit_Boolean_sub #(
    parameter WIDTH = 8 // Default width is 8 bits
)(
    input wire clk,                    // Clock signal
    input wire rst_n,                  // Active low reset signal
    input wire zeroize,                // Zeroize signal
    input wire sub_i,
    input wire [1:0] x [WIDTH-1:0],    // WIDTH-bit input operand x
    input wire [1:0] y [WIDTH-1:0],    // WIDTH-bit input operand y
    input wire [WIDTH-1:0] rnd,        // Random bits for masking

    output logic [1:0] s [WIDTH-1:0]
);

    // Internal signals
    logic  [WIDTH:0] [1:0] carry; // Carry signals for each stage
    logic  [WIDTH-1:0] [1:0] sum; // Sum signals for each stage
    logic  [WIDTH-1:0][WIDTH-1:0][1:0] x_reg; // Pipeline registers for x
    logic  [WIDTH-1:0][WIDTH-1:0][1:0] y_reg; // Pipeline registers for y
    logic  [WIDTH-1:0][WIDTH-1:0][1:0] sum_reg; // Pipeline registers for sum
    logic [1:0] the_last_sum;

    // Initialize the first carry input to 0
    assign carry[0] = sub_i ? 2'b01 : 2'b00;

    // Generate the full adders for each bit
    genvar i;
    generate
        for (i = 0; i < WIDTH; i = i + 1) begin : gen_full_adders
            // Pipeline registers for x and y inputs
            always_ff @(posedge clk or negedge rst_n) begin
                if (!rst_n) begin
                    x_reg[i] <= '0;
                    y_reg[i] <= '0;
                end
                else if (zeroize) begin
                    x_reg[i] <= '0;
                    y_reg[i] <= '0;
                end
                else begin
                    for (int j = 0; j < WIDTH; j = j + 1) begin
                        if (j == 0) begin
                            x_reg[i][j] <= x[i];
                            y_reg[i][j] <= y[i];
                        end
                        else begin
                            x_reg[i][j] <= x_reg[i][j-1];
                            y_reg[i][j] <= y_reg[i][j-1];
                        end
                    end
                end
            end

            // Pipeline registers for sum output
            always_ff @(posedge clk or negedge rst_n) begin
                if (!rst_n) begin
                    sum_reg[i] <= '0;
                end
                else if (zeroize) begin
                    sum_reg[i] <= '0;
                end
                else begin
                    for (int j = i; j < WIDTH; j = j + 1) begin
                        if (j == i && i == WIDTH-1) begin
                            sum_reg[i][j] <= the_last_sum;
                        end
                        else if (j == i) begin
                            sum_reg[i][j] <= sum[i];
                        end
                        else begin
                            sum_reg[i][j] <= sum_reg[i][j-1];
                        end
                    end
                end
            end
            if (i<(WIDTH-1)) begin : gen_masked_full_adder
                // Instance of abr_masked_full_adder
                abr_masked_full_adder u_abr_masked_full_adder (
                    .clk(clk),              // Connect clk to clk
                    .rst_n(rst_n),          // Connect rst_n to rst_n
                    .zeroize(zeroize),      // Connect zeroize to zeroize
                    .x(x_reg[i][i]),        // Connect x to the last stage of the x pipeline
                    .y(y_reg[i][i]),        // Connect y to the last stage of the y pipeline
                    .c_in(carry[i]),        // Connect c_in to carry[i]
                    .rnd(rnd[i]),           // Connect rnd to corresponding random bit
                    .s(sum[i]),             // Connect sum to sum[i]
                    .c_out(carry[i+1])      // Connect carry out to carry[i+1]
                );
            end
        end
    endgenerate

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            the_last_sum    <= 2'b00;
        end
        else if (zeroize) begin
            the_last_sum    <= 2'b00;
        end
        else begin
            the_last_sum <= x_reg[WIDTH-1][WIDTH-1] ^ y_reg[WIDTH-1][WIDTH-1] ^ carry[WIDTH-1];
        end
    end

    // Assign the outputs
    always_comb begin
        for (int i =0; i<WIDTH; i++) begin
            s[i] = sum_reg[i][WIDTH-1];
        end
    end

endmodule : abr_masked_N_bit_Boolean_sub
