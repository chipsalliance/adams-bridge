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
// ntt_masked_mult_redux46_tb.sv
// --------
//
//
//======================================================================

module ntt_masked_mult_redux46_tb;

    // Parameters
    parameter WIDTH = 46;
    parameter WIDTH_RND = 63;
    parameter PRIME = 23'd8380417;

    // Clock and reset
    reg clk;
    reg rst_n;

    // Inputs and outputs
    reg zeroize;    
    logic [WIDTH_RND-1:0] rnd;
    reg [WIDTH-1:0] x;
    reg [WIDTH/2-1:0] y;    
    reg [WIDTH-1:0] random_mask;
    reg [WIDTH-1:0] actual_input;
    reg [10:0] d_10_0;
    reg [22:0] d_22_0;
    reg [22:0] z_45_23;
    reg [23:0] d_22_0_r0c0;
    reg [23:0] d_22_0_r1c1;
    reg c0c1;
    reg [11:0] c_11_0;
    reg [13:0] f_14_0;
    reg [22:0] e_22_0, res_22_0;

    // Masked input shares
    reg [1:0] x_share [WIDTH-1:0];
    wire [1:0] y_share [WIDTH/2-1:0];

    // Queue to store inputs
    typedef struct {
      logic [1:0] x_boolean [WIDTH-1:0];
      logic [WIDTH-1:0] rnd;
    } input_t;
    input_t input_queue [(WIDTH + 2)];

    always_comb begin
        for (int i = 0; i < WIDTH; i = i + 1) begin
            x_share[i][0] = actual_input[i] ^ random_mask[i];
            x_share[i][1] = random_mask[i];
        end
        for (int i = 0; i < WIDTH/2; i = i + 1) begin
            y[i] = y_share[i][0] ^ y_share[i][1];
        end
        c_11_0 = actual_input[45:43] + actual_input[42:33] + actual_input[32:23] + actual_input[22:13];
        d_10_0 = c_11_0[11:10] + c_11_0[9:0];
        f_14_0 = actual_input[45:43] + actual_input[45:33] + c_11_0[11:10];
        d_22_0_r0c0 = {d_10_0,actual_input[12:0]};
        d_22_0_r1c1 = d_22_0_r0c0 - 23'd8380417;
        c0c1 = d_22_0_r0c0[23] ^ d_22_0_r1c1[23];
        d_22_0 = c0c1 ? d_22_0_r1c1[22:0] : d_22_0_r0c0[22:0];
        e_22_0 = (f_14_0+actual_input[45:23]) % PRIME;
        res_22_0 = (d_22_0 - e_22_0) % PRIME;
        z_45_23 = actual_input[45:23];
    end
    always begin
        @(negedge clk);
        rnd = 0;
    end

    // Instantiate the DUT
    ntt_masked_mult_redux46 #(
        .WIDTH(WIDTH)
    ) dut (
        .clk(clk),
        .rst_n(rst_n),
        .zeroize(zeroize),
        .rnd0_11(rnd[10:0]),
        .rnd1_11(rnd[21:11]),
        .rnd2_11(rnd[32:22]),
        .rnd0_12(rnd[44:33]),
        .rnd0_4(rnd[48:45]),
        .rnd0_14(rnd[62:49]),
        .rnd_3WIDTH(69'h0),
        .x(x_share),
        .y(y_share)
    );

    // Clock generation
    always #5 clk = ~clk;

    // Test vectors
    initial begin
        // Initialize clock and reset
        clk = 0;
        rst_n = 0;
        zeroize = 0;
        
        actual_input = 46'd0;
        random_mask = 0;
        #10 rst_n = 1;
        repeat (3) @(negedge clk);

        @(negedge clk);
        actual_input = 46'd39066633300384;
        random_mask = 0;
        $display("%d and mod(Q) = %d",actual_input, (actual_input % PRIME));
        @(negedge clk);
        actual_input = 46'd36135737955137;
        random_mask = 0;
        $display("%d and mod(Q) = %d",actual_input, (actual_input % PRIME));
        @(negedge clk);
        actual_input = 46'd39840167205202;
        random_mask = 0;
        $display("%d and mod(Q) = %d",actual_input, (actual_input % PRIME));
        
        
        repeat(10000) @(posedge clk);
        #1;
        $stop;
    end




endmodule
