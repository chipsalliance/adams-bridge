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
// ntt_masked_mult_redux46_auto_tb.sv
// --------
//
//
//======================================================================

module ntt_masked_mult_redux46_auto_tb;

    // Parameters
    parameter WIDTH = 46;
    parameter WIDTH_RND = 63;
    parameter PRIME = 23'd8380417;
    parameter LATENCY = 156;
    parameter NUM_OF_TEST_VECTOR = 1000000;

    // Clock and reset
    reg clk;
    reg rst_n;

    // Inputs and outputs
    reg zeroize;    
    reg [WIDTH_RND-1:0] rnd;
    reg [(WIDTH/2)*3-1:0] rnd_width3;
    reg [WIDTH-1:0] actual_input;
    reg [WIDTH-1:0] random_mask;
    reg [WIDTH/2-1:0] expected_output;
    reg [WIDTH/2-1:0] expected_output_shift_reg [0:LATENCY-1];
    integer cycle_count;

    // Masked input shares
    logic [1:0] x_share [WIDTH-1:0];
    wire [1:0] y_share [WIDTH/2-1:0];
    logic [WIDTH/2-1:0] y;

    // Assign x_share and reconstruct y
    always_comb begin
        for (int i = 0; i < WIDTH; i = i + 1) begin
            x_share[i][0] = actual_input[i] ^ random_mask[i];
            x_share[i][1] = random_mask[i];
        end
        for (int i = 0; i < WIDTH/2; i = i + 1) begin
            y[i] = y_share[i][0] ^ y_share[i][1];
        end
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
        .rnd_3WIDTH(rnd_width3),
        .x(x_share),
        .y(y_share)
    );

    // Clock generation
    always #5 clk = ~clk;

    // Testbench logic
    always @(posedge clk) begin
        if (!rst_n) begin
            cycle_count <= 0;
            // Initialize shift registers
            for (int i = 0; i < LATENCY; i = i + 1) begin
                expected_output_shift_reg[i] <= 0;
            end
        end else begin
            // Generate new inputs
            actual_input <= {$urandom, $urandom} % (PRIME**2);
            random_mask <= {$urandom, $urandom};

            // Compute expected output
            expected_output <= actual_input % PRIME;

            // Shift the expected outputs
            for (int i = LATENCY-1; i > 0; i = i - 1) begin
                expected_output_shift_reg[i] <= expected_output_shift_reg[i - 1];
            end

            // Store new expected output
            expected_output_shift_reg[0] <= expected_output;

            // Provide random numbers
            rnd <= {$urandom, $urandom, $urandom};
            rnd_width3 <= {$urandom, $urandom, $urandom};

            // Compare output after latency
            if (cycle_count >= LATENCY+2) begin
                if (y !== expected_output_shift_reg[LATENCY-1]) begin
                    $display("Mismatch at cycle %0d: expected %0d, got %0d", cycle_count, expected_output_shift_reg[LATENCY-1], y);
                end
                // else begin
                //     $display("Match at cycle %0d: output %0d", cycle_count, y);
                // end
            end

            cycle_count <= cycle_count + 1;

            if (cycle_count >= NUM_OF_TEST_VECTOR) begin
                $stop;
            end
            if ((cycle_count%10000) == 9999) begin
                $display("Hit the interval %d", cycle_count);
            end
        end
    end

    // Initialize clock and reset
    initial begin
        clk = 0;
        rst_n = 0;
        zeroize = 0;
        cycle_count = 0;
        rnd = '0;
        rnd_width3 = '0;
        #10 rst_n = 1;
    end

endmodule: ntt_masked_mult_redux46_auto_tb
