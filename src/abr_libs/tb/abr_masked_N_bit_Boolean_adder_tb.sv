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

module abr_masked_N_bit_Boolean_adder_tb;

    // Parameter for the width of the ripple-carry adder
    localparam WIDTH = 15;
    localparam MOD = (2**WIDTH);


    // DEBUG flag and number of test vector
    localparam DEBUG = 0;
    localparam NUM_OF_TEST_VECTOR = 32'd1_000_000;

    // Testbench signals
    logic clk;
    logic rst_n;
    logic zeroize;
    logic [1:0] x [WIDTH-1:0];
    logic [1:0] y [WIDTH-1:0];
    logic [WIDTH-1:0] rnd;
    logic [1:0] s [WIDTH-1:0];

    // Queue to store inputs
    typedef struct {
        logic [WIDTH-1:0] x_comb;
        logic [WIDTH-1:0] y_comb;
    } input_t;
    input_t input_queue[(WIDTH + 2)];

    // Instantiate the DUT (Device Under Test)
    abr_masked_N_bit_Boolean_adder #(
        .WIDTH(WIDTH)
    ) dut (
        .clk(clk),
        .rst_n(rst_n),
        .zeroize(zeroize),
        .x(x),
        .y(y),
        .rnd(rnd),
        .s(s)
    );

    // Clock generation
    always #5 clk = ~clk;

    // Task to initialize the inputs
    task initialize_inputs();
        integer i;
        begin
            rst_n = 1;
            zeroize = 0;
            for (i = 0; i < WIDTH; i = i + 1) begin
                x[i] = 2'b00;
                y[i] = 2'b00;
                rnd[i] = 1'b0;
            end
        end
    endtask

    // Task to apply a reset
    task apply_reset();
        begin
            rst_n = 0;
            #10;
            rst_n = 1;
        end
    endtask

    // Task to perform test with specified number of vectors
    logic [WIDTH-1:0] x_comb, y_comb;
    logic [WIDTH:0] expected_sum; // One extra bit for carry
    logic [WIDTH:0] actual_sum;   // One extra bit for carry
    input_t inputs;
    task perform_test(input int num_vectors);

        fork
            // Refresh the randomness
            begin
                for (int i = 0; i < num_vectors + (WIDTH + 2); i++) begin
                    @(posedge clk);
                    #1;
                    rnd = $random;
                end
            end
            // Drive inputs and push into queue
            begin
                for (int i = 0; i < num_vectors + (WIDTH + 2); i++) begin
                    @(posedge clk);
                    if (i < num_vectors) begin
                        x_comb = $random;
                        y_comb = $random;
                        for (int j = 0; j < WIDTH; j = j + 1) begin
                            x[j] = {1'b0, x_comb[j]};
                            y[j] = {1'b0, y_comb[j]};
                            rnd[j] = 0;
                        end
                        // Shift left and insert new inputs
                        for (int j = WIDTH + 1; j > 0; j = j - 1) begin
                            input_queue[j] = input_queue[j-1];
                        end
                        input_queue[0] = '{x_comb: x_comb, y_comb: y_comb};
                        if (DEBUG) $display("[%0t] Input pushed: x_comb = %0b, y_comb = %0b", $time, x_comb, y_comb);
                    end
                    else begin
                        // Shift left and insert new inputs
                        for (int j = WIDTH + 1; j > 0; j = j - 1) begin
                            input_queue[j] = input_queue[j-1];
                        end
                    end
                end
            end

            // Collect results, perform addition, and compare
            begin
                repeat (WIDTH+1) @(posedge clk);
                for (int i = 0; i < num_vectors; i++) begin
                    @(posedge clk);

                    // Access inputs from the queue
                    inputs = input_queue[WIDTH+1];
                    if (DEBUG) $display("[%0t] Input poped: x_comb = %0b, y_comb = %0b", $time, inputs.x_comb, inputs.y_comb);

                    // Calculate expected results
                    expected_sum = (inputs.x_comb + inputs.y_comb) % MOD;
                    #1;

                    // Combine the shares
                    actual_sum = (s[WIDTH-1][0] ^ s[WIDTH-1][1]);
                    for (int j = WIDTH-2; j >= 0; j = j - 1) begin
                        actual_sum = {actual_sum, (s[j][0] ^ s[j][1])};
                    end

                    // Compare the results
                    if (actual_sum !== expected_sum) begin
                        $display("[%0t] Error: Expected sum = %0b, got %0b", $time, expected_sum, actual_sum);
                    end
                    else begin
                        if (DEBUG) $display("[%0t] Correct: sum = %0b", $time, actual_sum);
                    end
                end
            end
        join
    endtask

    // Initial block to control the simulation
    initial begin
        // Initialize the clock
        $display("abr_masked_N_bit_Boolean_adder TEST started");
        clk = 0;

        // Initialize inputs
        initialize_inputs();

        // Apply reset
        apply_reset();

        // Perform test with specified number of vectors
        perform_test(NUM_OF_TEST_VECTOR);

        // Wait for some time to observe the outputs
        #100;

        // Finish the simulation
        $finish;
    end

endmodule
