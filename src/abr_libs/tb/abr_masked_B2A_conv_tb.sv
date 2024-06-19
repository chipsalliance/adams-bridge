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


module abr_masked_B2A_conv_tb;

    // Parameters
    localparam WIDTH = 8;
    localparam MOD = 2**WIDTH;
    localparam NUM_OF_TEST_VECTOR = 32'd1_000_000;
    localparam DEBUG = 0;
  
    // Testbench signals
    logic clk;
    logic rst_n;
    logic zeroize;
    logic [WIDTH-1:0] rnd;
    logic [1:0] x_boolean [WIDTH-1:0];
    logic [1:0] A [WIDTH-1:0];
    logic [WIDTH-1:0] expected_A;
    logic [WIDTH-1:0] actual_A;
    logic [WIDTH-1:0] A0;
    logic [WIDTH-1:0] A1;
  
    // Queue to store inputs
    typedef struct {
      logic [1:0] x_boolean [WIDTH-1:0];
      logic [WIDTH-1:0] rnd;
    } input_t;
    input_t input_queue [(WIDTH + 2)];
  
    input_t inputs;
  
    // Instantiate the DUT (Device Under Test)
    abr_masked_B2A_conv #(
      .WIDTH(WIDTH)
    ) dut (
      .clk(clk),
      .rst_n(rst_n),
      .zeroize(zeroize),
      .rnd(rnd),
      .x_boolean(x_boolean),
      .x_arith(A)
    );
  
    // Clock generation
    always #5 clk = ~clk;
  
    // Task to initialize the inputs
    task initialize_inputs();
      integer i;
      begin
        rst_n = 1;
        zeroize = 0;
        rnd = 'h0;
        expected_A = 'h0;
        actual_A = 'h0;
        for (i = 0; i < WIDTH; i = i + 1) begin
          x_boolean[i] = 2'b00;
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
    task perform_test(input int num_vectors);
        
      fork
        // Refresh the randomness
        begin
            for (int i = 0; i < num_vectors + 3; i++) begin
                @(posedge clk);
                #1;
                rnd = $random;
            end
        end
        // Drive inputs and push into queue
        begin
          for (int i = 0; i < num_vectors + 3; i++) begin
            @(posedge clk);
            #3;
            if (i < num_vectors) begin
              // Generate random inputs
              for (int j = 0; j < WIDTH; j = j + 1) begin
                x_boolean[j] = $random;
              end
  
              // Shift left and insert new inputs
              for (int j = WIDTH + 1; j > 0; j = j - 1) begin
                input_queue[j] = input_queue[j - 1];
              end
              input_queue[0] = '{x_boolean: x_boolean, rnd: rnd};
  
              if (DEBUG) $display("[%0t] Input pushed: x_boolean = %p, rnd = %0b", $time, x_boolean, rnd);
            end
            else begin
              // Shift left and insert new inputs
              for (int j = WIDTH + 1; j > 0; j = j - 1) begin
                input_queue[j] = input_queue[j - 1];
              end
            end
          end
        end
  
        // Collect results and compare
        begin
          repeat (2) @(negedge clk);
          for (int i = 0; i < num_vectors; i++) begin
            @(negedge clk);
  
            // Access inputs from the queue
            inputs = input_queue[2];
            if (DEBUG) $display("[%0t] Input popped: x_boolean = %p, rnd = %0b", $time, inputs.x_boolean, inputs.rnd);
  
            // Compare the results (you can define the expected results based on your logic)
            #2; // Wait for outputs to stabilize
            for (int j = 0; j < WIDTH; j = j + 1) begin
                expected_A[j] = inputs.x_boolean[j][0] ^ inputs.x_boolean[j][1];
                A0[j] = A[j][0];
                A1[j] = A[j][1];
            end
            actual_A = (A0+A1) % MOD;
  
            //Placeholder for comparison logic
            if (actual_A !== expected_A) begin
              $display("[%0t] Error: Expected A = %p, got %p", $time, expected_A, actual_A);
            end
            else begin
              if (DEBUG) $display("[%0t] Correct: A = %p", $time, actual_A);
            end
          end
        end
      join
    endtask
  
    // Initial block to control the simulation
    initial begin
      // Initialize the clock
      clk = 0;
  
      // Initialize inputs
      initialize_inputs();
  
      // Apply reset
      apply_reset();
      #10;
  
      // Perform test with specified number of vectors
      perform_test(NUM_OF_TEST_VECTOR);
  
      // Wait for some time to observe the outputs
      #100;
  
      // Finish the simulation
      $finish;
    end
  
  endmodule
  