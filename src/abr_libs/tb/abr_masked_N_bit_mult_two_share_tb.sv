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

module abr_masked_N_bit_mult_two_share_tb;

    // Parameters
    localparam WIDTH = 22;
    localparam HALF_WIDTH = WIDTH/2;
    localparam MOD = 2**WIDTH;
    localparam NUM_OF_TEST_VECTOR = 32'd0_100_000;
    localparam DEBUG = 0;

    // Testbench signals
    logic clk;
    logic rst_n;
    logic zeroize;
    logic [1:0] x [WIDTH-1:0];
    logic [1:0] y [WIDTH-1:0];
    logic [1:0] z [WIDTH-1:0];
    logic [WIDTH-1:0] expected_z;
    logic [WIDTH-1:0] actual_z;
    logic [WIDTH-1:0] random_tb;
    logic [HALF_WIDTH-1:0] actual_input, actual_y;
    logic [WIDTH-1:0] x0, y0, z0, tmp0, y_tmp0;
    logic [WIDTH-1:0] x1, y1, z1, tmp1, y_tmp1;

    // Queue to store inputs
    typedef struct {
      logic [1:0] x [WIDTH-1:0];
      logic [1:0] y [WIDTH-1:0];
    } input_t;
    input_t input_queue [(WIDTH + 2)];

    input_t inputs;

    // Instantiate the DUT (Device Under Test)
    abr_masked_N_bit_mult_two_share #(
      .WIDTH(WIDTH)
    ) dut (
      .clk(clk),
      .rst_n(rst_n),
      .zeroize(zeroize),
      .random(random_tb),
      .x(x),
      .y(y),
      .z(z)
    );

    // Clock generation
    always #5 clk = ~clk;

    // Task to initialize the inputs
    task initialize_inputs();
      integer i;
      begin
        rst_n = 1;
        zeroize = 0;
        
        expected_z = 'h0;
        actual_z = 'h0;
        for (i = 0; i < WIDTH; i = i + 1) begin
          x[i] = 2'b00;
          y[i] = 2'h0;
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
        // Drive inputs and push into queue
        begin
          for (int i = 0; i < num_vectors + 2; i++) begin
            @(posedge clk);
            #3;
            if (i < num_vectors) begin
                // Generate random inputs
                random_tb = $random;
                actual_input = $random;
                actual_y = $random;
                tmp1 = $random;
                tmp0 = (actual_input - tmp1) % MOD;
                for (int j = 0; j < WIDTH; j = j + 1) begin
                    x[j] = {tmp1[j], tmp0[j]};
                end
                y_tmp1 = $random;
                y_tmp0 = (actual_y - y_tmp1) % MOD;
                for (int j = 0; j < WIDTH; j = j+1) begin
                  y[j] = {y_tmp1[j], y_tmp0[j]};
                end

                // Shift left and insert new inputs
                for (int j = WIDTH + 1; j > 0; j = j - 1) begin
                    input_queue[j] = input_queue[j - 1];
                end
                input_queue[0] = '{x: x, y: y};

                if (DEBUG) $display("[%0t] Input pushed: x = %d ({%d,%d}), y = %d ({%d,%d})", $time, actual_input, tmp0, tmp1, actual_y, y_tmp0, y_tmp1);
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
          repeat (1) @(negedge clk);
          for (int i = 0; i < num_vectors; i++) begin
            @(negedge clk);

            // Access inputs from the queue
            inputs = input_queue[1];
            
            for (int i = 0; i < WIDTH; i++) begin
                x0[i] = inputs.x[i][0];
                x1[i] = inputs.x[i][1];

                y0[i] = inputs.y[i][0];
                y1[i] = inputs.y[i][1];
            end
            if (DEBUG) $display("[%0t] Input popped: x = %d, y = %d", $time, (x0+x1) % MOD, (y0+y1)%MOD);

            // Compare the results (you can define the expected results based on your logic)
            #2; // Wait for outputs to stabilize
            expected_z = ((x0 + x1) * (y0+y1)) % MOD;
            for (int j = 0; j < WIDTH; j = j + 1) begin                
                z0[j] = z[j][0];
                z1[j] = z[j][1];
            end
            actual_z = (z0 + z1) % MOD;

            // Placeholder for comparison logic
            if (actual_z !== expected_z) begin
              $display("[%0t] Error: Expected z = %p, got %p", $time, expected_z, actual_z);
            end
            else begin
              if (DEBUG) $display("[%0t] Correct: z = %p", $time, actual_z);
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
