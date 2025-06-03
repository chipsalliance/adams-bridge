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


`timescale 1ns/1ps

module abr_masked_OR_tb;

    // Parameters
    parameter REG_SIZE = 23;
    parameter MLKEM_REG_SIZE = 12;

    // DUT signals
    logic clk;
    logic reset_n;
    logic zeroize;
    logic rnd;
    logic [1:0] x, y, z;

    // Instantiate DUT
    abr_masked_OR dut (
        .clk(clk),
        .rst_n(reset_n),
        .zeroize(zeroize),
        .rnd(rnd),
        .x(x),
        .y(y),
        .z(z)
    );

    // Clock generation
    always #5 clk = ~clk;

    // Helper function for modular add/sub
    function automatic [REG_SIZE-1:0] or_gate(
        input opa,
        input opb
    );
        begin
            or_gate = opa | opb;
        end
    endfunction

    // Test task
    task automatic run_test();
        int errors = 0;
        int total = 0;
        logic x_in, y_in;
        logic expected;
        // Use small ranges for exhaustive test (full range is too large)
        for (int i = 0; i < 5; i++) begin
            for (int j = 0; j < 1; j++) begin
                // for (l = 0; l < 2; l++) begin // sub_i
                    rnd = $urandom();
                    x_in = $urandom();
                    x[0] = rnd - x_in;
                    x[1] = rnd;

                    y_in = $urandom();
                    y[0] = rnd - y_in;
                    y[1] = rnd;
                    
                    @(negedge clk);
                    
                    expected = or_gate(x[0] ^ x[1], y[0] ^ y[1]);
                    if (z[0] ^ z[1] !== expected) begin
                        $display("ERROR: x=%b, y=%b, z=%b, expected=%b", x, y, z, expected);
                        errors++;
                    end
                    total++;
                    @(negedge clk);
                // end
            end
        end
        $display("Total tests: %0d, Errors: %0d", total, errors);
        if (errors == 0)
            $display("PASS");
        else
            $display("FAIL");
    endtask

    // Main test sequence
    initial begin
        clk = 0;
        reset_n = 0;
        zeroize = 0;
        rnd = 0;
        x = 0;
        y = 0;
        @(negedge clk);
        reset_n = 1;
        @(negedge clk);

        run_test();

        $display("All tests completed.");
        $finish;
    end

endmodule