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

module masked_barrett_redux_tb;

    // Parameters
    parameter REG_SIZE = 23;
    parameter MLKEM_REG_SIZE = 12;
    parameter MASKED_REG_SIZE = 2 * MLKEM_REG_SIZE;

    // DUT signals
    logic clk;
    logic reset_n;
    logic zeroize;
    logic [54:0] rnd_tb;
    logic [23:0] rnd_24bit_tb;
    logic [1:0][MASKED_REG_SIZE-1:0] x;
    logic [1:0][MASKED_REG_SIZE-1:0] y;

    // Instantiate DUT
    masked_barrett_reduction mbr_inst (
        .clk(clk),
        .rst_n(reset_n),
        .zeroize(zeroize),
        .x(x),
        .y(y),
        .rnd_12bit(rnd_tb[11:0]),
        .rnd_14bit(rnd_tb[25:12]),
        .rnd_24bit(rnd_24bit_tb),
        .rnd_for_Boolean0(rnd_tb[39:26]),
        .rnd_for_Boolean1(rnd_tb[53:40]),
        .rnd_1bit(rnd_tb[54])
    );

    // Clock generation
    always #5 clk = ~clk;

    // Helper function for modular add/sub
    function automatic [MASKED_REG_SIZE-1:0] barrett_redux_exp(
        input [MASKED_REG_SIZE-1:0] opa
    );
        begin
            barrett_redux_exp = opa % 3329;
        end
    endfunction

    // Test task
    task automatic run_test();
        int errors = 0;
        int total = 0;
        logic [23:0] x_in = 0;
        logic [499:0][23:0] x_in_array;
        logic [54:0] rnd;
        logic [11:0] expected;
        // Use small ranges for exhaustive test (full range is too large)
        
        fork
            begin
                #10;
                for (int i = 0; i < 500; i++) begin
                    @(posedge clk);
                    rnd = 55'({$urandom(), $urandom()}); //$urandom();
                    x_in = $urandom();
                    x_in_array[i] = x_in;
                    x[0] <= x_in - rnd[23:0];
                    x[1] <= rnd[23:0];
                    // $display("Driving inputs for index %0d at time %t",i, $time);
                    rnd_tb = rnd;
                    rnd_24bit_tb = 24'($urandom());
                end
            end
            begin
                repeat(8) @(posedge clk);
                for (int i = 0; i < 500; i++)  begin
                    expected = barrett_redux_exp(x_in_array[i]);
                    
                    // expected = barrett_redux_exp(x[0] + x[1]);
                    if (y[0] + y[1] !== expected) begin
                        $display("========================");
                        $display("x_in_array = %h for index %0d at time %t", x_in_array[i], i, $time);
                        $display("Error: Expected %0x, got %0x at i=%0d, at time %t", expected, y[0] + y[1], i,  $time);
                        $display("========================");
                        errors++;
                    end
                    total++;
                    @(posedge clk);
                end
            end
        join

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
        rnd_tb = 0;
        rnd_24bit_tb = 0;
        x = 0;

        @(posedge clk);
        reset_n = 1;
        @(posedge clk);

        run_test();

        $display("All tests completed.");
        $finish;
    end

endmodule