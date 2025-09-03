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
//======================================================================
//
// mldsa_barrett_reduction_tb.sv
// -----------

module mldsa_barrett_reduction_tb;

    import abr_params_pkg::*;

    // Test Parameters
    localparam int prime = MLDSA_Q;
    localparam int REG_SIZE = $clog2(prime);  // Automatically set
    int NUM_TESTS;

    logic [REG_SIZE-1:0] op_a, op_b;
    logic [2*REG_SIZE-1:0] x_tb;
    logic [REG_SIZE-1:0] inv_tb, r_tb;

    logic [REG_SIZE-1:0] inv_ref, r_ref;

    // Instantiate the DUT
    barrett_reduction #(
        .prime(prime)
    ) dut (
        .x(x_tb),
        .inv(inv_tb),
        .r(r_tb)
    );

    // Test loop
    initial begin
        int errors = 0;

        $display("Testing div_mod_by_const with q = %0d and REG_SIZE = %0d", prime, REG_SIZE);
        $display("mu = %0d", dut.m);
        NUM_TESTS = 20_000_000;

        for (int i = 0; i < NUM_TESTS; i++) begin
            op_a = $urandom_range(0, prime-1);
            op_b = $urandom_range(0, prime-1);
            x_tb = op_a * op_b;

            // Reference calculation using SystemVerilog division
            inv_ref = x_tb / prime;
            r_ref = x_tb % prime;

            #1; // Allow combinational logic to settle

            if (inv_tb !== inv_ref || r_tb !== r_ref) begin
                $fatal(1, "Mismatch for x = %0d: inv_tb = %0d (ref %0d), r = %0d (ref %0d)",
                        x_tb, inv_tb, inv_ref, r_tb, r_ref);
                errors++;
            end
        end

        if (errors == 0) 
        begin
            $display("All %0d tests passed", NUM_TESTS);
            $display("* TESTCASE PASSED");
        end
        else
        begin
            $display("%0d tests failed", errors);
            $display("* TESTCASE FAILED");
        end

        $finish;
    end

endmodule
