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

`default_nettype none

module decompress_tb
    import abr_params_pkg::*;
    import decompress_defines_pkg::*;
    ();

    timeunit 1ns;
    timeprecision 1ps;

    logic [MLKEM_Q_WIDTH-1:0] op_i_tb, op_o_tb;
    decompress_mode_t mode_tb;
    int unsigned error_ctr, check_ctr;

    decompress dut (
        .op_i(op_i_tb),
        .mode(mode_tb),
        .op_o(op_o_tb)
    );

    task automatic check_mode(input decompress_mode_t test_mode,
                              input int unsigned coeff_bits);
        int unsigned expected;

        mode_tb = test_mode;
        for (int unsigned coeff = 0; coeff < (1 << coeff_bits); coeff++) begin
            op_i_tb = MLKEM_Q_WIDTH'(coeff);
            #1;
            if (test_mode == DECOMPRESS12) begin
                expected = coeff % MLKEM_Q;
            end else begin
                expected = ((MLKEM_Q * coeff) + (1 << (coeff_bits - 1))) >> coeff_bits;
            end
            if (op_o_tb !== MLKEM_Q_WIDTH'(expected)) begin
                if (error_ctr < 8) begin
                    $display("Mismatch: mode=%0d input=%0d expected=%0d observed=%0d",
                             test_mode, coeff, expected, op_o_tb);
                end
                error_ctr++;
            end
            check_ctr++;
        end
        $display("Checked all %0d inputs for d=%0d", 1 << coeff_bits, coeff_bits);
    endtask

    initial begin
        error_ctr = 0;
        check_ctr = 0;
        check_mode(DECOMPRESS1, 1);
        check_mode(DECOMPRESS5, 5);
        check_mode(DECOMPRESS11, 11);
        check_mode(DECOMPRESS12, 12);
        if (error_ctr != 0) begin
            $fatal(1, "* TESTCASE FAILED: %0d checks, error_ctr = %0d", check_ctr, error_ctr);
        end
        $display("* TESTCASE PASSED: %0d checks, error_ctr = 0", check_ctr);
        $finish;
    end
endmodule

`default_nettype wire
