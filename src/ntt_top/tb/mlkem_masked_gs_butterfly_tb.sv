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

module mlkem_masked_gs_butterfly_tb;

    // Parameters
    parameter REG_SIZE = 23;
    parameter MLKEM_REG_SIZE = 12;
    parameter MASKED_REG_SIZE = 2 * MLKEM_REG_SIZE;

    // DUT signals
    logic clk;
    logic reset_n;
    logic zeroize;
    logic [4:0][13:0] rnd_tb;
    logic [1:0][MASKED_REG_SIZE-1:0] opu_i, opv_i, opw_i;
    logic [1:0][MASKED_REG_SIZE-1:0] u_o, v_o;

    // Instantiate DUT
    ntt_mlkem_masked_gs_butterfly mlkem_masked_gs_inst (
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .opu_i(opu_i),
        .opv_i(opv_i),
        .opw_i(opw_i),
        .rnd_i(rnd_tb),
        .u_o(u_o),
        .v_o(v_o)
    );

    // Clock generation
    always #5 clk = ~clk;

    // // Helper function for gs butterfly
    // function automatic [MLKEM_REG_SIZE-1:0] gs_bf(
    //     input [MASKED_REG_SIZE-1:0] u, v, w
    // );
    //     begin
    //         barrett_redux_exp = opa % 3329;
    //     end
    // endfunction

    // Test task
    task automatic run_test();
        int errors = 0;
        int total = 0;
        logic [23:0] u = 0, v = 0, w = 0;
        logic [499:0][23:0] u_array, v_array, w_array;
        logic [4:0][13:0] rnd;
        logic [23:0] exp_u, exp_v;
        // Use small ranges for exhaustive test (full range is too large)
        
        fork
            begin
                #10;
                for (int i = 0; i < 500; i++) begin
                    @(posedge clk);
                    rnd = 'h0; //55'({$urandom(), $urandom()});
                    u = $urandom() % 'd3329;
                    v = $urandom() % 'd3329;
                    w = $urandom() % 'd3329;
                    u_array[i] = u;
                    v_array[i] = v;
                    w_array[i] = w;

                    opu_i[0] <= u - rnd;
                    opu_i[1] <= rnd;

                    opv_i[0] <= v - rnd;
                    opv_i[1] <= rnd;

                    opw_i[0] <= w - rnd;
                    opw_i[1] <= rnd;
                    
                    // $display("Driving inputs for index %0d at time %t",i, $time);
                    rnd_tb = rnd; //55'({$urandom(), $urandom()});
                    
                    // $display("Wait a clk");
                end
            end
            begin
                repeat(/*25*/17) @(posedge clk); //15+2
                for (int i = 0; i < 500; i++)  begin
                    exp_u = ((u_array[i] + v_array[i]) % 'd3329);
                    if (u_array[i] > v_array[i]) begin
                        exp_v = (((u_array[i] - v_array[i]) % 'd3329) * w_array[i]) % 'd3329;
                    end
                    else begin
                        exp_v = (((u_array[i] - v_array[i]) + 'd3329) * w_array[i]) % 'd3329;;
                    end
                    if (u_o[0] + u_o[1] !== exp_u) begin
                        $display("Error: Expected %0x, got %0x at i=%0d, at time %t", exp_u, u_o[0] + u_o[1], i,  $time);
                        errors++;
                    end
                    if (v_o[0] + v_o[1] !== exp_v) begin
                        $display("Error: Expected %0x, got %0x at i=%0d, at time %t", exp_v, v_o[0] + v_o[1], i,  $time);
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
        opu_i = 0;
        opv_i = 0;
        opw_i = 0;


        @(posedge clk);
        reset_n = 1;
        @(posedge clk);

        run_test();

        $display("All tests completed.");
        $finish;
    end

endmodule