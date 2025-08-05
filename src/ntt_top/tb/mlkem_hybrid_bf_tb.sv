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
//mlkem_hybrid_bf_tb.sv
// --------
//======================================================================

`default_nettype none

module mlkem_hybrid_bf_tb 
    import ntt_defines_pkg::*;
    import abr_params_pkg::*;
    ();

    // Testbench signals
    parameter CLK_HALF_PERIOD = 5;
    parameter CLK_PERIOD = 2 * CLK_HALF_PERIOD;

    logic clk_tb;
    logic reset_n_tb;
    logic zeroize_tb;
    mode_t mode_tb;
    logic mlkem_tb;
    logic acc_tb;

    logic [11:0] u_tb, v_tb, w_tb;
    logic [22:0] u_o_tb, v_o_tb;
    logic [((MLKEM_Q-1) * (MLKEM_Q-1))+(MLKEM_Q-1)-1:0][11:0] w_array;

    
    ntt_butterfly dut (
        .clk(clk_tb),
        .reset_n(reset_n_tb),
        .zeroize(zeroize_tb),
        .mode(mode_tb),
        .mlkem(mlkem_tb),
        .opu_i(23'(u_tb)),
        .opv_i(23'(v_tb)),
        .opw_i(23'(w_tb)),
        .accumulate(acc_tb),
        .u_o(u_o_tb),
        .v_o(v_o_tb),
        .pwm_res_o()
    );

    //----------------------------------------------------------------
// clk_gen
//
// Always running clock generator process.
//----------------------------------------------------------------
always
begin : clk_gen
  #CLK_HALF_PERIOD;
  clk_tb = !clk_tb;
end // clk_gen

//----------------------------------------------------------------
// reset_dut()
//
// Toggle reset to put the DUT into a well known state.
//----------------------------------------------------------------
task reset_dut;
begin
  $display("*** Toggle reset.");
  reset_n_tb = 0;


  #(2 * CLK_PERIOD);
  reset_n_tb = 1;

  $display("End of reset");
end
endtask // reset_dut

//----------------------------------------------------------------
// init_sim()
//
// Initialize all counters and testbed functionality as well
// as setting the DUT inputs to defined values.
//----------------------------------------------------------------
  task init_sim;
    int i;
    begin
        $display("Start of init");
        clk_tb        = 0;
        reset_n_tb    = 0;
        mode_tb = ct;
        zeroize_tb = 1'b0;
        mlkem_tb = 1'b0;
        acc_tb = 1'b0;
        
        u_tb = '0;
        v_tb = '0;
        w_tb = '0;
        $display("End of init");
    end
endtask

task ct_test(input logic mlkem);
    
    logic [22:0] exp_u_o_tb, exp_v_o_tb;
    int err_ctr = 0;

    begin
        $display("Start of ct_test");
        mode_tb = ct;
        mlkem_tb = mlkem;
        
        // Set inputs
        #CLK_HALF_PERIOD;
        #CLK_HALF_PERIOD;
        #CLK_PERIOD;
        @(posedge clk_tb);
        fork
            begin
                for (int i = 0; i < MLKEM_Q; i++) begin
                    for (int j = 0; j < MLKEM_Q; j++) begin
                        w_array[j+(i*j)] = $urandom() % MLKEM_Q;
                        u_tb <= i;
                        v_tb <= j;
                        w_tb <= w_array[j+(i*j)];

                        @(posedge clk_tb);
                    end
                end
            end
            begin
                #CLK_HALF_PERIOD;
                $display("Waiting for results to be ready...");
                repeat(4) @(posedge clk_tb);
                $display("Proceeding with checks...");

                for (int i = 0; i < MLKEM_Q; i++) begin
                    for (int j = 0; j < MLKEM_Q; j++) begin
                        exp_u_o_tb = (i + ((j*w_array[j+(i*j)])%MLKEM_Q)) % MLKEM_Q;
                        if (i >= j*w_array[j+(i*j)]%MLKEM_Q)
                            exp_v_o_tb = (i - ((j*w_array[j+(i*j)])%MLKEM_Q)) % MLKEM_Q;
                        else
                            exp_v_o_tb = ((i - ((j*w_array[j+(i*j)])%MLKEM_Q)+MLKEM_Q));


                        if (u_o_tb[11:0] != exp_u_o_tb) begin
                            $display("Error: u_o mismatch at i=%0x, j=%0x, w=%0x: expected %0x, got %0x", i, j, w_array[j+(i*j)], exp_u_o_tb, u_o_tb[11:0]);
                            err_ctr++;
                        end

                        if (v_o_tb[11:0] != exp_v_o_tb) begin
                            $display("Error: v_o mismatch at i=%0x, j=%0x, w=%0x: expected %0x, got %0x", i, j, w_array[j+(i*j)], exp_v_o_tb, v_o_tb[11:0]);
                            err_ctr++;
                        end
                        
                        @(posedge clk_tb);
                    end
                end
            end
        join

        if (err_ctr == 0) begin
            $display("CT test passed with no errors.");
        end else begin
            $display("CT test failed with %0d errors.", err_ctr);
        end
        $display("End of ct_test");

    end
endtask

//----------------------------------------------------------------
function logic [11:0] div2(input logic [11:0] in);
    // Divide the input by 2, rounding down
    if (in[0] == 1'b1) begin
        div2 = (in >> 1) + ((MLKEM_Q + 1)/2);
    end
    else
        div2 = in >> 1; // If even, just shift right
endfunction

//---------------------------------------------------------
task gs_test(input logic mlkem);
    
    logic [22:0] exp_u_o_tb, exp_v_o_tb;
    int err_ctr = 0;

    begin
        $display("Start of gs_test");
        mode_tb = gs;
        mlkem_tb = mlkem;
        
        // Set inputs
        #CLK_HALF_PERIOD;
        #CLK_HALF_PERIOD;
        #CLK_PERIOD;
        @(posedge clk_tb);
        fork
            begin
                for (int i = 0; i < MLKEM_Q; i++) begin
                    for (int j = 0; j < MLKEM_Q; j++) begin
                        w_array[j+(i*j)] = $urandom() % MLKEM_Q;
                        u_tb <= i;
                        v_tb <= j;
                        w_tb <= w_array[j+(i*j)];

                        @(posedge clk_tb);
                    end
                end
            end
            begin
                #CLK_HALF_PERIOD;
                $display("Waiting for results to be ready...");
                repeat(4) @(posedge clk_tb);
                $display("Proceeding with checks...");

                for (int i = 0; i < MLKEM_Q; i++) begin
                    for (int j = 0; j < MLKEM_Q; j++) begin
                        exp_u_o_tb = div2((i + j) % MLKEM_Q);
                        if (i >= j)
                            exp_v_o_tb = div2((((i - j) % MLKEM_Q)*w_array[j+(i*j)])% MLKEM_Q);
                        else
                            exp_v_o_tb = div2(((i - j)+MLKEM_Q)*w_array[j+(i*j)] % MLKEM_Q);


                        if (u_o_tb[11:0] != exp_u_o_tb) begin
                            $display("Error: u_o mismatch at i=%0x, j=%0x, w=%0x: expected %0x, got %0x", i, j, w_array[j+(i*j)], exp_u_o_tb, u_o_tb[11:0]);
                            err_ctr++;
                        end

                        if (v_o_tb[11:0] != exp_v_o_tb) begin
                            $display("Error: v_o mismatch at i=%0x, j=%0x, w=%0x: expected %0x, got %0x", i, j, w_array[j+(i*j)], exp_v_o_tb, v_o_tb[11:0]);
                            err_ctr++;
                        end
                        
                        @(posedge clk_tb);
                    end
                end
            end
        join

        if (err_ctr == 0) begin
            $display("GS test passed with no errors.");
        end else begin
            $display("GS test failed with %0d errors.", err_ctr);
        end
        $display("End of gs_test");

    end
endtask

//----------------------------------------------------------------


initial begin
    init_sim();
    reset_dut();
    // Run the test
    ct_test(1'b1); // MLKEM CT test
    gs_test(1'b1); // MLKEM GS test

    $display("End of hybrid_bf_tb");
    $finish;
end

endmodule