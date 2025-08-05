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
//mlkem_karatsuba_tb.sv
// --------
//======================================================================

`default_nettype none

module mlkem_karatsuba_tb 
    import ntt_defines_pkg::*;
    import abr_params_pkg::*;
    ();

    // Testbench signals
    parameter CLK_HALF_PERIOD = 5;
    parameter CLK_PERIOD = 2 * CLK_HALF_PERIOD;

    logic clk_tb;
    logic reset_n_tb;
    logic zeroize_tb;
    logic acc_tb;

    logic [11:0] u_tb, v_tb, w_tb;
    logic [22:0] u_o_tb, v_o_tb;
    logic [((MLKEM_Q-1) * (MLKEM_Q-1))+(MLKEM_Q-1)-1:0][11:0] w_array;

    mlkem_pwo_uvwzi_t pwo_uvw_i_tb;
    logic [11:0] zeta_tb;
    mlkem_pwo_t pwo_uv_o_tb;

    
    ntt_karatsuba_pairwm dut (
        .clk(clk_tb),
        .reset_n(reset_n_tb),
        .zeroize(zeroize_tb),
        .accumulate(acc_tb),
        .pwo_uvw_i(pwo_uvw_i_tb),
        .pwo_z_i(zeta_tb),
        .pwo_uv_o(pwo_uv_o_tb)
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
        reset_n_tb    = 1;
        zeroize_tb = 1'b0;
        acc_tb = 1'b0;
        
        pwo_uvw_i_tb.u0_i = '0;
        pwo_uvw_i_tb.u1_i = '0;
        pwo_uvw_i_tb.v0_i = '0;
        pwo_uvw_i_tb.v1_i = '0;
        pwo_uvw_i_tb.w0_i = '0;
        pwo_uvw_i_tb.w1_i = '0;

        zeta_tb = '0;

        for (i = 0; i < ((MLKEM_Q-1) * (MLKEM_Q-1))+(MLKEM_Q-1); i++) begin
            w_array[i] = '0;
        end

        $display("End of init");
    end
endtask

task pairwm_test(input logic acc_en);
    
    logic [22:0] exp_u_o_tb, exp_v_o_tb;
    int err_ctr = 0;

    begin
        $display("Start of pairwm_test");
        acc_tb = acc_en;
        
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
                        // u_tb <= i;
                        // v_tb <= j;
                        // w_tb <= w_array[j+(i*j)];
                        pwo_uvw_i_tb.u0_i <= i;
                        pwo_uvw_i_tb.u1_i <= j;
                        pwo_uvw_i_tb.v0_i <= i;
                        pwo_uvw_i_tb.v1_i <= j;
                        if (acc_en) begin
                            pwo_uvw_i_tb.w0_i <= i;
                            pwo_uvw_i_tb.w1_i <= j;
                        end else begin
                            pwo_uvw_i_tb.w0_i <= 0;
                            pwo_uvw_i_tb.w1_i <= 0;
                        end
                        
                        zeta_tb <= w_array[j+(i*j)];

                        // $display("Setting inputs: u0=%0x, u1=%0x, v0=%0x, v1=%0x, w0=%0x, w1=%0x, zeta=%0x", 
                            // pwo_uvw_i_tb.u0_i, pwo_uvw_i_tb.u1_i, pwo_uvw_i_tb.v0_i, pwo_uvw_i_tb.v1_i,
                            // pwo_uvw_i_tb.w0_i, pwo_uvw_i_tb.w1_i, zeta_tb);

                        @(posedge clk_tb);
                    end
                end
            end
            begin
                #CLK_HALF_PERIOD;
                $display("Waiting for results to be ready...");
                repeat(5) @(posedge clk_tb);
                if (acc_en) @(posedge clk_tb); // Wait for one more cycle if accumulating
                $display("Proceeding with checks...");

                for (int i = 0; i < MLKEM_Q; i++) begin
                    for (int j = 0; j < MLKEM_Q; j++) begin
                        // $display("Calculating exp res with zeta = %0x", w_array[j+(i*j)]);
                        exp_u_o_tb = (((i*i) % MLKEM_Q) + ((((j*j)%MLKEM_Q)*w_array[j+(i*j)])%MLKEM_Q)) % MLKEM_Q;
                        exp_v_o_tb = (((i*j) % MLKEM_Q) + ((i*j) % MLKEM_Q)) % MLKEM_Q;

                        if (acc_en) begin
                            exp_u_o_tb = (exp_u_o_tb + i) % MLKEM_Q;
                            exp_v_o_tb = (exp_v_o_tb + j) % MLKEM_Q;
                        end

                        if (pwo_uv_o_tb.uv0_o != exp_u_o_tb) begin
                            $display("Error: u_o mismatch at i=%0x, j=%0x, w=%0x, zeta=%0x: expected %0x, got %0x", i, j, i, w_array[j+(i*j)], exp_u_o_tb, pwo_uv_o_tb.uv0_o);
                            err_ctr++;
                        end

                        if (pwo_uv_o_tb.uv1_o != exp_v_o_tb) begin
                            $display("Error: v_o mismatch at i=%0x, j=%0x, w=%0x, zeta=%0x: expected %0x, got %0x", i, j, j, w_array[j+(i*j)], exp_v_o_tb, pwo_uv_o_tb.uv1_o);
                            err_ctr++;
                        end
                        
                        @(posedge clk_tb);
                    end
                end
            end
        join

        if (err_ctr == 0) begin
            $display("pairwm_test passed with no errors.");
        end else begin
            $display("pairwm_test failed with %0d errors.", err_ctr);
        end
        $display("End of pairwm_test");

    end
endtask


//----------------------------------------------------------------


initial begin
    init_sim();
    reset_dut();
    // Run the test
    $display("------------------------------");
    pairwm_test(1'b0); // Test without accumulation
    $display("------------------------------");
    init_sim();
    pairwm_test(1'b1); // Test with accumulation

    $display("End of hybrid_bf_tb");
    $finish;
end

endmodule