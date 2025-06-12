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
//
// compress_tb.sv
// --------

`default_nettype none

module compress_tb
    import abr_params_pkg::*;
    import compress_defines_pkg::*;
    ();

parameter CLK_HALF_PERIOD = 5;
parameter CLK_PERIOD      = 2 * CLK_HALF_PERIOD;

//----------------------------------------------------------------
// Register and Wire declarations.
//----------------------------------------------------------------
reg           clk_tb;
reg           reset_n_tb;
reg           zeroize_tb;
reg           en_tb;
reg [3:0][REG_SIZE-1:0] coeff_tb, mem_wr_data_o;
reg [ABR_MEM_ADDR_WIDTH-1:0] src_base_tb, dest_base_tb;
logic [255:0][REG_SIZE-1:0] coeff_array, coeff_exp;
compress_mode_t mode_tb_dut;
int error_count;

compress_top dut (
    .clk(clk_tb),
    .reset_n(reset_n_tb),
    .zeroize(zeroize_tb),
    .compress_enable(en_tb),
    .mode(mode_tb_dut),
    .src_base_addr(src_base_tb),
    .dest_base_addr(dest_base_tb),
    .mem_rd_req(),
    .mem_wr_req(),
    .mem_rd_data(coeff_tb),
    .mem_wr_data(mem_wr_data_o),
    .compress_done()
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

task init_sim;
    begin
        $display("Start of init\n");
        clk_tb = 0;
        reset_n_tb = 0;
        zeroize_tb = 0;
        en_tb = 0;
        coeff_tb = 0;
        src_base_tb = 'h0;
        dest_base_tb = 'h0;
        mode_tb_dut = 0;
    end
endtask

//----------------------------------------------------------------
// reset_dut()
//
// Toggle reset to put the DUT into a well known state.
//----------------------------------------------------------------
task reset_dut;
    begin
      $display("*** Toggle reset.");
    //   cptra_pwrgood_tb = '0;
      reset_n_tb = 0;
    
    //   #(2 * CLK_PERIOD);
    //   cptra_pwrgood_tb = 1;
    
      #(2 * CLK_PERIOD);
      reset_n_tb = 1;
    
      $display("End of reset");
    end
endtask // reset_dut

task compress_test(compress_mode_t mode_tb = 0);

    logic [3:0] d;
    logic flag;

    for (int poly = 0; poly < 4; poly++) begin
        $display("Initializing poly %0d", poly);
        for (int i = 0; i < 256; i++) begin
            coeff_array[i] <= REG_SIZE'(MLKEM_Q_WIDTH'($urandom()));
        end
    end

    @(posedge clk_tb);

    case(mode_tb)
        0: begin 
            d = 1;
            src_base_tb = 0;
            dest_base_tb = 'h40;
        end
        1: begin 
            d = 5;
            src_base_tb = 'h40;
            dest_base_tb = 'h80;
        end
        2: begin 
            d = 11;
            src_base_tb = 'h80;
            dest_base_tb = 'hC0;
        end
        default: begin
            d = 1;
            src_base_tb = 0;
            dest_base_tb = 'h40;
        end
    endcase

    // Calculate expected value
    for (int poly = 0; poly < 4; poly++) begin
        for (int i = 0; i < 256; i++) begin
            // $display("Calculating expected value for poly %0d, index %0d for d-value %0d, coeff %0d", poly, i, d, coeff_array[i]);
            coeff_exp[i] = ((coeff_array[i] << d) + MLKEM_Q/2) / MLKEM_Q;
            // $display("coeff_exp = %0d", coeff_exp[i]);
        end
    end

    

    $display("Starting compress test with mode %0d\n", mode_tb);
    @(posedge clk_tb);
    en_tb <= 1;
    @(posedge clk_tb);
    en_tb <= 0;
    
    flag = 0;
    mode_tb_dut = mode_tb;

    fork
        begin
            // Send coefficients to the DUT
            @(posedge clk_tb); //emulate read mem latency
            for (int poly = 0; poly < 4; poly++) begin
                for (int i = 0; i < 256; i=i+4) begin
                    coeff_tb = {coeff_array[i+3], coeff_array[i+2], coeff_array[i+1], coeff_array[i]};
                    @(posedge clk_tb);
                end
                // @(posedge clk_tb);
            end
        end
        begin
            // Wait for compress_done signal
            while (!flag) begin
                $display("Waiting for compress_done signal...");
                repeat(3) @(posedge clk_tb); //wait for output to stabilize
                for (int poly = 0; poly < 4; poly++) begin
                    for (int i = 0; i < 256; i=i+4) begin
                            if (mem_wr_data_o != {REG_SIZE'(coeff_exp[i+3]), REG_SIZE'(coeff_exp[i+2]), REG_SIZE'(coeff_exp[i+1]), REG_SIZE'(coeff_exp[i])}) begin
                                $display("Mismatch at index %0d: expected %0h, got %0h at time %t", i, {REG_SIZE'(coeff_exp[i+3]), REG_SIZE'(coeff_exp[i+2]), REG_SIZE'(coeff_exp[i+1]), REG_SIZE'(coeff_exp[i])}, mem_wr_data_o, $time);
                                error_count++;
                            end 
                            // else begin
                            //     $display("Match at index %0d: %0h", i, mem_wr_data_o);
                            // end
                            @(posedge clk_tb);
                    end
                end
                flag = 1; // Set flag to exit the loop
                // @(posedge clk_tb);
            end
        end
    join
    $display("Compression done");
    
endtask

initial begin
    init_sim();
    reset_dut();
    //mode 0
    compress_test(compress1);
    compress_test(compress5);
    compress_test(compress11);

    if (error_count == 0) begin
        $display("* TESTCASE PASSED");
    end else begin
        $display("* TESTCASE FAILED with %0d errs.", error_count);
    end
    $finish;
end
endmodule