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
// power2round_tb.sv
// --------
// 
//
//
//======================================================================

`default_nettype none

module power2round_tb
    import abr_params_pkg::*;
#(
        parameter REG_SIZE = 24,
        parameter MLDSA_Q = 23'd8380417,
        parameter MLDSA_N = 256,
        parameter MLDSA_K = 8,
        parameter OMEGA = 75,
        parameter BUFFER_DATA_W = 8,
        parameter MEM_ADDR_WIDTH = 15,
        parameter AHB_DATA_WIDTH = 32
) 
();

parameter CLK_HALF_PERIOD = 5;
parameter CLK_PERIOD      = 2 * CLK_HALF_PERIOD;

parameter TEST_VECTOR_NUM = 2048;

//----------------------------------------------------------------
// Register and Wire declarations.
//----------------------------------------------------------------
reg [31 : 0]  tc_ctr;
reg [31 : 0]  error_ctr;

reg           clk_tb;
reg           reset_n_tb;
reg           cptra_pwrgood_tb;
reg           zeroize_tb;
reg           en_tb;
reg [(4*24)-1:0] coeff_tb;
logic done_tb;

reg [TEST_VECTOR_NUM-1:0][23:0] coeff_input;
reg [TEST_VECTOR_NUM-1:0][9:0]  coeff_high;
reg [TEST_VECTOR_NUM-1:0][12:0] coeff_low;

logic [(4*24)-1:0] mem_rd_data_a_tb, mem_rd_data_b_tb;
logic mem_rd_data_valid_tb;
mem_if_t mem_a_rd_req_tb;
mem_if_t mem_b_rd_req_tb;
mem_if_t skmem_a_wr_req_tb;
mem_if_t skmem_b_wr_req_tb;
logic [AHB_DATA_WIDTH-1:0] skmem_wr_data_a_tb;
logic [AHB_DATA_WIDTH-1:0] skmem_wr_data_b_tb;
logic pk_t1_wren_tb;
logic [7:0][9:0] pk_t1_wrdata_tb;
logic [7:0] pk_t1_wr_addr_tb;

reg [831:0][31:0] skmem_data;

power2round_top #(
    //.BUFFER_DATA_W(BUFFER_DATA_W)
) dut (
    .clk(clk_tb),
    .reset_n(reset_n_tb),
    .zeroize(zeroize_tb),
    .enable(en_tb),
    .src_base_addr(15'h0),
    .skmem_dest_base_addr(15'h0),
    .mem_a_rd_req(mem_a_rd_req_tb),
    .mem_b_rd_req(mem_b_rd_req_tb),
    .mem_rd_data_a(mem_rd_data_a_tb),
    .mem_rd_data_b(mem_rd_data_b_tb),
    // .mem_rd_data_valid(mem_rd_data_valid_tb),
    .skmem_a_wr_req(skmem_a_wr_req_tb),
    .skmem_b_wr_req(skmem_b_wr_req_tb),
    .skmem_wr_data_a(skmem_wr_data_a_tb),
    .skmem_wr_data_b(skmem_wr_data_b_tb),
    .pk_t1_wren(pk_t1_wren_tb),
    .pk_t1_wrdata(pk_t1_wrdata_tb),
    .pk_t1_wr_addr(pk_t1_wr_addr_tb),
    .done(done_tb)
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
// init_sim()
//
// Initialize all counters and testbed functionality as well
// as setting the DUT inputs to defined values.
//----------------------------------------------------------------
task init_sim;
    begin
        $display("Start of init\n");
        error_ctr = 32'h00000000;
        tc_ctr    = 32'h00000000;

        clk_tb = 0;
        reset_n_tb = 0;
        cptra_pwrgood_tb = 0;
        zeroize_tb = 0;
        en_tb = 0;
        mem_rd_data_a_tb = 'h0;
        mem_rd_data_b_tb = 'h0;
        mem_rd_data_valid_tb = 0;
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
      reset_n_tb = 0;
    
      #(2 * CLK_PERIOD);
      reset_n_tb = 1;
    
      $display("End of reset");
    end
endtask // reset_dut

//----------------------------------------------------------------
// display_test_results()
//
// Display the accumulated test results.
//----------------------------------------------------------------
task display_test_results;
begin
    if (error_ctr == 0)
    begin
        $display("*** All %02d test cases completed successfully", tc_ctr);
        $display("* TESTCASE PASSED");
    end
    else
    begin
        $display("*** %02d tests completed - %02d test cases did not complete successfully.",
                tc_ctr, error_ctr);
        $display("* TESTCASE FAILED");
    end
end
endtask // display_test_results

task read_test_vectors();
    string coeff_input_fname = "coeff_input.hex";
    string coeff_high_fname = "coeff_high.hex";
    string coeff_low_fname = "coeff_low.hex";

    integer fin;
    integer ret;
    int test_vector_cnt;

    //generate input vectors and expected results
    $system($sformatf("python power2round.py"));
    
    // read input coeff
    fin = $fopen(coeff_input_fname, "r");
    if (fin == 0) 
        $error("Can't open file %s", coeff_input_fname);

    test_vector_cnt = 0;
    while (!$feof(fin)) begin
        ret = $fscanf(fin, "%h\n", coeff_input[test_vector_cnt]);
        if (ret != 1) begin
            $error("Failed to read a matching string");
            $fclose(fin);
            $finish;
        end
        test_vector_cnt++;
    end
    $fclose(fin);

    $display("Read input test vectors from %s", coeff_input_fname);

    // read coeff high
    fin = $fopen(coeff_high_fname, "r");
    if (fin == 0) 
        $error("Can't open file %s", coeff_high_fname);

    test_vector_cnt = 0;
    while (!$feof(fin)) begin
        ret = $fscanf(fin, "%h\n", coeff_high[test_vector_cnt]);
        if (ret != 1) begin
            $error("Failed to read a matching string");
            $fclose(fin);
            $finish;
        end
        test_vector_cnt++;
    end
    $fclose(fin);

    $display("Read input test vectors from %s", coeff_high_fname);


    // read coeff low
    fin = $fopen(coeff_low_fname, "r");
    if (fin == 0) 
        $error("Can't open file %s", coeff_low_fname);

    test_vector_cnt = 0;
    while (!$feof(fin)) begin
        ret = $fscanf(fin, "%h\n", coeff_low[test_vector_cnt]);
        if (ret != 1) begin
            $error("Failed to read a matching string");
            $fclose(fin);
            $finish;
        end
        test_vector_cnt++;
    end
    $fclose(fin);

    $display("Read input test vectors from %s", coeff_low_fname);
    
endtask

task power2round_test();
    reg [31  : 0] time_limit;
    int pk_index;
    begin
        time_limit = 0;
        pk_index = 0;
        skmem_data = 'h0;
        $display("Starting power2round test\n");
        //$system($sformatf("python3 power2round.py"));

        @(posedge clk_tb);
        en_tb <= 1;
        @(posedge clk_tb);
        en_tb <= 0;
        @(posedge clk_tb);

        while (~done_tb & (time_limit < 1000)) begin
            mem_rd_data_a_tb <= (mem_a_rd_req_tb.rd_wr_en == RW_READ)? {coeff_input[4*mem_a_rd_req_tb.addr+3],coeff_input[4*mem_a_rd_req_tb.addr+2],coeff_input[4*mem_a_rd_req_tb.addr+1],coeff_input[4*mem_a_rd_req_tb.addr]} : 'h0;
            mem_rd_data_b_tb <= (mem_b_rd_req_tb.rd_wr_en == RW_READ)? {coeff_input[4*mem_b_rd_req_tb.addr+3],coeff_input[4*mem_b_rd_req_tb.addr+2],coeff_input[4*mem_b_rd_req_tb.addr+1],coeff_input[4*mem_b_rd_req_tb.addr]} : 'h0;
            mem_rd_data_valid_tb <= (mem_a_rd_req_tb.rd_wr_en == RW_READ);
            if (pk_t1_wren_tb) begin
                if (pk_index != pk_t1_wr_addr_tb) begin
                        $display("Error: pk_t1 addr mismatch. Exp: %gh, Ohs: %6h", pk_index, pk_t1_wr_addr_tb);
                        error_ctr = error_ctr + 1;
                end
                for (int i=0; i<8; i++)
                    if (pk_t1_wrdata_tb[i] != coeff_high[8*pk_t1_wr_addr_tb+i]) begin
                        $display("Error: pk_t1 data mismatch. Exp: %gh, Ohs: %6h", coeff_high[8*pk_t1_wr_addr_tb+i], pk_t1_wrdata_tb[i]);
                        error_ctr = error_ctr + 1;
                    end
                pk_index++;
                tc_ctr = tc_ctr + 8;
            end

            if (skmem_a_wr_req_tb.rd_wr_en == RW_WRITE)
                skmem_data[skmem_a_wr_req_tb.addr] = skmem_wr_data_a_tb;
                
            if (skmem_b_wr_req_tb.rd_wr_en == RW_WRITE)
                skmem_data[skmem_b_wr_req_tb.addr] = skmem_wr_data_b_tb;

            time_limit =  time_limit + 1;
            @(posedge clk_tb);
        end

        if (pk_index != TEST_VECTOR_NUM/8) begin // 8 coeff per write
            $display("Error: pk_t1 write is not completed. Exp: %gh, Ohs: %6h", TEST_VECTOR_NUM/8, pk_index);
            error_ctr = error_ctr + 1;
        end
        
        if (skmem_data != coeff_low) begin
            $display("Error: coeff_low data mismatch.");
            error_ctr = error_ctr + 1;
        end

        $display("Test done\n");
        repeat(100) @(posedge clk_tb);
    end
endtask

initial begin
    init_sim();
    reset_dut();
    read_test_vectors();
    power2round_test();

    display_test_results();
      
    $display("");
    $display("*** ecc simulation done. ***");
    $finish;

end
endmodule