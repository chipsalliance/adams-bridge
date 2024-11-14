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
// skdecode_tb.sv
// ---------------
//======================================================================

`default_nettype none

module skdecode_tb
    import mldsa_params_pkg::*;
    import skdecode_defines_pkg::*;
#(
    parameter REG_SIZE = 24,
    parameter MEM_ADDR_WIDTH = 15,
    parameter MLDSA_ETA = 2,
    parameter ETA_SIZE = 3, //$clog2(2*MLDSA_ETA),
    parameter MLDSA_Q = 8380417
)
();

parameter CLK_HALF_PERIOD = 5;
parameter CLK_PERIOD      = 2 * CLK_HALF_PERIOD;

//----------------------------------------------------------------
// Register and Wire declarations.
//----------------------------------------------------------------
reg [31 : 0]  error_ctr;

reg           clk_tb;
reg           reset_n_tb;
reg           cptra_pwrgood_tb;
reg           zeroize_tb;
reg           en_tb;
reg [7:0][2:0] s1s2_data_i;
reg [3:0][12:0] t0_data_i;
reg [MLDSA_MEM_ADDR_WIDTH-1:0] dest_base_tb;
reg [31:0] ahb_data_tb, keymem_a_data_tb, keymem_b_data_tb;
reg [6:0][255:0][2:0] s1_array_rnd;
reg [6:0][255:0][23:0] s1_out_rnd;
reg [167:0][3:0][7:0] s1_array, s1_array_rev;

reg [7:0][255:0][2:0] s2_array_rnd;
reg [7:0][255:0][23:0] s2_out_rnd;

reg [7:0][255:0][12:0] t0_array_rnd;
reg [7:0][255:0][23:0] t0_out_rnd;

reg [191:0][3:0][7:0] s2_array;
reg [831:0][3:0][7:0] t0_array;
reg [(256*8)-1:0][REG_SIZE-1:0] t0_out_array, s2_out_array;
reg [(256*7)-1:0][REG_SIZE-1:0] s1_out_array;

typedef struct {
    logic [255:0][2:0]  poly_rnd_array;
    logic [255:0][23:0] poly_exp_array;
} s_poly_arrays_t;

typedef struct {
    logic [255:0][12:0] poly_rnd_array;
    logic [255:0][23:0] poly_exp_array;
} t_poly_arrays_t;

mem_if_t keymem_a_rd_req_tb;
mem_if_t keymem_b_rd_req_tb;
logic skdecode_error_tb;

skdecode_top dut (
    .clk(clk_tb),
    .reset_n(reset_n_tb),
    .zeroize(zeroize_tb),
    .skdecode_enable(en_tb),
    .keymem_src_base_addr(MLDSA_MEM_ADDR_WIDTH'(0)),
    .dest_base_addr(dest_base_tb),
    .keymem_a_rd_data(keymem_a_data_tb),
    .keymem_b_rd_data(keymem_b_data_tb),
    .keymem_a_rd_req(keymem_a_rd_req_tb),
    .keymem_b_rd_req(keymem_b_rd_req_tb),
    .mem_a_wr_req(),
    .mem_b_wr_req(),
    .mem_a_wr_data(),
    .mem_b_wr_data(),
    .skdecode_error(skdecode_error_tb),
    .skdecode_done(),
    .s1_done(),
    .s2_done(),
    .t0_done()
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
        error_ctr = 32'h00000000;

        clk_tb = 0;
        reset_n_tb = 0;
        cptra_pwrgood_tb = 0;
        // hint_4bit_tb = 0;
        // index_tb = 0;
        zeroize_tb = 0;
        en_tb = 0;
        s1s2_data_i = 'h0;
        t0_data_i = 'h0;
        dest_base_tb = 'h0;
        ahb_data_tb = 'h0;
        keymem_a_data_tb = 'h0;
        keymem_b_data_tb = 'h0;
    end
endtask

  //----------------------------------------------------------------
  // display_test_result()
  //
  // Display the accumulated test results.
  //----------------------------------------------------------------
  task display_test_result;
    begin
      if (error_ctr == 0)
        begin
          $display("*** All test cases completed successfully.");
          $display("* TESTCASE PASSED");
        end
      else
        begin
          $display("*** %02d errors detected during testing.", error_ctr);
          $display("* TESTCASE FAILED");
        end
    end
  endtask // display_test_result

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


//----------------------------------------------------------------
// Randomize Poly function
//
// 
//----------------------------------------------------------------
function s_poly_arrays_t random_s_poly_gen();
    s_poly_arrays_t result;
    for (int coeff_no = 0; coeff_no < 256; coeff_no++) begin
        result.poly_rnd_array[coeff_no] = $urandom_range(0, 4);
        if (result.poly_rnd_array[coeff_no] <= MLDSA_ETA)
            result.poly_exp_array[coeff_no] = ((MLDSA_ETA - result.poly_rnd_array[coeff_no]) % MLDSA_Q);
        else
            result.poly_exp_array[coeff_no] = (MLDSA_Q + MLDSA_ETA - result.poly_rnd_array[coeff_no]) % MLDSA_Q;
    end
    return result;
endfunction

function t_poly_arrays_t random_t_poly_gen();
    t_poly_arrays_t result;
    for (int coeff_no = 0; coeff_no < 256; coeff_no++) begin
        result.poly_rnd_array[coeff_no] = $urandom_range(0, 13'h1fff);
        if (result.poly_rnd_array[coeff_no] <= 13'h1000)
            result.poly_exp_array[coeff_no] = ((13'h1000 - result.poly_rnd_array[coeff_no]) % MLDSA_Q);
        else
            result.poly_exp_array[coeff_no] = (MLDSA_Q + 13'h1000 - result.poly_rnd_array[coeff_no]) % MLDSA_Q;
    end
    return result;
endfunction

//----------------------------------------------------------------
// skdecode_rand_test()
//
//----------------------------------------------------------------
task skdecode_rand_test();
    logic [167:0][31:0] s1_array_tb;
    logic [191:0][31:0] s2_array_tb; 
    logic [831:0][31:0] t0_array_tb;
    int i;
    string sval;
    int check_count;
    s_poly_arrays_t s_poly_rnd_array;
    t_poly_arrays_t t_poly_rnd_array;

    for (int vec_no=0; vec_no<7; vec_no++) begin
        s_poly_rnd_array = random_s_poly_gen();
        s1_array_rnd[vec_no] = s_poly_rnd_array.poly_rnd_array;
        s1_out_rnd[vec_no] = s_poly_rnd_array.poly_exp_array;
    end
    //reshape the array
    s1_array_tb = s1_array_rnd;
    s1_out_array = s1_out_rnd;

    for (int vec_no=0; vec_no<8; vec_no++) begin
        s_poly_rnd_array = random_s_poly_gen();
        s2_array_rnd[vec_no] = s_poly_rnd_array.poly_rnd_array;
        s2_out_rnd[vec_no] = s_poly_rnd_array.poly_exp_array;
    end
    //reshape the array
    s2_array_tb = s2_array_rnd;
    s2_out_array = s2_out_rnd;

    for (int vec_no=0; vec_no<8; vec_no++) begin
        t_poly_rnd_array = random_t_poly_gen();
        t0_array_rnd[vec_no] = t_poly_rnd_array.poly_rnd_array;
        t0_out_rnd[vec_no] = t_poly_rnd_array.poly_exp_array;
    end
    //reshape the array
    t0_array_tb = t0_array_rnd;
    t0_out_array = t0_out_rnd;

    $display("Starting random test\n");
    @(posedge clk_tb);
    en_tb = 1;
    @(posedge clk_tb);
    en_tb = 1'b0;
    dest_base_tb = 15'h0;

    $display("Wait a cycle to emulate mem read\n");
    @(posedge clk_tb);
    
    $display("Starting s1 poly\n");
    fork
        begin
            while ((keymem_a_rd_req_tb.addr < 168) & (keymem_b_rd_req_tb.addr < 168)) begin
                if (keymem_a_rd_req_tb.rd_wr_en == RW_READ)
                    keymem_a_data_tb <= s1_array_tb[keymem_a_rd_req_tb.addr];
                
                if (keymem_b_rd_req_tb.rd_wr_en == RW_READ)
                    keymem_b_data_tb <= s1_array_tb[keymem_b_rd_req_tb.addr];
                    
                @(posedge clk_tb);
            end
        end
        begin
            $display("Waiting for s1s2 valid\n");
            while (!dut.s1s2_valid[0]) @(posedge clk_tb);
            $display("Received s1s2 valid\n");
            for (int k = 0; k < 224; k++) begin
                for (int j = 0; j < 8; j++) begin
                    if (dut.s1s2_data[j] != s1_out_array[(8*k)+j]) begin
                        $display("Error: s1 data mismatch. Exp: %6h, Obs: %6h", s1_out_array[(8*k)+j], dut.s1s2_data[j]);
                        error_ctr = error_ctr + 1;
                    end
                    else check_count++;
                end
                @(posedge clk_tb);
            end
        end
    join

    if (check_count == 1792) 
        $display("s1 unpack passed, check count = %d", check_count);
    else 
        $display("s1 unpack failed, check count = %d", check_count);

    $display("Waiting for s1 done, value = %0d\n", dut.s1_done);
    @(posedge clk_tb iff (dut.s1_done == 1'b1));

    check_count = 0;
    @(posedge clk_tb); //Wait a cycle to emulate delay in fsm for last mem write

    $display("Starting s2 poly\n");
    fork
        begin
            while ((keymem_a_rd_req_tb.addr < (168+192)) & (keymem_b_rd_req_tb.addr < (168+192))) begin
                if (keymem_a_rd_req_tb.rd_wr_en == RW_READ)
                    keymem_a_data_tb <= s2_array_tb[keymem_a_rd_req_tb.addr - 168];
                
                if (keymem_b_rd_req_tb.rd_wr_en == RW_READ)
                    keymem_b_data_tb <= s2_array_tb[keymem_b_rd_req_tb.addr - 168];
                    
                @(posedge clk_tb);
            end
        end
        begin
            $display("Waiting for s1s2 valid\n");
            while (!dut.s1s2_valid[0]) @(posedge clk_tb);
            $display("Received s1s2 valid\n");
            for (int k = 0; k < 256; k++) begin
                for (int j = 0; j < 8; j++) begin
                    if (dut.s1s2_data[j] != s2_out_array[(8*k)+j]) begin
                        $display("Error: s2 data mismatch. Exp: %6h, Obs: %6h", s2_out_array[(8*k)+j], dut.s1s2_data[j]);
                        error_ctr = error_ctr + 1;
                    end
                    else check_count++;
                end
                @(posedge clk_tb);
            end
        end
    join

    if (check_count == 2048) 
        $display("s2 unpack passed, check count = %d", check_count);
    else 
        $display("s2 unpack failed, check count = %d", check_count);

    $display("Waiting for s2 done, value = %0d\n", dut.s2_done);

    @(posedge clk_tb iff (dut.s2_done == 1'b1));

    check_count = 0;
    @(posedge clk_tb); //Wait a cycle to emulate delay in fsm for last mem write

    $display("Starting t0 poly\n");
    fork
        begin
            while ((keymem_a_rd_req_tb.addr < (168+192+832)) & (keymem_b_rd_req_tb.addr < (168+192+832))) begin
                if (keymem_a_rd_req_tb.rd_wr_en == RW_READ)
                    keymem_a_data_tb <= t0_array_tb[keymem_a_rd_req_tb.addr-360];
                
                if (keymem_b_rd_req_tb.rd_wr_en == RW_READ)
                    keymem_b_data_tb <= t0_array_tb[keymem_b_rd_req_tb.addr-360];
                    
                @(posedge clk_tb);
            end
        end
        begin
            $display("Waiting for t0 valid\n");
            while (!dut.t0_valid[0]) @(posedge clk_tb);
            $display("Received t0 valid\n");
            for (int k = 0; k < 512; k++) begin
                for (int j = 0; j < 4; j++) begin
                    if (dut.t0_data[j] != t0_out_array[(4*k)+j]) begin
                        $display("Error: t0 data mismatch. Exp: %6h, Obs: %6h", t0_out_array[(4*k)+j], dut.t0_data[j]);
                        error_ctr = error_ctr + 1;
                    end
                    else check_count++;
                end
                @(posedge clk_tb);
            end
        end
    join

    if (check_count == 2048) 
        $display("T0 unpack passed, check count = %d", check_count);
    else 
        $display("T0 unpack failed, check count = %d", check_count);

    $display("Waiting for t0 done, value = %0d\n", dut.t0_done);

    @(posedge clk_tb iff (dut.t0_done == 1'b1));

    while (!dut.skdecode_done) @(posedge clk_tb);
    $display("Random Test done\n");
endtask

//----------------------------------------------------------------
// skdecode_error_test()
//
//----------------------------------------------------------------
task skdecode_error_test();
    logic [167:0][31:0] s1_array_tb;
    logic [167:0][31:0] s2_array_tb; 
    logic [831:0][31:0] t0_array_tb;
    int i;
    int rand_address;
    string sval;
    int check_count;
    s_poly_arrays_t poly_rnd_array;
    
    $display("Starting error test\n");

    for (int vec_no=0; vec_no<7; vec_no++) begin
        poly_rnd_array = random_s_poly_gen();
        s1_array_rnd[vec_no] = poly_rnd_array.poly_rnd_array;
        s1_out_rnd[vec_no] = poly_rnd_array.poly_exp_array;
    end
    //reshape the array
    s1_array_tb = s1_array_rnd;
    s1_out_array = s1_out_rnd;

    rand_address = $urandom_range(0,167);
    
    @(posedge clk_tb);
    en_tb = 1;
    @(posedge clk_tb);
    en_tb = 1'b0;
    dest_base_tb = 15'h0;

    //Wait a cycle to emulate mem read
    @(posedge clk_tb);
    
    $display("Starting s1 poly\n");

    while ((!skdecode_error_tb) && (keymem_a_rd_req_tb.addr < 168) & (keymem_b_rd_req_tb.addr < 168)) begin
        if (keymem_a_rd_req_tb.rd_wr_en == RW_READ) begin
            if (rand_address == keymem_a_rd_req_tb.addr)
                keymem_a_data_tb <= $urandom_range(5,7);
            else
                keymem_a_data_tb <= s1_array_tb[keymem_a_rd_req_tb.addr];
        end
        
        if (keymem_b_rd_req_tb.rd_wr_en == RW_READ)
            keymem_b_data_tb <= s1_array_tb[keymem_b_rd_req_tb.addr];
            
        @(posedge clk_tb);
    end
        
    if (!skdecode_error_tb) begin
        $display("Error: invalid s1 is not detected at %d!", rand_address);
        error_ctr = error_ctr + 1;
    end
    else
        $display("invalid s1 is detected at %d!", rand_address);

    @(posedge clk_tb); //Wait a cycle to emulate delay in fsm for last mem write


endtask

//----------------------------------------------------------------
// skdecode_test
// The main test functionality.
//
//----------------------------------------------------------------

initial begin
    init_sim();
    reset_dut();

    skdecode_rand_test();

    skdecode_error_test();

    display_test_result();
    $finish;
end

endmodule