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
// ntt_top_tb_fpga.sv
// --------
// 
//
//
//======================================================================

`default_nettype none

module ntt_top_tb_fpga 

    import ntt_defines_pkg::*;
    import abr_params_pkg::*;
    
#(
    parameter   TEST_VECTOR_NUM = 10,
    parameter   PRIME     = 23'd8380417,
    parameter   REG_SIZE  = 23,
    parameter   ABR_MEM_DEPTH = 32768, //32 KB
    parameter   MEM_ADDR_WIDTH = $clog2(ABR_MEM_DEPTH)
)
();

parameter CLK_HALF_PERIOD = 5;
parameter CLK_PERIOD      = 2 * CLK_HALF_PERIOD;

parameter AHB_HTRANS_IDLE     = 0;
  parameter AHB_HTRANS_BUSY     = 1;
  parameter AHB_HTRANS_NONSEQ   = 2;
  parameter AHB_HTRANS_SEQ      = 3;

  parameter AHB_ADDR_WIDTH = 14;
  parameter AHB_DATA_WIDTH = 64;
  parameter MEM_DEPTH = (2**AHB_ADDR_WIDTH);


//----------------------------------------------------------------
// Register and Wire declarations.
//----------------------------------------------------------------
reg [31 : 0]  cycle_ctr;
reg [31 : 0]  error_ctr;
reg [31 : 0]  tc_ctr;

reg           clk_tb;
reg           reset_n_tb;

reg           enable_tb;
reg           bf_ready_tb;
reg [(4*REG_SIZE)-1:0] data_i_tb, data_o_tb;

reg [7:0] addr0, addr1, addr2, addr3;
mode_t mode_tb;
reg [REG_SIZE-1:0] data0, data1, data2, data3;

reg [23:0] zeta [255:0];
reg [23:0] zeta_inv [255:0];
reg [(4*(REG_SIZE+1))-1:0] ntt_mem_tb [63:0];

reg load_tb_values;
reg [ABR_MEM_ADDR_WIDTH-1:0] load_tb_addr;

reg [7:0] src_base_addr, interim_base_addr, dest_base_addr;
reg acc_tb, svalid_tb, sampler_mode_tb;
reg ntt_done_tb;

ntt_mem_addr_t ntt_mem_base_addr_tb;
pwo_mem_addr_t pwo_mem_base_addr_tb;

string operation;

logic sub;
logic [45:0] actual_u, actual_v, actual_w;
logic [1:0][45:0] u;
logic [1:0][45:0] v;
logic [1:0][45:0] w;
logic [4:0][45:0] rnd_tb;
logic wren_tb, rden_tb;
logic [1:0] wrptr_tb, rdptr_tb;
logic [5:0] random_tb;
bf_uvwi_t uvw_i_tb;
pwo_uvwi_t pw_uvw_i_tb;
logic masking_en_tb;
logic shuffling_en_tb;
logic mlkem_tb;

reg [AHB_ADDR_WIDTH-1:0]  haddr_i_tb;
reg [AHB_DATA_WIDTH-1:0]  hwdata_i_tb;
reg           hsel_i_tb;
reg           hwrite_i_tb; 
reg           hready_i_tb;
reg [1:0]     htrans_i_tb;
reg [2:0]     hsize_i_tb;

wire          hresp_o_tb;
wire          hreadyout_o_tb;
wire [AHB_DATA_WIDTH-1:0] hrdata_o_tb;

reg [63 : 0]  read_data;

logic [255:0][REG_SIZE-1:0] exp_gs_array;
logic [ABR_MEM_MASKED_DATA_WIDTH-1:0] sampler_input;

//----------------------------------------------------------------
// Device Under Test.
//----------------------------------------------------------------

ntt_wrapper_fpga #(
    .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
    .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
    .MEM_ADDR_WIDTH(AHB_ADDR_WIDTH)
)
dut (
    .hclk(clk_tb),
    .hreset_n(reset_n_tb),
    .haddr_i(haddr_i_tb),
    .hwdata_i(hwdata_i_tb),
    .hsel_i(hsel_i_tb),
    .hwrite_i(hwrite_i_tb),
    .hready_i(hready_i_tb),
    .htrans_i(htrans_i_tb),
    .hsize_i(hsize_i_tb),
    .hresp_o(hresp_o_tb),
    .hreadyout_o(hreadyout_o_tb),
    .hrdata_o(hrdata_o_tb),
    .random(random_tb),
    .rnd_i(rnd_tb)
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

  //Starting random num gen
    random_tb <= 'h0; //$urandom();
    for (int i = 0; i < 5; i++)
        rnd_tb[i] <= 'h0; //$urandom();
end // clk_gen

//----------------------------------------------------------------
// sys_monitor()
//
// An always running process that creates a cycle counter and
// conditionally displays information about the DUT.
//----------------------------------------------------------------
always
begin : sys_monitor
  #(CLK_PERIOD);
  cycle_ctr = cycle_ctr + 1;
end

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
        $display("Start of init\n");
        cycle_ctr = 32'h00000000;
        error_ctr = 32'h00000000;
        tc_ctr    = 32'h00000000;

        clk_tb        = 0;
        reset_n_tb    = 0;

        haddr_i_tb      = 0;
        hwdata_i_tb     = 0;
        hsel_i_tb       = 0;
        hwrite_i_tb     = 0;
        hready_i_tb     = 0;
        htrans_i_tb     = AHB_HTRANS_IDLE;
        hsize_i_tb      = 3'b011;

        random_tb <= 'h0;
        rnd_tb <= '0;

        $display("End of init\n");
    end
endtask

//----------------------------------------------------------------
// wait_ready()
//
// Wait for the ready flag in the dut to be set.
// (Actually we wait for either ready or valid to be set.)
//
// Note: It is the callers responsibility to call the function
// when the dut is actively processing and will in fact at some
// point set the flag.
//----------------------------------------------------------------
task wait_ready;
begin
    read_data = 0;
    #(CLK_PERIOD);

    while (read_data == 0)
        begin
        read_single_word(MEM_DEPTH-1); //read the last word, which is the ready flag
        end
    end
endtask

//----------------------------------------------------------------
// write_single_word()
//
// Write the given word to the DUT using the DUT interface.
//----------------------------------------------------------------
task write_single_word(input [31 : 0]  address,
    input [63 : 0] dword);
    begin
    hsel_i_tb       <= 1;
    haddr_i_tb      <= address;
    hwrite_i_tb     <= 1;
    hready_i_tb     <= 1;
    htrans_i_tb     <= AHB_HTRANS_NONSEQ;
    hsize_i_tb      <= 3'b011;
    #(CLK_PERIOD);

    haddr_i_tb      <= 'Z;
    hwdata_i_tb     <= dword;
    hwrite_i_tb     <= 0;
    htrans_i_tb     <= AHB_HTRANS_IDLE;
    end
endtask // write_single_word

//----------------------------------------------------------------
// write_single_word_blocking()
//
// Write the given word to the DUT using the DUT interface.
//----------------------------------------------------------------
task write_single_word_blocking(input [31 : 0]  address,
    input [63 : 0] dword);
    begin
    hsel_i_tb       = 1;
    haddr_i_tb      = address;
    hwrite_i_tb     = 1;
    hready_i_tb     = 1;
    htrans_i_tb     = AHB_HTRANS_NONSEQ;
    hsize_i_tb      = 3'b011;
    #(CLK_PERIOD);

    haddr_i_tb      = 'Z;
    hwdata_i_tb     = dword;
    hwrite_i_tb     = 0;
    htrans_i_tb     = AHB_HTRANS_IDLE;
    end
endtask // write_single_word

//----------------------------------------------------------------
// read_single_word()
//
// Read a data word from the given address in the DUT.
// the word read will be available in the global variable
// read_data.
//----------------------------------------------------------------
task read_single_word(input [31 : 0]  address);
    begin
      hsel_i_tb       = 1;
      haddr_i_tb      = address;
      hwrite_i_tb     = 0;
      hready_i_tb     = 1;
      htrans_i_tb     = AHB_HTRANS_NONSEQ;
      hsize_i_tb      = 3'b011;
      #(CLK_PERIOD);
      
      hwdata_i_tb     = 0;
      haddr_i_tb     = 'Z;
      htrans_i_tb     = AHB_HTRANS_IDLE;
      read_data = hrdata_o_tb;
    end
endtask // read_single_word
//----------------------------------------------------------------

task init_mem_with_shares(input logic [13:0] base);
    logic [MASKED_WIDTH-1:0] share0, share1;

    $display("Initializing memory with shares");
    for (int i = base; i < base+512; i+=2) begin //256 coeff with 2 shares each --> 512 addr
        share0 = (base-i) - rnd_tb[0]; //start data from 0
        share1 = rnd_tb[0];
        write_single_word(i, share0);
        write_single_word(i+1, share1);
    end

endtask

task pgm_base_addr(input logic [13:0] src, input logic [13:0] interim, input logic [13:0] dest);
    $display("Writing base addr reg with src, interim and dest base addr");
    write_single_word(MEM_DEPTH-4, {22'h0, src, interim, dest}); //{src_base_addr, interim_base_addr, dest_base_addr}

    #(2*CLK_PERIOD);
    hsel_i_tb = 0;
endtask

task ct_test (input logic shuf_en);

    $display("Starting ct test");
    $display("Writing 1 poly to addr range 0 - 255");

    for (int i = 0; i < 256; i++) begin
        write_single_word(i, i);
    end

    // $display("Writing base addr reg with src, interim and dest base addr");
    // write_single_word(MEM_DEPTH-4, {22'h0, 14'h0, 14'h40, 14'h80}); //src_base_addr, interim_base_addr, dest_base_addr

    $display("Writing ctrl reg with mode and other ctrl signals");
    write_single_word(MEM_DEPTH-3, {56'h0, 1'b0, shuf_en, 1'b0, 1'b1, 1'b0, 3'h0}); //{zeroize, shuf, mask, svalid, acc, mode}

    $display("Writing enable reg with enable signal");
    write_single_word(MEM_DEPTH-2, {63'h0, 1'b1}); //enable

    //pulse
    $display("Pulsing enable reg");
    write_single_word(MEM_DEPTH-2, 64'h0);

    #CLK_PERIOD;
    hsel_i_tb = 0;

    #CLK_PERIOD;
    $display("Waiting for NTT to complete");
    wait_ready();

    #CLK_PERIOD;
    hsel_i_tb = 0;


endtask

task gs_test (input logic shuf_en, input logic mask_en, input logic check_en);

    logic [255:0][63:0] obs_data;

    $display("Starting gs test");
    // $display("Writing 1 poly to addr range 0 - 255");

    // for (int i = 0; i < 256; i++) begin
    //     write_single_word(i, i);
    // end

    $display("Writing ctrl reg with mode and other ctrl signals");
    write_single_word(MEM_DEPTH-3, {56'h0, 1'b0, shuf_en, mask_en, 1'b1, 1'b0, 3'h1}); //{zeroize, shuf, mask, svalid, acc, mode}

    $display("Writing enable reg with enable signal");
    write_single_word(MEM_DEPTH-2, {63'h0, 1'b1}); //enable

    //pulse
    write_single_word(MEM_DEPTH-2, 64'h0);

    #CLK_PERIOD;
    hsel_i_tb = 0;

    fork
        #(2*CLK_PERIOD);
        $display("Waiting for GS to complete at time %0t", $time);
        wait_ready();
        $display("GS done, reading output at time %0t", $time);
    join

    #CLK_PERIOD;
    hsel_i_tb = 0;
    #CLK_HALF_PERIOD;
    
    if (check_en) begin
        fork
            begin
                for (int i = 0; i < 256; i++) begin
                    read_single_word(i+(128*4));
                end
            end
            begin
                #(3*CLK_PERIOD);
                for (int i = 0; i < 255; i++) begin
                    if (read_data != i) begin
                        $error("gs_test: Read data mismatch at address %0d: expected %0d, got %0d", (i+(128*4)), i, read_data);
                        error_ctr = error_ctr + 1;
                    end 
                    #(CLK_PERIOD);
                end
            end
        join

        #CLK_PERIOD;
        hsel_i_tb = 0;

        if (error_ctr > 0) begin
            $error("gs_test completed with errors, %0d errors found", error_ctr);
        end else begin
            $display("gs_test completed successfully, all data matches expected values");
        end
    end
endtask

task pwm_sampler_test (input logic shuf_en, input logic mask_en, input logic acc_en);
    logic [63:0] share0, share1;
    logic [23:0] combined_res;
    logic rand_svalid;
    logic [255:0][63:0] sampler_data_array;
    int count;

    $display("Starting pwm, no acc, svalid test");
    $display("Writing 1 poly to addr range 0 - 255");

    for (int i = 0; i < 256; i++) begin
        write_single_word(i, i);
    end

    $display("Writing ctrl reg with mode and other ctrl signals");
    write_single_word(MEM_DEPTH-3, {55'h0, 1'b1, 1'b0, shuf_en, mask_en, 1'b0, acc_en, pwm}); //{shuf, mask, svalid, acc, mode}
    
    count = 0;

    fork
        begin
            $display("Writing enable reg with enable signal");
            write_single_word(MEM_DEPTH-2, {63'h0, 1'b1}); //enable
            //pulse
            $display("Pulsing enable reg");
            write_single_word(MEM_DEPTH-2, 64'h0);
            #CLK_PERIOD;

            hsel_i_tb = 0;
            #(CLK_PERIOD);
            #(CLK_HALF_PERIOD);
        end
        begin
            #(CLK_PERIOD);
            $display("Writing sampler data to dut at time %0t", $time);
            if (shuf_en)
                #(2*CLK_PERIOD);
            else
                #CLK_PERIOD;

            while (count < 12) begin
                rand_svalid = $urandom_range(0,1);
                $display("rand_svalid = %0d at time %0t", rand_svalid, $time);

                if (rand_svalid) begin
                    $display("Writing sampler data for i = %0d", count);
                    sampler_input = {24'((count*4)+3), 24'((count*4)+2), 24'((count*4)+1), 24'(count*4)};
                    sampler_data_array[(count*4)] = 64'(count*4);
                    sampler_data_array[(count*4)+1] = 64'((count*4)+1);
                    sampler_data_array[(count*4)+2] = 64'((count*4)+2);
                    sampler_data_array[(count*4)+3] = 64'((count*4)+3);

                    count++;
                    write_single_word(MEM_DEPTH-5, {40'h0, sampler_input[23:0]});
                    write_single_word(MEM_DEPTH-6, {40'h0, sampler_input[47:24]});
                    write_single_word(MEM_DEPTH-7, {40'h0, sampler_input[71:48]});
                    write_single_word(MEM_DEPTH-8, {40'h0, sampler_input[95:72]});
                end
                write_single_word(MEM_DEPTH-3, {55'h0, 1'b1, 1'b0, shuf_en, mask_en, rand_svalid, acc_en, pwm}); //{shuf, mask, svalid, acc, mode}
            end
        
            $display("Waiting for PWM to complete at time %0t", $time);
            wait_ready();
            $display("PWM done, reading output at time %0t", $time);
            #CLK_PERIOD;
            hsel_i_tb = 0;
        end
    join

endtask

task pwm_test (input logic shuf_en, input logic mask_en, input logic acc_en, input logic check_en);
    logic [255:0][63:0] sampler_data_array;
    logic [63:0] share0, share1;
    logic [23:0] combined_res;

    $display("Starting pwm, no acc, svalid test");
    $display("Writing 1 poly to addr range 0 - 255");

    for (int i = 0; i < 512; i++) begin
        write_single_word(i, i);
    end

    $display("Writing ctrl reg with mode and other ctrl signals");
    write_single_word(MEM_DEPTH-3, {55'h0, 1'b0, 1'b0, shuf_en, mask_en, 1'b1, acc_en, 3'h2}); //{sampler_mode,zeroize,shuf, mask, svalid, acc, mode}

    $display("Writing enable reg with enable signal");
    write_single_word(MEM_DEPTH-2, {63'h0, 1'b1}); //enable

    //pulse
    $display("Pulsing enable reg");
    write_single_word(MEM_DEPTH-2, 64'h0);

    #CLK_PERIOD;
    hsel_i_tb = 0;

    #(CLK_PERIOD);
    #CLK_HALF_PERIOD;

    
    $display("Waiting for PWM to complete at time %0t", $time);
    wait_ready();
    $display("PWM done, reading output at time %0t", $time);
    #CLK_PERIOD;
    hsel_i_tb = 0;

    if (check_en) begin
        fork
            begin
                for (int i = 0; i < 256; i++) begin
                    read_single_word(i+(128*4));
                end
            end
            begin
                #(3*CLK_PERIOD);
                for (int i = 0; i < 255; i++) begin
                    if (acc_en) begin
                        if (read_data != (i+(i*i)%MLDSA_Q)%MLDSA_Q) begin
                            $error("pwm_test: Read data mismatch at address %0d: expected %0d, got %0d", (i+(128*4)), (i+(i*i)%MLDSA_Q)%MLDSA_Q, read_data);
                            error_ctr = error_ctr + 1;
                        end
                    end
                    else begin
                        if (read_data != (i*i)%MLDSA_Q) begin
                            $error("pwm_test: Read data mismatch at address %0d: expected %0d, got %0d", (i+(128*4)), (i*i)%MLDSA_Q, read_data);
                            error_ctr = error_ctr + 1;
                        end
                    end
                    #(CLK_PERIOD);
                end
            end
        join

        #CLK_PERIOD;
        hsel_i_tb = 0;

        if (error_ctr > 0) begin
            $error("pwm_test completed with errors, %0d errors found", error_ctr);
        end else begin
            $display("pwm_test completed successfully, all data matches expected values");
        end
    end
endtask

task zeroize_dut;
    write_single_word(MEM_DEPTH-3, {56'h0, 1'b1, 7'h0}); //zeroize ctrl reg
endtask

initial begin
    $display("Starting ntt_top_tb_fpga");

    init_sim();
    reset_dut();

    // zeroize_dut();

    //Run test
    $display("Running ct/gs test without shuffling and masking");
    $display("------------------------");
    #CLK_PERIOD;
    pgm_base_addr(14'h0, 14'h40, 14'h80); //src_base_addr, interim_base_addr, dest_base_addr
    #CLK_PERIOD;

    // ct_test(0);
    // $display("------------------------");
    // pgm_base_addr(14'h80, 14'h40, 14'h80); //src_base_addr, interim_base_addr, dest_base_addr
    // $display("------------------------");
    // gs_test(0,0,1); //shuf, mask, check

    // $display("Running ct/gs test with shuffling");
    // $display("------------------------");
    // #CLK_PERIOD;
    // pgm_base_addr(14'h0, 14'h40, 14'h80); //src_base_addr, interim_base_addr, dest_base_addr
    // #CLK_PERIOD;
    // ct_test(1);
    // $display("------------------------");
    // pgm_base_addr(14'h80, 14'h40, 14'h80); //src_base_addr, interim_base_addr, dest_base_addr
    // $display("------------------------");
    // gs_test(1,0,1); //shuf, mask, check

    // $display("------------------------");
    // pwm_test(0,0,0,1); //shuf, mask, acc, check_en
    // $display("------------------------");
    // pwm_test(0,0,1,1); //shuf, mask, acc
    // $display("------------------------");

    // $display("------------------------");
    // pwm_test(1,0,0,1); //shuf, mask, acc, check
    // $display("------------------------");
    // pwm_test(1,0,1,1); //shuf, mask, acc, check
    // $display("------------------------");


    // $display("----------Masking----------");
    // // ct_test(0);
    // $display("------------------------");
    // pwm_test(1,1,1,0);
    // $display("------------------------");
    // pgm_base_addr(14'h80, 14'h40, 14'h80); //src_base_addr, interim_base_addr, dest_base_addr
    // gs_test(0,1,0); //shuf, mask, check
    // $display("------------------------");

    //Sampler mode
    pwm_sampler_test(0,0,0);
    $display("------------------------");
    pwm_sampler_test(0,0,1);

    
    $display("End of ntt_top_tb_fpga");
    $finish;
end

endmodule
