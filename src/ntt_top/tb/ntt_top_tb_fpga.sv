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
reg           cptra_pwrgood_tb;
reg           zeroize_tb;
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
    //.zeroize(zeroize_tb),
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
    random_tb <= $urandom();
    for (int i = 0; i < 5; i++)
        rnd_tb[i] <= $urandom();
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
    //   cptra_pwrgood_tb = '0;
      reset_n_tb = 0;
    
    //   #(2 * CLK_PERIOD);
    //   cptra_pwrgood_tb = 1;
    
      #(2 * CLK_PERIOD);
      reset_n_tb = 1;
    //   #(CLK_HALF_PERIOD);
    
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
        cptra_pwrgood_tb = 0;

        haddr_i_tb      = 0;
        hwdata_i_tb     = 0;
        hsel_i_tb       = 0;
        hwrite_i_tb     = 0;
        hready_i_tb     = 0;
        htrans_i_tb     = AHB_HTRANS_IDLE;
        hsize_i_tb      = 3'b011;

        random_tb <= 'h0;
        rnd_tb <= '0;

        /*
        data_i_tb = 'h0;
        zeroize_tb = 'b0;
        enable_tb = 'b0;
        wren_tb = 'b0; rden_tb = 'b0;
        wrptr_tb = 'h0; rdptr_tb = 'h0;

        mode_tb = ct;
        addr0 = 'h0; addr1 = 'h0; addr2 = 'h0; addr3 = 'h0;

        ntt_mem_base_addr_tb.src_base_addr = 'h0;
        ntt_mem_base_addr_tb.interim_base_addr = 'h0;
        ntt_mem_base_addr_tb.dest_base_addr = 'h0;

        pwo_mem_base_addr_tb.pw_base_addr_a = 'h0;
        pwo_mem_base_addr_tb.pw_base_addr_b = 'h40;
        pwo_mem_base_addr_tb.pw_base_addr_c = 'h80;

        //NTT ctrl
        bf_ready_tb = 1'b0;
        acc_tb = 1'b0;
        svalid_tb = 1'b0;
        sampler_mode_tb = 1'b0;
        

        //Masking
        for (int i = 0; i < 46; i++) begin
            u[i] = 2'h0;
            v[i] = 2'h0;
        end
        actual_u = 'h0;
        actual_v = 'h0;
        actual_w = 'h0;
        sub = 'h0;

        rnd0 = 'h0;
        rnd1 = 'h0;
        rnd2 = 'h0;
        rnd3 = 'h0;

        uvw_i_tb.u00_i = 'h0;
        uvw_i_tb.u01_i = 'h0;
        uvw_i_tb.v00_i = 'h0;
        uvw_i_tb.v01_i = 'h0;
        uvw_i_tb.w00_i = 'h0;
        uvw_i_tb.w01_i = 'h0;

        pw_uvw_i_tb.u0_i = 'h0;
        pw_uvw_i_tb.v0_i = 'h0;
        pw_uvw_i_tb.w0_i = 'h0;

        pw_uvw_i_tb.u1_i = 'h0;
        pw_uvw_i_tb.v1_i = 'h0;
        pw_uvw_i_tb.w1_i = 'h0;

        pw_uvw_i_tb.u2_i = 'h0;
        pw_uvw_i_tb.v2_i = 'h0;
        pw_uvw_i_tb.w2_i = 'h0;

        pw_uvw_i_tb.u3_i = 'h0;
        pw_uvw_i_tb.v3_i = 'h0;
        pw_uvw_i_tb.w3_i = 'h0;

        masking_en_tb = 'b0;
        shuffling_en_tb = 'b0;

        mlkem_tb = 'b0;
*/
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


task read_single_word_with_check(input [31 : 0]  address, input [63 : 0] expected_data);
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

    //   if (read_data != expected_data) begin
    //       $error("read_single_word_with_check: Read data mismatch at address %0d: expected %0d, got %0d", address, expected_data, read_data);
    //       error_ctr = error_ctr + 1;
    //   end else begin
    //       $display("read_single_word_with_check: Read data at address %0d: expected %0d, got %0d", address, expected_data, read_data);
    //   end
    end
endtask // read_single_word

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

task ct_test (input logic shuf_en);

    $display("Starting ct test");
    $display("Writing 1 poly to addr range 0 - 255");

    for (int i = 0; i < 256; i++) begin
        write_single_word(i, i);
    end

    $display("Writing base addr reg with src, interim and dest base addr");
    write_single_word(MEM_DEPTH-4, {22'h0, 14'h0, 14'h40, 14'h80}); //{src_base_addr, interim_base_addr, dest_base_addr}

    $display("Writing ctrl reg with mode and other ctrl signals");
    write_single_word(MEM_DEPTH-3, {57'h0, shuf_en, 1'b0, 1'b1, 1'b0, 3'h0}); //{shuf, mask, svalid, acc, mode}

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

task gs_test (input logic shuf_en, input logic mask_en, input logic check_en, input logic [13:0] src, 
              input logic [13:0] interim, input logic [13:0] dest);

    logic [255:0][63:0] obs_data;

    $display("Starting gs test");
    // $display("Writing 1 poly to addr range 0 - 255");

    // for (int i = 0; i < 256; i++) begin
    //     write_single_word(i, i);
    // end

    $display("Writing base addr reg with src, interim and dest base addr");
    write_single_word(MEM_DEPTH-4, {22'h0, src, interim, dest}); //{src_base_addr, interim_base_addr, dest_base_addr}

    $display("Writing ctrl reg with mode and other ctrl signals");
    write_single_word(MEM_DEPTH-3, {57'h0, shuf_en, mask_en, 1'b1, 1'b0, 3'h1}); //{shuf, mask, svalid, acc, mode}

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
                    // else begin
                    //     $display("pwm_test: Read data at address %0d: expected %0d, got %0d", (i+(128*4)), sampler_data_array[i]*i, read_data);
                    // end
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

task pwm_sampler_test (input logic shuf_en, input logic mask_en);
    logic [63:0] share0, share1;
    logic [23:0] combined_res;
    logic rand_svalid;
    logic [255:0][63:0] sampler_data_array;

    $display("Starting pwm, no acc, svalid test");
    $display("Writing 1 poly to addr range 0 - 255");

    for (int i = 0; i < 256; i++) begin
        write_single_word(i, i);
    end

    $display("Writing base addr reg with src, interim and dest base addr");
    write_single_word(MEM_DEPTH-4, {22'h0, 14'h0, 14'h40, 14'h80}); //{src_base_addr, interim_base_addr, dest_base_addr}
    $display("Writing ctrl reg with mode and other ctrl signals");
    write_single_word(MEM_DEPTH-3, {57'h0, shuf_en, mask_en, 1'b1, 1'b0, pwm}); //{shuf, mask, svalid, acc, mode}
    $display("Writing enable reg with enable signal");
    write_single_word(MEM_DEPTH-2, {63'h0, 1'b1}); //enable
    //pulse
    $display("Pulsing enable reg");
    write_single_word(MEM_DEPTH-2, 64'h0);
    #CLK_PERIOD;

    hsel_i_tb = 0;
    #(CLK_PERIOD);
    #(CLK_HALF_PERIOD);
    $display("Writing sampler data to dut at time %0t", $time);

    fork
        begin
            $display("Writing sampler data to dut at time %0t", $time);
            if (shuf_en)
                #(2*CLK_PERIOD);
            else
                #CLK_PERIOD;

            //TODO: masking
            for (int i = 0; i < 64; i++) begin
                sampler_input = {24'((i*4)+3), 24'((i*4)+2), 24'((i*4)+1), 24'(i*4)};
                sampler_data_array[(i*4)] = 64'(i*4);
                sampler_data_array[(i*4)+1] = 64'((i*4)+1);
                sampler_data_array[(i*4)+2] = 64'((i*4)+2);
                sampler_data_array[(i*4)+3] = 64'((i*4)+3);

                rand_svalid = $urandom_range(0,1);

                if (rand_svalid) begin
                    write_single_word(MEM_DEPTH-5, {40'h0, sampler_input[23:0]});
                    write_single_word(MEM_DEPTH-6, {40'h0, sampler_input[47:24]});
                    write_single_word(MEM_DEPTH-7, {40'h0, sampler_input[71:48]});
                    write_single_word(MEM_DEPTH-8, {40'h0, sampler_input[95:72]});
                end
                write_single_word(MEM_DEPTH-3, {57'h0, shuf_en, mask_en, rand_svalid, 1'b0, pwm}); //{shuf, mask, svalid, acc, mode}
            end
        end
        begin
            #CLK_PERIOD;
            $display("Waiting for PWM to complete at time %0t", $time);
            wait_ready();
            $display("PWM done, reading output at time %0t", $time);
            #CLK_PERIOD;
            hsel_i_tb = 0;
        end
    join

    //Read output thru AHB
    if (mask_en) begin
        fork
            begin
                for (int i = 0; i < 512; i+=2) begin
                    // $display("Index i = %0d", i);
                    read_single_word(i+(128*8));
                    share0 = read_data;
                    read_single_word(i+(128*8)+1);
                    share1 = read_data;
                    // $display("Done reading");
                end
            end
            begin
                #(4*CLK_PERIOD); //wait for read_single_word to read both shares
                for (int i = 0; i < 255; i++) begin
                    // $display("pwm_test: Read data obs %0d", read_data);
                    combined_res = share0 + share1;
                    if (sampler_data_array[i]*i != combined_res) begin
                        $error("pwm_test: Read data mismatch at address %0d: expected %0d, got %0d --> share0 = %0d, share1 = %0d", (i+(128*8)), sampler_data_array[i]*i, combined_res, share0, share1);
                        error_ctr = error_ctr + 1;
                    end 
                    // else begin
                    //     $display("pwm_test: Read data at address %0d: expected %0d, got %0d", (i+(128*4)), sampler_data_array[i]*i, read_data);
                    // end
                    #(2*CLK_PERIOD); //wait for read_single_word to read both shares
                end
            end
        join
        #CLK_PERIOD;
        hsel_i_tb = 0;
    end
    else begin
        fork
            begin
                for (int i = 0; i < 256; i++) begin
                    // $display("Index i = %0d", i);
                    read_single_word(i+(128*4));
                    // $display("Done reading");
                end
            end
            begin
                #(3*CLK_PERIOD);
                for (int i = 0; i < 255; i++) begin
                    // $display("pwm_test: Read data obs %0d", read_data);
                    if (sampler_data_array[i]*i != read_data) begin
                        $error("pwm_test: Read data mismatch at address %0d: expected %0d, got %0d", (i+(128*4)), sampler_data_array[i]*i, read_data);
                        error_ctr = error_ctr + 1;
                    end 
                    // else begin
                    //     $display("pwm_test: Read data at address %0d: expected %0d, got %0d", (i+(128*4)), sampler_data_array[i]*i, read_data);
                    // end
                    #(CLK_PERIOD);
                end
            end
        join
        #CLK_PERIOD;
        hsel_i_tb = 0;
    end

    if (error_ctr > 0) begin
        $error("pwm_test completed with errors, %0d errors found", error_ctr);
    end else begin
        $display("pwm_test completed successfully, all data matches expected values");
    end

endtask

task pwm_test (input logic shuf_en, input logic mask_en);
    logic [255:0][63:0] sampler_data_array;
    logic [63:0] share0, share1;
    logic [23:0] combined_res;

    $display("Starting pwm, no acc, svalid test");
    $display("Writing 1 poly to addr range 0 - 255");

    for (int i = 0; i < 512; i++) begin
        write_single_word(i, i);
    end

    $display("Writing base addr reg with src, interim and dest base addr");
    write_single_word(MEM_DEPTH-4, {22'h0, 14'h0, 14'h40, 14'h80}); //{src_base_addr, interim_base_addr, dest_base_addr}

    $display("Writing ctrl reg with mode and other ctrl signals");
    write_single_word(MEM_DEPTH-3, {57'h0, shuf_en, mask_en, 1'b1, 1'b0, 3'h2}); //{shuf, mask, svalid, acc, mode}

    $display("Writing enable reg with enable signal");
    write_single_word(MEM_DEPTH-2, {63'h0, 1'b1}); //enable

    //pulse
    $display("Pulsing enable reg");
    write_single_word(MEM_DEPTH-2, 64'h0);

    #CLK_PERIOD;
    hsel_i_tb = 0;

    #(CLK_PERIOD);
    #CLK_HALF_PERIOD;
    //Drive sampler input
    fork
        begin
            $display("Writing sampler data to dut at time %0t", $time);
            if (shuf_en)
                #(2*CLK_PERIOD);
            else
                #CLK_PERIOD;
            for (int i = 0; i < 64; i++) begin
                dut.sampler_data = {24'((i*4)+3), 24'((i*4)+2), 24'((i*4)+1), 24'(i*4)};
                sampler_data_array[(i*4)] = 64'(i*4);
                sampler_data_array[(i*4)+1] = 64'((i*4)+1);
                sampler_data_array[(i*4)+2] = 64'((i*4)+2);
                sampler_data_array[(i*4)+3] = 64'((i*4)+3);
                #CLK_PERIOD;
            end
        end
        begin
            #CLK_PERIOD;
            $display("Waiting for PWM to complete at time %0t", $time);
            wait_ready();
            $display("PWM done, reading output at time %0t", $time);
            #CLK_PERIOD;
            hsel_i_tb = 0;
        end
    join

    //Read output thru AHB
    if (mask_en) begin
        fork
            begin
                for (int i = 0; i < 512; i+=2) begin
                    // $display("Index i = %0d", i);
                    read_single_word(i+(128*8));
                    share0 = read_data;
                    read_single_word(i+(128*8)+1);
                    share1 = read_data;
                    // $display("Done reading");
                end
            end
            begin
                #(4*CLK_PERIOD); //wait for read_single_word to read both shares
                for (int i = 0; i < 255; i++) begin
                    // $display("pwm_test: Read data obs %0d", read_data);
                    combined_res = share0 + share1;
                    if (sampler_data_array[i]*i != combined_res) begin
                        $error("pwm_test: Read data mismatch at address %0d: expected %0d, got %0d --> share0 = %0d, share1 = %0d", (i+(128*8)), sampler_data_array[i]*i, combined_res, share0, share1);
                        error_ctr = error_ctr + 1;
                    end 
                    // else begin
                    //     $display("pwm_test: Read data at address %0d: expected %0d, got %0d", (i+(128*4)), sampler_data_array[i]*i, read_data);
                    // end
                    #(2*CLK_PERIOD); //wait for read_single_word to read both shares
                end
            end
        join
        #CLK_PERIOD;
        hsel_i_tb = 0;
    end
    else begin
        fork
            begin
                for (int i = 0; i < 256; i++) begin
                    // $display("Index i = %0d", i);
                    read_single_word(i+(128*4));
                    // $display("Done reading");
                end
            end
            begin
                #(3*CLK_PERIOD);
                for (int i = 0; i < 255; i++) begin
                    // $display("pwm_test: Read data obs %0d", read_data);
                    if (sampler_data_array[i]*i != read_data) begin
                        $error("pwm_test: Read data mismatch at address %0d: expected %0d, got %0d", (i+(128*4)), sampler_data_array[i]*i, read_data);
                        error_ctr = error_ctr + 1;
                    end 
                    // else begin
                    //     $display("pwm_test: Read data at address %0d: expected %0d, got %0d", (i+(128*4)), sampler_data_array[i]*i, read_data);
                    // end
                    #(CLK_PERIOD);
                end
            end
        join
        #CLK_PERIOD;
        hsel_i_tb = 0;
    end

    if (error_ctr > 0) begin
        $error("pwm_test completed with errors, %0d errors found", error_ctr);
    end else begin
        $display("pwm_test completed successfully, all data matches expected values");
    end


endtask

initial begin
    $display("Starting ntt_top_tb_fpga");

    init_sim();
    reset_dut();

    //Run test
    // $display("----------No masking, no shuffling----------");
    // ct_test(0);
    // $display("------------------------");
    // gs_test(0,0,1);
    // $display("------------------------");
    // pwm_test(0,0);
    // $display("------------------------");

    // $display("----------Shuffling----------");
    // ct_test(1);
    // $display("------------------------");
    // gs_test(1,0,1);
    // $display("------------------------");
    // pwm_test(1,0);
    // $display("------------------------");

    // $display("----------Masking----------");
    // // ct_test(0);
    // // $display("------------------------");
    // pwm_test(0,1);
    // $display("------------------------");
    // gs_test(0,1,0);
    // $display("------------------------");

    // $display("----------Both----------");
    // // ct_test(1);
    // // $display("------------------------");
    // // pwm_test(1,1);
    // // $display("------------------------");
    // init_mem_with_shares(14'h0);
    // gs_test(1,1,0, 14'h0, 14'h40, 14'h80);
    // $display("------------------------");

    //Sampler mode
    pwm_sampler_test(0,0);

    //TODO: make sampler_data input as a mem location that AHB can write to and continuously provide that data as sampler input to NTT
    //TODO: test accumulate

    $display("End of ntt_top_tb_fpga");
    $finish;
end

endmodule
