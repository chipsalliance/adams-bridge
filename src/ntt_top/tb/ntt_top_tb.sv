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
// ntt_top_tb.sv
// --------
// 
//
//
//======================================================================

`default_nettype none

module ntt_top_tb 

    import ntt_defines_pkg::*;
    import mldsa_params_pkg::*;
    
#(
    parameter   TEST_VECTOR_NUM = 10,
    parameter   PRIME     = 23'd8380417,
    parameter   REG_SIZE  = 23,
    parameter   MEM_DEPTH = 32768, //32 KB
    parameter   MEM_ADDR_WIDTH = $clog2(MEM_DEPTH)
)
();

parameter CLK_HALF_PERIOD = 5;
parameter CLK_PERIOD      = 2 * CLK_HALF_PERIOD;

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
reg [MLDSA_MEM_ADDR_WIDTH-1:0] load_tb_addr;

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
logic [45:0] rnd0, rnd1, rnd2, rnd3;
logic wren_tb, rden_tb;
logic [1:0] wrptr_tb, rdptr_tb;
logic [5:0] random_tb;

//----------------------------------------------------------------
// Device Under Test.
//----------------------------------------------------------------
// ntt_buffer #(
//     .REG_SIZE(REG_SIZE),
//     .NUM_COEFF(4)
// ) dut (
//     .clk(clk_tb),
//     .reset_n(reset_n_tb),
//     .zeroize(zeroize_tb),
//     .enable(enable_tb),
//     .data_i(data_i_tb),
//     .data_o(data_o_tb)
// );

// twiddle_rom dut (
//     .zeroize(),
//     .mode   (mode_tb),
//     .raddr00(addr0),
//     .raddr01(addr1),
//     .raddr10(addr2),
//     .raddr11(addr3),
//     .rdata00(data0),
//     .rdata01(data1),
//     .rdata10(data2),
//     .rdata11(data3)
// );

// ntt_ctrl dut (
//     .clk(clk_tb),
//     .reset_n(reset_n_tb),
//     .zeroize(zeroize_tb),
//     .ntt_mode(mode_tb),
//     .ntt_enable(enable_tb),
//     .butterfly_ready(bf_ready_tb)
// );

// ntt_top dut (
//     .clk(clk_tb),
//     .reset_n(reset_n_tb),
//     .zeroize(zeroize_tb),
//     .mode(mode_tb),
//     .ntt_enable(enable_tb),
//     .load_tb_values(load_tb_values),
//     .load_tb_addr(load_tb_addr),
//     // .src_base_addr(src_base_addr),
//     // .interim_base_addr(interim_base_addr),
//     // .dest_base_addr(dest_base_addr),
//     // .pw_base_addr_a(8'd0),
//     // .pw_base_addr_b(8'd0),
//     // .pw_base_addr_c(8'd0),
//     .ntt_mem_base_addr(ntt_mem_base_addr_tb),
//     .pwo_mem_base_addr(pwo_mem_base_addr_tb),
//     .accumulate(acc_tb),
//     .sampler_valid(svalid_tb)
// );

// ntt_wrapper dut (
//     .clk(clk_tb),
//     .reset_n(reset_n_tb),
//     .zeroize(zeroize_tb),
//     .mode(mode_tb),
//     .ntt_enable(enable_tb),
//     .load_tb_values(load_tb_values),
//     .load_tb_addr(load_tb_addr),
//     .ntt_mem_base_addr(ntt_mem_base_addr_tb),
//     .pwo_mem_base_addr(pwo_mem_base_addr_tb),
//     .accumulate(acc_tb),
//     .sampler_valid(svalid_tb),
//     .sampler_mode(sampler_mode_tb),
//     .sampler_data(96'hFFFFFF),
//     .ntt_done(ntt_done_tb),
//     .ntt_busy()
// );

// ntt_masked_BFU_add_sub dut (
//     .clk(clk_tb),
//     .reset_n(reset_n_tb),
//     .zeroize(zeroize_tb),
//     .sub(sub),
//     .u(u),
//     .v(v),
//     .rnd0(rnd0),
//     .rnd1(rnd1),
//     .rnd2(rnd2),
//     .rnd3(rnd3),
//     .res()
// );

// ntt_masked_BFU_mult dut (
//     .clk(clk_tb),
//     .reset_n(reset_n_tb),
//     .zeroize(zeroize_tb),
//     .u(u),
//     .v(v),
//     .rnd0(rnd0),
//     .rnd1(rnd1),
//     .rnd2(rnd2),
//     .rnd3(rnd3),
//     .rnd4(rnd0+rnd1),
//     .res()
// );

// ntt_shuffle_buffer dut (
//     .clk(clk_tb),
//     .reset_n(reset_n_tb),
//     .zeroize(zeroize_tb),
//     .wren(wren_tb),
//     .rden(rden_tb),
//     .wrptr(wrptr_tb),
//     .rdptr(rdptr_tb),
//     .wr_rst_count(),
//     .data_i(data_i_tb),
//     .buf_valid(),
//     .data_o()
// );

ntt_masked_gs_butterfly dut (
    .clk(clk_tb),
    .reset_n(reset_n_tb),
    .zeroize(zeroize_tb),
    .opu_i(u),
    .opv_i(v),
    .opw_i(w),
    .rnd_i({rnd0+rnd1, rnd3, rnd2, rnd1, rnd0}),
    .u_o(),
    .v_o()
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
  rnd0 = $random();
  rnd1 = $random();
  rnd2 = $random();
  rnd3 = $random();
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
        random_tb <= 'h0;

        //Masking
        for (int i = 0; i < 46; i++) begin
            u[i] = 2'h0;
            v[i] = 2'h0;
        end
        actual_u = 'h0;
        actual_v = 'h0;
        sub = 'h0;

        $display("End of init\n");
    end
endtask

task buffer_test();
    reg [REG_SIZE-1:0] i;
    reg [1:0] j;
    wren_tb <= 1'b1;
    rden_tb <= 'b1;
    for (i = 0; i < 64; i++) begin
        // data_i_tb <= {(i*23'd64)+23'd192, (i*23'd64)+23'd128, (i*23'd64)+23'd64, (i*23'd64)};
        wrptr_tb <= i%4;
        j = $urandom_range(3);
        rdptr_tb <= (i%4)+j;
        data_i_tb <= {(i*23'd64)+23'd3, (i*23'd64)+23'd2, (i*23'd64)+23'd1, i*23'd64}; //{23'd3, 23'd2, 23'd1, 23'd0};
        @(posedge clk_tb);
    end
    wren_tb <= 1'b0;
    rden_tb <= 'b0;
endtask

task twiddle_rom_test();
    int i;
    for(i = 0; i < 256; i++) begin
        addr0 <= i; addr1 <= i; addr2 <= i; addr3 <= i;
        if (data0 != zeta[i])
            $display("Error, test failed while reading NTT twiddle rom at index %0d, observed value = %h, actual value = %h", i, data0, zeta[i]);    
        // if (data1 != zeta[i])
        //     $display("Error, test failed while reading NTT twiddle rom at index %0d", i);    
        // if (data2 != zeta[i])
        //     $display("Error, test failed while reading NTT twiddle rom at index %0d", i);    
        // if (data3 != zeta[i])
        //     $display("Error, test failed while reading NTT twiddle rom at index %0d", i);    
        
        // @(posedge clk_tb);
    end
    mode_tb <= gs;
    for(i = 0; i < 256; i++) begin
        addr0 <= i; addr1 <= i; addr2 <= i; addr3 <= i;
        if (data0 != zeta_inv[i])
            $display("Error, test failed while reading INTT twiddle rom at index %0d, observed value = %h, actual value = %h", i, data0, zeta_inv[i]);    
        // if (data1 != zeta_inv[i])
        //     $display("Error, test failed while reading INTT twiddle rom at index %0d", i);    
        // if (data2 != zeta_inv[i])
        //     $display("Error, test failed while reading INTT twiddle rom at index %0d", i);    
        // if (data3 != zeta_inv[i])
        //     $display("Error, test failed while reading INTT twiddle rom at index %0d", i);
        // @(posedge clk_tb);
    end
    @(posedge clk_tb);
endtask

task ntt_ctrl_test();
    mode_tb = ct;
    enable_tb = 1;
    repeat(16) @(posedge clk_tb); //IDLE - STAGE - RD MEM - RD AND EXE = 1 + 1 + 4 + 10 = 16 clk delay
    bf_ready_tb = 1'b1;
    repeat(64) @(posedge clk_tb);
    bf_ready_tb = 1'b0;
    repeat(10) @(posedge clk_tb);
    bf_ready_tb = 1'b1;
    repeat(64) @(posedge clk_tb);
    bf_ready_tb = 1'b0;
endtask

task ntt_top_test();
    fork
        begin
            while(1) begin
                random_tb <= $urandom();
                @(posedge clk_tb);
            end
        end
        begin
    $display("NTT operation\n");
    operation = "NTT";
    mode_tb = ct;
    enable_tb = 1;
    ntt_mem_base_addr_tb.src_base_addr = 8'd0;
    ntt_mem_base_addr_tb.interim_base_addr = 8'd64;
    ntt_mem_base_addr_tb.dest_base_addr = 8'd128;
    acc_tb = 1'b0;
    svalid_tb = 1'b1;
    @(posedge clk_tb);
    enable_tb = 1'b0;

    // while(dut.ntt_top_inst0.ntt_ctrl_inst0.rounds_count == 'h0)
    //     @(posedge clk_tb);
    // random_tb = {4'h9, 2'h3};

    // while(dut.ntt_top_inst0.ntt_ctrl_inst0.rounds_count == 'h1)
    //     @(posedge clk_tb);
    // random_tb = {4'h0, 2'h2};

    // while(dut.ntt_top_inst0.ntt_ctrl_inst0.rounds_count == 'h2)
    //     @(posedge clk_tb);
    // random_tb = {4'hf, 2'h0};

    $display("Waiting for ntt_done\n");
    while(ntt_done_tb == 1'b0)
        @(posedge clk_tb);
    $display("Received ntt_done\n");

    // for (int i = 0; i < 64; i++) begin
    //     if (dut.ntt_mem.mem[i+dest_base_addr] != ntt_mem_tb[i])
    //         $display("Error: NTT data mismatch at index %0d (dest_base addr = %0d). Actual data = %h, expected data = %h", i, dest_base_addr, dut.ntt_mem.mem[i+dest_base_addr], ntt_mem_tb[i]);
    //     @(posedge clk_tb);
    // end
    //     end
    // join
    // fork
    //         begin
    //             while(ntt_done_tb == 1'b0) begin
    //                 random_tb = $urandom();
    //                 @(posedge clk_tb);
    //             end
    //         end
    //         begin
    $display("INTT operation\n");
    operation = "INTT";
    mode_tb = gs;
    enable_tb = 1;
    ntt_mem_base_addr_tb.src_base_addr = 8'd128; //read from addr where ntt stored its results
    ntt_mem_base_addr_tb.interim_base_addr = 8'd64;
    ntt_mem_base_addr_tb.dest_base_addr = 8'd128;
    acc_tb = 1'b0;
    @(posedge clk_tb);
    enable_tb = 1'b0;
    $display("Waiting for intt_done\n");
    while(ntt_done_tb == 1'b0)
        @(posedge clk_tb);
    $display("Received intt_done\n");
    
    $display("PWM operation 1\n");
    operation = "PWM 1 no acc";
    // $readmemh("pwm_iter1.hex", ntt_mem_tb);
    mode_tb = pwm;
    enable_tb = 1;
    acc_tb = 1'b0;
    @(posedge clk_tb);
    enable_tb = 1'b0;
    $display("Waiting for pwo_done\n");
    while(ntt_done_tb == 1'b0)
        @(posedge clk_tb);
    $display("Received pwo_done\n");

    // for (int i = 0; i < 64; i++) begin
    //     if (dut.pwm_mem_c.mem[i+0] != ntt_mem_tb[i])
    //         $display("Error: PWM data mismatch at index %0d (pw_base_addr_c = %0d). Actual data = %h, expected data = %h", i, 0, dut.pwm_mem_c.mem[i+0], ntt_mem_tb[i]);
    //     @(posedge clk_tb);
    // end


    $display("PWM operation 2\n");
    operation = "PWM 2 no acc";
    mode_tb = pwm;
    enable_tb = 1;
    acc_tb = 1'b0;
    @(posedge clk_tb);
    enable_tb = 1'b0;
    $display("Waiting for pwo_done\n");
    while(ntt_done_tb == 1'b0)
        @(posedge clk_tb);
    $display("Received pwo_done\n");

    $display("PWM operation 3\n");
    operation = "PWM 3 acc";
    mode_tb = pwm;
    enable_tb = 1;
    acc_tb = 1'b1;
    $readmemh("pwm_iter2.hex", ntt_mem_tb);
    @(posedge clk_tb);
    enable_tb = 1'b0;
    $display("Waiting for pwo_done\n");
    while(ntt_done_tb == 1'b0)
        @(posedge clk_tb);
    $display("Received pwo_done\n");

    // $readmemh("pwm_iter2.hex", ntt_mem_tb);
    // for (int i = 0; i < 64; i++) begin
    //     if (dut.pwm_mem_c.mem[i+0] != ntt_mem_tb[i])
    //         $display("Error: PWM data mismatch at index %0d (pw_base_addr_c = %0d). Actual data = %h, expected data = %h", i, 0, dut.pwm_mem_c.mem[i+0], ntt_mem_tb[i]);
    //     @(posedge clk_tb);
    // end

    $display("PWA operation 1\n");
    operation = "PWA 1";
    mode_tb = pwa;
    enable_tb = 1;
    acc_tb = 1'b0;
    @(posedge clk_tb);
    enable_tb = 1'b0;
    $display("Waiting for pwo_done\n");
    while(ntt_done_tb == 1'b0)
        @(posedge clk_tb);
    $display("Received pwo_done\n");

    $display("PWA operation 2\n");
    operation = "PWA 2";
    mode_tb = pwa;
    enable_tb = 1;
    acc_tb = 1'b0;
    @(posedge clk_tb);
    enable_tb = 1'b0;
    $display("Waiting for pwo_done\n");
    while(ntt_done_tb == 1'b0)
        @(posedge clk_tb);
    $display("Received pwo_done\n");

    $display("PWA operation 3\n");
    operation = "PWA 3";
    mode_tb = pwa;
    enable_tb = 1;
    acc_tb = 1'b0;
    @(posedge clk_tb);
    enable_tb = 1'b0;
    $display("Waiting for pwo_done\n");
    while(ntt_done_tb == 1'b0)
        @(posedge clk_tb);
    $display("Received pwo_done\n");

    $display("PWS operation 1\n");
    operation = "PWS 1";
    mode_tb = pws;
    enable_tb = 1;
    acc_tb = 1'b0;
    @(posedge clk_tb);
    enable_tb = 1'b0;
    $display("Waiting for pwo_done\n");
    while(ntt_done_tb == 1'b0)
        @(posedge clk_tb);
    $display("Received pwo_done\n");

    $display("PWS operation 2\n");
    operation = "PWS 2";
    mode_tb = pws;
    enable_tb = 1;
    acc_tb = 1'b0;
    @(posedge clk_tb);
    enable_tb = 1'b0;
    $display("Waiting for pwo_done\n");
    while(ntt_done_tb == 1'b0)
        @(posedge clk_tb);
    $display("Received pwo_done\n");

    $display("PWS operation 3\n");
    operation = "PWS 3";
    mode_tb = pws;
    enable_tb = 1;
    acc_tb = 1'b0;
    @(posedge clk_tb);
    enable_tb = 1'b0;
    $display("Waiting for pwo_done\n");
    while(ntt_done_tb == 1'b0)
        @(posedge clk_tb);
    $display("Received pwo_done\n");
    svalid_tb = 1'b0;
    @(posedge clk_tb);

    

    $display("PWM + sampler operation 1\n");
    operation = "PWM sampler";
    mode_tb = pwm;
    enable_tb = 1;
    acc_tb = 1'b0;
    sampler_mode_tb = 1'b1;
    repeat(2) @(posedge clk_tb);
    svalid_tb <= 1'b1;
    @(posedge clk_tb);
    enable_tb = 1'b0;
    repeat(10) @(posedge clk_tb);
    svalid_tb <= 1'b0;
    repeat(10) @(posedge clk_tb);
    svalid_tb <= 1'b1;
    repeat(10) @(posedge clk_tb);
    svalid_tb <= 1'b0;
    repeat(10) @(posedge clk_tb);
    svalid_tb <= 1'b1;
    repeat(45) @(posedge clk_tb);
    svalid_tb <= 1'b0;
    $display("Waiting for pwo_done\n");
    while(ntt_done_tb == 1'b0)
        @(posedge clk_tb);
    $display("Received pwo_done\n");
    
        end
    join_any
    $display("End of test\n");
endtask
/*
task pwm_opt_test();
    $display("PWM operation 1\n");
    $readmemh("pwm_iter1.hex", ntt_mem_tb);
    mode_tb = pwm;
    enable_tb = 1;
    acc_tb = 1'b0;
    svalid_tb = 1'b1;
    @(posedge clk_tb);
    enable_tb = 1'b0;
    $display("Waiting for rd_exec\n");
    while(dut.ntt_top_inst0.ntt_ctrl_inst0.read_fsm_state_ps != RD_EXEC)
        @(posedge clk_tb);
    $display("Waiting for rd_stage\n");
    while(dut.ntt_top_inst0.ntt_ctrl_inst0.read_fsm_state_ps != RD_STAGE)
        @(posedge clk_tb);
    $display("Read fsm transitioned to rd_stage state. Queuing next pwm\n");

    // for (int i = 0; i < 64; i++) begin
    //     if (dut.pwm_mem_c.mem[i+0] != ntt_mem_tb[i])
    //         $display("Error: PWM data mismatch at index %0d (pw_base_addr_c = %0d). Actual data = %h, expected data = %h", i, 0, dut.pwm_mem_c.mem[i+0], ntt_mem_tb[i]);
    //     @(posedge clk_tb);
    // end


    $display("PWM operation 2\n");
    mode_tb = pwm;
    enable_tb = 1;
    acc_tb = 1'b0;
    @(posedge clk_tb);
    enable_tb = 1'b0;
    $display("Waiting for rd_exec\n");
    while(dut.ntt_top_inst0.ntt_ctrl_inst0.read_fsm_state_ps != RD_EXEC)
        @(posedge clk_tb);
    $display("Waiting for rd_stage\n");
    while(dut.ntt_top_inst0.ntt_ctrl_inst0.read_fsm_state_ps != RD_STAGE)
        @(posedge clk_tb);
    $display("Read fsm transitioned to rd_stage state. Queuing next pwm\n");

    $display("PWM operation 3\n");
    mode_tb = pwm;
    enable_tb = 1;
    acc_tb = 1'b1;
    $readmemh("pwm_iter2.hex", ntt_mem_tb);
    @(posedge clk_tb);
    enable_tb = 1'b0;
    $display("Waiting for pwo_done\n");
    while(ntt_done_tb == 1'b0)
        @(posedge clk_tb);
    $display("Received pwo_done\n");

    for (int i = 0; i < 64; i++) begin
        if (dut.ntt_mem.mem[i+0] != ntt_mem_tb[i])
            $display("Error: PWM data mismatch at index %0d (pw_base_addr_c = %0d). Actual data = %h, expected data = %h", i, 0, dut.ntt_mem.mem[i+0], ntt_mem_tb[i]);
        @(posedge clk_tb);
    end
endtask
*/
task init_mem();
    for (int i = 0; i < 32768; i++) begin
        load_tb_addr = i;
        load_tb_values = 1'b1;
        @(posedge clk_tb);
    end
    load_tb_values = 1'b0;
    load_tb_addr = 'h0;
endtask

/*
task masked_BFU_adder_test();
    logic [45:0] u_array, v_array;
    logic [45:0] rand0, rand1;
    sub = 1;
    for (int i = 0; i < 1000; i++) begin
        @(posedge clk_tb);
        fork
            begin
                actual_u = $random()%PRIME;
                actual_v = $random()%PRIME;
                u_array = actual_u;
                v_array = actual_v;
                rand0 = $random();
                rand1 = $random();

                u[0] = actual_u-rand0;
                u[1] = rand0;
                v[0] = actual_v-rand1;
                v[1] = rand1;
                // $display("u0 = %h, u1 = %h, v0 = %h, v1 = %h", u[0], u[1], v[0], v[1]);
            end
            begin
                repeat(54) @(posedge clk_tb);
                if (!sub) begin
                    if ((dut.add_res_reduced[1] + dut.add_res_reduced[0]) != ((u_array + v_array)%PRIME)) begin
                        $error("Addition Mismatch: exp_output = %h   output shares = %h %h actual output = %h", (u_array + v_array)%PRIME, dut.add_res_reduced[0], dut.add_res_reduced[1], dut.add_res_reduced[0] + dut.add_res_reduced[1]);
                    end
                end
                else begin
                    if ((dut.add_res_reduced[1] + dut.add_res_reduced[0]) != ((u_array - v_array + PRIME)%PRIME)) begin
                        $error("Subtraction Mismatch: exp_output = %h   output shares = %h %h actual output = %h", (u_array + PRIME + (~v_array+'h1))%PRIME, dut.add_res_reduced[0], dut.add_res_reduced[1], dut.add_res_reduced[0] + dut.add_res_reduced[1]);
                    end
                end
            end
        join
    end
endtask
*/
/*
task masked_BFU_mult_test();
    logic [45:0] u_array, v_array;
    logic [45:0] rand0, rand1;

    for (int i = 0; i < 10; i++) begin
        @(posedge clk_tb);
        fork
            begin
                actual_u = $random()%PRIME;
                actual_v = $random()%PRIME;
                u_array = actual_u;
                v_array = actual_v;
                rand0 = $random();
                rand1 = $random();

                // $display("actual u = %h, actual v = %h", actual_u, actual_v);

                u[0] = actual_u-rand0;
                u[1] = rand0;
                v[0] = actual_v-rand1;
                v[1] = rand1;
                // $display("u0 = %h, u1 = %h, v0 = %h, v1 = %h", u[0], u[1], v[0], v[1]);
            end
            begin
                repeat(3) @(posedge clk_tb);
                if ((dut.final_res[1] + dut.final_res[0]) != ((u_array * v_array)%PRIME)) begin
                    $error("Multiplication Mismatch: exp_output = %h   output shares = %h %h actual output = %h", (u_array * v_array)%PRIME, dut.final_res[0], dut.final_res[1], dut.final_res[0] + dut.final_res[1]);
                end
            end
        join
    end
endtask
*/

task masked_gs_butterfly_test();
    logic [45:0] rand0, rand1, rand2;
    for (int i = 0; i < 10; i++) begin
        @(posedge clk_tb);
        fork
            begin
                actual_u = $random()%PRIME;
                actual_v = $random()%PRIME;
                actual_w = 'h2;
                // u_array = actual_u;
                // v_array = actual_v;
                rand0 = $random();
                rand1 = $random();
                rand2 = $random();

                // $display("actual u = %h, actual v = %h", actual_u, actual_v);

                u[0] = actual_u-rand0;
                u[1] = rand0;
                v[0] = actual_v-rand1;
                v[1] = rand1;
                w[0] = actual_w-rand2;
                w[1] = rand2;
                // $display("u0 = %h, u1 = %h, v0 = %h, v1 = %h", u[0], u[1], v[0], v[1]);
            end
            //TODO: check with Emre - when doing (u-v), should exp result be ((u-v)+Q) % Q to account for negative nums? FPV had issues with this, so do (if u < v), result + Q
            // begin
            //     repeat(3) @(posedge clk_tb);
            //     if ((dut.final_res[1] + dut.final_res[0]) != ((u_array * v_array)%PRIME)) begin
            //         $error("Multiplication Mismatch: exp_output = %h   output shares = %h %h actual output = %h", (u_array * v_array)%PRIME, dut.final_res[0], dut.final_res[1], dut.final_res[0] + dut.final_res[1]);
            //     end
            // end
        join
    end
endtask

initial begin
    init_sim();
    reset_dut();
    // $readmemh("zeta.txt", zeta);
    // $readmemh("zeta_inv.hex", zeta_inv);

    @(posedge clk_tb);
    $display("Starting init mem\n");
    init_mem();
    // $readmemh("ntt_stage67.hex", ntt_mem_tb);
    @(posedge clk_tb);
    // buffer_test();
    // twiddle_rom_test();
    // ntt_ctrl_test();
    $display("Starting ntt test\n");
    // ntt_top_test();
    // masked_BFU_adder_test();
    // masked_BFU_mult_test();
    masked_gs_butterfly_test();
    // pwm_opt_test();
    repeat(1000) @(posedge clk_tb);
    $finish;
end

endmodule
