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
bf_uvwi_t uvw_i_tb;
pwo_uvwi_t pw_uvw_i_tb;
logic masking_en_tb;

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

ntt_wrapper dut (
    .clk(clk_tb),
    .reset_n(reset_n_tb),
    .zeroize(zeroize_tb),
    .mode(mode_tb),
    .ntt_enable(enable_tb),
    .load_tb_values(load_tb_values),
    .load_tb_addr(load_tb_addr),
    .shuffle_en(1'b0),
    .random(random_tb),
    .masking_en(masking_en_tb),
    .rnd_i(230'h0),
    .ntt_mem_base_addr(ntt_mem_base_addr_tb),
    .pwo_mem_base_addr(pwo_mem_base_addr_tb),
    .accumulate(acc_tb),
    .sampler_valid(svalid_tb),
    .sampler_mode(sampler_mode_tb),
    .sampler_data(96'hFFFFFF),
    .ntt_done(ntt_done_tb),
    .ntt_busy()
);

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

    $display("Waiting for ntt_done\n");
    while(ntt_done_tb == 1'b0)
        @(posedge clk_tb);
    $display("Received ntt_done\n");

    
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
    repeat(41) @(posedge clk_tb);
    svalid_tb <= 1'b0;
    repeat(5) @(posedge clk_tb);
    svalid_tb <= 1'b1;
    @(posedge clk_tb);
    svalid_tb <= 1'b0;
    repeat(10) @(posedge clk_tb);
    svalid_tb <= 1'b1;
    @(posedge clk_tb);
    svalid_tb <= 1'b0;
    $display("Waiting for pwo_done\n");
    while(ntt_done_tb == 1'b0)
        @(posedge clk_tb);
    $display("Received pwo_done\n");

    $display("PWM+INTT operation\n");
    operation = "PWM INTT";
    mode_tb = pwm_intt;
    enable_tb = 1;
    acc_tb = 1'b0;
    svalid_tb = 1'b1;
    masking_en_tb = 1'b1;
    @(posedge clk_tb);
    enable_tb = 1'b0;
    $display("Waiting for pwo_done\n");
    while(ntt_done_tb == 1'b0)
        @(posedge clk_tb);
    $display("Received pwo_done\n");
    svalid_tb = 1'b0;
    @(posedge clk_tb);

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
    for (int i = 0; i < 512; i++) begin
        load_tb_addr = i;
        load_tb_values = 1'b1;
        @(posedge clk_tb);
    end
    load_tb_values = 1'b0;
    load_tb_addr = 'h0;
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
    ntt_top_test();
    // pwm_opt_test();
    repeat(1000) @(posedge clk_tb);
    $finish;
end

endmodule
