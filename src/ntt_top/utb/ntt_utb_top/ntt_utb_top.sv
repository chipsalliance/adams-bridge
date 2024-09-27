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
// import ntt_defines_pkg::*;

module ntt_utb_top
    import mldsa_params_pkg::*;
    #(
    parameter REG_SIZE = 24,
    parameter RADIX = 23,
    parameter MLDSA_Q = 23'd8380417,
    parameter MLDSA_N = 256
);

    // Clock and reset
    bit clk;
    bit rst;

    ntt_if ntt_if_i(clk);
    mem_if ntt_mem_if_i(clk);
    mem_if pwm_a_mem_if_i(clk);
    mem_if pwm_b_mem_if_i(clk);

    // Connect reset to the interfaces
    assign ntt_if_i.reset_n = rst;
    assign ntt_mem_if_i.reset_n = rst;
    assign pwm_a_mem_if_i.reset_n = rst;
    assign pwm_b_mem_if_i.reset_n = rst;

    // UNUSED PORTs
    assign pwm_a_mem_if_i.mem_port0_req.rd_wr_en = mem_rw_mode_e'(RW_IDLE);
    assign pwm_a_mem_if_i.mem_port0_req.addr = 'h0;
    assign pwm_b_mem_if_i.mem_port0_req.rd_wr_en = mem_rw_mode_e'(RW_IDLE);
    assign pwm_b_mem_if_i.mem_port0_req.addr = 'h0;

    //Port a signal that indicates NTT completes its stages
    localparam int DELAY_CYCLES = 2;
    logic [DELAY_CYCLES-1:0] stage_done_array;
    logic delayed_done;
    logic wired_ntt_done;
    assign ntt_if_i.stage_done = stage_done_array[DELAY_CYCLES-1];
    assign ntt_if_i.ntt_done = delayed_done;

    

    // TAKEN FROM ntt_wrapper

    //NTT, PWM C memory IF
    mem_if_t mem_port0_req;
    mem_if_t mem_rd_req;
    logic [MEM_DATA_WIDTH-1:0] mem_wr_data;
    logic [MEM_DATA_WIDTH-1:0] mem_rd_data;


    //PWM A/B, PWA/S memory IF
    mem_if_t pwm_a_rd_req;
    mem_if_t pwm_b_rd_req;
    logic [MEM_DATA_WIDTH-1:0] pwm_a_rd_data;
    logic [MEM_DATA_WIDTH-1:0] pwm_b_rd_data;

    //NTT/PWM muxes
    logic ntt_mem_wren, ntt_mem_rden;
    logic [MLDSA_MEM_ADDR_WIDTH-1:0] ntt_mem_wr_addr;
    logic [MLDSA_MEM_ADDR_WIDTH-1:0] ntt_mem_rd_addr;
    logic [MEM_DATA_WIDTH-1:0] ntt_mem_wr_data;
    logic [MEM_DATA_WIDTH-1:0] ntt_mem_rd_data;

    logic pwm_mem_a_rden, pwm_mem_b_rden;

    //Modes
    logic ct_mode;
    logic gs_mode;
    logic pwo_mode;
    logic pwm_mode, pwa_mode, pws_mode;

    assign ct_mode = (ntt_if_i.mode == ct);
    assign gs_mode = (ntt_if_i.mode == gs);
    assign pwo_mode = (ntt_if_i.mode inside {pwm, pwa, pws});
    assign pwm_mode = (ntt_if_i.mode == pwm);
    assign pwa_mode = (ntt_if_i.mode == pwa);
    assign pws_mode = (ntt_if_i.mode == pws);

    //NTT mem
    assign ntt_mem_wren = (ntt_mem_if_i.mem_port0_req.rd_wr_en == RW_WRITE);
    assign ntt_mem_rden = (ntt_mem_if_i.mem_port1_req.rd_wr_en == RW_READ);
    
    //PWM mem
    assign pwm_mem_a_rden = (pwm_a_mem_if_i.mem_port1_req.rd_wr_en == RW_READ);
    assign pwm_mem_b_rden = (pwm_b_mem_if_i.mem_port1_req.rd_wr_en == RW_READ);

    ntt_ram_tdp_file #(
        .ADDR_WIDTH(MLDSA_MEM_ADDR_WIDTH),
        .DATA_WIDTH(4*REG_SIZE)
    ) ntt_mem (
        .clk(clk),
        .reset_n(rst),
        .zeroize(ntt_if_i.zeroize),
        .ena(ntt_mem_wren),
        .wea(ntt_mem_wren),
        .addra(ntt_mem_if_i.mem_port0_req.addr),
        .dina(ntt_mem_if_i.p0_write_data),
        .douta(), //Need only one read port, so this can be 0
        .enb(ntt_mem_rden),
        .web(1'b0), //Need only one write port so this can be 0
        .addrb(ntt_mem_if_i.mem_port1_req.addr),
        .dinb(),
        .doutb(ntt_mem_if_i.p1_read_data),
        .load_tb_values(1'b0),
        .load_tb_addr({MLDSA_MEM_ADDR_WIDTH{1'b0}})
    );

    ntt_ram_tdp_file #(
        .ADDR_WIDTH(MLDSA_MEM_ADDR_WIDTH),
        .DATA_WIDTH(4*REG_SIZE)
    ) pwm_mem_a (
        .clk(clk),
        .reset_n(rst),
        .zeroize(ntt_if_i.zeroize),
        .ena(),
        .wea(),
        .addra(),
        .dina(),
        .douta(), //Need only one read port, so this can be 0
        .enb(pwm_mem_a_rden), //(pw_rden_d1),
        .web(1'b0), //Need only one write port so this can be 0
        .addrb(pwm_a_mem_if_i.mem_port1_req.addr), //(pwm_rd_addr_a_reg),
        .dinb(),
        .doutb(pwm_a_mem_if_i.p1_read_data),
        .load_tb_values(1'b0),
        .load_tb_addr({MLDSA_MEM_ADDR_WIDTH{1'b0}})
    );

    ntt_ram_tdp_file #(
        .ADDR_WIDTH(MLDSA_MEM_ADDR_WIDTH),
        .DATA_WIDTH(4*REG_SIZE)
    ) pwm_mem_b (
        .clk(clk),
        .reset_n(rst),
        .zeroize(ntt_if_i.zeroize),
        .ena(),
        .wea(),
        .addra(),
        .dina(),
        .douta(), //Need only one read port, so this can be 0
        .enb(pwm_mem_b_rden), //(pw_rden_d1),
        .web(1'b0), //Need only one write port so this can be 0
        .addrb(pwm_b_mem_if_i.mem_port1_req.addr), //(pwm_rd_addr_b_reg),
        .dinb(),
        .doutb(pwm_b_mem_if_i.p1_read_data),
        .load_tb_values(1'b0),
        .load_tb_addr({MLDSA_MEM_ADDR_WIDTH{1'b0}})
    );

    ntt_top #(
        .REG_SIZE(REG_SIZE),
        .MLDSA_Q(MLDSA_Q),
        .MLDSA_N(MLDSA_N),
        .MEM_ADDR_WIDTH(MLDSA_MEM_ADDR_WIDTH)
    )
    ntt_top_inst0 (
        .clk(clk),
        .reset_n(rst),
        .zeroize(ntt_if_i.zeroize),
        .mode(ntt_if_i.mode),
        .ntt_enable(ntt_if_i.ntt_enable),

        .ntt_mem_base_addr(ntt_if_i.ntt_mem_base_addr),
        .pwo_mem_base_addr(ntt_if_i.pwo_mem_base_addr),

        .accumulate(ntt_if_i.accumulate),
        .sampler_valid(ntt_if_i.sampler_valid),
        //NTT mem IF
        .mem_wr_req(ntt_mem_if_i.mem_port0_req),
        .mem_rd_req(ntt_mem_if_i.mem_port1_req),
        .mem_wr_data(ntt_mem_if_i.p0_write_data),
        .mem_rd_data(ntt_mem_if_i.p1_read_data),
        //PWM mem IF
        .pwm_a_rd_req(pwm_a_mem_if_i.mem_port1_req),
        .pwm_b_rd_req(pwm_b_mem_if_i.mem_port1_req),
        .pwm_a_rd_data(pwm_a_mem_if_i.p1_read_data),
        .pwm_b_rd_data(ntt_if_i.sampler_mode ? ntt_if_i.sampler_data : pwm_a_mem_if_i.p1_read_data),
        .ntt_busy(),
        .ntt_done(wired_ntt_done)
    );


    always_ff @(posedge clk) begin
        stage_done_array <= {stage_done_array[DELAY_CYCLES-2:0], ntt_top_inst0.ntt_ctrl_inst0.stage_done};
        delayed_done <= wired_ntt_done;
    end

    always begin
        #1 clk = ~clk;
    end

    initial begin
        clk = 0;
        rst = 1;
        #10; rst = 0;
        #10; rst = 1;
    end

    initial begin
        // Set the virtual interfaces in the UVM configuration database
        ntt_mem_if_i.mem_path = "mem_ntt";
        pwm_a_mem_if_i.mem_path = "mem_pwm_a";
        pwm_b_mem_if_i.mem_path = "mem_pwm_b";
        uvm_config_db#(virtual ntt_if)::set(null, "*", "ntt_vif", ntt_if_i);
        uvm_config_db#(virtual mem_if)::set(null, "*", "ntt_mem_vif", ntt_mem_if_i);
        uvm_config_db#(virtual mem_if)::set(null, "*", "pwm_a_mem_vif", pwm_a_mem_if_i);
        uvm_config_db#(virtual mem_if)::set(null, "*", "pwm_b_mem_vif", pwm_b_mem_if_i);
        run_test();
    end


endmodule: ntt_utb_top