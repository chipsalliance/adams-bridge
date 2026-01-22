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
// ntt_wrapper.sv
// Temp Top level that contains NTT and mem
// TODO: remove after top level NTT integration is done
//======================================================================

module ntt_wrapper
    import ntt_defines_pkg::*;
    import abr_params_pkg::*;
#(
    parameter REG_SIZE = 24,
    parameter RADIX = 23,
    parameter MLDSA_Q = 23'd8380417,
    parameter MLDSA_N = 256,
    parameter MEM_ADDR_WIDTH = ABR_MEM_ADDR_WIDTH,
    parameter MEM_DATA_WIDTH = 96
)
(
    input wire clk,
    input wire reset_n,
    input wire zeroize,

    input mode_t mode,
    input wire ntt_enable,
    input wire mlkem,
    input wire shuffle_en,
    input wire masking_en,
    input wire [5:0] random,
    input wire [4:0][45:0] rnd_i,
    
    //TB purpose
    input wire load_tb_values,
    input wire load_random_values,
    input wire load_pwm_a_values,
    input wire load_pwm_b_values,

    input ntt_mem_addr_t ntt_mem_base_addr,
    input pwo_mem_addr_t pwo_mem_base_addr,
    input wire accumulate,
    input wire sampler_valid,
    input wire sampler_mode,
    input wire [MEM_DATA_WIDTH-1:0] sampler_data,
    output logic ntt_done,
    output logic ntt_busy

);

    //NTT, PWM C memory IF
    mem_if_t mem_wr_req;
    mem_if_t mem_rd_req;
    logic [ABR_MEM_MASKED_DATA_WIDTH-1:0] mem_wr_data;
    logic [ABR_MEM_MASKED_DATA_WIDTH-1:0] mem_rd_data_int, mem_rd_data;


    //PWM A/B, PWA/S memory IF
    mem_if_t pwm_a_rd_req;
    mem_if_t pwm_b_rd_req;
    logic [ABR_MEM_MASKED_DATA_WIDTH-1:0] pwm_a_rd_data;
    logic [ABR_MEM_MASKED_DATA_WIDTH-1:0] pwm_b_rd_data;

    //NTT/PWM muxes
    logic ntt_mem_wren, ntt_mem_rden;
    logic [MEM_ADDR_WIDTH-1:0] ntt_mem_wr_addr;
    logic [MEM_ADDR_WIDTH-1:0] ntt_mem_rd_addr;
    logic [MEM_DATA_WIDTH-1:0] ntt_mem_wr_data;
    logic [MEM_DATA_WIDTH-1:0] ntt_mem_rd_data;

    logic pwm_mem_a_rden, pwm_mem_b_rden;

    //Modes
    logic ct_mode;
    logic gs_mode;
    logic pwo_mode;
    logic pwm_mode, pwa_mode, pws_mode;

    assign ct_mode = (mode == ct);
    assign gs_mode = (mode == gs);
    assign pwo_mode = (mode inside {pwm, pwa, pws});
    assign pwm_mode = (mode == pwm);
    assign pwa_mode = (mode == pwa);
    assign pws_mode = (mode == pws);

    //NTT mem
    assign ntt_mem_wren = (mem_wr_req.rd_wr_en == RW_WRITE);
    assign ntt_mem_rden = (mem_rd_req.rd_wr_en == RW_READ);
    
    //PWM mem
    assign pwm_mem_a_rden = (pwm_a_rd_req.rd_wr_en == RW_READ);
    assign pwm_mem_b_rden = (pwm_b_rd_req.rd_wr_en == RW_READ);

    ntt_ram_tdp_file #(
        .ADDR_WIDTH(MEM_ADDR_WIDTH),
        .DATA_WIDTH(ABR_MEM_MASKED_DATA_WIDTH)
    ) ntt_mem (
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .ena(ntt_mem_wren),
        .wea(ntt_mem_wren),
        .addra(mem_wr_req.addr),
        .dina(mem_wr_data),
        .douta(), //Need only one read port, so this can be 0
        .enb(ntt_mem_rden),
        .web(1'b0), //Need only one write port so this can be 0
        .addrb(mem_rd_req.addr),
        .dinb(),
        .doutb(mem_rd_data_int),
        .load_tb_values(load_tb_values),
        .load_random_values(load_random_values),
        .mlkem(mlkem)
    );

    ntt_ram_tdp_file #(
        .ADDR_WIDTH(MEM_ADDR_WIDTH),
        .DATA_WIDTH(ABR_MEM_MASKED_DATA_WIDTH)
    ) pwm_mem_a (
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .ena(),
        .wea(),
        .addra(),
        .dina(),
        .douta(), //Need only one read port, so this can be 0
        .enb(pwm_mem_a_rden), //(pw_rden_d1),
        .web(1'b0), //Need only one write port so this can be 0
        .addrb(pwm_a_rd_req.addr), //(pwm_rd_addr_a_reg),
        .dinb(),
        .doutb(pwm_a_rd_data),
        .load_tb_values(1'b0),
        .load_random_values(load_pwm_a_values),
        .mlkem(mlkem)
    );

    ntt_ram_tdp_file #(
        .ADDR_WIDTH(MEM_ADDR_WIDTH),
        .DATA_WIDTH(ABR_MEM_MASKED_DATA_WIDTH)
    ) pwm_mem_b (
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .ena(),
        .wea(),
        .addra(),
        .dina(),
        .douta(), //Need only one read port, so this can be 0
        .enb(pwm_mem_b_rden), //(pw_rden_d1),
        .web(1'b0), //Need only one write port so this can be 0
        .addrb(pwm_b_rd_req.addr), //(pwm_rd_addr_b_reg),
        .dinb(),
        .doutb(pwm_b_rd_data),
        .load_tb_values(1'b0),
        .load_random_values(load_pwm_b_values),
        .mlkem(mlkem)
    );

    always_comb begin
        mem_rd_data = (mlkem & (mode == gs) & ntt_top_inst0.ntt_ctrl_inst0.masking_en_ctrl) ? {MLDSA_SHARE_WIDTH'(0),
                                                                                               MLDSA_SHARE_WIDTH'(mem_rd_data_int[95:72]),
                                                                                               MLDSA_SHARE_WIDTH'(0),
                                                                                               MLDSA_SHARE_WIDTH'(mem_rd_data_int[71:48]),
                                                                                               MLDSA_SHARE_WIDTH'(0),
                                                                                               MLDSA_SHARE_WIDTH'(mem_rd_data_int[47:24]),
                                                                                               MLDSA_SHARE_WIDTH'(0),
                                                                                               MLDSA_SHARE_WIDTH'(mem_rd_data_int[23:0])}  
                                                                                            : mem_rd_data_int;
    end

    logic ntt_mem_rd_data_valid;
    logic pwm_mem_a_rd_data_valid;
    logic pwm_mem_b_rd_data_valid;

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            ntt_mem_rd_data_valid <= 1'b0;
            pwm_mem_a_rd_data_valid <= 1'b0;
            pwm_mem_b_rd_data_valid <= 1'b0;
        end
        else begin
            ntt_mem_rd_data_valid <= ntt_mem_rden;
            pwm_mem_a_rd_data_valid <= pwm_mem_a_rden;
            pwm_mem_b_rd_data_valid <= pwm_mem_b_rden;
        end
    end

    ntt_top #(
        .REG_SIZE(REG_SIZE),
        .MLDSA_Q(MLDSA_Q),
        .MLDSA_N(MLDSA_N),
        .MEM_ADDR_WIDTH(MEM_ADDR_WIDTH)
    )
    ntt_top_inst0 (
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .mode(mode),
        .ntt_enable(ntt_enable),
        .mlkem(mlkem),
        .ntt_mem_base_addr(ntt_mem_base_addr),
        .pwo_mem_base_addr(pwo_mem_base_addr),
        .accumulate(accumulate),
        .sampler_valid(sampler_valid),
        .shuffle_en(shuffle_en),
        .masking_en(masking_en),
        .random(random),
        .rnd_i(rnd_i),
        //NTT mem IF
        .mem_wr_req(mem_wr_req),
        .mem_rd_req(mem_rd_req),
        .mem_wr_data(mem_wr_data),
        .mem_rd_data_valid(ntt_mem_rd_data_valid),
        .mem_rd_data(mem_rd_data),
        //PWM mem IF
        .pwm_a_rd_req(pwm_a_rd_req),
        .pwm_b_rd_req(pwm_b_rd_req),
        .pwm_a_rd_data_valid(pwm_mem_a_rd_data_valid),
        .pwm_b_rd_data_valid(pwm_mem_b_rd_data_valid),
        .pwm_a_rd_data(pwm_a_rd_data),
        .pwm_b_rd_data(sampler_mode ? sampler_data : pwm_b_rd_data),
        .ntt_busy(ntt_busy),
        .ntt_done(ntt_done)
    );
endmodule