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
// ntt_wrapper_fpga.sv
//======================================================================

module ntt_wrapper_fpga
    import ntt_defines_pkg::*;
    import abr_params_pkg::*;
    #(
        //TODO: clean up
        parameter REG_SIZE = 24,
        parameter RADIX = 23,
        parameter MLDSA_Q = 23'd8380417,
        parameter MLDSA_N = 256,
        parameter MEM_ADDR_WIDTH = 14,
        parameter MEM_DATA_WIDTH = 96,
        parameter MASKED_MEM_DATA_WIDTH = 384, // Memory data width for masking
        parameter AHB_ADDR_WIDTH = 14,
        parameter AHB_DATA_WIDTH = 64 // AHB data width
    )
    (
        input wire hclk,
        input wire hreset_n,
        input wire [AHB_ADDR_WIDTH-1:0] haddr_i,
        input wire [AHB_DATA_WIDTH-1:0] hwdata_i,
        input wire hsel_i,
        input wire hwrite_i,
        input wire hready_i,
        input wire [1:0] htrans_i,
        input wire [2:0] hsize_i,

        output logic hresp_o,
        output logic hreadyout_o,
        output logic [AHB_DATA_WIDTH-1:0] hrdata_o,

        input wire [5:0] random,
        input wire [4:0][MASKED_WIDTH-1:0] rnd_i
    );

    logic dv, hld, err, write;
    logic [AHB_DATA_WIDTH-1:0] wdata;
    logic [AHB_ADDR_WIDTH-1:0] addr;
    logic [AHB_DATA_WIDTH-1:0] rdata;

    logic ahb_ena, ahb_wea;
    logic [AHB_ADDR_WIDTH-1:0] ahb_addr;
    logic [AHB_DATA_WIDTH-1:0] ahb_wdata;
    logic [AHB_DATA_WIDTH-1:0] ahb_rdata;


    logic ntt_enb, ntt_web;
    logic [AHB_ADDR_WIDTH-4:0] ntt_addr;
    logic [MASKED_MEM_DATA_WIDTH-1:0] ntt_data_in;
    logic [MASKED_MEM_DATA_WIDTH-1:0] ntt_data_out;

    logic [AHB_DATA_WIDTH-1:0] ctrl_data;
    logic [AHB_DATA_WIDTH-1:0] enable_data;
    logic [AHB_DATA_WIDTH-1:0] base_addr_data;

    logic ntt_enable, ntt_accumulate, ntt_sampler_valid, ntt_masking_en, ntt_shuffling_en;
    mode_t ntt_mode;

    //NTT signals
    mem_if_t ntt_mem_wr_req, ntt_mem_rd_req, pwm_a_rd_req, pwm_b_rd_req, gen_mem_rd_req, gen_mem_wr_req;
    logic ntt_done;
    logic [ABR_MEM_MASKED_DATA_WIDTH-1:0] ntt_mem_wr_data, ntt_mem_rd_data, sampler_data;
    logic masking_en_ctrl;

    //AHB slv interface
    abr_ahb_slv_sif #(
        .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
        .CLIENT_DATA_WIDTH(AHB_DATA_WIDTH),
        .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
        .CLIENT_ADDR_WIDTH(AHB_ADDR_WIDTH)
    ) ntt_ahb_sif (
        .hclk(hclk),
        .hreset_n(hreset_n),
        .haddr_i(haddr_i),
        .hwdata_i(hwdata_i),
        .hsel_i(hsel_i),
        .hwrite_i(hwrite_i),
        .hready_i(hready_i),
        .htrans_i(htrans_i),
        .hsize_i(hsize_i),
        .hresp_o(hresp_o),
        .hreadyout_o(hreadyout_o),
        .hrdata_o(hrdata_o),
        .dv(dv),
        .hld(hld),
        .err(err),
        .write(write),
        .wdata(wdata),
        .addr(addr),
        .rdata(rdata)
    );

    //AHB to NTT memory adapter
    ntt_ahb_mem_adapter #(
        .MEM_ADDR_WIDTH(AHB_ADDR_WIDTH),
        .MEM_DATA_WIDTH(MEM_DATA_WIDTH),
        .MASKED_MEM_DATA_WIDTH(MASKED_MEM_DATA_WIDTH)
    ) ntt_ahb_mem_adptr_inst (
        .clk(hclk),
        .rst(hreset_n),
        .dv(dv),
        .write(write),
        .wdata(wdata),
        .addr(addr),
        .rdata(rdata),
        .hold(hld),
        .err(err),
        .mem_ctrl_data_i(ctrl_data),
        .mem_enable_data_i(enable_data),
        .ntt_en_o(ntt_enable),
        .ntt_mode_o(ntt_mode),
        .ntt_accumulate_o(ntt_accumulate),
        .ntt_sampler_valid_o(ntt_sampler_valid),
        .ntt_masking_en_o(ntt_masking_en),
        .ntt_shuffle_en_o(ntt_shuffling_en),
        .ahb_ena(ahb_ena),
        .ahb_wea(ahb_wea),
        .ahb_addr(ahb_addr),
        .ahb_wdata(ahb_wdata),
        .ahb_rdata(ahb_rdata)
    );

    //NTT special mem inst
    //TODO: confirm: reuse same mem for NTT and PWM modes?
    always_comb begin
        gen_mem_rd_req = (ntt_mode inside {ct, gs}) ? ntt_mem_rd_req : pwm_a_rd_req;
        gen_mem_wr_req = ntt_mem_wr_req;
    end

    //Used by NTT in ct, gs. Also is pwm A mem and pwm wr back mem
    ntt_special_mem #(
        .ADDR_WIDTH(AHB_ADDR_WIDTH),
        .AHB_DATA_WIDTH(AHB_DATA_WIDTH)
    ) special_mem_inst (
        .clk(hclk),
        .reset_n(hreset_n),
        .zeroize(),
        .ahb_ena(ahb_ena),
        .ahb_wea(ahb_wea),
        .ahb_addr(ahb_addr),
        .ahb_data_in(ahb_wdata),
        .ahb_data_out(ahb_rdata),
        .ntt_enb(gen_mem_rd_req.rd_wr_en == RW_READ ? 1'b1 : 1'b0),
        .ntt_web(ntt_mem_wr_req.rd_wr_en == RW_WRITE ? 1'b1 : 1'b0),
        .ntt_rd_addr(11'(gen_mem_rd_req.addr)),
        .ntt_wr_addr(11'(ntt_mem_wr_req.addr)),
        .ntt_data_in(ntt_mem_wr_data),
        .ntt_data_out(ntt_mem_rd_data),
        .ntt_done(ntt_done),
        .ctrl_data(ctrl_data),
        .enable_data(enable_data),
        .base_addr_data(base_addr_data),
        .masking_en_ctrl(masking_en_ctrl),
        .sampler_data(sampler_data)
    );

    logic ct_mode, gs_mode;

    always_comb begin
        ct_mode = (ntt_mode == ct);
        gs_mode = (ntt_mode == gs);
    end

    ntt_top #(
        .MEM_ADDR_WIDTH(AHB_ADDR_WIDTH)
    ) ntt_top_inst0 (
        .clk(hclk),
        .reset_n(hreset_n),
        .zeroize(),
        .mode(ntt_mode),
        .ntt_enable(ntt_enable),
        .mlkem(1'b0),
        .ntt_mem_base_addr(base_addr_data), //(ct_mode ? {14'h0, 14'h40, 14'h80} : {14'h80, 14'h40, 14'h80}), // Base address for NTT memory
        .pwo_mem_base_addr(base_addr_data), //({14'h0, 14'h40, 14'h80}), // Base address for PWO memory
        .accumulate(ntt_accumulate),
        .sampler_valid(ntt_sampler_valid),
        .shuffle_en(ntt_shuffling_en),
        .masking_en(ntt_masking_en),
        .random(random),
        .rnd_i(rnd_i),
        .mem_wr_req(ntt_mem_wr_req),
        .mem_rd_req(ntt_mem_rd_req),
        .mem_wr_data(ntt_mem_wr_data),
        .mem_rd_data(ntt_mem_rd_data), //ct, gs, or acc input for pwm
        .pwm_a_rd_req(pwm_a_rd_req), //TODO: separate mem or same?
        .pwm_b_rd_req(pwm_b_rd_req),
        .pwm_a_rd_data(ntt_mem_rd_data),
        .pwm_b_rd_data(sampler_data),
        .ntt_done(ntt_done),
        .ntt_busy(),
        .masking_en_ctrl(masking_en_ctrl)
    );
endmodule