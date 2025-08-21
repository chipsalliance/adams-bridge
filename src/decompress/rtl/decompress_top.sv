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
//======================================================================
//
// decompress_top.sv
// --------
// This module processes 4 coeffs/clk and is fully pipelined. 
// Each command trigger will compute decompression over 4 polynomials and produces a done signal at the end of the last polynomial.

module decompress_top
    import abr_params_pkg::*;
    import decompress_defines_pkg::*;
    (
        input logic clk,
        input logic reset_n,
        input logic zeroize,

        input logic decompress_enable,
        input decompress_mode_t mode,
        input logic [2:0] num_poly,
        input logic [ABR_MEM_ADDR_WIDTH-1:0] src_base_addr,
        input logic [ABR_MEM_ADDR_WIDTH-1:0] dest_base_addr,

        output mem_if_t mem_wr_req,
        output logic [COEFF_PER_CLK-1:0][MLDSA_Q_WIDTH-1:0] mem_wr_data, //Match memory width of ABR

        output logic api_rd_en,
        output logic [ABR_MEM_ADDR_WIDTH-1:0] api_rd_addr,
        input  logic [1:0][DATA_WIDTH-1:0] api_rd_data,

        output logic decompress_done
    );

    localparam DECOMP_DATA_W = MLKEM_Q_WIDTH;

    logic api_rd_en_f;
    logic piso_hold_o;
    logic read_done;
    logic [3:0] d; // Decompression count
    logic piso_data_valid;
    logic [(COEFF_PER_CLK*DECOMP_DATA_W)-1:0] piso_data_o;
    logic [COEFF_PER_CLK-1:0][DECOMP_DATA_W-1:0] decompress_data_i;
    logic [COEFF_PER_CLK-1:0][MLKEM_Q_WIDTH-1:0] decompress_data_o;
    logic [ABR_MEM_ADDR_WIDTH-1:0] mem_wr_addr;
    logic write_done;
    logic decompress_busy;

    always_comb decompress_done = decompress_busy & write_done;

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            decompress_busy <= '0;
        end
        else if (zeroize) begin
            decompress_busy <= '0;
        end
        else begin
            decompress_busy <= decompress_enable ? '1 :
                               decompress_done ? '0 : decompress_busy;
        end
    end

    //Multi-rate piso
    abr_piso_multi #(
        .NUM_MODES(4),
        .PISO_BUFFER_W(104),
        .PISO_ACT_INPUT_RATE(64),
        .PISO_ACT_OUTPUT_RATE(48),
        `ifdef VERILATOR
        .INPUT_RATES('{64, 64, 64, 64, 0}),
        .OUTPUT_RATES('{4, 20, 44, 48, 0})
        `else
        .INPUT_RATES('{64, 64, 64, 64}),
        .OUTPUT_RATES('{4, 20, 44, 48})
        `endif
    ) abr_piso_inst (
        .clk(clk),
        .rst_b(reset_n),
        .zeroize(zeroize),
        .mode(mode),
        .valid_i(api_rd_en_f),
        .hold_o(piso_hold_o),
        .data_i(api_rd_data),
        .valid_o(piso_data_valid),
        .hold_i('0),
        .data_o(piso_data_o)
      );

    //Cast the API bitstream into 12 bit vectors per coefficient
    always_comb begin
        for (int i = 0; i < COEFF_PER_CLK; i++) begin
            unique case (mode)
                DECOMPRESS1: begin
                    decompress_data_i[i] = 12'(piso_data_o[i*1 +: 1]);
                end
                DECOMPRESS5: begin
                    decompress_data_i[i] = 12'(piso_data_o[i*5 +: 5]);
                end
                DECOMPRESS11: begin
                    decompress_data_i[i] = 12'(piso_data_o[i*11 +: 11]);
                end
                DECOMPRESS12: begin
                    decompress_data_i[i] = 12'(piso_data_o[i*12 +: 12]);
                end
                default: begin
                    decompress_data_i[i] = 12'(piso_data_o[i*12 +: 12]); // Default case
                end
            endcase
        end
    end

    generate
        for (genvar i = 0; i < COEFF_PER_CLK; i++) begin : gen_decompress_data_o
            decompress decompress_inst (
                .op_i(decompress_data_i[i]),
                .mode(mode),
                .op_o(decompress_data_o[i])
            );

        assign mem_wr_data[i][MLKEM_Q_WIDTH-1:0] = decompress_data_o[i];
        assign mem_wr_data[i][MLDSA_Q_WIDTH-1:MLKEM_Q_WIDTH] = '0; //Zero padding for memory width

        end
    endgenerate

    always_comb api_rd_en = decompress_busy & ~read_done & ~piso_hold_o;

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            api_rd_en_f <= '0;
        end
        else if (zeroize) begin
            api_rd_en_f <= '0;
        end
        else begin
            api_rd_en_f <= api_rd_en | (api_rd_en_f & piso_hold_o);
        end
    end

    //Compute API read address
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            api_rd_addr <= '0;
        end
        else if (zeroize) begin
            api_rd_addr <= '0;
        end
        else if (decompress_enable) begin
            api_rd_addr <= src_base_addr;
        end 
        else if (api_rd_en) begin
            api_rd_addr <= api_rd_addr + 'd1;
        end
    end

    always_comb begin
        unique case (mode)
            DECOMPRESS1: d = 1;
            DECOMPRESS5: d = 5;
            DECOMPRESS11: d = 11;
            DECOMPRESS12: d = 12;
            default: d = 12; // Default case
        endcase
    end

    always_comb read_done = api_rd_addr == (src_base_addr + (num_poly * d * MLKEM_N)/64);

    //Compute Memory Write Requests
    decompress_ctrl decomp_ctrl_inst (
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .decompress_enable(decompress_enable),
        .num_poly(num_poly),
        .dest_base_addr(dest_base_addr),
        .mem_wr_valid(piso_data_valid),
        .mem_wr_addr(mem_wr_addr),
        .done(write_done)
    );

    always_comb mem_wr_req.addr = mem_wr_addr;
    always_comb mem_wr_req.rd_wr_en = piso_data_valid ? RW_WRITE : RW_IDLE;

endmodule
