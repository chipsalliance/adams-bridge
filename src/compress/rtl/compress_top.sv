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
// compress_top.sv
// --------
// This module processes 4 coeffs/clk and is fully pipelined. 
// Each command trigger will compute compression over num_polynomials and produces a done signal at the end of the last polynomial.
// Compare mode is used to compare encaps resulting ciphertext with the ciphertext from decaps step
// Instead of writing to the API memory, reads are made and the data is compared against the compressed data

module compress_top
    import abr_params_pkg::*;
    import compress_defines_pkg::*;
    (
        input wire clk,
        input wire reset_n,
        input wire zeroize,

        input wire compress_enable,
        input compress_mode_t mode,
        input logic compare_mode,
        input wire [2:0] num_poly,
        input wire [ABR_MEM_ADDR_WIDTH-1:0] src_base_addr,
        input wire [ABR_MEM_ADDR_WIDTH-1:0] dest_base_addr,

        output mem_if_t mem_rd_req,
        input wire [COEFF_PER_CLK-1:0][REG_SIZE-1:0] mem_rd_data,

        output logic [1:0] api_rw_en,
        output logic [ABR_MEM_ADDR_WIDTH-1:0] api_rw_addr,
        output logic [DATA_WIDTH-1:0] api_wr_data,
        input  logic [DATA_WIDTH-1:0] api_rd_data,
        output logic compare_failed,
        output logic compress_done
    );

    localparam COMP_DATA_W = MLKEM_Q_WIDTH;

    logic [COEFF_PER_CLK-1:0][MLKEM_Q_WIDTH-1:0] compress_data_i, compress_data_o, compress_data;
    logic [COEFF_PER_CLK-1:0][MLKEM_Q_WIDTH-1:0] mem_rd_data_stalled;
    logic [COMP_DATA_W-1:0] compress_data_valid;
    logic read_done;
    logic mem_rd_data_valid;
    logic mem_rd_data_hold,mem_rd_data_hold_f ;
    logic buffer_valid, buffer_valid_f;
    logic [DATA_WIDTH-1:0] buffer_data, buffer_data_f;
    logic compress_busy;

    always_comb compress_done = compress_busy & read_done & ~(mem_rd_data_valid | (|api_rw_en) | buffer_valid | buffer_valid_f);

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            compress_busy <= '0;
            mem_rd_data_hold_f <= '0;
        end
        else if (zeroize) begin
            compress_busy <= '0;
            mem_rd_data_hold_f <= '0;
        end
        else begin
            compress_busy <= compress_enable ? '1 :
                             compress_done ? '0 : compress_busy;
            mem_rd_data_hold_f <= mem_rd_data_hold;
        end
    end

    compress_ctrl cmp_ctrl_inst (
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .cmp_enable(compress_enable),
        .num_poly(num_poly),
        .src_base_addr(src_base_addr),
        .mem_rd_req(mem_rd_req),
        .mem_rd_data_valid(mem_rd_data_valid),
        .mem_rd_data_hold(mem_rd_data_hold),
        .done(read_done)
    );

    generate
        for (genvar i = 0; i < COEFF_PER_CLK; i++) begin : gen_mem_rd_data_stalled

            always_ff @(posedge clk or negedge reset_n) begin
                if (!reset_n) begin
                    mem_rd_data_stalled[i] <= '0;
                end
                else if (zeroize) begin
                    mem_rd_data_stalled[i] <= '0;
                end
                else begin
                    mem_rd_data_stalled[i] <= mem_rd_data[i][MLKEM_Q_WIDTH-1:0];
                end
            end

            always_comb compress_data_i[i] = mem_rd_data_hold_f ? mem_rd_data_stalled[i] : mem_rd_data[i][MLKEM_Q_WIDTH-1:0];

            compress cmp_inst (
                .op_i(compress_data_i[i]),
                .mode(mode),
                .op_o(compress_data_o[i])
            );
        end
    endgenerate

    always_comb begin
        unique case (mode)
            compress1: begin
                compress_data = {44'b0, compress_data_o[3][0:0], compress_data_o[2][0:0], compress_data_o[1][0:0],compress_data_o[0][0:0]};
                compress_data_valid = COMP_DATA_W'({COMP_DATA_W{mem_rd_data_valid | mem_rd_data_hold_f}} >> 11);
            end
            compress5: begin
                compress_data = {28'b0, compress_data_o[3][4:0], compress_data_o[2][4:0], compress_data_o[1][4:0],compress_data_o[0][4:0]};
                compress_data_valid = COMP_DATA_W'({COMP_DATA_W{mem_rd_data_valid | mem_rd_data_hold_f}} >> 7);
            end
            compress11: begin
                compress_data = {4'b0, compress_data_o[3][10:0], compress_data_o[2][10:0], compress_data_o[1][10:0],compress_data_o[0][10:0]};
                compress_data_valid = COMP_DATA_W'({COMP_DATA_W{mem_rd_data_valid | mem_rd_data_hold_f}} >> 1);
            end
            compress12: begin
                compress_data = compress_data_o;
                compress_data_valid = {COMP_DATA_W{mem_rd_data_valid | mem_rd_data_hold_f}};
            end
            default: begin
                compress_data = compress_data_o; // Default case
                compress_data_valid = '0;
            end
        endcase
    end

    abr_sample_buffer #(
        .BUFFER_DATA_W(4),
        .NUM_WR(12),
        .NUM_RD(8)
    ) compress_sample_buffer_inst (
        .clk(clk),
        .rst_b(reset_n),
        .zeroize(zeroize),
        .data_i(compress_data),
        .data_valid_i(compress_data_valid),
        .buffer_full_o(mem_rd_data_hold),
        .data_valid_o(buffer_valid),
        .data_o(buffer_data)
    );

    //Compute API write address
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            api_rw_addr <= '0;
        end
        else if (zeroize) begin
            api_rw_addr <= '0;
        end
        else if (compress_enable) begin
            api_rw_addr <= dest_base_addr;
        end 
        else if (|api_rw_en) begin
            api_rw_addr <= api_rw_addr + 'd1;
        end
    end
    //api write interface
    always_comb api_rw_en[0] = buffer_valid & ~compare_mode;
    always_comb api_wr_data = buffer_data;
    //api read interface for compare mode
    always_comb api_rw_en[1] = buffer_valid & compare_mode;
    always_comb compare_failed = compare_mode & buffer_valid_f & (buffer_data_f != api_rd_data);

    always_ff@(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            buffer_valid_f <= '0;
            buffer_data_f <= '0;
        end
        else if (zeroize) begin
            buffer_valid_f <= '0;
            buffer_data_f <= '0;
        end
        else begin
            buffer_valid_f <= buffer_valid;
            buffer_data_f <= buffer_valid ? buffer_data : buffer_data_f;
        end
    end

endmodule
