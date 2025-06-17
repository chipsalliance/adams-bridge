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
// Each command trigger will compute compression over 4 polynomials and produces a done signal at the end of the last polynomial.

module compress_top
    import abr_params_pkg::*;
    import compress_defines_pkg::*;
    (
        input wire clk,
        input wire reset_n,
        input wire zeroize,

        input wire compress_enable,
        input compress_mode_t mode,
        input wire [ABR_MEM_ADDR_WIDTH-1:0] src_base_addr,
        input wire [ABR_MEM_ADDR_WIDTH-1:0] dest_base_addr,

        output mem_if_t mem_rd_req,
        input wire [COEFF_PER_CLK-1:0][REG_SIZE-1:0] mem_rd_data,

        output logic api_wr_en,
        output logic [ABR_MEM_ADDR_WIDTH-1:0] api_wr_addr,
        output logic [DATA_WIDTH-1:0] api_wr_data,

        output logic compress_done
    );

    localparam COMP_DATA_W = COEFF_PER_CLK*MLKEM_Q_WIDTH;

    logic [COEFF_PER_CLK-1:0][MLKEM_Q_WIDTH-1:0] compress_data_i, compress_data_o, compress_data;
    logic [COEFF_PER_CLK-1:0][MLKEM_Q_WIDTH-1:0] mem_rd_data_stalled;
    logic [COEFF_PER_CLK-1:0][MLKEM_Q_WIDTH-1:0] compress_data_valid;
    logic read_done;
    logic mem_rd_data_valid;
    logic mem_rd_data_hold,mem_rd_data_hold_f ;
    logic compress_busy;

    always_comb compress_done = compress_busy & read_done & ~api_wr_en;

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
        .src_base_addr(src_base_addr),
        .mem_rd_req(mem_rd_req),
        .mem_rd_data_valid(mem_rd_data_valid),
        .mem_rd_data_hold(mem_rd_data_hold),
        .done(read_done)
    );

    generate
        for (genvar i = 0; i < COEFF_PER_CLK; i++) begin

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
                compress_data_valid = COMP_DATA_W'({COMP_DATA_W{mem_rd_data_valid | mem_rd_data_hold_f}} >> 44);
            end
            compress5: begin
                compress_data = {28'b0, compress_data_o[3][4:0], compress_data_o[2][4:0], compress_data_o[1][4:0],compress_data_o[0][4:0]};
                compress_data_valid = COMP_DATA_W'({COMP_DATA_W{mem_rd_data_valid | mem_rd_data_hold_f}} >> 28);
            end
            compress11: begin
                compress_data = {4'b0, compress_data_o[3][10:0], compress_data_o[2][10:0], compress_data_o[1][10:0],compress_data_o[0][10:0]};
                compress_data_valid = COMP_DATA_W'({COMP_DATA_W{mem_rd_data_valid | mem_rd_data_hold_f}} >> 4);
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
        .BUFFER_DATA_W(1),
        .NUM_WR(48),
        .NUM_RD(32)
    ) compress_sample_buffer_inst (
        .clk(clk),
        .rst_b(reset_n),
        .zeroize(zeroize),
        .data_i(compress_data),
        .data_valid_i(compress_data_valid),
        .buffer_full_o(mem_rd_data_hold),
        .data_valid_o(api_wr_en),
        .data_o(api_wr_data)
    );

    //Compute API write address
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            api_wr_addr <= '0;
        end
        else if (zeroize) begin
            api_wr_addr <= '0;
        end
        else if (compress_enable) begin
            api_wr_addr <= dest_base_addr;
        end 
        else if (api_wr_en) begin
            api_wr_addr <= api_wr_addr + 'd1;
        end
    end

endmodule