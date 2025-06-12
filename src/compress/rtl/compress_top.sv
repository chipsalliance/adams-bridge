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
        output mem_if_t mem_wr_req,
        input wire [COEFF_PER_CLK-1:0][REG_SIZE-1:0] mem_rd_data,
        output logic [COEFF_PER_CLK-1:0][REG_SIZE-1:0] mem_wr_data,

        output logic compress_done
    );

    logic [COEFF_PER_CLK-1:0][MLKEM_Q_WIDTH-1:0] compress_data_int, compress_data;
    logic /*[1:0]*/ ready;
    logic enable;

    compress_ctrl cmp_ctrl_inst (
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .cmp_enable(compress_enable),
        .src_base_addr(src_base_addr),
        .dest_base_addr(dest_base_addr),
        .ready(ready),
        .mem_rd_req(mem_rd_req),
        .mem_wr_req(mem_wr_req),
        .done(compress_done)
    );

    generate
        for (genvar i = 0; i < COEFF_PER_CLK; i++) begin
            compress cmp_inst (
                .op_i(mem_rd_data[i][MLKEM_Q_WIDTH-1:0]),
                .mode(mode),
                .op_o(compress_data_int[i])
            );
        end
    endgenerate

    //Flop compress data combo output, generate ready
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            compress_data <= '0;
            enable <= '0;
            ready <= '0;
        end
        else if (zeroize) begin
            compress_data <= '0;
            enable <= '0;
            ready <= '0;
        end
        else begin
            compress_data <= compress_data_int;
            enable <= compress_enable ? 'b1 : compress_done ? '0 : enable;
            ready <= enable; //{enable, ready[1]};
        end
    end

    always_comb begin
        for (int i = 0; i < COEFF_PER_CLK; i++) begin
            mem_wr_data[i] = REG_SIZE'(compress_data[i]);
        end
    end
endmodule