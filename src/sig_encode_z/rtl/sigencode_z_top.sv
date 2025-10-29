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
// sigencode_z_top.sv
// --------
// @brief Top-level module for the signature encoder in the Mldsa scheme.
// 
// This module implements the top-level logic for encoding z polynomial (a part of signature) in the
// Mldsa post-quantum cryptographic scheme. The encoder reads coefficients from memory,
// processes them through encoding units, and writes the encoded values to a specified
// register map.
// The module interfaces with memory through two parallel read ports and writes the
// encoded data to a destination address in the register map.
// 
//======================================================================

module sigencode_z_top
    import abr_params_pkg::*;
    import sigencode_z_defines_pkg::*;
    #(
        parameter MEM_ADDR_WIDTH = ABR_MEM_ADDR_WIDTH,
        parameter REG_SIZE = 24,
        parameter GAMMA1 = 19
    )
    (
        input wire clk,
        input wire reset_n,
        input wire zeroize,

        // Input memory ports
        input wire [MEM_ADDR_WIDTH-1:0] src_base_addr,
        output mem_if_t mem_a_rd_req,
        output mem_if_t mem_b_rd_req,
        input wire [3:0][REG_SIZE-1:0] mem_a_rd_data,
        input wire [3:0][REG_SIZE-1:0] mem_b_rd_data,
        input logic mem_rd_data_valid,

        // Output API ports
        input wire [MEM_ADDR_WIDTH-1:0] sigmem_dest_base_addr,
        output sig_mem_if_t sigmem_a_wr_req,
        output sig_mem_if_t sigmem_b_wr_req,
        output logic [3:0][GAMMA1:0]  sigmem_a_wr_data,
        output logic [3:0][GAMMA1:0]  sigmem_b_wr_data,

        //Control and status signals        
        input wire sigencode_z_enable,
        output logic sigencode_z_done
    );

    localparam THE_LAST_ADDR = ((MLDSA_N)/4)-1;
    // State Machine States
    localparam  SIGENCODE_IDLE                = 2'b00,
                SIGENCODE_READ                = 2'b01,
                SIGENCODE_WRITE               = 2'b10,
                SIGENCODE_DONE                = 2'b11;


    logic [31:0] num_mem_operands, num_api_operands;   // encoded each four coeff will increment these by one
    logic [MEM_ADDR_WIDTH-1:0] locked_dest_addr, locked_src_addr; // this ensures that addresses are captured when the block is enabled
    logic [1:0] state, next_state;


    // State Machine
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            state <= SIGENCODE_IDLE;
        end
        else if (zeroize) begin
            state <= SIGENCODE_IDLE;
        end
        else begin
            state <= next_state;
        end
    end

    always_comb begin
        next_state = state;
        unique case (state) inside
            SIGENCODE_IDLE: begin
                if (sigencode_z_enable)
                    next_state = SIGENCODE_READ;
                else
                    next_state = SIGENCODE_IDLE;
            end
            SIGENCODE_READ: begin
                if (num_mem_operands == THE_LAST_ADDR-1) begin
                    next_state = SIGENCODE_WRITE;
                end
            end
            SIGENCODE_WRITE: begin
                if (~mem_rd_data_valid) begin
                    next_state = SIGENCODE_DONE;
                end
            end
            SIGENCODE_DONE: begin
                next_state = SIGENCODE_IDLE;
            end
            default: begin
                next_state = SIGENCODE_IDLE;
            end
        endcase
    end

    // Lock the src and dest addresses and initialize the counter
    // Assert the done signal when it is needed
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            num_mem_operands    <= '0;
            num_api_operands    <= '0;
            locked_dest_addr    <= '0;
            locked_src_addr     <= '0;
            sigencode_z_done    <= '0;
        end
        else if (zeroize) begin
            num_mem_operands    <= '0;
            num_api_operands    <= '0;
            locked_dest_addr    <= '0;
            locked_src_addr     <= '0;
            sigencode_z_done    <= '0;
        end
        else begin
            if (sigencode_z_enable) begin
                locked_dest_addr    <= sigmem_dest_base_addr;
                locked_src_addr     <= src_base_addr;
            end

            
            if (state == SIGENCODE_READ) begin
                num_mem_operands    <= num_mem_operands +2'h2;
            end
            else begin
                num_mem_operands    <= '0;
            end
            if (mem_rd_data_valid) begin
                num_api_operands    <= num_api_operands +2'h2;
            end
            else begin
                num_api_operands    <= '0;
            end
            if (state == SIGENCODE_DONE) begin
                sigencode_z_done      <= 1'b1;
            end
            else begin
                sigencode_z_done      <= 1'b0;
            end
        end
    end

    // Write request generation
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            sigmem_a_wr_req <= '{rd_wr_en: RW_IDLE, addr: '0};
            sigmem_b_wr_req <= '{rd_wr_en: RW_IDLE, addr: '0};
        end
        else if (zeroize) begin
            sigmem_a_wr_req <= '{rd_wr_en: RW_IDLE, addr: '0};
            sigmem_b_wr_req <= '{rd_wr_en: RW_IDLE, addr: '0};
        end
        else if (mem_rd_data_valid) begin
            sigmem_a_wr_req <= '{rd_wr_en: RW_WRITE, addr: locked_dest_addr + num_api_operands};
            sigmem_b_wr_req <= '{rd_wr_en: RW_WRITE, addr: locked_dest_addr + num_api_operands + 1};
        end
        else begin
            sigmem_a_wr_req <= '{rd_wr_en: RW_IDLE, addr: '0};
            sigmem_b_wr_req <= '{rd_wr_en: RW_IDLE, addr: '0};
        end
    end

    // Memory read request generation
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            mem_a_rd_req <= '{rd_wr_en: RW_IDLE, addr: '0};
            mem_b_rd_req <= '{rd_wr_en: RW_IDLE, addr: '0};
        end
        else if (zeroize) begin
            mem_a_rd_req <= '{rd_wr_en: RW_IDLE, addr: '0};
            mem_b_rd_req <= '{rd_wr_en: RW_IDLE, addr: '0};
        end
        else if (state == SIGENCODE_READ) begin
            mem_a_rd_req <= '{rd_wr_en: RW_READ, addr: locked_src_addr + num_mem_operands};
            mem_b_rd_req <= '{rd_wr_en: RW_READ, addr: locked_src_addr + num_mem_operands + 1};
        end else begin
            mem_a_rd_req <= '{rd_wr_en: RW_IDLE, addr: '0};
            mem_b_rd_req <= '{rd_wr_en: RW_IDLE, addr: '0};
        end
    end

    //8 encoding instances
    generate
        for (genvar i = 0; i < 4; i++) begin : enc_unit
            sigencode_z_unit #(
                .REG_SIZE(REG_SIZE),
                .GAMMA1(GAMMA1)
            )
            upper_encode (
                .clk(clk),
                .reset_n(reset_n),
                .zeroize(zeroize),
                .data_i(mem_a_rd_data[i]),
                .data_o(sigmem_a_wr_data[i])
            );
            sigencode_z_unit #(
                .REG_SIZE(REG_SIZE),
                .GAMMA1(GAMMA1)
            )
            lower_encode (
                .clk(clk),
                .reset_n(reset_n),
                .zeroize(zeroize),
                .data_i(mem_b_rd_data[i]),
                .data_o(sigmem_b_wr_data[i])
            );
        end : enc_unit
    endgenerate



endmodule