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
// sigdecode_z_top.sv
// --------
// @brief Top-level module for the signature decoder for z in the Mldsa scheme.
// 
// This module implements the top-level logic for encoding z polynomial (a part of signature) in the
// Mldsa post-quantum cryptographic scheme. The decoder reads encoded byte string from API register,
// processes them through decoding units, and writes the decoded values to a specified
// memory locations starting from the dest address.
// The module interfaces with memory through two parallel read ports and writes the
// decoded data to a destination address in the memory.
// 
//======================================================================

module sigdecode_z_top
    import abr_params_pkg::*;
    import sigdecode_z_defines_pkg::*;
    #(
        parameter MEM_ADDR_WIDTH = ABR_MEM_ADDR_WIDTH,
        parameter REG_SIZE = 24,
        parameter GAMMA1 = 19
    )
    (
        input logic clk,
        input logic reset_n,
        input logic zeroize,

        //Active ML-DSA parameter set. Both are public.
        input logic gamma1_17_i,
        input logic [3:0] mldsa_l_i,

        // Output memory ports
        input logic [MEM_ADDR_WIDTH-1:0] dest_base_addr,
        output mem_if_t mem_a_wr_req,
        output mem_if_t mem_b_wr_req,
        output logic [3:0][REG_SIZE-1:0] mem_a_wr_data,
        output logic [3:0][REG_SIZE-1:0] mem_b_wr_data,

        // Input API ports
        output sig_mem_if_t sigmem_rd_req,
        input logic [1:0][3:0][GAMMA1:0]  sigmem_rd_data,
        input logic sigmem_rd_data_valid,

        //Control and status signals        
        input logic sigdecode_z_enable,
        output logic sigdecode_z_done
    );

    localparam COEFF_ADDR_PER_POLY = MLDSA_N/4;
    // State Machine States
    localparam  SIGDECODE_IDLE  = 2'b00,
                SIGDECODE_READ  = 2'b01,
                SIGDECODE_WRITE = 2'b10,
                SIGDECODE_DONE  = 2'b11;


    logic [31:0] num_mem_operands, num_api_operands;   // encoded each four coeff will increment these by one
    logic [MEM_ADDR_WIDTH-1:0] locked_dest_addr; // this ensures that addresses are captured when the block is enabled
    logic [1:0] state, next_state;
    logic [31:0] the_last_addr;
    logic gamma1_17_gated;

    //Constant folds to 0 when ML-DSA-44 is not built in.
    always_comb gamma1_17_gated = ABR_NEED_GAMMA1_17 & gamma1_17_i;

    //Only the active l polynomials of z are decoded; the remaining cat-5 sized
    //slots are left untouched. l is public, so this bound is not secret dependent.
    always_comb the_last_addr = (32'(mldsa_l_i) * COEFF_ADDR_PER_POLY) - 32'd1;


    // State Machine
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            state <= SIGDECODE_IDLE;
        end
        else if (zeroize) begin
            state <= SIGDECODE_IDLE;
        end
        else begin
            state <= next_state;
        end
    end

    always_comb begin
        next_state = state;
        unique case (state) inside
            SIGDECODE_IDLE: begin
                if (sigdecode_z_enable)
                    next_state = SIGDECODE_READ;
                else
                    next_state = SIGDECODE_IDLE;
            end
            SIGDECODE_READ: begin
                if (num_api_operands == the_last_addr-1) begin
                    next_state = SIGDECODE_WRITE;
                end
            end
            //Done reading, only writes remaining
            SIGDECODE_WRITE: begin
                if (~sigmem_rd_data_valid) begin
                    next_state = SIGDECODE_DONE;
                end
            end
            SIGDECODE_DONE: begin
                next_state = SIGDECODE_IDLE;
            end
            default: begin
                next_state = SIGDECODE_IDLE;
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
            sigdecode_z_done    <= '0;
        end
        else if (zeroize) begin
            num_mem_operands    <= '0;
            num_api_operands    <= '0;
            locked_dest_addr    <= '0;
            sigdecode_z_done    <= '0;
        end
        else begin
            if (sigdecode_z_enable) begin
                locked_dest_addr    <= dest_base_addr;
            end

            
            if (state == SIGDECODE_READ) begin
                num_api_operands    <= num_api_operands + 2'h2;
            end
            else begin
                num_api_operands    <= 'h0;
            end
            if (sigmem_rd_data_valid) begin
                num_mem_operands    <= num_mem_operands + 2'h2;
            end
            else begin
                num_mem_operands    <= 'h0;
            end
            if (state == SIGDECODE_DONE) begin
                sigdecode_z_done      <= 1'b1;
            end
            else begin
                sigdecode_z_done      <= 1'b0;
            end
        end
    end

    // Write request generation
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            mem_a_wr_req <= '{rd_wr_en: RW_IDLE, addr: '0};
            mem_b_wr_req <= '{rd_wr_en: RW_IDLE, addr: '0};
        end
        else if (zeroize) begin
            mem_a_wr_req <= '{rd_wr_en: RW_IDLE, addr: '0};
            mem_b_wr_req <= '{rd_wr_en: RW_IDLE, addr: '0};
        end
        else if (sigmem_rd_data_valid) begin
            mem_a_wr_req <= '{rd_wr_en: RW_WRITE, addr: locked_dest_addr + num_mem_operands};
            mem_b_wr_req <= '{rd_wr_en: RW_WRITE, addr: locked_dest_addr + num_mem_operands + 1};
        end
        else begin
            mem_a_wr_req <= '{rd_wr_en: RW_IDLE, addr: '0};
            mem_b_wr_req <= '{rd_wr_en: RW_IDLE, addr: '0};
        end
    end

    // Memory read request generation
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            sigmem_rd_req <= '{rd_wr_en: RW_IDLE, addr: '0};
        end
        else if (zeroize) begin
            sigmem_rd_req <= '{rd_wr_en: RW_IDLE, addr: '0};
        end
        else if (state == SIGDECODE_READ) begin
            sigmem_rd_req <= '{rd_wr_en: RW_READ, addr: num_api_operands};
        end else begin
            sigmem_rd_req <= '{rd_wr_en: RW_IDLE, addr: '0};
        end
    end

    //8 decoding instances
    generate
        for (genvar i = 0; i < 4; i++) begin : dec_unit
            sigdecode_z_unit #(
                .REG_SIZE(REG_SIZE),
                .GAMMA1(GAMMA1)
            )
            upper_encode (
                .clk(clk),
                .reset_n(reset_n),
                .zeroize(zeroize),
                .gamma1_17_i(gamma1_17_gated),
                .data_i(sigmem_rd_data[0][i]),
                .data_o(mem_a_wr_data[i])
            );
            sigdecode_z_unit #(
                .REG_SIZE(REG_SIZE),
                .GAMMA1(GAMMA1)
            )
            lower_encode (
                .clk(clk),
                .reset_n(reset_n),
                .zeroize(zeroize),
                .gamma1_17_i(gamma1_17_gated),
                .data_i(sigmem_rd_data[1][i]),
                .data_o(mem_b_wr_data[i])
            );
        end : dec_unit
    endgenerate



endmodule
