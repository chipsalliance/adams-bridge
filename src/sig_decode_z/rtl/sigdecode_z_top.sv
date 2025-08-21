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
        input wire clk,
        input wire reset_n,
        input wire zeroize,

        // Output memory ports
        input wire [MEM_ADDR_WIDTH-1:0] dest_base_addr,
        output mem_if_t mem_a_wr_req,
        output mem_if_t mem_b_wr_req,
        output logic [3:0][REG_SIZE-1:0] mem_a_wr_data,
        output logic [3:0][REG_SIZE-1:0] mem_b_wr_data,

        // Input API ports
        output sig_mem_if_t sigmem_a_rd_req,
        output sig_mem_if_t sigmem_b_rd_req,
        input wire [3:0][GAMMA1:0]  sigmem_a_rd_data,
        input wire [3:0][GAMMA1:0]  sigmem_b_rd_data,

        //Control and status signals        
        input wire sigdecode_z_enable,
        output logic sigdecode_z_done
    );

    localparam THE_LAST_ADDR = ((MLDSA_L * MLDSA_N)/4)-1;
    // State Machine States
    localparam  IDLE                = 3'b000,
                READ                = 3'b001,
                READ_and_EXEC       = 3'b010,
                READ_EXEC_and_WRITE = 3'b011,
                EXEC_and_WRITE      = 3'b100,
                WRITE               = 3'b101,
                DONE                = 3'b110;


    logic [31:0] num_mem_operands, num_api_operands;   // encoded each four coeff will increment these by one
    logic [MEM_ADDR_WIDTH-1:0] locked_dest_addr; // this ensures that addresses are captured when the block is enabled
    logic [2:0] state, next_state;


    // State Machine
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            state <= IDLE;
        end
        else if (zeroize) begin
            state <= IDLE;
        end
        else begin
            state <= next_state;
        end
    end

    always_comb begin
        case (state)
            IDLE: begin
                if (sigdecode_z_enable)
                    next_state = READ;
                else
                    next_state = IDLE;
            end
            READ: begin
                next_state = READ_and_EXEC;
            end
            READ_and_EXEC: begin
                next_state = READ_EXEC_and_WRITE;
            end
            READ_EXEC_and_WRITE: begin
                if ((num_api_operands+1) == THE_LAST_ADDR) begin
                    next_state = EXEC_and_WRITE;
                end
                else begin
                    next_state = READ_EXEC_and_WRITE;
                end
            end
            EXEC_and_WRITE: begin
                next_state = WRITE;
            end
            WRITE: begin
                next_state = DONE;
            end
            DONE: begin
                next_state = IDLE;
            end
            default: begin
                next_state = IDLE;
            end
        endcase
    end

    // Lock the src and dest addresses and initialize the counter
    // Assert the done signal when it is needed
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            num_mem_operands    <= 'h0;
            num_api_operands    <= 'h0;
            locked_dest_addr    <= 'h0;
            sigdecode_z_done    <= 'h0;
        end
        else if (zeroize) begin
            num_mem_operands    <= 'h0;
            num_api_operands    <= 'h0;
            locked_dest_addr    <= 'h0;
            sigdecode_z_done    <= 'h0;
        end
        else begin
            if (sigdecode_z_enable) begin
                locked_dest_addr    <= dest_base_addr;
            end

            
            if (state == READ || state == READ_and_EXEC || state == READ_EXEC_and_WRITE) begin
                num_api_operands    <= num_api_operands +2'h2;
            end
            else begin
                num_api_operands    <= 'h0;
            end
            if (state == READ_EXEC_and_WRITE || state == EXEC_and_WRITE || state == WRITE) begin
                num_mem_operands    <= num_mem_operands +2'h2;
            end
            else begin
                num_mem_operands    <= 'h0;
            end
            if (state == DONE) begin
                sigdecode_z_done      <= 'h1;
            end
            else begin
                sigdecode_z_done      <= 'h0;
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
        else if (state == READ_EXEC_and_WRITE || state == EXEC_and_WRITE || state == WRITE) begin
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
            sigmem_a_rd_req <= '{rd_wr_en: RW_IDLE, addr: '0};
            sigmem_b_rd_req <= '{rd_wr_en: RW_IDLE, addr: '0};
        end
        else if (zeroize) begin
            sigmem_a_rd_req <= '{rd_wr_en: RW_IDLE, addr: '0};
            sigmem_b_rd_req <= '{rd_wr_en: RW_IDLE, addr: '0};
        end
        else if (state == READ || state == READ_and_EXEC || state == READ_EXEC_and_WRITE) begin
            sigmem_a_rd_req <= '{rd_wr_en: RW_READ, addr: num_api_operands};
            sigmem_b_rd_req <= '{rd_wr_en: RW_READ, addr: num_api_operands + 1};
        end else begin
            sigmem_a_rd_req <= '{rd_wr_en: RW_IDLE, addr: '0};
            sigmem_b_rd_req <= '{rd_wr_en: RW_IDLE, addr: '0};
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
                .data_i(sigmem_a_rd_data[i]),
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
                .data_i(sigmem_b_rd_data[i]),
                .data_o(mem_b_wr_data[i])
            );
        end : dec_unit
    endgenerate



endmodule