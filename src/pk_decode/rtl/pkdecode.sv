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
// pkdecode.sv
// --------
// The pkdecode module decodes the t1 polynomials according to the ML-DSA-87 protocol. 
// Each set of 10 bits represents a single coefficient, which is then shifted left by 
// 13 bits to produce a 24-bit output with the MSB set to zero. This module supports
// parallel processing of coefficients and interfaces with memory for storing the results.
// One cycle read and write latency
//======================================================================

module pkdecode
    import abr_params_pkg::*;
    #(
        parameter MLDSA_K = 'h8,
        parameter MLDSA_N = 'd256,
        parameter REG_SIZE = 24,
        parameter INPUT_COEFF_SIZE = 10,
        parameter API_ADDR_WIDTH = 16
    )
    (
        input wire clk,
        input wire reset_n,
        input wire zeroize,

        input wire pkdecode_enable,
        input wire [ABR_MEM_ADDR_WIDTH-1:0] dest_base_addr,
        input wire [8*INPUT_COEFF_SIZE-1:0] API_rd_data,

        output logic [API_ADDR_WIDTH-1:0] API_rd_address,
        output logic [3:0][REG_SIZE-1:0] mem_a_wr_data,
        output logic [3:0][REG_SIZE-1:0] mem_b_wr_data,
        output mem_if_t mem_a_wr_req,
        output mem_if_t mem_b_wr_req,

        output logic pkdecode_done
    );

    localparam COEFF_WIDTH = 10;
    localparam SHIFT_LEFT = 13;
    localparam NUM_COEFFS_PER_CYCLE = 8;
    localparam THE_LAST_ADDR = (MLDSA_K * MLDSA_N)/8;
    // State Machine States
    localparam  IDLE                = 3'b000,
                READ                = 3'b001,
                READ_and_EXEC       = 3'b010,
                READ_and_WRITE      = 3'b011,
                WRITE               = 3'b100,
                DONE                = 3'b101;

    // Internal signals
    logic [7:0][REG_SIZE-1:0] coefficients;  // Extracted 10-bit coefficients
    logic [7:0][REG_SIZE-1:0] encoded_coeffs; // Encoded 24-bit coefficients
    logic [ABR_MEM_ADDR_WIDTH-1:0] locked_dest_addr;
    logic [31:0] num_mem_operands, num_api_operands;   // encoded each four coeff will increment these by one
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
                if (pkdecode_enable)
                    next_state = READ;
                else
                    next_state = IDLE;
            end
            READ: begin
                next_state = READ_and_EXEC;
            end
            READ_and_EXEC: begin
                next_state = READ_and_WRITE;
            end
            READ_and_WRITE: begin
                if (num_api_operands == THE_LAST_ADDR) begin
                    next_state = WRITE;
                end
                else begin
                    next_state = READ_and_WRITE;
                end
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


    // Extract 10-bit coefficients from API_rd_data
    always_comb begin
        for (int i = 0; i < NUM_COEFFS_PER_CYCLE; i++) begin
            coefficients[i] = {24'h0, API_rd_data[COEFF_WIDTH*i +: COEFF_WIDTH]};
        end
    end

    // Encode coefficients into 24-bit format
    always_comb begin
        for (int i = 0; i < NUM_COEFFS_PER_CYCLE; i++) begin
            encoded_coeffs[i] = (coefficients[i] << SHIFT_LEFT);
        end
    end

    // Assign encoded data to memory write ports
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            mem_a_wr_data <= '{default: 0};
            mem_b_wr_data <= '{default: 0};
        end
        else if (zeroize) begin
            mem_a_wr_data <= '{default: 0};
            mem_b_wr_data <= '{default: 0};
        end
        else begin
            mem_a_wr_data <= '{encoded_coeffs[3], encoded_coeffs[2], encoded_coeffs[1], encoded_coeffs[0]};
            mem_b_wr_data <= '{encoded_coeffs[7], encoded_coeffs[6], encoded_coeffs[5], encoded_coeffs[4]};
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
        else if (state == READ_and_WRITE || state == WRITE) begin
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
            API_rd_address <= '0;
        end
        else if (zeroize) begin
            API_rd_address <= '0;
        end
        else if (state == READ || state == READ_and_EXEC || state == READ_and_WRITE) begin
            API_rd_address <= API_ADDR_WIDTH'(num_api_operands);
        end else begin
            API_rd_address <= '0;
        end
    end



    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            num_mem_operands    <= 'h0;
            num_api_operands    <= 'h0;
            locked_dest_addr    <= 'h0;
            pkdecode_done       <= 'h0;
        end
        else if (zeroize) begin
            num_mem_operands    <= 'h0;
            num_api_operands    <= 'h0;
            locked_dest_addr    <= 'h0;
            pkdecode_done       <= 'h0;
        end
        else begin
            if (pkdecode_enable) begin
                locked_dest_addr    <= dest_base_addr;
            end
            if (state == READ || state == READ_and_EXEC || state == READ_and_WRITE) begin
                num_api_operands    <= num_api_operands +1'h1;
            end
            else begin
                num_api_operands    <= 'h0;
            end
            if (state == READ_and_WRITE || state == WRITE) begin
                num_mem_operands    <= num_mem_operands +2'h2;
            end
            else begin
                num_mem_operands    <= 'h0;
            end
            
            if (state == DONE) begin
                pkdecode_done      <= 'h1;
            end
            else begin
                pkdecode_done      <= 'h0;
            end
        end
    end

endmodule
