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
// skencode.sv
// --------
// The skencode module performs the encoding of secret key components into a packed format. 
// This module supports the MLDSA scheme, encoding sk inputs into s1, s2 polynomials. 
// The output coefficients are packed into 24-bit format.
// The design supports dual memory writes per cycle, processing 8 values per cycle for s1 and s2 encoding. 
// The module operates under the control of a single enable pulse, triggering the encoding process for all polynomials. 
// Upon completion, control is transferred back to the host. If any invalid input is detected, the module raises 
// an error flag, halting the operation. Error handling and notifications are left to the host's implementation. 
// 8 instances of the s1s2 encoder can operate simultaneously, each handling 24 bits of data per cycle.
//
//======================================================================

module skencode
    import abr_params_pkg::*;
    import skdecode_defines_pkg::*;
    #(
        parameter MEM_ADDR_WIDTH = 15,
        parameter MLDSA_Q = 23'd8380417,
        parameter MLDSA_L = 'h7,
        parameter MLDSA_K = 'h8,
        parameter MLDSA_N = 'd256,
        parameter REG_SIZE = 24,
        parameter AHB_DATA_WIDTH = 32
    )
    (
        input wire clk,
        input wire reset_n,
        input wire zeroize,
        
        input wire skencode_enable,
        input wire [MEM_ADDR_WIDTH-1:0] dest_base_addr,
        input wire [MEM_ADDR_WIDTH-1:0] src_base_addr,
        input wire  [3:0][REG_SIZE-1:0] mem_a_rd_data,
        input wire  [3:0][REG_SIZE-1:0] mem_b_rd_data,
        input logic mem_rd_data_valid,

        output mem_if_t mem_a_rd_req,
        output mem_if_t mem_b_rd_req,
        output mem_if_t keymem_a_wr_req,
        output logic [AHB_DATA_WIDTH-1:0] keymem_a_wr_data,

        output logic skencode_done
    );

    `include "abr_prim_assert.sv"

    localparam THE_LAST_ADDR = ((MLDSA_K * MLDSA_N)/4)+((MLDSA_L * MLDSA_N)/4)-1;
    localparam THE_LAST_API = ((MLDSA_K +MLDSA_L)*MLDSA_N*3)/32;

    // State Machine States
    localparam  SKENC_IDLE                    = 3'b000,
                SKENC_READ                    = 3'b001,
                SKENC_WAIT_BUFFER             = 3'b010,
                SKENC_WRITE                   = 3'b011,
                SKENC_STALL                   = 3'b100,
                SKENC_GET_LAST                = 3'b101,
                SKENC_DONE                    = 3'b111;

    
    logic [2:0] main_state, next_main_state, write_state, next_write_state;
    logic error_flag;
    logic [7:0][2:0] encoded_coeffs;
    logic [7:0] encoding_error;
    logic [23:0] one_encoding_string;
    logic [95:0] buffer;
    logic [1:0] producer_selector, consumer_selector;
    logic [31:0] num_mem_operands, num_api_operands;   // encoded each four coeff will increment these by one
    logic [MEM_ADDR_WIDTH-1:0] locked_dest_addr, locked_src_addr; // this ensures that addresses are captured when the block is enabled

    assign one_encoding_string = {encoded_coeffs[7],encoded_coeffs[6],encoded_coeffs[5],encoded_coeffs[4],
                                    encoded_coeffs[3],encoded_coeffs[2],encoded_coeffs[1],encoded_coeffs[0]};
    
    
    // State Machine: Updates main_state and write_state based on current conditions and next states.
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            main_state  <= SKENC_IDLE;
            write_state <= SKENC_IDLE;
        end
        else if (zeroize) begin
            main_state  <= SKENC_IDLE;
            write_state <= SKENC_IDLE;
        end
        else begin
            if (error_flag) begin
                main_state     <= SKENC_IDLE;
                write_state    <= SKENC_IDLE;
            end
            else begin
                main_state     <= next_main_state;
                write_state    <= next_write_state;
            end
        end
    end

    // Determines next state for main_state based on current main_state and conditions.
    always_comb begin
        next_main_state = main_state;
        unique case (main_state) inside
            SKENC_IDLE: begin
                if (skencode_enable)
                    next_main_state = SKENC_READ;
                else
                    next_main_state = SKENC_IDLE;
            end
            SKENC_READ: begin
                if (num_mem_operands == THE_LAST_ADDR-1) begin
                    next_main_state = SKENC_DONE;
                end
            end
            SKENC_DONE: begin
                next_main_state = SKENC_IDLE;
            end
            default: begin
                next_main_state = SKENC_IDLE;
            end
        endcase
    end

    // Determines next state for write_state based on current write_state and conditions.
    always_comb begin
        next_write_state = write_state;
        unique case (write_state) inside
            SKENC_IDLE: begin
                if (mem_rd_data_valid)
                    next_write_state    = SKENC_WAIT_BUFFER;
            end
            SKENC_WAIT_BUFFER: begin
                if (producer_selector == 1'b1)
                    next_write_state    = SKENC_WRITE;
            end
            SKENC_WRITE: begin
                if (consumer_selector == 1'b1)
                    next_write_state    = SKENC_STALL;
            end
            SKENC_STALL: begin
                if (num_api_operands == THE_LAST_API) begin
                    next_write_state = SKENC_GET_LAST;
                end
                else begin
                    next_write_state = SKENC_WAIT_BUFFER;
                end
            end
            SKENC_GET_LAST: begin
                next_write_state    = SKENC_DONE;
            end
            SKENC_DONE: begin
                next_write_state    = SKENC_IDLE;
            end
            default: begin
                next_write_state    = SKENC_IDLE;
            end
        endcase
    end

    // Write request generation
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            keymem_a_wr_req     <= '{rd_wr_en: RW_IDLE, addr: '0};
            num_api_operands    <= '0;
            consumer_selector   <= '0;
        end
        else if (zeroize) begin
            keymem_a_wr_req <= '{rd_wr_en: RW_IDLE, addr: '0};
            num_api_operands    <= '0;
            consumer_selector   <= '0;
        end
        else begin
            if (write_state == SKENC_WRITE)
                consumer_selector   <= consumer_selector + 1'b1;
            else
                consumer_selector   <= '0;

            if (write_state == SKENC_IDLE ) begin
                num_api_operands    <= '0;
            end
            else if (write_state == SKENC_WRITE || (write_state == SKENC_WAIT_BUFFER && producer_selector == 1'b1)) begin
                num_api_operands    <= num_api_operands +'h1;
            end

            if (write_state == SKENC_WRITE || (write_state == SKENC_WAIT_BUFFER && producer_selector == 1'b1)) begin
                keymem_a_wr_req <= '{rd_wr_en: RW_WRITE, addr: locked_dest_addr + num_api_operands};
            end
            else begin
                keymem_a_wr_req <= '{rd_wr_en: RW_IDLE, addr: '0};
            end
        end
    end

    // Controls and updates the state of various internal signals and registers based on the state machine and input signals.
    // Resets or initializes all signals execpt for the write operation related logics.
    // Locks destination and source addresses when skencode_enable is active.
    // Manages write_buffer and producer_selector based on the main state machine.
    // Issues read requests to memory and increments num_mem_operands during appropriate states.
    // Signals completion (skencode_done) based on operation progress.
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            producer_selector   <= '0;
            num_mem_operands    <= '0;
            locked_dest_addr    <= '0;
            locked_src_addr     <= '0;
            skencode_done       <= '0;
            mem_a_rd_req        <= '{rd_wr_en: RW_IDLE, addr: '0};
            mem_b_rd_req        <= '{rd_wr_en: RW_IDLE, addr: '0};
        end
        else if (zeroize) begin
            producer_selector   <= '0;
            num_mem_operands    <= '0;
            locked_dest_addr    <= '0;
            locked_src_addr     <= '0;
            skencode_done       <= '0;
            mem_a_rd_req        <= '{rd_wr_en: RW_IDLE, addr: '0};
            mem_b_rd_req        <= '{rd_wr_en: RW_IDLE, addr: '0};
        end
        else begin
            if (skencode_enable) begin
                locked_dest_addr    <= dest_base_addr;
                locked_src_addr     <= src_base_addr;
            end

            if (mem_rd_data_valid)
                producer_selector   <= producer_selector + 1'b1;
            else
                producer_selector   <= '0;

            if (main_state == SKENC_READ) begin
                mem_a_rd_req        <= '{rd_wr_en: RW_READ, addr: locked_src_addr + num_mem_operands};
                mem_b_rd_req        <= '{rd_wr_en: RW_READ, addr: locked_src_addr + num_mem_operands + 1};
                num_mem_operands    <= num_mem_operands +2'h2;
            end else begin
                mem_a_rd_req        <= '{rd_wr_en: RW_IDLE, addr: '0};
                mem_b_rd_req        <= '{rd_wr_en: RW_IDLE, addr: '0};
                num_mem_operands    <= '0;
            end

            if (main_state == SKENC_DONE) begin
                skencode_done      <= 1'b1;
            end
            else begin
                skencode_done      <= '0;
            end
        end
    end
    
    // Manages the 96-bit buffer register based on the write_buffer signal and producer_selector state.
    // Accumulates 24-bit encoded strings into the 96-bit buffer, preparing data for further processing or output.
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            buffer  <= '0;
        end
        else if (zeroize) begin
            buffer  <= '0;
        end
        else begin
            if (mem_rd_data_valid) begin
                if (producer_selector == 2'h0)
                    buffer[23:0]  <= one_encoding_string;
                else if (producer_selector == 2'h1)
                    buffer[47:24] <= one_encoding_string;
                else if (producer_selector == 2'h2)
                    buffer[71:48] <= one_encoding_string;
                else
                    buffer[95:72] <= one_encoding_string;
            end
        end
    end

    // Assigns the appropriate 32-bit portion of the buffer to keymem_a_wr_data based on consumer_selector.
    always_comb begin : API_org
        case(consumer_selector)
            2'h0: keymem_a_wr_data = buffer[31:0];
            2'h1: keymem_a_wr_data = buffer[63:32];
            2'h2: keymem_a_wr_data = buffer[95:64];
            2'h3: keymem_a_wr_data = '0; // Ignored case
        endcase
    end : API_org

    always_comb begin : encoding
        for (int i = 0; i < 4; i++) begin
            unique case(mem_a_rd_data[i]) inside
                REG_SIZE'(0): begin
                    encoded_coeffs[i] = 2;
                    encoding_error[i] = 0;
                end
                REG_SIZE'(1): begin
                    encoded_coeffs[i] = 1;
                    encoding_error[i] = 0;
                end
                REG_SIZE'(2): begin
                    encoded_coeffs[i] = 0;
                    encoding_error[i] = 0;
                end
                MLDSA_Q-1: begin
                    encoded_coeffs[i] = 3;
                    encoding_error[i] = 0;
                end
                MLDSA_Q-2: begin
                    encoded_coeffs[i] = 4;
                    encoding_error[i] = 0;
                end
                default: begin
                    encoded_coeffs[i] = 0;
                    encoding_error[i] = 1;
                end
            endcase
            unique case(mem_b_rd_data[i])
                REG_SIZE'(0): begin
                    encoded_coeffs[i+4] = 2;
                    encoding_error[i+4] = 0;
                end
                REG_SIZE'(1): begin
                    encoded_coeffs[i+4] = 1;
                    encoding_error[i+4] = 0;
                end
                REG_SIZE'(2): begin
                    encoded_coeffs[i+4] = 0;
                    encoding_error[i+4] = 0;
                end
                MLDSA_Q-1: begin
                    encoded_coeffs[i+4] = 3;
                    encoding_error[i+4] = 0;
                end
                MLDSA_Q-2: begin
                    encoded_coeffs[i+4] = 4;
                    encoding_error[i+4] = 0;
                end
                default: begin
                    encoded_coeffs[i+4] = 0;
                    encoding_error[i+4] = 1;
                end
            endcase
        end
    end : encoding
    
    assign error_flag = (|encoding_error) & mem_rd_data_valid;

    `ABR_ASSERT_NEVER(SKENCODE_ERROR_FLAG, error_flag, clk, !reset_n)

endmodule
