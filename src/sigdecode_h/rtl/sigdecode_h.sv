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
// sigdecode_h.sv
// -----------
// Processes encoded h component of the signature reg and generates hint vectors per polynomial.
// Every index recorded in y byte string indicates a non-zero hint. Remaining are 0s.
// This module reads the y[w+k-1:w] locations to obtain the number of non-zero hints
// per poly. Then it begins to process y[w-1:0] locations to construct the hint vector.
// To keep it consistent with memory layout, the generated coefficients are 24-bits and
// 4 coeffs are written to each memory addr.

module sigdecode_h
    import mldsa_params_pkg::*;
    #(
        parameter REG_SIZE = 24,
        parameter MLDSA_OMEGA = 75,
        parameter MLDSA_K = 8,
        parameter MLDSA_N = 256
    )
    (
        input wire clk,
        input wire reset_n,
        input wire zeroize,

        input wire [(MLDSA_OMEGA+MLDSA_K)-1:0][7:0] encoded_h_i,

        input wire sigdecode_h_enable,
        input wire [MLDSA_MEM_ADDR_WIDTH-1:0] dest_base_addr,

        output mem_if_t mem_wr_req,
        output logic [(4*REG_SIZE)-1:0] mem_wr_data,
        output logic sigdecode_h_done,
        output logic sigdecode_h_error
    );

    localparam SIG_H_NUM_DWORDS = ((MLDSA_OMEGA + MLDSA_K + 1)*8)/32;

    //TODO: look into remaining_zero - to save some latency, we can save y[w-1:0] as we read them and
    //keep track of what coeffs are being written to memory. If we see that the last y[i] coeff has been written
    //to memory, we don't need to continue and can exit and move to the next poly. Assumption is that memory contains 0s
    //and it's ok for this operation to be non-constant time.

    //Delay flops
    always_ff @(posedge clk) begin   
        mem_wr_data         <= 'h0;
        mem_wr_req.addr     <= 'h0;
        mem_wr_req.rd_wr_en <= RW_IDLE;
        sigdecode_h_error   <= 'b0;
    end


    // State and counter declaration
    typedef enum logic [1:0] {
        IDLE,
        COUNTING,
        DONE
    } sigdecode_hstate_t;

    sigdecode_hstate_t current_state, next_state;
    logic [3:0] cycle_count;  // 4-bit counter to count up to 10 cycles

    // Sequential logic for state transition and cycle counting
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            current_state <= IDLE;
            cycle_count <= 4'd0;
        end else begin
            current_state <= next_state;
            if (current_state == COUNTING) begin
                cycle_count <= cycle_count + 1;
            end else begin
                cycle_count <= 4'd0;
            end
        end
    end

    // Combinational logic for next state and output
    always_comb begin
        next_state = current_state;
        sigdecode_h_done = 1'b0;

        case (current_state)
            IDLE: begin
                if (sigdecode_h_enable) begin
                    next_state = COUNTING;
                end
            end

            COUNTING: begin
                if (cycle_count == 4'd9) begin  // 10 cycles (0-9)
                    next_state = DONE;
                end
            end

            DONE: begin
                sigdecode_h_done = 1'b1;
                next_state = IDLE;  // Go back to IDLE after setting sigdecode_h_done for 1 cycle
            end
        endcase
    end

endmodule