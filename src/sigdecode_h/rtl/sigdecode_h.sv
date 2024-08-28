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

    // logic [(MLDSA_OMEGA+MLDSA_K)-1:0][7:0] encoded_h;
    // logic [SIG_H_NUM_DWORDS-1:0][31:0] encoded_h_reg;
    logic [MLDSA_OMEGA-1:0] hint_array;
    logic [7:0] hintsum, hintsum_prev_poly, hintsum_curr_poly;
    logic [3:0] poly_count;
    logic [6:0] rd_ptr;
    logic [MLDSA_N-1:0] bitmap;
    logic rst_bitmap;
    logic [3:0][7:0] hint;
    logic [3:0] curr_poly_map;
    logic [$clog2(MLDSA_N)-1:0] bitmap_ptr;
    logic hint_rd_en;
    mem_if_t mem_wr_req_int;

    //TODO: look into remaining_zero - to save some latency, we can save y[w-1:0] as we read them and
    //keep track of what coeffs are being written to memory. If we see that the last y[i] coeff has been written
    //to memory, we don't need to continue and can exit and move to the next poly. Assumption is that memory contains 0s
    //and it's ok for this operation to be non-constant time.

    //Delay flops
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            hintsum             <= 'h0;
            hintsum_prev_poly   <= 'h0;
            mem_wr_data         <= 'h0;
            hint                <= 'h0;
            mem_wr_req.addr     <= 'h0;
            mem_wr_req.rd_wr_en <= RW_IDLE;
            sigdecode_h_error   <= 'b0;
        end
        else if (zeroize) begin
            hintsum             <= 'h0;
            hintsum_prev_poly   <= 'h0;
            mem_wr_data         <= 'h0;
            hint                <= 'h0;
            mem_wr_req.addr     <= 'h0;
            mem_wr_req.rd_wr_en <= RW_IDLE;
            sigdecode_h_error   <= 'b0;
        end
        else begin
            hintsum             <= sigdecode_h_done ? 'h0 : encoded_h_i[MLDSA_OMEGA+poly_count];
            hintsum_prev_poly   <= hintsum;
            mem_wr_data         <= {REG_SIZE'(bitmap[8'(bitmap_ptr+3)]), REG_SIZE'(bitmap[8'(bitmap_ptr+2)]), REG_SIZE'(bitmap[8'(bitmap_ptr+1)]), REG_SIZE'(bitmap[8'(bitmap_ptr)])};
            hint                <= hint_rd_en ? {encoded_h_i[7'(rd_ptr+3)], encoded_h_i[7'(rd_ptr+2)], encoded_h_i[7'(rd_ptr+1)], encoded_h_i[7'(rd_ptr)]} : 'h0;
            mem_wr_req          <= mem_wr_req_int;
            sigdecode_h_error   <= ~sigdecode_h_done & (hintsum < hintsum_prev_poly);
        end
    end

    //bitmap construction
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            bitmap <= 'h0;
        end
        else if (zeroize) begin
            bitmap <= 'h0;
        end
        else if (rst_bitmap) begin
            bitmap <= 'h0;
        end
        else begin
            if (curr_poly_map[0])
                bitmap[hint[0]] <= 'b1;
            if (curr_poly_map[1])
                bitmap[hint[1]] <= 'b1;
            if (curr_poly_map[2])
                bitmap[hint[2]] <= 'b1;
            if (curr_poly_map[3])
                bitmap[hint[3]] <= 'b1;
        end
    end

    always_comb hintsum_curr_poly = hintsum - hintsum_prev_poly;

    sigdecode_h_ctrl sdh_ctrl_inst (
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .sigdecode_h_enable(sigdecode_h_enable),
        .dest_base_addr(dest_base_addr),
        .hintsum_i(hintsum_curr_poly),
        .sigdecode_h_error(sigdecode_h_error),
        .mem_wr_req(mem_wr_req_int),
        .sigdecode_h_done(sigdecode_h_done),
        .poly_count(poly_count),
        .rd_ptr(rd_ptr),
        .rst_bitmap(rst_bitmap),
        .curr_poly_map(curr_poly_map),
        .bitmap_ptr(bitmap_ptr),
        .hint_rd_en(hint_rd_en)
    );

endmodule