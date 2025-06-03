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
//
//======================================================================
//
// ntt_shuffle_buffer.sv
// --------

// This buffer temporarily holds data from NTT memory OR NTT BF and collects
// 4 coeffs for each address being read/written to. This buffer will be confisgured based on BF
// mode at ntt_top level. 
// NTT mode --> buffer contains data read from memory before it's consumed by BF2x2
// INTT mode --> buffer contains data from BF2x2 to be written to memory

// This buffer is customized to support shuffling countermeasure for NTT. It's an
// addressable buffer with the following attributes:
// NTT mode --> writes to buffer are in order. Starting read addr is randomized
// INTT mode --> Starting write addr is randomized. Reads from buffer are in order

module ntt_shuffle_buffer
    import abr_params_pkg::*;
    import ntt_defines_pkg::*;
    #(
        parameter REG_SIZE = 24
    )
    (
        input wire clk,
        input wire reset_n,
        input wire zeroize,
        input mode_t mode,
        input wire shuffle_en,
        input wire wren,
        input wire rden,
        input wire [1:0] wrptr,
        input wire [1:0] rdptr,
        input wire wr_rst_count,
        // input wire rd_rst_count,
        input wire [(4*REG_SIZE)-1:0] data_i,
        output logic buf_valid,
        output logic [(4*REG_SIZE)-1:0] data_o
    );

        //buffer*[0] is lo, buffer*[1] is hi
        logic [1:0][3:0][3:0][REG_SIZE-1:0] buffer; //2x4x4 buffer [lo_hi][]

        logic [1:0] data_i_count, data_i_count_reg;
        logic lo_hi, lo_hi_reg, lo_hi_rd; //0 - lo, 1 - hi

        //Write
        always_ff @(posedge clk or negedge reset_n) begin
            if (!reset_n) begin
                buffer <= 'h0;
            end
            else if (zeroize) begin
                buffer <= 'h0;
            end
            else if (wren) begin
                buffer[lo_hi][wrptr] <= data_i; //4 coeff into lo/hi buf0/1/2/3 based on wrptr
            end
        end

        //Buffer valid
        always_ff @(posedge clk or negedge reset_n) begin
            if (!reset_n) begin
                data_i_count <= 'h0;
                data_i_count_reg <= 'h0;
            end
            else if (zeroize) begin
                data_i_count <= 'h0;
                data_i_count_reg <= 'h0;
            end
            else if (wr_rst_count) begin
                data_i_count <= 'h0;
                data_i_count_reg <= 'h0;
            end
            else if (wren) begin
                data_i_count <= data_i_count + 'h1;
                data_i_count_reg <= data_i_count;
            end
        end

        always_comb begin
            buf_valid = (data_i_count_reg == 'd3);
            lo_hi = buf_valid ^ lo_hi_reg;
            lo_hi_rd = (shuffle_en & (mode == 0)) ? lo_hi_reg : lo_hi; //shuffling delays logic by a cycle, so that needs to be accounted for here as well
        end

        //lo hi
        always_ff @(posedge clk or negedge reset_n) begin
            if (!reset_n)
                lo_hi_reg <= 'b0;
            else if (zeroize)
                lo_hi_reg <= 'b0;
            else if (buf_valid)
                lo_hi_reg <= ~lo_hi_reg;
        end

        //assign output
        always_comb begin
            data_o = '0;
            if (lo_hi_rd) begin
                data_o = {buffer[0][3][rdptr], buffer[0][2][rdptr], buffer[0][1][rdptr], buffer[0][0][rdptr]};
            end else if (~lo_hi_rd) begin
                data_o = {buffer[1][3][rdptr], buffer[1][2][rdptr], buffer[1][1][rdptr], buffer[1][0][rdptr]};
            end
        end

endmodule