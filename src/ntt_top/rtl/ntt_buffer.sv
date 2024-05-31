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
// ntt_buffer.sv
// --------
// Set of 4 buffers of widths 4, 5, 6 and 7 slots. These buffers will
// temporarily hold data from NTT memory and collect 4 coefficients for each
// address being read/written to. This buffer will be configured based on bf mode at ntt_top level.
// In NTT mode (ct mode), buffer will contain data read from memory before 
// it is consumed by butterfly2x2. In INTT mode (gs mode), buffer will contain
// data to be written to memory (bf2x2 outputs). When all 4 coefficients for a given
// op have arrived, the data is passed to bf2x2 module or written to NTT memory (based on bf mode)
//======================================================================

module ntt_buffer
    import ntt_defines_pkg::*;
#(
    parameter REG_SIZE = 23
    // parameter NUM_COEFF = 4
)
(
    input wire clk,
    input wire reset_n,
    input wire zeroize,
    input wire wren, //enables writes to the buffer
    input wire rden, //enables reads to the buffer
    input wire wr_rst_count,
    input wire rd_rst_count,
    input mode_t mode,
    input wire [(4*REG_SIZE)-1:0] data_i,
    output logic buf0_valid,
    output logic [(4*REG_SIZE)-1:0] data_o
);

    logic [3:0][REG_SIZE-1:0] buf0;  //holds 4 entries
    logic [4:0][REG_SIZE-1:0] buf1;  //holds 5 entries
    logic [5:0][REG_SIZE-1:0] buf2;  //holds 6 entries
    logic [6:0][REG_SIZE-1:0] buf3;  //holds 7 entries

    logic [1:0] data_i_count, data_i_count_reg;
    logic [1:0] data_o_count;
    logic wren_reg;

    
    //Write/read
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            buf0 <= 'h0;
            buf1 <= 'h0;
            buf2 <= 'h0;
            buf3 <= 'h0;
            
        end
        else if (zeroize) begin
            buf0 <= 'h0;
            buf1 <= 'h0;
            buf2 <= 'h0;
            buf3 <= 'h0;
            
        end
        else if (wren) begin
                buf0 <= {data_i[REG_SIZE-1:0], buf0[3:1]};
                buf1 <= {data_i[(2*REG_SIZE)-1:REG_SIZE], buf1[4:1]};
                buf2 <= {data_i[(3*REG_SIZE)-1:(2*REG_SIZE)], buf2[5:1]};
                buf3 <= {data_i[(4*REG_SIZE)-1:(3*REG_SIZE)], buf3[6:1]};
        end
    end

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            data_o_count <= 'h0;
        else if (zeroize)
            data_o_count <= 'h0;
        else if (rd_rst_count)
            data_o_count <= 'h0;
        else if (rden)
            data_o_count <= data_o_count + 'h1;
    end

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

    assign buf0_valid = (data_i_count_reg == 'd3);

    always_comb begin
        case(data_o_count)
            'd0: data_o = {buf0[3],buf0[2],buf0[1],buf0[0]};
            'd1: data_o = {buf1[3],buf1[2],buf1[1],buf1[0]};
            'd2: data_o = {buf2[3],buf2[2],buf2[1],buf2[0]};
            'd3: data_o = {buf3[3],buf3[2],buf3[1],buf3[0]};
        endcase
    end

endmodule