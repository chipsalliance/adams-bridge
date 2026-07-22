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

// -------------------------------------------------
// Copyright(c) LUBIS EDA GmbH, All rights reserved
// Contact: contact@lubis-eda.com
// -------------------------------------------------


module fv_ntt_shuffle_buffer
    import abr_params_pkg::*;
    import ntt_defines_pkg::*;
#(
    parameter REG_SIZE = 24
    //#$localparams
    //$#//
) (
    //#$ports
    input                          pi_clk,
    input                          pi_reset_n,
    input                          pi_zeroize,
    input mode_t                   pi_mode,
    input                          pi_shuffle_en,
    input                          pi_wren,
    input                          pi_rden,
    input [1:0]                    pi_wrptr,
    input [1:0]                    pi_rdptr,
    input                          pi_wr_rst_count,
    input [(4*REG_SIZE)-1:0]       pi_data_i,
    input logic                    po_buf_valid,
    input logic [(4*REG_SIZE)-1:0] po_data_o,
    input logic                    read_in_progress,
    input logic [1:0]              wr_cnt,
    input logic [1:0]              rd_cnt
    //$#//
);
    // Verification strategy: symbolically choose a wrptr, a buffer half and
    // an entry (REGSIZE chunk of data). When wren is high, the wrptr equals
    // our symbolic entry and the we are writing to the chosen symbolic half,
    // store the expected data. When the rdptr equals our symbolic entry,
    // (the buffer is read in columns instead of rows) compare the REGSIZE
    // chunk of data_o given by the wrptr, to the expected data.

    default clocking default_clk @(posedge pi_clk); endclocking

    logic                sym_half;
    logic [1:0]          sym_wptr;
    logic [1:0]          sym_entry;
    logic                current_wr_half;
    logic                current_rd_half;
    logic [REG_SIZE-1:0] expected_data;

    assume_stable_sym_half : assume property (##1 $stable(sym_half));
    assume_stable_sym_wptr : assume property (##1 $stable(sym_wptr));
    assume_stable_sym_entry: assume property (##1 $stable(sym_entry));

    // Store the expected data when the inputs match our symbolic variables.
    always_ff @(posedge pi_clk) begin
        if (!pi_reset_n || pi_zeroize) begin
            expected_data <= '0;
        end
        else begin
            if (pi_wren && pi_wrptr == sym_wptr && current_wr_half == sym_half) begin
                expected_data <= pi_data_i[REG_SIZE*sym_entry+:REG_SIZE];
            end
        end
    end

    // Calculate which half we are currently reading and writing. Each half consists of
    // 4 elements, so we switch half when the count reaches 3.
    always_ff @(posedge pi_clk) begin
        if (!pi_reset_n || pi_zeroize) begin
            current_wr_half <= 1'b0;
            current_rd_half <= 1'b0;
        end
        else begin
            if (pi_wren && wr_cnt == 3) begin
                current_wr_half <= ~current_wr_half;
            end
            if (rd_cnt == 3) begin
                current_rd_half <= ~current_rd_half;
            end
        end
    end

    // Assertion to check the data_o output. When we read our symbolic entry
    // compare the expected data against the data_o
    assert_buffer_read: assert property (disable iff(!pi_reset_n || pi_zeroize)
        read_in_progress      &&
        pi_rdptr == sym_entry &&
        current_rd_half == sym_half
    |->
        po_data_o[REG_SIZE*sym_wptr+:REG_SIZE] == expected_data
    );

    // buf_valid is only asserted 1 clock cycle after we have written all the entries
    // in a half.
    assert_buf_valid: assert property (disable iff(!pi_reset_n || pi_zeroize)
        pi_wren &&
        wr_cnt == 3
    |->
        ##1
        po_buf_valid
    );

    // otherwise it remains low
    assert_buf_not_valid: assert property (disable iff(!pi_reset_n || pi_zeroize)
        pi_wren &&
        wr_cnt < 3
    |->
        ##1
        !po_buf_valid
    );


endmodule

