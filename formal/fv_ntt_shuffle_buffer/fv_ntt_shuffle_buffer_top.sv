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


module fv_ntt_shuffle_buffer_top
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
    input logic [(4*REG_SIZE)-1:0] po_data_o
    //$#//
);

    logic       read_in_progress;
    logic       delay_read;
    logic       buf_valid_reg;
    logic [1:0] wr_cnt;
    logic [1:0] rd_cnt;

    // The rden is not used. When buf valid is asserted we start reading continuosly until all
    // columns of a half have been read. Depending on the mode there could be a 1 clock cycle
    // for the reads to start.
    assign delay_read       = (pi_shuffle_en & (pi_mode == 0));
    assign read_in_progress = ((delay_read ? (buf_valid_reg) : (po_buf_valid)) || rd_cnt > 0);

    always_ff @(posedge pi_clk) begin
        if (!pi_reset_n || pi_zeroize) begin
            buf_valid_reg <= 1'b0;
        end
        else begin
            buf_valid_reg <= po_buf_valid;
        end
    end

    lubis_incr_counter_m #(
        .COUNTER_WIDTH(2)
    ) write_counter
    (
        .clk       (pi_clk                                      ),
        .rst       (!pi_reset_n || pi_zeroize || pi_wr_rst_count),
        .soft_rst  (pi_wren && wr_cnt == 3                      ),
        .incr_en   (pi_wren                                     ),
        .incr_val  (2'd1                                        ),
        .count_next(/*open*/                                    ),
        .count     (wr_cnt                                      )
    );

    lubis_incr_counter_m #(
        .COUNTER_WIDTH(2)
    ) read_counter
    (
        .clk       (pi_clk                   ),
        .rst       (!pi_reset_n || pi_zeroize),
        .soft_rst  (rd_cnt == 3              ),
        .incr_en   (read_in_progress         ),
        .incr_val  (2'd1                     ),
        .count_next(/*open*/                 ),
        .count     (rd_cnt                   )
    );

    fv_ntt_shuffle_buffer_constraints #(
        .REG_SIZE(REG_SIZE)
    ) fv_ntt_shuffle_buffer_constraints_i (
        .*,
        .read_in_progress(read_in_progress),
        .wr_cnt          (wr_cnt          ),
        .rd_cnt          (rd_cnt          ),
        .delay_read      (delay_read      ),
        .buf_valid_reg   (buf_valid_reg   )
    );

    fv_ntt_shuffle_buffer #(
        .REG_SIZE(REG_SIZE)
    ) fv_ntt_shuffle_buffer_i (
        .*,
        .read_in_progress(read_in_progress),
        .wr_cnt          (wr_cnt          ),
        .rd_cnt          (rd_cnt          )
    );

endmodule


bind ntt_shuffle_buffer fv_ntt_shuffle_buffer_top #(
    //#$bind
    .REG_SIZE (REG_SIZE)
) fv_ntt_shuffle_buffer_top_i (
    .pi_clk (clk),
    .pi_reset_n (reset_n),
    .pi_zeroize (zeroize),
    .pi_mode (mode),
    .pi_shuffle_en (shuffle_en),
    .pi_wren (wren),
    .pi_rden (rden),
    .pi_wrptr (wrptr),
    .pi_rdptr (rdptr),
    .pi_wr_rst_count (wr_rst_count),
    .pi_data_i (data_i),
    .po_buf_valid (buf_valid),
    .po_data_o (data_o)
    //$#//
);
