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


module fv_ntt_shuffle_buffer_constraints
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
    input logic [1:0]              rd_cnt,
    input logic                    delay_read,
    input logic                    buf_valid_reg
    //$#//
);

    default clocking default_clk @(posedge pi_clk); endclocking

    logic       first_write;
    logic       first_read;

    // Logic to help identify when we are performing a first read and a first
    // write in the sequence. This is to help with the constraints.
    always_ff @(posedge pi_clk) begin
        if (!pi_reset_n || pi_zeroize) begin
            first_write <= 1'b1;
            first_read  <= 1'b1;
        end
        else if (pi_wr_rst_count) begin
            first_write <= 1'b1;
        end
        else begin
            if (pi_wren) begin
                if (wr_cnt == 3) begin
                    first_write <= 1'b1;
                end
                else begin
                    first_write <= 1'b0;
                end
            end

            if (rd_cnt == 3) begin
                first_read <= 1'b1;
            end
            else if (delay_read && buf_valid_reg) begin
                first_read <= 1'b0;
            end
            else if (po_buf_valid) begin
                first_read <= 1'b0;
            end
        end
    end

    // Constraint to simplify verification
    // mode an shuffle en remain stable during proof time.
    // They are allowed to change for different proof instances.
    assume_mode_stable_when_buf_valid_low: assume property (
        ##1 $stable(pi_mode)
    );

    assume_shuffle_en_stable_when_buf_valid_low: assume property (
        ##1 $stable(pi_shuffle_en)
    );

    // System level constraint. When it's not the first write, always increment wrptr by 1
    assume_incr_wptr: assume property (disable iff (!pi_reset_n || pi_zeroize)
        pi_wren &&
        !first_write
    |->
        pi_wrptr == ($past(pi_wrptr) + 2'd1)
    );

    // System level constraint. When it's not the first read, always increment rdptr by 1
    assume_incr_rptr: assume property (disable iff (!pi_reset_n || pi_zeroize)
        read_in_progress &&
        !first_read
    |->
        pi_rdptr == ($past(pi_rdptr) + 2'd1)
    );

    // System level constraint. When wren is low the wrptr should remain stable
    assume_stable_when_not_wren: assume property (disable iff (!pi_reset_n || pi_zeroize)
        ##1 !pi_wren
    |->
        $stable(pi_wrptr)
    );

    // System level constraint. When a read is not in progress the rdptr should remain stable
    assume_stable_when_not_rden: assume property (disable iff (!pi_reset_n || pi_zeroize)
        ##1 !read_in_progress
    |->
        $stable(pi_rdptr)
    );

    // System level constraint.
    // For ntt mode, the first write should always start with wrptr == 0
    // For the rest of the modes it can start with a random value
    assume_init_wptr_ntt: assume property (disable iff (!pi_reset_n || pi_zeroize)
        !pi_shuffle_en                      ||
        ((pi_shuffle_en && (pi_mode == ct)) &&
        first_write                         &&
        pi_wren)
    |->
        pi_wrptr == 0
    );

    // System level constraint.
    // For INTT mode, the first read should always start with rdptr == 0
    // For the rest of the modes it can start with a random value
    assume_init_rptr_intt: assume property (disable iff (!pi_reset_n || pi_zeroize)
        !pi_shuffle_en                                             ||
        //((pi_shuffle_en && (pi_mode == gs || pi_mode == pwm_intt)) &&
        ((pi_shuffle_en && (pi_mode == gs)) &&
        first_read                                                 &&
        read_in_progress)
    |->
        pi_rdptr == 0
    );

    // System level constraint. There is no wren when the mode is not NTT or INTT
    assume_not_wren_when_not_supported_mode: assume property (disable iff (!pi_reset_n || pi_zeroize)
        pi_mode == pwm || pi_mode == pws || pi_mode == pwa
    |->
        !pi_wren
    );

    // System level constraint. The wren input must remain high when a write sequence has been iniated
    assume_no_bubbles_wren: assume property (disable iff (!pi_reset_n || pi_zeroize)
        wr_cnt > 0
    |->
        pi_wren
    );

    assume_valid_mode: assume property (disable iff (!pi_reset_n)
        pi_mode < 3'd6
    );

    // System level constraint. When buf_valid is asserted, if wren is also not asserted
    // there must be a wr_rst_cnt to prevent the buf_valid from remaining high.
    assume_wr_rst_cnt_when_buf_valid_and_not_wren: assume property (disable iff (!pi_reset_n)
        po_buf_valid &&
        !pi_wren
    |->
        pi_wr_rst_count
    );

    // System level constraint. When wren is high, wr_rst_cnt must be low.
    assume_wr_rst_cnt_low_when_wren: assume property (disable iff (!pi_reset_n)
        pi_wren
    |->
        !pi_wr_rst_count
    );

endmodule

