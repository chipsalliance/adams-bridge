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


module fv_compress_constraints
    import abr_params_pkg::*;
    import compress_defines_pkg::*;
#(
    //#$localparams
    localparam COMP_DATA_W = 12
    //$#//
) (
    //#$ports
    input                                   pi_clk,
    input                                   pi_reset_n,
    input                                   pi_zeroize,
    input                                   pi_compress_enable,
    input compress_mode_t                   pi_mode,
    input logic                             pi_compare_mode,
    input [2:0]                             pi_num_poly,
    input [ABR_MEM_ADDR_WIDTH-1:0]          pi_src_base_addr,
    input [ABR_MEM_ADDR_WIDTH-1:0]          pi_dest_base_addr,
    input mem_if_t                          po_mem_rd_req,
    input [COEFF_PER_CLK-1:0][REG_SIZE-1:0] pi_mem_rd_data,
    input logic [1:0]                       po_api_rw_en,
    input logic [ABR_MEM_ADDR_WIDTH-1:0]    po_api_rw_addr,
    input logic [DATA_WIDTH-1:0]            po_api_wr_data,
    input logic [DATA_WIDTH-1:0]            pi_api_rd_data,
    input logic                             po_compare_failed,
    input logic                             po_compress_done
    //$#//
);

    default clocking default_clk @(posedge pi_clk); endclocking

    // compress_ongoing flag to be used within each constraint
    logic fv_compress_ongoing;
    always_ff @(posedge pi_clk or negedge pi_reset_n) begin
        if(!pi_reset_n || pi_zeroize) begin
            fv_compress_ongoing  <= '0;
        end else begin
            if(pi_compress_enable) begin
                fv_compress_ongoing <= 1'b1;
            end else if(po_compress_done) begin
                fv_compress_ongoing <= 1'b0;
            end
        end
    end

    // when compress_enable is set, it cannot be set again until compress_done is high
    // this constraint also guarantees that compress_enable is a pulse
    assume_compress_enable_low: assume property (disable iff(!pi_reset_n || pi_zeroize)
        fv_compress_ongoing
    |->
        !pi_compress_enable
    );

    // mode stays stable during compression
    assume_mode_stable: assume property (disable iff(!pi_reset_n || pi_zeroize)
        ##1 fv_compress_ongoing
    |->
        $stable(pi_mode)
    );

    // compare_mode stays stable during compression
    assume_compare_mode_stable: assume property (disable iff(!pi_reset_n || pi_zeroize)
        ##1 fv_compress_ongoing
    |->
        $stable(pi_compare_mode)
    );

    // compare_mode stays stable during compression
    assume_num_poly_stable: assume property (disable iff(!pi_reset_n || pi_zeroize)
        ##1 fv_compress_ongoing
    |->
        $stable(pi_num_poly)
    );

    // src_base_addr stays stable during compression
    assume_src_base_addr_stable: assume property (disable iff(!pi_reset_n || pi_zeroize)
        ##1 fv_compress_ongoing
    |->
        $stable(pi_src_base_addr)
    );

    // dest_base_addr stays stable during compression
    assume_dest_base_addr_stable: assume property (disable iff(!pi_reset_n || pi_zeroize)
        ##1 fv_compress_ongoing
    |->
        $stable(pi_dest_base_addr)
    );

    // The value of src_base_addr shouldn't allow the address to wrap around
    // 32'h3fff is used to ensure no rollover can happen with the MSBs set to zeros
    assume_src_base_addr_no_wrap_around: assume property (disable iff(!pi_reset_n || pi_zeroize)
        pi_compress_enable
    |->
        (pi_src_base_addr + ((pi_num_poly * (MLKEM_N/4)) - 1)) <= 32'h3fff
    );

    // poly_num cannot be zero
    assume_num_poly_not_zero: assume property (disable iff(!pi_reset_n || pi_zeroize)
        pi_compress_enable
    |->
        pi_num_poly != 0
    );

endmodule

