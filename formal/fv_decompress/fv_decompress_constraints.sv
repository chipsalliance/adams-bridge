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


module fv_decompress_constraints
    //#$imports
    import abr_params_pkg::*;
    import decompress_defines_pkg::*;
    //$#//
#(
    //#$localparams
    //$#//
) (
    //#$ports
    input logic                                        pi_clk,
    input logic                                        pi_reset_n,
    input logic                                        pi_zeroize,
    input logic                                        pi_decompress_enable,
    input decompress_mode_t                            pi_mode,
    input logic [2:0]                                  pi_num_poly,
    input logic [ABR_MEM_ADDR_WIDTH-1:0]               pi_src_base_addr,
    input logic [ABR_MEM_ADDR_WIDTH-1:0]               pi_dest_base_addr,
    input mem_if_t                                     po_mem_wr_req,
    input logic [COEFF_PER_CLK-1:0][MLDSA_Q_WIDTH-1:0] po_mem_wr_data,
    input logic                                        po_api_rd_en,
    input logic [ABR_MEM_ADDR_WIDTH-1:0]               po_api_rd_addr,
    input logic [1:0][DATA_WIDTH-1:0]                  pi_api_rd_data,
    input logic                                        po_decompress_done
    //$#//
);

    default clocking default_clk @(posedge pi_clk); endclocking

    // decompress_ongoing flag to be used within each constraint
    logic fv_decompress_ongoing;
    always_ff @(posedge pi_clk or negedge pi_reset_n) begin
        if(!pi_reset_n || pi_zeroize) begin
            fv_decompress_ongoing  <= '0;
        end else begin
            if(pi_decompress_enable) begin
                fv_decompress_ongoing <= 1'b1;
            end else if(po_decompress_done) begin
                fv_decompress_ongoing <= 1'b0;
            end
        end
    end

    // when compress_enable is set, it cannot be set again until decompress_done is high
    // this constraint also guarantees that decompress_enable is a pulse
    assume_decompress_enable_low: assume property (disable iff(!pi_reset_n || pi_zeroize)
        fv_decompress_ongoing
    |->
        !pi_decompress_enable
    );

    // mode stays stable during decompression
    assume_mode_stable: assume property (disable iff(!pi_reset_n || pi_zeroize)
        ##1 fv_decompress_ongoing
    |->
        $stable(pi_mode)
    );

    // compare_mode stays stable during decompression
    assume_num_poly_stable: assume property (disable iff(!pi_reset_n || pi_zeroize)
        ##1 fv_decompress_ongoing
    |->
        $stable(pi_num_poly)
    );

    // src_base_addr stays stable during decompression
    assume_src_base_addr_stable: assume property (disable iff(!pi_reset_n || pi_zeroize)
        ##1 fv_decompress_ongoing
    |->
        $stable(pi_src_base_addr)
    );

    // dest_base_addr stays stable during decompression
    assume_dest_base_addr_stable: assume property (disable iff(!pi_reset_n || pi_zeroize)
        ##1 fv_decompress_ongoing
    |->
        $stable(pi_dest_base_addr)
    );

    // The value of dest_base_addr shouldn't allow the address to wrap around
    // 32'h3fff is used to ensure no rollover can happen with the MSBs set to zeros
    assume_dest_base_addr_no_wrap_around: assume property (disable iff(!pi_reset_n || pi_zeroize)
        pi_decompress_enable
    |->
        (pi_dest_base_addr + ((pi_num_poly * (MLKEM_N/4)) - 1)) <= 32'h3fff
    );

    // Maximum number of polynomials that can be received
    localparam FV_MAX_NUM_POLY = (2**($bits(pi_num_poly))-1); // (2^3) - 1 = 8 polynomials
    // Maximum number of api requests per polynomial
    localparam FV_MAX_NUM_API_REQ_PER_POLY = ((12 * MLKEM_N)/64); // ((12*256)/64) = 48 requests
    // Maximum number of api requests if max polynomial and max number of api requests per polynomial is used
    localparam FV_MAX_NUM_API_REQ = FV_MAX_NUM_POLY * FV_MAX_NUM_API_REQ_PER_POLY; // 7 * 48 = 336 requests

    logic [$clog2(FV_MAX_NUM_API_REQ+1)-1:0] fv_api_req_num;
    assign fv_api_req_num = ((pi_mode == DECOMPRESS1)  ? pi_num_poly * ((1 * MLKEM_N)/64) :
                            ((pi_mode == DECOMPRESS5)  ? pi_num_poly * ((5 * MLKEM_N)/64) :
                            ((pi_mode == DECOMPRESS11) ? pi_num_poly * ((11 * MLKEM_N)/64) :
                            ((pi_mode == DECOMPRESS12) ? pi_num_poly * ((12 * MLKEM_N)/64) : 0))));

    // The value of src_base_addr shouldn't allow the address to wrap around
    // 32'h3fff is used to ensure no rollover can happen with the MSBs set to zeros
    // Originally, the assumption was (pi_src_base_addr + fv_api_req_num - 1) <= 32'h3fff
    // Based on issue 189 "https://github.com/chipsalliance/adams-bridge/issues/189", the corner case of reaching 3fff doesn't happen
    // So, -1 was removed in order not to allow the src_base_address to have a value of a location that doesn't exist that causes the address
    // to roll over in the design causing the read done to be lowered which will cause extra requests to be sent to the api memory
    assume_src_base_addr_no_wrap_around: assume property (disable iff(!pi_reset_n || pi_zeroize)
        pi_decompress_enable
    |->
        (pi_src_base_addr + fv_api_req_num) <= 32'h3fff
    );

    // poly_num cannot be zero
    assume_num_poly_not_zero: assume property (disable iff(!pi_reset_n || pi_zeroize)
        pi_decompress_enable
    |->
        pi_num_poly != 0
    );

    // If there is no request to the api memory, its data stay stable
    assume_api_rd_data_stable: assume property (disable iff(!pi_reset_n || pi_zeroize)
        !po_api_rd_en
    |->
        ##1 $stable(pi_api_rd_data)
    );
endmodule

