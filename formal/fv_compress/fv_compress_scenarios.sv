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


module fv_compress_scenarios
    //#$imports
    import abr_params_pkg::*;
    import compress_defines_pkg::*;
    //$#//
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

    `ifdef SCENARIO0
        assume_num_poly_1: assume property(disable iff(!pi_reset_n || pi_zeroize)
            pi_num_poly == 3'h1
        );
    `endif

    `ifdef SCENARIO1
        assume_num_poly_lte_2: assume property(disable iff(!pi_reset_n || pi_zeroize)
            pi_num_poly <= 3'h2
        );
    `endif

    `ifdef SCENARIO2
        assume_num_poly_lte_3: assume property(disable iff(!pi_reset_n || pi_zeroize)
            pi_num_poly <= 3'h3
        );
    `endif

    `ifdef SCENARIO3
        assume_num_poly_lte_4: assume property(disable iff(!pi_reset_n || pi_zeroize)
            pi_num_poly <= 3'h4
        );
    `endif

    `ifdef SCENARIO4
        assume_num_poly_lte_5: assume property(disable iff(!pi_reset_n || pi_zeroize)
            pi_num_poly <= 3'h5
        );
    `endif

    `ifdef SCENARIO5
        assume_num_poly_lte_6: assume property(disable iff(!pi_reset_n || pi_zeroize)
            pi_num_poly <= 3'h6
        );
    `endif
endmodule

