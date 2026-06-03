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


module fv_sib_mem_top
#(
    parameter DEPTH      = 64,
    parameter NUM_PORTS  = 1,
    parameter DATA_WIDTH = 32,
    parameter ADDR_WIDTH = $clog2(DEPTH)
    //#$localparams
    //$#//
) (
    //#$ports
    input logic                                 pi_clk_i,
    input logic                                 pi_rst_b,
    input logic                                 pi_zeroize,
    input logic [NUM_PORTS-1:0]                 pi_cs_i,
    input logic [NUM_PORTS-1:0]                 pi_we_i,
    input logic [NUM_PORTS-1:0][ADDR_WIDTH-1:0] pi_addr_i,
    input logic [NUM_PORTS-1:0][DATA_WIDTH-1:0] pi_wdata_i,
    input logic [NUM_PORTS-1:0][DATA_WIDTH-1:0] po_rdata_o
    //$#//
);

    fv_sib_mem_memory #(
        .DEPTH         (DEPTH      ),
        .NUM_PORTS     (NUM_PORTS  ),
        .DATA_WIDTH    (DATA_WIDTH ),
        .MEM_LATENCY   (1          ),
        .RD_WR_SYM_ADDR(1          ),
        .ENABLE_COVERS (1          )
    ) sib_mem_verif
    (
        .clk         (pi_clk_i               ),
        .rst_n       (pi_rst_b && !pi_zeroize),
        .write_enable(pi_we_i & pi_cs_i      ),
        .read_enable (~pi_we_i & pi_cs_i     ),
        .read_address     (pi_addr_i         ),
        .write_address    (pi_addr_i         ),
        .write_data  (pi_wdata_i             ),
        .read_data   (po_rdata_o             )
    );

endmodule

bind sib_mem fv_sib_mem_top #(
    .DEPTH      (DEPTH      ),
    .NUM_PORTS  (NUM_PORTS  ),
    .DATA_WIDTH (DATA_WIDTH ),
    .ADDR_WIDTH (ADDR_WIDTH )
) fv_sib_mem_top_i(
    //#$bind
    .pi_clk_i (clk_i),
    .pi_rst_b (rst_b),
    .pi_zeroize (zeroize),
    .pi_cs_i (cs_i),
    .pi_we_i (we_i),
    .pi_addr_i (addr_i),
    .pi_wdata_i (wdata_i),
    .po_rdata_o (rdata_o)
    //$#//
);
