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
//#$includes

//`include "abr_sva.svh"
//$#//

module fv_abr_splitter_constraints
    //#$imports
    import abr_params_pkg::*;
    import ntt_defines_pkg::*;
    //$#//
#(
    //#$parameters
    //$#//
    //#$localparams
    //$#//
) (
    //#$ports
    input wire                            pi_clk,
    input wire                            pi_reset_n,
    input wire                            pi_zeroize,
    input wire                            pi_en_i,
    input wire                            pi_mode,
    input wire  [ABR_MEM_DATA_WIDTH-1:0]  pi_data_i,
    input wire  [ABR_MEM_DATA_WIDTH-1:0]  pi_rand_i,
    input logic [ABR_MEM_DATA_WIDTH-1:0]  po_share0_o,
    input logic [ABR_MEM_DATA_WIDTH-1:0]  po_share1_o,
    input logic                           po_ready_o
    //$#//
);

    default clocking default_clk @(posedge pi_clk); endclocking

    //#$instances
    //$#//


    // MldsaDataBit23Zero_A
    // MlkemDataUpperZero_A
    genvar c;
    generate
        for (c = 0; c < COEFF_PER_CLK; c++) begin : gen_data_range
            assume_data_range: assume property (disable iff(!pi_reset_n | pi_zeroize)
                pi_mode ? (pi_data_i[c*REG_SIZE +: REG_SIZE] < MLKEM_Q)
                        : (pi_data_i[c*REG_SIZE +: REG_SIZE] < MLDSA_Q)
            );
        end
    endgenerate

    assume_stable_mode: assume property (disable iff(!pi_reset_n)
        $stable(pi_mode)
    );

endmodule

