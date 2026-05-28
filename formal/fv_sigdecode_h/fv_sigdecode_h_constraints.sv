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


module fv_sigdecode_h_constraints
    import abr_params_pkg::*;
    import sigdecode_h_defines_pkg::*;
#(
    parameter REG_SIZE    = 24,
    parameter MLDSA_OMEGA = 75,
    parameter MLDSA_K     = 8,
    parameter MLDSA_N     = 256,
    //#$localparams
    localparam SIG_H_NUM_DWORDS = ((MLDSA_OMEGA+MLDSA_K+1)*8)/32
    //$#//
) (
    //#$ports
    input                                  pi_clk,
    input                                  pi_reset_n,
    input                                  pi_zeroize,
    input [(MLDSA_OMEGA+MLDSA_K)-1:0][7:0] pi_encoded_h_i,
    input                                  pi_sigdecode_h_enable,
    input [ABR_MEM_ADDR_WIDTH-1:0]       pi_dest_base_addr,
    input mem_if_t                         po_mem_wr_req,
    input logic [(4*REG_SIZE)-1:0]         po_mem_wr_data,
    input logic                            po_sigdecode_h_done,
    input logic                            po_sigdecode_h_error
    //$#//
);

    default clocking default_clk @(posedge pi_clk); endclocking

    logic fv_rst_flag;

    always_ff @(posedge pi_clk) begin
        if(!pi_reset_n || pi_zeroize) begin
            fv_rst_flag <= '1;
        end
        else begin
            if(pi_sigdecode_h_enable) begin
                fv_rst_flag <= '0;
            end
        end
    end

    assume_rst_before_enable: assume property (
        ( pi_sigdecode_h_enable
        |->
        fv_rst_flag )
    );

    assume_const_dest_address: assume property (
        ( pi_dest_base_addr[5:0] == 0 ) 
    );

    assume_stable_input: assume property (
        ( !pi_sigdecode_h_enable
        |->
         $stable(pi_encoded_h_i) &&
         $stable(pi_dest_base_addr) )
    );

    assume_one_enable: assume property (
        ( pi_sigdecode_h_enable
        |->
         ##1 !pi_sigdecode_h_enable )
    );

endmodule

bind sigdecode_h fv_sigdecode_h_constraints #(
    .REG_SIZE    (REG_SIZE   ),
    .MLDSA_OMEGA (MLDSA_OMEGA),
    .MLDSA_K     (MLDSA_K    ),
    .MLDSA_N     (MLDSA_N    )
 ) fv_sigdecode_h_constraints_i (
    //#$bind
    .pi_clk (clk),
    .pi_reset_n (reset_n),
    .pi_zeroize (zeroize),
    .pi_encoded_h_i (encoded_h_i),
    .pi_sigdecode_h_enable (sigdecode_h_enable),
    .pi_dest_base_addr (dest_base_addr),
    .po_mem_wr_req (mem_wr_req),
    .po_mem_wr_data (mem_wr_data),
    .po_sigdecode_h_done (sigdecode_h_done),
    .po_sigdecode_h_error (sigdecode_h_error)
    //$#//
);

