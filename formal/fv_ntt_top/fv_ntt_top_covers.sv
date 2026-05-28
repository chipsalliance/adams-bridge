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


module fv_ntt_top_covers
    import mldsa_params_pkg::*;
    import ntt_defines_pkg::*;
#(
    parameter REG_SIZE         = 24,
    parameter NTT_REG_SIZE     = REG_SIZE-1,
    parameter MLDSA_Q          = 23'd8380417,
    parameter MLDSA_Q_DIV2_ODD = (MLDSA_Q+1)/2,
    parameter MLDSA_N          = 256,
    parameter MLDSA_LOGN       = $clog2(MLDSA_N),
    parameter MEM_ADDR_WIDTH   = 15,
    parameter MEM_DATA_WIDTH   = 4*REG_SIZE,
    parameter WIDTH            = 46
    //#$localparams
    //$#//
) (
    //#$ports
    input                            pi_clk,
    input                            pi_reset_n,
    input                            pi_zeroize,
    input mode_t                     pi_mode,
    input                            pi_ntt_enable,
    input ntt_mem_addr_t             pi_ntt_mem_base_addr,
    input pwo_mem_addr_t             pi_pwo_mem_base_addr,
    input                            pi_accumulate,
    input                            pi_sampler_valid,
    input                            pi_shuffle_en,
    input                            pi_masking_en,
    input [5:0]                      pi_random,
    input [4:0][WIDTH-1:0]           pi_rnd_i,
    input mem_if_t                   po_mem_wr_req,
    input mem_if_t                   po_mem_rd_req,
    input logic [MEM_DATA_WIDTH-1:0] po_mem_wr_data,
    input [MEM_DATA_WIDTH-1:0]       pi_mem_rd_data,
    input mem_if_t                   po_pwm_a_rd_req,
    input mem_if_t                   po_pwm_b_rd_req,
    input [MEM_DATA_WIDTH-1:0]       pi_pwm_a_rd_data,
    input [MEM_DATA_WIDTH-1:0]       pi_pwm_b_rd_data,
    input logic                      po_ntt_busy,
    input logic                      po_ntt_done
    //$#//
);
default clocking default_clk @(posedge pi_clk); endclocking


property busy;
        disable iff(!pi_reset_n || pi_zeroize)

    po_ntt_busy 
;endproperty
cover_busy: cover property (busy);

property done;
        disable iff(!pi_reset_n || pi_zeroize)

    po_ntt_done
;endproperty
cover_done: cover property (done);


// Make sure all modes are possible
localparam ct =3'd0,
           gs =3'd1,
           pwm=3'd2,
           pwa=3'd3,
           pws=3'd4,
           pwm_intt = 3'd5;
 
property mode_allowed(mode);
        disable iff(!pi_reset_n || pi_zeroize)

    pi_mode == mode
; endproperty 

cover_mode_ct_allowed: cover property (mode_allowed(ct));
cover_mode_gs_allowed: cover property (mode_allowed(gs));
cover_mode_pwm_allowed: cover property (mode_allowed(pwm));
cover_mode_pwa_allowed: cover property (mode_allowed(pwa));
cover_mode_pws_allowed: cover property (mode_allowed(pws));
cover_mode_pwm_intt_allowed: cover property (mode_allowed(pwm_intt));

endmodule
