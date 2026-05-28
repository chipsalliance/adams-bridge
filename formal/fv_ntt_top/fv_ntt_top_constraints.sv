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


module fv_ntt_top_constraints
    import mldsa_params_pkg::*;
    import mldsa_ctrl_pkg::*;
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



/////////////////////////////


    ///aux logic for stable mode enable and done signal


    logic fv_ongoing;

    always_ff@(posedge pi_clk or negedge pi_reset_n)
    begin
        if(!pi_reset_n || pi_zeroize)
            fv_ongoing <= 1'b0;
        else if(pi_ntt_enable)
            fv_ongoing <= 1'b1;
        else if(po_ntt_done)
            fv_ongoing <= 1'b0;
    end

property stable_mode;
    ##0 fv_ongoing 
    |->
    ##0 $stable(pi_mode)
    ##0 $stable(pi_shuffle_en)
    ##0 $stable(pi_accumulate)
    ##0 $stable(pi_ntt_mem_base_addr)
    ##0 $stable(pi_pwo_mem_base_addr)
;endproperty
assume_stable_mode : assume property(stable_mode);

// Fairness for the sampler_valid
  logic [6:0] sampler_valid_counter;

  always_ff @(posedge pi_clk) begin
    if (!pi_reset_n || pi_zeroize || po_ntt_done) begin
      sampler_valid_counter <= 7'd0;
    end else if ((pi_mode == pwa ||pi_mode == pws ||pi_mode == pwm || pi_mode == pwm_intt) && (ntt_ctrl_inst0.read_fsm_state_ps == RD_EXEC || ntt_ctrl_inst0.read_fsm_state_ps == EXEC_WAIT)) begin
      sampler_valid_counter <= sampler_valid_counter + 7'd1;
    end
  end

assume_64_sampler_valid: assume property(
    sampler_valid_counter < 7'd64
  |=>
    s_eventually(pi_sampler_valid)
  );


  assume_not_more_64_sampler_valid: assume property(
    sampler_valid_counter == 7'd64
  |->
    !pi_sampler_valid
  );

  logic signed [MLDSA_MEM_ADDR_WIDTH:0] src_addr;
  assign src_addr = pi_ntt_mem_base_addr.src_base_addr;
  logic signed [MLDSA_MEM_ADDR_WIDTH:0] interim_addr;
  assign interim_addr = pi_ntt_mem_base_addr.interim_base_addr;
  logic signed [MLDSA_MEM_ADDR_WIDTH:0] dest_addr;
  assign dest_addr = pi_ntt_mem_base_addr.dest_base_addr;

  property valid_base_address;
    fv_ongoing
  |->
    (dest_addr == src_addr || dest_addr >= src_addr + 64 || dest_addr <= src_addr - 64) &&
    (interim_addr <= src_addr - 64 || interim_addr >= src_addr + 64) &&
    (interim_addr <= dest_addr - 64 || interim_addr >= dest_addr + 64)&&
     src_addr[5:0] == '0 &&
    dest_addr[5:0] == '0 &&
    interim_addr[5:0] == '0 ;
  endproperty
  assume_valid_base_address: assume property (valid_base_address);


//Req from spec: Must be set to 1 if mode = PWM_INTT
//Must be set to 0 for all other modes

property mask_only_in_pwmintt;
    ##0 pi_masking_en == (pi_mode == pwm_intt )
;endproperty
assume_mask_only_in_pwmintt: assume property(mask_only_in_pwmintt);

/*
Sampler Valid: Only applies to PWM/PWA/PWS modes. Can randomly be deasserted in each round to model sampler behavior
*/

property sampler_valid_only_in_pwo;
    !(pi_mode == pwa|| pi_mode == pwm || pi_mode == pws)
    |->
    !pi_sampler_valid
;endproperty
assume_sampler_valid_only_in_pwo: assume property(sampler_valid_only_in_pwo);


property only_legal_modes;
    ##0 pi_mode != 3'b111 && pi_mode != 3'b110
;endproperty
assume_only_legal_modes : assume property(only_legal_modes);

endmodule

