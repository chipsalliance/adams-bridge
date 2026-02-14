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


module fv_ntt_top_mlkem
    import abr_params_pkg::*;
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
    input                            pi_mlkem,
    input [5:0]                      pi_random,
    input [4:0][WIDTH-1:0]           pi_rnd_i,
    input mem_if_t                   po_mem_wr_req,
    input mem_if_t                   po_mem_rd_req,
    input logic [ABR_MEM_MASKED_DATA_WIDTH-1:0] po_mem_wr_data,
    input [ABR_MEM_MASKED_DATA_WIDTH-1:0]       pi_mem_rd_data,
    input mem_if_t                   po_pwm_a_rd_req,
    input mem_if_t                   po_pwm_b_rd_req,
    input [ABR_MEM_MASKED_DATA_WIDTH-1:0]       pi_pwm_a_rd_data,
    input [ABR_MEM_MASKED_DATA_WIDTH-1:0]       pi_pwm_b_rd_data,
    input logic                      po_ntt_busy,
    input logic                      po_ntt_done
    //$#//
);

    default clocking default_clk @(posedge pi_clk); endclocking

  //auxiliary logic fv_ongoing to to be asserted & latched when ntt_enable signal is 1 and deasserted when ntt_done is 1
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

    sequence reset_sequence;
        !pi_reset_n ##1 pi_reset_n;
    endsequence

    //Property to check liveness condition of ntt_busy output signal
    property busy_eventually_not_busy;
        disable iff(!pi_reset_n || pi_zeroize)

    po_ntt_busy |=> s_eventually(!po_ntt_busy)
    ;endproperty
    assert_busy_eventually_not_busy : assert property(busy_eventually_not_busy);

    //Connection check for cmd_ctrl busy to ntt_busy
    property cmd_ctrl_busy_to_output;
        disable iff(!pi_reset_n || pi_zeroize)

    ntt_ctrl_inst0.busy |-> po_ntt_busy
    ;endproperty
    assert_cmd_ctrl_busy_to_output : assert property(cmd_ctrl_busy_to_output);

    //Connection check for cmd_ctrl done to ntt_done
    property cmd_ctrl_done_to_output;
        disable iff(!pi_reset_n || pi_zeroize)

    ntt_ctrl_inst0.done |-> ##1 po_ntt_done
    ;endproperty
    assert_cmd_ctrl_done_to_output : assert property(cmd_ctrl_done_to_output);

    //////////////////////////////
    //////////// Requirement: po_pwm_*_rd_req
    //////////////////////////////
    // Property to check request outputs when the masking is enabled (both for shuffle and not shuffle case)
    // req and addr are flopped from the ntt_ctrl_inst0
     property check_po_pwm_a_rd_req; //line 286 & 287, no change, only pwo mode to incorporate pairwm mode, pwm_a_rd_req is combined into one property
        disable iff(!pi_reset_n || pi_zeroize)

        ##0 ((pi_mode inside {pwm, pwa, pws}) || (pi_mlkem && pi_mode == pairwm))
        ##0 fv_ongoing
        |->
        ##1 po_pwm_a_rd_req.rd_wr_en == ((pi_masking_en & ~pi_shuffle_en) ? ($past(ntt_ctrl_inst0.pw_rden)? RW_READ : RW_IDLE) : ((ntt_ctrl_inst0.pw_rden)? RW_READ : RW_IDLE))
        ##0 po_pwm_a_rd_req.addr == ((pi_masking_en & ~pi_shuffle_en) ? $past(ntt_ctrl_inst0.pw_mem_rd_addr_a) : ntt_ctrl_inst0.pw_mem_rd_addr_a)
    ;endproperty
    assert_check_po_pwm_a_rd_req : assert property(check_po_pwm_a_rd_req);

    // Property to check if it is not a pwo mode then no read request and addr.
    property check_po_pwm_a_rd_req_no_pwo; //line 286, no change, only pwo mode to incorporate pairwm mode
        disable iff(!pi_reset_n || pi_zeroize)
        !((pi_mode inside {pwm, pwa, pws}) | (pi_mlkem & pi_mode == pairwm))
        |->
        po_pwm_a_rd_req.rd_wr_en ==  RW_IDLE
    ;endproperty
    assert_check_po_pwm_a_rd_req_no_pwo : assert property(check_po_pwm_a_rd_req_no_pwo);

    // Property to check if nothing is ongoing then no read request and addr.
    property check_po_pwm_a_rd_req_no_ongoing;
        disable iff(!pi_reset_n || pi_zeroize)
        ##0 !fv_ongoing
        |->
        ##0 po_pwm_a_rd_req.rd_wr_en ==  RW_IDLE
    ;endproperty
    assert_check_po_pwm_a_rd_req_no_ongoing : assert property(check_po_pwm_a_rd_req_no_ongoing);
   
    // Property to check req b when the shuffle is disabled
    property check_po_pwm_b_rd_req_no_shuffle; //line 298-299,  added pairwm case in the condition
        disable iff(!pi_reset_n || pi_zeroize)

        ##0 ((pi_mode inside {pwm, pwa, pws}) || (pi_mlkem && pi_mode == pairwm)) 
        ##0 !pi_shuffle_en
        ##0 (fv_ongoing && !po_ntt_done)
        |->
        ##1 po_pwm_b_rd_req.rd_wr_en == (pi_sampler_valid ? pi_masking_en ? ($past(ntt_ctrl_inst0.pw_rden)? RW_READ : RW_IDLE) : (ntt_ctrl_inst0.pw_rden? RW_READ : RW_IDLE) : RW_IDLE)
        ##0 po_pwm_b_rd_req.addr == ( pi_sampler_valid ? pi_masking_en ? $past(ntt_ctrl_inst0.pw_mem_rd_addr_b) : ntt_ctrl_inst0.pw_mem_rd_addr_b : 0)
    ;endproperty 
    assert_check_po_pwm_b_rd_req_no_shuffle : assert property(check_po_pwm_b_rd_req_no_shuffle);

    // Property to check req_b when the masking is disabled and the shuffle is disabled
    // read req and addr are directly taken from the ntt_ctrl_inst0
    property check_po_pwm_b_rd_req_no_shuffle_no_mask_en; //line 298-299,  added pairwm case in the pwo condition
        disable iff(!pi_reset_n || pi_zeroize)

        ##0 ((pi_mode inside {pwm, pwa, pws}) || (pi_mlkem && pi_mode == pairwm))
        ##0 !pi_shuffle_en
        ##0 fv_ongoing
        ##0 pi_sampler_valid
        ##0 !pi_masking_en
        |->
        ##0 po_pwm_b_rd_req.rd_wr_en == (((ntt_ctrl_inst0.pw_rden))? RW_READ : RW_IDLE)
        ##0 po_pwm_b_rd_req.addr == (ntt_ctrl_inst0.pw_mem_rd_addr_b)
    ;endproperty 
    assert_check_po_pwm_b_rd_req_no_shuffle_no_mask_en : assert property(check_po_pwm_b_rd_req_no_shuffle_no_mask_en);

    // Property to check req b when the shuffling is enabled irrespective of the masking, 
    // just depending on the sampler valid flopped updates the 
    // read req and addr
    property check_po_pwm_b_rd_req_shuffle; //line 293-294,  added pairwm case in the pwo condition
        disable iff(!pi_reset_n || pi_zeroize)

        ##0 ((pi_mode inside {pwm, pwa, pws}) || (pi_mlkem && pi_mode == pairwm))
        ##1 pi_shuffle_en
        |->
        ##0 po_pwm_b_rd_req.rd_wr_en == ((ntt_ctrl_inst0.pw_rden && $past(pi_sampler_valid) )? RW_READ : RW_IDLE)
        ##0 $past(pi_sampler_valid) ? (po_pwm_b_rd_req.addr == ntt_ctrl_inst0.pw_mem_rd_addr_b) : 1'b1
    ;endproperty 
    assert_po_pwm_b_rd_req_shuffle : assert property(check_po_pwm_b_rd_req_shuffle);

    // Property to check if the mode is not pwo then no read request.
    property no_p_mode_no_req; //line 293 298 no change
        disable iff(!pi_reset_n || pi_zeroize)

        ##0 !((pi_mode inside {pwm, pwa, pws}) || (pi_mlkem && pi_mode == pairwm))
        |->
        ##0 po_pwm_a_rd_req.rd_wr_en ==  RW_IDLE
        ##0 po_pwm_b_rd_req.rd_wr_en ==  RW_IDLE
    ;endproperty 
    assert_no_p_mode_no_req : assert property(no_p_mode_no_req);


    //////////////////////////////
    //////////// Requirement: po_mem_wr
    //////////////////////////////

    logic fv_pwo;
    assign fv_pwo = (pi_mode inside {pwm, pwa, pws} || (pi_mlkem && pi_mode == pairwm)); //pwo is added with pairwm_mode condition

    // Property to check write req and addr for ct mode when shuffle is disabled
    property check_mem_wr_req_ct_no_shuffle; //line 216 820 821, no change
        disable iff(!pi_reset_n || pi_zeroize)

        ##0 pi_mode == ct 
        ##0 !pi_shuffle_en
        |=>
        ##0 po_mem_wr_req.rd_wr_en == ($past(ntt_ctrl_inst0.mem_wr_en) ? RW_WRITE : RW_IDLE)
        ##0 (po_mem_wr_req.rd_wr_en == RW_WRITE) ? (po_mem_wr_req.addr == $past(ntt_ctrl_inst0.mem_wr_addr)) : 1'b1
    ;endproperty 
    assert_mem_wr_req_ct_no_shuffle : assert property(check_mem_wr_req_ct_no_shuffle);

    // Property to check write req and addr for ct mode when shuffle is enabled
    property check_mem_wr_req_ct_shuffle; //line 216 820 821, no change
        disable iff(!pi_reset_n || pi_zeroize)

        ##0 pi_mode == ct 
        ##0 pi_shuffle_en
        |=>
        ##0 po_mem_wr_req.rd_wr_en == (ntt_ctrl_inst0.mem_wr_en ? RW_WRITE : RW_IDLE)
        ##0 (po_mem_wr_req.rd_wr_en == RW_WRITE) ? (po_mem_wr_req.addr == ntt_ctrl_inst0.mem_wr_addr) : 1'b1
    ;endproperty 
    assert_mem_wr_req_ct_shuffle : assert property(check_mem_wr_req_ct_shuffle);

    // Property to check write req and addr for gs mode
    property check_mem_wr_req_gs; //line 216 820 821, no change
        disable iff(!pi_reset_n || pi_zeroize)

        ##0 pi_mode == gs
        |=>
        ##0 po_mem_wr_req.rd_wr_en == ((ntt_ctrl_inst0.mem_wr_en) ? RW_WRITE : RW_IDLE)
        ##0 (po_mem_wr_req.rd_wr_en == RW_WRITE) ? (po_mem_wr_req.addr == ntt_ctrl_inst0.mem_wr_addr) : 1'b1
    ;endproperty 
    assert_mem_wr_req_gs : assert property(check_mem_wr_req_gs);

    // Property to check write req and addr for pwo mode
    property check_mem_wr_req_pwo; //line 214 216 no change
        disable iff(!pi_reset_n || pi_zeroize)

        ##0 fv_pwo
        |=>
        ##0 po_mem_wr_req.rd_wr_en == ($past(ntt_ctrl_inst0.pw_wren) ? RW_WRITE : RW_IDLE)
        ##0 (po_mem_wr_req.rd_wr_en == RW_WRITE) ? (po_mem_wr_req.addr == $past(ntt_ctrl_inst0.pw_mem_wr_addr_c)) : 1'b1
    ;endproperty 
    assert_mem_wr_req_pwo : assert property(check_mem_wr_req_pwo);

    // Property to check  for wr_data output during ct_mode and wr_req is write
    // data is flopped from the hybrid_bf2x2 instance u & v outputs
    property check_mem_wr_data_ct; //line 217 no change
        disable iff(!pi_reset_n || pi_zeroize)

        ##0 pi_mode == ct 
        ##0 po_mem_wr_req.rd_wr_en == RW_WRITE
        |->
        po_mem_wr_data ==  $past({1'b0, hybrid_bf2x2.uv_o.v21_o, 1'b0, hybrid_bf2x2.uv_o.u21_o, 1'b0, hybrid_bf2x2.uv_o.v20_o, 1'b0, hybrid_bf2x2.uv_o.u20_o})
    ;endproperty 
    assert_mem_wr_data_ct : assert property(check_mem_wr_data_ct);

    // Property to check  for wr_data output during gs_mode and wr_req is write
    // data is taken from the buffer instance
    property check_mem_wr_data_gs; //line 217 no change
        disable iff(!pi_reset_n || pi_zeroize)

        ##0 pi_mode == gs 
        ##0 po_mem_wr_req.rd_wr_en == RW_WRITE
        |->
        po_mem_wr_data == buffer_inst0.data_o
    ;endproperty 
    assert_mem_wr_data_gs : assert property(check_mem_wr_data_gs);

   
    logic [(4*REG_SIZE)-1:0] fv_pwm_wr_data; 
    assign fv_pwm_wr_data = {1'b0, hybrid_bf2x2.pwo_uv_o.uv3, 1'b0, hybrid_bf2x2.pwo_uv_o.uv2, 1'b0, hybrid_bf2x2.pwo_uv_o.uv1, 1'b0, hybrid_bf2x2.pwo_uv_o.uv0};
    
    // Property to check for wr_data output during pwo mode when masking is disabled
    // data is flopped from the hybrid_bf2x2 instance pwo outputs
    property check_mem_wr_data_pwm_pwa_pws; //line 232 - 234 added pairwm_case
            disable iff(!pi_reset_n || pi_zeroize)

        ##0 ((pi_mode == pwm) && !pi_masking_en) || ((pi_mode == pairwm) && pi_mlkem && !pi_masking_en)|| pi_mode == pwa || pi_mode == pws
        ##0 po_mem_wr_req.rd_wr_en == RW_WRITE
        |->
        po_mem_wr_data == (pi_shuffle_en ? $past(fv_pwm_wr_data,2) : $past(fv_pwm_wr_data)) 
    ;endproperty 
    assert_mem_wr_data_pwm_pwa_pws : assert property(check_mem_wr_data_pwm_pwa_pws);

    logic [3:0][1:0][MLDSA_SHARE_WIDTH-1:0] fv_pwm_masked_wr_data;
    always_comb begin
        fv_pwm_masked_wr_data[0] = {2'b0, hybrid_bf2x2.pwm_shares_uvo.uv0[1], 2'b0, hybrid_bf2x2.pwm_shares_uvo.uv0[0]};
        fv_pwm_masked_wr_data[1] = {2'b0, hybrid_bf2x2.pwm_shares_uvo.uv1[1], 2'b0, hybrid_bf2x2.pwm_shares_uvo.uv1[0]};
        fv_pwm_masked_wr_data[2] = {2'b0, hybrid_bf2x2.pwm_shares_uvo.uv2[1], 2'b0, hybrid_bf2x2.pwm_shares_uvo.uv2[0]};
        fv_pwm_masked_wr_data[3] = {2'b0, hybrid_bf2x2.pwm_shares_uvo.uv3[1], 2'b0, hybrid_bf2x2.pwm_shares_uvo.uv3[0]}; 
    end

    // Property to check for wr_data output during pwo mode when masking is enabled
    // data is flopped from hybrid 2x2 masked pwm outputs and masked_buttefly1x2 pwm shares output for mldsa case, and taken from masked_pairwm outputs for mlkem case
    property check_mem_wr_data_pwm_masked; //line 236, added pairwm case
        disable iff(!pi_reset_n || pi_zeroize)

        ##0 (((pi_mode == pwm) || ((pi_mode == pairwm) && pi_mlkem)) && pi_masking_en)
        ##0 po_mem_wr_req.rd_wr_en == RW_WRITE
        |->
        po_mem_wr_data ==  (pi_shuffle_en ? $past(fv_pwm_masked_wr_data,2):$past(fv_pwm_masked_wr_data))
    ;endproperty
    assert_mem_wr_data_pwm_masked : assert property(check_mem_wr_data_pwm_masked);

    // Property to check for share_mem_wr_data regs during pwm/pairwm mode and masking enabled
    property check_share_mem_wr_data; //line 248, added pairwm_case
        disable iff(!pi_reset_n || pi_zeroize)

        ##0 (((pi_mode == pwm) || ((pi_mode == pairwm) && pi_mlkem)) && pi_masking_en)
        ##0 po_mem_wr_req.rd_wr_en == RW_WRITE
        |->
        ntt_top.share_mem_wr_data == $past(fv_pwm_masked_wr_data,2)
    ;endproperty
    assert_share_mem_wr_data : assert property(check_share_mem_wr_data);

    // Property to check for share_mem_wr_data regs when not in pwm/pairwm mode and masking enabled
    property check_share_mem_wr_data_other; //line 248, added pairwm_case
        disable iff(!pi_reset_n || pi_zeroize)

        ##0 !((ntt_top.pwm_mode || ntt_top.pairwm_mode) && pi_masking_en)
        |=>
        ntt_top.share_mem_wr_data == '0
    ;endproperty
    assert_share_mem_wr_data_other : assert property(check_share_mem_wr_data_other);

    // Property to check for share_mem_wr_data regs during reset
    property check_share_mem_wr_data_reset; //no change
        $past(!pi_reset_n || pi_zeroize)
        |->
        ntt_top.share_mem_wr_data == '0 &&
        ntt_top.pwm_b_rd_data_reg == '0
    ;endproperty
    assert_check_share_mem_wr_data_reset : assert property(check_share_mem_wr_data_reset);
   
   //////////////////////////////
   //////////// Requirement: po_mem_rd
   //////////////////////////////

    // Property to check read enable and addr for ct or gs mode
    property check_mem_rd_req_ct_gs; //line 272 273, no change for ct/gs non masking mode.
            disable iff(!pi_reset_n || pi_zeroize)

            ##0 fv_ongoing
            ##0 pi_mode == ct || (pi_mode == gs ) // not the first round if masking enable or no masking enable
            |->
            ##0 po_mem_rd_req.rd_wr_en == (ntt_ctrl_inst0.mem_rd_en ? RW_READ : RW_IDLE)
            ##0 ntt_ctrl_inst0.mem_rd_en ? (po_mem_rd_req.addr == ntt_ctrl_inst0.mem_rd_addr) : 1'b1
    ;endproperty 
    assert_check_mem_rd_req_ct_gs : assert property(check_mem_rd_req_ct_gs);

    // Property to check read enable and addr for pwm/pairwm mode when masking is enabled
    property check_mem_rd_req_pwm_mask_shuffle; //line 272 273 added pairwm case
            disable iff(!pi_reset_n || pi_zeroize)

            ##0 fv_ongoing
            ##0 (((pi_mode == pwm) || ((pi_mode == pairwm) && pi_mlkem)) && pi_masking_en ) 
            |->
            ##0 po_mem_rd_req.rd_wr_en == (ntt_ctrl_inst0.pw_share_mem_rden && pi_accumulate ? RW_READ : RW_IDLE)
            ##0 (ntt_ctrl_inst0.pw_share_mem_rden && pi_accumulate) ? (po_mem_rd_req.addr == ntt_ctrl_inst0.pw_mem_rd_addr_c) : 1'b1
    ;endproperty 
    assert_check_mem_rd_req_pwm_mask_shuffle : assert property(check_mem_rd_req_pwm_mask_shuffle);

    // Property to check read enable and addr for pwm/pairwm mode when masking is disabled
    property check_mem_rd_req_pwm_no_mask;  //line 272, added pairwm case
            disable iff(!pi_reset_n || pi_zeroize)

            ##0 fv_ongoing
            ##0 (((pi_mode == pwm) || ((pi_mode == pairwm) && pi_mlkem)) && !pi_masking_en ) 
            |->
            ##0 po_mem_rd_req.rd_wr_en == (ntt_ctrl_inst0.pw_share_mem_rden  ? RW_READ : RW_IDLE)
            ##0 (ntt_ctrl_inst0.pw_share_mem_rden) ? (po_mem_rd_req.addr == ntt_ctrl_inst0.pw_mem_rd_addr_c) : 1
    ;endproperty 
    assert_check_mem_rd_req_pwm_no_mask : assert property(check_mem_rd_req_pwm_no_mask);

    // Property to check read enable and addr for other modes when not in ct, gs or pwm/pairwm mode
    property check_mem_rd_req_other; //line 272, added pairwm case
            disable iff(!pi_reset_n || pi_zeroize)

            ##0 !((pi_mode == pwm) || ((pi_mode == pairwm) && pi_mlkem) || pi_mode == ct || pi_mode == gs)
            |=>
            ##0 po_mem_rd_req.rd_wr_en ==  RW_IDLE
    ;endproperty 
    assert_mem_rd_req_other : assert property(check_mem_rd_req_other);

    // Property to check that mem_rd_en is always asserted 64-cycle long
    property num_rd_always_64;
    disable iff(!pi_reset_n || pi_zeroize)
     fv_ongoing &&
     $rose(ntt_ctrl_inst0.mem_rd_en)
     |->
     ntt_ctrl_inst0.mem_rd_en[*64] ##1 !ntt_ctrl_inst0.mem_rd_en
    ;endproperty
    assert_num_rd_always_64 : assert property(num_rd_always_64);

    // Property to check that mem_wr_en is always asserted 64-cycle long
    property num_wr_always_64;
    disable iff(!pi_reset_n || pi_zeroize)
     fv_ongoing &&
     $rose(ntt_ctrl_inst0.mem_wr_en)
     |->
     ntt_ctrl_inst0.mem_wr_en[*64] ##1 !ntt_ctrl_inst0.mem_wr_en
    ;endproperty
    assert_num_wr_always_64 : assert property(num_wr_always_64);

    // Property to check that pw_rden is always asserted 64-cycle long until done signal is asserted
    property num_pwrd_always_64;
    disable iff(!pi_reset_n || pi_zeroize)
     fv_ongoing &&
     fv_pwo &&
     ((ntt_ctrl_inst0.arc_IDLE_RD_STAGE) ||
     (ntt_ctrl_inst0.pwo_done && pi_ntt_enable))
     |->
     ntt_ctrl_inst0.pw_rden[->64] s_until (ntt_ctrl_inst0.pwo_done)
    ;endproperty
    assert_num_pwrd_always_64 : assert property(num_pwrd_always_64);

    // Property to check that pw_wren is always asserted 64-cycle long until done signal is asserted
    property num_pwwr_always_64;
    disable iff(!pi_reset_n || pi_zeroize)
     fv_ongoing &&
     fv_pwo &&
      ((ntt_ctrl_inst0.arc_IDLE_RD_STAGE) ||
     (ntt_ctrl_inst0.pwo_done && pi_ntt_enable))
     |->
     ntt_ctrl_inst0.pw_wren[->64] s_until (ntt_ctrl_inst0.pwo_done)
    ;endproperty
    assert_num_pwwr_always_64 : assert property(num_pwwr_always_64);

   
    
endmodule

