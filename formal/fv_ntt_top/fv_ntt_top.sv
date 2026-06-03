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


module fv_ntt_top
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

    property busy_eventually_not_busy;
        disable iff(!pi_reset_n || pi_zeroize)

    po_ntt_busy |=> s_eventually(!po_ntt_busy)
    ;endproperty
    assert_busy_eventually_not_busy : assert property(busy_eventually_not_busy);

    //Connection check for cmd_ctrl busy to ntt_busy
    property cmd_ctrl_busy_to_output;
        disable iff(!pi_reset_n || pi_zeroize)

    (ntt_ctrl_inst0.busy == po_ntt_busy)
    ;endproperty
    assert_cmd_ctrl_busy_to_output : assert property(cmd_ctrl_busy_to_output);

    //Connection check for cmd_ctrl done to ntt_done
    property cmd_ctrl_done_to_output;
        disable iff(!pi_reset_n || pi_zeroize)

    ntt_ctrl_inst0.done |-> ##1 po_ntt_done
    ;endproperty
    assert_cmd_ctrl_done_to_output : assert property(cmd_ctrl_done_to_output);

    property cmd_ctrl_no_done_to_output;
        disable iff(!pi_reset_n || pi_zeroize)

    !ntt_ctrl_inst0.done |-> ##1 !po_ntt_done
    ;endproperty
    assert_cmd_ctrl_no_done_to_output : assert property(cmd_ctrl_no_done_to_output);
    
    //////////////////////////////
    //////////// Requirement: po_pwm_*_rd_req
    //////////////////////////////
    property check_po_pwm_a_rd_req;
        disable iff(!pi_reset_n || pi_zeroize)

        ##0 pi_mode inside {pwm, pwa, pws} || pi_mode == pwm_intt
        |=>
        ##0 po_pwm_a_rd_req.rd_wr_en == (ntt_ctrl_inst0.pw_rden? RW_READ : RW_IDLE)
        ##0 po_pwm_a_rd_req.addr == ntt_ctrl_inst0.pw_mem_rd_addr_a
    ;endproperty
    assert_po_pwm_a_rd_req : assert property(check_po_pwm_a_rd_req);
 
    property check_po_pwm_b_rd_req_no_shuffle;
        disable iff(!pi_reset_n || pi_zeroize)

        ##0 pi_mode inside {pwm, pwa, pws} || pi_mode == pwm_intt
        ##1 !pi_shuffle_en
        |->
        ##0 po_pwm_b_rd_req.rd_wr_en == ((ntt_ctrl_inst0.pw_rden && pi_sampler_valid )? RW_READ : RW_IDLE)
        ##0 (pi_sampler_valid ? po_pwm_b_rd_req.addr == ntt_ctrl_inst0.pw_mem_rd_addr_b:1'b1)
    ;endproperty 
    assert_po_pwm_b_rd_req_no_shuffle : assert property(check_po_pwm_b_rd_req_no_shuffle);
    // replace the sufix implication with the logical implication.

    property check_po_pwm_b_rd_req_shuffle;
        disable iff(!pi_reset_n || pi_zeroize)

        ##0 pi_mode inside {pwm, pwa, pws} || pi_mode == pwm_intt
        ##1 pi_shuffle_en
        |->
        ##0 po_pwm_b_rd_req.rd_wr_en == ((ntt_ctrl_inst0.pw_rden && $past(pi_sampler_valid) )? RW_READ : RW_IDLE)
        ##0 ($past(pi_sampler_valid)? po_pwm_b_rd_req.addr == ntt_ctrl_inst0.pw_mem_rd_addr_b:1'b1)
    ;endproperty 
    assert_po_pwm_b_rd_req_shuffle : assert property(check_po_pwm_b_rd_req_shuffle);

    property no_p_mode_no_req;
        disable iff(!pi_reset_n || pi_zeroize)

        ##0 !(pi_mode inside {pwm, pwa, pws} || pi_mode == pwm_intt)
        
        |->
        ##0 po_pwm_a_rd_req.rd_wr_en ==  RW_IDLE
        ##0 po_pwm_b_rd_req.rd_wr_en ==  RW_IDLE
    ;endproperty 
    assert_no_p_mode_no_req : assert property(no_p_mode_no_req);


    //////////////////////////////
    //////////// Requirement: po_mem_wr
    //////////////////////////////

    logic fv_pwo;
    assign fv_pwo = (pi_mode inside {pwm, pwa, pws} || pi_mode == pwm_intt);

    property check_mem_wr_req_ct_no_shuffle;
        disable iff(!pi_reset_n || pi_zeroize)

        ##0 pi_mode == ct 
        ##0 !pi_shuffle_en
        |=>
        ##0 po_mem_wr_req.rd_wr_en == ($past(ntt_ctrl_inst0.mem_wr_en) ? RW_WRITE : RW_IDLE)
        ##0 ((po_mem_wr_req.rd_wr_en == RW_WRITE)? po_mem_wr_req.addr == $past(ntt_ctrl_inst0.mem_wr_addr):1'b1)
    ;endproperty 
    assert_mem_wr_req_ct_no_shuffle : assert property(check_mem_wr_req_ct_no_shuffle);

    property check_mem_wr_req_ct_shuffle;
        disable iff(!pi_reset_n || pi_zeroize)

        ##0 pi_mode == ct 
        ##0 pi_shuffle_en
        |=>
        ##0 po_mem_wr_req.rd_wr_en == (ntt_ctrl_inst0.mem_wr_en ? RW_WRITE : RW_IDLE)
        ##0 ((po_mem_wr_req.rd_wr_en == RW_WRITE)? po_mem_wr_req.addr == ntt_ctrl_inst0.mem_wr_addr : 1'b1)
    ;endproperty 
    assert_mem_wr_req_ct_shuffle : assert property(check_mem_wr_req_ct_shuffle);

    property check_mem_wr_req_gs;
        disable iff(!pi_reset_n || pi_zeroize)

        ##0 pi_mode == gs
        |=>
        ##0 po_mem_wr_req.rd_wr_en == ((ntt_ctrl_inst0.mem_wr_en) ? RW_WRITE : RW_IDLE) 
        ##0 ((po_mem_wr_req.rd_wr_en == RW_WRITE) ? po_mem_wr_req.addr == ntt_ctrl_inst0.mem_wr_addr:1'b1)
    ;endproperty 
    assert_mem_wr_req_gs : assert property(check_mem_wr_req_gs);

    property check_mem_wr_req_pwo;
        disable iff(!pi_reset_n || pi_zeroize)

        ##0 fv_pwo
        |=>
        ##0 po_mem_wr_req.rd_wr_en == ($past(ntt_ctrl_inst0.pw_wren) ? RW_WRITE : RW_IDLE)
        ##0 ((po_mem_wr_req.rd_wr_en == RW_WRITE)? po_mem_wr_req.addr == $past(ntt_ctrl_inst0.pw_mem_wr_addr_c):1'b1)
    ;endproperty 
    assert_mem_wr_req_pwo : assert property(check_mem_wr_req_pwo);

    property check_mem_wr_data_ct;
        disable iff(!pi_reset_n || pi_zeroize)

        ##0 pi_mode == ct 
        ##0 po_mem_wr_req.rd_wr_en == RW_WRITE
        |->
        po_mem_wr_data ==  $past({1'b0, hybrid_bf2x2.uv_o.v21_o, 1'b0, hybrid_bf2x2.uv_o.u21_o, 1'b0, hybrid_bf2x2.uv_o.v20_o, 1'b0, hybrid_bf2x2.uv_o.u20_o})
    ;endproperty 
    assert_mem_wr_data_ct : assert property(check_mem_wr_data_ct);

    property check_mem_wr_data_gs;
        disable iff(!pi_reset_n || pi_zeroize)

        ##0 pi_mode == gs 
        ##0 po_mem_wr_req.rd_wr_en == RW_WRITE
        |->
        po_mem_wr_data == buffer_inst0.data_o
    ;endproperty 
    assert_mem_wr_data_gs : assert property(check_mem_wr_data_gs);

    property check_mem_wr_data_pwmintt;
        disable iff(!pi_reset_n || pi_zeroize)

        ##0 pi_mode == pwm_intt
        ##0 po_mem_wr_req.rd_wr_en == RW_WRITE
        |->
        po_mem_wr_data == buffer_inst0.data_o
    ;endproperty 
    assert_mem_wr_data_pwmintt : assert property(check_mem_wr_data_pwmintt);

    logic [(4*REG_SIZE)-1:0] fv_pwm_wr_data; 
    assign fv_pwm_wr_data = {1'b0, hybrid_bf2x2.pwo_uv_o.uv3, 1'b0, hybrid_bf2x2.pwo_uv_o.uv2, 1'b0, hybrid_bf2x2.pwo_uv_o.uv1, 1'b0, hybrid_bf2x2.pwo_uv_o.uv0};
    property check_mem_wr_data_pwm_pwa_pws;
            disable iff(!pi_reset_n || pi_zeroize)

        ##0 pi_mode == pwm || pi_mode == pwa || pi_mode == pws
        ##0 po_mem_wr_req.rd_wr_en == RW_WRITE
        |->
        po_mem_wr_data == (pi_shuffle_en ? $past(fv_pwm_wr_data,2) : $past(fv_pwm_wr_data)) 
    ;endproperty 
    assert_mem_wr_data_pwm_pwa_pws : assert property(check_mem_wr_data_pwm_pwa_pws);

   //////////////////////////////
   //////////// Requirement: po_mem_rd
   //////////////////////////////
    

    property check_mem_rd_req_ct_gs_pwm_intt;
            disable iff(!pi_reset_n || pi_zeroize)

            ##0 pi_mode == ct || pi_mode == gs || pi_mode == pwm_intt
            |=>
            ##0 po_mem_rd_req.rd_wr_en == (ntt_ctrl_inst0.mem_rd_en ? RW_READ : RW_IDLE)
            ##0 ((ntt_ctrl_inst0.mem_rd_en) ? po_mem_rd_req.addr == ntt_ctrl_inst0.mem_rd_addr:1'b1)
    ;endproperty 
    assert_mem_rd_req_ct_gs_pwm_intt : assert property(check_mem_rd_req_ct_gs_pwm_intt);

    property check_mem_rd_req_pwm;
            disable iff(!pi_reset_n || pi_zeroize)

            ##0 pi_mode == pwm
            |=>
            ##0 po_mem_rd_req.rd_wr_en == (ntt_ctrl_inst0.pw_rden && pi_accumulate ? RW_READ : RW_IDLE)
            ##0 po_mem_rd_req.addr ==  ntt_ctrl_inst0.pw_mem_rd_addr_c
    ;endproperty 
    assert_mem_rd_req_pwm : assert property(check_mem_rd_req_pwm);

    property check_mem_rd_req_other;
            disable iff(!pi_reset_n || pi_zeroize)

            ##0 !((pi_mode == pwm) || pi_mode == ct || pi_mode == gs || pi_mode == pwm_intt)
            |=>
            ##0 po_mem_rd_req.rd_wr_en ==  RW_IDLE
    ;endproperty 
    assert_mem_rd_req_other : assert property(check_mem_rd_req_other);
    
    property num_rd_always_64;
    disable iff(!pi_reset_n || pi_zeroize)
     fv_constraints_i.fv_ongoing &&
     $rose(ntt_ctrl_inst0.mem_rd_en)
     |->
     ntt_ctrl_inst0.mem_rd_en[*64] ##1 !ntt_ctrl_inst0.mem_rd_en
    ;endproperty
    assert_num_rd_always_64 : assert property(num_rd_always_64);

    property num_wr_always_64;
    disable iff(!pi_reset_n || pi_zeroize)
     fv_constraints_i.fv_ongoing &&
     $rose(ntt_ctrl_inst0.mem_wr_en)
     |->
     ntt_ctrl_inst0.mem_wr_en[*64] ##1 !ntt_ctrl_inst0.mem_wr_en
    ;endproperty
    assert_num_wr_always_64 : assert property(num_wr_always_64);

        
    property num_pwrd_always_64;
    disable iff(!pi_reset_n || pi_zeroize)
     fv_constraints_i.fv_ongoing &&
     fv_pwo &&
     ((ntt_ctrl_inst0.arc_IDLE_RD_STAGE) ||
     (ntt_ctrl_inst0.pwo_done && pi_ntt_enable))
     |->
     ntt_ctrl_inst0.pw_rden[->64] s_until (ntt_ctrl_inst0.pwo_done)
    ;endproperty
    assert_num_pwrd_always_64 : assert property(num_pwrd_always_64);

    property num_pwwr_always_64;
    disable iff(!pi_reset_n || pi_zeroize)
     fv_constraints_i.fv_ongoing &&
     fv_pwo &&
      ((ntt_ctrl_inst0.arc_IDLE_RD_STAGE) ||
     (ntt_ctrl_inst0.pwo_done && pi_ntt_enable))
     |->
     ntt_ctrl_inst0.pw_wren[->64] s_until (ntt_ctrl_inst0.pwo_done)
    ;endproperty
    assert_num_pwwr_always_64 : assert property(num_pwwr_always_64);
endmodule

