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


module fv_ntt_top_mlkem_internal
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

    sequence reset_sequence;
        !pi_reset_n ##1 pi_reset_n;
    endsequence

    //Connectivy property
    property check_connectivity(source,sink);
        source == sink
    ;endproperty

    
    /////////////////
    /// CMD CTRL input
    ////////////////
    // Assertions to check connectivity of command control inputs
    assert_correct_cmd_ctrl_input_ntt_mode: assert property(check_connectivity(ntt_ctrl_inst0.ntt_mode,pi_mode));
    assert_correct_cmd_ctrl_input_ntt_enable: assert property(check_connectivity(ntt_ctrl_inst0.ntt_enable,pi_ntt_enable));
    assert_correct_cmd_ctrl_input_butterfly_ready: assert property(check_connectivity(ntt_ctrl_inst0.butterfly_ready,hybrid_bf2x2.ready_o));
    assert_correct_cmd_ctrl_input_buf0_valid: assert property(check_connectivity(ntt_ctrl_inst0.buf0_valid,buffer_inst0.buf_valid));
    assert_correct_cmd_ctrl_input_sampler_valid: assert property(check_connectivity(ntt_ctrl_inst0.sampler_valid,pi_sampler_valid));
    assert_correct_cmd_ctrl_input_accumulate: assert property(check_connectivity(ntt_ctrl_inst0.accumulate, pi_accumulate));
    assert_correct_cmd_ctrl_input_ntt_mem_base_addr: assert property(check_connectivity(ntt_ctrl_inst0.ntt_mem_base_addr,pi_ntt_mem_base_addr));
    assert_correct_cmd_ctrl_input_pwo_mem_base_addr: assert property(check_connectivity(ntt_ctrl_inst0.pwo_mem_base_addr, pi_pwo_mem_base_addr));
    assert_correct_cmd_ctrl_input_shuffle_en: assert property(check_connectivity(ntt_ctrl_inst0.shuffle_en,pi_shuffle_en));
    assert_correct_cmd_ctrl_input_random: assert property(check_connectivity(ntt_ctrl_inst0.random,pi_random));
    assert_correct_cmd_ctrl_input_masking_en: assert property(check_connectivity(ntt_ctrl_inst0.masking_en,pi_masking_en));
    assert_correct_cmd_ctrl_input_mlkem: assert property(check_connectivity(ntt_ctrl_inst0.mlkem,pi_mlkem));


    /////////////////
    /// Butterfly input
    ////////////////
    // Assertions to check connectivity of butterfly inputs
    assert_correct_butterfly_input_opcode: assert property(check_connectivity(hybrid_bf2x2.mode,ntt_ctrl_inst0.opcode));

    logic [2:0] fv_bf_enable_ctrl_reg;
    always_ff @(posedge pi_clk or negedge pi_reset_n) begin
        if(!pi_reset_n || pi_zeroize) begin
            fv_bf_enable_ctrl_reg <= 1'b0;
        end
        else begin
            fv_bf_enable_ctrl_reg <= {fv_bf_enable_ctrl_reg[1:0],ntt_ctrl_inst0.bf_enable};
        end
    end
    logic fv_bf_enable;
    always_comb begin
        if(ntt_top.ntt_ctrl_aip_i.fv_constraints_i.fv_ongoing) begin
            if(pi_mode == ct) begin
                fv_bf_enable = ntt_ctrl_inst0.bf_enable;
            end
            else if(pi_mode == gs) begin
                if(ntt_ctrl_inst0.masking_en_ctrl) begin
                    fv_bf_enable = fv_bf_enable_ctrl_reg[1];//$past(ntt_ctrl_inst0.bf_enable,2);
                end
                else begin
                    fv_bf_enable = fv_bf_enable_ctrl_reg[0];//$past(ntt_ctrl_inst0.bf_enable);
                end
            end
            else if((pi_mode == pwm) || ((pi_mode == pairwm) && pi_mlkem)) begin //added pairwm_mode line 819
                if(pi_masking_en & !pi_shuffle_en) begin
                    fv_bf_enable = fv_bf_enable_ctrl_reg[2];//$past(ntt_ctrl_inst0.bf_enable,3);
                end
                else begin
                    fv_bf_enable = fv_bf_enable_ctrl_reg[0];//$past(ntt_ctrl_inst0.bf_enable);
                end
            end
            else begin
                fv_bf_enable = fv_bf_enable_ctrl_reg[0];//$past(ntt_ctrl_inst0.bf_enable);
            end
        end
        else begin
            fv_bf_enable = '0;
        end

    end 

    assert_correct_butterfly_input_enable_bf: assert property(
        disable iff(!pi_reset_n || pi_zeroize || !ntt_top.ntt_ctrl_aip_i.fv_constraints_i.fv_ongoing)
    check_connectivity(hybrid_bf2x2.enable,fv_bf_enable));

    assert_correct_butterfly_input_masking: assert property(check_connectivity(hybrid_bf2x2.masking_en,((ntt_top.gs_mode ? ntt_ctrl_inst0.masking_en_ctrl : pi_masking_en))));
    assert_correct_butterfly_input_rnd_i: assert property(check_connectivity(hybrid_bf2x2.rnd_i,pi_rnd_i));
    assert_correct_butterfly_input_accumulate: assert property(check_connectivity(hybrid_bf2x2.accumulate,ntt_ctrl_inst0.accumulate));
    

    //UVW_I: Shuffling
    // Assertion to check uvw_i w input assignments on ct_mode
    property pi_mode_ct_assignment; //added mlkem case: line 378
        disable iff (!pi_reset_n || pi_zeroize)
        (pi_mode == ct) |-> (
            hybrid_bf2x2.uvw_i.w00_i == (pi_mlkem ? {12'h0, w_rom.rdata[MLKEM_REG_SIZE-1:0]} : w_rom.rdata[NTT_REG_SIZE-1:0]) &&
            hybrid_bf2x2.uvw_i.w01_i == (pi_mlkem ? {12'h0, w_rom.rdata[MLKEM_REG_SIZE-1:0]} : w_rom.rdata[NTT_REG_SIZE-1:0]) &&
            hybrid_bf2x2.uvw_i.w10_i == (pi_mlkem ? {12'h0, w_rom.rdata[(2*MLKEM_REG_SIZE)-1:MLKEM_REG_SIZE]} : w_rom.rdata[(2*NTT_REG_SIZE)-1:NTT_REG_SIZE]) &&
            hybrid_bf2x2.uvw_i.w11_i == (pi_mlkem ? {12'h0, w_rom.rdata[(3*MLKEM_REG_SIZE)-1:(2*MLKEM_REG_SIZE)]} : w_rom.rdata[(3*NTT_REG_SIZE)-1:(2*NTT_REG_SIZE)])
        );
    endproperty
    assert_pi_mode_ct_assignment: assert property (pi_mode_ct_assignment);

    // Assertion to check uvw_i w input assignments on gs_mode & shuffling enabled
    property pi_mode_gs_pwm_intt_shuffle; //added mlkem case: line 385
        disable iff (!pi_reset_n || pi_zeroize )
        ##0 ntt_top.ntt_ctrl_aip_i.fv_constraints_i.fv_ongoing
        ##0 (pi_mode == gs) && pi_shuffle_en 
        |-> 
        (
            hybrid_bf2x2.uvw_i.w11_i == (pi_mlkem ? {12'h0, w_rom.rdata[(3*MLKEM_REG_SIZE)-1:(2*MLKEM_REG_SIZE)]} : w_rom.rdata[(3*NTT_REG_SIZE)-1:(2*NTT_REG_SIZE)]) &&
            hybrid_bf2x2.uvw_i.w10_i == (pi_mlkem ? {12'h0, w_rom.rdata[(3*MLKEM_REG_SIZE)-1:(2*MLKEM_REG_SIZE)]} : w_rom.rdata[(3*NTT_REG_SIZE)-1:(2*NTT_REG_SIZE)]) &&
            hybrid_bf2x2.uvw_i.w01_i == (pi_mlkem ? {12'h0, w_rom.rdata[(2*MLKEM_REG_SIZE)-1:MLKEM_REG_SIZE]} : w_rom.rdata[(2*NTT_REG_SIZE)-1:NTT_REG_SIZE]) &&
            hybrid_bf2x2.uvw_i.w00_i == (pi_mlkem ? {12'h0, w_rom.rdata[MLKEM_REG_SIZE-1:0]} : w_rom.rdata[NTT_REG_SIZE-1:0])
        );
    endproperty
    assert_pi_mode_gs_pwm_intt_shuffle: assert property (pi_mode_gs_pwm_intt_shuffle);

    // Assertion to check uvw_i w input assignments on gs_mode & shuffling disabled
    property pi_mode_gs_pwm_intt_no_shuffle; //line 391 added mlkem case
        disable iff (!pi_reset_n || pi_zeroize )
        ##0 ntt_top.ntt_ctrl_aip_i.fv_constraints_i.fv_ongoing
        ##0 (pi_mode == gs ) && 
        !pi_shuffle_en  
        |-> 
        (
            hybrid_bf2x2.uvw_i.w10_i == (pi_mlkem ? {12'h0, $past(w_rom.rdata[(3*MLKEM_REG_SIZE)-1:(2*MLKEM_REG_SIZE)])} : $past(w_rom.rdata[(3*NTT_REG_SIZE)-1:(2*NTT_REG_SIZE)])) &&
            hybrid_bf2x2.uvw_i.w11_i == (pi_mlkem ? {12'h0, $past(w_rom.rdata[(3*MLKEM_REG_SIZE)-1:(2*MLKEM_REG_SIZE)])} : $past(w_rom.rdata[(3*NTT_REG_SIZE)-1:(2*NTT_REG_SIZE)])) &&
            hybrid_bf2x2.uvw_i.w01_i == (pi_mlkem ? {12'h0, $past(w_rom.rdata[(2*MLKEM_REG_SIZE)-1:MLKEM_REG_SIZE])} : $past(w_rom.rdata[(2*NTT_REG_SIZE)-1:NTT_REG_SIZE])) &&
            hybrid_bf2x2.uvw_i.w00_i == (pi_mlkem ? {12'h0, $past(w_rom.rdata[MLKEM_REG_SIZE-1:0])} : $past(w_rom.rdata[NTT_REG_SIZE-1:0]))
        );
    endproperty
    assert_pi_mode_gs_pwm_intt_no_shuffle:assert property (pi_mode_gs_pwm_intt_no_shuffle);

    // Assertion to check uvw_i w input assignments on other modes
    property pi_mode_default_assignment;
        disable iff (!pi_reset_n || pi_zeroize)
        (pi_mode != ct && pi_mode != gs) |-> (
            hybrid_bf2x2.uvw_i.w11_i == 'h0 &&
            hybrid_bf2x2.uvw_i.w10_i == 'h0 &&
            hybrid_bf2x2.uvw_i.w01_i == 'h0 &&
            hybrid_bf2x2.uvw_i.w00_i == 'h0
        );
    endproperty
    assert_pi_mode_default_assignment: assert property (pi_mode_default_assignment);

    // Assertions to check mlkem_shares_pairwm_zeta13_i inputs assignments in pairwm mode    
    property mlkem_shares_pairwm_zeta; //added new register checks for pairwm mode line 407
    ntt_top.ntt_ctrl_aip_i.fv_constraints_i.fv_ongoing
    ##0 !po_ntt_done && ntt_top.pairwm_mode
    |->
    ##3
    hybrid_bf2x2.mlkem_shares_pairwm_zeta13_i.z0_i[0] == ((pi_mlkem && pi_mode == pairwm && pi_masking_en) ? 
                                                            pi_shuffle_en ? (MLKEM_MASKED_WIDTH)'((MASKED_WIDTH)'((MLKEM_MASKED_WIDTH)'($past(w_rom.rdata[(2*MLKEM_Q_WIDTH)-1:MLKEM_Q_WIDTH], 2)) 
                                                            - $past(pi_rnd_i[2][(2*MLKEM_Q_WIDTH)-1:0], 2))) 
                                                            : (MLKEM_MASKED_WIDTH)'((MASKED_WIDTH)'((MLKEM_MASKED_WIDTH)'($past(w_rom.rdata[(2*MLKEM_Q_WIDTH)-1:MLKEM_Q_WIDTH], 3)) 
                                                            - $past(pi_rnd_i[2][(2*MLKEM_Q_WIDTH)-1:0], 3)))
                                                            : 0) &&
    hybrid_bf2x2.mlkem_shares_pairwm_zeta13_i.z0_i[1] == ((pi_mlkem && pi_mode == pairwm && pi_masking_en) ? 
                                                           pi_shuffle_en ? $past(pi_rnd_i[2][(2*MLKEM_Q_WIDTH)-1:0], 2) 
                                                           : $past(pi_rnd_i[2][(2*MLKEM_Q_WIDTH)-1:0], 3)
                                                           : 0) &&
    hybrid_bf2x2.mlkem_shares_pairwm_zeta13_i.z1_i[0] == ((pi_mlkem && pi_mode == pairwm && pi_masking_en) ? 
                                                            pi_shuffle_en ? (MLKEM_MASKED_WIDTH)'((MASKED_WIDTH)'((MLKEM_MASKED_WIDTH)'($past(w_rom.rdata[(3*MLKEM_Q_WIDTH)-1:(2*MLKEM_Q_WIDTH)], 2)) 
                                                            - $past(pi_rnd_i[3][(2*MLKEM_Q_WIDTH)-1:0], 2))) 
                                                            : (MLKEM_MASKED_WIDTH)'((MASKED_WIDTH)'((MLKEM_MASKED_WIDTH)'($past(w_rom.rdata[(3*MLKEM_Q_WIDTH)-1:(2*MLKEM_Q_WIDTH)], 3)) 
                                                            - $past(pi_rnd_i[3][(2*MLKEM_Q_WIDTH)-1:0], 3)))
                                                            : 0) &&
    hybrid_bf2x2.mlkem_shares_pairwm_zeta13_i.z1_i[1] == ((pi_mlkem && pi_mode == pairwm && pi_masking_en) ? 
                                                           pi_shuffle_en ? $past(pi_rnd_i[3][(2*MLKEM_Q_WIDTH)-1:0], 2) 
                                                           : $past(pi_rnd_i[3][(2*MLKEM_Q_WIDTH)-1:0], 3)
                                                           : 0)
    ;
    endproperty
    assert_mlkem_shares_pairwm_zeta: assert property(disable iff (!pi_reset_n || pi_zeroize) mlkem_shares_pairwm_zeta);

    // Assertions to check mlkem_pairwm_zeta13_i inputs assignments in pairwm mode
    property mlkem_pairwm_zeta; //added new register checks for pairwm mode line 417
    ntt_top.ntt_ctrl_aip_i.fv_constraints_i.fv_ongoing
    ##0 ntt_top.pairwm_mode
    |->
    hybrid_bf2x2.mlkem_pairwm_zeta13_i.z0_i == (pi_masking_en ? 0 : $past(w_rom.rdata[(2*MLKEM_REG_SIZE)-1:MLKEM_REG_SIZE])) &&
    hybrid_bf2x2.mlkem_pairwm_zeta13_i.z1_i == (pi_masking_en ? 0 : $past(w_rom.rdata[(3*MLKEM_REG_SIZE)-1:(2*MLKEM_REG_SIZE)]))
    ;
    endproperty
    assert_mlkem_pairwm_zeta: assert property(disable iff (!pi_reset_n || pi_zeroize) mlkem_pairwm_zeta);

    // Assertions to check mlkem_pairwm_zeta13_i inputs assignments are zero when not in pairwm mode
    property no_mlkem_pairwm_zeta; //added new register checks for pairwm mode line 424
    ntt_top.ntt_ctrl_aip_i.fv_constraints_i.fv_ongoing
    ##0 !ntt_top.pairwm_mode
    |->
    hybrid_bf2x2.mlkem_pairwm_zeta13_i.z0_i == 0 &&
    hybrid_bf2x2.mlkem_pairwm_zeta13_i.z1_i == 0 &&
    hybrid_bf2x2.mlkem_shares_pairwm_zeta13_i.z0_i == 0 &&
    hybrid_bf2x2.mlkem_shares_pairwm_zeta13_i.z1_i == 0
    ;
    endproperty
    assert_no_mlkem_pairwm_zeta: assert property(disable iff (!pi_reset_n || pi_zeroize) no_mlkem_pairwm_zeta);

    // -----------------------------------------------
    // Assertions for uvw_i Assignments (Struct)
    // -----------------------------------------------
    // Assertion to check uvw_i u & v & pw_uvw_i input assignments for ct mode
    property check_uvw_assignment_ct; //no change, line 660
        disable iff (!pi_reset_n || pi_zeroize )

        ##0 (pi_mode == ct) 
        ##0 (ntt_top.ntt_ctrl_aip_i.fv_constraints_i.fv_ongoing)
    |-> 
        (hybrid_bf2x2.uvw_i.u00_i == buffer_inst0.data_o[REG_SIZE-2:0] &&
        hybrid_bf2x2.uvw_i.u01_i == buffer_inst0.data_o[(2*REG_SIZE)-2:REG_SIZE] &&
        hybrid_bf2x2.uvw_i.v00_i == buffer_inst0.data_o[(3*REG_SIZE)-2:(2*REG_SIZE)] &&
        hybrid_bf2x2.uvw_i.v01_i == buffer_inst0.data_o[(4*REG_SIZE)-2:(3*REG_SIZE)] &&
         hybrid_bf2x2.pw_uvw_i == '0);
    endproperty
    assert_check_uvw_assignment_ct: assert property (check_uvw_assignment_ct);

    // Assertion to check uvw_i u & v & pw_uvw_i input assignments for gs mode
    property check_uvw_assignment_gs; //no change, line 668
        disable iff (!pi_reset_n || pi_zeroize )
        ##0 (ntt_top.ntt_ctrl_aip_i.fv_constraints_i.fv_ongoing)
        ##0 (pi_mode == gs) 
    |-> 
        (hybrid_bf2x2.uvw_i.u00_i == (ntt_ctrl_inst0.masking_en_ctrl ? '0 :  $past(pi_mem_rd_data[REG_SIZE-2:0])) &&
        hybrid_bf2x2.uvw_i.u01_i ==  (ntt_ctrl_inst0.masking_en_ctrl ? '0 : $past(pi_mem_rd_data[(3*REG_SIZE)-2:(2*REG_SIZE)])) &&
        hybrid_bf2x2.uvw_i.v00_i ==  (ntt_ctrl_inst0.masking_en_ctrl ? '0 : $past(pi_mem_rd_data[(2*REG_SIZE)-2:REG_SIZE])) &&
        hybrid_bf2x2.uvw_i.v01_i ==  (ntt_ctrl_inst0.masking_en_ctrl ? '0 : $past(pi_mem_rd_data[(4*REG_SIZE)-2:(3*REG_SIZE)])) &&
        hybrid_bf2x2.pw_uvw_i == '0 );
    endproperty
    assert_check_uvw_assignment_gs: assert property (check_uvw_assignment_gs);

    // -----------------------------------------------
    // Assertions for pw_uvw_i Assignments (Struct) in pwo mode
    // -----------------------------------------------
    // Assertion to check uvw_i & pw_uvw_i input assignments during pwm mode / pairwm mode and no masking
    property check_pw_uvw_assignment_pwm; //added case pairwm, line 675
        disable iff (!pi_reset_n || pi_zeroize)
        ##0 (ntt_top.ntt_ctrl_aip_i.fv_constraints_i.fv_ongoing)
        ##0 (pi_mode == pwm || pi_mode == pairwm) && !pi_masking_en
    |-> 
        (hybrid_bf2x2.pw_uvw_i.u0_i == $past(ntt_top.pwm_rd_data_a[REG_SIZE-2:0]) &&
        hybrid_bf2x2.pw_uvw_i.u1_i == $past(ntt_top.pwm_rd_data_a[(2*REG_SIZE)-2:REG_SIZE]) &&
        hybrid_bf2x2.pw_uvw_i.u2_i == $past(ntt_top.pwm_rd_data_a[(3*REG_SIZE)-2:(2*REG_SIZE)]) &&
        hybrid_bf2x2.pw_uvw_i.u3_i == $past(ntt_top.pwm_rd_data_a[(4*REG_SIZE)-2:(3*REG_SIZE)]) &&
        hybrid_bf2x2.pw_uvw_i.v0_i == (pi_shuffle_en ? ntt_top.pwm_rd_data_b[REG_SIZE-2:0] : $past(ntt_top.pwm_rd_data_b[REG_SIZE-2:0])) &&
        hybrid_bf2x2.pw_uvw_i.v1_i == (pi_shuffle_en ? ntt_top.pwm_rd_data_b[(2*REG_SIZE)-2:REG_SIZE] : $past(ntt_top.pwm_rd_data_b[(2*REG_SIZE)-2:REG_SIZE])) &&
        hybrid_bf2x2.pw_uvw_i.v2_i == (pi_shuffle_en ? ntt_top.pwm_rd_data_b[(3*REG_SIZE)-2:(2*REG_SIZE)] : $past(ntt_top.pwm_rd_data_b[(3*REG_SIZE)-2:(2*REG_SIZE)])) &&
        hybrid_bf2x2.pw_uvw_i.v3_i == (pi_shuffle_en ? ntt_top.pwm_rd_data_b[(4*REG_SIZE)-2:(3*REG_SIZE)] : $past(ntt_top.pwm_rd_data_b[(4*REG_SIZE)-2:(3*REG_SIZE)])) &&
        hybrid_bf2x2.pw_uvw_i.w0_i == $past(ntt_top.pwm_rd_data_c[REG_SIZE-2:0]) &&
        hybrid_bf2x2.pw_uvw_i.w1_i == $past(ntt_top.pwm_rd_data_c[(2*REG_SIZE)-2:REG_SIZE]) &&
        hybrid_bf2x2.pw_uvw_i.w2_i == $past(ntt_top.pwm_rd_data_c[(3*REG_SIZE)-2:(2*REG_SIZE)]) &&
        hybrid_bf2x2.pw_uvw_i.w3_i == $past(ntt_top.pwm_rd_data_c[(4*REG_SIZE)-2:(3*REG_SIZE)]) &&
        hybrid_bf2x2.uvw_i == '0 );
    endproperty
    assert_check_pw_uvw_assignment_pwm: assert property (check_pw_uvw_assignment_pwm);

    // Assertion to check uvw_i & pw_uvw_i input assignments for pwm mode / pairwm mode and masking
    property check_pw_uvw_assignment_pwm_masking; //line 706 added pairwm case
        disable iff (!pi_reset_n || pi_zeroize)
        ##0 (ntt_top.ntt_ctrl_aip_i.fv_constraints_i.fv_ongoing)
        ##0 (pi_mode == pwm || pi_mode == pairwm) && pi_masking_en
    |-> 
        (hybrid_bf2x2.pw_uvw_i == '0 &&
        hybrid_bf2x2.uvw_i == '0 
       );
    endproperty
    assert_check_pw_uvw_assignment_pwm_masking: assert property (check_pw_uvw_assignment_pwm_masking);

    // Assertion to check uvw_i & pw_uvw_i input assignments for pwa or pws mode
    property check_pw_uvw_assignment_pwa_pws; //line 709, no change
        disable iff (!pi_reset_n || pi_zeroize)
        ##0 (ntt_top.ntt_ctrl_aip_i.fv_constraints_i.fv_ongoing)
        ##0 (pi_mode == pwa || pi_mode == pws)
    |-> 
        (hybrid_bf2x2.pw_uvw_i.u0_i == $past(ntt_top.pwm_rd_data_a[REG_SIZE-2:0]) &&
        hybrid_bf2x2.pw_uvw_i.u1_i == $past(ntt_top.pwm_rd_data_a[(2*REG_SIZE)-2:REG_SIZE]) &&
        hybrid_bf2x2.pw_uvw_i.u2_i == $past(ntt_top.pwm_rd_data_a[(3*REG_SIZE)-2:(2*REG_SIZE)]) &&
        hybrid_bf2x2.pw_uvw_i.u3_i == $past(ntt_top.pwm_rd_data_a[(4*REG_SIZE)-2:(3*REG_SIZE)]) &&
        hybrid_bf2x2.pw_uvw_i.v0_i == (pi_shuffle_en ? ntt_top.pwm_rd_data_b[REG_SIZE-2:0] : $past(ntt_top.pwm_rd_data_b[REG_SIZE-2:0])) &&
        hybrid_bf2x2.pw_uvw_i.v1_i == (pi_shuffle_en ? ntt_top.pwm_rd_data_b[(2*REG_SIZE)-2:REG_SIZE] : $past(ntt_top.pwm_rd_data_b[(2*REG_SIZE)-2:REG_SIZE])) &&
        hybrid_bf2x2.pw_uvw_i.v2_i == (pi_shuffle_en ? ntt_top.pwm_rd_data_b[(3*REG_SIZE)-2:(2*REG_SIZE)] : $past(ntt_top.pwm_rd_data_b[(3*REG_SIZE)-2:(2*REG_SIZE)])) &&
        hybrid_bf2x2.pw_uvw_i.v3_i == (pi_shuffle_en ? ntt_top.pwm_rd_data_b[(4*REG_SIZE)-2:(3*REG_SIZE)] : $past(ntt_top.pwm_rd_data_b[(4*REG_SIZE)-2:(3*REG_SIZE)])) &&
        hybrid_bf2x2.pw_uvw_i.w0_i == '0 &&
        hybrid_bf2x2.pw_uvw_i.w1_i == '0 &&
        hybrid_bf2x2.pw_uvw_i.w2_i == '0 &&
        hybrid_bf2x2.pw_uvw_i.w3_i == '0 &&
        hybrid_bf2x2.uvw_i == '0 );
    endproperty
    assert_check_pw_uvw_assignment_pwa_pws: assert property (check_pw_uvw_assignment_pwa_pws);

    // -----------------------------------------------
    // Assertions for Default Case (Zeroing Out)
    // -----------------------------------------------
    property check_zero_uvw_default; //added pairwm case, line 743
        disable iff (!pi_reset_n || pi_zeroize)
        ##0 ntt_top.ntt_ctrl_aip_i.fv_constraints_i.fv_ongoing
        ##0 (pi_mode != ct && pi_mode != gs && pi_mode != pwm  && pi_mode != pwa && pi_mode != pws && pi_mode != pairwm) 

    |-> 
        (hybrid_bf2x2.uvw_i.u00_i == 'h0 &&
        hybrid_bf2x2.uvw_i.u01_i == 'h0 &&
        hybrid_bf2x2.uvw_i.v00_i == 'h0 &&
        hybrid_bf2x2.uvw_i.v01_i == 'h0);
    endproperty
    assert_check_zero_uvw_default: assert property (check_zero_uvw_default);

    property check_zero_pw_uvw_default; //added pairwm case, line 749
        disable iff (!pi_reset_n || pi_zeroize)
        ##0 ntt_top.ntt_ctrl_aip_i.fv_constraints_i.fv_ongoing &&
        (pi_mode != ct && pi_mode != gs && pi_mode != pwm && pi_mode != pwa && pi_mode != pws && pi_mode != pairwm) 
    |-> 
        (hybrid_bf2x2.pw_uvw_i.u0_i == 'h0 &&
        hybrid_bf2x2.pw_uvw_i.u1_i == 'h0 &&
        hybrid_bf2x2.pw_uvw_i.u2_i == 'h0 &&
        hybrid_bf2x2.pw_uvw_i.u3_i == 'h0 &&
        hybrid_bf2x2.pw_uvw_i.v0_i == 'h0 &&
        hybrid_bf2x2.pw_uvw_i.v1_i == 'h0 &&
        hybrid_bf2x2.pw_uvw_i.v2_i == 'h0 &&
        hybrid_bf2x2.pw_uvw_i.v3_i == 'h0 &&
        hybrid_bf2x2.pw_uvw_i.w0_i == 'h0 &&
        hybrid_bf2x2.pw_uvw_i.w1_i == 'h0 &&
        hybrid_bf2x2.pw_uvw_i.w2_i == 'h0 &&
        hybrid_bf2x2.pw_uvw_i.w3_i == 'h0);
    endproperty
    assert_check_zero_pw_uvw_default: assert property (check_zero_pw_uvw_default);

     // -----------------------------------------------
    // Assertion for the pwm shares used in pwm mode or pairwm mode with masking enable
    // -----------------------------------------------

    logic fv_ongoing_trans;
    logic fv_trans,fv_trans_reset;
    assign fv_ongoing_trans = ntt_top.ntt_ctrl_aip_i.fv_constraints_i.fv_ongoing;
    
    always_ff @( posedge pi_clk, negedge pi_reset_n ) begin : fv_ong_reg
        if ( !pi_reset_n || pi_zeroize ) begin
            fv_trans <= 1'b0;
            fv_trans_reset <= '0;
        end
        else begin  
            fv_trans_reset <= 1'b1;
            fv_trans <= fv_trans_reset;
        end
    end
    // pwm shares u inputs
    property check_pwm_shares_in_pwm_masking_u; //line 773, added pairwm_mode case
        disable iff (!pi_reset_n || pi_zeroize)
        ##0 ntt_top.ntt_ctrl_aip_i.fv_constraints_i.fv_ongoing
        ##0 (pi_mode == pwm || (pi_mlkem && pi_mode == pairwm)) && pi_masking_en /*&& pi_shuffle_en*/
        |->
        ##0 hybrid_bf2x2.pwm_shares_uvw_i.u0_i[0] == (!fv_trans ? '0:  MASKED_WIDTH'(MASKED_WIDTH'($past(ntt_top.pwm_rd_data_a[REG_SIZE-2:0],2)) - $past(pi_rnd_i[0],2)) )
        ##0 hybrid_bf2x2.pwm_shares_uvw_i.u0_i[1] == (!fv_trans ? '0: $past(pi_rnd_i[0],2) )
        ##0 hybrid_bf2x2.pwm_shares_uvw_i.u1_i[0] == (!fv_trans ? '0:  MASKED_WIDTH'(MASKED_WIDTH'($past(ntt_top.pwm_rd_data_a[(2*REG_SIZE)-2:REG_SIZE],2)) - $past(pi_rnd_i[0],2)) )
        ##0 hybrid_bf2x2.pwm_shares_uvw_i.u1_i[1] == (!fv_trans ? '0: $past(pi_rnd_i[0],2) )
        ##0 hybrid_bf2x2.pwm_shares_uvw_i.u2_i[0] == (!fv_trans ? '0:  MASKED_WIDTH'(MASKED_WIDTH'($past(ntt_top.pwm_rd_data_a[(3*REG_SIZE)-2:2*REG_SIZE],2)) - $past(pi_rnd_i[0],2)) )
        ##0 hybrid_bf2x2.pwm_shares_uvw_i.u2_i[1] == (!fv_trans ? '0: $past(pi_rnd_i[0],2))
        ##0 hybrid_bf2x2.pwm_shares_uvw_i.u3_i[0] == (!fv_trans ? '0:  MASKED_WIDTH'(MASKED_WIDTH'($past(ntt_top.pwm_rd_data_a[(4*REG_SIZE)-2:3*REG_SIZE],2)) - $past(pi_rnd_i[0],2)) )
        ##0 hybrid_bf2x2.pwm_shares_uvw_i.u3_i[1] == (!fv_trans ? '0: $past(pi_rnd_i[0],2) )
    ;endproperty
    assert_check_pwm_shares_in_pwm_masking_u: assert property (check_pwm_shares_in_pwm_masking_u);

    // pwm shares v inputs
    property check_pwm_shares_in_pwm_masking_v;
        disable iff (!pi_reset_n || pi_zeroize)
        ##0 ntt_top.ntt_ctrl_aip_i.fv_constraints_i.fv_ongoing
        ##0 !po_ntt_done && (pi_mode == pwm || (pi_mlkem && pi_mode == pairwm)) && pi_masking_en
        |->
        ##2 hybrid_bf2x2.pwm_shares_uvw_i.v0_i[0] == (pi_masking_en ? pi_shuffle_en ? MASKED_WIDTH'($past(ntt_top.pwm_rd_data_b[REG_SIZE-2:0],1)) - $past(pi_rnd_i[1],1)
                                                        : MASKED_WIDTH'($past(ntt_top.pwm_rd_data_b[REG_SIZE-2:0],2)) - $past(pi_rnd_i[1],2)
                                                        : 0)
        ##0 hybrid_bf2x2.pwm_shares_uvw_i.v0_i[1] == (pi_masking_en ? 
                                                        (pi_shuffle_en ?  $past(pi_rnd_i[1],1) : $past(pi_rnd_i[1],2))
                                                        : 0)
        ##0 hybrid_bf2x2.pwm_shares_uvw_i.v1_i[0] == (pi_masking_en ? pi_shuffle_en ? MASKED_WIDTH'($past(ntt_top.pwm_rd_data_b[(2*REG_SIZE)-2:REG_SIZE],1)) - $past(pi_rnd_i[1],1)
                                                        : MASKED_WIDTH'($past(ntt_top.pwm_rd_data_b[(2*REG_SIZE)-2:REG_SIZE],2)) - $past(pi_rnd_i[1],2)
                                                        : 0)
        ##0 hybrid_bf2x2.pwm_shares_uvw_i.v1_i[1] == (pi_masking_en ? 
                                                        (pi_shuffle_en ?  $past(pi_rnd_i[1],1) : $past(pi_rnd_i[1],2))
                                                        : 0)
        ##0 hybrid_bf2x2.pwm_shares_uvw_i.v2_i[0] == (pi_masking_en ? pi_shuffle_en ? MASKED_WIDTH'($past(ntt_top.pwm_rd_data_b[(3*REG_SIZE)-2:2*REG_SIZE],1)) - $past(pi_rnd_i[1],1)
                                                        : MASKED_WIDTH'($past(ntt_top.pwm_rd_data_b[(3*REG_SIZE)-2:2*REG_SIZE],2)) - $past(pi_rnd_i[1],2)
                                                        : 0)
        ##0 hybrid_bf2x2.pwm_shares_uvw_i.v2_i[1] == (pi_masking_en ? 
                                                        (pi_shuffle_en ?  $past(pi_rnd_i[1],1) : $past(pi_rnd_i[1],2))
                                                        : 0)
        ##0 hybrid_bf2x2.pwm_shares_uvw_i.v3_i[0] == (pi_masking_en ? pi_shuffle_en ? MASKED_WIDTH'($past(ntt_top.pwm_rd_data_b[(4*REG_SIZE)-2:3*REG_SIZE],1)) - $past(pi_rnd_i[1],1)
                                                        : MASKED_WIDTH'($past(ntt_top.pwm_rd_data_b[(4*REG_SIZE)-2:3*REG_SIZE],2)) - $past(pi_rnd_i[1],2)
                                                        : 0)
        ##0 hybrid_bf2x2.pwm_shares_uvw_i.v3_i[1] == (pi_masking_en ? 
                                                        (pi_shuffle_en ?  $past(pi_rnd_i[1],1) : $past(pi_rnd_i[1],2))
                                                        : 0)
    ;endproperty
    assert_check_pwm_shares_in_pwm_masking_v: assert property (check_pwm_shares_in_pwm_masking_v);

    // pwm shares w inputs and shuffle enabled
    property check_pwm_shares_in_pwm_masking_w;
        disable iff (!pi_reset_n || pi_zeroize)
        ##0 ntt_top.ntt_ctrl_aip_i.fv_constraints_i.fv_ongoing
        ##0 (pi_mode == pwm || (pi_mlkem && pi_mode == pairwm)) && pi_masking_en && pi_shuffle_en
        |->
        ##0 hybrid_bf2x2.pwm_shares_uvw_i.w0_i[0] == ( (($past(ntt_top.pwm_mode) | $past(ntt_top.pairwm_mode)) & pi_accumulate ? $past(pi_mem_rd_data[(2*REG_SIZE)-3:0]) : '0))
        ##0 hybrid_bf2x2.pwm_shares_uvw_i.w0_i[1] == ( (($past(ntt_top.pwm_mode) | $past(ntt_top.pairwm_mode)) & pi_accumulate ? $past(pi_mem_rd_data[(4*REG_SIZE)-3:2*REG_SIZE]) : '0))
        ##0 hybrid_bf2x2.pwm_shares_uvw_i.w1_i[0] == ( (($past(ntt_top.pwm_mode) | $past(ntt_top.pairwm_mode)) & pi_accumulate ? $past(pi_mem_rd_data[(6*REG_SIZE)-3:4*REG_SIZE]) : '0))
        ##0 hybrid_bf2x2.pwm_shares_uvw_i.w1_i[1] == ( (($past(ntt_top.pwm_mode) | $past(ntt_top.pairwm_mode)) & pi_accumulate ? $past(pi_mem_rd_data[(8*REG_SIZE)-3:6*REG_SIZE]) : '0))
        ##0 hybrid_bf2x2.pwm_shares_uvw_i.w2_i[0] == ( (($past(ntt_top.pwm_mode) | $past(ntt_top.pairwm_mode)) & pi_accumulate ? $past(pi_mem_rd_data[(10*REG_SIZE)-3:8*REG_SIZE]) : '0))
        ##0 hybrid_bf2x2.pwm_shares_uvw_i.w2_i[1] == ( (($past(ntt_top.pwm_mode) | $past(ntt_top.pairwm_mode)) & pi_accumulate ? $past(pi_mem_rd_data[(12*REG_SIZE)-3:10*REG_SIZE]) : '0))
        ##0 hybrid_bf2x2.pwm_shares_uvw_i.w3_i[0] == ( (($past(ntt_top.pwm_mode) | $past(ntt_top.pairwm_mode)) & pi_accumulate ? $past(pi_mem_rd_data[(14*REG_SIZE)-3:12*REG_SIZE]) : '0))
        ##0 hybrid_bf2x2.pwm_shares_uvw_i.w3_i[1] == ( (($past(ntt_top.pwm_mode) | $past(ntt_top.pairwm_mode)) & pi_accumulate ? $past(pi_mem_rd_data[(16*REG_SIZE)-3:14*REG_SIZE]) : '0))
    ;endproperty
    assert_check_pwm_shares_in_pwm_masking_w: assert property (check_pwm_shares_in_pwm_masking_w);

    // pwm shares w inputs in pwm mode and shuffle not enabled
    property check_pwm_shares_in_pwm_masking_w_no_shuffle;
        disable iff (!pi_reset_n || pi_zeroize)

        ##0 ntt_top.ntt_ctrl_aip_i.fv_constraints_i.fv_ongoing && !po_ntt_done && pi_mode == pwm && pi_masking_en && pi_accumulate
        |->
        ##2 hybrid_bf2x2.pwm_shares_uvw_i.w0_i[0] == (pi_masking_en & pi_accumulate ? !pi_shuffle_en ? $past(pi_mem_rd_data[(2*REG_SIZE)-3:0], 2) : $past(pi_mem_rd_data[(2*REG_SIZE)-3:0]) : '0)
        ##0 hybrid_bf2x2.pwm_shares_uvw_i.w0_i[1] == (pi_masking_en & pi_accumulate ? !pi_shuffle_en ? $past(pi_mem_rd_data[(4*REG_SIZE)-3:2*REG_SIZE], 2) : $past(pi_mem_rd_data[(4*REG_SIZE)-3:2*REG_SIZE]) : '0)
        ##0 hybrid_bf2x2.pwm_shares_uvw_i.w1_i[0] == (pi_masking_en & pi_accumulate ? !pi_shuffle_en ? $past(pi_mem_rd_data[(6*REG_SIZE)-3:4*REG_SIZE], 2) : $past(pi_mem_rd_data[(6*REG_SIZE)-3:4*REG_SIZE]) : '0)
        ##0 hybrid_bf2x2.pwm_shares_uvw_i.w1_i[1] == (pi_masking_en & pi_accumulate ? !pi_shuffle_en ? $past(pi_mem_rd_data[(8*REG_SIZE)-3:6*REG_SIZE], 2) : $past(pi_mem_rd_data[(8*REG_SIZE)-3:6*REG_SIZE]) : '0)
        ##0 hybrid_bf2x2.pwm_shares_uvw_i.w2_i[0] == (pi_masking_en & pi_accumulate ? !pi_shuffle_en ? $past(pi_mem_rd_data[(10*REG_SIZE)-3:8*REG_SIZE], 2) : $past(pi_mem_rd_data[(10*REG_SIZE)-3:8*REG_SIZE]) : '0)
        ##0 hybrid_bf2x2.pwm_shares_uvw_i.w2_i[1] == (pi_masking_en & pi_accumulate ? !pi_shuffle_en ? $past(pi_mem_rd_data[(12*REG_SIZE)-3:10*REG_SIZE], 2) : $past(pi_mem_rd_data[(12*REG_SIZE)-3:10*REG_SIZE]) : '0)
        ##0 hybrid_bf2x2.pwm_shares_uvw_i.w3_i[0] == (pi_masking_en & pi_accumulate ? !pi_shuffle_en ? $past(pi_mem_rd_data[(14*REG_SIZE)-3:12*REG_SIZE], 2) : $past(pi_mem_rd_data[(14*REG_SIZE)-3:12*REG_SIZE]) : '0)
        ##0 hybrid_bf2x2.pwm_shares_uvw_i.w3_i[1] == (pi_masking_en & pi_accumulate ? !pi_shuffle_en ? $past(pi_mem_rd_data[(16*REG_SIZE)-3:14*REG_SIZE], 2) : $past(pi_mem_rd_data[(16*REG_SIZE)-3:14*REG_SIZE]) : '0)
    ;endproperty
    assert_check_pwm_shares_in_pwm_masking_w_no_shuffle: assert property (check_pwm_shares_in_pwm_masking_w_no_shuffle);

    // pwm shares w inputs in pairwm mode and shuffle not enabled
    property check_pwm_shares_in_pairwm_masking_w_no_shuffle;
        disable iff (!pi_reset_n || pi_zeroize)

        ##0 ntt_top.ntt_ctrl_aip_i.fv_constraints_i.fv_ongoing && !po_ntt_done
        ##0 ((pi_mlkem && pi_mode == pairwm)) && pi_masking_en && !pi_shuffle_en
        |->
        ##1 hybrid_bf2x2.pwm_shares_uvw_i.w0_i[0] == (($past(ntt_top.pairwm_mode) & pi_accumulate & pi_masking_en & !pi_shuffle_en ? $past(pi_mem_rd_data[(2*REG_SIZE)-3:0]) : '0))
        ##0 hybrid_bf2x2.pwm_shares_uvw_i.w0_i[1] == (($past(ntt_top.pairwm_mode) & pi_accumulate & pi_masking_en & !pi_shuffle_en ? $past(pi_mem_rd_data[(4*REG_SIZE)-3:2*REG_SIZE]) : '0))
        ##0 hybrid_bf2x2.pwm_shares_uvw_i.w1_i[0] == (($past(ntt_top.pairwm_mode) & pi_accumulate & pi_masking_en & !pi_shuffle_en ? $past(pi_mem_rd_data[(6*REG_SIZE)-3:4*REG_SIZE]) : '0))
        ##0 hybrid_bf2x2.pwm_shares_uvw_i.w1_i[1] == (($past(ntt_top.pairwm_mode) & pi_accumulate & pi_masking_en & !pi_shuffle_en ? $past(pi_mem_rd_data[(8*REG_SIZE)-3:6*REG_SIZE]) : '0))
        ##0 hybrid_bf2x2.pwm_shares_uvw_i.w2_i[0] == (($past(ntt_top.pairwm_mode) & pi_accumulate & pi_masking_en & !pi_shuffle_en ? $past(pi_mem_rd_data[(10*REG_SIZE)-3:8*REG_SIZE]) : '0))
        ##0 hybrid_bf2x2.pwm_shares_uvw_i.w2_i[1] == (($past(ntt_top.pairwm_mode) & pi_accumulate & pi_masking_en & !pi_shuffle_en ? $past(pi_mem_rd_data[(12*REG_SIZE)-3:10*REG_SIZE]) : '0))
        ##0 hybrid_bf2x2.pwm_shares_uvw_i.w3_i[0] == (($past(ntt_top.pairwm_mode) & pi_accumulate & pi_masking_en & !pi_shuffle_en ? $past(pi_mem_rd_data[(14*REG_SIZE)-3:12*REG_SIZE]) : '0))
        ##0 hybrid_bf2x2.pwm_shares_uvw_i.w3_i[1] == (($past(ntt_top.pairwm_mode) & pi_accumulate & pi_masking_en & !pi_shuffle_en ? $past(pi_mem_rd_data[(16*REG_SIZE)-3:14*REG_SIZE]) : '0))
    ;endproperty
    assert_check_pwm_shares_in_pairwm_masking_w_no_shuffle: assert property (check_pwm_shares_in_pairwm_masking_w_no_shuffle);

    // pwm shares all inputs zero in pwm/pairwm mode and no masking
    property check_pwm_shares_in_pwm_no_masking;
         disable iff (!pi_reset_n || pi_zeroize)
         ##0 ntt_top.ntt_ctrl_aip_i.fv_constraints_i.fv_ongoing
        ##0 (pi_mode == pwm || !ntt_top.pairwm_mode) && !pi_masking_en
        |->
         ##0 hybrid_bf2x2.pwm_shares_uvw_i == '0 
    ;endproperty
    assert_check_pwm_shares_in_pwm_no_masking: assert property (check_pwm_shares_in_pwm_no_masking);

    // Asserion to check input to the butterfly unit the bf_shares used in case of the gs mode with ctrl masking enable
    property check_bf_shares_in_gs_masking; //line 756 no changes
        disable iff (!pi_reset_n || pi_zeroize)
        ##0 ntt_top.ntt_ctrl_aip_i.fv_constraints_i.fv_ongoing
        ##0 (pi_mode == gs) && ntt_ctrl_inst0.masking_en_ctrl && !pi_mlkem
        |->
        ##0 hybrid_bf2x2.bf_shares_uvw_i.u00_i[0] == ($past(ntt_top.gs_mode && ntt_top.masking_en_ctrl,2) || $past((ntt_top.pwm_mode || ntt_top.pairwm_mode) && pi_accumulate,2) ? $past(pi_mem_rd_data[(2*REG_SIZE)-3:0],2) : '0)
        ##0 hybrid_bf2x2.bf_shares_uvw_i.u00_i[1] == ($past(ntt_top.gs_mode && ntt_top.masking_en_ctrl,2) || $past((ntt_top.pwm_mode || ntt_top.pairwm_mode) && pi_accumulate,2) ? $past(pi_mem_rd_data[(4*REG_SIZE)-3:2*REG_SIZE],2) : '0)
        ##0 hybrid_bf2x2.bf_shares_uvw_i.v00_i[0] == ($past(ntt_top.gs_mode && ntt_top.masking_en_ctrl,2) || $past((ntt_top.pwm_mode || ntt_top.pairwm_mode) && pi_accumulate,2) ? $past(pi_mem_rd_data[(6*REG_SIZE)-3:4*REG_SIZE],2) : '0)
        ##0 hybrid_bf2x2.bf_shares_uvw_i.v00_i[1] == ($past(ntt_top.gs_mode && ntt_top.masking_en_ctrl,2) || $past((ntt_top.pwm_mode || ntt_top.pairwm_mode) && pi_accumulate,2) ? $past(pi_mem_rd_data[(8*REG_SIZE)-3:6*REG_SIZE],2) : '0)
        ##0 hybrid_bf2x2.bf_shares_uvw_i.u01_i[0] == ($past(ntt_top.gs_mode && ntt_top.masking_en_ctrl,2) || $past((ntt_top.pwm_mode || ntt_top.pairwm_mode) && pi_accumulate,2) ? $past(pi_mem_rd_data[(10*REG_SIZE)-3:8*REG_SIZE],2) : '0)
        ##0 hybrid_bf2x2.bf_shares_uvw_i.u01_i[1] == ($past(ntt_top.gs_mode && ntt_top.masking_en_ctrl,2) || $past((ntt_top.pwm_mode || ntt_top.pairwm_mode) && pi_accumulate,2) ? $past(pi_mem_rd_data[(12*REG_SIZE)-3:10*REG_SIZE],2) : '0)
        ##0 hybrid_bf2x2.bf_shares_uvw_i.v01_i[0] == ($past(ntt_top.gs_mode && ntt_top.masking_en_ctrl,2) || $past((ntt_top.pwm_mode || ntt_top.pairwm_mode) && pi_accumulate,2) ? $past(pi_mem_rd_data[(14*REG_SIZE)-3:12*REG_SIZE],2) : '0)
        ##0 hybrid_bf2x2.bf_shares_uvw_i.v01_i[1] == ($past(ntt_top.gs_mode && ntt_top.masking_en_ctrl,2) || $past((ntt_top.pwm_mode || ntt_top.pairwm_mode) && pi_accumulate,2) ? $past(pi_mem_rd_data[(16*REG_SIZE)-3:14*REG_SIZE],2) : '0)
        ##0 hybrid_bf2x2.bf_shares_uvw_i.w00_i[0] == (pi_shuffle_en ? $past(MASKED_WIDTH'(w_rom.rdata[NTT_REG_SIZE-1:0])) - $past(pi_rnd_i[2]):$past(MASKED_WIDTH'(w_rom.rdata[NTT_REG_SIZE-1:0]),2) - $past(pi_rnd_i[2],2))
        ##0 hybrid_bf2x2.bf_shares_uvw_i.w00_i[1] == (pi_shuffle_en? $past(pi_rnd_i[2]):$past(pi_rnd_i[2],2))
        ##0 hybrid_bf2x2.bf_shares_uvw_i.w01_i[0] == (pi_shuffle_en? $past(MASKED_WIDTH'(w_rom.rdata[(2*NTT_REG_SIZE)-1:NTT_REG_SIZE])) - $past(pi_rnd_i[3]):$past(MASKED_WIDTH'(w_rom.rdata[(2*NTT_REG_SIZE)-1:NTT_REG_SIZE]),2) - $past(pi_rnd_i[3],2))
        ##0 hybrid_bf2x2.bf_shares_uvw_i.w01_i[1] == (pi_shuffle_en? $past(pi_rnd_i[3]):$past(pi_rnd_i[3],2))
        ##0 hybrid_bf2x2.bf_shares_uvw_i.w10_i == $past(hybrid_bf2x2.uvw_i.w10_i) 
        ##0 hybrid_bf2x2.bf_shares_uvw_i.w11_i == $past(hybrid_bf2x2.uvw_i.w11_i)
    ;endproperty
    assert_check_bf_shares_in_gs_masking: assert property (check_bf_shares_in_gs_masking);

    // Asserion to check input to the butterfly unit the bf_shares used in gs mode with no masking enable
    property check_bf_shares_in_gs_no_masking; //line 767 no changes
        disable iff (!pi_reset_n || pi_zeroize)
        ##0 ntt_top.ntt_ctrl_aip_i.fv_constraints_i.fv_ongoing
        ##0 (pi_mode == gs) && !ntt_ctrl_inst0.masking_en_ctrl
        |->
        ##0 hybrid_bf2x2.bf_shares_uvw_i == '0
    ;endproperty
    assert_check_bf_shares_in_gs_no_masking: assert property (check_bf_shares_in_gs_no_masking);

    ///////////////////////////////////////
    ///  Shuffle Buffer connectivity checks
    ///////////////////////////////////////
    assert_correct_buffer_input_shuffle_en: assert property(check_connectivity(buffer_inst0.shuffle_en,pi_shuffle_en));
    assert_correct_buffer_input_wren: assert property(check_connectivity(buffer_inst0.wren, ntt_ctrl_inst0.buf_wren));
    assert_correct_buffer_input_rden: assert property(check_connectivity(buffer_inst0.rden, ntt_ctrl_inst0.buf_rden));
    assert_correct_buffer_input_wrptr: assert property(check_connectivity(buffer_inst0.wrptr,ntt_ctrl_inst0.buf_wrptr));
    assert_correct_buffer_input_rdptr: assert property(check_connectivity(buffer_inst0.rdptr,ntt_ctrl_inst0.buf_rdptr));
    assert_correct_buffer_input_wr_rst_count: assert property(check_connectivity(buffer_inst0.wr_rst_count,ntt_ctrl_inst0.buf_wr_rst_count));


    logic [(4*REG_SIZE)-1:0] fv_buf_data_in;

    always_comb begin //line 654, no changes
        if(pi_mode == ct)
            fv_buf_data_in = pi_mem_rd_data;
        else if(pi_shuffle_en)
             fv_buf_data_in = $past({1'b0, hybrid_bf2x2.uv_o.v21_o, 1'b0, hybrid_bf2x2.uv_o.v20_o, 1'b0, hybrid_bf2x2.uv_o.u21_o, 1'b0, hybrid_bf2x2.uv_o.u20_o});
        else 
            fv_buf_data_in = {1'b0, hybrid_bf2x2.uv_o.v21_o, 1'b0, hybrid_bf2x2.uv_o.v20_o, 1'b0, hybrid_bf2x2.uv_o.u21_o, 1'b0, hybrid_bf2x2.uv_o.u20_o};
    end
    //Care about the data, once we move to busy 
    assert_correct_buffer_input_data_i: assert property(po_ntt_busy |-> check_connectivity(buffer_inst0.data_i,fv_buf_data_in));

    // -----------------------------------------------
    // Assertion for hybrid_pw_uvw_i Aggregation
    // -----------------------------------------------
    property check_hybrid_pw_uvw_aggregation;
    disable iff (!pi_reset_n || pi_zeroize)
        (ntt_top.hybrid_pw_uvw_i == {ntt_top.pw_uvw_i, ntt_top.uvw_i.w00_i, ntt_top.uvw_i.w01_i, ntt_top.uvw_i.w10_i, ntt_top.uvw_i.w11_i});
    endproperty
    assert_check_hybrid_pw_uvw_aggregation: assert property (check_hybrid_pw_uvw_aggregation);


endmodule

