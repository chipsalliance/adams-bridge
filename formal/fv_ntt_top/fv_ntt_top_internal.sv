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


module fv_ntt_top_internal
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
    //Connectivy property
    property check_connectivity(source,sink);
        source == sink
    ;endproperty
    /////////////////
    /// CMD CTRL input
    ////////////////

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


    /////////////////
    /// Butterfly input
    ////////////////
    assert_correct_butterfly_input_opoce: assert property(check_connectivity(hybrid_bf2x2.mode,ntt_ctrl_inst0.opcode));

    logic fv_bf_enable;
    assign fv_bf_enable = (pi_mode == ct) ? ntt_ctrl_inst0.bf_enable : $past(ntt_ctrl_inst0.bf_enable); 

    assert_correct_butterfly_input_enable_bf: assert property(
        disable iff(!pi_reset_n || pi_zeroize || !ntt_top.ntt_ctrl_aip_i.fv_constraints_i.fv_ongoing)
    check_connectivity(hybrid_bf2x2.enable,fv_bf_enable));

    assert_correct_butterfly_input_masking: assert property(check_connectivity(hybrid_bf2x2.masking_en,pi_masking_en));

    
    
    
    //UVW_I: Shuffeling

    property pi_mode_ct_assignment;
        disable iff (!pi_reset_n || pi_zeroize)
        (pi_mode == ct) |-> (
            hybrid_bf2x2.uvw_i.w00_i == w_rom.rdata[NTT_REG_SIZE-1:0] &&
            hybrid_bf2x2.uvw_i.w01_i == w_rom.rdata[NTT_REG_SIZE-1:0] &&
            hybrid_bf2x2.uvw_i.w10_i == w_rom.rdata[(2*NTT_REG_SIZE)-1:NTT_REG_SIZE] &&
            hybrid_bf2x2.uvw_i.w11_i == w_rom.rdata[(3*NTT_REG_SIZE)-1:(2*NTT_REG_SIZE)]
        );
    endproperty
    assert_pi_mode_ct_assignment: assert property (pi_mode_ct_assignment);

    property pi_mode_gs_pwm_intt_shuffle;
        disable iff (!pi_reset_n || pi_zeroize )
        ##0 ntt_top.ntt_ctrl_aip_i.fv_constraints_i.fv_ongoing
        ##0 (pi_mode == gs || pi_mode == pwm_intt) && pi_shuffle_en 
        |-> 
        (
            hybrid_bf2x2.uvw_i.w11_i == w_rom.rdata[(3*NTT_REG_SIZE)-1:(2*NTT_REG_SIZE)] &&
            hybrid_bf2x2.uvw_i.w10_i == w_rom.rdata[(3*NTT_REG_SIZE)-1:(2*NTT_REG_SIZE)] &&
            hybrid_bf2x2.uvw_i.w01_i == w_rom.rdata[(2*NTT_REG_SIZE)-1:NTT_REG_SIZE] &&
            hybrid_bf2x2.uvw_i.w00_i == w_rom.rdata[NTT_REG_SIZE-1:0]
        );
    endproperty
    assert_pi_mode_gs_pwm_intt_shuffle: assert property (pi_mode_gs_pwm_intt_shuffle);

    property pi_mode_gs_pwm_intt_no_shuffle;
        disable iff (!pi_reset_n || pi_zeroize )
        ##0 ntt_top.ntt_ctrl_aip_i.fv_constraints_i.fv_ongoing
        ##0 (pi_mode == gs || pi_mode == pwm_intt) && 
        !pi_shuffle_en  
        |-> 
        (
            hybrid_bf2x2.uvw_i.w10_i == $past(w_rom.rdata[(3*NTT_REG_SIZE)-1:(2*NTT_REG_SIZE)]) &&
            hybrid_bf2x2.uvw_i.w11_i == $past(w_rom.rdata[(3*NTT_REG_SIZE)-1:(2*NTT_REG_SIZE)]) &&
            hybrid_bf2x2.uvw_i.w01_i == $past(w_rom.rdata[(2*NTT_REG_SIZE)-1:NTT_REG_SIZE]) &&
            hybrid_bf2x2.uvw_i.w00_i == $past(w_rom.rdata[NTT_REG_SIZE-1:0])
        );
    endproperty
    assert_pi_mode_gs_pwm_intt_no_shuffle:assert property (pi_mode_gs_pwm_intt_no_shuffle);

    property pi_mode_default_assignment;
        disable iff (!pi_reset_n || pi_zeroize)
        (pi_mode != ct && pi_mode != gs && pi_mode != pwm_intt) |-> (
            hybrid_bf2x2.uvw_i.w11_i == 'h0 &&
            hybrid_bf2x2.uvw_i.w10_i == 'h0 &&
            hybrid_bf2x2.uvw_i.w01_i == 'h0 &&
            hybrid_bf2x2.uvw_i.w00_i == 'h0
        );
    endproperty
    assert_pi_mode_default_assignment: assert property (pi_mode_default_assignment);

    assert_correct_butterfly_input_rnd_i: assert property(check_connectivity(hybrid_bf2x2.rnd_i,pi_rnd_i));
    assert_correct_butterfly_input_accumulate: assert property(check_connectivity(hybrid_bf2x2.accumulate,ntt_ctrl_inst0.accumulate));


    // pwm_b_rd_data_reg
    property check_pwm_b_rd_data_reg;
        disable iff (!pi_reset_n || pi_zeroize)
        ##1
        (ntt_top.pwm_b_rd_data_reg == $past(ntt_top.pwm_b_rd_data));
    endproperty
    assert_check_pwm_b_rd_data_reg: assert property (check_pwm_b_rd_data_reg);

    property check_pwm_b_rd_data_reg_reset;
       (!pi_reset_n || pi_zeroize)
       |=>
      (ntt_top.pwm_b_rd_data_reg == '0);
    endproperty
    assert_check_pwm_b_rd_data_reg_reset: assert property (check_pwm_b_rd_data_reg_reset);
    // -----------------------------------------------
    // Assertions for uvw_i Assignments (Struct)
    // -----------------------------------------------
    property check_uvw_assignment_ct;
        disable iff (!pi_reset_n || pi_zeroize )

        ##0 (pi_mode == ct) 
        ##0 (ntt_top.ntt_ctrl_aip_i.fv_constraints_i.fv_ongoing)
    |-> 
        (hybrid_bf2x2.uvw_i.u00_i == buffer_inst0.data_o[REG_SIZE-2:0] &&
        hybrid_bf2x2.uvw_i.u01_i == buffer_inst0.data_o[(2*REG_SIZE)-2:REG_SIZE] &&
        hybrid_bf2x2.uvw_i.v00_i == buffer_inst0.data_o[(3*REG_SIZE)-2:(2*REG_SIZE)] &&
        hybrid_bf2x2.uvw_i.v01_i == buffer_inst0.data_o[(4*REG_SIZE)-2:(3*REG_SIZE)]);
    endproperty
    assert_check_uvw_assignment_ct: assert property (check_uvw_assignment_ct);

    property check_uvw_assignment_gs;
        disable iff (!pi_reset_n || pi_zeroize )
        ##0 (ntt_top.ntt_ctrl_aip_i.fv_constraints_i.fv_ongoing)
        ##0 (pi_mode == gs) 
    |-> 
        (hybrid_bf2x2.uvw_i.u00_i == $past(pi_mem_rd_data[REG_SIZE-2:0]) &&
        hybrid_bf2x2.uvw_i.u01_i == $past(pi_mem_rd_data[(3*REG_SIZE)-2:(2*REG_SIZE)]) &&
        hybrid_bf2x2.uvw_i.v00_i == $past(pi_mem_rd_data[(2*REG_SIZE)-2:REG_SIZE]) &&
        hybrid_bf2x2.uvw_i.v01_i == $past(pi_mem_rd_data[(4*REG_SIZE)-2:(3*REG_SIZE)]));
    endproperty
    assert_check_uvw_assignment_gs: assert property (check_uvw_assignment_gs);

    // -----------------------------------------------
    // Assertions for pw_uvw_i Assignments (Struct) in pwm & pwm_intt
    // -----------------------------------------------
    property check_pw_uvw_assignment_pwm;
        disable iff (!pi_reset_n || pi_zeroize)
        ##0 (ntt_top.ntt_ctrl_aip_i.fv_constraints_i.fv_ongoing)
        ##0 (pi_mode == pwm || pi_mode == pwm_intt) 
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
        hybrid_bf2x2.pw_uvw_i.w3_i == $past(ntt_top.pwm_rd_data_c[(4*REG_SIZE)-2:(3*REG_SIZE)]));
    endproperty
    assert_check_pw_uvw_assignment_pwm: assert property (check_pw_uvw_assignment_pwm);

    // -----------------------------------------------
    // Assertions for Default Case (Zeroing Out)
    // -----------------------------------------------
    property check_zero_uvw_default;
        disable iff (!pi_reset_n || pi_zeroize)
        ##0 ntt_top.ntt_ctrl_aip_i.fv_constraints_i.fv_ongoing
        ##0 (pi_mode != ct && pi_mode != gs && pi_mode != pwm && pi_mode != pwm_intt && pi_mode != pwa && pi_mode != pws) 

    |-> 
        (hybrid_bf2x2.uvw_i.u00_i == 'h0 &&
        hybrid_bf2x2.uvw_i.u01_i == 'h0 &&
        hybrid_bf2x2.uvw_i.v00_i == 'h0 &&
        hybrid_bf2x2.uvw_i.v01_i == 'h0);
    endproperty
    assert_check_zero_uvw_default: assert property (check_zero_uvw_default);

    property check_zero_pw_uvw_default;
        disable iff (!pi_reset_n || pi_zeroize)
        
        (pi_mode != ct && pi_mode != gs && pi_mode != pwm && pi_mode != pwm_intt && pi_mode != pwa && pi_mode != pws) 
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



    /////////////////
    ///  Shuffle Buffer
    ////////////////
    
    assert_correct_buffer_input_shuffle_en: assert property(check_connectivity(buffer_inst0.shuffle_en,pi_shuffle_en));
    assert_correct_buffer_input_wren: assert property(check_connectivity(buffer_inst0.wren, ntt_ctrl_inst0.buf_wren));
    assert_correct_buffer_input_rden: assert property(check_connectivity(buffer_inst0.rden, ntt_ctrl_inst0.buf_rden));
    assert_correct_buffer_input_wrptr: assert property(check_connectivity(buffer_inst0.wrptr,ntt_ctrl_inst0.buf_wrptr));
    assert_correct_buffer_input_rdptr: assert property(check_connectivity(buffer_inst0.rdptr,ntt_ctrl_inst0.buf_rdptr));
    assert_correct_buffer_input_wr_rst_count: assert property(check_connectivity(buffer_inst0.wr_rst_count,ntt_ctrl_inst0.buf_wr_rst_count));


    logic [(4*REG_SIZE)-1:0] fv_buf_data_in;

    always_comb begin
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

