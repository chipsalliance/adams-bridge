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
        input                            pi_mlkem,
        input [5:0]                      pi_random,
        input mem_if_t                   po_mem_wr_req,
        input mem_if_t                   po_mem_rd_req,
        input logic [ABR_MEM_DATA_WIDTH-1:0] po_mem_wr_data,
        input [ABR_MEM_DATA_WIDTH-1:0]       pi_mem_rd_data,
        input                            pi_mem_rd_data_valid,
        input mem_if_t                   po_pwm_a_rd_req,
        input mem_if_t                   po_pwm_b_rd_req,
        input [ABR_MEM_DATA_WIDTH-1:0]       pi_pwm_a_rd_data,
        input [ABR_MEM_DATA_WIDTH-1:0]       pi_pwm_b_rd_data,
        input logic                      po_ntt_busy,
        input logic                      po_ntt_done
        //$#//
    );
        default clocking default_clk @(posedge pi_clk); endclocking

        sequence reset_sequence;
            !pi_reset_n ##1 pi_reset_n;
        endsequence

        //Connectivy property
        property check_connectivity(source, sink);
            source == sink
        ;endproperty


        /////////////////
        /// CMD CTRL input
        ////////////////
        // Verifies each ntt_ctrl_inst0 control input is driven by the correct primary input or
        // sibling submodule output.
        assert_correct_cmd_ctrl_input_ntt_mode: assert property(
          check_connectivity(ntt_ctrl_inst0.ntt_mode, pi_mode));
        assert_correct_cmd_ctrl_input_ntt_enable: assert property(
          check_connectivity(ntt_ctrl_inst0.ntt_enable, pi_ntt_enable));
        assert_correct_cmd_ctrl_input_butterfly_ready: assert property(
          check_connectivity(ntt_ctrl_inst0.butterfly_ready, hybrid_bf2x2.ready_o));
        assert_correct_cmd_ctrl_input_buf0_valid: assert property(
          check_connectivity(ntt_ctrl_inst0.buf0_valid, buffer_inst0.buf_valid));
        assert_correct_cmd_ctrl_input_sampler_valid: assert property(
          check_connectivity(ntt_ctrl_inst0.sampler_valid, pi_sampler_valid));
        assert_correct_cmd_ctrl_input_accumulate: assert property(
          check_connectivity(ntt_ctrl_inst0.accumulate, pi_accumulate));
        assert_correct_cmd_ctrl_input_ntt_mem_base_addr: assert property(
          check_connectivity(ntt_ctrl_inst0.ntt_mem_base_addr, pi_ntt_mem_base_addr));
        assert_correct_cmd_ctrl_input_pwo_mem_base_addr: assert property(
          check_connectivity(ntt_ctrl_inst0.pwo_mem_base_addr, pi_pwo_mem_base_addr));
        assert_correct_cmd_ctrl_input_shuffle_en: assert property(
          check_connectivity(ntt_ctrl_inst0.shuffle_en, pi_shuffle_en));
        assert_correct_cmd_ctrl_input_random: assert property(
          check_connectivity(ntt_ctrl_inst0.random, pi_random));
        assert_correct_cmd_ctrl_input_mlkem: assert property(
          check_connectivity(ntt_ctrl_inst0.mlkem, pi_mlkem));
        assert_correct_cmd_ctrl_input_mem_rd_data_valid: assert property(
          check_connectivity(ntt_ctrl_inst0.mem_rd_data_valid, pi_mem_rd_data_valid));

        /////////////////
        /// Twiddle ROM input
        ////////////////
        // verifies w_rom.raddr (the ROM's own address input) is driven by
        // ntt_ctrl_inst0.twiddle_addr.
        assert_correct_twiddle_rom_input_addr: assert property(
          check_connectivity(w_rom.raddr, ntt_ctrl_inst0.twiddle_addr));
        // Verifies w_rom.mode/w_rom.mlkem are driven by the top-level pi_mode/pi_mlkem ports.
        assert_correct_twiddle_rom_input_mode: assert property(
          check_connectivity(w_rom.mode, pi_mode));
        assert_correct_twiddle_rom_input_mlkem: assert property(
          check_connectivity(w_rom.mlkem, pi_mlkem));

        /////////////////
        /// Butterfly input
        ////////////////
        // Verifies hybrid_bf2x2.mode is driven by ntt_ctrl_inst0.opcode.
        assert_correct_butterfly_input_opcode: assert property(
          check_connectivity(hybrid_bf2x2.mode, ntt_ctrl_inst0.opcode));
        // Verifies hybrid_bf2x2.shuffle_en/mlkem are driven by the top-level
        // pi_shuffle_en/pi_mlkem ports.
        assert_correct_butterfly_input_shuffle_en: assert property(
          check_connectivity(hybrid_bf2x2.shuffle_en, pi_shuffle_en));
        assert_correct_butterfly_input_mlkem: assert property(
          check_connectivity(hybrid_bf2x2.mlkem, pi_mlkem));

         // Verifies hybrid_bf2x2.enable matches bf_enable_mux  same-cycle
        // bf_enable in ct mode, 1-cycle delayed otherwise.
        logic fv_bf_enable_reg;
        always_ff @(posedge pi_clk or negedge pi_reset_n) begin
            if (!pi_reset_n || pi_zeroize) begin
                fv_bf_enable_reg <= 1'b0;
            end
            else begin
                fv_bf_enable_reg <= ntt_ctrl_inst0.bf_enable;
            end
        end

        logic fv_bf_enable;
        always_comb begin
            fv_bf_enable = (pi_mode == ct) ? ntt_ctrl_inst0.bf_enable : fv_bf_enable_reg;
        end

        assert_correct_butterfly_input_enable_bf: assert property(
            disable iff(!pi_reset_n || pi_zeroize ||
              !ntt_top.ntt_ctrl_aip_i.fv_constraints_i.fv_ongoing)
            check_connectivity(hybrid_bf2x2.enable, fv_bf_enable)
        );


        // Verifies hybrid_bf2x2.accumulate is driven by ntt_ctrl_inst0.accumulate.
        assert_correct_butterfly_input_accumulate: assert property(
          check_connectivity(hybrid_bf2x2.accumulate, ntt_ctrl_inst0.accumulate));
        // Verifies hybrid_bf2x2.ntt_passthrough/intt_passthrough are driven by the matching
        // ntt_ctrl_inst0 outputs.
        assert_correct_butterfly_input_ntt_passthrough: assert property(
          check_connectivity(hybrid_bf2x2.ntt_passthrough, ntt_ctrl_inst0.ntt_passthrough));
        assert_correct_butterfly_input_intt_passthrough: assert property(
          check_connectivity(hybrid_bf2x2.intt_passthrough, ntt_ctrl_inst0.intt_passthrough));


        //UVW_I: Shuffling
        // Verifies hybrid_bf2x2.uvw_i.w00_i/w01_i/w10_i/w11_i are loaded from w_rom.rdata (sized
        // per mlkem) in ct mode.
        property pi_mode_ct_assignment; //added mlkem case: line 378
            disable iff (!pi_reset_n || pi_zeroize)
            (pi_mode == ct)
        |->
            (
                hybrid_bf2x2.uvw_i.w00_i == (pi_mlkem ? {12'h0, w_rom.rdata[MLKEM_REG_SIZE-1:0]} :
                  w_rom.rdata[NTT_REG_SIZE-1:0]) &&
                hybrid_bf2x2.uvw_i.w01_i == (pi_mlkem ? {12'h0, w_rom.rdata[MLKEM_REG_SIZE-1:0]} :
                  w_rom.rdata[NTT_REG_SIZE-1:0]) &&
                hybrid_bf2x2.uvw_i.w10_i == (pi_mlkem ? {12'h0,
                  w_rom.rdata[(2*MLKEM_REG_SIZE)-1:MLKEM_REG_SIZE]} :
                  w_rom.rdata[(2*NTT_REG_SIZE)-1:NTT_REG_SIZE]) &&
                hybrid_bf2x2.uvw_i.w11_i == (pi_mlkem ? {12'h0,
                  w_rom.rdata[(3*MLKEM_REG_SIZE)-1:(2*MLKEM_REG_SIZE)]} :
                  w_rom.rdata[(3*NTT_REG_SIZE)-1:(2*NTT_REG_SIZE)])
            );
        endproperty
        assert_pi_mode_ct_assignment: assert property (pi_mode_ct_assignment);

        // Verifies hybrid_bf2x2.uvw_i.w*_i are loaded from the current-cycle w_rom.rdata in gs
        // mode with shuffling enabled.
        property pi_mode_gs_pwm_intt_shuffle; //added mlkem case: line 385
            disable iff (!pi_reset_n || pi_zeroize )
            ##0 ntt_top.ntt_ctrl_aip_i.fv_constraints_i.fv_ongoing
            ##0 (pi_mode == gs) && pi_shuffle_en
        |->
            (
                hybrid_bf2x2.uvw_i.w11_i == (pi_mlkem ? {12'h0,
                  w_rom.rdata[(3*MLKEM_REG_SIZE)-1:(2*MLKEM_REG_SIZE)]} :
                  w_rom.rdata[(3*NTT_REG_SIZE)-1:(2*NTT_REG_SIZE)]) &&
                hybrid_bf2x2.uvw_i.w10_i == (pi_mlkem ? {12'h0,
                  w_rom.rdata[(3*MLKEM_REG_SIZE)-1:(2*MLKEM_REG_SIZE)]} :
                  w_rom.rdata[(3*NTT_REG_SIZE)-1:(2*NTT_REG_SIZE)]) &&
                hybrid_bf2x2.uvw_i.w01_i == (pi_mlkem ? {12'h0,
                  w_rom.rdata[(2*MLKEM_REG_SIZE)-1:MLKEM_REG_SIZE]} :
                  w_rom.rdata[(2*NTT_REG_SIZE)-1:NTT_REG_SIZE]) &&
                hybrid_bf2x2.uvw_i.w00_i == (pi_mlkem ? {12'h0, w_rom.rdata[MLKEM_REG_SIZE-1:0]} :
                  w_rom.rdata[NTT_REG_SIZE-1:0])
            );
        endproperty
        assert_pi_mode_gs_pwm_intt_shuffle: assert property (pi_mode_gs_pwm_intt_shuffle);

        // Verifies hybrid_bf2x2.uvw_i.w*_i are loaded from the prior-cycle w_rom.rdata in gs mode
        // with shuffling disabled.
        property pi_mode_gs_pwm_intt_no_shuffle; //line 391 added mlkem case
            disable iff (!pi_reset_n || pi_zeroize )
            ##0 ntt_top.ntt_ctrl_aip_i.fv_constraints_i.fv_ongoing
            ##0 (pi_mode == gs ) &&
            !pi_shuffle_en
        |->
            (
                hybrid_bf2x2.uvw_i.w10_i == (pi_mlkem ? {12'h0,
                  $past(w_rom.rdata[(3*MLKEM_REG_SIZE)-1:(2*MLKEM_REG_SIZE)])} :
                  $past(w_rom.rdata[(3*NTT_REG_SIZE)-1:(2*NTT_REG_SIZE)])) &&
                hybrid_bf2x2.uvw_i.w11_i == (pi_mlkem ? {12'h0,
                  $past(w_rom.rdata[(3*MLKEM_REG_SIZE)-1:(2*MLKEM_REG_SIZE)])} :
                  $past(w_rom.rdata[(3*NTT_REG_SIZE)-1:(2*NTT_REG_SIZE)])) &&
                hybrid_bf2x2.uvw_i.w01_i == (pi_mlkem ? {12'h0,
                  $past(w_rom.rdata[(2*MLKEM_REG_SIZE)-1:MLKEM_REG_SIZE])} :
                  $past(w_rom.rdata[(2*NTT_REG_SIZE)-1:NTT_REG_SIZE])) &&
                hybrid_bf2x2.uvw_i.w00_i == (pi_mlkem ? {12'h0,
                  $past(w_rom.rdata[MLKEM_REG_SIZE-1:0])} : $past(w_rom.rdata[NTT_REG_SIZE-1:0]))
            );
        endproperty
        assert_pi_mode_gs_pwm_intt_no_shuffle:assert property (pi_mode_gs_pwm_intt_no_shuffle);

        // Verifies hybrid_bf2x2.uvw_i.w*_i are zeroed in all modes other than ct/gs.
        property pi_mode_default_assignment;
            disable iff (!pi_reset_n || pi_zeroize)
            (pi_mode != ct && pi_mode != gs)
        |-> (
                hybrid_bf2x2.uvw_i.w11_i == 'h0 &&
                hybrid_bf2x2.uvw_i.w10_i == 'h0 &&
                hybrid_bf2x2.uvw_i.w01_i == 'h0 &&
                hybrid_bf2x2.uvw_i.w00_i == 'h0
            );
        endproperty
        assert_pi_mode_default_assignment: assert property (pi_mode_default_assignment);

        // Verifies hybrid_bf2x2.mlkem_pairwm_zeta13_i.z0_i/z1_i are loaded from the prior-cycle
        // w_rom.rdata in pairwm mode.
        property mlkem_pairwm_zeta;
        ntt_top.ntt_ctrl_aip_i.fv_constraints_i.fv_ongoing
        ##0 ntt_top.pairwm_mode
        |->
        hybrid_bf2x2.mlkem_pairwm_zeta13_i.z0_i ==
          $past(w_rom.rdata[(2*MLKEM_REG_SIZE)-1:MLKEM_REG_SIZE]) &&
        hybrid_bf2x2.mlkem_pairwm_zeta13_i.z1_i ==
          $past(w_rom.rdata[(3*MLKEM_REG_SIZE)-1:(2*MLKEM_REG_SIZE)])
        ;
        endproperty
        assert_mlkem_pairwm_zeta: assert property(
          disable iff (!pi_reset_n || pi_zeroize) mlkem_pairwm_zeta);

        // Verifies hybrid_bf2x2.mlkem_pairwm_zeta13_i.z0_i/z1_i are zero when not in pairwm mode.
        property no_mlkem_pairwm_zeta;
        ntt_top.ntt_ctrl_aip_i.fv_constraints_i.fv_ongoing
        ##0 !ntt_top.pairwm_mode
        |->
        hybrid_bf2x2.mlkem_pairwm_zeta13_i.z0_i == 0 &&
        hybrid_bf2x2.mlkem_pairwm_zeta13_i.z1_i == 0
        ;
        endproperty
        assert_no_mlkem_pairwm_zeta: assert property(
          disable iff (!pi_reset_n || pi_zeroize) no_mlkem_pairwm_zeta);

        // -----------------------------------------------
        // Assertions for uvw_i Assignments (Struct)
        // -----------------------------------------------
        // Verifies hybrid_bf2x2.uvw_i.u/v fields are loaded from buffer_inst0.data_o, and
        // pw_uvw_i is zero, in ct mode.
        property check_uvw_assignment_ct;
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

        // Verifies hybrid_bf2x2.uvw_i.u/v fields are loaded from the prior-cycle pi_mem_rd_data,
        // and pw_uvw_i is zero, in gs mode.
        property check_uvw_assignment_gs;
            disable iff (!pi_reset_n || pi_zeroize )
            ##0 (ntt_top.ntt_ctrl_aip_i.fv_constraints_i.fv_ongoing)
            ##0 (pi_mode == gs)
        |->
            (hybrid_bf2x2.uvw_i.u00_i == $past(pi_mem_rd_data[REG_SIZE-2:0]) &&
            hybrid_bf2x2.uvw_i.u01_i == $past(pi_mem_rd_data[(3*REG_SIZE)-2:(2*REG_SIZE)]) &&
            hybrid_bf2x2.uvw_i.v00_i == $past(pi_mem_rd_data[(2*REG_SIZE)-2:REG_SIZE]) &&
            hybrid_bf2x2.uvw_i.v01_i == $past(pi_mem_rd_data[(4*REG_SIZE)-2:(3*REG_SIZE)]) &&
            hybrid_bf2x2.pw_uvw_i == '0 );
        endproperty
        assert_check_uvw_assignment_gs: assert property (check_uvw_assignment_gs);

        // -----------------------------------------------
        // Assertions for pw_uvw_i Assignments (Struct) in pwo mode
        // -----------------------------------------------
        // Verifies hybrid_bf2x2.pw_uvw_i.u/v/w fields are loaded from ntt_top.pwm_rd_data_a/b/c,
        // and uvw_i is zero, in pwm/pairwm mode.
        property check_pw_uvw_assignment_pwm;
            disable iff (!pi_reset_n || pi_zeroize)
            ##0 (ntt_top.ntt_ctrl_aip_i.fv_constraints_i.fv_ongoing)
            ##0 (pi_mode == pwm || pi_mode == pairwm)
        |->
            (hybrid_bf2x2.pw_uvw_i.u0_i == $past(ntt_top.pwm_rd_data_a[REG_SIZE-2:0]) &&
            hybrid_bf2x2.pw_uvw_i.u1_i == $past(ntt_top.pwm_rd_data_a[(2*REG_SIZE)-2:REG_SIZE]) &&
            hybrid_bf2x2.pw_uvw_i.u2_i ==
              $past(ntt_top.pwm_rd_data_a[(3*REG_SIZE)-2:(2*REG_SIZE)]) &&
            hybrid_bf2x2.pw_uvw_i.u3_i ==
              $past(ntt_top.pwm_rd_data_a[(4*REG_SIZE)-2:(3*REG_SIZE)]) &&
            hybrid_bf2x2.pw_uvw_i.v0_i == (pi_shuffle_en ? ntt_top.pwm_rd_data_b[REG_SIZE-2:0] :
              $past(ntt_top.pwm_rd_data_b[REG_SIZE-2:0])) &&
            hybrid_bf2x2.pw_uvw_i.v1_i == (pi_shuffle_en ?
              ntt_top.pwm_rd_data_b[(2*REG_SIZE)-2:REG_SIZE] :
              $past(ntt_top.pwm_rd_data_b[(2*REG_SIZE)-2:REG_SIZE])) &&
            hybrid_bf2x2.pw_uvw_i.v2_i == (pi_shuffle_en ?
              ntt_top.pwm_rd_data_b[(3*REG_SIZE)-2:(2*REG_SIZE)] :
              $past(ntt_top.pwm_rd_data_b[(3*REG_SIZE)-2:(2*REG_SIZE)])) &&
            hybrid_bf2x2.pw_uvw_i.v3_i == (pi_shuffle_en ?
              ntt_top.pwm_rd_data_b[(4*REG_SIZE)-2:(3*REG_SIZE)] :
              $past(ntt_top.pwm_rd_data_b[(4*REG_SIZE)-2:(3*REG_SIZE)])) &&
            hybrid_bf2x2.pw_uvw_i.w0_i == $past(ntt_top.pwm_rd_data_c[REG_SIZE-2:0]) &&
            hybrid_bf2x2.pw_uvw_i.w1_i == $past(ntt_top.pwm_rd_data_c[(2*REG_SIZE)-2:REG_SIZE]) &&
            hybrid_bf2x2.pw_uvw_i.w2_i ==
              $past(ntt_top.pwm_rd_data_c[(3*REG_SIZE)-2:(2*REG_SIZE)]) &&
            hybrid_bf2x2.pw_uvw_i.w3_i ==
              $past(ntt_top.pwm_rd_data_c[(4*REG_SIZE)-2:(3*REG_SIZE)]) &&
            hybrid_bf2x2.uvw_i == '0 );
        endproperty
        assert_check_pw_uvw_assignment_pwm: assert property (check_pw_uvw_assignment_pwm);


        // Verifies hybrid_bf2x2.pw_uvw_i.u/v fields are loaded from ntt_top.pwm_rd_data_a/b, w
        // fields and uvw_i are zero, in pwa/pws mode.
        property check_pw_uvw_assignment_pwa_pws;
            disable iff (!pi_reset_n || pi_zeroize)
            ##0 (ntt_top.ntt_ctrl_aip_i.fv_constraints_i.fv_ongoing)
            ##0 (pi_mode == pwa || pi_mode == pws)
        |->
            (hybrid_bf2x2.pw_uvw_i.u0_i == $past(ntt_top.pwm_rd_data_a[REG_SIZE-2:0]) &&
            hybrid_bf2x2.pw_uvw_i.u1_i == $past(ntt_top.pwm_rd_data_a[(2*REG_SIZE)-2:REG_SIZE]) &&
            hybrid_bf2x2.pw_uvw_i.u2_i ==
              $past(ntt_top.pwm_rd_data_a[(3*REG_SIZE)-2:(2*REG_SIZE)]) &&
            hybrid_bf2x2.pw_uvw_i.u3_i ==
              $past(ntt_top.pwm_rd_data_a[(4*REG_SIZE)-2:(3*REG_SIZE)]) &&
            hybrid_bf2x2.pw_uvw_i.v0_i == (pi_shuffle_en ? ntt_top.pwm_rd_data_b[REG_SIZE-2:0] :
              $past(ntt_top.pwm_rd_data_b[REG_SIZE-2:0])) &&
            hybrid_bf2x2.pw_uvw_i.v1_i == (pi_shuffle_en ?
              ntt_top.pwm_rd_data_b[(2*REG_SIZE)-2:REG_SIZE] :
              $past(ntt_top.pwm_rd_data_b[(2*REG_SIZE)-2:REG_SIZE])) &&
            hybrid_bf2x2.pw_uvw_i.v2_i == (pi_shuffle_en ?
              ntt_top.pwm_rd_data_b[(3*REG_SIZE)-2:(2*REG_SIZE)] :
              $past(ntt_top.pwm_rd_data_b[(3*REG_SIZE)-2:(2*REG_SIZE)])) &&
            hybrid_bf2x2.pw_uvw_i.v3_i == (pi_shuffle_en ?
              ntt_top.pwm_rd_data_b[(4*REG_SIZE)-2:(3*REG_SIZE)] :
              $past(ntt_top.pwm_rd_data_b[(4*REG_SIZE)-2:(3*REG_SIZE)])) &&
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
        // Verifies hybrid_bf2x2.uvw_i.u00_i/u01_i/v00_i/v01_i are zero in modes other than
        // ct/gs/pwm/pwa/pws/pairwm.
        property check_zero_uvw_default;
            disable iff (!pi_reset_n || pi_zeroize)
            ##0 ntt_top.ntt_ctrl_aip_i.fv_constraints_i.fv_ongoing
            ##0 (pi_mode != ct && pi_mode != gs && pi_mode != pwm  && pi_mode != pwa && pi_mode !=
              pws && pi_mode != pairwm)

        |->
            (hybrid_bf2x2.uvw_i.u00_i == 'h0 &&
            hybrid_bf2x2.uvw_i.u01_i == 'h0 &&
            hybrid_bf2x2.uvw_i.v00_i == 'h0 &&
            hybrid_bf2x2.uvw_i.v01_i == 'h0);
        endproperty
        assert_check_zero_uvw_default: assert property (check_zero_uvw_default);

        // Verifies all hybrid_bf2x2.pw_uvw_i u/v/w fields are zero in modes other than
        // ct/gs/pwm/pwa/pws/pairwm.
        property check_zero_pw_uvw_default;
            disable iff (!pi_reset_n || pi_zeroize)
            ##0 ntt_top.ntt_ctrl_aip_i.fv_constraints_i.fv_ongoing &&
            (pi_mode != ct && pi_mode != gs && pi_mode != pwm && pi_mode != pwa && pi_mode != pws
              && pi_mode != pairwm)
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

        // Property to check pw_rden_reg/pw_mem_rd_addr_a_reg/pw_mem_rd_addr_b_reg/w10_reg/w11_reg
        // reset to 0
        property check_pwo_regs_reset;
            $past(!pi_reset_n || pi_zeroize)
        |->
            (ntt_top.pw_rden_reg == '0 &&
            ntt_top.pw_mem_rd_addr_a_reg == '0 &&
            ntt_top.pw_mem_rd_addr_b_reg == '0 &&
            ntt_top.w10_reg == '0 &&
            ntt_top.w11_reg == '0);
        endproperty
        assert_check_pwo_regs_reset: assert property (check_pwo_regs_reset);


        ///////////////////////////////////////
        ///  Shuffle Buffer connectivity checks
        ///////////////////////////////////////
        // Verifies buffer_inst0.mode is driven by the top-level pi_mode port.
        assert_correct_buffer_input_mode: assert property(
          check_connectivity(buffer_inst0.mode, pi_mode));
        assert_correct_buffer_input_shuffle_en: assert property(
          check_connectivity(buffer_inst0.shuffle_en, pi_shuffle_en));
        assert_correct_buffer_input_wren: assert property(
          check_connectivity(buffer_inst0.wren, ntt_ctrl_inst0.buf_wren));
        assert_correct_buffer_input_rden: assert property(
          check_connectivity(buffer_inst0.rden, ntt_ctrl_inst0.buf_rden));
        assert_correct_buffer_input_wrptr: assert property(
          check_connectivity(buffer_inst0.wrptr, ntt_ctrl_inst0.buf_wrptr));
        assert_correct_buffer_input_rdptr: assert property(
          check_connectivity(buffer_inst0.rdptr, ntt_ctrl_inst0.buf_rdptr));
        assert_correct_buffer_input_wr_rst_count: assert property(
          check_connectivity(buffer_inst0.wr_rst_count, ntt_ctrl_inst0.buf_wr_rst_count));


        logic [(4*REG_SIZE)-1:0] fv_buf_data_in;

        always_comb begin //line 654, no changes
            if(pi_mode == ct) begin
                fv_buf_data_in = pi_mem_rd_data;
            end else if(pi_shuffle_en) begin
                fv_buf_data_in = $past({1'b0, hybrid_bf2x2.uv_o.v21_o, 1'b0,
                  hybrid_bf2x2.uv_o.v20_o, 1'b0, hybrid_bf2x2.uv_o.u21_o, 1'b0,
                  hybrid_bf2x2.uv_o.u20_o});
            end else begin
                fv_buf_data_in = {1'b0, hybrid_bf2x2.uv_o.v21_o, 1'b0, hybrid_bf2x2.uv_o.v20_o,
                  1'b0, hybrid_bf2x2.uv_o.u21_o, 1'b0, hybrid_bf2x2.uv_o.u20_o};
            end
        end
        // Verifies buffer_inst0.data_i, once po_ntt_busy is asserted, matches the expected
        // memory/butterfly-output source per mode/shuffle_en.
        property buffer_input_data_i;
          po_ntt_busy
        |->
          check_connectivity(buffer_inst0.data_i, fv_buf_data_in)
        ;endproperty
        assert_correct_buffer_input_data_i: assert property(buffer_input_data_i);

        ///////////////////////////////////////
        ///  Shuffle buffer transit correctness
        ///////////////////////////////////////
        // verifies a coefficient written via data_i lands in buffer_inst0.buffer at the matching
        // (lo_hi, wrptr) cell.
        property check_buf_array_write;
            disable iff (!pi_reset_n || pi_zeroize)
            buffer_inst0.wren
        |=>
            buffer_inst0.buffer[$past(buffer_inst0.lo_hi)][$past(buffer_inst0.wrptr)] ==
              $past(buffer_inst0.data_i)
        ;endproperty
        assert_check_buf_array_write: assert property (check_buf_array_write);

        //  verifies buffer_inst0.data_o reproduces the buffer cells selected by lo_hi_rd/rdptr.
        property check_buf_array_read;
            disable iff (!pi_reset_n || pi_zeroize)
            buffer_inst0.data_o == (buffer_inst0.lo_hi_rd ?
                {buffer_inst0.buffer[0][3][buffer_inst0.rdptr],
                  buffer_inst0.buffer[0][2][buffer_inst0.rdptr],
                buffer_inst0.buffer[0][1][buffer_inst0.rdptr],
                  buffer_inst0.buffer[0][0][buffer_inst0.rdptr]} :
                {buffer_inst0.buffer[1][3][buffer_inst0.rdptr],
                  buffer_inst0.buffer[1][2][buffer_inst0.rdptr],
                buffer_inst0.buffer[1][1][buffer_inst0.rdptr],
                  buffer_inst0.buffer[1][0][buffer_inst0.rdptr]})
        ;endproperty
        assert_check_buf_array_read: assert property (check_buf_array_read);

    endmodule

