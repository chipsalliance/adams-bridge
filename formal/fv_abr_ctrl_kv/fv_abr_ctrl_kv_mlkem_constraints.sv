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


module fv_abr_ctrl_kv_mlkem_constraints
    import abr_params_pkg::*;
    import abr_sampler_pkg::*;
    import abr_ctrl_pkg::*;
    import abr_sha3_pkg::*;
    import abr_reg_pkg::*;
    import ntt_defines_pkg::*;
    import compress_defines_pkg::*;
    import decompress_defines_pkg::*;
    import kv_defines_pkg::*;
#(
     parameter FV_ADAMSBRIDGE_BUSY_CNTR = 2,
     parameter FV_ADAMSBRIDGE_CNTRL_RDY_DELAY = 1,
     parameter FV_ADAMSBRIDGE_AUX_DLY = 2,
    //#$localparams
    localparam ABR_SEQ_NTT = 0
    //$#//

) (
    //#$ports
    input logic                                                 pi_clk,
    input logic                                                 pi_rst_b,
    input logic                                                 po_zeroize,
    input abr_reg__in_t                                         po_abr_reg_hwif_in_o,
    input abr_reg__out_t                                        pi_abr_reg_hwif_out_i,
    input abr_sampler_mode_e                                    po_sampler_mode_o,
    input logic                                                 po_sha3_start_o,
    input logic                                                 po_msg_start_o,
    input logic                                                 po_msg_valid_o,
    input logic                                                 pi_msg_rdy_i,
    input logic [MsgStrbW-1:0]                                  po_msg_strobe_o,
    input logic [MsgWidth-1:0]                                  po_msg_data_o,
    input logic                                                 po_sampler_start_o,
    input logic                                                 pi_sampler_busy_i,
    input logic                                                 pi_sampler_state_dv_i,
    input logic [abr_sha3_pkg::StateW-1:0]                      pi_sampler_state_data_i,
    input logic [ABR_MEM_ADDR_WIDTH-1:0]                        po_dest_base_addr_o,
    input logic                                                 po_ntt_enable_o,
    input abr_ntt_mode_e                                        po_ntt_mode_o,
    input ntt_mem_addr_t                                        po_ntt_mem_base_addr_o,
    input pwo_mem_addr_t                                        po_pwo_mem_base_addr_o,
    input logic                                                 po_ntt_masking_en_o,
    input logic                                                 po_ntt_shuffling_en_o,
    input logic                                                 pi_ntt_busy_i,
    input logic [ABR_MEM_ADDR_WIDTH-1:0]                        po_aux_src0_base_addr_o,
    input logic [ABR_MEM_ADDR_WIDTH-1:0]                        po_aux_src1_base_addr_o,
    input logic [ABR_MEM_ADDR_WIDTH-1:0]                        po_aux_dest_base_addr_o,
    input logic                                                 po_power2round_enable_o,
    input mem_if_t [1:0]                                        pi_pwr2rnd_keymem_if_i,
    input logic [1:0][ABR_REG_WIDTH-1:0]                        pi_pwr2rnd_wr_data_i,
    input logic                                                 pi_pk_t1_wren_i,
    input logic [7:0][T1_COEFF_W-1:0]                           pi_pk_t1_wrdata_i,
    input logic [7:0]                                           pi_pk_t1_wr_addr_i,
    input logic                                                 pi_power2round_done_i,
    input logic                                                 po_decompose_enable_o,
    input logic                                                 po_decompose_mode_o,
    input logic                                                 pi_decompose_done_i,
    input logic                                                 po_skencode_enable_o,
    input mem_if_t                                              pi_skencode_keymem_if_i,
    input logic [ABR_REG_WIDTH-1:0]                             pi_skencode_wr_data_i,
    input logic                                                 pi_skencode_done_i,
    input logic                                                 po_skdecode_enable_o,
    input mem_if_t [1:0]                                        pi_skdecode_keymem_if_i,
    input logic [1:0][ABR_REG_WIDTH-1:0]                        po_skdecode_rd_data_o,
    input logic                                                 pi_skdecode_done_i,
    input logic                                                 pi_skdecode_error_i,
    input logic                                                 po_makehint_enable_o,
    input logic                                                 pi_makehint_invalid_i,
    input logic                                                 pi_makehint_done_i,
    input logic                                                 pi_makehint_reg_wren_i,
    input logic [3:0][7:0]                                      pi_makehint_reg_wrdata_i,
    input logic [ABR_MEM_ADDR_WIDTH-1:0]                        pi_makehint_reg_wr_addr_i,
    input logic                                                 po_normcheck_enable_o,
    input logic [1:0]                                           po_normcheck_mode_o,
    input logic                                                 pi_normcheck_invalid_i,
    input logic                                                 pi_normcheck_done_i,
    input logic                                                 po_sigencode_enable_o,
    input mem_if_t                                              pi_sigencode_wr_req_i,
    input logic [1:0][3:0][19:0]                                pi_sigencode_wr_data_i,
    input logic                                                 pi_sigencode_done_i,
    input logic                                                 po_pkdecode_enable_o,
    input logic [7:0]                                           pi_pkdecode_rd_addr_i,
    input logic [7:0][T1_COEFF_W-1:0]                           po_pkdecode_rd_data_o,
    input logic                                                 pi_pkdecode_done_i,
    input logic                                                 po_sigdecode_h_enable_o,
    input logic [SIGNATURE_H_VALID_NUM_BYTES-1:0][7:0]          po_signature_h_o,
    input logic                                                 pi_sigdecode_h_invalid_i,
    input logic                                                 pi_sigdecode_h_done_i,
    input logic                                                 po_sigdecode_z_enable_o,
    input mem_if_t                                              pi_sigdecode_z_rd_req_i,
    input logic [1:0][3:0][19:0]                                po_sigdecode_z_rd_data_o,
    input logic                                                 pi_sigdecode_z_done_i,
    input logic                                                 po_compress_enable_o,
    input compress_mode_t                                       po_compress_mode_o,
    input logic                                                 po_compress_compare_mode_o,
    input logic [2:0]                                           po_compress_num_poly_o,
    input logic                                                 pi_compress_done_i,
    input logic                                                 pi_compress_compare_failed_i,
    input logic [1:0]                                           pi_compress_api_rw_en_i,
    input logic [ABR_MEM_ADDR_WIDTH-1:0]                        pi_compress_api_rw_addr_i,
    input logic [ABR_REG_WIDTH-1:0]                             pi_compress_api_wr_data_i,
    input logic [ABR_REG_WIDTH-1:0]                             po_compress_api_rd_data_o,
    input logic                                                 po_decompress_enable_o,
    input logic                                                 pi_decompress_done_i,
    input decompress_mode_t                                     po_decompress_mode_o,
    input logic [2:0]                                           po_decompress_num_poly_o,
    input logic                                                 pi_decompress_api_rd_en_i,
    input logic [ABR_MEM_ADDR_WIDTH-1:0]                        pi_decompress_api_rd_addr_i,
    input logic [1:0][ABR_REG_WIDTH-1:0]                        po_decompress_api_rd_data_o,
    input logic                                                 po_lfsr_enable_o,
    input abr_lfsr_seed_t                                       po_lfsr_seed_o,
    input mem_if_t                                              po_zeroize_mem_o,
    input logic                                                 pi_debugUnlock_or_scan_mode_switch,
    input logic                                                 po_busy_o,
    input logic                                                 po_error_intr,
    input logic                                                 po_notif_intr,
    input logic                                                 po_sk_bank0_mem_if_re_i,
    input logic [SK_MEM_BANK_DATA_W-1:0]                        pi_sk_bank0_mem_if_rdata_o,
    input logic                                                 po_sk_bank1_mem_if_re_i,
    input logic [SK_MEM_BANK_DATA_W-1:0]                        pi_sk_bank1_mem_if_rdata_o,
    input logic                                                 po_sig_z_mem_if_re_i,
    input logic [SIG_Z_MEM_DATA_W-1:0]                          pi_sig_z_mem_if_rdata_o,
    input logic                                                 po_pk_mem_if_re_i,
    `ifdef CALIPTRA
    // KV interface
    input kv_read_t [2:0]                                       po_kv_read,
    input kv_rd_resp_t [2:0]                                    pi_kv_rd_resp,
    input kv_write_t                                            po_kv_write,
    input kv_wr_resp_t                                          pi_kv_wr_resp,
    //PCR Signing
    input pcr_signing_t                                         pi_pcr_signing_data,
    input logic                                                 pi_ocp_lock_in_progress,
    `endif
    input logic [PK_MEM_DATA_W-1:0]                             pi_pk_mem_if_rdata_o
    //$#//
);

    // Define default clock
    default clocking default_clk @(posedge pi_clk); endclocking

//-------------------------Constrain primary inputs-------------------------------------
     // Aux logic to track if compress is enabled
     // And reset when the compress is done.
     logic fv_compress_en;
     always_ff @(posedge pi_clk, negedge pi_rst_b) begin : compress_en_logic
            if (!pi_rst_b || po_zeroize) begin
                fv_compress_en <= 1'b0;
            end else if (po_compress_enable_o) begin
                fv_compress_en <= 1'b1;
            end else if (pi_compress_done_i) begin
                fv_compress_en <= 1'b0;
            end
        end
    // Done signal could assert only if enable is triggered previously.
      property assume_compress_done_p;
          pi_compress_done_i
      |->
          (fv_compress_en)
      endproperty
      assume_compress_done: assume property (assume_compress_done_p);
    `ifdef EVENTUAL_ASSUME
        assume_compress_done_eventually: assume property(
            s_eventually(pi_compress_done_i)
        );
    `else
        // To minisise the time delay for the operation by the
        // External block, we assume that the done signal will be
        // Asserted within FV_ADAMSBRIDGE_AUX_DLY cycles after the
        // Enable signal is asserted.
        property assume_compress_done_in_dly_p;
            po_compress_enable_o
        |->
                ## FV_ADAMSBRIDGE_AUX_DLY pi_compress_done_i
        endproperty
        assume_compress_done_in_dly: assume property (assume_compress_done_in_dly_p);
    `endif

     // Compress compare failed signal is asserted
     // if compare mode is selected previously when enabled.
     property assume_compress_compare_failed_p;
         (pi_compress_compare_failed_i)
     |->
         (fv_compress_en && po_compress_compare_mode_o)
     endproperty
     assume_compress_compare_failed: assume property (assume_compress_compare_failed_p);

    // API read and write enable signals can be asserted
    // only if compress is enabled.
         property assume_compress_api_rw_en_read_0_p;
             (pi_compress_api_rw_en_i[0])
         |->
             (fv_compress_en)
         endproperty
         assume_compress_api_rw_en_read_0: assume property (assume_compress_api_rw_en_read_0_p);

         property assume_compress_api_rw_en_write_0_p;
             (pi_compress_api_rw_en_i[0])
         |->
             (fv_compress_en)
         endproperty
         assume_compress_api_rw_en_write_0: assume property (assume_compress_api_rw_en_write_0_p);

        property assume_compress_api_rw_en_read_1_p;
            (pi_compress_api_rw_en_i[1] )
        |->
            (fv_compress_en)
        endproperty
        assume_compress_api_rw_en_read_1: assume property (assume_compress_api_rw_en_read_1_p);

         property assume_compress_api_rw_en_write_1_p;
             (pi_compress_api_rw_en_i[1])
         |->
             (fv_compress_en)
         endproperty
         assume_compress_api_rw_en_write_1: assume property (assume_compress_api_rw_en_write_1_p);


    // Aux logic to track if decompress is enabled
    // And reset when the decompress is done.
    logic fv_decompress_en;
    always_ff @(posedge pi_clk, negedge pi_rst_b) begin : decompress_en_logic
        if (!pi_rst_b || po_zeroize) begin
            fv_decompress_en <= 1'b0;
        end else if (po_decompress_enable_o) begin
            fv_decompress_en <= 1'b1;
        end else if (pi_decompress_done_i) begin
            fv_decompress_en <= 1'b0;
        end
    end

    // Done signal could assert only if enable is triggered previously.
    property assume_decompress_done_p;
        pi_decompress_done_i
    |->
        (fv_decompress_en)
    endproperty
    assume_decompress_done: assume property (assume_decompress_done_p);
    `ifdef EVENTUAL_ASSUME
        assume_decompress_done_eventually: assume property(
            s_eventually(pi_decompress_done_i)
        );
    `else
        // To minisise the time delay for the operation by the
        // External block, we assume that the done signal will be
        // Asserted within FV_ADAMSBRIDGE_AUX_DLY cycles after the
        // Enable signal is asserted.
        property assume_decompress_done_in_dly_p;
            po_decompress_enable_o
        |->
                ## FV_ADAMSBRIDGE_AUX_DLY pi_decompress_done_i
        endproperty
        assume_decompress_done_in_dly: assume property (assume_decompress_done_in_dly_p);
    `endif

    // API read enable signals can be asserted
    // only if decompress is enabled.
    property assume_decompress_api_rd_en_p;
        pi_decompress_api_rd_en_i
    |->
        (fv_decompress_en)
    endproperty
    assume_decompress_api_rd_en: assume property (assume_decompress_api_rd_en_p);


    // Sampler busy signal should be high if sampler is started
    // And should remain high for FV_ADAMSBRIDGE_BUSY_CNTR cycles
    // After that it should go low.
    logic fv_sampler_enabled;
    logic [FV_ADAMSBRIDGE_BUSY_CNTR-1:0] fv_sampler_busy_cntr;
    always_ff @(posedge pi_clk, negedge pi_rst_b) begin : sampler_enabled_tracking
        if (!pi_rst_b || po_zeroize) begin
            fv_sampler_enabled <= 1'b0;
            fv_sampler_busy_cntr <= '0;
        end else begin
            if (po_sampler_start_o) begin
                fv_sampler_enabled <= 1'b1;
                fv_sampler_busy_cntr <= FV_ADAMSBRIDGE_BUSY_CNTR;
            end else if (fv_sampler_enabled &&( fv_sampler_busy_cntr == '0)) begin
                fv_sampler_enabled <= 1'b0;
            end
            if(fv_sampler_enabled &&( fv_sampler_busy_cntr != '0)) begin
                fv_sampler_busy_cntr <= fv_sampler_busy_cntr -1;
            end
        end
    end

    // Assume the busy signal is correct
    assume_sampler_busy_i_2: assume property(
        pi_sampler_busy_i == fv_sampler_enabled
    );



    // NTT busy signal should be high if NTT is enabled
    // And should remain high for FV_ADAMSBRIDGE_BUSY_CNTR cycles
    // After that it should go low.
    logic fv_ntt_enabled;
    logic [FV_ADAMSBRIDGE_BUSY_CNTR-1:0] fv_ntt_busy_cntr;

    always_ff @(posedge pi_clk, negedge pi_rst_b) begin : ntt_enabled_tracking
        if (!pi_rst_b) begin
            fv_ntt_enabled <= 1'b0;
            fv_ntt_busy_cntr <= '0;
        end else begin
            if (po_ntt_enable_o) begin
                fv_ntt_enabled <= 1'b1;
                fv_ntt_busy_cntr <= FV_ADAMSBRIDGE_BUSY_CNTR;
            end else if (fv_ntt_enabled && ( fv_ntt_busy_cntr=='0)) begin
                fv_ntt_enabled <= 1'b0;
            end
            if(fv_ntt_enabled && ( fv_ntt_busy_cntr!='0)) begin
                fv_ntt_busy_cntr <= fv_ntt_busy_cntr -1;
            end
        end
    end

    // Assume the busy signal is correct
    assume_ntt_busy_i_2: assume property(
       pi_ntt_busy_i == (fv_ntt_enabled)
    );



    // Sampler data valid signal should be high if sampler is started
    // And it should always be a pulse.
    logic fv_sample_dv;
    always_ff @(posedge pi_clk, negedge pi_rst_b) begin : sample_dv_logic
        if (!pi_rst_b || po_zeroize) begin
            fv_sample_dv <= 1'b0;
        end else if (po_sha3_start_o) begin
            fv_sample_dv <= 1'b1;
        end else if (fv_sampler_busy_cntr==1) begin
            fv_sample_dv <= 1'b0;
        end
    end
    // Assume the data valid signal is correct if sampler is busy and started
    property assume_sampler_dv_p;
        pi_sampler_state_dv_i
    |->
        (fv_sample_dv && (pi_sampler_busy_i))
    endproperty
    assume_sampler_dv: assume property (assume_sampler_dv_p);

    // Assume the data valid signal is a pulse
    property assume_sampler_valid_pulse_p;
        pi_sampler_state_dv_i
    |->
        ##1 !pi_sampler_state_dv_i
    endproperty
    assume_sampler_valid_pulse: assume property (assume_sampler_valid_pulse_p);

    //When no data valid, data should be zero
    property assume_sampler_data_stable_p;
        !pi_sampler_state_dv_i
    |->
        (pi_sampler_state_data_i == '0)
    endproperty
    assume_sampler_data_stable: assume property (assume_sampler_data_stable_p);



    //MLDSA constraints////////////////////////////////////////
    // No aux units which are used for MLDSA mode should trigger
    // the done or mem rd/wr requests and error since these are not used
    // in the MLKEM mode.To make sure these are not triggered an assertion is written
    // to check that these units are always idle.
    property no_mldsa_aux_units;
        !pi_sigdecode_z_done_i &&
        !pi_sigdecode_h_done_i &&
        !pi_sigdecode_h_invalid_i &&
        !pi_pkdecode_done_i &&
        !pi_sigencode_done_i &&
        !pi_power2round_done_i &&
        !pi_decompose_done_i &&
        !pi_skencode_done_i &&
        !pi_skdecode_done_i &&
        !pi_normcheck_done_i &&
        !pi_normcheck_invalid_i &&
        !pi_makehint_done_i &&
        !pi_makehint_invalid_i &&
        !pi_makehint_reg_wren_i &&
        pi_pwr2rnd_keymem_if_i[0].rd_wr_en == RW_IDLE &&
        pi_pwr2rnd_keymem_if_i[1].rd_wr_en == RW_IDLE &&
        !pi_pk_t1_wren_i &&
        pi_skencode_keymem_if_i.rd_wr_en == RW_IDLE &&
        pi_skdecode_keymem_if_i[0].rd_wr_en == RW_IDLE &&
        pi_skdecode_keymem_if_i[1].rd_wr_en == RW_IDLE &&
        !pi_skdecode_error_i
    ;endproperty

    assume_no_mldsa_aux_units: assume property(no_mldsa_aux_units);



    // When MLKEM is enabled, MLDSA should be disabled.
    assume_disable_mldsa: assume property(
        pi_abr_reg_hwif_out_i.MLDSA_CTRL.CTRL.value == MLDSA_NONE &&
        !pi_abr_reg_hwif_out_i.kv_mldsa_seed_rd_ctrl.read_en.value
    );
    // End MLDSA constraints//////////////////////////////////////

    ///////////////////////////////////////////////////////////////////

    // MSG rdy is asserted immediately after its deassertion
    property assume_msg_rdy__p;
        po_msg_valid_o && !pi_msg_rdy_i
    |->
                ##FV_ADAMSBRIDGE_CNTRL_RDY_DELAY pi_msg_rdy_i
    endproperty
    assume_msg_rdy_: assume property (assume_msg_rdy__p);


    property assume_mlkem_ctrl_value_i_p;
        //disable iff(!pi_rst_b)
            po_abr_reg_hwif_in_o.MLKEM_CTRL.CTRL.hwclr
    |->
            ##1 pi_abr_reg_hwif_out_i.MLKEM_CTRL.CTRL.value == '0
    endproperty
    assume_mlkem_ctrl_value_i: assume property (assume_mlkem_ctrl_value_i_p);

    // MLKEM control registers are stable during the operation
    // i.e., when abr_ready is low.
    property assume_hwif_out_mlkem_value_i_stable_p;
        !po_abr_reg_hwif_in_o.abr_ready
    |->
            ##1 $stable(pi_abr_reg_hwif_out_i.MLKEM_CTRL.CTRL.value) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_SEED_Z[0].req) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_SEED_Z[0].req_is_wr) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_SEED_Z[0].wr_data) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_SEED_Z[0].wr_biten) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_SEED_Z[1].req) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_SEED_Z[1].req_is_wr) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_SEED_Z[1].wr_data) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_SEED_Z[1].wr_biten) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_SEED_Z[2].req) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_SEED_Z[2].req_is_wr) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_SEED_Z[2].wr_data) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_SEED_Z[2].wr_biten) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_SEED_Z[3].req) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_SEED_Z[3].req_is_wr) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_SEED_Z[3].wr_data) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_SEED_Z[3].wr_biten) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_SEED_Z[4].req) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_SEED_Z[4].req_is_wr) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_SEED_Z[4].wr_data) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_SEED_Z[4].wr_biten) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_SEED_Z[5].req) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_SEED_Z[5].req_is_wr) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_SEED_Z[5].wr_data) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_SEED_Z[5].wr_biten) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_SEED_Z[6].req) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_SEED_Z[6].req_is_wr) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_SEED_Z[6].wr_data) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_SEED_Z[6].wr_biten) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_SEED_Z[7].req) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_SEED_Z[7].req_is_wr) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_SEED_Z[7].wr_data) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_SEED_Z[7].wr_biten) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_SHARED_KEY[0].req) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_SHARED_KEY[0].req_is_wr) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_SHARED_KEY[1].req) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_SHARED_KEY[1].req_is_wr) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_SHARED_KEY[2].req) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_SHARED_KEY[2].req_is_wr) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_SHARED_KEY[3].req) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_SHARED_KEY[3].req_is_wr) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_SHARED_KEY[4].req) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_SHARED_KEY[4].req_is_wr) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_SHARED_KEY[5].req) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_SHARED_KEY[5].req_is_wr) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_SHARED_KEY[6].req) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_SHARED_KEY[6].req_is_wr) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_SHARED_KEY[7].req) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_SHARED_KEY[7].req_is_wr) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_MSG.req) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_MSG.addr) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_MSG.req_is_wr) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_MSG.wr_data) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_MSG.wr_biten) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_DECAPS_KEY.req) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_DECAPS_KEY.addr) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_DECAPS_KEY.req_is_wr) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_DECAPS_KEY.wr_data) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_DECAPS_KEY.wr_biten) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_ENCAPS_KEY.req) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_ENCAPS_KEY.addr) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_ENCAPS_KEY.req_is_wr) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_ENCAPS_KEY.wr_data) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_ENCAPS_KEY.wr_biten) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_CIPHERTEXT.req) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_CIPHERTEXT.addr) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_CIPHERTEXT.req_is_wr) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_CIPHERTEXT.wr_data) &&
                $stable(pi_abr_reg_hwif_out_i.MLKEM_CIPHERTEXT.wr_biten)
    endproperty
    assume_hwif_out_mlkem_value_i_stable: assume property (assume_hwif_out_mlkem_value_i_stable_p);


    // Additional constraints especially for the memory interfaces to avoid mldsa writes
    // these constraints were to be converted for mlkem in mldsa mode.
    // No MLDSA requests in this case where MLKEM is enabled.

    property no_req_when_mlkem_enabled_P(req);
       !req
    ;endproperty
    assume_mldsa_privkey_mem_no_req_when_mlkem_enabled_p: assume property(no_req_when_mlkem_enabled_P(pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_IN.req));
    assume_mldsa_pubkey_mem_no_req_when_mlkem_enabled_p: assume property(no_req_when_mlkem_enabled_P(pi_abr_reg_hwif_out_i.MLDSA_PUBKEY.req));


    //-------------------------Constrain memory interface signals-------------------------------------//

    // When there is no read request, the data should be stable
    property stable_data_no_req_P(req, data);
        !req
    |=>
        $stable(data)
    ;endproperty

    assume_sk_mem_0_stable_data_no_req_p: assume property(stable_data_no_req_P(po_sk_bank0_mem_if_re_i,pi_sk_bank0_mem_if_rdata_o));
    assume_sk_mem_1_stable_data_no_req_p: assume property(stable_data_no_req_P(po_sk_bank1_mem_if_re_i,pi_sk_bank1_mem_if_rdata_o));
    assume_sig_z_mem_stable_data_no_req_p: assume property(stable_data_no_req_P(po_sig_z_mem_if_re_i,pi_sig_z_mem_if_rdata_o));
    assume_pk_mem_stable_data_no_req_p: assume property(stable_data_no_req_P(po_pk_mem_if_re_i,pi_pk_mem_if_rdata_o));

`ifndef NO_ABSTRACTION
    // Added the snipped signal constraint for the msg_cnt
    logic [ABR_OPR_WIDTH-1:$clog2(MsgStrbW)] fv_msg_cnt;
    always_ff @( posedge pi_clk, negedge pi_rst_b ) begin : fv_msg_cnt_abs_logic
        if(!pi_rst_b) begin
            fv_msg_cnt <= '0;
        end
        else if(po_zeroize) begin
            fv_msg_cnt <= '0;
        end
        else begin
            if(abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_IDLE) begin
                fv_msg_cnt <= '0;
            end
            else if(abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_MSG_LOAD && (((fv_msg_cnt == '0)|| (fv_msg_cnt == abr_ctrl.abr_instr.length[ABR_OPR_WIDTH-1:$clog2(MsgStrbW)]-1) || (fv_msg_cnt == abr_ctrl.abr_instr.length[ABR_OPR_WIDTH-1:$clog2(MsgStrbW)])) && pi_msg_rdy_i)) begin
                fv_msg_cnt <= fv_msg_cnt + 1;
            end
            else if(abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_MSG_LOAD && (fv_msg_cnt == 1) && pi_msg_rdy_i) begin
                fv_msg_cnt <= abr_ctrl.abr_instr.length[ABR_OPR_WIDTH-1:$clog2(MsgStrbW)]-1;
            end
            else if(abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_MSG_LOAD && !pi_msg_rdy_i) begin
                fv_msg_cnt <= fv_msg_cnt;
            end
            else begin
                 fv_msg_cnt <= '0;
            end
        end
    end

    // msg_cnt should be equal to the fv_msg_cnt
     property msg_cnt_abstracted_p;
         abr_ctrl.msg_cnt == fv_msg_cnt
     ;endproperty
    assume_msg_cnt_abstracted_asm: assume property(msg_cnt_abstracted_p);

    // Program counter should take only the valid values
    property abstract_mlkem_prim_prog_cntr_P;
        (abr_ctrl.abr_prog_cntr == ABR_RESET) ||
        (abr_ctrl.abr_prog_cntr == ABR_ZEROIZE) ||
        ((abr_ctrl.abr_prog_cntr >= MLKEM_KG_S) && (abr_ctrl.abr_prog_cntr <= MLKEM_KG_E)) ||
        ((abr_ctrl.abr_prog_cntr >= MLKEM_DECAPS_S) && (abr_ctrl.abr_prog_cntr <= MLKEM_DECAPS_E)) ||
        ((abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S) && (abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_E))
    ;endproperty

    assume_abstract_mlkem_prim_prog_cntr_asm: assume property(abstract_mlkem_prim_prog_cntr_P);

    logic fv_keygen_set;
    logic fv_keygen_signing_set;
    logic fv_signing_set;
    logic fv_verify_set;
    logic fv_mlkem_keygen_set;
    logic fv_mlkem_encaps_set;
    logic fv_mlkem_decaps_set;
    logic fv_mlkem_keygen_decaps_process_set;

    always_comb begin: fv_set_mode_logic
            fv_keygen_set = '0;
            fv_keygen_signing_set = '0;
            fv_signing_set = '0;
            fv_verify_set = '0;
            fv_mlkem_keygen_set = '0;
            fv_mlkem_decaps_set = '0;
            fv_mlkem_encaps_set = '0;
            if((abr_ctrl.abr_prog_cntr >= MLDSA_KG_S) && (abr_ctrl.abr_prog_cntr <= MLDSA_KG_E)) begin
                fv_keygen_set = 1;
            end
            if((abr_ctrl.abr_prog_cntr >= MLDSA_SIGN_S) && (abr_ctrl.abr_prog_cntr <= MLDSA_SIGN_E)) begin
                fv_signing_set = 1;
            end
            if((abr_ctrl.abr_prog_cntr >= MLDSA_VERIFY_S) && (abr_ctrl.abr_prog_cntr <= MLDSA_VERIFY_E)) begin
                fv_verify_set = 1;
            end
            if((abr_ctrl.abr_prog_cntr >= MLKEM_KG_S) && (abr_ctrl.abr_prog_cntr <= MLKEM_KG_E)) begin
                fv_mlkem_keygen_set = 1;
            end
            if((abr_ctrl.abr_prog_cntr >= MLKEM_DECAPS_S) && (abr_ctrl.abr_prog_cntr <= MLKEM_DECAPS_E)) begin
                fv_mlkem_decaps_set = 1;
            end
            if((abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S) && (abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_E)) begin
                fv_mlkem_encaps_set = 1;
            end
    end

    // Process signals are set when the program counter is in the respective ranges
    // This is to avoid the first cycle of the process signal being unconstrained
    // due to the init value abstraction of the program counter
    property abstract_mlkem_init_value_prim_prog_cntr_P;
        abr_ctrl.mlkem_keygen_process == (abr_ctrl.mlkem_cmd_reg == MLKEM_KEYGEN && fv_mlkem_keygen_set) &&
        abr_ctrl.mlkem_encaps_process == (abr_ctrl.mlkem_cmd_reg == MLKEM_ENCAPS && fv_mlkem_encaps_set) &&
        abr_ctrl.mlkem_decaps_process == ((abr_ctrl.mlkem_cmd_reg == MLKEM_DECAPS && fv_mlkem_decaps_set) || (abr_ctrl.mlkem_cmd_reg == MLKEM_KEYGEN_DEC && fv_mlkem_decaps_set)) &&
        abr_ctrl.mlkem_keygen_decaps_process == (abr_ctrl.mlkem_cmd_reg == MLKEM_KEYGEN_DEC)
    ;endproperty
    assume_abstract_mlkem_init_value_prim_prog_cntr_asm: assume property(abstract_mlkem_init_value_prim_prog_cntr_P);


    // Post reset it takes 1cycle to update the out of sequencer. Since in the init value abstartcion this
    //would cause the first cycle to be unconstrained and the data_o could take any value triggering unnecessary
    // state transitions.
    property abstract_reset_value_P;
        $past(!pi_rst_b)
    |->
        abr_ctrl.abr_seq_inst.data_o == '0
    ;endproperty
    assume_abstract_reset_value_p: assume property(abstract_reset_value_P);
`endif

    // Required since init value counter can start at a end state and trigger the valid
    // post that valid is resetted only if zeroize and in between cmds it is expected to have a zeroize
    // if thats not the case the proofs will fail, since the valid reg stays asserted.
    property zeroize_post_mlkem_valid;
        abr_ctrl.mlkem_valid_reg
    |=>
        pi_abr_reg_hwif_out_i.MLKEM_CTRL.ZEROIZE.value
    ;endproperty
    assume_zeroize_post_mlkem_valid: assume property(zeroize_post_mlkem_valid);


    //MLKEM_CTRL and kv_ctrl reg should be mutually exclusive
    property assume_if_mlkem_ctrl_no_kv_mlkem_seed_rd_for_2_cycles_p;
        pi_abr_reg_hwif_out_i.MLKEM_CTRL.CTRL.value != '0
    |->
            !pi_abr_reg_hwif_out_i.kv_mlkem_seed_rd_ctrl.read_en.value [*2]
    endproperty
    assume_if_mlkem_ctrl_no_kv_mlkem_seed_rd_for_2_cycles: assume property (assume_if_mlkem_ctrl_no_kv_mlkem_seed_rd_for_2_cycles_p);


    property assume_if_kv_mlkem_seed_rd_no_mlkem_ctrl_for_2_cycles_p;
        pi_abr_reg_hwif_out_i.kv_mlkem_seed_rd_ctrl.read_en.value
    |->
            pi_abr_reg_hwif_out_i.MLKEM_CTRL.CTRL.value == '0 [*2]
    endproperty
    assume_if_kv_mlkem_seed_rd_no_mlkem_ctrl_for_2_cycles: assume property (assume_if_kv_mlkem_seed_rd_no_mlkem_ctrl_for_2_cycles_p);

    property assume_if_mlkem_ctrl_no_kv_mlkem_msg_rd_for_2_cycles_p;
        pi_abr_reg_hwif_out_i.MLKEM_CTRL.CTRL.value != '0
    |->
            !pi_abr_reg_hwif_out_i.kv_mlkem_msg_rd_ctrl.read_en.value [*2]
    endproperty
    assume_if_mlkem_ctrl_no_kv_mlkem_msg_rd_for_2_cycles: assume property (assume_if_mlkem_ctrl_no_kv_mlkem_msg_rd_for_2_cycles_p);

    property assume_if_kv_mlkem_msg_rd_no_mlkem_ctrl_for_2_cycles_p;
        pi_abr_reg_hwif_out_i.kv_mlkem_msg_rd_ctrl.read_en.value
    |->
            pi_abr_reg_hwif_out_i.MLKEM_CTRL.CTRL.value == '0 [*2]
    endproperty
    assume_if_kv_mlkem_msg_rd_no_mlkem_ctrl_for_2_cycles: assume property (assume_if_kv_mlkem_msg_rd_no_mlkem_ctrl_for_2_cycles_p);


    //If swwe is not asserted, read_ctrl registers should be stable
    property assume_kv_mlkem_seed_rd_ctrl_read_en_stable_p;
        disable iff(!pi_rst_b)
            !po_abr_reg_hwif_in_o.kv_mlkem_seed_rd_ctrl.read_en.swwe &&
            !po_abr_reg_hwif_in_o.kv_mlkem_seed_rd_ctrl.read_en.hwclr
    |->
            ##1 $stable(pi_abr_reg_hwif_out_i.kv_mlkem_seed_rd_ctrl.read_en.value)
    endproperty
    assume_kv_mlkem_seed_rd_ctrl_read_en_stable: assume property (assume_kv_mlkem_seed_rd_ctrl_read_en_stable_p);

    property assume_kv_mlkem_seed_rd_ctrl_read_entry_stable_p;
        disable iff(!pi_rst_b)
            !po_abr_reg_hwif_in_o.kv_mlkem_seed_rd_ctrl.read_entry.swwe &&
            !po_abr_reg_hwif_in_o.kv_mlkem_seed_rd_ctrl.read_en.hwclr
    |->
            ##1 $stable(pi_abr_reg_hwif_out_i.kv_mlkem_seed_rd_ctrl.read_entry.value)
    endproperty
    assume_kv_mlkem_seed_rd_ctrl_read_entry_stable: assume property (assume_kv_mlkem_seed_rd_ctrl_read_entry_stable_p);

    property assume_kv_mlkem_seed_rd_ctrl_read_pcr_hash_extend_stable_p;
        disable iff(!pi_rst_b)
            !po_abr_reg_hwif_in_o.kv_mlkem_seed_rd_ctrl.pcr_hash_extend.swwe &&
            !po_abr_reg_hwif_in_o.kv_mlkem_seed_rd_ctrl.read_en.hwclr
    |->
            ##1 $stable(pi_abr_reg_hwif_out_i.kv_mlkem_seed_rd_ctrl.pcr_hash_extend.value)
    endproperty
    assume_kv_mlkem_seed_rd_ctrl_read_pcr_hash_extend_stable: assume property (assume_kv_mlkem_seed_rd_ctrl_read_pcr_hash_extend_stable_p);

    property assume_kv_mlkem_seed_rd_ctrl_read_rsvd_stable_p;
        disable iff(!pi_rst_b)
            !po_abr_reg_hwif_in_o.kv_mlkem_seed_rd_ctrl.rsvd.swwe &&
            !po_abr_reg_hwif_in_o.kv_mlkem_seed_rd_ctrl.read_en.hwclr
    |->
            ##1 $stable(pi_abr_reg_hwif_out_i.kv_mlkem_seed_rd_ctrl.rsvd.value)
    endproperty
    assume_kv_mlkem_seed_rd_ctrl_read_rsvd_stable: assume property (assume_kv_mlkem_seed_rd_ctrl_read_rsvd_stable_p);

    property assume_kv_mlkem_msg_rd_ctrl_read_en_stable_p;
        disable iff(!pi_rst_b)
            !po_abr_reg_hwif_in_o.kv_mlkem_msg_rd_ctrl.read_en.swwe &&
            !po_abr_reg_hwif_in_o.kv_mlkem_msg_rd_ctrl.read_en.hwclr
    |->
            ##1 $stable(pi_abr_reg_hwif_out_i.kv_mlkem_msg_rd_ctrl.read_en.value)
    endproperty
    assume_kv_mlkem_msg_rd_ctrl_read_en_stable: assume property (assume_kv_mlkem_msg_rd_ctrl_read_en_stable_p);

    property assume_kv_mlkem_msg_rd_ctrl_read_entry_stable_p;
        disable iff(!pi_rst_b)
            !po_abr_reg_hwif_in_o.kv_mlkem_msg_rd_ctrl.read_entry.swwe &&
            !po_abr_reg_hwif_in_o.kv_mlkem_msg_rd_ctrl.read_en.hwclr
    |->
            ##1 $stable(pi_abr_reg_hwif_out_i.kv_mlkem_msg_rd_ctrl.read_entry.value)
    endproperty
    assume_kv_mlkem_msg_rd_ctrl_read_entry_stable: assume property (assume_kv_mlkem_msg_rd_ctrl_read_entry_stable_p);

    property assume_kv_mlkem_msg_rd_ctrl_read_pcr_hash_extend_stable_p;
        disable iff(!pi_rst_b)
            !po_abr_reg_hwif_in_o.kv_mlkem_msg_rd_ctrl.pcr_hash_extend.swwe &&
            !po_abr_reg_hwif_in_o.kv_mlkem_msg_rd_ctrl.read_en.hwclr
    |->
            ##1 $stable(pi_abr_reg_hwif_out_i.kv_mlkem_msg_rd_ctrl.pcr_hash_extend.value)
    endproperty
    assume_kv_mlkem_msg_rd_ctrl_read_pcr_hash_extend_stable: assume property (assume_kv_mlkem_msg_rd_ctrl_read_pcr_hash_extend_stable_p);

    property assume_kv_mlkem_msg_rd_ctrl_read_rsvd_stable_p;
        disable iff(!pi_rst_b)
            !po_abr_reg_hwif_in_o.kv_mlkem_msg_rd_ctrl.rsvd.swwe &&
            !po_abr_reg_hwif_in_o.kv_mlkem_msg_rd_ctrl.read_en.hwclr
    |->
            ##1 $stable(pi_abr_reg_hwif_out_i.kv_mlkem_msg_rd_ctrl.rsvd.value)
    endproperty
    assume_kv_mlkem_msg_rd_ctrl_read_rsvd_stable: assume property (assume_kv_mlkem_msg_rd_ctrl_read_rsvd_stable_p);


    //If hwclr is asserted, read_ctrl registers should be deasserted
    property assume_kv_mlkem_seed_rd_ctrl_clear_p;
        po_abr_reg_hwif_in_o.kv_mlkem_seed_rd_ctrl.read_en.hwclr
    |->
            ##1 !pi_abr_reg_hwif_out_i.kv_mlkem_seed_rd_ctrl.read_entry.value &&
                !pi_abr_reg_hwif_out_i.kv_mlkem_seed_rd_ctrl.pcr_hash_extend.value &&
                !pi_abr_reg_hwif_out_i.kv_mlkem_seed_rd_ctrl.rsvd.value &&
                !pi_abr_reg_hwif_out_i.kv_mlkem_seed_rd_ctrl.read_en.value
    endproperty
    assume_kv_mlkem_seed_rd_ctrl_clear: assume property (assume_kv_mlkem_seed_rd_ctrl_clear_p);

    property assume_kv_mlkem_msg_rd_ctrl_clear_p;
        po_abr_reg_hwif_in_o.kv_mlkem_msg_rd_ctrl.read_en.hwclr
    |->
            ##1 !pi_abr_reg_hwif_out_i.kv_mlkem_msg_rd_ctrl.read_entry.value &&
                !pi_abr_reg_hwif_out_i.kv_mlkem_msg_rd_ctrl.pcr_hash_extend.value &&
                !pi_abr_reg_hwif_out_i.kv_mlkem_msg_rd_ctrl.rsvd.value &&
                !pi_abr_reg_hwif_out_i.kv_mlkem_msg_rd_ctrl.read_en.value
    endproperty
    assume_kv_mlkem_msg_rd_ctrl_clear: assume property (assume_kv_mlkem_msg_rd_ctrl_clear_p);

    //If reset is asserted, read_ctrl registers should be deasserted
    property assume_kv_mlkem_seed_rd_ctrl_rst_p;
        $past(!pi_rst_b)
    |->
            pi_abr_reg_hwif_out_i.kv_mlkem_seed_rd_ctrl.read_entry.value == '0 &&
            pi_abr_reg_hwif_out_i.kv_mlkem_seed_rd_ctrl.pcr_hash_extend.value == '0 &&
            pi_abr_reg_hwif_out_i.kv_mlkem_seed_rd_ctrl.rsvd.value == '0 &&
            pi_abr_reg_hwif_out_i.kv_mlkem_seed_rd_ctrl.read_en.value == '0
    endproperty
    assume_kv_mlkem_seed_rd_ctrl_rst: assume property (assume_kv_mlkem_seed_rd_ctrl_rst_p);

    property assume_kv_mlkem_msg_rd_ctrl_rst_p;
        $past(!pi_rst_b)
    |->
            pi_abr_reg_hwif_out_i.kv_mlkem_msg_rd_ctrl.read_entry.value == '0 &&
            pi_abr_reg_hwif_out_i.kv_mlkem_msg_rd_ctrl.pcr_hash_extend.value == '0 &&
            pi_abr_reg_hwif_out_i.kv_mlkem_msg_rd_ctrl.rsvd.value == '0 &&
            pi_abr_reg_hwif_out_i.kv_mlkem_msg_rd_ctrl.read_en.value == '0
    endproperty
    assume_kv_mlkem_msg_rd_ctrl_rst: assume property (assume_kv_mlkem_msg_rd_ctrl_rst_p);


    //MLKEM seed response data should be '0 in case of read error
    property assume_kv_mlkem_seed_resp_data_zero_during_error_p;
        // disable iff(!pi_rst_b)
            pi_kv_rd_resp[1].error
    |->
            pi_kv_rd_resp[1].read_data == '0
    endproperty
    assume_kv_mlkem_seed_resp_data_zero_during_error: assume property (assume_kv_mlkem_seed_resp_data_zero_during_error_p);

    //MLKEM msg response data should be '0 in case of read error
    property assume_kv_mlkem_msg_resp_data_zero_during_error_p;
        // disable iff(!pi_rst_b)
            pi_kv_rd_resp[2].error
    |->
            pi_kv_rd_resp[2].read_data == '0
    endproperty
    assume_kv_mlkem_msg_resp_data_zero_during_error: assume property (assume_kv_mlkem_msg_resp_data_zero_during_error_p);

endmodule
