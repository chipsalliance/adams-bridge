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

`define abr_ctrl fv_abr_ctrl_dut.abr_ctrl_inst

module fv_abr_ctrl_constraints
    import abr_params_pkg::*;
    import abr_sampler_pkg::*;
    import abr_ctrl_pkg::*;
    import abr_sha3_pkg::*;
    import abr_reg_pkg::*;
    import ntt_defines_pkg::*;
    import compress_defines_pkg::*;
    import decompress_defines_pkg::*;
    `ifdef CALIPTRA
  import kv_defines_pkg::*; 
  `endif
#(
     parameter FV_ADAMSBRIDGE_BUSY_CNTR = 2,
     parameter FV_ADAMSBRIDGE_CNTRL_RDY_DELAY = 1,
     parameter FV_ADAMSBRIDGE_AUX_DLY = 2,
    //#$localparams
    localparam ABR_SEQ_NTT = 0
    //$#//
   
) (//#$ports
    input logic                                        pi_clk,
    input logic                                        pi_rst_b,
    input logic                                        po_zeroize,
    input abr_reg__in_t                                po_abr_reg_hwif_in_o,
    input abr_reg__out_t                               pi_abr_reg_hwif_out_i,
    input abr_sampler_mode_e                           po_sampler_mode_o,
    input logic                                        po_sha3_start_o,
    input logic                                        po_msg_start_o,
    input logic                                        po_msg_valid_o,
    input logic                                        pi_msg_rdy_i,
    input logic [MsgStrbW-1:0]                         po_msg_strobe_o,
    input logic [MsgWidth-1:0]                         po_msg_data_o,
    input logic                                        po_sampler_start_o,
    input logic                                        pi_sampler_busy_i,
    input logic                                        pi_sampler_state_dv_i,
    input logic [abr_sha3_pkg::StateW-1:0]             pi_sampler_state_data_i,
    input logic [ABR_MEM_ADDR_WIDTH-1:0]               po_dest_base_addr_o,
    input logic                                        po_ntt_enable_o,
    input abr_ntt_mode_e                               po_ntt_mode_o,
    input ntt_mem_addr_t                               po_ntt_mem_base_addr_o,
    input pwo_mem_addr_t                               po_pwo_mem_base_addr_o,
    input logic                                        po_ntt_masking_en_o,
    input logic                                        po_ntt_shuffling_en_o,
    input logic                                        pi_ntt_busy_i,
    input logic [ABR_MEM_ADDR_WIDTH-1:0]          po_aux_src0_base_addr_o,
    input logic [ABR_MEM_ADDR_WIDTH-1:0]          po_aux_src1_base_addr_o,
    input logic [ABR_MEM_ADDR_WIDTH-1:0]          po_aux_dest_base_addr_o,
    input logic                                        po_power2round_enable_o,
    input mem_if_t [1:0]                               pi_pwr2rnd_keymem_if_i,
    input logic [1:0][ABR_REG_WIDTH-1:0]                  pi_pwr2rnd_wr_data_i,
    input logic                                        pi_pk_t1_wren_i,
    input logic [7:0][T1_COEFF_W-1:0]                             pi_pk_t1_wrdata_i,
    input logic [7:0]                                  pi_pk_t1_wr_addr_i,
    input logic                                        pi_power2round_done_i,
    input logic                                        po_decompose_enable_o,
    input logic                                        po_decompose_mode_o,
    input logic                                        pi_decompose_done_i,
    input logic                                        po_skencode_enable_o,
    input mem_if_t                                     pi_skencode_keymem_if_i,
    input logic [ABR_REG_WIDTH-1:0]                       pi_skencode_wr_data_i,
    input logic                                        pi_skencode_done_i,
    input logic                                        po_skdecode_enable_o,
    input mem_if_t [1:0]                               pi_skdecode_keymem_if_i,
    input logic [1:0][ABR_REG_WIDTH-1:0]                  po_skdecode_rd_data_o,
    input logic [1:0]                                   po_skdecode_rd_data_valid_o,
    input logic                                        pi_skdecode_done_i,
    input logic                                        pi_skdecode_error_i,
    input logic                                        po_makehint_enable_o,
    input logic                                        pi_makehint_invalid_i,
    input logic                                        pi_makehint_done_i,
    input logic                                        pi_makehint_reg_wren_i,
    input logic [3:0][7:0]                             pi_makehint_reg_wrdata_i,
    input logic [ABR_MEM_ADDR_WIDTH-1:0]               pi_makehint_reg_wr_addr_i,
    input logic                                        po_normcheck_enable_o,
    input logic [1:0]                                  po_normcheck_mode_o,
    input logic                                        pi_normcheck_invalid_i,
    input logic                                        pi_normcheck_done_i,
    input logic                                        po_sigencode_enable_o,
    input mem_if_t                                     pi_sigencode_wr_req_i,
    input logic [1:0][3:0][19:0]                       pi_sigencode_wr_data_i,
    input logic                                        pi_sigencode_done_i,
    input logic                                        po_pkdecode_enable_o,
    input logic                                        pi_pkdecode_rd_en_i,
    input logic [7:0]                                  pi_pkdecode_rd_addr_i,
    input logic [7:0][T1_COEFF_W-1:0]                  po_pkdecode_rd_data_o,
    input logic                                        po_pkdecode_rd_data_valid_o,
    input logic                                        pi_pkdecode_done_i,
    input logic                                        po_sigdecode_h_enable_o,
    input logic [SIGNATURE_H_VALID_NUM_BYTES-1:0][7:0] po_signature_h_o,
    input logic                                        pi_sigdecode_h_invalid_i,
    input logic                                        pi_sigdecode_h_done_i,
    input logic                                        po_sigdecode_z_enable_o,
    input mem_if_t                                     pi_sigdecode_z_rd_req_i,
    input logic [1:0][3:0][19:0]                       po_sigdecode_z_rd_data_o,
    input logic                                        po_sigdecode_z_rd_data_valid_o,
    input logic                                        pi_sigdecode_z_done_i,
    input logic                                        po_compress_enable_o,
    input compress_mode_t                              po_compress_mode_o,
    input logic                                        po_compress_compare_mode_o,
    input logic [2:0]                                  po_compress_num_poly_o,
    input logic                                        pi_compress_done_i,
    input logic                                        pi_compress_compare_failed_i,
    input logic [1:0]                                  pi_compress_api_rw_en_i,
    input logic [ABR_MEM_ADDR_WIDTH-1:0]               pi_compress_api_rw_addr_i,
    input logic [ABR_REG_WIDTH-1:0]                       pi_compress_api_wr_data_i,
    input logic [ABR_REG_WIDTH-1:0]                       po_compress_api_rd_data_o,
    input logic                                        po_compress_api_rd_data_valid_o,
    input logic                                        po_decompress_enable_o,
    input logic                                        pi_decompress_done_i,
    input decompress_mode_t                            po_decompress_mode_o,
    input logic [2:0]                                  po_decompress_num_poly_o,
    input logic                                        pi_decompress_api_rd_en_i,
    input logic [ABR_MEM_ADDR_WIDTH-1:0]               pi_decompress_api_rd_addr_i,
    input logic [1:0][ABR_REG_WIDTH-1:0]                  po_decompress_api_rd_data_o,
    input logic                                        po_decompress_api_rd_data_valid_o,
    input logic                                        po_lfsr_enable_o,
    input abr_lfsr_seed_t                              po_lfsr_seed_o,
    input mem_if_t                                     po_zeroize_mem_o,
    input logic                                        pi_debugUnlock_or_scan_mode_switch,
    input logic                                        po_busy_o,
    input logic                                        po_error_intr,
    input logic                                        po_notif_intr,
     input logic                                        po_sk_bank0_mem_if_we_i,
    input logic [SK_MEM_BANK_ADDR_W-1:0]               po_sk_bank0_mem_if_waddr_i,
    input logic [SK_MEM_BANK_DATA_W-1:0]               po_sk_bank0_mem_if_wdata_i,
    input logic                                        po_sk_bank0_mem_if_re_i,
    input logic [SK_MEM_BANK_ADDR_W-1:0]               po_sk_bank0_mem_if_raddr_i,
    input logic [SK_MEM_BANK_DATA_W-1:0]               pi_sk_bank0_mem_if_rdata_o,
    input logic                                        po_sk_bank1_mem_if_we_i,
    input logic [SK_MEM_BANK_ADDR_W-1:0]               po_sk_bank1_mem_if_waddr_i,
    input logic [SK_MEM_BANK_DATA_W-1:0]               po_sk_bank1_mem_if_wdata_i,
    input logic                                        po_sk_bank1_mem_if_re_i,
    input logic [SK_MEM_BANK_ADDR_W-1:0]               po_sk_bank1_mem_if_raddr_i,
    input logic [SK_MEM_BANK_DATA_W-1:0]               pi_sk_bank1_mem_if_rdata_o,
    input logic                                        po_sig_z_mem_if_we_i,
    input logic [SIG_Z_MEM_ADDR_W-1:0]                 po_sig_z_mem_if_waddr_i,
    input logic [SIG_Z_MEM_DATA_W-1:0]                 po_sig_z_mem_if_wdata_i,
    input logic [SIG_Z_MEM_DATA_W/8-1:0]               po_sig_z_mem_if_wstrobe_i,
    input logic                                        po_sig_z_mem_if_re_i,
    input logic [SIG_Z_MEM_ADDR_W-1:0]                 po_sig_z_mem_if_raddr_i,
    input logic [SIG_Z_MEM_DATA_W-1:0]                 pi_sig_z_mem_if_rdata_o,
    input logic                                        po_pk_mem_if_we_i,
    input logic [PK_MEM_ADDR_W-1:0]                    po_pk_mem_if_waddr_i,
    input logic [PK_MEM_DATA_W-1:0]                    po_pk_mem_if_wdata_i,
    input logic [PK_MEM_DATA_W/8-1:0]                  po_pk_mem_if_wstrobe_i,
    input logic                                        po_pk_mem_if_re_i,
    input logic [PK_MEM_ADDR_W-1:0]                    po_pk_mem_if_raddr_i,
    `ifdef CALIPTRA
    // KV interface
    input kv_read_t [2:0]                                               po_kv_read,
    input kv_rd_resp_t [2:0]                                            pi_kv_rd_resp,
    input kv_write_t                                                    po_kv_write,
    input kv_wr_resp_t                                                  pi_kv_wr_resp,
    //PCR Signing
    input pcr_signing_t                                                 pi_pcr_signing_data,
    input logic                                                         pi_ocp_lock_in_progress,
    `endif
    input logic [PK_MEM_DATA_W-1:0]                    pi_pk_mem_if_rdata_o
    //$#//
   

);

    // Define default clock
    default clocking default_clk @(posedge pi_clk); endclocking

//-------------------------Constrain primary inputs-------------------------------------
     // Aux logic to track if compress is enabled
     // And reset when the compress is done.
     logic compress_en;
     always_ff @(posedge pi_clk, negedge pi_rst_b) begin : compress_en_logic
            if (!pi_rst_b || po_zeroize) begin
                compress_en <= 1'b0;
            end else if (po_compress_enable_o) begin
                compress_en <= 1'b1;
            end else if (pi_compress_done_i) begin
                compress_en <= 1'b0;
            end
        end
    // Done signal could assert only if enable is triggered previously.
      assume_compress_done: assume property(
            pi_compress_done_i |-> (compress_en)
        );
    `ifdef EVENTUAL_ASSUME
        assume_compress_done_eventually: assume property(
                s_eventually(pi_compress_done_i)
            );
    `else
    // To minisise the time delay for the operation by the 
    // External block, we assume that the done signal will be
    // Asserted within FV_ADAMSBRIDGE_AUX_DLY cycles after the
    // Enable signal is asserted.
     assume_compress_done_in_dly: assume property (
        po_compress_enable_o 
        |->
        ## FV_ADAMSBRIDGE_AUX_DLY pi_compress_done_i
     );
     `endif

     // Compress compare failed signal is asserted
     // if compare mode is selected previously when enabled.
     assume_compress_compare_failed: assume property(
            (pi_compress_compare_failed_i) |-> (compress_en && po_compress_compare_mode_o)
        );

    // API read and write enable signals can be asserted
    // only if compress is enabled.
         assume_compress_api_rw_en_read_0: assume property(
            (pi_compress_api_rw_en_i[0]) |-> (compress_en)
        );

         assume_compress_api_rw_en_write_0: assume property(
            (pi_compress_api_rw_en_i[0]) |-> (compress_en)
        );

        assume_compress_api_rw_en_read_1: assume property(
            (pi_compress_api_rw_en_i[1] ) |-> (compress_en)
        );

         assume_compress_api_rw_en_write_1: assume property(
            (pi_compress_api_rw_en_i[1]) |-> (compress_en)
        );


    // Aux logic to track if decompress is enabled
    // And reset when the decompress is done.
    logic decompress_en;
        always_ff @(posedge pi_clk, negedge pi_rst_b) begin : decompress_en_logic
            if (!pi_rst_b || po_zeroize) begin
                decompress_en <= 1'b0;
            end else if (po_decompress_enable_o) begin
                decompress_en <= 1'b1;
            end else if (pi_decompress_done_i) begin
                decompress_en <= 1'b0;
            end
        end

    // Done signal could assert only if enable is triggered previously.
    assume_decompress_done: assume property(
            pi_decompress_done_i |-> (decompress_en)
        );
    `ifdef EVENTUAL_ASSUME
        assume_decompress_done_eventually: assume property(
                s_eventually(pi_decompress_done_i)
            );
    `else
        // To minisise the time delay for the operation by the 
        // External block, we assume that the done signal will be
        // Asserted within FV_ADAMSBRIDGE_AUX_DLY cycles after the
        // Enable signal is asserted.
        assume_decompress_done_in_dly: assume property (
            po_decompress_enable_o 
            |->
            ## FV_ADAMSBRIDGE_AUX_DLY pi_decompress_done_i
        );
    `endif

    // API read enable signals can be asserted
    // only if decompress is enabled.
    assume_decompress_api_rd_en: assume property(
        pi_decompress_api_rd_en_i |-> (decompress_en)
    );


    // Sampler busy signal should be high if sampler is started
    // And should remain high for FV_ADAMSBRIDGE_BUSY_CNTR cycles
    // After that it should go low.
    logic sampler_enabled;
    logic [FV_ADAMSBRIDGE_BUSY_CNTR-1:0] sampler_busy_cntr;
    always_ff @(posedge pi_clk, negedge pi_rst_b) begin : sampler_enabled_tracking
        if (!pi_rst_b || po_zeroize) begin
            sampler_enabled <= 1'b0;
            sampler_busy_cntr <= '0;
        end else begin
            if (po_sampler_start_o) begin
                sampler_enabled <= 1'b1;
                sampler_busy_cntr <= FV_ADAMSBRIDGE_BUSY_CNTR;
            end else if (sampler_enabled &&( sampler_busy_cntr == '0)) begin
                sampler_enabled <= 1'b0;
            end
            if(sampler_enabled &&( sampler_busy_cntr != '0)) begin
                sampler_busy_cntr <= sampler_busy_cntr -1;
            end
        end
    end

    // Assume the busy signal is correct
    assume_sampler_busy_i_2: assume property(
        pi_sampler_busy_i == sampler_enabled
    );



    // NTT busy signal should be high if NTT is enabled
    // And should remain high for FV_ADAMSBRIDGE_BUSY_CNTR cycles
    // After that it should go low.
    logic ntt_enabled;
    logic [FV_ADAMSBRIDGE_BUSY_CNTR-1:0] ntt_busy_cntr;

    always_ff @(posedge pi_clk, negedge pi_rst_b) begin : ntt_enabled_tracking
        if (!pi_rst_b) begin
            ntt_enabled <= 1'b0;
            ntt_busy_cntr <= '0;
        end else begin
            if (po_ntt_enable_o) begin
                ntt_enabled <= 1'b1;
                ntt_busy_cntr <= FV_ADAMSBRIDGE_BUSY_CNTR;
            end else if (ntt_enabled && (ntt_busy_cntr == '0)) begin
                ntt_enabled <= 1'b0;
            end
            if (ntt_enabled && (ntt_busy_cntr != '0)) begin
                ntt_busy_cntr <= ntt_busy_cntr - 1;
            end
        end
    end

    // Assume the busy signal is correct
    assume_ntt_busy_i_2: assume property(
        pi_ntt_busy_i == ntt_enabled
    );



    // Sampler data valid signal should be high if sampler is started
    // And it should always be a pulse.
 logic sample_dv;
     always_ff @(posedge pi_clk, negedge pi_rst_b) begin : sample_dv_logic
            if (!pi_rst_b || po_zeroize) begin
                sample_dv <= 1'b0;
            end else if (po_sha3_start_o) begin
                sample_dv <= 1'b1;
            end else if (sampler_busy_cntr==1) begin
                sample_dv <= 1'b0;
            end
        end
    // Assume the data valid signal is correct if sampler is busy and started
    assume_sampler_dv: assume property(
          pi_sampler_state_dv_i |-> (sample_dv && (pi_sampler_busy_i))
      );

    // Assume the data valid signal is a pulse
    assume_sampler_valid_pulse: assume property(
        pi_sampler_state_dv_i |-> ##1 !pi_sampler_state_dv_i
    );

    //When no data valid, data should be zero
    assume_sampler_data_stable: assume property(
        !pi_sampler_state_dv_i |-> (pi_sampler_state_data_i == '0)
    );



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

//assume_no_mldsa_aux_units: assume property(no_mldsa_aux_units);


// MLDSA aux units
//

//-------------------------Constrain primary inputs-------------------------------------
     logic sigdecode_z_en;
     always_ff @(posedge pi_clk, negedge pi_rst_b) begin : sigdecode_z_en_logic
            if (!pi_rst_b || po_zeroize) begin
                sigdecode_z_en <= 1'b0;
            end else if (po_sigdecode_z_enable_o) begin
                sigdecode_z_en <= 1'b1;
            end else if (pi_sigdecode_z_done_i) begin
                sigdecode_z_en <= 1'b0;
            end
        end

      assume_sigdecode_z_done: assume property(
            pi_sigdecode_z_done_i |-> (sigdecode_z_en)
        );
    `ifdef EVENTUAL_ASSUME
        assume_sigdecode_z_done_eventually: assume property(
                s_eventually(pi_sigdecode_z_done_i)
            );
    `else
     assume_sigdecode_z_done_in_dly: assume property (
        po_sigdecode_z_enable_o 
        |->
        ## FV_ADAMSBRIDGE_AUX_DLY pi_sigdecode_z_done_i
     );
     `endif

      logic sigdecode_h_en;
     always_ff @(posedge pi_clk, negedge pi_rst_b) begin : sigdecode_h_en_logic
            if (!pi_rst_b || po_zeroize) begin
                sigdecode_h_en <= 1'b0;
            end else if (po_sigdecode_h_enable_o) begin
                sigdecode_h_en <= 1'b1;
            end else if (pi_sigdecode_h_done_i) begin
                sigdecode_h_en <= 1'b0;
            end
        end

      assume_sigdecode_h_done: assume property(
            pi_sigdecode_h_done_i |-> (sigdecode_h_en)
        );
     `ifdef EVENTUAL_ASSUME
        assume_sigdecode_h_done_eventually: assume property(
               s_eventually(pi_sigdecode_h_done_i)
           );
         `else

        assume_sigdecode_h_done_in_dly: assume property (
            po_sigdecode_h_enable_o 
            |->
            ## FV_ADAMSBRIDGE_AUX_DLY pi_sigdecode_h_done_i
        );
        `endif
     logic pkdecode_en;
     always_ff @(posedge pi_clk, negedge pi_rst_b) begin : pkdecode_en_logic
            if (!pi_rst_b || po_zeroize) begin
                pkdecode_en <= 1'b0;
            end else if (po_pkdecode_enable_o) begin
                pkdecode_en <= 1'b1;
            end else if (pi_pkdecode_done_i) begin
                pkdecode_en <= 1'b0;
            end
        end

      assume_pkdecode_done: assume property(
            pi_pkdecode_done_i |-> (pkdecode_en)
        );
    `ifdef EVENTUAL_ASSUME
      assume_pkdecode_done_eventually: assume property(
            s_eventually(pi_pkdecode_done_i)
        );
    `else
     assume_pkdecode_done_in_dly: assume property (
        po_pkdecode_enable_o 
        |->
        ## FV_ADAMSBRIDGE_AUX_DLY pi_pkdecode_done_i
     );
        `endif

        logic sigencode_en;
     always_ff @(posedge pi_clk, negedge pi_rst_b) begin : sigencode_en_logic
            if (!pi_rst_b || po_zeroize) begin
                sigencode_en <= 1'b0;
            end else if (po_sigencode_enable_o) begin
                sigencode_en <= 1'b1;
            end else if (pi_sigencode_done_i) begin
                sigencode_en <= 1'b0;
            end
        end

      assume_sigencode_done: assume property(
            pi_sigencode_done_i |-> (sigencode_en)
        );
    `ifdef EVENTUAL_ASSUME
        assume_sigencode_done_eventually: assume property(
            s_eventually(pi_sigencode_done_i)
        );
    `else

    assume_sigencode_done_in_dly: assume property (
        po_sigencode_enable_o 
        |->
        ## FV_ADAMSBRIDGE_AUX_DLY pi_sigencode_done_i
     );
    `endif

    logic normcheck_enabled;

    always_ff @(posedge pi_clk) begin : normcheck_enabled_tracking
        if (!pi_rst_b) begin
            normcheck_enabled <= 1'b0;
        end else if (po_normcheck_enable_o) begin
            normcheck_enabled <= 1'b1;
        end else if (pi_normcheck_done_i) begin
            normcheck_enabled <= 1'b0;
        end
    end

     assume_normcheck_invalid_i: assume property(
        // disable iff(!pi_rst_b)
        !pi_normcheck_done_i
    |->
        $stable(pi_normcheck_invalid_i)
    );

     assume_normcheck_done: assume property(
            pi_normcheck_done_i |-> (normcheck_enabled )
        );
    `ifdef EVENTUAL_ASSUME
     assume_normcheck_done_eventually: assume property(
            s_eventually(pi_normcheck_done_i)
        );
    `else
    assume_normcheck_done_in_dly: assume property (
        po_normcheck_enable_o
        |->
        ## FV_ADAMSBRIDGE_AUX_DLY pi_normcheck_done_i
     );
     `endif
    logic makehint_enabled;

    always_ff @(posedge pi_clk) begin : makehint_enabled_tracking
        if (!pi_rst_b) begin
            makehint_enabled <= 1'b0;
        end else if (po_makehint_enable_o) begin
            makehint_enabled <= 1'b1;
        end else if (pi_makehint_done_i) begin
            makehint_enabled <= 1'b0;
        end
    end

    assume_makehint_invalid_i: assume property(
        // disable iff(!pi_rst_b)
        !pi_makehint_done_i
    |->
        $stable(pi_makehint_invalid_i)
    );

     assume_makehint_done: assume property(
            pi_makehint_done_i |-> (makehint_enabled )
        );
         assume_makehint_wren: assume property(
            pi_makehint_reg_wren_i |-> (makehint_enabled )
        );

    `ifdef EVENTUAL_ASSUME
     assume_makehint_done_eventually: assume property(
           s_eventually (pi_makehint_done_i)
        );
    `else
     assume_makehint_done_in_dly: assume property (
        po_makehint_enable_o
        |->
        ##FV_ADAMSBRIDGE_AUX_DLY pi_makehint_done_i
     );
    `endif
    assume_makehint_req_addr_range: assume property(
        pi_makehint_reg_wr_addr_i >= 0 && pi_makehint_reg_wr_addr_i < SIGNATURE_H_NUM_DWORDS
    );

   

 logic pwr2rnd_en;
     always_ff @(posedge pi_clk, negedge pi_rst_b) begin : pwr2rnd_en_logic
            if (!pi_rst_b || po_zeroize) begin
                pwr2rnd_en <= 1'b0;
            end else if (po_power2round_enable_o) begin
                pwr2rnd_en <= 1'b1;
            end else if (pi_power2round_done_i) begin
                pwr2rnd_en <= 1'b0;
            end
        end

      assume_power2round_done: assume property(
            pi_power2round_done_i |-> (pwr2rnd_en) // dont trigger when enable 
        );

    `ifdef EVENTUAL_ASSUME
      assume_power2round_done_eventually: assume property(
            s_eventually(pi_power2round_done_i) // dont trigger when enable 
        );
    `else

    assume_pwr2rnd_in_2cycles: assume property (
        po_power2round_enable_o 
        |->
        ##FV_ADAMSBRIDGE_AUX_DLY pi_power2round_done_i
    );
    `endif

    assume_pwr2rnd_mem_0: assume property(
        (pi_pwr2rnd_keymem_if_i[0].rd_wr_en == RW_WRITE) |-> (pwr2rnd_en)
    );

     assume_pwr2rnd_mem_1: assume property(
        (pi_pwr2rnd_keymem_if_i[1].rd_wr_en == RW_WRITE) |-> (pwr2rnd_en)
    );
    assume_pwr2rnd_api_wren: assume property(
        (pi_pk_t1_wren_i) |-> (pwr2rnd_en)
    );

 logic decompose_en;
     always_ff @(posedge pi_clk, negedge pi_rst_b) begin : decompose_en_logic
            if (!pi_rst_b || po_zeroize) begin
                decompose_en <= 1'b0;
            end else if (po_decompose_enable_o) begin
                decompose_en <= 1'b1;
            end else if (pi_decompose_done_i) begin
                decompose_en <= 1'b0;
            end
        end

      assume_decompose_done: assume property(
            pi_decompose_done_i |-> (decompose_en)
        );
    `ifdef EVENTUAL_ASSUME
      assume_decompose_done_eventually: assume property(
            s_eventually(pi_decompose_done_i)
        );
    `else
    assume_decompose_done_2cycles: assume property (
        po_decompose_enable_o 
        |->
        ##FV_ADAMSBRIDGE_AUX_DLY pi_decompose_done_i
    );
    `endif
   
 logic skencode_en;
     always_ff @(posedge pi_clk, negedge pi_rst_b) begin : skencode_en_logic
            if (!pi_rst_b || po_zeroize) begin
                skencode_en <= 1'b0;
            end else if (po_skencode_enable_o) begin
                skencode_en <= 1'b1;
            end else if (pi_skencode_done_i) begin
                skencode_en <= 1'b0;
            end
        end

      assume_skencode_done: assume property(
            pi_skencode_done_i |-> (skencode_en)
        );
    `ifdef EVENTUAL_ASSUME
        assume_skencode_done_eventually: assume property(
            s_eventually(pi_skencode_done_i)
        );
    `else

    assume_skencode_done_2cycles: assume property (
        po_skencode_enable_o 
        |->
        ##FV_ADAMSBRIDGE_AUX_DLY pi_skencode_done_i
    );
    `endif

    assume_skencode_mem_wr: assume property (
        (pi_skencode_keymem_if_i.rd_wr_en == RW_WRITE) |-> (skencode_en)
    );

 logic skdecode_en;
     always_ff @(posedge pi_clk, negedge pi_rst_b) begin : skdecode_en_logic
            if (!pi_rst_b || po_zeroize) begin
                skdecode_en <= 1'b0;
            end else if (po_skdecode_enable_o) begin
                skdecode_en <= 1'b1;
            end else if (pi_skdecode_done_i) begin
                skdecode_en <= 1'b0;
            end
        end

      assume_skdecode_done: assume property(
            pi_skdecode_done_i |-> (skdecode_en)
        );

    assume_error_when_enabled_only: assume property(
        pi_skdecode_error_i |-> (skdecode_en)
    );
    `ifdef EVENTUAL_ASSUME
        assume_skdecode_done_eventually: assume property(
            s_eventually(pi_skdecode_done_i)
        );
    `else

    assume_skdecode_done_2cycles: assume property (
        po_skdecode_enable_o 
        |->
        ##FV_ADAMSBRIDGE_AUX_DLY pi_skdecode_done_i
    );
    `endif
        assume_skdecode_mem_0: assume property(
            (pi_skdecode_keymem_if_i[0].rd_wr_en == RW_READ) |-> (skdecode_en)
        );

         assume_skdecode_mem_1: assume property(
            (pi_skdecode_keymem_if_i[1].rd_wr_en == RW_READ) |-> (skdecode_en)
        );

//-------------------------Constrain for MSG interface-------------------------------------//

    // When the stream msg is valid and ready is low, the stream msg should be stable
 property stream_valid_stable_if_no_ready_P;
        !po_abr_reg_hwif_in_o.MLDSA_MSG[0].MSG.swwe &&// ready
        pi_abr_reg_hwif_out_i.MLDSA_MSG[0].MSG.swmod  //valid
        |=>
        //$stable(pi_abr_reg_hwif_out_i.MLDSA_MSG[0].MSG.swmod) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_MSG[0].MSG.value)
    ;endproperty

    //assume_stream_valid_stable_if_no_ready_P: assume property(stream_valid_stable_if_no_ready_P);

    // The stream msg input valid should have atleast a clk cycle gap between the valids
    property stream_valid_toggles_min_P;
        //po_abr_reg_hwif_in_o.MLDSA_MSG[0].MSG.swwe && // ready
        pi_abr_reg_hwif_out_i.MLDSA_MSG[0].MSG.swmod //valid
        |=>
        !pi_abr_reg_hwif_out_i.MLDSA_MSG[0].MSG.swmod
    ;endproperty

    assume_stream_valid_toggles_min_P: assume property(stream_valid_toggles_min_P);


    // Fairness constraints such that we could leave the MSG_LOAD state at some point
    logic fv_stream_msg_valid_reg;
    always_ff @(posedge pi_clk, negedge pi_rst_b) begin: fv_flop_valid
        if(!pi_rst_b) begin
        end
        else begin
            fv_stream_msg_valid_reg <= pi_abr_reg_hwif_out_i.MLDSA_MSG[0].MSG.swmod;
        end
    end

    property eventually_stream_valid_msg_P;
        po_abr_reg_hwif_in_o.MLDSA_MSG[0].MSG.swwe // ready
         //valid
        |->
        s_eventually(fv_stream_msg_valid_reg &&
        (pi_abr_reg_hwif_out_i.MLDSA_MSG_STROBE.STROBE.value inside {4'b0000, 4'b0001, 4'b0011, 4'b0111}))
    ;endproperty

    assume_eventually_stream_valid_msg_P: assume property(eventually_stream_valid_msg_P);
    
    property stream_valid_msg_P;
        po_abr_reg_hwif_in_o.MLDSA_MSG[0].MSG.swwe // ready
         //valid
        |->
        ##FV_ADAMSBRIDGE_CNTRL_RDY_DELAY pi_abr_reg_hwif_out_i.MLDSA_MSG[0].MSG.swmod
    ;endproperty
    //assume_stream_valid_msg_P: assume property(stream_valid_msg_P);

        logic [4:0] fv_msg_rdy_counter;
        lubis_incr_decr_counter_m #(
        .INCR_VAL_WIDTH(2),
        .COUNTER_WIDTH (5),
        .NUM_INC_SRCS  (1)       
        ) fv_counter_msg_rdy_inst
        (
            .clk           (pi_clk      ),
            .rst           (!pi_rst_b ),
            .soft_rst      (po_zeroize || (fv_msg_rdy_counter == 16 && !(po_msg_valid_o &&
            po_msg_strobe_o != '1))|| (fv_msg_rdy_counter == 17)),
            .incr_en       (`abr_ctrl.abr_ctrl_fsm_ns == ABR_CTRL_MSG_LOAD),
            .decr_en       (1'b0      ),
            .incr_val      (po_msg_valid_o),
            .decr_val      ('0        ),
            .count         (fv_msg_rdy_counter),
            .count_next    (/* open */)
        );

        property msg_rdy_counter_based_P;
            fv_msg_rdy_counter != 16 ||
            (fv_msg_rdy_counter == 16 && po_msg_valid_o &&
            po_msg_strobe_o != '1) // partial buffer an extra buffer in the keccak
            |->
            pi_msg_rdy_i
        ;endproperty

        assume_msg_rdy_counter_based_P: assume property(msg_rdy_counter_based_P);

    cover_fv_msg_counter_reach_17: cover property(disable iff(!pi_rst_b || po_zeroize) fv_msg_rdy_counter == 17);


    property strobe_has_no_bubbles_P;
        pi_abr_reg_hwif_out_i.MLDSA_MSG_STROBE.STROBE.value inside {4'b0000, 4'b0001, 4'b0011, 4'b0111, 4'b1111}
    ;endproperty

    assume_strobe_has_no_bubbles_P: assume property(strobe_has_no_bubbles_P);

///////////////////////////////////
// cmd registers mutually exclusive
// The cmd registers are mutually exclusive, i.e., only one of them can be set at
// a time. This is to ensure that only one operation is triggered at a time.
// The properties below ensure that the cmd registers are mutually exclusive.

// these should be cleared by hwclr and look for process signals

// MLDSA control registers are stable during the operation
// i.e., when abr_ready is low.
assume_hwif_out_mldsa_value_i_stable: assume property(
        !po_abr_reg_hwif_in_o.abr_ready
    |->
    ##1
        $stable(pi_abr_reg_hwif_out_i.MLDSA_CTRL.CTRL.value)  &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_CTRL.PCR_SIGN.value) &&
        $stable(pi_abr_reg_hwif_out_i.ABR_ENTROPY[0].ENTROPY.value) &&
        $stable(pi_abr_reg_hwif_out_i.ABR_ENTROPY[1].ENTROPY.value) &&
        $stable(pi_abr_reg_hwif_out_i.ABR_ENTROPY[2].ENTROPY.value) &&
        $stable(pi_abr_reg_hwif_out_i.ABR_ENTROPY[3].ENTROPY.value) &&
        $stable(pi_abr_reg_hwif_out_i.ABR_ENTROPY[4].ENTROPY.value) &&
        $stable(pi_abr_reg_hwif_out_i.ABR_ENTROPY[5].ENTROPY.value) &&
        $stable(pi_abr_reg_hwif_out_i.ABR_ENTROPY[6].ENTROPY.value) &&
        $stable(pi_abr_reg_hwif_out_i.ABR_ENTROPY[7].ENTROPY.value) &&
        $stable(pi_abr_reg_hwif_out_i.ABR_ENTROPY[8].ENTROPY.value) &&
        $stable(pi_abr_reg_hwif_out_i.ABR_ENTROPY[9].ENTROPY.value) &&
        $stable(pi_abr_reg_hwif_out_i.ABR_ENTROPY[10].ENTROPY.value) &&
        $stable(pi_abr_reg_hwif_out_i.ABR_ENTROPY[11].ENTROPY.value) &&
        $stable(pi_abr_reg_hwif_out_i.ABR_ENTROPY[12].ENTROPY.value) &&
        $stable(pi_abr_reg_hwif_out_i.ABR_ENTROPY[13].ENTROPY.value) &&
        $stable(pi_abr_reg_hwif_out_i.ABR_ENTROPY[14].ENTROPY.value) &&
        $stable(pi_abr_reg_hwif_out_i.ABR_ENTROPY[15].ENTROPY.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_SIGN_RND[0].SIGN_RND.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_SIGN_RND[1].SIGN_RND.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_SIGN_RND[2].SIGN_RND.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_SIGN_RND[3].SIGN_RND.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_SIGN_RND[4].SIGN_RND.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_SIGN_RND[5].SIGN_RND.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_SIGN_RND[6].SIGN_RND.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_SIGN_RND[7].SIGN_RND.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_MSG[0].MSG.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_MSG[1].MSG.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_MSG[2].MSG.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_MSG[3].MSG.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_MSG[4].MSG.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_MSG[5].MSG.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_MSG[6].MSG.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_MSG[7].MSG.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_MSG[8].MSG.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_MSG[9].MSG.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_MSG[10].MSG.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_MSG[11].MSG.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_MSG[12].MSG.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_MSG[13].MSG.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_MSG[14].MSG.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_MSG[15].MSG.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_VERIFY_RES[0].VERIFY_RES.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_VERIFY_RES[1].VERIFY_RES.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_VERIFY_RES[2].VERIFY_RES.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_VERIFY_RES[3].VERIFY_RES.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_VERIFY_RES[4].VERIFY_RES.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_VERIFY_RES[5].VERIFY_RES.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_VERIFY_RES[6].VERIFY_RES.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_VERIFY_RES[7].VERIFY_RES.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_VERIFY_RES[8].VERIFY_RES.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_VERIFY_RES[9].VERIFY_RES.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_VERIFY_RES[10].VERIFY_RES.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_VERIFY_RES[11].VERIFY_RES.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_VERIFY_RES[12].VERIFY_RES.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_VERIFY_RES[13].VERIFY_RES.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_VERIFY_RES[14].VERIFY_RES.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_VERIFY_RES[15].VERIFY_RES.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_EXTERNAL_MU[0].EXTERNAL_MU.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_EXTERNAL_MU[1].EXTERNAL_MU.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_EXTERNAL_MU[2].EXTERNAL_MU.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_EXTERNAL_MU[3].EXTERNAL_MU.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_EXTERNAL_MU[4].EXTERNAL_MU.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_EXTERNAL_MU[5].EXTERNAL_MU.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_EXTERNAL_MU[6].EXTERNAL_MU.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_EXTERNAL_MU[7].EXTERNAL_MU.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_EXTERNAL_MU[8].EXTERNAL_MU.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_EXTERNAL_MU[9].EXTERNAL_MU.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_EXTERNAL_MU[10].EXTERNAL_MU.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_EXTERNAL_MU[11].EXTERNAL_MU.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_EXTERNAL_MU[12].EXTERNAL_MU.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_EXTERNAL_MU[13].EXTERNAL_MU.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_EXTERNAL_MU[14].EXTERNAL_MU.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_EXTERNAL_MU[15].EXTERNAL_MU.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_CTRL.EXTERNAL_MU.value) &&
        $stable(pi_abr_reg_hwif_out_i.MLDSA_CTX_CONFIG.CTX_SIZE.value)&&         // new interface
        $stable(pi_abr_reg_hwif_out_i.MLDSA_CTRL.STREAM_MSG.value)            //new interface

    );

    property hw_if_ctx_stable(i);
         !po_abr_reg_hwif_in_o.abr_ready
        |->
        ##1
         $stable(pi_abr_reg_hwif_out_i.MLDSA_CTX[i].CTX.value)
    ;endproperty
         for (genvar dword = 0; dword < CTX_NUM_DWORDS; dword++) begin
            assume_hw_if_ctx_stable: assume property(hw_if_ctx_stable(dword));
        end


// When MLKEM is enabled, MLDSA should be disabled.
// This is checked when abr_ready is high, i.e., when the control
// registers can be written.
//assume_disable_mldsa_when_mlkem_enabled: assume property(
//    po_abr_reg_hwif_in_o.abr_ready
//    |->
//    (pi_abr_reg_hwif_out_i.MLDSA_CTRL.CTRL.value == MLDSA_NONE)
//);
// End MLDSA constraints//////////////////////////////////////

///////////////////////////////////////////////////////////////////


// MLKEM control registers are stable during the operation
// i.e., when abr_ready is low.
    assume_hwif_out_mlkem_value_i_stable: assume property(
        !po_abr_reg_hwif_in_o.abr_ready
        |->
        ##1
            $stable(pi_abr_reg_hwif_out_i.MLKEM_CTRL.CTRL.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLKEM_STATUS.ERROR.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLKEM_SEED_D[0].SEED.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLKEM_SEED_D[1].SEED.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLKEM_SEED_D[2].SEED.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLKEM_SEED_D[3].SEED.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLKEM_SEED_D[4].SEED.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLKEM_SEED_D[5].SEED.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLKEM_SEED_D[6].SEED.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLKEM_SEED_D[7].SEED.value) &&
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
    );

    property mldsa_ctrl_clr_on_hwif_P;
        po_abr_reg_hwif_in_o.MLDSA_CTRL.CTRL.hwclr
        |->
        ##1
        (pi_abr_reg_hwif_out_i.MLDSA_CTRL.CTRL.value == '0)
    ;endproperty
    assume property(mldsa_ctrl_clr_on_hwif_P);

     property mlkem_ctrl_clr_on_hwif_P;
        po_abr_reg_hwif_in_o.MLKEM_CTRL.CTRL.hwclr
        |->
        ##1
        (pi_abr_reg_hwif_out_i.MLKEM_CTRL.CTRL.value == '0)
    ;endproperty
    assume property(mlkem_ctrl_clr_on_hwif_P);

    property mutually_exclusive_req_P;
        $onehot0({pi_abr_reg_hwif_out_i.MLKEM_ENCAPS_KEY.req,
        pi_abr_reg_hwif_out_i.MLKEM_DECAPS_KEY.req,
        pi_abr_reg_hwif_out_i.MLKEM_MSG.req,
        pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_IN.req,
        pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_OUT.req,
        pi_abr_reg_hwif_out_i.MLDSA_PUBKEY.req,
        pi_abr_reg_hwif_out_i.MLKEM_CIPHERTEXT.req,
        pi_abr_reg_hwif_out_i.MLDSA_SIGNATURE.req});
    endproperty
    assume property(mutually_exclusive_req_P);
        
    //-------------------------Constrain memory interface signals-------------------------------------//
    //Removed these and verified since latency is handled using shift registers
    // When there is no read request, the data should be stable
    property stable_data_no_req_P(req, data);
        !req
        |=>
        $stable(data)
    ;endproperty

    //assume_sk_mem_0_stable_data_no_req_P: assume property(stable_data_no_req_P(po_sk_bank0_mem_if_re_i,pi_sk_bank0_mem_if_rdata_o));
    //assume_sk_mem_1_stable_data_no_req_P: assume property(stable_data_no_req_P(po_sk_bank1_mem_if_re_i,pi_sk_bank1_mem_if_rdata_o));
    //assume_sig_z_mem_stable_data_no_req_P: assume property(stable_data_no_req_P(po_sig_z_mem_if_re_i,pi_sig_z_mem_if_rdata_o));
    //assume_pk_mem_stable_data_no_req_P: assume property(stable_data_no_req_P(po_pk_mem_if_re_i,pi_pk_mem_if_rdata_o));
 
     //-------------------------Constrain kv-------------------------------------//

     //MLDSA_CTRL, MLKEM_CTRL and kv_ctrl reg should be mutually exclusive
    assume_mldsa_mlkem_ctrl_kv_ctrl_mutually_exclusive: assume property(
        $onehot0({|pi_abr_reg_hwif_out_i.MLDSA_CTRL.CTRL.value, pi_abr_reg_hwif_out_i.kv_mldsa_seed_rd_ctrl.read_en.value,
                |pi_abr_reg_hwif_out_i.MLKEM_CTRL.CTRL.value, pi_abr_reg_hwif_out_i.kv_mlkem_seed_rd_ctrl.read_en.value, pi_abr_reg_hwif_out_i.kv_mlkem_msg_rd_ctrl.read_en.value})
    );

       //MLDSA_CTRL and kv_ctrl reg should be mutually exclusive
    assume_if_mldsa_ctrl_no_kv_mldsa_seed_rd_for_2_cycles: assume property(
        (pi_abr_reg_hwif_out_i.MLDSA_CTRL.CTRL.value != '0) ||
        (pi_abr_reg_hwif_out_i.MLKEM_CTRL.CTRL.value != '0 )
    |->
        (!pi_abr_reg_hwif_out_i.kv_mldsa_seed_rd_ctrl.read_en.value &&
        !pi_abr_reg_hwif_out_i.kv_mlkem_seed_rd_ctrl.read_en.value &&
        !pi_abr_reg_hwif_out_i.kv_mlkem_msg_rd_ctrl.read_en.value) [*2]
    );


    assume_if_kv_mldsa_seed_rd_no_mldsa_ctrl_for_2_cycles: assume property(
        pi_abr_reg_hwif_out_i.kv_mldsa_seed_rd_ctrl.read_en.value ||
        pi_abr_reg_hwif_out_i.kv_mlkem_seed_rd_ctrl.read_en.value ||
        pi_abr_reg_hwif_out_i.kv_mlkem_msg_rd_ctrl.read_en.value
    |->
        (pi_abr_reg_hwif_out_i.MLDSA_CTRL.CTRL.value == '0 &&
        pi_abr_reg_hwif_out_i.MLKEM_CTRL.CTRL.value == '0) [*2] 
    );
    //If swwe is not asserted, read_ctrl registers should be stable
    assume_kv_mldsa_seed_rd_ctrl_stable: assume property(
        !po_abr_reg_hwif_in_o.kv_mldsa_seed_rd_ctrl.read_en.swwe &&
        !po_abr_reg_hwif_in_o.kv_mldsa_seed_rd_ctrl.read_en.hwclr
    |->
        ##1 $stable(pi_abr_reg_hwif_out_i.kv_mldsa_seed_rd_ctrl.pcr_hash_extend.value) &&
            $stable(pi_abr_reg_hwif_out_i.kv_mldsa_seed_rd_ctrl.rsvd.value) &&
            $stable(pi_abr_reg_hwif_out_i.kv_mldsa_seed_rd_ctrl.read_en.value) &&
            $stable(pi_abr_reg_hwif_out_i.kv_mldsa_seed_rd_ctrl.read_entry.value)
    );


    //If hwclr is asserted, read_ctrl registers should be deasserted
    assume_kv_mldsa_seed_rd_ctrl_clear: assume property(
        po_abr_reg_hwif_in_o.kv_mldsa_seed_rd_ctrl.read_en.hwclr
    |->
        ##1 !pi_abr_reg_hwif_out_i.kv_mldsa_seed_rd_ctrl.read_entry.value &&
            !pi_abr_reg_hwif_out_i.kv_mldsa_seed_rd_ctrl.pcr_hash_extend.value &&
            !pi_abr_reg_hwif_out_i.kv_mldsa_seed_rd_ctrl.rsvd.value &&
            !pi_abr_reg_hwif_out_i.kv_mldsa_seed_rd_ctrl.read_en.value
    );

//MLDSA_SEED constraints to model abr_reg

    genvar fv_mldsa_seed_var;
    generate
        for(fv_mldsa_seed_var=0; fv_mldsa_seed_var<SEED_NUM_DWORDS; fv_mldsa_seed_var++) begin: fv_gen_mldsa_seed_constraints
            assume_mldsa_seed_stable: assume property(
                !po_abr_reg_hwif_in_o.MLDSA_SEED[fv_mldsa_seed_var].SEED.swwe && //SW write
                !po_abr_reg_hwif_in_o.MLDSA_SEED[fv_mldsa_seed_var].SEED.hwclr &&
                !po_abr_reg_hwif_in_o.MLDSA_SEED[fv_mldsa_seed_var].SEED.we     //HW write
            |->
                ##1 $stable(pi_abr_reg_hwif_out_i.MLDSA_SEED[fv_mldsa_seed_var].SEED.value)
            );

            assume_mldsa_seed_clear: assume property(
                po_abr_reg_hwif_in_o.MLDSA_SEED[fv_mldsa_seed_var].SEED.hwclr &&
                !po_abr_reg_hwif_in_o.MLDSA_SEED[fv_mldsa_seed_var].SEED.we &&
                !po_abr_reg_hwif_in_o.MLDSA_SEED[fv_mldsa_seed_var].SEED.swwe
            |->
                ##1 pi_abr_reg_hwif_out_i.MLDSA_SEED[fv_mldsa_seed_var].SEED.value == '0
            );

            assume_mldsa_seed_hwwrite: assume property(
                po_abr_reg_hwif_in_o.MLDSA_SEED[fv_mldsa_seed_var].SEED.we
            |->
                ##1 pi_abr_reg_hwif_out_i.MLDSA_SEED[fv_mldsa_seed_var].SEED.value == $past(po_abr_reg_hwif_in_o.MLDSA_SEED[fv_mldsa_seed_var].SEED.next)
            );
        end
    endgenerate


    //If swwe is not asserted, read_ctrl registers should be stable
    assume_kv_mlkem_seed_rd_ctrl_stable: assume property(
        !po_abr_reg_hwif_in_o.kv_mlkem_seed_rd_ctrl.read_en.swwe &&
        !po_abr_reg_hwif_in_o.kv_mlkem_seed_rd_ctrl.read_en.hwclr
    |->
        ##1 $stable(pi_abr_reg_hwif_out_i.kv_mlkem_seed_rd_ctrl.pcr_hash_extend.value) &&
            $stable(pi_abr_reg_hwif_out_i.kv_mlkem_seed_rd_ctrl.rsvd.value) &&
            $stable(pi_abr_reg_hwif_out_i.kv_mlkem_seed_rd_ctrl.read_en.value) &&
            $stable(pi_abr_reg_hwif_out_i.kv_mlkem_seed_rd_ctrl.read_entry.value)
    );




    //If hwclr is asserted, read_ctrl registers should be deasserted
    assume_kv_mlkem_seed_rd_ctrl_clear: assume property(
        po_abr_reg_hwif_in_o.kv_mlkem_seed_rd_ctrl.read_en.hwclr
    |->
        ##1 !pi_abr_reg_hwif_out_i.kv_mlkem_seed_rd_ctrl.read_entry.value &&
            !pi_abr_reg_hwif_out_i.kv_mlkem_seed_rd_ctrl.pcr_hash_extend.value &&
            !pi_abr_reg_hwif_out_i.kv_mlkem_seed_rd_ctrl.rsvd.value &&
            !pi_abr_reg_hwif_out_i.kv_mlkem_seed_rd_ctrl.read_en.value
    );

    //If swwe is not asserted, read_ctrl registers should be stable
    assume_kv_mlkem_msg_rd_ctrl_stable: assume property(
        !po_abr_reg_hwif_in_o.kv_mlkem_msg_rd_ctrl.read_en.swwe &&
        !po_abr_reg_hwif_in_o.kv_mlkem_msg_rd_ctrl.read_en.hwclr
    |->
        ##1 $stable(pi_abr_reg_hwif_out_i.kv_mlkem_msg_rd_ctrl.pcr_hash_extend.value) &&
            $stable(pi_abr_reg_hwif_out_i.kv_mlkem_msg_rd_ctrl.rsvd.value) &&
            $stable(pi_abr_reg_hwif_out_i.kv_mlkem_msg_rd_ctrl.read_en.value) &&
            $stable(pi_abr_reg_hwif_out_i.kv_mlkem_msg_rd_ctrl.read_entry.value)
    );




    //If hwclr is asserted, read_ctrl registers should be deasserted
    assume_kv_mlkem_msg_rd_ctrl_clear: assume property(
        po_abr_reg_hwif_in_o.kv_mlkem_msg_rd_ctrl.read_en.hwclr
    |->
        ##1 !pi_abr_reg_hwif_out_i.kv_mlkem_msg_rd_ctrl.read_entry.value &&
            !pi_abr_reg_hwif_out_i.kv_mlkem_msg_rd_ctrl.pcr_hash_extend.value &&
            !pi_abr_reg_hwif_out_i.kv_mlkem_msg_rd_ctrl.rsvd.value &&
            !pi_abr_reg_hwif_out_i.kv_mlkem_msg_rd_ctrl.read_en.value
    );

// if their is a req then the addr remains stable for the SRAM LATENCY
// IF thats not the case then the rd_data outputs from the PO of signature, pubkey and privkey
// will have the incorrect data since the ack are set after the SRAM latency.

    property stable_api_addr_P(req, rd_ack, addr);
        req &&
        !rd_ack
        |->
        ##1
        $stable(addr)
    ;endproperty

    assume_stable_mldsa_sig_api_addr: assume property(stable_api_addr_P(pi_abr_reg_hwif_out_i.MLDSA_SIGNATURE.req && !pi_abr_reg_hwif_out_i.MLDSA_SIGNATURE.req_is_wr,po_abr_reg_hwif_in_o.MLDSA_SIGNATURE.rd_ack,pi_abr_reg_hwif_out_i.MLDSA_SIGNATURE.addr));
    assume_stable_mldsa_pk_out_api_addr: assume property(stable_api_addr_P(pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_OUT.req && !pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_OUT.req_is_wr,po_abr_reg_hwif_in_o.MLDSA_PRIVKEY_OUT.rd_ack,pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_OUT.addr));
    assume_stable_mldsa_pubkey_out_api_addr: assume property(stable_api_addr_P(pi_abr_reg_hwif_out_i.MLDSA_PUBKEY.req && !pi_abr_reg_hwif_out_i.MLDSA_PUBKEY.req_is_wr,po_abr_reg_hwif_in_o.MLDSA_PUBKEY.rd_ack,pi_abr_reg_hwif_out_i.MLDSA_PUBKEY.addr));

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
            if(`abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_IDLE || `abr_ctrl.stream_msg_ip) begin
                fv_msg_cnt <= '0;
            end
            else if(`abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_MSG_LOAD && (((fv_msg_cnt == '0)|| (fv_msg_cnt == `abr_ctrl.abr_instr.length[ABR_OPR_WIDTH-1:$clog2(MsgStrbW)]-1) || (fv_msg_cnt == `abr_ctrl.abr_instr.length[ABR_OPR_WIDTH-1:$clog2(MsgStrbW)])))) begin
                fv_msg_cnt <= fv_msg_cnt + 1;
            end
            else if(`abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_MSG_LOAD && (fv_msg_cnt == 1) ) begin
                fv_msg_cnt <= `abr_ctrl.abr_instr.length[ABR_OPR_WIDTH-1:$clog2(MsgStrbW)]-1;
            end
            else begin
                 fv_msg_cnt <= '0;
            end
        end
    end

    // msg_cnt should be equal to the fv_msg_cnt
     property msg_cnt_abstracted_p;
         `abr_ctrl.msg_cnt == fv_msg_cnt
    ;endproperty
    assume_msg_cnt_abstracted_ASM: assume property(msg_cnt_abstracted_p);

    // Program counter should take only the valid values
    property abstract_abr_prog_cntr_P;
        (`abr_ctrl.abr_prog_cntr == ABR_RESET) ||
        (`abr_ctrl.abr_prog_cntr == ABR_ZEROIZE) ||
        ((`abr_ctrl.abr_prog_cntr >= MLKEM_KG_S) && (`abr_ctrl.abr_prog_cntr <= MLKEM_KG_E)) ||
        ((`abr_ctrl.abr_prog_cntr >= MLKEM_DECAPS_S) && (`abr_ctrl.abr_prog_cntr <= MLKEM_DECAPS_E)) ||
        ((`abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S) && (`abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_E)) ||
        ((`abr_ctrl.abr_prog_cntr  >= MLDSA_KG_S) && (`abr_ctrl.abr_prog_cntr <= MLDSA_KG_E)) ||
        ((`abr_ctrl.abr_prog_cntr  >= MLDSA_SIGN_S) && (`abr_ctrl.abr_prog_cntr <= MLDSA_SIGN_E)) ||
        ((`abr_ctrl.abr_prog_cntr  >= MLDSA_VERIFY_S) && (`abr_ctrl.abr_prog_cntr <= MLDSA_VERIFY_E))

    ;endproperty

    assume_abstract_abr_prog_cntr_ASM: assume property(abstract_abr_prog_cntr_P);

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
            if((`abr_ctrl.abr_prog_cntr >= MLDSA_KG_S) && (`abr_ctrl.abr_prog_cntr <= MLDSA_KG_E)) begin
                fv_keygen_set = 1;
            end
            if((`abr_ctrl.abr_prog_cntr >= MLDSA_SIGN_S) && (`abr_ctrl.abr_prog_cntr <= MLDSA_SIGN_E)) begin
                fv_signing_set = 1;
            end
            if((`abr_ctrl.abr_prog_cntr >= MLDSA_VERIFY_S) && (`abr_ctrl.abr_prog_cntr <= MLDSA_VERIFY_E)) begin
                fv_verify_set = 1;
            end
            if((`abr_ctrl.abr_prog_cntr >= MLKEM_KG_S) && (`abr_ctrl.abr_prog_cntr <= MLKEM_KG_E)) begin
                fv_mlkem_keygen_set = 1;
            end
            if((`abr_ctrl.abr_prog_cntr >= MLKEM_DECAPS_S) && (`abr_ctrl.abr_prog_cntr <= MLKEM_DECAPS_E)) begin
                fv_mlkem_decaps_set = 1;
            end
            if((`abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S) && (`abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_E)) begin
                fv_mlkem_encaps_set = 1;
            end

        end

    mlkem_cmd_e fv_mlkem_cmd_reg;
    // Process signals are set when the program counter is in the respective ranges
    // This is to avoid the first cycle of the process signal being unconstrained
    // due to the init value abstraction of the program counter
    property abstract_mlkem_init_value_prim_prog_cntr_P;
      `abr_ctrl.mlkem_keygen_process == (fv_mlkem_cmd_reg == MLKEM_KEYGEN && fv_mlkem_keygen_set) &&
      `abr_ctrl.mlkem_encaps_process == (fv_mlkem_cmd_reg == MLKEM_ENCAPS && fv_mlkem_encaps_set) &&
      `abr_ctrl.mlkem_decaps_process == ((fv_mlkem_cmd_reg == MLKEM_DECAPS && fv_mlkem_decaps_set) || (fv_mlkem_cmd_reg == MLKEM_KEYGEN_DEC && fv_mlkem_decaps_set)) &&
      `abr_ctrl.mlkem_keygen_decaps_process == (fv_mlkem_cmd_reg == MLKEM_KEYGEN_DEC)
    ;endproperty
    assume_abstract_mlkem_init_value_prim_prog_cntr_ASM: assume property(abstract_mlkem_init_value_prim_prog_cntr_P);

    mldsa_cmd_e fv_mldsa_cmd_reg;
    property abstract_mldsa_init_value_prim_prog_cntr_P;
      `abr_ctrl.mldsa_keygen_process == (fv_mldsa_cmd_reg == MLDSA_KEYGEN && fv_keygen_set) &&
      `abr_ctrl.mldsa_signing_process == ((fv_mldsa_cmd_reg == MLDSA_SIGN && fv_signing_set)|| (fv_mldsa_cmd_reg == MLDSA_KEYGEN_SIGN && fv_signing_set)) &&
      `abr_ctrl.mldsa_verifying_process == (fv_mldsa_cmd_reg == MLDSA_VERIFY && fv_verify_set) &&
      `abr_ctrl.mldsa_keygen_signing_process == (fv_mldsa_cmd_reg == MLDSA_KEYGEN_SIGN)
    ;endproperty
    assume_abstract_mldsa_init_value_prim_prog_cntr_ASM: assume property(abstract_mldsa_init_value_prim_prog_cntr_P);


    // Post reset it takes 1cycle to update the out of sequencer. Since in the init value abstartcion this 
    //would cause the first cycle to be unconstrained and the data_o could take any value triggering unnecessary
    // state transitions.
    property abstract_reset_value_P;
    $past(!pi_rst_b)
    |->
    `abr_ctrl.abr_seq_inst.data_o == '0
    ;endproperty
    assume_abstract_reset_value_P: assume property(abstract_reset_value_P);


    // This is used only incase of KV related checks since inorder to make sure KV interactions work
    // We need to check right before the engine starts and after the engine is done switching to a new cmd or mode
    // During the engine operation for KV is not expected to do anything.
    // Ideally with the full prog_cntr to achieve done state it needs hundreds of clk cycles
    // And IVA will not help since KV present signals are triggered at the engine start and holds till engine is done.

      logic [ABR_PROG_ADDR_W-1 : 0] fv_abr_prog_cntr,fv_abr_prog_cntr_nxt,fv_sym_state;

      always_comb begin
        fv_abr_prog_cntr_nxt = fv_abr_prog_cntr;
       
      if(fv_abr_prog_cntr == ABR_RESET) begin 
        // Waiting for new valid command
        unique case ({`abr_ctrl.mlkem_cmd_reg,`abr_ctrl.mldsa_cmd_reg}) inside
          {MLKEM_NONE,MLDSA_KEYGEN} : begin  // keygen
            fv_abr_prog_cntr_nxt = MLDSA_KG_S;
          end
          {MLKEM_NONE,MLDSA_SIGN} : begin  // signing
            fv_abr_prog_cntr_nxt = MLDSA_SIGN_S;
          end
          {MLKEM_NONE,MLDSA_VERIFY} : begin  // verifying
            fv_abr_prog_cntr_nxt = MLDSA_VERIFY_S;
          end
          {MLKEM_NONE,MLDSA_KEYGEN_SIGN} : begin  // KEYGEN + SIGNING 
            fv_abr_prog_cntr_nxt = MLDSA_KG_S;
          end
          {MLKEM_KEYGEN,MLDSA_NONE} : begin  // MLKEM KEYGEN
            fv_abr_prog_cntr_nxt = MLKEM_KG_S;
          end                    
          {MLKEM_ENCAPS,MLDSA_NONE} : begin  // MLKEM ENCAPS
            fv_abr_prog_cntr_nxt = MLKEM_ENCAPS_S;
          end
          {MLKEM_DECAPS,MLDSA_NONE} : begin  // MLKEM DECAPS
            fv_abr_prog_cntr_nxt = MLKEM_DECAPS_S;
          end
          {MLKEM_KEYGEN_DEC,MLDSA_NONE} : begin  // MLKEM DECAPS
            fv_abr_prog_cntr_nxt = MLKEM_KG_S;
          end
          default : begin
            fv_abr_prog_cntr_nxt = ABR_RESET;
          end
        endcase
      end
      else if(fv_abr_prog_cntr == ABR_ZEROIZE) begin
        if (`abr_ctrl.zeroize_mem_done)
          fv_abr_prog_cntr_nxt = ABR_RESET;
        else
          fv_abr_prog_cntr_nxt = ABR_ZEROIZE;
      end
      else if(((fv_abr_prog_cntr == MLDSA_KG_S) ||
                (fv_abr_prog_cntr == MLDSA_SIGN_S) ||
                (fv_abr_prog_cntr == MLDSA_VERIFY_S) ||
                (fv_abr_prog_cntr == MLKEM_KG_S) ||
                (fv_abr_prog_cntr == MLKEM_DECAPS_S) ||
                (fv_abr_prog_cntr == MLKEM_ENCAPS_S)) && !`abr_ctrl.subcomponent_busy) begin
                    fv_abr_prog_cntr_nxt = fv_sym_state;
     end
      else begin
        if((fv_abr_prog_cntr == fv_sym_state) && !`abr_ctrl.subcomponent_busy) begin
            unique case ({fv_mlkem_cmd_reg,fv_mldsa_cmd_reg}) inside
          {MLKEM_NONE,MLDSA_KEYGEN} : begin  // keygen
            fv_abr_prog_cntr_nxt = MLDSA_KG_E;
          end
          {MLKEM_NONE,MLDSA_SIGN} : begin  // signing
            fv_abr_prog_cntr_nxt = MLDSA_SIGN_E;
          end
          {MLKEM_NONE,MLDSA_VERIFY} : begin  // verifying
            fv_abr_prog_cntr_nxt = MLDSA_VERIFY_E;
          end
          {MLKEM_NONE,MLDSA_KEYGEN_SIGN} : begin  // KEYGEN + SIGNING 
            fv_abr_prog_cntr_nxt = MLDSA_SIGN_E;
          end
          {MLKEM_KEYGEN,MLDSA_NONE} : begin  // MLKEM KEYGEN
            fv_abr_prog_cntr_nxt = MLKEM_KG_E;
          end
          {MLKEM_ENCAPS,MLDSA_NONE} : begin  // MLKEM ENCAPS
            fv_abr_prog_cntr_nxt = MLKEM_ENCAPS_E;
          end
          {MLKEM_DECAPS,MLDSA_NONE} : begin  // MLKEM DECAPS
            fv_abr_prog_cntr_nxt = MLKEM_DECAPS_E;
          end
          {MLKEM_KEYGEN_DEC,MLDSA_NONE} : begin  // MLKEM DECAPS
            fv_abr_prog_cntr_nxt = MLKEM_DECAPS_E;
          end
          default : begin
            fv_abr_prog_cntr_nxt = ABR_RESET;
          end
        endcase
        end
        else begin
            fv_abr_prog_cntr_nxt = fv_abr_prog_cntr;
        end
      end
      end

    always_ff @(posedge pi_clk or negedge pi_rst_b) begin
        if(!pi_rst_b) begin
            fv_abr_prog_cntr <= ABR_RESET;
        end
        else if(po_zeroize) begin
            fv_abr_prog_cntr <= ABR_ZEROIZE;
        end
        else if (`abr_ctrl.error_flag_reg) begin
            fv_abr_prog_cntr <= ABR_ERROR;
        end else begin
            fv_abr_prog_cntr <= fv_abr_prog_cntr_nxt;
        end
    end
`ifdef KV_ABR_PROG
    always_ff @(posedge pi_clk or negedge pi_rst_b) begin
        if(!pi_rst_b || po_zeroize) begin
            fv_mldsa_cmd_reg <= MLDSA_NONE;
            fv_mlkem_cmd_reg <= MLKEM_NONE;
        end
        else if (`abr_ctrl.abr_ready) begin
            fv_mldsa_cmd_reg <= `abr_ctrl.mldsa_cmd_reg;
            fv_mlkem_cmd_reg <= `abr_ctrl.mlkem_cmd_reg;
        end
         else begin
            fv_mldsa_cmd_reg <= fv_mldsa_cmd_reg;
            fv_mlkem_cmd_reg <= fv_mlkem_cmd_reg;
        end
    end
`endif
  property sym_state_stable_P;
        !po_zeroize
        |->
        ##1
        $stable(fv_sym_state)
    ;endproperty
    assume_sym_state_stable_ASM: assume property(sym_state_stable_P);

`ifndef KV_ABR_PROG
    // ---------------------------------------------------------------
    // Auxiliary cmd_reg consistency: when the prog_cntr is inside a
    // particular operation's address range, the fv cmd_reg must
    // reflect a command that legitimately uses that range, and must
    // remain stable for the duration of the range.
    // ---------------------------------------------------------------

    // Post reset and zeroize cmd reg should be set to zero.
    property fv_post_reset_zeroize_cmd_P;
        (`abr_ctrl.abr_prog_cntr == ABR_RESET) || (`abr_ctrl.abr_prog_cntr == ABR_ZEROIZE)
        |->
        (fv_mldsa_cmd_reg == MLDSA_NONE && fv_mlkem_cmd_reg == MLKEM_NONE)
    ;endproperty
    assume_fv_post_reset_zeroize_cmd_ASM: assume property(fv_post_reset_zeroize_cmd_P);

    // MLDSA keygen range -> cmd must be KEYGEN or KEYGEN_SIGN (stable)
    property fv_keygen_set_cmd_P;
        fv_keygen_set
        |->
        fv_mldsa_cmd_reg inside {MLDSA_KEYGEN, MLDSA_KEYGEN_SIGN}
        ##1 $stable(fv_mldsa_cmd_reg)
    ;endproperty
    assume_fv_keygen_set_cmd_ASM: assume property(fv_keygen_set_cmd_P);

    // MLDSA signing range -> cmd must be SIGN or KEYGEN_SIGN (stable)
    property fv_signing_set_cmd_P;
        fv_signing_set
        |->
        fv_mldsa_cmd_reg inside {MLDSA_SIGN, MLDSA_KEYGEN_SIGN}
        ##1 $stable(fv_mldsa_cmd_reg)
    ;endproperty
    assume_fv_signing_set_cmd_ASM: assume property(fv_signing_set_cmd_P);

    // MLDSA verify range -> cmd must be VERIFY
    property fv_verify_set_cmd_P;
        fv_verify_set
        |->
        fv_mldsa_cmd_reg == MLDSA_VERIFY
        ##1 $stable(fv_mldsa_cmd_reg)
    ;endproperty
    assume_fv_verify_set_cmd_ASM: assume property(fv_verify_set_cmd_P);

    // MLKEM keygen range -> cmd must be MLKEM_KEYGEN or MLKEM_KEYGEN_DEC (stable)
    property fv_mlkem_keygen_set_cmd_P;
        fv_mlkem_keygen_set
        |->
        fv_mlkem_cmd_reg inside {MLKEM_KEYGEN, MLKEM_KEYGEN_DEC}
        ##1 $stable(fv_mlkem_cmd_reg)
    ;endproperty
    assume_fv_mlkem_keygen_set_cmd_ASM: assume property(fv_mlkem_keygen_set_cmd_P);

    logic fv_switch_to_mlkem_decaps;
    // MLKEM encaps range -> cmd must be MLKEM_ENCAPS
    property fv_mlkem_encaps_set_cmd_P;
        fv_mlkem_encaps_set && !fv_switch_to_mlkem_decaps
        |->
        fv_mlkem_cmd_reg == MLKEM_ENCAPS
        ##1 $stable(fv_mlkem_cmd_reg)
    ;endproperty
    assume_fv_mlkem_encaps_set_cmd_ASM: assume property(fv_mlkem_encaps_set_cmd_P);

    // MLKEM decaps range -> cmd must be MLKEM_DECAPS or MLKEM_KEYGEN_DEC (stable)
    property fv_mlkem_decaps_set_cmd_P;
        fv_mlkem_decaps_set && fv_switch_to_mlkem_decaps
        |->
        fv_mlkem_cmd_reg inside {MLKEM_DECAPS, MLKEM_KEYGEN_DEC}
        ##1 $stable(fv_mlkem_cmd_reg)
    ;endproperty
    assume_fv_mlkem_decaps_set_cmd_ASM: assume property(fv_mlkem_decaps_set_cmd_P);

    // Reset or zeroize -> mldsa cmd reg must be NONE
    property fv_no_mldsa_set_cmd_none_P;
        (`abr_ctrl.abr_prog_cntr == ABR_RESET) || (`abr_ctrl.abr_prog_cntr == ABR_ZEROIZE)
        |->
        fv_mldsa_cmd_reg == MLDSA_NONE
    ;endproperty
    assume_fv_no_mldsa_set_cmd_none_ASM: assume property(fv_no_mldsa_set_cmd_none_P);

    // Reset or zeroize -> mlkem cmd reg must be NONE
    property fv_no_mlkem_set_cmd_none_P;
        (`abr_ctrl.abr_prog_cntr == ABR_RESET) || (`abr_ctrl.abr_prog_cntr == ABR_ZEROIZE)
        |->
        fv_mlkem_cmd_reg == MLKEM_NONE
    ;endproperty
    assume_fv_no_mlkem_set_cmd_none_ASM: assume property(fv_no_mlkem_set_cmd_none_P);


    property fv_switch_to_mlkem_decaps_P;
        $stable(fv_switch_to_mlkem_decaps)
    ;endproperty
    assume_fv_switch_to_mlkem_decaps_ASM: assume property(fv_switch_to_mlkem_decaps_P);
`endif

      property abr_prog_cntr_mldsa_symbolic_P(start_state,cmd,end_state);
        fv_abr_prog_cntr == start_state &&
        cmd != MLDSA_KEYGEN_SIGN
        |->
        (fv_sym_state >= (start_state+1) && 
        fv_sym_state <= (end_state-1))
      ;endproperty

    property abr_prog_cntr_mlkem_symbolic_P(start_state,cmd,end_state);
        fv_abr_prog_cntr == start_state &&
        cmd != MLKEM_KEYGEN_DEC
        |->
        (fv_sym_state >= (start_state+1) && 
        fv_sym_state <= (end_state-1))
      ;endproperty

      property abr_prog_cntr_symbolic_mldsa_keygen_sign_P(start_state,cmd,end_state);
        fv_abr_prog_cntr == start_state &&
        cmd == MLDSA_KEYGEN_SIGN
        |->
        (fv_sym_state >= (start_state) && 
        fv_sym_state <= (end_state-1)) &&
        fv_sym_state != MLDSA_KG_E // Since in KEYGEN_SIGN mode it can directly go to SIGNING without going through the keygen state end state
        ;endproperty

      property abr_prog_cntr_symbolic_mlkem_keygen_dec_P(start_state,cmd,end_state);
        fv_abr_prog_cntr == start_state &&
        cmd == MLKEM_KEYGEN_DEC
        |->
        (fv_sym_state >= (start_state+1) && 
        fv_sym_state <= (end_state-1))
      ;endproperty
`ifdef KV_ABR_PROG
      assume_abr_prog_cntr_mldsa_kg_symbolic_ASM: assume property(abr_prog_cntr_mldsa_symbolic_P(MLDSA_KG_S,fv_mldsa_cmd_reg, MLDSA_KG_E));
      assume_abr_prog_cntr_mldsa_sign_symbolic_ASM: assume property(abr_prog_cntr_mldsa_symbolic_P(MLDSA_SIGN_S,fv_mldsa_cmd_reg, MLDSA_SIGN_E));
      assume_abr_prog_cntr_mldsa_verify_symbolic_ASM: assume property(abr_prog_cntr_mldsa_symbolic_P(MLDSA_VERIFY_S,fv_mldsa_cmd_reg, MLDSA_VERIFY_E));
      assume_abr_prog_cntr_mldsa_keygen_sign_symbolic_ASM: assume property(abr_prog_cntr_symbolic_mldsa_keygen_sign_P(MLDSA_KG_S,fv_mldsa_cmd_reg, MLDSA_SIGN_E));
      assume_abr_prog_cntr_mlkem_kg_symbolic_ASM: assume property(abr_prog_cntr_mlkem_symbolic_P(MLKEM_KG_S,fv_mlkem_cmd_reg, MLKEM_KG_E));
      assume_abr_prog_cntr_mlkem_keygen_dec_symbolic_ASM: assume property(abr_prog_cntr_symbolic_mlkem_keygen_dec_P(MLKEM_KG_S,fv_mlkem_cmd_reg, MLKEM_DECAPS_E));
      assume_abr_prog_cntr_mlkem_encaps_symbolic_ASM: assume property(abr_prog_cntr_mlkem_symbolic_P(MLKEM_ENCAPS_S,fv_mlkem_cmd_reg, MLKEM_ENCAPS_E));
      assume_abr_prog_cntr_mlkem_decaps_symbolic_ASM: assume property(abr_prog_cntr_mlkem_symbolic_P(MLKEM_DECAPS_S,fv_mlkem_cmd_reg, MLKEM_DECAPS_E));

        property abr_prog_cntr_dut_connect_P;
         `abr_ctrl.abr_prog_cntr == fv_abr_prog_cntr
      ;endproperty
      assume_abr_prog_cntr_dut_connect_ASM: assume property(abr_prog_cntr_dut_connect_P);
`endif
`else
    property prim_prog_cntr_P;
        (`abr_ctrl.abr_prog_cntr == ABR_RESET) ||
        (`abr_ctrl.abr_prog_cntr == ABR_ZEROIZE) ||
        (`abr_ctrl.abr_prog_cntr == ABR_ERROR) ||
        ((`abr_ctrl.abr_prog_cntr >= MLKEM_KG_S) && (`abr_ctrl.abr_prog_cntr <= MLKEM_KG_E)) ||
        ((`abr_ctrl.abr_prog_cntr >= MLKEM_DECAPS_S) && (`abr_ctrl.abr_prog_cntr <= MLKEM_DECAPS_E)) ||
        ((`abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S) && (`abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_E)) ||
        ((`abr_ctrl.abr_prog_cntr >= MLDSA_KG_S) && (`abr_ctrl.abr_prog_cntr <= MLDSA_KG_E)) ||
        ((`abr_ctrl.abr_prog_cntr >= MLDSA_SIGN_S) && (`abr_ctrl.abr_prog_cntr <= MLDSA_SIGN_E)) ||
        ((`abr_ctrl.abr_prog_cntr >= MLDSA_VERIFY_S) && (`abr_ctrl.abr_prog_cntr <= MLDSA_VERIFY_E))
    ;endproperty

    assert_prim_prog_cntr_A: assert property(disable iff(!pi_rst_b || po_zeroize) prim_prog_cntr_P);


`endif

    // Required since init value counter can start at a end state and trigger the valid
    // post that valid is resetted only if zeroize and in between cmds it is expected to have a zeroize
    // if thats not the case the proofs will fail, since the valid reg stays asserted.
     property zeroize_post_mlkem_valid;
        $rose(`abr_ctrl.mlkem_valid_reg)
        |=>
        ##FV_ADAMSBRIDGE_AUX_DLY
        pi_abr_reg_hwif_out_i.MLKEM_CTRL.ZEROIZE.value
        //!pi_rst_b
    ;endproperty
    assume_zeroize_post_mlkem_valid: assume property(zeroize_post_mlkem_valid);

    // Required since init value counter can start at a end state and trigger the valid
    // post that valid is resetted only if zeroize and in between cmds it is expected to have a zeroize
    // if thats not the case the proofs will fail, since the valid reg stays asserted.
    property zeroize_post_mldsa_valid;
        $rose(`abr_ctrl.mldsa_valid_reg)
        |=>
        ##FV_ADAMSBRIDGE_AUX_DLY
        pi_abr_reg_hwif_out_i.MLDSA_CTRL.ZEROIZE.value
        //!pi_rst_b
    ;endproperty
    assume_zeroize_post_mldsa_valid: assume property(zeroize_post_mldsa_valid);

// Zeroize should be a pulse of 1 cycle
    

    property zeroize_pulse_mldsa_P;
        pi_abr_reg_hwif_out_i.MLDSA_CTRL.ZEROIZE.value
        |->
        ##1 !pi_abr_reg_hwif_out_i.MLDSA_CTRL.ZEROIZE.value
    ;endproperty
    assume_zeroize_pulse_mldsa__ASM: assume property(zeroize_pulse_mldsa_P);


    property zeroize_pulse_mlkem_P;
        pi_abr_reg_hwif_out_i.MLKEM_CTRL.ZEROIZE.value
        |->
        ##1 !pi_abr_reg_hwif_out_i.MLKEM_CTRL.ZEROIZE.value
    ;endproperty
    assume_zeroize_pulse_mlkem__ASM: assume property(zeroize_pulse_mlkem_P);

     property zeroize_pulse_debug_P;
        pi_debugUnlock_or_scan_mode_switch
        |->
        ##1 !pi_debugUnlock_or_scan_mode_switch

    ;endproperty
    assume_zeroize_pulse_debug__ASM: assume property(zeroize_pulse_debug_P);

    property mldsa_pulse_valid_P;
        po_abr_reg_hwif_in_o.MLDSA_STATUS.VALID.next
        |=>
        pi_abr_reg_hwif_out_i.MLDSA_STATUS.VALID.value
    ;endproperty

    assume_mldsa_pulse_valid_ASM: assume property(mldsa_pulse_valid_P);

    property mldsa_no_pulse_valid_P;
        !po_abr_reg_hwif_in_o.MLDSA_STATUS.VALID.next
        |=>
        !pi_abr_reg_hwif_out_i.MLDSA_STATUS.VALID.value
    ;endproperty
    assume_mldsa_no_pulse_valid_ASM: assume property(mldsa_no_pulse_valid_P);

    property mlkem_pulse_valid_P;
        po_abr_reg_hwif_in_o.MLKEM_STATUS.VALID.next
        |=>
        pi_abr_reg_hwif_out_i.MLKEM_STATUS.VALID.value
    ;endproperty

    assume_mlkem_pulse_valid_ASM: assume property(mlkem_pulse_valid_P);

    property mlkem_no_pulse_valid_P;
        !po_abr_reg_hwif_in_o.MLKEM_STATUS.VALID.next
        |=>
        !pi_abr_reg_hwif_out_i.MLKEM_STATUS.VALID.value
    ;endproperty
    assume_mlkem_no_pulse_valid_ASM: assume property(mlkem_no_pulse_valid_P);

    ///Abstraction for the zeroize_mem_addr so that it takes only valid values
    // This is used when switching between the modes there will be zeroize triggering 
    // Mem clear which could last several clk cycles.

      logic [ABR_MEM_ADDR_WIDTH-1:0] fv_zeroize_mem_addr;
      always_ff @(posedge pi_clk or negedge pi_rst_b) begin
          if (!pi_rst_b) begin
            fv_zeroize_mem_addr <= 0;
          end
          else if (`abr_ctrl.abr_prog_cntr == ABR_ZEROIZE) begin
            if (fv_zeroize_mem_addr == ABR_MEM_MAX_DEPTH-1) begin
              fv_zeroize_mem_addr <= 0;
            end else if ((fv_zeroize_mem_addr == (ABR_MEM_MAX_DEPTH-2)) || (fv_zeroize_mem_addr == 0)) begin
              fv_zeroize_mem_addr <= fv_zeroize_mem_addr + 1;
            end else if(fv_zeroize_mem_addr == 1) begin
              fv_zeroize_mem_addr <= ABR_MEM_MAX_DEPTH-1;
            end else begin
              fv_zeroize_mem_addr <= fv_zeroize_mem_addr;
            end
          end else begin
            fv_zeroize_mem_addr <= 0;
          end
        end

        property zeroize_mem_addr_abstracted_P;
          `abr_ctrl.zeroize_mem_addr == fv_zeroize_mem_addr
        ;endproperty
        assume_zeroize_mem_addr_abstracted_ASM: assume property(zeroize_mem_addr_abstracted_P);


endmodule

