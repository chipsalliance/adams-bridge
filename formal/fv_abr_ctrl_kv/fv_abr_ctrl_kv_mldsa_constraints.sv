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


module fv_abr_ctrl_kv_mldsa_constraints
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
    // Parameters
    parameter ADAMSBRIDGE_CNTRL_RDY_DELAY       = 1,
    parameter ADAMSBRIDGE_AUX_DLY               = 2,
    parameter ADAMSBRIDGE_BUSY_CNTR             = 2,
    parameter AHB_ADDR_WIDTH                    = 32,
    parameter AHB_DATA_WIDTH                    = 64,
    parameter CLIENT_DATA_WIDTH                 = 32
)(
    ////////////////////////////
    // Input / Output signals //
    ////////////////////////////
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
);

    // Define default clock
    default clocking default_clk @(posedge pi_clk); endclocking


    //-------------------------Constrain primary inputs-------------------------------------
     logic fv_sigdecode_z_en;
     always_ff @(posedge pi_clk, negedge pi_rst_b) begin : sigdecode_z_en_logic
            if (!pi_rst_b || po_zeroize) begin
                fv_sigdecode_z_en <= 1'b0;
            end else if (po_sigdecode_z_enable_o) begin
                fv_sigdecode_z_en <= 1'b1;
            end else if (pi_sigdecode_z_done_i) begin
                fv_sigdecode_z_en <= 1'b0;
            end
        end

      property assume_sigdecode_z_done_p;
          pi_sigdecode_z_done_i
      |->
          (fv_sigdecode_z_en)
      endproperty
      assume_sigdecode_z_done: assume property (assume_sigdecode_z_done_p);

    `ifdef EVENTUAL_ASSUME
        assume_sigdecode_z_done_eventually: assume property(
                s_eventually(pi_sigdecode_z_done_i)
            );
    `else
        property assume_sigdecode_z_done_in_dly_p;
            po_sigdecode_z_enable_o
        |->
            ## ADAMSBRIDGE_AUX_DLY pi_sigdecode_z_done_i
        endproperty
        assume_sigdecode_z_done_in_dly: assume property (assume_sigdecode_z_done_in_dly_p);
     `endif

      logic fv_sigdecode_h_en;
     always_ff @(posedge pi_clk, negedge pi_rst_b) begin : sigdecode_h_en_logic
            if (!pi_rst_b || po_zeroize) begin
                fv_sigdecode_h_en <= 1'b0;
            end else if (po_sigdecode_h_enable_o) begin
                fv_sigdecode_h_en <= 1'b1;
            end else if (pi_sigdecode_h_done_i) begin
                fv_sigdecode_h_en <= 1'b0;
            end
        end

      property assume_sigdecode_h_done_p;
          pi_sigdecode_h_done_i
      |->
          (fv_sigdecode_h_en)
      endproperty
      assume_sigdecode_h_done: assume property (assume_sigdecode_h_done_p);
     `ifdef EVENTUAL_ASSUME
        assume_sigdecode_h_done_eventually: assume property(
               s_eventually(pi_sigdecode_h_done_i)
           );
     `else

        property assume_sigdecode_h_done_in_dly_p;
            po_sigdecode_h_enable_o
        |->
            ## ADAMSBRIDGE_AUX_DLY pi_sigdecode_h_done_i
        endproperty
        assume_sigdecode_h_done_in_dly: assume property (assume_sigdecode_h_done_in_dly_p);
     `endif
     logic fv_pkdecode_en;
     always_ff @(posedge pi_clk, negedge pi_rst_b) begin : pkdecode_en_logic
            if (!pi_rst_b || po_zeroize) begin
                fv_pkdecode_en <= 1'b0;
            end else if (po_pkdecode_enable_o) begin
                fv_pkdecode_en <= 1'b1;
            end else if (pi_pkdecode_done_i) begin
                fv_pkdecode_en <= 1'b0;
            end
        end

      property assume_pkdecode_done_p;
          pi_pkdecode_done_i
      |->
          (fv_pkdecode_en)
      endproperty
      assume_pkdecode_done: assume property (assume_pkdecode_done_p);
    `ifdef EVENTUAL_ASSUME
      assume_pkdecode_done_eventually: assume property(
            s_eventually(pi_pkdecode_done_i)
        );
    `else
     property assume_pkdecode_done_in_dly_p;
         po_pkdecode_enable_o
     |->
         ## ADAMSBRIDGE_AUX_DLY pi_pkdecode_done_i
     endproperty
     assume_pkdecode_done_in_dly: assume property (assume_pkdecode_done_in_dly_p);
        `endif

        logic fv_sigencode_en;
     always_ff @(posedge pi_clk, negedge pi_rst_b) begin : sigencode_en_logic
            if (!pi_rst_b || po_zeroize) begin
                fv_sigencode_en <= 1'b0;
            end else if (po_sigencode_enable_o) begin
                fv_sigencode_en <= 1'b1;
            end else if (pi_sigencode_done_i) begin
                fv_sigencode_en <= 1'b0;
            end
        end

      property assume_sigencode_done_p;
          pi_sigencode_done_i
      |->
          (fv_sigencode_en)
      endproperty
      assume_sigencode_done: assume property (assume_sigencode_done_p);
    `ifdef EVENTUAL_ASSUME
        assume_sigencode_done_eventually: assume property(
            s_eventually(pi_sigencode_done_i)
        );
    `else

    property assume_sigencode_done_in_dly_p;
        po_sigencode_enable_o
    |->
        ## ADAMSBRIDGE_AUX_DLY pi_sigencode_done_i
    endproperty
    assume_sigencode_done_in_dly: assume property (assume_sigencode_done_in_dly_p);
    `endif

    logic fv_sampler_enabled;
    logic [ADAMSBRIDGE_BUSY_CNTR-1:0] fv_sampler_busy_cntr;
    always_ff @(posedge pi_clk, negedge pi_rst_b) begin : sampler_enabled_tracking
        if (!pi_rst_b || po_zeroize) begin
            fv_sampler_enabled <= 1'b0;
            fv_sampler_busy_cntr <= '0;
        end else begin
            if (po_sampler_start_o) begin
                fv_sampler_enabled <= 1'b1;
                fv_sampler_busy_cntr <= ADAMSBRIDGE_BUSY_CNTR;
            end else if (fv_sampler_enabled &&( fv_sampler_busy_cntr == '0)) begin
                fv_sampler_enabled <= 1'b0;
            end
            if(fv_sampler_enabled &&( fv_sampler_busy_cntr != '0)) begin
                fv_sampler_busy_cntr <= fv_sampler_busy_cntr -1;
            end
        end
    end

    assume_sampler_busy_i_2: assume property(
        pi_sampler_busy_i == fv_sampler_enabled
    );


    logic fv_ntt_enabled;
    logic [ADAMSBRIDGE_BUSY_CNTR-1:0] fv_ntt_busy_cntr;

    always_ff @(posedge pi_clk, negedge pi_rst_b) begin : ntt_enabled_tracking
        if (!pi_rst_b) begin
            fv_ntt_enabled <= 1'b0;
            fv_ntt_busy_cntr <= '0;
        end else begin
            if (po_ntt_enable_o) begin
                fv_ntt_enabled <= 1'b1;
                fv_ntt_busy_cntr <= ADAMSBRIDGE_BUSY_CNTR;
            end else if (fv_ntt_enabled && ( fv_ntt_busy_cntr=='0)) begin
                fv_ntt_enabled <= 1'b0;
            end
            if(fv_ntt_enabled && ( fv_ntt_busy_cntr!='0)) begin
                fv_ntt_busy_cntr <= fv_ntt_busy_cntr -1;
            end
        end
    end

    assume_ntt_busy_i_2: assume property(
       pi_ntt_busy_i == (fv_ntt_enabled)
    );

    logic fv_normcheck_enabled;

    always_ff @(posedge pi_clk) begin : normcheck_enabled_tracking
        if (!pi_rst_b) begin
            fv_normcheck_enabled <= 1'b0;
        end else if (po_normcheck_enable_o) begin
            fv_normcheck_enabled <= 1'b1;
        end else if (pi_normcheck_done_i) begin
            fv_normcheck_enabled <= 1'b0;
        end
    end

     property assume_normcheck_invalid_i_p;
         // disable iff(!pi_rst_b)
             !pi_normcheck_done_i
     |->
             $stable(pi_normcheck_invalid_i)
     endproperty
     assume_normcheck_invalid_i: assume property (assume_normcheck_invalid_i_p);

     property assume_normcheck_done_p;
         pi_normcheck_done_i
     |->
         (fv_normcheck_enabled )
     endproperty
     assume_normcheck_done: assume property (assume_normcheck_done_p);
    `ifdef EVENTUAL_ASSUME
     assume_normcheck_done_eventually: assume property(
            s_eventually(pi_normcheck_done_i)
        );
    `else
    property assume_normcheck_done_in_dly_p;
        po_normcheck_enable_o
    |->
        ## ADAMSBRIDGE_AUX_DLY pi_normcheck_done_i
    endproperty
    assume_normcheck_done_in_dly: assume property (assume_normcheck_done_in_dly_p);
     `endif
    logic fv_makehint_enabled;

    always_ff @(posedge pi_clk) begin : makehint_enabled_tracking
        if (!pi_rst_b) begin
            fv_makehint_enabled <= 1'b0;
        end else if (po_makehint_enable_o) begin
            fv_makehint_enabled <= 1'b1;
        end else if (pi_makehint_done_i) begin
            fv_makehint_enabled <= 1'b0;
        end
    end

    property assume_makehint_invalid_i_p;
        // disable iff(!pi_rst_b)
            !pi_makehint_done_i
    |->
            $stable(pi_makehint_invalid_i)
    endproperty
    assume_makehint_invalid_i: assume property (assume_makehint_invalid_i_p);

     property assume_makehint_done_p;
         pi_makehint_done_i
     |->
         (fv_makehint_enabled )
     endproperty
     assume_makehint_done: assume property (assume_makehint_done_p);
         property assume_makehint_wren_p;
             pi_makehint_reg_wren_i
         |->
             (fv_makehint_enabled )
         endproperty
         assume_makehint_wren: assume property (assume_makehint_wren_p);

    `ifdef EVENTUAL_ASSUME
     assume_makehint_done_eventually: assume property(
           s_eventually (pi_makehint_done_i)
        );
    `else
     property assume_makehint_done_in_dly_p;
         po_makehint_enable_o
     |->
         ##ADAMSBRIDGE_AUX_DLY pi_makehint_done_i
     endproperty
     assume_makehint_done_in_dly: assume property (assume_makehint_done_in_dly_p);
    `endif
    assume_makehint_req_addr_range: assume property(
        pi_makehint_reg_wr_addr_i >= 0 && pi_makehint_reg_wr_addr_i < SIGNATURE_H_NUM_DWORDS
    );



 logic fv_pwr2rnd_en;
     always_ff @(posedge pi_clk, negedge pi_rst_b) begin : pwr2rnd_en_logic
            if (!pi_rst_b || po_zeroize) begin
                fv_pwr2rnd_en <= 1'b0;
            end else if (po_power2round_enable_o) begin
                fv_pwr2rnd_en <= 1'b1;
            end else if (pi_power2round_done_i) begin
                fv_pwr2rnd_en <= 1'b0;
            end
        end

      property assume_power2round_done_p;
          pi_power2round_done_i
      |->
          (fv_pwr2rnd_en) // dont trigger when enable
      endproperty
      assume_power2round_done: assume property (assume_power2round_done_p);

    `ifdef EVENTUAL_ASSUME
      assume_power2round_done_eventually: assume property(
            s_eventually(pi_power2round_done_i) // dont trigger when enable
        );
    `else

    property assume_pwr2rnd_in_2cycles_p;
        po_power2round_enable_o
    |->
        ##ADAMSBRIDGE_AUX_DLY pi_power2round_done_i
    endproperty
    assume_pwr2rnd_in_2cycles: assume property (assume_pwr2rnd_in_2cycles_p);
    `endif

    property assume_pwr2rnd_mem_0_p;
        (pi_pwr2rnd_keymem_if_i[0].rd_wr_en == RW_WRITE)
    |->
        (fv_pwr2rnd_en)
    endproperty
    assume_pwr2rnd_mem_0: assume property (assume_pwr2rnd_mem_0_p);

     property assume_pwr2rnd_mem_1_p;
         (pi_pwr2rnd_keymem_if_i[1].rd_wr_en == RW_WRITE)
     |->
         (fv_pwr2rnd_en)
     endproperty
     assume_pwr2rnd_mem_1: assume property (assume_pwr2rnd_mem_1_p);
    property assume_pwr2rnd_api_wren_p;
        (pi_pk_t1_wren_i)
    |->
        (fv_pwr2rnd_en)
    endproperty
    assume_pwr2rnd_api_wren: assume property (assume_pwr2rnd_api_wren_p);

 logic fv_decompose_en;
     always_ff @(posedge pi_clk, negedge pi_rst_b) begin : decompose_en_logic
            if (!pi_rst_b || po_zeroize) begin
                fv_decompose_en <= 1'b0;
            end else if (po_decompose_enable_o) begin
                fv_decompose_en <= 1'b1;
            end else if (pi_decompose_done_i) begin
                fv_decompose_en <= 1'b0;
            end
        end

      property assume_decompose_done_p;
          pi_decompose_done_i
      |->
          (fv_decompose_en)
      endproperty
      assume_decompose_done: assume property (assume_decompose_done_p);
    `ifdef EVENTUAL_ASSUME
      assume_decompose_done_eventually: assume property(
            s_eventually(pi_decompose_done_i)
        );
    `else
    property assume_decompose_done_2cycles_p;
        po_decompose_enable_o
    |->
        ##ADAMSBRIDGE_AUX_DLY pi_decompose_done_i
    endproperty
    assume_decompose_done_2cycles: assume property (assume_decompose_done_2cycles_p);
    `endif

 logic fv_skencode_en;
     always_ff @(posedge pi_clk, negedge pi_rst_b) begin : skencode_en_logic
            if (!pi_rst_b || po_zeroize) begin
                fv_skencode_en <= 1'b0;
            end else if (po_skencode_enable_o) begin
                fv_skencode_en <= 1'b1;
            end else if (pi_skencode_done_i) begin
                fv_skencode_en <= 1'b0;
            end
        end

      property assume_skencode_done_p;
          pi_skencode_done_i
      |->
          (fv_skencode_en)
      endproperty
      assume_skencode_done: assume property (assume_skencode_done_p);
    `ifdef EVENTUAL_ASSUME
        assume_skencode_done_eventually: assume property(
            s_eventually(pi_skencode_done_i)
        );
    `else

    property assume_skencode_done_2cycles_p;
        po_skencode_enable_o
    |->
        ##ADAMSBRIDGE_AUX_DLY pi_skencode_done_i
    endproperty
    assume_skencode_done_2cycles: assume property (assume_skencode_done_2cycles_p);
    `endif

    property assume_skencode_mem_wr_p;
        (pi_skencode_keymem_if_i.rd_wr_en == RW_WRITE)
    |->
        (fv_skencode_en)
    endproperty
    assume_skencode_mem_wr: assume property (assume_skencode_mem_wr_p);

 logic fv_skdecode_en;
     always_ff @(posedge pi_clk, negedge pi_rst_b) begin : skdecode_en_logic
            if (!pi_rst_b || po_zeroize) begin
                fv_skdecode_en <= 1'b0;
            end else if (po_skdecode_enable_o) begin
                fv_skdecode_en <= 1'b1;
            end else if (pi_skdecode_done_i) begin
                fv_skdecode_en <= 1'b0;
            end
        end

      property assume_skdecode_done_p;
          pi_skdecode_done_i
      |->
          (fv_skdecode_en)
      endproperty
      assume_skdecode_done: assume property (assume_skdecode_done_p);

    property assume_error_when_enabled_only_p;
        pi_skdecode_error_i
    |->
        (fv_skdecode_en)
    endproperty
    assume_error_when_enabled_only: assume property (assume_error_when_enabled_only_p);
    `ifdef EVENTUAL_ASSUME
        assume_skdecode_done_eventually: assume property(
            s_eventually(pi_skdecode_done_i)
        );
    `else

    property assume_skdecode_done_2cycles_p;
        po_skdecode_enable_o
    |->
        ##ADAMSBRIDGE_AUX_DLY pi_skdecode_done_i
    endproperty
    assume_skdecode_done_2cycles: assume property (assume_skdecode_done_2cycles_p);
    `endif
        property assume_skdecode_mem_0_p;
            (pi_skdecode_keymem_if_i[0].rd_wr_en == RW_READ)
        |->
            (fv_skdecode_en)
        endproperty
        assume_skdecode_mem_0: assume property (assume_skdecode_mem_0_p);

         property assume_skdecode_mem_1_p;
             (pi_skdecode_keymem_if_i[1].rd_wr_en == RW_READ)
         |->
             (fv_skdecode_en)
         endproperty
         assume_skdecode_mem_1: assume property (assume_skdecode_mem_1_p);

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

      property assume_sampler_dv_p;
          pi_sampler_state_dv_i
      |->
          (fv_sample_dv && (pi_sampler_busy_i))
      endproperty
      assume_sampler_dv: assume property (assume_sampler_dv_p);

    property assume_sampler_valid_pulse_p;
        pi_sampler_state_dv_i
    |->
        ##1 !pi_sampler_state_dv_i
    endproperty
    assume_sampler_valid_pulse: assume property (assume_sampler_valid_pulse_p);


    property assume_sampler_data_stable_p;
        !pi_sampler_state_dv_i
    |->
        (pi_sampler_state_data_i == '0)
    endproperty
    assume_sampler_data_stable: assume property (assume_sampler_data_stable_p);

    assume_msg_rdy_eventually: assume property(
        s_eventually(pi_msg_rdy_i)
    );

    property assume_msg_rdy__p;
        po_msg_valid_o && !pi_msg_rdy_i
    |->
            ##ADAMSBRIDGE_CNTRL_RDY_DELAY pi_msg_rdy_i
    endproperty
    assume_msg_rdy_: assume property (assume_msg_rdy__p);


    // assume_no_op_after_reset: assume property(
    //     $past(!pi_rst_b || abr_ctrl.zeroize)
    // |->
    //     $past(pi_abr_reg_hwif_out_i.abr_ctrl.CTRL.value ==  3'd0)
    // );

    //-------------------------Constrain abr_reg_hwif_out_i-------------------------------------

    property assume_ctrl_value_i_p;
        //disable iff(!pi_rst_b)
            po_abr_reg_hwif_in_o.MLDSA_CTRL.CTRL.hwclr
    |->
            ##1 pi_abr_reg_hwif_out_i.MLDSA_CTRL.CTRL.value == '0
    endproperty
    assume_ctrl_value_i: assume property (assume_ctrl_value_i_p);

    property assume_pcr_sign_value_i_p;
        //disable iff(!pi_rst_b)
            po_abr_reg_hwif_in_o.MLDSA_CTRL.PCR_SIGN.hwclr
    |->
            ##1 pi_abr_reg_hwif_out_i.MLDSA_CTRL.PCR_SIGN.value == '0
    endproperty
    assume_pcr_sign_value_i: assume property (assume_pcr_sign_value_i_p);


    property assume_hwif_out_value_i_stable_p;
        // disable iff(!pi_rst_b)
            !po_abr_reg_hwif_in_o.abr_ready
    |->
            ##1 $stable(pi_abr_reg_hwif_out_i.MLDSA_CTRL.CTRL.value) &&
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
                $stable(pi_abr_reg_hwif_out_i.MLDSA_EXTERNAL_MU[15].EXTERNAL_MU.value)
    endproperty
    assume_hwif_out_value_i_stable: assume property (assume_hwif_out_value_i_stable_p);


    //MLDSA_CTRL and kv_ctrl reg should be mutually exclusive
    property assume_if_mldsa_ctrl_no_kv_mldsa_seed_rd_for_2_cycles_p;
        pi_abr_reg_hwif_out_i.MLDSA_CTRL.CTRL.value != '0
    |->
            !pi_abr_reg_hwif_out_i.kv_mldsa_seed_rd_ctrl.read_en.value [*2]
    endproperty
    assume_if_mldsa_ctrl_no_kv_mldsa_seed_rd_for_2_cycles: assume property (assume_if_mldsa_ctrl_no_kv_mldsa_seed_rd_for_2_cycles_p);


    property assume_if_kv_mldsa_seed_rd_no_mldsa_ctrl_for_2_cycles_p;
        pi_abr_reg_hwif_out_i.kv_mldsa_seed_rd_ctrl.read_en.value
    |->
            pi_abr_reg_hwif_out_i.MLDSA_CTRL.CTRL.value == '0 [*2]
    endproperty
    assume_if_kv_mldsa_seed_rd_no_mldsa_ctrl_for_2_cycles: assume property (assume_if_kv_mldsa_seed_rd_no_mldsa_ctrl_for_2_cycles_p);

    //-------------------------Constrain memory interface signals-------------------------------------//

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

     property msg_cnt_abstracted_p;
         abr_ctrl.msg_cnt == fv_msg_cnt
     ;endproperty
    assume_msg_cnt_abstracted_asm: assume property(msg_cnt_abstracted_p);

    property abstract_abr_prog_cntr_P;
        (abr_ctrl.abr_prog_cntr == ABR_RESET) ||
        (abr_ctrl.abr_prog_cntr == ABR_ZEROIZE) ||
        ((abr_ctrl.abr_prog_cntr >= MLDSA_KG_S) && (abr_ctrl.abr_prog_cntr <= MLDSA_KG_E)) ||
        ((abr_ctrl.abr_prog_cntr >= MLDSA_SIGN_S) && (abr_ctrl.abr_prog_cntr <= MLDSA_SIGN_E)) ||
        ((abr_ctrl.abr_prog_cntr >= MLDSA_VERIFY_S) && (abr_ctrl.abr_prog_cntr <= MLDSA_VERIFY_E))
    ;endproperty

    assume_abstract_abr_prog_cntr_asm: assume property(abstract_abr_prog_cntr_P);

    logic fv_keygen_set;
    logic fv_keygen_signing_set;
    logic fv_signing_set;
    logic fv_verify_set;

    always_comb begin: fv_set_mode_logic
            fv_keygen_set = '0;
            fv_keygen_signing_set = '0;
            fv_signing_set = '0;
            fv_verify_set = '0;
            if((abr_ctrl.abr_prog_cntr >= MLDSA_KG_S) && (abr_ctrl.abr_prog_cntr <= MLDSA_KG_E)) begin
                fv_keygen_set = 1;
            end
            if((abr_ctrl.abr_prog_cntr >= MLDSA_SIGN_S) && (abr_ctrl.abr_prog_cntr <= MLDSA_SIGN_E)) begin
                fv_signing_set = 1;
            end
            if((abr_ctrl.abr_prog_cntr >= MLDSA_VERIFY_S) && (abr_ctrl.abr_prog_cntr <= MLDSA_VERIFY_E)) begin
                fv_verify_set = 1;
            end

        end
    property abstract_init_value_abr_prog_cntr_P;
      abr_ctrl.mldsa_keygen_process == fv_keygen_set &&
      abr_ctrl.mldsa_signing_process == fv_signing_set &&
      abr_ctrl.mldsa_verifying_process == fv_verify_set &&
      abr_ctrl.mldsa_keygen_signing_process == (abr_ctrl.mldsa_cmd_reg == MLDSA_KEYGEN_SIGN)
    ;endproperty
    assume_abstract_init_value_abr_prog_cntr_asm: assume property(abstract_init_value_abr_prog_cntr_P);


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
    property zeroize_post_valid;
        abr_ctrl.mldsa_valid_reg
    |=>
        ##ADAMSBRIDGE_AUX_DLY pi_abr_reg_hwif_out_i.MLDSA_CTRL.ZEROIZE.value
    ;endproperty
    assume_zeroize_post_valid: assume property(zeroize_post_valid);




    // MLKEM is disabled. WIP
    assume_disable_mlkem: assume property(
        (pi_abr_reg_hwif_out_i.MLKEM_CTRL.CTRL.value == MLKEM_NONE) &&
        !pi_abr_reg_hwif_out_i.kv_mlkem_msg_rd_ctrl.read_en.value &&
        !pi_abr_reg_hwif_out_i.kv_mlkem_seed_rd_ctrl.read_en.value
    );


    //If swwe is not asserted, read_ctrl registers should be stable
    property assume_kv_mldsa_seed_rd_ctrl_read_en_stable_p;
        disable iff(!pi_rst_b)
            !po_abr_reg_hwif_in_o.kv_mldsa_seed_rd_ctrl.read_en.swwe &&
            !po_abr_reg_hwif_in_o.kv_mldsa_seed_rd_ctrl.read_en.hwclr
    |->
            ##1 $stable(pi_abr_reg_hwif_out_i.kv_mldsa_seed_rd_ctrl.read_en.value)
    endproperty
    assume_kv_mldsa_seed_rd_ctrl_read_en_stable: assume property (assume_kv_mldsa_seed_rd_ctrl_read_en_stable_p);

    property assume_kv_mldsa_seed_rd_ctrl_read_entry_stable_p;
        disable iff(!pi_rst_b)
            !po_abr_reg_hwif_in_o.kv_mldsa_seed_rd_ctrl.read_entry.swwe &&
            !po_abr_reg_hwif_in_o.kv_mldsa_seed_rd_ctrl.read_en.hwclr
    |->
            ##1 $stable(pi_abr_reg_hwif_out_i.kv_mldsa_seed_rd_ctrl.read_entry.value)
    endproperty
    assume_kv_mldsa_seed_rd_ctrl_read_entry_stable: assume property (assume_kv_mldsa_seed_rd_ctrl_read_entry_stable_p);

    property assume_kv_mldsa_seed_rd_ctrl_read_pcr_hash_extend_stable_p;
        disable iff(!pi_rst_b)
            !po_abr_reg_hwif_in_o.kv_mldsa_seed_rd_ctrl.pcr_hash_extend.swwe &&
            !po_abr_reg_hwif_in_o.kv_mldsa_seed_rd_ctrl.read_en.hwclr
    |->
            ##1 $stable(pi_abr_reg_hwif_out_i.kv_mldsa_seed_rd_ctrl.pcr_hash_extend.value)
    endproperty
    assume_kv_mldsa_seed_rd_ctrl_read_pcr_hash_extend_stable: assume property (assume_kv_mldsa_seed_rd_ctrl_read_pcr_hash_extend_stable_p);

    property assume_kv_mldsa_seed_rd_ctrl_read_rsvd_stable_p;
        disable iff(!pi_rst_b)
            !po_abr_reg_hwif_in_o.kv_mldsa_seed_rd_ctrl.rsvd.swwe &&
            !po_abr_reg_hwif_in_o.kv_mldsa_seed_rd_ctrl.read_en.hwclr
    |->
            ##1 $stable(pi_abr_reg_hwif_out_i.kv_mldsa_seed_rd_ctrl.rsvd.value)
    endproperty
    assume_kv_mldsa_seed_rd_ctrl_read_rsvd_stable: assume property (assume_kv_mldsa_seed_rd_ctrl_read_rsvd_stable_p);


    //If hwclr is asserted, read_ctrl registers should be deasserted
    property assume_kv_mldsa_seed_rd_ctrl_clear_p;
        // disable iff(!pi_rst_b)
            po_abr_reg_hwif_in_o.kv_mldsa_seed_rd_ctrl.read_en.hwclr
    |->
            ##1 pi_abr_reg_hwif_out_i.kv_mldsa_seed_rd_ctrl.read_entry.value == '0 &&
                pi_abr_reg_hwif_out_i.kv_mldsa_seed_rd_ctrl.pcr_hash_extend.value == '0 &&
                pi_abr_reg_hwif_out_i.kv_mldsa_seed_rd_ctrl.rsvd.value == '0 &&
                pi_abr_reg_hwif_out_i.kv_mldsa_seed_rd_ctrl.read_en.value == '0
    endproperty
    assume_kv_mldsa_seed_rd_ctrl_clear: assume property (assume_kv_mldsa_seed_rd_ctrl_clear_p);

    //If reset is asserted, read_ctrl registers should be deasserted
    property assume_kv_mldsa_seed_rd_ctrl_rst_p;
        $past(!pi_rst_b)
    |->
            pi_abr_reg_hwif_out_i.kv_mldsa_seed_rd_ctrl.read_entry.value == '0 &&
            pi_abr_reg_hwif_out_i.kv_mldsa_seed_rd_ctrl.pcr_hash_extend.value == '0 &&
            pi_abr_reg_hwif_out_i.kv_mldsa_seed_rd_ctrl.rsvd.value == '0 &&
            pi_abr_reg_hwif_out_i.kv_mldsa_seed_rd_ctrl.read_en.value == '0
    endproperty
    assume_kv_mldsa_seed_rd_ctrl_rst: assume property (assume_kv_mldsa_seed_rd_ctrl_rst_p);


    //MLDSA_SEED[].SEED constraints to model abr_reg
    genvar fv_mldsa_seed_var;
    generate
        for(fv_mldsa_seed_var=0; fv_mldsa_seed_var<SEED_NUM_DWORDS; fv_mldsa_seed_var++) begin: gen_mldsa_seed_constraints
            property assume_mldsa_seed_stable_p;
                disable iff(!pi_rst_b)
                    !po_abr_reg_hwif_in_o.MLDSA_SEED[fv_mldsa_seed_var].SEED.swwe && //SW write
                    !po_abr_reg_hwif_in_o.MLDSA_SEED[fv_mldsa_seed_var].SEED.hwclr &&
                    !po_abr_reg_hwif_in_o.MLDSA_SEED[fv_mldsa_seed_var].SEED.we     //HW write
            |->
                    ##1 $stable(pi_abr_reg_hwif_out_i.MLDSA_SEED[fv_mldsa_seed_var].SEED.value)
            endproperty
            assume_mldsa_seed_stable: assume property (assume_mldsa_seed_stable_p);

            property assume_mldsa_seed_clear_p;
                disable iff(!pi_rst_b)
                    po_abr_reg_hwif_in_o.MLDSA_SEED[fv_mldsa_seed_var].SEED.hwclr &&
                    !po_abr_reg_hwif_in_o.MLDSA_SEED[fv_mldsa_seed_var].SEED.we &&
                    !po_abr_reg_hwif_in_o.MLDSA_SEED[fv_mldsa_seed_var].SEED.swwe
            |->
                    ##1 pi_abr_reg_hwif_out_i.MLDSA_SEED[fv_mldsa_seed_var].SEED.value == '0
            endproperty
            assume_mldsa_seed_clear: assume property (assume_mldsa_seed_clear_p);

            property assume_mldsa_seed_hwwrite_p;
                disable iff(!pi_rst_b)
                    po_abr_reg_hwif_in_o.MLDSA_SEED[fv_mldsa_seed_var].SEED.we
            |->
                    ##1 pi_abr_reg_hwif_out_i.MLDSA_SEED[fv_mldsa_seed_var].SEED.value == $past(po_abr_reg_hwif_in_o.MLDSA_SEED[fv_mldsa_seed_var].SEED.next)
            endproperty
            assume_mldsa_seed_hwwrite: assume property (assume_mldsa_seed_hwwrite_p);

            property assume_mldsa_seed_rst_p;
                $past(!pi_rst_b)
            |->
                    pi_abr_reg_hwif_out_i.MLDSA_SEED[fv_mldsa_seed_var].SEED.value == '0
            endproperty
            assume_mldsa_seed_rst: assume property (assume_mldsa_seed_rst_p);
        end
    endgenerate


    //MLDSA seed response data should be '0 in case of read error
    property assume_kv_mldsa_seed_resp_data_zero_during_error_p;
        // disable iff(!pi_rst_b)
            pi_kv_rd_resp[0].error
    |->
            pi_kv_rd_resp[0].read_data == '0
    endproperty
    assume_kv_mldsa_seed_resp_data_zero_during_error: assume property (assume_kv_mldsa_seed_resp_data_zero_during_error_p);


endmodule
