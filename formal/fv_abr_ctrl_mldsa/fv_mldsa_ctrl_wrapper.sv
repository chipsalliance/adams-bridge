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
`include "mldsa_config_defines.svh"


module fv_mldsa_ctrl_wrapper
    import mldsa_reg_pkg::*;
    import abr_sha3_pkg::*;
    import mldsa_sampler_pkg::*;
    import mldsa_ctrl_pkg::*;
    import mldsa_params_pkg::*;
    import ntt_defines_pkg::*;
#(
    // Parameters
    parameter ADAMSBRIDGE_CNTRL_RDY_DELAY     = 1,
    parameter ADAMSBRIDGE_AUX_DLY             = 2,
    parameter ADAMSBRIDGE_BUSY_CNTR = 2,
    parameter AHB_ADDR_WIDTH = 32,
    parameter AHB_DATA_WIDTH = 64,
    parameter CLIENT_DATA_WIDTH = 32
)(
    ////////////////////////////
    // Input / Output signals //
    ////////////////////////////
    input logic pi_clk,
    input logic pi_rst_b,
    input logic po_zeroize,

    input mldsa_reg__in_t   po_abr_reg_hwif_in_o,
    input  mldsa_reg__out_t pi_abr_reg_hwif_out_i,

    //sampler interface
    input mldsa_sampler_mode_e          po_sampler_mode_o,
    input logic                       po_sha3_start_o,
    input logic                       po_msg_start_o,
    input logic                       po_msg_valid_o,
    input logic                       pi_msg_rdy_i,
    input logic [MsgStrbW-1:0]        po_msg_strobe_o,
    input logic [MsgWidth-1:0]        po_msg_data_o[Sha3Share],
    input logic                       po_sampler_start_o,

    input logic                        pi_sampler_busy_i,
    input logic                        pi_sampler_state_dv_i,
    input logic [abr_sha3_pkg::StateW-1:0] pi_sampler_state_data_i [Sha3Share],

    input logic [MLDSA_MEM_ADDR_WIDTH-1:0] po_dest_base_addr_o,

    //ntt interfaces
    input logic [1:0]                        po_ntt_enable_o,
    input mldsa_ntt_mode_e [1:0]               po_ntt_mode_o,
       input logic [1:0]                        po_ntt_masking_en_o,
    input logic [1:0]                        po_ntt_shuffling_en_o,
    input ntt_mem_addr_t [1:0]               po_ntt_mem_base_addr_o,
    input pwo_mem_addr_t [1:0]               po_pwo_mem_base_addr_o,
    input logic [1:0]                        pi_ntt_busy_i,

    //aux interfaces
    input logic [1:0][MLDSA_MEM_ADDR_WIDTH-1:0] po_aux_src0_base_addr_o,
    input logic [1:0][MLDSA_MEM_ADDR_WIDTH-1:0] po_aux_src1_base_addr_o,
    input logic [1:0][MLDSA_MEM_ADDR_WIDTH-1:0] po_aux_dest_base_addr_o,

    input logic                         po_power2round_enable_o,
    input mem_if_t [1:0]                pi_pwr2rnd_keymem_if_i,
    input logic [1:0] [DATA_WIDTH-1:0]  pi_pwr2rnd_wr_data_i,
    input logic                         pi_pk_t1_wren_i,
    input logic [7:0][9:0]              pi_pk_t1_wrdata_i, // change to parameter
    input logic [7:0]                   pi_pk_t1_wr_addr_i, // change to parameter
    input logic                         pi_power2round_done_i,

    input logic po_decompose_enable_o,
    input logic po_decompose_mode_o,
    input logic pi_decompose_done_i,

    input logic                  po_skencode_enable_o,
    input mem_if_t               pi_skencode_keymem_if_i,
    input logic [DATA_WIDTH-1:0] pi_skencode_wr_data_i,
    input logic                  pi_skencode_done_i,

    input logic                       po_skdecode_enable_o,
    input mem_if_t [1:0]              pi_skdecode_keymem_if_i,
    input logic [1:0][DATA_WIDTH-1:0] po_skdecode_rd_data_o,
    input logic                       pi_skdecode_done_i,
     input logic                       pi_skdecode_error_i,

    input logic                      po_makehint_enable_o,
    input logic                      pi_makehint_invalid_i,
    input logic                      pi_makehint_done_i,
    input logic                      pi_makehint_reg_wren_i,
    input logic [3:0][7:0]           pi_makehint_reg_wrdata_i,
    input logic [MLDSA_MEM_ADDR_WIDTH-1:0] pi_makehint_reg_wr_addr_i,

    input logic                          po_normcheck_enable_o,
    input logic [1:0]                    po_normcheck_mode_o,
    input logic [MLDSA_MEM_ADDR_WIDTH-1:0] po_normcheck_src_addr_o,
    input logic                          pi_normcheck_invalid_i,
    input logic                          pi_normcheck_done_i,

    input logic                  po_sigencode_enable_o,
    input mem_if_t               pi_sigencode_wr_req_i,
    input logic [1:0][3:0][19:0] pi_sigencode_wr_data_i,
    input logic                  pi_sigencode_done_i,

    input logic                       po_pkdecode_enable_o,
    input logic [7:0]                 pi_pkdecode_rd_addr_i,
    input logic [7:0][T1_COEFF_W-1:0] po_pkdecode_rd_data_o,
    input logic                       pi_pkdecode_done_i,


    input logic                                        po_sigdecode_h_enable_o, 
    input logic [SIGNATURE_H_VALID_NUM_BYTES-1:0][7:0] po_signature_h_o,
    input logic                                        pi_sigdecode_h_invalid_i,
    input logic                                        pi_sigdecode_h_done_i,

    input logic                  po_sigdecode_z_enable_o, 
    input mem_if_t               pi_sigdecode_z_rd_req_i,
    input logic [1:0][3:0][19:0] po_sigdecode_z_rd_data_o,
    input logic                  pi_sigdecode_z_done_i,

    input logic po_lfsr_enable_o,
    input logic [1:0][LFSR_W-1:0]                       po_lfsr_seed_o,
    input logic                                         po_sk_bank0_mem_if_we_i,
    input logic [SK_MEM_BANK_ADDR_W-1:0]                po_sk_bank0_mem_if_waddr_i,
    input logic [DATA_WIDTH-1:0]                        po_sk_bank0_mem_if_wdata_i,
    input logic                                         po_sk_bank0_mem_if_re_i,
    input logic [SK_MEM_BANK_ADDR_W-1:0]                po_sk_bank0_mem_if_raddr_i,
    input logic [DATA_WIDTH-1:0]                        pi_sk_bank0_mem_if_rdata_o,
    input logic                                         po_sk_bank1_mem_if_we_i,
    input logic [SK_MEM_BANK_ADDR_W-1:0]                po_sk_bank1_mem_if_waddr_i,
    input logic [DATA_WIDTH-1:0]                        po_sk_bank1_mem_if_wdata_i,
    input logic                                         po_sk_bank1_mem_if_re_i,
    input logic [SK_MEM_BANK_ADDR_W-1:0]                po_sk_bank1_mem_if_raddr_i,
    input logic [DATA_WIDTH-1:0]                        pi_sk_bank1_mem_if_rdata_o,

    input logic                   po_sig_z_mem_if_we_i,
    input logic [SIG_Z_MEM_ADDR_W-1:0]      po_sig_z_mem_if_waddr_i,
    input logic [SIG_Z_MEM_DATA_W-1:0]      po_sig_z_mem_if_wdata_i,
    input logic [SIG_Z_MEM_DATA_W/8-1:0]    po_sig_z_mem_if_wstrobe_i,
    input logic                   po_sig_z_mem_if_re_i,
    input logic [SIG_Z_MEM_ADDR_W-1:0]      po_sig_z_mem_if_raddr_i,
    input logic [SIG_Z_MEM_DATA_W-1:0]      pi_sig_z_mem_if_rdata_o,
    input logic                   po_pk_mem_if_we_i,
    input logic [PK_ADDR_W-1:0]      po_pk_mem_if_waddr_i,
    input logic [PK_MEM_DATA_W-1:0]      po_pk_mem_if_wdata_i,
    input logic [PK_MEM_DATA_W/8-1:0]    po_pk_mem_if_wstrobe_i,
    input logic                   po_pk_mem_if_re_i,
    input logic [PK_ADDR_W-1:0]      po_pk_mem_if_raddr_i,
    input logic [PK_MEM_DATA_W-1:0]      pi_pk_mem_if_rdata_o,

    input mem_if_t zeroize_mem_o,

    `ifdef CALIPTRA
    // KV interface
    input kv_read_t kv_read,
    input kv_rd_resp_t kv_rd_resp,
    //PCR Signing
    input pcr_signing_t pcr_signing_data,
    `endif

    input logic pi_debugUnlock_or_scan_mode_switch,
    input logic po_busy_o,

    //Interrupts
    input logic po_error_intr,
    input logic po_notif_intr
);

    // Define default clock
    default clocking default_clk @(posedge pi_clk); endclocking


// Whitebox checks instantiation

fv_mldsa_ctrl_whitebox fv_mldsa_ctrl_whitebox_inst (.*);


// constraints module instantiation

fv_mldsa_ctrl_constraints fv_mldsa_ctrl_constraints_inst (.*);
endmodule

bind mldsa_ctrl fv_mldsa_ctrl_wrapper fv_mldsa_ctrl_wrapper_i (
    .pi_clk(clk),
    .pi_rst_b(rst_b),
    .po_zeroize(zeroize),

    // Register interface
    .po_abr_reg_hwif_in_o(mldsa_reg_hwif_in_o),
    .pi_abr_reg_hwif_out_i(mldsa_reg_hwif_out_i),

    // Sampler interface
    .po_sampler_mode_o(sampler_mode_o),
    .po_sha3_start_o(sha3_start_o),
    .po_msg_start_o(msg_start_o),
    .po_msg_valid_o(msg_valid_o),
    .pi_msg_rdy_i(msg_rdy_i),
    .po_msg_strobe_o(msg_strobe_o),
    .po_msg_data_o(msg_data_o),
    .po_sampler_start_o(sampler_start_o),

    .pi_sampler_busy_i(sampler_busy_i),
    .pi_sampler_state_dv_i(sampler_state_dv_i),
    .pi_sampler_state_data_i(sampler_state_data_i),

    .po_dest_base_addr_o(dest_base_addr_o),

    // NTT interfaces
    .po_ntt_enable_o(ntt_enable_o),
    .po_ntt_mode_o(ntt_mode_o),
    .po_ntt_masking_en_o(ntt_masking_en_o),
    .po_ntt_shuffling_en_o(ntt_shuffling_en_o),
    .po_ntt_mem_base_addr_o(ntt_mem_base_addr_o),
    .po_pwo_mem_base_addr_o(pwo_mem_base_addr_o),
    .pi_ntt_busy_i(ntt_busy_i),

    // Auxiliary interfaces
    .po_aux_src0_base_addr_o(aux_src0_base_addr_o),
    .po_aux_src1_base_addr_o(aux_src1_base_addr_o),
    .po_aux_dest_base_addr_o(aux_dest_base_addr_o),

    // Power2Round interface
    .po_power2round_enable_o(power2round_enable_o),
    .pi_pwr2rnd_keymem_if_i(pwr2rnd_keymem_if_i),
    .pi_pwr2rnd_wr_data_i(pwr2rnd_wr_data_i),
    .pi_pk_t1_wren_i(pk_t1_wren_i),
    .pi_pk_t1_wrdata_i(pk_t1_wrdata_i),
    .pi_pk_t1_wr_addr_i(pk_t1_wr_addr_i),
    .pi_power2round_done_i(power2round_done_i),

    // Decompose interface
    .po_decompose_enable_o(decompose_enable_o),
    .po_decompose_mode_o(decompose_mode_o),
    .pi_decompose_done_i(decompose_done_i),

    // Skencode interface
    .po_skencode_enable_o(skencode_enable_o),
    .pi_skencode_keymem_if_i(skencode_keymem_if_i),
    .pi_skencode_wr_data_i(skencode_wr_data_i),
    .pi_skencode_done_i(skencode_done_i),

    // Skdecode interface
    .po_skdecode_enable_o(skdecode_enable_o),
    .pi_skdecode_keymem_if_i(skdecode_keymem_if_i),
    .po_skdecode_rd_data_o(skdecode_rd_data_o),
    .pi_skdecode_done_i(skdecode_done_i),
    .pi_skdecode_error_i(skdecode_error_i),
    // Makehint interface
    .po_makehint_enable_o(makehint_enable_o),
    .pi_makehint_invalid_i(makehint_invalid_i),
    .pi_makehint_done_i(makehint_done_i),
    .pi_makehint_reg_wren_i(makehint_reg_wren_i),
    .pi_makehint_reg_wrdata_i(makehint_reg_wrdata_i),
    .pi_makehint_reg_wr_addr_i(makehint_reg_wr_addr_i),

    // Normcheck interface
    .po_normcheck_enable_o(normcheck_enable_o),
    .po_normcheck_mode_o(normcheck_mode_o),
    .po_normcheck_src_addr_o(normcheck_src_addr_o),
    .pi_normcheck_invalid_i(normcheck_invalid_i),
    .pi_normcheck_done_i(normcheck_done_i),

    // Sigencode interface
    .po_sigencode_enable_o(sigencode_enable_o),
    .pi_sigencode_wr_req_i(sigencode_wr_req_i),
    .pi_sigencode_wr_data_i(sigencode_wr_data_i),
    .pi_sigencode_done_i(sigencode_done_i),

    // Pkdecode interface
    .po_pkdecode_enable_o(pkdecode_enable_o),
    .pi_pkdecode_rd_addr_i(pkdecode_rd_addr_i),
    .po_pkdecode_rd_data_o(pkdecode_rd_data_o),
    .pi_pkdecode_done_i(pkdecode_done_i),

    // Sigdecode H interface
    .po_sigdecode_h_enable_o(sigdecode_h_enable_o),
    .po_signature_h_o(signature_h_o),
    .pi_sigdecode_h_invalid_i(sigdecode_h_invalid_i),
    .pi_sigdecode_h_done_i(sigdecode_h_done_i),

    // Sigdecode Z interface
    .po_sigdecode_z_enable_o(sigdecode_z_enable_o),
    .pi_sigdecode_z_rd_req_i(sigdecode_z_rd_req_i),
    .po_sigdecode_z_rd_data_o(sigdecode_z_rd_data_o),
    .pi_sigdecode_z_done_i(sigdecode_z_done_i),

    // mem interfaces
    .po_sk_bank0_mem_if_we_i(mldsa_ctrl.sk_ram_we_bank[0]),
    .po_sk_bank0_mem_if_waddr_i(mldsa_ctrl.sk_ram_waddr_bank[0]),
    .po_sk_bank0_mem_if_wdata_i(mldsa_ctrl.sk_ram_wdata[0]),
    .po_sk_bank0_mem_if_re_i(mldsa_ctrl.sk_ram_re_bank[0]),
    .po_sk_bank0_mem_if_raddr_i(mldsa_ctrl.sk_ram_raddr_bank[0]),
    .pi_sk_bank0_mem_if_rdata_o(mldsa_ctrl.sk_ram_rdata[0]),
    .po_sk_bank1_mem_if_we_i(mldsa_ctrl.sk_ram_we_bank[1]),
    .po_sk_bank1_mem_if_waddr_i(mldsa_ctrl.sk_ram_waddr_bank[1]),
    .po_sk_bank1_mem_if_wdata_i(mldsa_ctrl.sk_ram_wdata[1]),
    .po_sk_bank1_mem_if_re_i(mldsa_ctrl.sk_ram_re_bank[1]),
    .po_sk_bank1_mem_if_raddr_i(mldsa_ctrl.sk_ram_raddr_bank[1]),
    .pi_sk_bank1_mem_if_rdata_o(mldsa_ctrl.sk_ram_rdata[1]),
    .po_sig_z_mem_if_we_i(mldsa_ctrl.sig_z_ram_we),
    .po_sig_z_mem_if_waddr_i(mldsa_ctrl.sig_z_ram_waddr),
    .po_sig_z_mem_if_wdata_i(mldsa_ctrl.sig_z_ram_wdata),
    .po_sig_z_mem_if_wstrobe_i(mldsa_ctrl.sig_z_ram_wstrobe),
    .po_sig_z_mem_if_re_i(mldsa_ctrl.sig_z_ram_re),
    .po_sig_z_mem_if_raddr_i(mldsa_ctrl.sig_z_ram_raddr),
    .pi_sig_z_mem_if_rdata_o(mldsa_ctrl.sig_z_ram_rdata),
    .po_pk_mem_if_we_i(mldsa_ctrl.pubkey_ram_we),
    .po_pk_mem_if_waddr_i(mldsa_ctrl.pubkey_ram_waddr),
    .po_pk_mem_if_wdata_i(mldsa_ctrl.pubkey_ram_wdata),
    .po_pk_mem_if_wstrobe_i(mldsa_ctrl.pubkey_ram_wstrobe),
    .po_pk_mem_if_re_i(mldsa_ctrl.pubkey_ram_re),
    .po_pk_mem_if_raddr_i(mldsa_ctrl.pubkey_ram_raddr),
    .pi_pk_mem_if_rdata_o(mldsa_ctrl.pubkey_ram_rdata),
    // LFSR interface
    .po_lfsr_enable_o(lfsr_enable_o),
    .po_lfsr_seed_o(lfsr_seed_o),
    .zeroize_mem_o(zeroize_mem_o),
    // Interrupts
    .po_error_intr(error_intr),
    .po_notif_intr(notif_intr),

    //debug
    .pi_debugUnlock_or_scan_mode_switch(debugUnlock_or_scan_mode_switch),
    .po_busy_o(busy_o)
);

