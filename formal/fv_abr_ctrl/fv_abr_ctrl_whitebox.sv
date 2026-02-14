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
module fv_abr_ctrl_whitebox
    import abr_params_pkg::*;
    import abr_sampler_pkg::*;
    import abr_ctrl_pkg::*;
    import abr_sha3_pkg::*;
    import abr_reg_pkg::*;
    import ntt_defines_pkg::*;
    import compress_defines_pkg::*;
    import decompress_defines_pkg::*;
#(
    //#$localparams
    localparam ABR_SEQ_NTT = 0
    //$#//
) (
    //#$ports
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
    input logic [MsgWidth-1:0]                         po_msg_data_o[Sha3Share],
    input logic                                        po_sampler_start_o,
    input logic                                        pi_sampler_busy_i,
    input logic                                        pi_sampler_state_dv_i,
    input logic [abr_sha3_pkg::StateW-1:0]             pi_sampler_state_data_i[Sha3Share],
    input logic [ABR_MEM_ADDR_WIDTH-1:0]               po_dest_base_addr_o,
    input logic [ABR_NUM_NTT-1:0]                      po_ntt_enable_o,
    input abr_ntt_mode_e [ABR_NUM_NTT-1:0]             po_ntt_mode_o,
    input ntt_mem_addr_t [ABR_NUM_NTT-1:0]             po_ntt_mem_base_addr_o,
    input pwo_mem_addr_t [ABR_NUM_NTT-1:0]             po_pwo_mem_base_addr_o,
    input logic [ABR_NUM_NTT-1:0]                      po_ntt_masking_en_o,
    input logic [ABR_NUM_NTT-1:0]                      po_ntt_shuffling_en_o,
    input logic [ABR_NUM_NTT-1:0]                      pi_ntt_busy_i,
    input logic [1:0][ABR_MEM_ADDR_WIDTH-1:0]          po_aux_src0_base_addr_o,
    input logic [1:0][ABR_MEM_ADDR_WIDTH-1:0]          po_aux_src1_base_addr_o,
    input logic [1:0][ABR_MEM_ADDR_WIDTH-1:0]          po_aux_dest_base_addr_o,
    input logic                                        po_power2round_enable_o,
    input mem_if_t [1:0]                               pi_pwr2rnd_keymem_if_i,
    input logic [1:0][DATA_WIDTH-1:0]                  pi_pwr2rnd_wr_data_i,
    input logic                                        pi_pk_t1_wren_i,
    input logic [7:0][9:0]                             pi_pk_t1_wrdata_i,
    input logic [7:0]                                  pi_pk_t1_wr_addr_i,
    input logic                                        pi_power2round_done_i,
    input logic                                        po_decompose_enable_o,
    input logic                                        po_decompose_mode_o,
    input logic                                        pi_decompose_done_i,
    input logic                                        po_skencode_enable_o,
    input mem_if_t                                     pi_skencode_keymem_if_i,
    input logic [DATA_WIDTH-1:0]                       pi_skencode_wr_data_i,
    input logic                                        pi_skencode_done_i,
    input logic                                        po_skdecode_enable_o,
    input mem_if_t [1:0]                               pi_skdecode_keymem_if_i,
    input logic [1:0][DATA_WIDTH-1:0]                  po_skdecode_rd_data_o,
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
    input logic [7:0]                                  pi_pkdecode_rd_addr_i,
    input logic [7:0][T1_COEFF_W-1:0]                  po_pkdecode_rd_data_o,
    input logic                                        pi_pkdecode_done_i,
    input logic                                        po_sigdecode_h_enable_o,
    input logic [SIGNATURE_H_VALID_NUM_BYTES-1:0][7:0] po_signature_h_o,
    input logic                                        pi_sigdecode_h_invalid_i,
    input logic                                        pi_sigdecode_h_done_i,
    input logic                                        po_sigdecode_z_enable_o,
    input mem_if_t                                     pi_sigdecode_z_rd_req_i,
    input logic [1:0][3:0][19:0]                       po_sigdecode_z_rd_data_o,
    input logic                                        pi_sigdecode_z_done_i,
    input logic                                        po_compress_enable_o,
    input compress_mode_t                              po_compress_mode_o,
    input logic                                        po_compress_compare_mode_o,
    input logic [2:0]                                  po_compress_num_poly_o,
    input logic                                        pi_compress_done_i,
    input logic                                        pi_compress_compare_failed_i,
    input logic [1:0]                                  pi_compress_api_rw_en_i,
    input logic [ABR_MEM_ADDR_WIDTH-1:0]               pi_compress_api_rw_addr_i,
    input logic [DATA_WIDTH-1:0]                       pi_compress_api_wr_data_i,
    input logic [DATA_WIDTH-1:0]                       po_compress_api_rd_data_o,
    input logic                                        po_decompress_enable_o,
    input logic                                        pi_decompress_done_i,
    input decompress_mode_t                            po_decompress_mode_o,
    input logic [2:0]                                  po_decompress_num_poly_o,
    input logic                                        pi_decompress_api_rd_en_i,
    input logic [ABR_MEM_ADDR_WIDTH-1:0]               pi_decompress_api_rd_addr_i,
    input logic [1:0][DATA_WIDTH-1:0]                  po_decompress_api_rd_data_o,
    input logic                                        po_lfsr_enable_o,
    input logic [1:0][LFSR_W-1:0]                      po_lfsr_seed_o,
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
    input logic [PK_MEM_DATA_W-1:0]                    pi_pk_mem_if_rdata_o
    //$#//
);

default clocking default_clk @(posedge pi_clk); endclocking

///////////////////Reset//////////////////////
// Reset check: After reset or zeroize, all relevant registers should be cleared
property reset_check_P;
    $past(!pi_rst_b || po_zeroize)
    |->
    !`abr_ctrl.mlkem_valid_reg &&
    `abr_ctrl.abr_scratch_reg == '0 &&
    `ifdef NO_ABSTRACTION
    !`abr_ctrl.mlkem_keygen_process &&
    !`abr_ctrl.mlkem_decaps_process &&
    !`abr_ctrl.mlkem_keygen_decaps_process &&
    `endif
    !`abr_ctrl.error_flag_reg &&
    `abr_ctrl.msg_cnt == '0
;endproperty
assert_reset_check_A: assert property (reset_check_P);




///////////////////Memory interfaces//////////////////////

logic [1:0] fv_compress_keymem_we_bank;
logic [1:0] fv_mlkem_api_dk_we_bank;
logic [1:0] fv_mlkem_api_ek_we_bank;
logic [1:0] fv_mlkem_api_ct_we_bank;
logic [1:0] fv_mlkem_api_msg_we_bank;
logic [1:0] fv_api_keymem_we_bank;
logic [1:0] fv_compress_keymem_re_bank;
logic [1:0] fv_mlkem_api_dk_re_bank;
logic [1:0] fv_sk_ram_re_bank;
logic [1:0] fv_mlkem_api_ct_re_bank;
logic [1:0] fv_mlkem_api_ek_re_bank;

logic [SK_MEM_BANK_ADDR_W:0] fv_mlkem_api_dk_waddr;
logic [SK_MEM_BANK_ADDR_W:0] fv_mlkem_api_dk_raddr;
logic [SK_MEM_BANK_ADDR_W:0] fv_mlkem_api_ek_mem_waddr;
logic [SK_MEM_BANK_ADDR_W:0] fv_mlkem_api_ek_mem_raddr;
logic [SK_MEM_BANK_ADDR_W:0] fv_mlkem_api_ek_reg_waddr;
logic [SK_MEM_BANK_ADDR_W:0] fv_mlkem_api_ek_reg_raddr;
logic [SK_MEM_BANK_ADDR_W:0] fv_mlkem_api_ek_waddr;
logic [SK_MEM_BANK_ADDR_W:0] fv_mlkem_api_ek_raddr;
logic [SK_MEM_BANK_ADDR_W:0] fv_mlkem_api_ct_waddr;
logic [SK_MEM_BANK_ADDR_W:0] fv_mlkem_api_ct_raddr;
logic [SK_MEM_BANK_ADDR_W:0] fv_mlkem_api_ct_mem_waddr;
logic [SK_MEM_BANK_ADDR_W:0] fv_mlkem_api_ct_mem_raddr;
logic [SK_MEM_BANK_ADDR_W:0] fv_mlkem_api_msg_waddr;
logic [SK_MEM_BANK_ADDR_W:0] fv_mlkem_api_msg_mem_waddr;
logic [SK_MEM_BANK_ADDR_W:0] fv_mlkem_api_dk_mem_waddr;
logic [SK_MEM_BANK_ADDR_W:0] fv_mlkem_api_dk_mem_raddr;
logic [1:0][SK_MEM_BANK_ADDR_W:0] fv_sk_ram_waddr_bank;
logic [1:0][SK_MEM_BANK_ADDR_W:0] fv_sk_ram_raddr_bank;
logic [DATA_WIDTH-1:0] fv_mlkem_msg_wdata;
logic [1:0][DATA_WIDTH-1:0] fv_sk_ram_wdata, fv_sk_ram_rdata;
logic fv_zeroize;
logic fv_zeroize_mem_we;



logic fv_abr_ready;
logic fv_abr_status_done;
logic fv_api_keymem_wr_dec;
logic fv_mlkem_api_dk_mem_rd_vld;
logic fv_mlkem_api_ek_mem_rd_vld;
logic fv_mlkem_api_ct_mem_rd_vld;
logic fv_mlkem_api_ek_reg_rd_dec;
logic fv_mlkem_api_dk_reg_rd_dec;
logic fv_error_flag_reg;

logic [DATA_WIDTH-1:0] fv_privkey_out_rdata;
mldsa_cmd_e fv_mldsa_cmd_reg;
mlkem_cmd_e fv_mlkem_cmd_reg;

// Zeroize is triggered when input reg is set or debugUnlock_or_scan_mode_switch is set
assign fv_zeroize = pi_abr_reg_hwif_out_i.MLDSA_CTRL.ZEROIZE.value || 
                        pi_abr_reg_hwif_out_i.MLKEM_CTRL.ZEROIZE.value ||
                        pi_debugUnlock_or_scan_mode_switch;
//ABR Ready allows writes to api registers
//No writes allowed during operation or when keyvault reads are in progress
  `ifdef CALIPTRA
  always_comb fv_abr_ready = (`abr_ctrl.abr_prog_cntr == ABR_RESET) & 
                          !`abr_ctrl.kv_mlkem_seed_write_en &
                          !`abr_ctrl.kv_mlkem_msg_write_en &
                          !`abr_ctrl.kv_mldsa_seed_write_en;
  `else
  always_comb fv_abr_ready = (`abr_ctrl.abr_prog_cntr == ABR_RESET);
  `endif

// api mem req from PI, if req_is_wr then it is wr if not a rd along with req.
// Addresses truncated and concatenated with zero's inorder to match the memory depth
// Trucated bits are used to identify the bank
always_comb begin : fv_mem_triggers
    fv_api_keymem_wr_dec = pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_IN.req & pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_IN.addr[12:2] inside {[31:PRIVKEY_NUM_DWORDS-1]};
    fv_mlkem_api_dk_waddr = {1'b0,pi_abr_reg_hwif_out_i.MLKEM_DECAPS_KEY.addr[11:2]};
    fv_mlkem_api_dk_raddr = {1'b0,pi_abr_reg_hwif_out_i.MLKEM_DECAPS_KEY.addr[11:2]};
    fv_mlkem_api_ek_mem_waddr = {2'b0,pi_abr_reg_hwif_out_i.MLKEM_ENCAPS_KEY.addr[10:2]} + MLKEM_DEST_EK_MEM_OFFSET[SK_MEM_BANK_ADDR_W:0];
    fv_mlkem_api_ek_mem_raddr = {2'b0,pi_abr_reg_hwif_out_i.MLKEM_ENCAPS_KEY.addr[10:2]} + MLKEM_DEST_EK_MEM_OFFSET[SK_MEM_BANK_ADDR_W:0];
    fv_mlkem_api_ek_reg_waddr = {5'b0,pi_abr_reg_hwif_out_i.MLKEM_ENCAPS_KEY.addr[4:2]};
    fv_mlkem_api_ek_reg_raddr = {5'b0,pi_abr_reg_hwif_out_i.MLKEM_ENCAPS_KEY.addr[4:2]};
    fv_mlkem_api_ek_waddr = {2'b0,pi_abr_reg_hwif_out_i.MLKEM_ENCAPS_KEY.addr[10:2]};
    fv_mlkem_api_ek_raddr = {2'b0,pi_abr_reg_hwif_out_i.MLKEM_ENCAPS_KEY.addr[10:2]};
    fv_mlkem_api_ct_waddr = {2'b0,pi_abr_reg_hwif_out_i.MLKEM_CIPHERTEXT.addr[10:2]};
    fv_mlkem_api_ct_raddr = {2'b0,pi_abr_reg_hwif_out_i.MLKEM_CIPHERTEXT.addr[10:2]};
    fv_mlkem_api_ct_mem_waddr = fv_mlkem_api_ct_waddr + MLKEM_DEST_C1_MEM_OFFSET[SK_MEM_BANK_ADDR_W:0];
    fv_mlkem_api_ct_mem_raddr = fv_mlkem_api_ct_raddr + MLKEM_DEST_C1_MEM_OFFSET[SK_MEM_BANK_ADDR_W:0];
    fv_mlkem_api_msg_waddr =  `abr_ctrl.kv_mlkem_msg_write_en ? {8'b0,`abr_ctrl.kv_mlkem_msg_write_offset} : {8'b0,pi_abr_reg_hwif_out_i.MLKEM_MSG.addr[4:2]};
    fv_mlkem_api_msg_mem_waddr = fv_mlkem_api_msg_waddr + MLKEM_DEST_MSG_MEM_OFFSET[SK_MEM_BANK_ADDR_W:0];
    fv_mlkem_msg_wdata = `abr_ctrl.kv_mlkem_msg_write_en ? `abr_ctrl.kv_mlkem_msg_write_data : pi_abr_reg_hwif_out_i.MLKEM_MSG.wr_data;
    fv_mlkem_api_dk_mem_rd_vld = pi_abr_reg_hwif_out_i.MLKEM_DECAPS_KEY.req & ~pi_abr_reg_hwif_out_i.MLKEM_DECAPS_KEY.req_is_wr & 
                                        `abr_ctrl.mlkem_valid_reg & ~`abr_ctrl.mlkem_dk_lock;
    fv_mlkem_api_ek_mem_rd_vld = pi_abr_reg_hwif_out_i.MLKEM_ENCAPS_KEY.req & ~pi_abr_reg_hwif_out_i.MLKEM_ENCAPS_KEY.req_is_wr & 
                                        `abr_ctrl.mlkem_valid_reg;
    fv_zeroize_mem_we = (`abr_ctrl.abr_prog_cntr == ABR_ZEROIZE);

    fv_mlkem_api_ct_mem_rd_vld = pi_abr_reg_hwif_out_i.MLKEM_CIPHERTEXT.req & ~pi_abr_reg_hwif_out_i.MLKEM_CIPHERTEXT.req_is_wr & 
                                        `abr_ctrl.mlkem_valid_reg;
end

always_comb begin:fv_mem
    for(int i=0; i<2; i++) begin
        fv_compress_keymem_we_bank[i] = (pi_compress_api_rw_en_i[0] & (pi_compress_api_rw_addr_i[0] == i));
        fv_mlkem_api_dk_we_bank[i] = pi_abr_reg_hwif_out_i.MLKEM_DECAPS_KEY.req & pi_abr_reg_hwif_out_i.MLKEM_DECAPS_KEY.req_is_wr 
                                    & fv_abr_ready & pi_abr_reg_hwif_out_i.MLKEM_DECAPS_KEY.req & (fv_mlkem_api_dk_waddr inside {[0:MLKEM_DK_MEM_NUM_DWORDS-1]}) & (fv_mlkem_api_dk_waddr[0] == i);
        fv_mlkem_api_ek_we_bank[i] = pi_abr_reg_hwif_out_i.MLKEM_ENCAPS_KEY.req & pi_abr_reg_hwif_out_i.MLKEM_ENCAPS_KEY.req_is_wr 
                                    & fv_abr_ready & (pi_abr_reg_hwif_out_i.MLKEM_ENCAPS_KEY.req & fv_mlkem_api_ek_waddr inside {[0:MLKEM_EK_MEM_NUM_DWORDS-1]}) & (fv_mlkem_api_ek_mem_waddr[0] == i);
        fv_mlkem_api_ct_we_bank[i] = pi_abr_reg_hwif_out_i.MLKEM_CIPHERTEXT.req & pi_abr_reg_hwif_out_i.MLKEM_CIPHERTEXT.req_is_wr & fv_abr_ready &
                                      pi_abr_reg_hwif_out_i.MLKEM_CIPHERTEXT.req & (fv_mlkem_api_ct_waddr inside {[0:MLKEM_CIPHERTEXT_MEM_NUM_DWORDS-1]}) & (fv_mlkem_api_ct_mem_waddr[0] == i);
        fv_mlkem_api_msg_we_bank[i] = ((pi_abr_reg_hwif_out_i.MLKEM_MSG.req & pi_abr_reg_hwif_out_i.MLKEM_MSG.req_is_wr
                                         & fv_abr_ready & pi_abr_reg_hwif_out_i.MLKEM_MSG.req & !`abr_ctrl.kv_mlkem_msg_data_present 
                                         & fv_mlkem_api_msg_waddr inside {[0:MLKEM_MSG_MEM_NUM_DWORDS-1]}) | `abr_ctrl.kv_mlkem_msg_write_en) & (fv_mlkem_api_msg_waddr[0] == i);


        fv_sk_ram_waddr_bank[i] = ({SK_MEM_BANK_ADDR_W{fv_compress_keymem_we_bank[i]}} & pi_compress_api_rw_addr_i[SK_MEM_BANK_ADDR_W:1]) |
                             ({SK_MEM_BANK_ADDR_W{fv_mlkem_api_dk_we_bank[i]}} & fv_mlkem_api_dk_waddr[SK_MEM_BANK_ADDR_W:1]) |
                             ({SK_MEM_BANK_ADDR_W{fv_mlkem_api_ek_we_bank[i]}} & fv_mlkem_api_ek_mem_waddr[SK_MEM_BANK_ADDR_W:1]) |
                             ({SK_MEM_BANK_ADDR_W{fv_mlkem_api_ct_we_bank[i]}} & fv_mlkem_api_ct_mem_waddr[SK_MEM_BANK_ADDR_W:1]) |
                             ({SK_MEM_BANK_ADDR_W{fv_mlkem_api_msg_we_bank[i]}} & fv_mlkem_api_msg_mem_waddr[SK_MEM_BANK_ADDR_W:1]) |
                             ({SK_MEM_BANK_ADDR_W{fv_zeroize_mem_we}} & `abr_ctrl.zeroize_mem_addr[SK_MEM_BANK_ADDR_W-1:0]);

        fv_sk_ram_wdata[i] = ({DATA_WIDTH{fv_compress_keymem_we_bank[i]}} & pi_compress_api_wr_data_i) |
                        ({DATA_WIDTH{fv_mlkem_api_dk_we_bank[i]}} & pi_abr_reg_hwif_out_i.MLKEM_DECAPS_KEY.wr_data) |
                        ({DATA_WIDTH{fv_mlkem_api_ek_we_bank[i]}} & pi_abr_reg_hwif_out_i.MLKEM_ENCAPS_KEY.wr_data) |
                        ({DATA_WIDTH{fv_mlkem_api_ct_we_bank[i]}} & pi_abr_reg_hwif_out_i.MLKEM_CIPHERTEXT.wr_data) |
                        ({DATA_WIDTH{fv_mlkem_api_msg_we_bank[i]}} & fv_mlkem_msg_wdata);         
        fv_compress_keymem_re_bank[i] = pi_compress_api_rw_en_i[1] & (pi_compress_api_rw_addr_i[0] == i);

        fv_mlkem_api_dk_re_bank[i] = fv_mlkem_api_dk_mem_rd_vld & pi_abr_reg_hwif_out_i.MLKEM_DECAPS_KEY.req & fv_mlkem_api_dk_raddr inside {[0:MLKEM_DK_MEM_NUM_DWORDS-1]} & (fv_mlkem_api_dk_raddr[0] == i);
        fv_mlkem_api_ek_re_bank[i] = fv_mlkem_api_ek_mem_rd_vld & pi_abr_reg_hwif_out_i.MLKEM_ENCAPS_KEY.req & fv_mlkem_api_ek_raddr inside {[0:MLKEM_EK_MEM_NUM_DWORDS-1]} & (fv_mlkem_api_ek_mem_raddr[0] == i);
        fv_mlkem_api_ct_re_bank[i] = fv_mlkem_api_ct_mem_rd_vld &  pi_abr_reg_hwif_out_i.MLKEM_CIPHERTEXT.req & fv_mlkem_api_ct_raddr inside {[0:MLKEM_CIPHERTEXT_MEM_NUM_DWORDS-1]} & (fv_mlkem_api_ct_mem_raddr[0] == i);

        fv_sk_ram_re_bank[i] = fv_mlkem_api_dk_re_bank[i] |  fv_mlkem_api_ek_re_bank[i] |
                          fv_mlkem_api_ct_re_bank[i] | `abr_ctrl.sampler_sk_rd_en | pi_decompress_api_rd_en_i | fv_compress_keymem_re_bank[i];

        fv_sk_ram_raddr_bank[i] =   ({SK_MEM_BANK_ADDR_W{fv_mlkem_api_dk_re_bank[i]}} & fv_mlkem_api_dk_raddr[SK_MEM_BANK_ADDR_W:1]) |
                                    ({SK_MEM_BANK_ADDR_W{fv_mlkem_api_ek_re_bank[i]}} & fv_mlkem_api_ek_mem_raddr[SK_MEM_BANK_ADDR_W:1]) |
                                    ({SK_MEM_BANK_ADDR_W{fv_mlkem_api_ct_re_bank[i]}} & fv_mlkem_api_ct_mem_raddr[SK_MEM_BANK_ADDR_W:1]) |
                                    ({SK_MEM_BANK_ADDR_W{pi_decompress_api_rd_en_i}} & pi_decompress_api_rd_addr_i[SK_MEM_BANK_ADDR_W-1:0]) |
                                    ({SK_MEM_BANK_ADDR_W{fv_compress_keymem_re_bank[i]}} & pi_compress_api_rw_addr_i[SK_MEM_BANK_ADDR_W:1]) |
                                    ({SK_MEM_BANK_ADDR_W{`abr_ctrl.sampler_sk_rd_en}} & (`abr_ctrl.sampler_src_offset[SK_MEM_BANK_ADDR_W-1:0] + `abr_ctrl.sampler_sk_rd_offset));

    end
end

// check sk mem interface outputs
// sk mem wr if it is dk,ek,ct,api,compress,zeroize
// sk mem rd if it is dk,ek,ct,decompress,compress,sampler
// we is high if any of the write enables are high
// waddr is the address of the enabled write
// wdata is the data of the enabled write
// re is high if any of the read enables are high
// raddr is the address of the enabled read
// only one write or read enable should be high at a time
property sk_mem_outputs_check_P;
    po_sk_bank0_mem_if_we_i == (fv_mlkem_api_dk_we_bank[0] | fv_mlkem_api_ek_we_bank[0] | fv_mlkem_api_ct_we_bank[0] | fv_compress_keymem_we_bank[0] | fv_mlkem_api_msg_we_bank[0] | fv_zeroize_mem_we) &&
    po_sk_bank0_mem_if_waddr_i == fv_sk_ram_waddr_bank[0] &&
    po_sk_bank0_mem_if_wdata_i == fv_sk_ram_wdata[0] &&
    po_sk_bank0_mem_if_re_i == fv_sk_ram_re_bank[0] &&
    po_sk_bank0_mem_if_raddr_i == fv_sk_ram_raddr_bank[0] &&
    po_sk_bank1_mem_if_we_i == (fv_mlkem_api_dk_we_bank[1] | fv_mlkem_api_ek_we_bank[1] | fv_mlkem_api_ct_we_bank[1] | fv_compress_keymem_we_bank[1] | fv_mlkem_api_msg_we_bank[1]| fv_zeroize_mem_we) &&
    po_sk_bank1_mem_if_waddr_i == fv_sk_ram_waddr_bank[1]&&
    po_sk_bank1_mem_if_wdata_i == fv_sk_ram_wdata[1]&&
    po_sk_bank1_mem_if_re_i == fv_sk_ram_re_bank[1]&&
    po_sk_bank1_mem_if_raddr_i == fv_sk_ram_raddr_bank[1]
;endproperty

assert_sk_mem_outputs_check_A: assert property (sk_mem_outputs_check_P);

// If there is a read enable for compress then data is
// from the sk ram.
property mlkem_compress_rd_data_o_P;
    |fv_compress_keymem_re_bank
    |=>
    po_compress_api_rd_data_o == ({DATA_WIDTH{$past(fv_compress_keymem_re_bank[0])}} & pi_sk_bank0_mem_if_rdata_o |
                                       {DATA_WIDTH{$past(fv_compress_keymem_re_bank[1])}} & pi_sk_bank1_mem_if_rdata_o);
endproperty
assert_mlkem_compress_rd_data_o_A: assert property (disable iff(!pi_rst_b || po_zeroize)mlkem_compress_rd_data_o_P);

// Decompress read data is always from sk ram data
property mlkem_decompress_rd_data_o_P;
    po_decompress_api_rd_data_o == {pi_sk_bank1_mem_if_rdata_o,pi_sk_bank0_mem_if_rdata_o}
;endproperty

assert_mlkem_decompress_rd_data_o_A: assert property (mlkem_decompress_rd_data_o_P);

    /////////////////////////////////////////////////////////
    // REGISTER INTERFACE
    /////////////////////////////////////////////////////////

    //MLKEM status, version and ready if ctrl is ready.
    // valid is asserted once the process is completed successfully
    // error is set if any error occurs during the process
    property mlkem_reg_if_name_status_check_P;
        po_abr_reg_hwif_in_o.MLKEM_NAME[0].NAME.next == MLKEM_CORE_NAME[31:0] &&
        po_abr_reg_hwif_in_o.MLKEM_NAME[1].NAME.next == MLKEM_CORE_NAME[63:32] &&
        po_abr_reg_hwif_in_o.MLKEM_VERSION[0].VERSION.next == MLKEM_CORE_VERSION[31:0] &&
        po_abr_reg_hwif_in_o.MLKEM_VERSION[1].VERSION.next == MLKEM_CORE_VERSION[63:32] &&
        po_abr_reg_hwif_in_o.MLKEM_STATUS.READY.next == fv_abr_ready &&
        po_abr_reg_hwif_in_o.MLKEM_STATUS.VALID.next == `abr_ctrl.mlkem_valid_reg && 
        po_abr_reg_hwif_in_o.MLKEM_STATUS.ERROR.next == fv_error_flag_reg; 
    endproperty
    assert_mlkem_reg_if_name_status_check_A: assert property (mlkem_reg_if_name_status_check_P);
    
    // seed_d register write enable, next value, hwclr and swwe conditions
    // hwclr is set on zeroize, data_present_reset or if kv read fails
    // swwe is set when abr is ready and kv data not present
    // next value is set to the kv write data when kv write enable is set
    property mlkem_reg_if_seed_D_check_P(dword);
      `ifdef CALIPTRA
      po_abr_reg_hwif_in_o.MLKEM_SEED_D[dword].SEED.we == ((`abr_ctrl.kv_mlkem_seed_write_en & (`abr_ctrl.kv_mlkem_seed_write_offset == dword))) & ~fv_zeroize &&
      po_abr_reg_hwif_in_o.MLKEM_SEED_D[dword].SEED.next == `abr_ctrl.kv_mlkem_seed_write_data &&
      po_abr_reg_hwif_in_o.MLKEM_SEED_D[dword].SEED.hwclr == fv_zeroize | `abr_ctrl.kv_data_present_reset | (`abr_ctrl.kv_mlkem_seed_error == KV_READ_FAIL) &&
      po_abr_reg_hwif_in_o.MLKEM_SEED_D[dword].SEED.swwe == fv_abr_ready & ~`abr_ctrl.kv_mlkem_seed_data_present;
      `else
      po_abr_reg_hwif_in_o.MLKEM_SEED_D[dword].SEED.we == '0 &&
      po_abr_reg_hwif_in_o.MLKEM_SEED_D[dword].SEED.next == '0 &&
      po_abr_reg_hwif_in_o.MLKEM_SEED_D[dword].SEED.hwclr == fv_zeroize && 
      po_abr_reg_hwif_in_o.MLKEM_SEED_D[dword].SEED.swwe == fv_abr_ready;
      `endif
    endproperty
    
    for (genvar dword=0; dword < SEED_NUM_DWORDS; dword++) begin
        assert_mlkem_reg_if_seed_D_check_A: assert property (mlkem_reg_if_seed_D_check_P(dword));
    end

    // seed_z register write enable and ack conditions
    // wr_ack is set when there is a write req from the pi
    property mlkem_reg_if_seed_Z_check_P(dword);
      po_abr_reg_hwif_in_o.MLKEM_SEED_Z[dword].wr_ack ==( pi_abr_reg_hwif_out_i.MLKEM_SEED_Z[dword].req & pi_abr_reg_hwif_out_i.MLKEM_SEED_Z[dword].req_is_wr);
    endproperty
    for (genvar dword=0; dword < SEED_NUM_DWORDS; dword++) begin
        assert_mlkem_reg_if_seed_Z_check_A: assert property (mlkem_reg_if_seed_Z_check_P(dword));
    end

    // shared_key register read ack and data conditions
    // rd_ack is set when there is a read req from the pi
    // rd_data is set to the shared key value when there is a read req from the pi and mlkem process is valid
    // otherwise it is set to 0
    // In caliptra, it is also checked if the kv read is successful and data is present
    // if not the rd_data is set to 0
    property mlkem_reg_if_shared_key_check_P(dword);
      po_abr_reg_hwif_in_o.MLKEM_SHARED_KEY[dword].rd_ack == (pi_abr_reg_hwif_out_i.MLKEM_SHARED_KEY[dword].req & ~pi_abr_reg_hwif_out_i.MLKEM_SHARED_KEY[dword].req_is_wr) &&
      `ifdef CALIPTRA
      po_abr_reg_hwif_in_o.MLKEM_SHARED_KEY[dword].rd_data == (`abr_ctrl.mlkem_valid_reg & ~`abr_ctrl.dest_keyvault & ~`abr_ctrl.kv_mlkem_seed_data_present & ~`abr_ctrl.kv_mlkem_msg_data_present ? 
                                                        `abr_ctrl.abr_scratch_reg.mlkem_enc.shared_key[dword] : '0);
      `else
      po_abr_reg_hwif_in_o.MLKEM_SHARED_KEY[dword].rd_data == (`abr_ctrl.mlkem_valid_reg ? `abr_ctrl.abr_scratch_reg.mlkem_enc.shared_key[dword] : '0);
      `endif
    endproperty

    for (genvar dword=0; dword < SHAREDKEY_NUM_DWORDS; dword++) begin
        assert_mlkem_reg_if_shared_key_check_A: assert property (mlkem_reg_if_shared_key_check_P(dword));
    end

always_comb begin: fv_api_ek_dk_privkey_out
        fv_privkey_out_rdata = {DATA_WIDTH{$past(fv_sk_ram_re_bank[0])}} & pi_sk_bank0_mem_if_rdata_o |
                                  {DATA_WIDTH{$past(fv_sk_ram_re_bank[1])}} & pi_sk_bank1_mem_if_rdata_o |
                                  {DATA_WIDTH{$past(fv_mlkem_api_ek_reg_rd_dec | fv_mlkem_api_ek_reg_rd_dec)}} & `abr_ctrl.api_reg_rdata;

        fv_mlkem_api_ek_reg_rd_dec = pi_abr_reg_hwif_out_i.MLKEM_ENCAPS_KEY.req & fv_mlkem_api_ek_raddr inside {[MLKEM_EK_MEM_NUM_DWORDS:EK_NUM_DWORDS-1]};
        fv_mlkem_api_dk_reg_rd_dec = pi_abr_reg_hwif_out_i.MLKEM_DECAPS_KEY.req & fv_mlkem_api_dk_raddr inside {[MLKEM_DK_MEM_NUM_DWORDS:DK_NUM_DWORDS-1]};

end

    // decaps_key, encaps_key and ciphertext register read ack and data conditions
    // rd_ack is set when there is a read req from the pi
    // rd_data is set to the priv key value when there is a read req from the pi and mlkem process is valid
    // otherwise it is set to 0
    // In caliptra, it is also checked if the kv read is successful and data is present
    // if not the rd_data is set to 0
    property mlkem_abr_reg_hwif_in_mem_assign_check_rd_P;
    ##1
        po_abr_reg_hwif_in_o.MLKEM_CIPHERTEXT.rd_ack == $past(pi_abr_reg_hwif_out_i.MLKEM_CIPHERTEXT.req & ~pi_abr_reg_hwif_out_i.MLKEM_CIPHERTEXT.req_is_wr) &&
        po_abr_reg_hwif_in_o.MLKEM_CIPHERTEXT.rd_data == ($past(pi_abr_reg_hwif_out_i.MLKEM_CIPHERTEXT.req & ~pi_abr_reg_hwif_out_i.MLKEM_CIPHERTEXT.req_is_wr) & `abr_ctrl.mlkem_valid_reg ? fv_privkey_out_rdata : '0) &&
        po_abr_reg_hwif_in_o.MLKEM_DECAPS_KEY.rd_ack == $past(pi_abr_reg_hwif_out_i.MLKEM_DECAPS_KEY.req & ~pi_abr_reg_hwif_out_i.MLKEM_DECAPS_KEY.req_is_wr) &&
        po_abr_reg_hwif_in_o.MLKEM_DECAPS_KEY.rd_data == ($past(pi_abr_reg_hwif_out_i.MLKEM_DECAPS_KEY.req & ~pi_abr_reg_hwif_out_i.MLKEM_DECAPS_KEY.req_is_wr) & `abr_ctrl.mlkem_valid_reg & ~`abr_ctrl.mlkem_dk_lock ? fv_privkey_out_rdata : '0) &&
        po_abr_reg_hwif_in_o.MLKEM_ENCAPS_KEY.rd_ack == $past(pi_abr_reg_hwif_out_i.MLKEM_ENCAPS_KEY.req & ~pi_abr_reg_hwif_out_i.MLKEM_ENCAPS_KEY.req_is_wr) &&
        po_abr_reg_hwif_in_o.MLKEM_ENCAPS_KEY.rd_data == ($past(pi_abr_reg_hwif_out_i.MLKEM_ENCAPS_KEY.req & ~pi_abr_reg_hwif_out_i.MLKEM_ENCAPS_KEY.req_is_wr) & `abr_ctrl.mlkem_valid_reg ? fv_privkey_out_rdata : '0)
        
    endproperty

    assert_mlkem_abr_reg_hwif_in_mem_assign_check_rd_A: assert property (disable iff(!pi_rst_b || po_zeroize) mlkem_abr_reg_hwif_in_mem_assign_check_rd_P);

    // decaps_key, encaps_key and message register write ack conditions
    // wr_ack is set when there is a write req from the pi
    property mlkem_abr_reg_hwif_in_mem_assign_check_wr_P;
        po_abr_reg_hwif_in_o.MLKEM_DECAPS_KEY.wr_ack == (pi_abr_reg_hwif_out_i.MLKEM_DECAPS_KEY.req & pi_abr_reg_hwif_out_i.MLKEM_DECAPS_KEY.req_is_wr) &&
        po_abr_reg_hwif_in_o.MLKEM_ENCAPS_KEY.wr_ack == (pi_abr_reg_hwif_out_i.MLKEM_ENCAPS_KEY.req & pi_abr_reg_hwif_out_i.MLKEM_ENCAPS_KEY.req_is_wr) &&
        po_abr_reg_hwif_in_o.MLKEM_MSG.rd_ack == (pi_abr_reg_hwif_out_i.MLKEM_MSG.req & ~pi_abr_reg_hwif_out_i.MLKEM_MSG.req_is_wr )&& // Read is not used thats why it is not flopped.
        po_abr_reg_hwif_in_o.MLKEM_MSG.rd_data == '0 &&
        po_abr_reg_hwif_in_o.MLKEM_MSG.wr_ack == (pi_abr_reg_hwif_out_i.MLKEM_MSG.req & pi_abr_reg_hwif_out_i.MLKEM_MSG.req_is_wr);
    endproperty
    assert_mlkem_abr_reg_hwif_in_mem_assign_check_wr_A: assert property (mlkem_abr_reg_hwif_in_mem_assign_check_wr_P);

// status done is set when there is a transition of valid from 0 to 1
// for either mldsa or mlkem status
always_comb fv_abr_status_done = (po_abr_reg_hwif_in_o.MLDSA_STATUS.VALID.next & ~pi_abr_reg_hwif_out_i.MLDSA_STATUS.VALID.value) || 
                                (po_abr_reg_hwif_in_o.MLKEM_STATUS.VALID.next & ~pi_abr_reg_hwif_out_i.MLKEM_STATUS.VALID.value);

// Interrupts from PI to ABR ctrl
property interrupts_check_P;
    po_error_intr == (pi_abr_reg_hwif_out_i.intr_block_rf.error_global_intr_r.intr) &&
    po_notif_intr == (pi_abr_reg_hwif_out_i.intr_block_rf.notif_global_intr_r.intr);
endproperty
assert_interrupts_check_A: assert property (interrupts_check_P);

// Interrupts from ABR ctrl
// error internal interrupt is set when there is an edge on error flag
// notif internal interrupt is set when there is a done status
property mlkem_abr_reg_interrupt_check_p;
    po_abr_reg_hwif_in_o.intr_block_rf.error_internal_intr_r.error_internal_sts.hwset == `abr_ctrl.error_flag_edge &&
    po_abr_reg_hwif_in_o.intr_block_rf.notif_internal_intr_r.notif_cmd_done_sts.hwset == fv_abr_status_done;
endproperty
assert_mlkem_abr_reg_interrupt_check_A: assert property (mlkem_abr_reg_interrupt_check_p);

/// reset and clr abr_Reg
assign    fv_mldsa_cmd_reg                 = mldsa_cmd_e'(pi_abr_reg_hwif_out_i.MLDSA_CTRL.CTRL.value);
assign    fv_mlkem_cmd_reg                 = mlkem_cmd_e'(pi_abr_reg_hwif_out_i.MLKEM_CTRL.CTRL.value);
property mlkem_abr_reg_reset_clr_check_P;
    po_zeroize                    == (pi_abr_reg_hwif_out_i.MLDSA_CTRL.ZEROIZE.value || 
                                        pi_abr_reg_hwif_out_i.MLKEM_CTRL.ZEROIZE.value ||
                                        pi_debugUnlock_or_scan_mode_switch) &&
    po_abr_reg_hwif_in_o.reset_b       == pi_rst_b &&
    po_abr_reg_hwif_in_o.hard_reset_b  == pi_rst_b &&
    po_abr_reg_hwif_in_o.abr_ready     == fv_abr_ready &&
    po_abr_reg_hwif_in_o.MLDSA_CTRL.CTRL.hwclr == |fv_mldsa_cmd_reg &&
    po_abr_reg_hwif_in_o.MLKEM_CTRL.CTRL.hwclr == |fv_mlkem_cmd_reg &&
    `ifdef CALIPTRA
    po_abr_reg_hwif_in_o.MLDSA_CTRL.PCR_SIGN.hwclr == pi_abr_reg_hwif_out_i.MLDSA_CTRL.PCR_SIGN.value &&
    `else
    po_abr_reg_hwif_in_o.MLDSA_CTRL.PCR_SIGN.hwclr == '0 &&
    `endif
    po_abr_reg_hwif_in_o.MLDSA_CTRL.EXTERNAL_MU.hwclr == pi_abr_reg_hwif_out_i.MLDSA_CTRL.EXTERNAL_MU.value
;endproperty
assert_mlkem_abr_reg_reset_clr_check_A: assert property (mlkem_abr_reg_reset_clr_check_P);



// Zeroize the mem addresses.

 logic [ABR_MEM_ADDR_WIDTH-1:0] fv_mem_addr_cntr;
always_ff @(posedge pi_clk, negedge pi_rst_b) begin
  if(!pi_rst_b || po_zeroize) begin
      fv_mem_addr_cntr <= '0;
    end
    else begin
      if(`abr_ctrl.abr_prog_cntr == ABR_ZEROIZE )begin
        if(fv_mem_addr_cntr == ABR_MEM_MAX_DEPTH)begin
          fv_mem_addr_cntr <= '0;
        end
        else begin
          fv_mem_addr_cntr <= fv_mem_addr_cntr + 1;
        end
      end
    end
end

// zeroize memory when in zeroize state
property zeroize_mem_if_zeroize_cntr;
  `abr_ctrl.abr_prog_cntr == ABR_ZEROIZE
  |->
  po_zeroize_mem_o.rd_wr_en ==  RW_WRITE &&
  po_zeroize_mem_o.addr == fv_mem_addr_cntr
;endproperty
assert_zeroize_mem_if_zeroize_cntr: assert property(zeroize_mem_if_zeroize_cntr);

// do not zeroize memory when not in zeroize state
property not_zeroize_mem_if_zeroize_cntr_reset;
  `abr_ctrl.abr_prog_cntr != ABR_ZEROIZE
  |->
  po_zeroize_mem_o.rd_wr_en ==  RW_IDLE 
;endproperty
assert_not_zeroize_mem_if_zeroize_cntr_reset: assert property(not_zeroize_mem_if_zeroize_cntr_reset);


// busy output when not in ready state
property abr_busy_check_P;
  po_busy_o == !(fv_abr_ready)
;endproperty
assert_abr_busy_check_A: assert property(abr_busy_check_P);

/////////////////////////////////////////////////////////////
// NTT addresses from operands
logic [ABR_NUM_NTT-1:0][ABR_MEM_ADDR_WIDTH-1:0] fv_ntt_temp_address;
    //passing a bit on the immediate field to mux between temp address locations
  assign fv_ntt_temp_address[ABR_SEQ_NTT] = (`abr_ctrl.abr_instr.imm[0] ? MLDSA_TEMP2_BASE[ABR_MEM_ADDR_WIDTH-1:0] : MLDSA_TEMP0_BASE[ABR_MEM_ADDR_WIDTH-1:0]);

// check ntt and pwo mem base addresses from operands
// ABR_MEM_ADDR_WIDTH is 10, so truncating the upper bits of the base addresses
// ABR_MEM_ADDR_WIDTH-1:0 to match the memory depth
// ABR_SEQ_NTT is 0, so only one ntt and pwo base address to check
property ntt_pwo_mem_base_addr_check_P;
  po_ntt_mem_base_addr_o[ABR_SEQ_NTT] == ('{src_base_addr:`abr_ctrl.abr_instr.operand1[ABR_MEM_ADDR_WIDTH-1:0],
                                        interim_base_addr:fv_ntt_temp_address[ABR_SEQ_NTT],
                                        dest_base_addr:`abr_ctrl.abr_instr.operand3[ABR_MEM_ADDR_WIDTH-1:0]}) &&
  po_pwo_mem_base_addr_o[ABR_SEQ_NTT] == ('{pw_base_addr_b:`abr_ctrl.abr_instr.operand1[ABR_MEM_ADDR_WIDTH-1:0], //PWO src
                                        pw_base_addr_a:`abr_ctrl.abr_instr.operand2[ABR_MEM_ADDR_WIDTH-1:0], //PWO src or sampler src
                                        pw_base_addr_c:`abr_ctrl.abr_instr.operand3[ABR_MEM_ADDR_WIDTH-1:0]});                                   
endproperty
assert_ntt_pwo_mem_base_addr_check_A: assert property (ntt_pwo_mem_base_addr_check_P);





    //////////////////////////////////////////////////////////
    // MSG CNT
    ///////////////////////////////////////////////////////////

    // msg cnt increments when in msg load state and msg rdy is high except for the very first packet
    // msg cnt resets when in idle state or zeroize
    // msg cnt holds its value when in msg load state and msg rdy is low
    // msg cnt width is 8 bits to support max message length of 256 bytes
    // msg cnt is compared with the length field of the instruction to determine when to stop loading
    // msg cnt is also compared with the max message length to prevent overflow
  logic [ABR_OPR_WIDTH-1:$clog2(MsgStrbW)] fv_msg_cnt;
   always_ff @( posedge pi_clk, negedge pi_rst_b ) begin : fv_msg_cnt_abs_logic
        if(!pi_rst_b) begin
            fv_msg_cnt <= '0;
        end
        else if(po_zeroize) begin
            fv_msg_cnt <= '0;
        end
        else begin
            if(`abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_IDLE) begin
                fv_msg_cnt <= '0;
            end
            else if(`abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_MSG_LOAD && ((fv_msg_cnt == '0)|| ((fv_msg_cnt <= `abr_ctrl.abr_instr.length[ABR_OPR_WIDTH-1:$clog2(MsgStrbW)]) && pi_msg_rdy_i))) begin
                fv_msg_cnt <= fv_msg_cnt + 1;
            end
            else if(`abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_MSG_LOAD && !pi_msg_rdy_i) begin
                fv_msg_cnt <= fv_msg_cnt;
            end
            else begin
                 fv_msg_cnt <= '0;
            end
        end
    end


`ifdef NO_ABSTRACTION
     property msg_cnt_p;
         `abr_ctrl.msg_cnt == fv_msg_cnt
    ;endproperty
    assert_msg_cnt: assert property(msg_cnt_p);
`endif


//////////////////////////////////////////////////////////////
// Error flag register
///////////////////////////////////////////////////////////////

// error flag is set when there is a compress compare fail during mlkem encaps or
// when there is a tr mismatch during mlkem decaps
property mlkem_error_set_P;
    (`abr_ctrl.abr_instr.opcode.aux_en && 
    (`abr_ctrl.abr_instr.opcode.mode.aux_mode == MLKEM_COMPRESS) &&
    po_compress_compare_mode_o &&
    pi_compress_compare_failed_i &&
    `abr_ctrl.mlkem_encaps_process) ||
    (pi_sampler_state_dv_i &&
    (`abr_ctrl.abr_instr.operand3 == MLKEM_DEST_TR_REG_ID) &&
    (pi_sampler_state_data_i[0][255:0] != `abr_ctrl.abr_scratch_reg.mlkem_enc.tr) &&
    `abr_ctrl.mlkem_decaps_process)
    |->
    `abr_ctrl.error_flag
;endproperty
assert_mlkem_error_set_A: assert property( disable iff(!pi_rst_b || po_zeroize) mlkem_error_set_P);

// error flag is not set when there is no compress compare fail during mlkem encaps or
// when there is no tr mismatch during mlkem decaps
property mlkem_error_no_set_P;
    !(`abr_ctrl.abr_instr.opcode.aux_en && 
    (`abr_ctrl.abr_instr.opcode.mode.aux_mode == MLKEM_COMPRESS) &&
    po_compress_compare_mode_o &&
    pi_compress_compare_failed_i &&
    `abr_ctrl.mlkem_encaps_process) &&
    !(pi_sampler_state_dv_i &&
    (`abr_ctrl.abr_instr.operand3 == MLKEM_DEST_TR_REG_ID) &&
    (pi_sampler_state_data_i[0][255:0] != `abr_ctrl.abr_scratch_reg.mlkem_enc.tr) &&
    `abr_ctrl.mlkem_decaps_process)
    |->
    !`abr_ctrl.error_flag
;endproperty
assert_mlkem_error_no_set_P: assert property(disable iff(!pi_rst_b || po_zeroize) mlkem_error_no_set_P);

always_ff @(posedge pi_clk, negedge pi_rst_b) begin
    if(!pi_rst_b || po_zeroize) begin
        fv_error_flag_reg <= 1'b0;
    end
    else begin
        if(`abr_ctrl.error_flag) begin
            fv_error_flag_reg <= 1'b1;
        end
    end
end


//////////////////////////////////////////////
// sampler rd en and offset used in the sk ram 
//////////////////////////////////////////////
// sampler sk rd en is set when in msg load state and
// when the program counter is in the mlkem decaps state or
// in the mlkem encaps state + 2 (to read the ek) or
// in the mlkem kg state + 39 (to read the ek) and
// the msg cnt is less than or equal to 191 (to read the 192 dwords of ek) or
// when the program counter is in the mlkem encaps state + 3 (to read the msg) and
// the msg cnt is less than or equal to 7 (to read the 8 dwords of msg) or
// when the program counter is in the mlkem decaps check state + 1 (to read the cipher) and
// the msg cnt is less than or equal to 195 (to read the 196 dwords of cipher) and
// msg hold is not set
// sampler sk rd en is not set when not in the above conditions
property mlkem_sampler_sk_rd_en_P;
    (((((`abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_S) ||
    (`abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 2) ||
    (`abr_ctrl.abr_prog_cntr == MLKEM_KG_S + 39)) && 
    (`abr_ctrl.msg_cnt inside {[0:191]})) ||
    ((`abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 3) &&
    (`abr_ctrl.msg_cnt inside{[0:7]})) ||
    ((`abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_CHK + 1) &&
    (`abr_ctrl.msg_cnt inside {[0:195]}))) &&
    !`abr_ctrl.msg_hold &&
    `abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_MSG_LOAD)
    |->
    `abr_ctrl.sampler_sk_rd_en
;endproperty
assert_mlkem_sampler_sk_rd_en_A: assert property(mlkem_sampler_sk_rd_en_P);

property mlkem_sampler_no_sk_rd_en_P;
    !((((`abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_S) ||
    (`abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 2) ||
    (`abr_ctrl.abr_prog_cntr == MLKEM_KG_S + 39) && 
    (`abr_ctrl.msg_cnt inside {[0:191]})) ||
    ((`abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 3) &&
    (`abr_ctrl.msg_cnt inside{[0:7]})) ||
    ((`abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_CHK + 1) &&
    (`abr_ctrl.msg_cnt inside {[0:195]}))) &&
    !`abr_ctrl.msg_hold &&
    `abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_MSG_LOAD)
    |->
    !`abr_ctrl.sampler_sk_rd_en
;endproperty
assert_mlkem_sampler_no_sk_rd_en_A: assert property(mlkem_sampler_no_sk_rd_en_P);

// sampler sk rd offset is set to ek offset when in the mlkem decaps state or
// in the mlkem encaps state + 2 (to read the ek) or
// in the mlkem kg state + 39 (to read the ek) and
property mlkem_sampler_sk_rd_offset_ek_reg_P;
    ((`abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_S) ||
    (`abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 2) ||
    (`abr_ctrl.abr_prog_cntr == MLKEM_KG_S + 39) ) &&
    `abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_MSG_LOAD
    |->
    `abr_ctrl.sampler_sk_rd_offset == (MLKEM_DEST_EK_MEM_OFFSET/2)
;endproperty
assert_mlkem_sampler_sk_rd_offset_ek_reg_A: assert property(mlkem_sampler_sk_rd_offset_ek_reg_P);

// sampler sk rd offset is set to msg offset when in the mlkem encaps state + 3 (to read the msg)

property mlkem_sampler_sk_rd_offset_msg_P;
    ((`abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 3) ) &&
    `abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_MSG_LOAD
    |->
    `abr_ctrl.sampler_sk_rd_offset == (MLKEM_DEST_MSG_MEM_OFFSET/2)
;endproperty
assert_mlkem_sampler_sk_rd_offset_msg_A: assert property(mlkem_sampler_sk_rd_offset_msg_P);

// sampler sk rd offset is set to cipher offset when in the mlkem decaps check state + 1 (to read the cipher)
property mlkem_sampler_sk_rd_offset_cipher_P;
    ((`abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_CHK + 1) ) &&
    `abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_MSG_LOAD
    |->
    `abr_ctrl.sampler_sk_rd_offset == (MLKEM_DEST_C1_MEM_OFFSET/2)
;endproperty
assert_mlkem_sampler_sk_rd_offset_cipher_A: assert property(mlkem_sampler_sk_rd_offset_cipher_P);

// sampler sk rd offset is 0 when not in the above states
property mlkem_sampler_sk_rd_no_offset_P;
    !((`abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_S) ||
    (`abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 2) ||
    (`abr_ctrl.abr_prog_cntr == MLKEM_KG_S + 39) ||
    (`abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 3) ||
    (`abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_CHK + 1))
    |->
    `abr_ctrl.sampler_sk_rd_offset == '0
;endproperty
assert_mlkem_sampler_sk_rd_no_offset_A: assert property(mlkem_sampler_sk_rd_no_offset_P);

//////////////////////////////////////////////////////////////
// Main register abr_scratch register which is used for the data
// to either be sent to keccak or to be written
// to the memory
///////////////////////////////////////////////////////////////

// scratch reg from sampler when dv is high and dest is rho and sigma reg
// rho and sigma are updated and other fields are stable
property mlkem_abr_scratch_reg_dest_rho_sigma_check_P;
    pi_sampler_state_dv_i &&
    `abr_ctrl.abr_instr.operand3 == MLKEM_DEST_RHO_SIGMA_REG_ID
    |=>
    `abr_ctrl.abr_scratch_reg.mlkem_enc.rho == $past(pi_sampler_state_data_i[0][255:0]) &&
    `abr_ctrl.abr_scratch_reg.mlkem_enc.sigma == $past(pi_sampler_state_data_i[0][511:256]) &&
    $stable(`abr_ctrl.abr_scratch_reg.mlkem_enc.shared_key) &&
    $stable(`abr_ctrl.abr_scratch_reg.mlkem_enc.tr)
;endproperty
assert_mlkem_abr_scratch_reg_dest_rho_sigma_check_A: assert property(disable iff(!pi_rst_b || po_zeroize) mlkem_abr_scratch_reg_dest_rho_sigma_check_P);

// scratch reg from sampler when dv is high and dest is tr reg
// tr is updated and other fields are stable
property mlkem_abr_scratch_reg_dest_tr_check_P;
    pi_sampler_state_dv_i &&
    `abr_ctrl.abr_instr.operand3 == MLKEM_DEST_TR_REG_ID
    |=>
    `abr_ctrl.abr_scratch_reg.mlkem_enc.tr == $past(pi_sampler_state_data_i[0][255:0]) &&
    $stable(`abr_ctrl.abr_scratch_reg.mlkem_enc.shared_key) &&
    $stable(`abr_ctrl.abr_scratch_reg.mlkem_enc.rho) &&
    $stable(`abr_ctrl.abr_scratch_reg.mlkem_enc.sigma)
;endproperty
assert_mlkem_abr_scratch_reg_dest_tr_check_A: assert property(disable iff(!pi_rst_b || po_zeroize) mlkem_abr_scratch_reg_dest_tr_check_P);

// scratch reg from sampler when dv is high and dest is shared key reg
// and decaps is in process
// shared key is updated and other fields are stable
property mlkem_abr_scratch_reg_dest_shared_key_check_P;
    pi_sampler_state_dv_i &&
    `abr_ctrl.abr_instr.operand3 == MLKEM_DEST_K_REG_ID &&
    !`abr_ctrl.decaps_valid &&
    `abr_ctrl.mlkem_decaps_process
    |=>
    `abr_ctrl.abr_scratch_reg.mlkem_enc.shared_key == $past(pi_sampler_state_data_i[0][255:0]) &&
    $stable(`abr_ctrl.abr_scratch_reg.mlkem_enc.rho) &&
    $stable(`abr_ctrl.abr_scratch_reg.mlkem_enc.sigma) &&
    $stable(`abr_ctrl.abr_scratch_reg.mlkem_enc.tr)
;endproperty
assert_mlkem_abr_scratch_reg_dest_shared_key_check_A: assert property(disable iff(!pi_rst_b || po_zeroize) mlkem_abr_scratch_reg_dest_shared_key_check_P);  

// scratch reg from sampler when dv is high and dest is shared key reg
// and encaps is in process
// shared key is stable and other fields are stable
property mlkem_abr_scratch_reg_dest_shared_key_check_stable_P;
    pi_sampler_state_dv_i &&
    `abr_ctrl.abr_instr.operand3 == MLKEM_DEST_K_REG_ID &&
    !(!`abr_ctrl.decaps_valid &&
    `abr_ctrl.mlkem_decaps_process)
    |=>
    $stable(`abr_ctrl.abr_scratch_reg.mlkem_enc.shared_key) &&
    $stable(`abr_ctrl.abr_scratch_reg.mlkem_enc.rho) &&
    $stable(`abr_ctrl.abr_scratch_reg.mlkem_enc.sigma) &&
    $stable(`abr_ctrl.abr_scratch_reg.mlkem_enc.tr)
;endproperty
assert_mlkem_abr_scratch_reg_dest_shared_key_check_stable_A: assert property(disable iff(!pi_rst_b || po_zeroize) mlkem_abr_scratch_reg_dest_shared_key_check_stable_P);

// scratch reg from sampler when dv is high and dest is kr reg
// rho and sigma are updated and other fields are stable
property mlkem_abr_scratch_reg_dest_kr_check_P;
    pi_sampler_state_dv_i &&
    `abr_ctrl.abr_instr.operand3 == MLKEM_DEST_K_R_REG_ID
    |=>
    $stable(`abr_ctrl.abr_scratch_reg.mlkem_enc.tr) &&
    (`abr_ctrl.abr_scratch_reg.mlkem_enc.shared_key) == $past(pi_sampler_state_data_i[0][255:0]) &&
    $stable(`abr_ctrl.abr_scratch_reg.mlkem_enc.rho) &&
    (`abr_ctrl.abr_scratch_reg.mlkem_enc.sigma) == $past(pi_sampler_state_data_i[0][511:256])
;endproperty
assert_mlkem_abr_scratch_reg_dest_kr_check_A: assert property(disable iff(!pi_rst_b || po_zeroize) mlkem_abr_scratch_reg_dest_kr_check_P);

// scratch reg from api when there is a write req from the pi to the encap key reg
// and the waddr is in the ek mem range
// the corresponding dword in the scratch reg is updated with the wr data
// other fields are stable
property mlkem_abr_scratch_reg_ek_api_check_P;
    pi_abr_reg_hwif_out_i.MLKEM_ENCAPS_KEY.req &&
    pi_abr_reg_hwif_out_i.MLKEM_ENCAPS_KEY.req_is_wr &&
    fv_abr_ready && 
    (fv_mlkem_api_ek_waddr inside {[MLKEM_EK_MEM_NUM_DWORDS:EK_NUM_DWORDS-1]})
    |=>
    `abr_ctrl.abr_scratch_reg.raw[$past(fv_mlkem_api_ek_reg_waddr)] == $past(pi_abr_reg_hwif_out_i.MLKEM_ENCAPS_KEY.wr_data)
;endproperty
assert_mlkem_abr_scratch_reg_ek_api_check_A: assert property(disable iff(!pi_rst_b || po_zeroize) mlkem_abr_scratch_reg_ek_api_check_P);

// scratch reg from api when there is a write req from the pi to the decap key reg
// and the waddr is in the dk mem range
// the corresponding dword in the scratch reg is updated with the wr data
property mlkem_abr_scratch_reg_dk_api_check_P;
    pi_abr_reg_hwif_out_i.MLKEM_DECAPS_KEY.req && 
    pi_abr_reg_hwif_out_i.MLKEM_DECAPS_KEY.req_is_wr &&
    fv_abr_ready && 
    (fv_mlkem_api_dk_waddr inside {[MLKEM_DK_MEM_NUM_DWORDS:DK_NUM_DWORDS-1]}) &&
    !(pi_abr_reg_hwif_out_i.MLKEM_ENCAPS_KEY.req &&
    pi_abr_reg_hwif_out_i.MLKEM_ENCAPS_KEY.req_is_wr )
    |=>
    `abr_ctrl.abr_scratch_reg.raw[$past({1'b0,fv_mlkem_api_dk_waddr[4:0]})] == $past(pi_abr_reg_hwif_out_i.MLKEM_DECAPS_KEY.wr_data)
;endproperty
assert_mlkem_abr_scratch_reg_dk_api_check_A: assert property(disable iff(!pi_rst_b || po_zeroize) mlkem_abr_scratch_reg_dk_api_check_P);

// scratch reg from api when there is a write req from the pi to the seed z reg dword i
// and the waddr is in the seed z mem range
// the corresponding dword in the scratch reg is updated with the wr data
 property mlkem_abr_scratch_reg_seed_z_check_P(i);
    (pi_abr_reg_hwif_out_i.MLKEM_SEED_Z[i].req &&
    pi_abr_reg_hwif_out_i.MLKEM_SEED_Z[i].req_is_wr &&
    fv_abr_ready && !`abr_ctrl.kv_mlkem_seed_data_present) &&
    !(pi_abr_reg_hwif_out_i.MLKEM_ENCAPS_KEY.req &&
     pi_abr_reg_hwif_out_i.MLKEM_ENCAPS_KEY.req_is_wr ) &&
    !(pi_abr_reg_hwif_out_i.MLKEM_DECAPS_KEY.req &&
     pi_abr_reg_hwif_out_i.MLKEM_DECAPS_KEY.req_is_wr)
    |=>
    `abr_ctrl.abr_scratch_reg.mlkem_enc.seed_z[$past(i)] == $past(pi_abr_reg_hwif_out_i.MLKEM_SEED_Z[i].wr_data)
;endproperty


`ifdef CALIPTRA
// scratch reg from kv when there is a write req from the kv to the seed z reg dword i
// and the waddr is in the seed z mem range
// the corresponding dword in the scratch reg is updated with the wr data
    property mlkem_abr_scratch_reg_seed_z_kv_check_P(i);
     (`abr_ctrl.kv_mlkem_seed_write_en &&
     (`abr_ctrl.kv_mlkem_seed_write_offset == (SEED_NUM_DWORDS + i))) 
        |=>
      `abr_ctrl.abr_scratch_reg.mlkem_enc.seed_z[$past(i)] == $past(`abr_ctrl.kv_mlkem_seed_write_data)
    ;endproperty
`endif

logic[SEED_NUM_DWORDS-1:0] fv_seed_req;
for (genvar i = 0; i < SEED_NUM_DWORDS; i++) begin
        assert_mlkem_abr_scratch_reg_seed_z_check_A: assert property(disable iff(!pi_rst_b || po_zeroize) mlkem_abr_scratch_reg_seed_z_check_P(i));
        `ifdef CALIPTRA
         assert_mlkem_abr_scratch_reg_seed_z_kv_check_A: assert property(disable iff(!pi_rst_b || po_zeroize) mlkem_abr_scratch_reg_seed_z_kv_check_P(i));
        `endif
end

always_comb begin
    for (int i = 0; i < SEED_NUM_DWORDS; i++) begin
        fv_seed_req[i] = (pi_abr_reg_hwif_out_i.MLKEM_SEED_Z[i].req && pi_abr_reg_hwif_out_i.MLKEM_SEED_Z[i].req_is_wr);
    end
end

// scratch reg is stable when there is no write from sampler or api to the scratch reg
// and abr is ready
// or when there is a write to the seed z reg from the api or kv and the seed data is not present
// the scratch reg holds its value
property mlkem_abr_scratch_reg_stable_check_P;
        !((pi_sampler_state_dv_i &&
        (`abr_ctrl.abr_instr.operand3 == MLKEM_DEST_RHO_SIGMA_REG_ID)) ||
        (pi_sampler_state_dv_i &&
        (`abr_ctrl.abr_instr.operand3 == MLKEM_DEST_TR_REG_ID)) ||
        (pi_sampler_state_dv_i &&
        (`abr_ctrl.abr_instr.operand3 == MLKEM_DEST_K_REG_ID) &&
        !`abr_ctrl.decaps_valid &&
        `abr_ctrl.mlkem_decaps_process) ||
        (pi_sampler_state_dv_i &&
        (`abr_ctrl.abr_instr.operand3 == MLKEM_DEST_K_R_REG_ID)) ||
        (pi_abr_reg_hwif_out_i.MLKEM_ENCAPS_KEY.req & pi_abr_reg_hwif_out_i.MLKEM_ENCAPS_KEY.req_is_wr & fv_abr_ready & 
        (fv_mlkem_api_ek_waddr inside {[MLKEM_EK_MEM_NUM_DWORDS:EK_NUM_DWORDS-1]})) ||
        (pi_abr_reg_hwif_out_i.MLKEM_DECAPS_KEY.req & pi_abr_reg_hwif_out_i.MLKEM_DECAPS_KEY.req_is_wr & fv_abr_ready & 
        (fv_mlkem_api_dk_waddr inside {[MLKEM_DK_MEM_NUM_DWORDS:DK_NUM_DWORDS-1]})) ||
        (|fv_seed_req &&
        fv_abr_ready && !`abr_ctrl.kv_mlkem_seed_data_present)
        )
        |=> 
        $stable(`abr_ctrl.abr_scratch_reg)
    ;endproperty
    assert_mlkem_abr_scratch_reg_stable_check_A: assert property(disable iff(!pi_rst_b || po_zeroize) mlkem_abr_scratch_reg_stable_check_P);

`ifdef NO_ABSTRACTION
    // mlkem process signals
    // process signals are set when the cmd is set and the program counter is in the respective range
    // process signals are not set when the cmd is not set or the program counter is not in the respective range
    property mlkem_process_set_P;
        `abr_ctrl.mlkem_keygen_process == ((`abr_ctrl.mlkem_cmd_reg == MLKEM_KEYGEN) && (`abr_ctrl.abr_prog_cntr >= MLKEM_KG_S) && (`abr_ctrl.abr_prog_cntr <= MLKEM_KG_E)) &&
        `abr_ctrl.mlkem_encaps_process == ((`abr_ctrl.mlkem_cmd_reg == MLKEM_ENCAPS) && (`abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S) && (`abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_E)) &&
        `abr_ctrl.mlkem_decaps_process == (((`abr_ctrl.mlkem_cmd_reg == MLKEM_DECAPS) && (`abr_ctrl.abr_prog_cntr >= MLKEM_DECAPS_S) && (`abr_ctrl.abr_prog_cntr <= MLKEM_DECAPS_E)) || 
                                            ((`abr_ctrl.mlkem_cmd_reg == MLKEM_KEYGEN_DEC) && (`abr_ctrl.abr_prog_cntr >= MLKEM_DECAPS_S) && (`abr_ctrl.abr_prog_cntr <= MLKEM_DECAPS_E))) &&
        `abr_ctrl.mlkem_keygen_decaps_process == ((`abr_ctrl.mlkem_cmd_reg == MLKEM_KEYGEN_DEC) && ((`abr_ctrl.abr_prog_cntr >= MLKEM_KG_S) && (`abr_ctrl.abr_prog_cntr <= MLKEM_DECAPS_E)))
    ;endproperty
    assert_mlkem_process_set_A: assert property(disable iff(!pi_rst_b || po_zeroize || fv_error_flag_reg) mlkem_process_set_P);
`endif


//////////////////////////////////////////////////////////////
// MLKEM valid reg and the process signals

// valid reg is set when in the last state of the respective process
// valid reg is not set when not in the last state of the respective process
property mlkem_valid_reg_keygen_P;
    `abr_ctrl.mlkem_keygen_process &&
    `abr_ctrl.abr_prog_cntr == MLKEM_KG_E
    |=>
    `abr_ctrl.mlkem_valid_reg
;endproperty
assert_mlkem_valid_reg_keygen_A: assert property(disable iff(!pi_rst_b || po_zeroize) mlkem_valid_reg_keygen_P);

property mlkem_valid_reg_encaps_P;
    `abr_ctrl.mlkem_encaps_process &&
    `abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_E
    |=>
    `abr_ctrl.mlkem_valid_reg
;endproperty
assert_mlkem_valid_reg_encaps_A: assert property(disable iff(!pi_rst_b || po_zeroize) mlkem_valid_reg_encaps_P);

property mlkem_valid_reg_decaps_P;
    `abr_ctrl.mlkem_decaps_process &&
    `abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_E
    |=>
    `abr_ctrl.mlkem_valid_reg
;endproperty
assert_mlkem_valid_reg_decaps_A: assert property(disable iff(!pi_rst_b || po_zeroize) mlkem_valid_reg_decaps_P);

property mlkem_valid_reg_keygen_decaps_P;
    `abr_ctrl.mlkem_keygen_decaps_process &&
    `abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_E
    |=>
    `abr_ctrl.mlkem_valid_reg
;endproperty
assert_mlkem_valid_reg_keygen_decaps_A: assert property(disable iff(!pi_rst_b || po_zeroize) mlkem_valid_reg_keygen_decaps_P);

property mlkem_valid_reg_no_set_P;
    !(`abr_ctrl.mlkem_keygen_process &&
    `abr_ctrl.abr_prog_cntr == MLKEM_KG_E) &&
    !(`abr_ctrl.mlkem_encaps_process &&
    `abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_E) &&
    !(`abr_ctrl.mlkem_decaps_process &&
    `abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_E)
    |=>
    !`abr_ctrl.mlkem_valid_reg
;endproperty
assert_mlkem_valid_reg_no_set_A: assert property(disable iff(!pi_rst_b || po_zeroize) mlkem_valid_reg_no_set_P);

//////////////////////////////////////////////////////////////
// MLDSA all outputs should be set to zero
///////////////////////////////////////////////////////////////

property mldsa_outputs_zero_P;
    !po_power2round_enable_o &&
    !po_decompose_enable_o &&
    !po_skencode_enable_o &&
    !po_skdecode_enable_o &&
    !po_makehint_enable_o &&
    !po_normcheck_enable_o &&
    !po_sigencode_enable_o &&
    !po_pkdecode_enable_o &&
    !po_sigdecode_h_enable_o &&
    !po_sigdecode_z_enable_o &&
    !po_lfsr_enable_o &&
    !`abr_ctrl.mldsa_keygen_process &&
    !`abr_ctrl.mldsa_signing_process &&
    !`abr_ctrl.mldsa_verifying_process &&
    !`abr_ctrl.mldsa_keygen_signing_process &&
    !`abr_ctrl.mldsa_valid_reg &&
    !`abr_ctrl.signature_valid &&
    !`abr_ctrl.verify_valid &&
    !`abr_ctrl.mldsa_process_done
;endproperty
assert_mldsa_outputs_zero_A: assert property(disable iff(!pi_rst_b || po_zeroize) mldsa_outputs_zero_P);

//////////////////////////////////////////////////////////////
// Keyvault specific properties
// Note: Currently not tested in caliptra mode since keyvault files aren't available.
///////////////////////////////////////////////////////////////

`ifndef CALIPTRA

    property kv_all_set_to_zero_no_caliptra_P;
        `abr_ctrl.kv_mlkem_seed_data_present == '0 &&
        `abr_ctrl.kv_mlkem_msg_data_present == '0 &&
        `abr_ctrl.kv_mldsa_seed_data_present == '0 &&
        `abr_ctrl.kv_mlkem_msg_write_en == '0 &&
        `abr_ctrl.kv_mlkem_msg_write_offset == '0 &&
        `abr_ctrl.kv_mlkem_msg_write_data == '0 &&
        po_abr_reg_hwif_in_o.kv_mldsa_seed_rd_status.ERROR.next == '0 &&
        po_abr_reg_hwif_in_o.kv_mldsa_seed_rd_status.READY.next == '0 &&
        po_abr_reg_hwif_in_o.kv_mldsa_seed_rd_status.VALID.hwset == '0 &&
        po_abr_reg_hwif_in_o.kv_mldsa_seed_rd_status.VALID.hwclr == '0 &&
        po_abr_reg_hwif_in_o.kv_mldsa_seed_rd_ctrl.read_en.hwclr == '0 &&
        po_abr_reg_hwif_in_o.kv_mlkem_seed_rd_status.ERROR.next == '0 &&
        po_abr_reg_hwif_in_o.kv_mlkem_seed_rd_status.READY.next == '0 &&
        po_abr_reg_hwif_in_o.kv_mlkem_seed_rd_status.VALID.hwset == '0 &&
        po_abr_reg_hwif_in_o.kv_mlkem_seed_rd_status.VALID.hwclr == '0 &&
        po_abr_reg_hwif_in_o.kv_mlkem_seed_rd_ctrl.read_en.hwclr == '0 &&
        po_abr_reg_hwif_in_o.kv_mlkem_msg_rd_status.ERROR.next == '0 &&
        po_abr_reg_hwif_in_o.kv_mlkem_msg_rd_status.READY.next == '0 &&
        po_abr_reg_hwif_in_o.kv_mlkem_msg_rd_status.VALID.hwset == '0 &&
        po_abr_reg_hwif_in_o.kv_mlkem_msg_rd_status.VALID.hwclr == '0 &&
        po_abr_reg_hwif_in_o.kv_mlkem_msg_rd_ctrl.read_en.hwclr == '0 &&
        po_abr_reg_hwif_in_o.kv_mlkem_sharedkey_wr_status.ERROR.next == '0 &&
        po_abr_reg_hwif_in_o.kv_mlkem_sharedkey_wr_status.READY.next == '0 &&
        po_abr_reg_hwif_in_o.kv_mlkem_sharedkey_wr_status.VALID.hwset == '0 &&
        po_abr_reg_hwif_in_o.kv_mlkem_sharedkey_wr_status.VALID.hwclr == '0 &&
        po_abr_reg_hwif_in_o.kv_mlkem_sharedkey_wr_ctrl.write_en.hwclr == '0
    ;endproperty
    assert_kv_all_set_to_zero_no_caliptra_A: assert property(kv_all_set_to_zero_no_caliptra_P);

`endif

endmodule

