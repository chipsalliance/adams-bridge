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


module fv_mldsa_ctrl_whitebox 
    import mldsa_reg_pkg::*;
    import abr_sha3_pkg::*;
    import mldsa_sampler_pkg::*;
    import mldsa_ctrl_pkg::*;
    import mldsa_params_pkg::*;
    import ntt_defines_pkg::*;
#(
    // Parameters
    parameter ADAMSBRIDGE_CNTRL_RDY_DELAY     = 1,
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
    input logic [1:0][LFSR_W-1:0] po_lfsr_seed_o,
    input logic                                       po_sk_bank0_mem_if_we_i,
    input logic [SK_MEM_BANK_ADDR_W-1:0]              po_sk_bank0_mem_if_waddr_i,
    input logic [DATA_WIDTH-1:0]                      po_sk_bank0_mem_if_wdata_i,
    input logic                                       po_sk_bank0_mem_if_re_i,
    input logic [SK_MEM_BANK_ADDR_W-1:0]              po_sk_bank0_mem_if_raddr_i,
    input logic [DATA_WIDTH-1:0]                      pi_sk_bank0_mem_if_rdata_o,
    input logic                                       po_sk_bank1_mem_if_we_i,
    input logic [SK_MEM_BANK_ADDR_W-1:0]              po_sk_bank1_mem_if_waddr_i,
    input logic [DATA_WIDTH-1:0]                      po_sk_bank1_mem_if_wdata_i,
    input logic                                       po_sk_bank1_mem_if_re_i,
    input logic [SK_MEM_BANK_ADDR_W-1:0]              po_sk_bank1_mem_if_raddr_i,
    input logic [DATA_WIDTH-1:0]                      pi_sk_bank1_mem_if_rdata_o,

    input logic                                       po_sig_z_mem_if_we_i,
    input logic [SIG_Z_MEM_ADDR_W-1:0]                po_sig_z_mem_if_waddr_i,
    input logic [SIG_Z_MEM_DATA_W-1:0]                po_sig_z_mem_if_wdata_i,
    input logic [SIG_Z_MEM_DATA_W/8-1:0]              po_sig_z_mem_if_wstrobe_i,
    input logic                                       po_sig_z_mem_if_re_i,
    input logic [SIG_Z_MEM_ADDR_W-1:0]                po_sig_z_mem_if_raddr_i,
    input logic [SIG_Z_MEM_DATA_W-1:0]                pi_sig_z_mem_if_rdata_o,
    input logic                                       po_pk_mem_if_we_i,
    input logic [PK_ADDR_W-1:0]                       po_pk_mem_if_waddr_i,
    input logic [PK_MEM_DATA_W-1:0]                   po_pk_mem_if_wdata_i,
    input logic [PK_MEM_DATA_W/8-1:0]                 po_pk_mem_if_wstrobe_i,
    input logic                                       po_pk_mem_if_re_i,
    input logic [PK_ADDR_W-1:0]                       po_pk_mem_if_raddr_i,
    input logic [PK_MEM_DATA_W-1:0]                   pi_pk_mem_if_rdata_o,

    input mem_if_t                                    zeroize_mem_o,

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

    property reset_P;
      $past(!pi_rst_b || po_zeroize) 
      |->
      mldsa_ctrl.mldsa_privkey_lock &&
      mldsa_ctrl.privatekey_reg == '0 &&
      mldsa_ctrl.publickey_reg  == '0 &&
      mldsa_ctrl.pk_reg_rdata == '0 &&
      mldsa_ctrl.signature_reg == '0 &&
      mldsa_ctrl.rho_p_reg == '0 &&
      mldsa_ctrl.signature_reg_rdata == '0 &&
      mldsa_ctrl.privkey_reg_rdata == '0 &&
      !mldsa_ctrl.c_valid &&
      !mldsa_ctrl.w0_valid &&
      !mldsa_ctrl.y_valid &&
      !mldsa_ctrl.verify_valid &&
      !mldsa_ctrl.mldsa_status_done_p &&
      !mldsa_ctrl.signature_valid &&
      !mldsa_ctrl.signature_rd_ack &&
      !mldsa_ctrl.pubkey_rd_ack &&
      !mldsa_ctrl.privkey_out_rd_ack
    ;endproperty

    assert_reset_A: assert property(reset_P);

    property rst_b_P;
      $past(!pi_rst_b)
      |->
      po_lfsr_seed_o == '0 &&
      mldsa_ctrl.lfsr_entropy_reg == '0
    ;endproperty

    assert_rst_b_A: assert property(rst_b_P);


    property mldsa_reg_hwif_in_comb_P;
         po_abr_reg_hwif_in_o.reset_b == pi_rst_b &&
         po_abr_reg_hwif_in_o.hard_reset_b == pi_rst_b &&
         po_abr_reg_hwif_in_o.mldsa_ready == (mldsa_ctrl.prim_prog_cntr == MLDSA_RESET) &&
         mldsa_ctrl.cmd_reg == pi_abr_reg_hwif_out_i.MLDSA_CTRL.CTRL.value &&
         po_abr_reg_hwif_in_o.MLDSA_CTRL.CTRL.hwclr == |mldsa_ctrl.cmd_reg &&
         po_abr_reg_hwif_in_o.MLDSA_CTRL.EXTERNAL_MU.hwclr == pi_abr_reg_hwif_out_i.MLDSA_CTRL.EXTERNAL_MU.value &&
        `ifdef CALIPTRA
          po_abr_reg_hwif_in_o.MLDSA_CTRL.PCR_SIGN.hwclr == pi_abr_reg_hwif_out_i.MLDSA_CTRL.PCR_SIGN.value &&
        `else
          po_abr_reg_hwif_in_o.MLDSA_CTRL.PCR_SIGN.hwclr == '0 &&
        `endif

        po_abr_reg_hwif_in_o.MLDSA_NAME[0].NAME.next == '0 &&
        po_abr_reg_hwif_in_o.MLDSA_NAME[1].NAME.next == '0 &&
        po_abr_reg_hwif_in_o.MLDSA_VERSION[0].VERSION.next == '0 &&
        po_abr_reg_hwif_in_o.MLDSA_VERSION[1].VERSION.next == '0 &&

        po_abr_reg_hwif_in_o.MLDSA_STATUS.READY.next == (mldsa_ctrl.prim_prog_cntr == MLDSA_RESET) &&
        po_abr_reg_hwif_in_o.MLDSA_STATUS.VALID.next == mldsa_ctrl.mldsa_valid_reg &&

        po_zeroize == (pi_abr_reg_hwif_out_i.MLDSA_CTRL.ZEROIZE.value || pi_debugUnlock_or_scan_mode_switch) &&
        po_error_intr == pi_abr_reg_hwif_out_i.intr_block_rf.error_global_intr_r.intr &&
        po_notif_intr == pi_abr_reg_hwif_out_i.intr_block_rf.notif_global_intr_r.intr &&
        po_abr_reg_hwif_in_o.intr_block_rf.error_internal_intr_r.error_internal_sts.hwset ==  mldsa_ctrl.error_flag_edge &&
        po_abr_reg_hwif_in_o.intr_block_rf.notif_internal_intr_r.notif_cmd_done_sts.hwset == mldsa_ctrl.mldsa_status_done_p &&
        po_abr_reg_hwif_in_o.MLDSA_SIGNATURE.wr_ack == (pi_abr_reg_hwif_out_i.MLDSA_SIGNATURE.req &  pi_abr_reg_hwif_out_i.MLDSA_SIGNATURE.req_is_wr)
;endproperty

assert_mldsa_reg_hwif_in_comb_P: assert property(mldsa_reg_hwif_in_comb_P);


// Outputs combination for the data out parts which involves the dwords

    property entropy_reg_per_word(dword);
       mldsa_ctrl.entropy_reg[dword] == pi_abr_reg_hwif_out_i.MLDSA_ENTROPY[ENTROPY_NUM_DWORDS-1-dword].ENTROPY.value &&
      po_abr_reg_hwif_in_o.MLDSA_ENTROPY[dword].ENTROPY.hwclr == po_zeroize
    ;endproperty

    for (genvar dword=0; dword < ENTROPY_NUM_DWORDS; dword++)begin
       assert_entropy_reg_per_word: assert property(entropy_reg_per_word(dword));
    end

    property seed_reg_per_dword(dword);
      mldsa_ctrl.seed_reg[dword] == pi_abr_reg_hwif_out_i.MLDSA_SEED[SEED_NUM_DWORDS-1-dword].SEED.value &&

      `ifdef CALIPTRA
      po_abr_reg_hwif_in_o.MLDSA_SEED[dword].SEED.we == (mldsa_ctrl.pcr_sign_mode | (mldsa_ctrl.kv_seed_write_en & (mldsa_ctrl.kv_seed_write_offset == dword))) & ~po_zeroize &&
      po_abr_reg_hwif_in_o.MLDSA_SEED[dword].SEED.next == mldsa_ctrl.pcr_sign_mode   ? mldsa_ctrl.pcr_signing_data.pcr_mldsa_signing_seed[dword]  &&
                                                      mldsa_ctrl.kv_seed_write_data &&
      po_abr_reg_hwif_in_o.MLDSA_SEED[dword].SEED.hwclr == po_zeroize | mldsa_ctrl.kv_seed_data_present_reset | (mldsa_ctrl.kv_seed_error == KV_READ_FAIL) &&
      po_abr_reg_hwif_in_o.MLDSA_SEED[dword].SEED.swwe == mldsa_ctrl.mldsa_ready & ~mldsa_ctrl.kv_seed_data_present
      `else
      po_abr_reg_hwif_in_o.MLDSA_SEED[dword].SEED.we == '0 &&
      po_abr_reg_hwif_in_o.MLDSA_SEED[dword].SEED.next == '0 &&
      po_abr_reg_hwif_in_o.MLDSA_SEED[dword].SEED.hwclr == po_zeroize &&
      po_abr_reg_hwif_in_o.MLDSA_SEED[dword].SEED.swwe == mldsa_ctrl.mldsa_ready
      `endif
    ;endproperty

    for (genvar dword=0; dword < SEED_NUM_DWORDS; dword++)begin
       assert_seed_reg_per_dword: assert property(seed_reg_per_dword(dword));
    end

    property msg_reg_per_dword(dword);
      mldsa_ctrl.msg_reg[dword] ==( mldsa_ctrl.external_mu_mode? '0 : pi_abr_reg_hwif_out_i.MLDSA_MSG[MSG_NUM_DWORDS-1-dword].MSG.value) &&
      `ifdef CALIPTRA
      po_abr_reg_hwif_in_o.MLDSA_MSG[dword].MSG.we == mldsa_ctrl.pcr_sign_mode & !mldsa_ctrl.external_mu & !po_zeroize &&
      po_abr_reg_hwif_in_o.MLDSA_MSG[dword].MSG.next == mldsa_ctrl.pcr_signing_data.pcr_hash[dword] &&
      po_abr_reg_hwif_in_o.MLDSA_MSG[dword].MSG.hwclr == po_zeroize
      `else
      po_abr_reg_hwif_in_o.MLDSA_MSG[dword].MSG.we == '0 &&
      po_abr_reg_hwif_in_o.MLDSA_MSG[dword].MSG.next == '0 &&
      po_abr_reg_hwif_in_o.MLDSA_MSG[dword].MSG.hwclr == po_zeroize
      `endif
    ;endproperty
    for (genvar dword=0; dword < MSG_NUM_DWORDS; dword++)begin
      assert_msg_reg_per_dword: assert property(msg_reg_per_dword(dword));
    end

    property external_mu_reg_per_dword(dword);
      mldsa_ctrl.external_mu_reg[dword] == pi_abr_reg_hwif_out_i.MLDSA_EXTERNAL_MU[MU_NUM_DWORDS-1-dword].EXTERNAL_MU.value &&
      po_abr_reg_hwif_in_o.MLDSA_EXTERNAL_MU[dword].EXTERNAL_MU.we == (pi_sampler_state_dv_i & (mldsa_ctrl.prim_instr.operand3 == MLDSA_DEST_MU_REG_ID) & !mldsa_ctrl.external_mu & !po_zeroize) &&
      po_abr_reg_hwif_in_o.MLDSA_EXTERNAL_MU[dword].EXTERNAL_MU.next == mldsa_ctrl.internal_mu_reg[MU_NUM_DWORDS-1-dword] &&
      po_abr_reg_hwif_in_o.MLDSA_EXTERNAL_MU[dword].EXTERNAL_MU.hwclr == po_zeroize
    ;endproperty


    for (genvar dword=0; dword < MU_NUM_DWORDS; dword++)begin
      assert_external_mu_reg_per_dword: assert property(external_mu_reg_per_dword(dword));
    end


    property sign_rnd_reg_per_dword(dword);
      mldsa_ctrl.sign_rnd_reg[dword] == pi_abr_reg_hwif_out_i.MLDSA_SIGN_RND[SIGN_RND_NUM_DWORDS-1-dword].SIGN_RND.value &&
      po_abr_reg_hwif_in_o.MLDSA_SIGN_RND[dword].SIGN_RND.hwclr == po_zeroize
    ;endproperty
    for (genvar dword=0; dword < SIGN_RND_NUM_DWORDS; dword++)begin
      assert_sign_rnd_reg_per_dword: assert property(sign_rnd_reg_per_dword(dword));
    end

    property verify_reg_per_dword(dword);
      po_abr_reg_hwif_in_o.MLDSA_VERIFY_RES[dword].VERIFY_RES.we == ( mldsa_ctrl.verify_valid & pi_sampler_state_dv_i & (mldsa_ctrl.prim_instr.operand3 == MLDSA_DEST_VERIFY_RES_REG_ID)) &&      
      po_abr_reg_hwif_in_o.MLDSA_VERIFY_RES[VERIFY_RES_NUM_DWORDS-1-dword].VERIFY_RES.next == pi_sampler_state_data_i[0][dword*32 +: 32] &&
      po_abr_reg_hwif_in_o.MLDSA_VERIFY_RES[dword].VERIFY_RES.hwclr == (po_zeroize | (mldsa_ctrl.verifying_process & ((pi_normcheck_done_i & pi_normcheck_invalid_i) | 
                                   (mldsa_ctrl.prim_instr.opcode.aux_en & (mldsa_ctrl.prim_instr.opcode.mode.aux_mode == MLDSA_SIGDEC_H) & pi_sigdecode_h_invalid_i))))
    ;endproperty

    for (genvar dword=0; dword < VERIFY_RES_NUM_DWORDS; dword++)begin
      assert_verify_reg_per_dword : assert property(verify_reg_per_dword(dword));
    end

    property entropy_clr_per_dword(dword);
      po_abr_reg_hwif_in_o.MLDSA_ENTROPY[dword].ENTROPY.hwclr == po_zeroize;
    endproperty

    for (genvar dword=0; dword < ENTROPY_NUM_DWORDS; dword++)begin
        assert_entropy_clr_per_dword: assert property(entropy_clr_per_dword(dword));
    end
  

///////////////////////////
// Memory INterface outputs
///////////////////////////

  //logic fv_zeroize_mem_we;
  //logic [MLDSA_MEM_ADDR_WIDTH-1:0] fv_zeroize_mem_addr;
  //logic fv_zeroize_mem_done;
  logic [1:0] fv_skencode_keymem_we_bank;
  logic [1:0] fv_pwr2rnd_keymem_we_bank;
  logic [1:0] fv_api_keymem_we_bank,fv_skdecode_re_bank;
  logic [1:0] fv_sk_ram_we_bank,fv_sk_ram_re_bank;
  logic [1:0][SK_MEM_BANK_ADDR_W-1:0] fv_sk_ram_waddr_bank,fv_sk_ram_raddr_bank;
  logic [1:0][DATA_WIDTH-1:0] fv_sk_ram_wdata;

  logic [SK_MEM_BANK_ADDR_W:0] fv_api_sk_mem_waddr;
  logic [1:0][SK_MEM_BANK_ADDR_W:0] fv_skdecode_rdaddr;
  logic fv_api_keymem_rd_vld;
  logic [1:0] fv_api_keymem_re_bank;
  logic [SIG_ADDR_W-1:0] fv_api_sig_addr;
  mldsa_signature_z_addr_t fv_api_sig_z_addr;
  mldsa_signature_z_addr_t fv_api_sig_z_addr_f;
  logic [SIG_C_REG_ADDR_W-1:0] fv_api_sig_c_addr;
  logic [SIG_H_REG_ADDR_W-1:0] fv_api_sig_h_addr;
  logic fv_api_sig_z_we;
  logic fv_api_sig_z_re;
  logic fv_api_sig_c_dec;
  logic fv_api_sig_z_dec;
  logic fv_api_sig_h_dec;
  logic fv_sig_z_ram_we;
logic [SIG_Z_MEM_ADDR_W-1:0] fv_sig_z_ram_waddr;
logic [SIG_Z_MEM_WSTROBE_W-1:0] fv_sig_z_ram_wstrobe;
logic [SIG_Z_MEM_NUM_DWORD-1:0][31:0]  fv_sig_z_ram_wdata;
logic fv_sig_z_ram_re;
logic [SIG_Z_MEM_ADDR_W-1:0] fv_sig_z_ram_raddr;
logic fv_pubkey_ram_we;
logic fv_api_pubkey_we;
logic [PK_MEM_ADDR_W-1:0] fv_pubkey_ram_waddr;
logic [PK_MEM_WSTROBE_W-1:0] fv_pubkey_ram_wstrobe;
logic [PK_MEM_NUM_DWORDS-1:0][31:0] fv_pubkey_ram_wdata;
logic fv_pubkey_ram_re;
logic [PK_MEM_ADDR_W-1:0] fv_pubkey_ram_raddr;
logic fv_api_pubkey_re;


// sk_mem interface.

  always_comb begin
    for (int i = 0; i < 2; i++) begin
      fv_skencode_keymem_we_bank[i] = ((pi_skencode_keymem_if_i.rd_wr_en == RW_WRITE) & (pi_skencode_keymem_if_i.addr[0] == i));
      fv_pwr2rnd_keymem_we_bank[i] = (pi_pwr2rnd_keymem_if_i[i].rd_wr_en == RW_WRITE);
      fv_api_keymem_we_bank[i] = po_abr_reg_hwif_in_o.MLDSA_PRIVKEY_IN.wr_ack & mldsa_ctrl.mldsa_ready & mldsa_ctrl.api_keymem_wr_dec & (mldsa_ctrl.api_sk_mem_waddr[0] == i);

      fv_sk_ram_we_bank[i] = fv_skencode_keymem_we_bank[i] | fv_pwr2rnd_keymem_we_bank[i] | fv_api_keymem_we_bank[i] | mldsa_ctrl.zeroize_mem_we;

      fv_sk_ram_waddr_bank[i] = ({SK_MEM_BANK_ADDR_W{fv_skencode_keymem_we_bank[i]}} & pi_skencode_keymem_if_i.addr[SK_MEM_BANK_ADDR_W:1]) |
                             ({SK_MEM_BANK_ADDR_W{fv_pwr2rnd_keymem_we_bank[i]}} & pi_pwr2rnd_keymem_if_i[i].addr[SK_MEM_BANK_ADDR_W:1] ) |
                             ({SK_MEM_BANK_ADDR_W{fv_api_keymem_we_bank[i]}} & mldsa_ctrl.api_sk_mem_waddr[SK_MEM_BANK_ADDR_W:1]) |
                             ({SK_MEM_BANK_ADDR_W{mldsa_ctrl.zeroize_mem_we}} & mldsa_ctrl.zeroize_mem_addr[SK_MEM_BANK_ADDR_W-1:0]);
                 
      fv_sk_ram_wdata[i] = ({DATA_WIDTH{fv_skencode_keymem_we_bank[i]}} & pi_skencode_wr_data_i) |
                        ({DATA_WIDTH{fv_pwr2rnd_keymem_we_bank[i]}} & pi_pwr2rnd_wr_data_i[i]) |
                        ({DATA_WIDTH{fv_api_keymem_we_bank[i]}} & pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_IN.wr_data);         
    end
  end
  assign fv_api_keymem_rd_vld = pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_OUT.req & ~pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_OUT.req_is_wr & 
                                  mldsa_ctrl.mldsa_valid_reg & ~mldsa_ctrl.mldsa_privkey_lock ;


   always_comb begin
    for (int i = 0; i < 2; i++) begin
      fv_api_keymem_re_bank[i] = fv_api_keymem_rd_vld & mldsa_ctrl.api_keymem_rd_dec & (mldsa_ctrl.api_sk_mem_raddr[0] == i);

      fv_skdecode_re_bank[i] = (pi_skdecode_keymem_if_i[i].rd_wr_en == RW_READ);

      fv_skdecode_rdaddr[i] = pi_skdecode_keymem_if_i[i].addr[SK_MEM_BANK_ADDR_W:0];

      fv_sk_ram_re_bank[i] = fv_skdecode_re_bank[i] | fv_api_keymem_re_bank[i];

      fv_sk_ram_raddr_bank[i] = ({SK_MEM_BANK_ADDR_W{fv_skdecode_re_bank[i]}} & fv_skdecode_rdaddr[i][SK_MEM_BANK_ADDR_W:1]) |
                             ({SK_MEM_BANK_ADDR_W{fv_api_keymem_re_bank[i]}} & mldsa_ctrl.api_sk_mem_raddr[SK_MEM_BANK_ADDR_W:1]);

    end
  end


  always_comb begin
    fv_api_sig_addr = SIGNATURE_NUM_DWORDS-1-pi_abr_reg_hwif_out_i.MLDSA_SIGNATURE.addr[SIG_ADDR_W+1:2];
    fv_api_sig_c_dec = pi_abr_reg_hwif_out_i.MLDSA_SIGNATURE.req & fv_api_sig_addr inside {[0:SIGNATURE_C_NUM_DWORDS-1]};
    fv_api_sig_z_dec = pi_abr_reg_hwif_out_i.MLDSA_SIGNATURE.req & fv_api_sig_addr inside {[SIGNATURE_C_NUM_DWORDS:SIGNATURE_C_NUM_DWORDS+SIGNATURE_Z_NUM_DWORDS-1]};
    fv_api_sig_h_dec = pi_abr_reg_hwif_out_i.MLDSA_SIGNATURE.req & fv_api_sig_addr inside {[SIGNATURE_C_NUM_DWORDS+SIGNATURE_Z_NUM_DWORDS:SIGNATURE_NUM_DWORDS-1]};
    fv_api_sig_z_addr.addr   = SIG_Z_MEM_ADDR_W'( (fv_api_sig_addr - SIGNATURE_C_NUM_DWORDS)/SIG_Z_MEM_NUM_DWORD );
    fv_api_sig_z_addr.offset = (fv_api_sig_addr - SIGNATURE_C_NUM_DWORDS)%SIG_Z_MEM_NUM_DWORD;
    fv_api_sig_c_addr = fv_api_sig_addr[SIG_C_REG_ADDR_W-1:0];
    fv_api_sig_h_addr = SIG_H_REG_ADDR_W'( fv_api_sig_addr - (SIGNATURE_C_NUM_DWORDS+SIGNATURE_Z_NUM_DWORDS) );
    fv_api_sig_z_we = mldsa_ctrl.mldsa_ready & fv_api_sig_z_dec & po_abr_reg_hwif_in_o.MLDSA_SIGNATURE.wr_ack;
    fv_api_sig_z_re = mldsa_ctrl.mldsa_valid_reg & fv_api_sig_z_dec & ~pi_abr_reg_hwif_out_i.MLDSA_SIGNATURE.req_is_wr;
  end

property sk_mem_if_outputs_comb;
  po_sk_bank0_mem_if_we_i  == fv_sk_ram_we_bank[0] &&
  po_sk_bank0_mem_if_waddr_i  == fv_sk_ram_waddr_bank[0] &&
  po_sk_bank0_mem_if_wdata_i  == fv_sk_ram_wdata[0] &&
  po_sk_bank0_mem_if_re_i  == fv_sk_ram_re_bank[0] &&
  po_sk_bank0_mem_if_raddr_i  == fv_sk_ram_raddr_bank[0] &&
  po_sk_bank1_mem_if_we_i  == fv_sk_ram_we_bank[1] &&
  po_sk_bank1_mem_if_waddr_i  == fv_sk_ram_waddr_bank[1] &&
  po_sk_bank1_mem_if_wdata_i  == fv_sk_ram_wdata[1] &&
  po_sk_bank1_mem_if_re_i  == fv_sk_ram_re_bank[1] &&
  po_sk_bank1_mem_if_raddr_i  == fv_sk_ram_raddr_bank[1]
;endproperty

assert_sk_mem_if_outputs_comb: assert property(disable iff(!pi_rst_b || po_zeroize) sk_mem_if_outputs_comb);



  //write requests
  always_comb fv_sig_z_ram_we = (pi_sigencode_wr_req_i.rd_wr_en == RW_WRITE) | fv_api_sig_z_we | mldsa_ctrl.zeroize_mem_we;
  always_comb fv_sig_z_ram_waddr = ({SIG_Z_MEM_ADDR_W{(pi_sigencode_wr_req_i.rd_wr_en == RW_WRITE)}} & pi_sigencode_wr_req_i.addr[SIG_Z_MEM_ADDR_W:1]) |
                                ({SIG_Z_MEM_ADDR_W{fv_api_sig_z_we}} & fv_api_sig_z_addr.addr) |
                                ({SIG_Z_MEM_ADDR_W{mldsa_ctrl.zeroize_mem_we}} & mldsa_ctrl.zeroize_mem_addr[SIG_Z_MEM_ADDR_W-1:0]);

  always_comb fv_sig_z_ram_wstrobe = ({SIG_Z_MEM_WSTROBE_W{(pi_sigencode_wr_req_i.rd_wr_en == RW_WRITE)}}) |
                                  ({SIG_Z_MEM_WSTROBE_W{fv_api_sig_z_we}} & ('hF << fv_api_sig_z_addr.offset*4)) |
                                  ({SIG_Z_MEM_WSTROBE_W{mldsa_ctrl.zeroize_mem_we}});


  always_comb fv_sig_z_ram_wdata = ({SIG_Z_MEM_DATA_W{(pi_sigencode_wr_req_i.rd_wr_en == RW_WRITE)}} & pi_sigencode_wr_data_i) |
                                ({SIG_Z_MEM_DATA_W{(fv_api_sig_z_we)}} & SIG_Z_MEM_DATA_W'(pi_abr_reg_hwif_out_i.MLDSA_SIGNATURE.wr_data << fv_api_sig_z_addr.offset*32));

//read requests
  always_comb fv_sig_z_ram_re = (pi_sigdecode_z_rd_req_i.rd_wr_en == RW_READ) | fv_api_sig_z_re;
  always_comb fv_sig_z_ram_raddr = ({SIG_Z_MEM_ADDR_W{(pi_sigdecode_z_rd_req_i.rd_wr_en == RW_READ)}} & pi_sigdecode_z_rd_req_i.addr[SIG_Z_MEM_ADDR_W:1]) |
                                ({SIG_Z_MEM_ADDR_W{fv_api_sig_z_re}} & fv_api_sig_z_addr.addr);

property sig_z_mem_outputs_comb;
  po_sig_z_mem_if_we_i  == fv_sig_z_ram_we &&
  po_sig_z_mem_if_waddr_i  == fv_sig_z_ram_waddr &&
  po_sig_z_mem_if_wdata_i  == fv_sig_z_ram_wdata &&
  po_sig_z_mem_if_wstrobe_i  == fv_sig_z_ram_wstrobe &&
  po_sig_z_mem_if_re_i  == fv_sig_z_ram_re &&
  po_sig_z_mem_if_raddr_i  == fv_sig_z_ram_raddr &&
  po_sigdecode_z_rd_data_o == pi_sig_z_mem_if_rdata_o
;endproperty

assert_sig_z_mem_outputs_comb : assert property(disable iff(!pi_rst_b || po_zeroize) sig_z_mem_outputs_comb);


//write requests
  always_comb fv_pubkey_ram_we = (pi_pk_t1_wren_i) | fv_api_pubkey_we | mldsa_ctrl.zeroize_mem_we;
  always_comb fv_pubkey_ram_waddr = ({PK_MEM_ADDR_W{pi_pk_t1_wren_i}} & pi_pk_t1_wr_addr_i[PK_MEM_ADDR_W+1:2]) |
                                ({PK_MEM_ADDR_W{fv_api_pubkey_we}} & mldsa_ctrl.api_pubkey_mem_addr.addr) |
                                ({PK_MEM_ADDR_W{mldsa_ctrl.zeroize_mem_we}} & mldsa_ctrl.zeroize_mem_addr[PK_MEM_ADDR_W-1:0]);

  always_comb fv_pubkey_ram_wstrobe = ({PK_MEM_WSTROBE_W{pi_pk_t1_wren_i}} & 'h3FF << pi_pk_t1_wr_addr_i[1:0]*10) |
                                   ({PK_MEM_WSTROBE_W{fv_api_pubkey_we}} & ('hF << mldsa_ctrl.api_pubkey_mem_addr.offset*4)) |
                                   ({PK_MEM_WSTROBE_W{mldsa_ctrl.zeroize_mem_we}});


  always_comb fv_pubkey_ram_wdata = ({PK_MEM_DATA_W{pi_pk_t1_wren_i}} & PK_MEM_DATA_W'(pi_pk_t1_wrdata_i << pi_pk_t1_wr_addr_i[1:0]*80)) |
                                 ({PK_MEM_DATA_W{(fv_api_pubkey_we)}} & PK_MEM_DATA_W'(pi_abr_reg_hwif_out_i.MLDSA_PUBKEY.wr_data << mldsa_ctrl.api_pubkey_mem_addr.offset*32));

  //read requests
  always_comb fv_pubkey_ram_re = mldsa_ctrl.sampler_pk_rd_en | mldsa_ctrl.pkdecode_rd_en | fv_api_pubkey_re;
  always_comb fv_pubkey_ram_raddr = ({PK_MEM_ADDR_W{mldsa_ctrl.sampler_pk_rd_en}} & mldsa_ctrl.sampler_pubkey_mem_addr.addr) |
                                 ({PK_MEM_ADDR_W{mldsa_ctrl.pkdecode_rd_en}} & pi_pkdecode_rd_addr_i[PK_MEM_ADDR_W+1:2]) |
                                 ({PK_MEM_ADDR_W{fv_api_pubkey_re}} & mldsa_ctrl.api_pubkey_mem_addr.addr);

  always_comb begin
    fv_api_pubkey_re = mldsa_ctrl.mldsa_valid_reg & pi_abr_reg_hwif_out_i.MLDSA_PUBKEY.req &((PUBKEY_NUM_DWORDS-1-pi_abr_reg_hwif_out_i.MLDSA_PUBKEY.addr[PK_ADDR_W+1:2]) inside {[8:PUBKEY_NUM_DWORDS-1]}) & ~pi_abr_reg_hwif_out_i.MLDSA_PUBKEY.req_is_wr;
    fv_api_pubkey_we = mldsa_ctrl.mldsa_ready & pi_abr_reg_hwif_out_i.MLDSA_PUBKEY.req &((PUBKEY_NUM_DWORDS-1-pi_abr_reg_hwif_out_i.MLDSA_PUBKEY.addr[PK_ADDR_W+1:2]) inside {[8:PUBKEY_NUM_DWORDS-1]}) & po_abr_reg_hwif_in_o.MLDSA_PUBKEY.wr_ack;
  end

property pk_mem_if_comb_outputs;
    po_pk_mem_if_we_i == fv_pubkey_ram_we &&
    po_pk_mem_if_waddr_i == fv_pubkey_ram_waddr &&
    po_pk_mem_if_wdata_i == fv_pubkey_ram_wdata &&
    po_pk_mem_if_wstrobe_i == fv_pubkey_ram_wstrobe &&
    po_pk_mem_if_re_i == fv_pubkey_ram_re &&
    po_pk_mem_if_raddr_i == fv_pubkey_ram_raddr 
;endproperty

assert_pk_mem_if_comb_outputs : assert property(disable iff(!pi_rst_b || po_zeroize) pk_mem_if_comb_outputs);

//pkdecode_rd_data from the ram

// Zeroize the mem addresses.

 logic [MLDSA_MEM_ADDR_WIDTH-1:0] fv_mem_addr_cntr;
always_ff @(posedge pi_clk, negedge pi_rst_b) begin
  if(!pi_rst_b || po_zeroize) begin
      fv_mem_addr_cntr <= '0;
    end
    else begin
      if(mldsa_ctrl.prim_prog_cntr == MLDSA_ZEROIZE )begin
        if(fv_mem_addr_cntr == MLDSA_MEM_MAX_DEPTH)begin
          fv_mem_addr_cntr <= '0;
        end
        else begin
          fv_mem_addr_cntr <= fv_mem_addr_cntr + 1;
        end
      end
    end
end

property zeroize_mem_if_zeroize_cntr;
  zeroize_mem_o.rd_wr_en == (((mldsa_ctrl.prim_prog_cntr == MLDSA_ZEROIZE) ) ? RW_WRITE:RW_IDLE )&&
  zeroize_mem_o.addr == fv_mem_addr_cntr
;endproperty
assert_zeroize_mem_if_zeroize_cntr: assert property(zeroize_mem_if_zeroize_cntr);



/////////////////////////////////////////////////////
/// Internal registers used in the state transition proofs
////////////////////////////////////////////////////

//Private_key
property private_key_reg_update_k_rho_P;
  pi_sampler_state_dv_i &&
  (mldsa_ctrl.prim_instr.operand3 == MLDSA_DEST_K_RHO_REG_ID)
  |=>
  mldsa_ctrl.privatekey_reg.enc.rho == $past(pi_sampler_state_data_i[0][255:0]) &&
  mldsa_ctrl.privatekey_reg.enc.K  == $past(pi_sampler_state_data_i[0][1023:768])
;endproperty

assert_private_key_reg_update_k_rho_P : assert property(disable iff(!pi_rst_b || po_zeroize) private_key_reg_update_k_rho_P);
property private_key_reg_update_tr_P;
  pi_sampler_state_dv_i &&
  (mldsa_ctrl.prim_instr.operand3 == MLDSA_DEST_TR_REG_ID)
  |=>
  mldsa_ctrl.privatekey_reg.enc.tr == $past(pi_sampler_state_data_i[0][511:0])
;endproperty
assert_private_key_reg_update_tr_P : assert property(disable iff(!pi_rst_b || po_zeroize) private_key_reg_update_tr_P);

property private_key_reg_update_from_api_P;
  po_abr_reg_hwif_in_o.MLDSA_PRIVKEY_IN.wr_ack &&
  mldsa_ctrl.mldsa_ready &&
  mldsa_ctrl.api_sk_reg_wr_dec
  |=>
  mldsa_ctrl.privatekey_reg.raw[$past(mldsa_ctrl.api_sk_reg_waddr)] == $past(pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_IN.wr_data)
;endproperty
assert_private_key_reg_update_from_api_P : assert property(disable iff(!pi_rst_b || po_zeroize) private_key_reg_update_from_api_P);

property stable_private_key_reg;
  !pi_sampler_state_dv_i &&
  !(po_abr_reg_hwif_in_o.MLDSA_PRIVKEY_IN.wr_ack &&
  mldsa_ctrl.mldsa_ready &&
  mldsa_ctrl.api_sk_reg_wr_dec)
  |=>
  $stable(mldsa_ctrl.privatekey_reg)
;endproperty
assert_stable_private_key_reg : assert property(disable iff(!pi_rst_b || po_zeroize) stable_private_key_reg);

//publickey_reg

property public_key_reg_rho_update;
  pi_sampler_state_dv_i &&
  (mldsa_ctrl.prim_instr.operand3 == MLDSA_DEST_K_RHO_REG_ID)
  |=>
  mldsa_ctrl.publickey_reg.enc.rho == $past(pi_sampler_state_data_i[0][255:0])
;endproperty

assert_public_key_reg_rho_update : assert property(disable iff(!pi_rst_b || po_zeroize) public_key_reg_rho_update);
property publickey_reg_rho_from_api;
  (mldsa_ctrl.mldsa_ready &&
  mldsa_ctrl.api_pubkey_rho_dec &&
  pi_abr_reg_hwif_out_i.MLDSA_PUBKEY.req_is_wr)
  |=>
   mldsa_ctrl.publickey_reg.enc.rho[$past(mldsa_ctrl.api_pk_rho_addr)] == $past(pi_abr_reg_hwif_out_i.MLDSA_PUBKEY.wr_data)
;endproperty
assert_publickey_reg_rho_from_api : assert property(disable iff(!pi_rst_b || po_zeroize) publickey_reg_rho_from_api);


property stable_public_key_reg;
  !pi_sampler_state_dv_i &&
  !(mldsa_ctrl.mldsa_ready &&
  mldsa_ctrl.api_pubkey_rho_dec &&
  pi_abr_reg_hwif_out_i.MLDSA_PUBKEY.req_is_wr)
  |=>
  $stable(mldsa_ctrl.publickey_reg)
;endproperty

assert_stable_public_key_reg : assert property(disable iff(!pi_rst_b || po_zeroize) stable_public_key_reg);

// pk_reg_rdata

property pk_reg_rdata_update;
  mldsa_ctrl.mldsa_valid_reg &&
  mldsa_ctrl.api_pubkey_rho_dec
  |=>
  mldsa_ctrl.pk_reg_rdata == $past(mldsa_ctrl.publickey_reg.enc.rho[mldsa_ctrl.api_pk_rho_addr])
;endproperty

assert_pk_reg_rdata_update: assert property(disable iff(!pi_rst_b || po_zeroize)pk_reg_rdata_update);

property pk_reg_rdata_stable;
  !mldsa_ctrl.mldsa_valid_reg ||
  !mldsa_ctrl.api_pubkey_rho_dec
  |=>
  $stable(mldsa_ctrl.pk_reg_rdata)
;endproperty

assert_pk_reg_rdata_stable: assert property(disable iff(!pi_rst_b || po_zeroize) pk_reg_rdata_stable);


//Signature_reg

property signature_reg_c_update;
  pi_sampler_state_dv_i &&
  mldsa_ctrl.prim_instr.operand3 == MLDSA_DEST_SIG_C_REG_ID
  |=>
  mldsa_ctrl.signature_reg.enc.c == $past(pi_sampler_state_data_i[0][511:0])
;endproperty

assert_signature_reg_c_update: assert property(disable iff(!pi_rst_b || po_zeroize)signature_reg_c_update);

property signature_reg_c_update_from_api;
  mldsa_ctrl.mldsa_ready &&
  fv_api_sig_c_dec &&
  pi_abr_reg_hwif_out_i.MLDSA_SIGNATURE.req_is_wr
  |=>
   mldsa_ctrl.signature_reg.enc.c[$past(fv_api_sig_c_addr)] == $past( pi_abr_reg_hwif_out_i.MLDSA_SIGNATURE.wr_data)
;endproperty

assert_signature_reg_c_update_from_api: assert property(disable iff(!pi_rst_b || po_zeroize) signature_reg_c_update_from_api);

property signature_reg_c_stable;
  !(pi_sampler_state_dv_i &&
  mldsa_ctrl.prim_instr.operand3 == MLDSA_DEST_SIG_C_REG_ID) &&
  !(mldsa_ctrl.mldsa_ready &&
  fv_api_sig_c_dec &&
  pi_abr_reg_hwif_out_i.MLDSA_SIGNATURE.req_is_wr)
  |=>
  $stable( mldsa_ctrl.signature_reg.enc.c)
;endproperty
assert_signature_reg_c_stable : assert property(disable iff(!pi_rst_b || po_zeroize) signature_reg_c_stable);

property signature_reg_h_update;
  mldsa_ctrl.set_signature_valid
  |=>
   mldsa_ctrl.signature_reg.enc.h <= '0
;endproperty

assert_signature_reg_h_update: assert property(disable iff(!pi_rst_b || po_zeroize) signature_reg_h_update);

property signature_reg_h_update_makehint(dword);
  pi_makehint_reg_wren_i &&
  pi_makehint_reg_wr_addr_i == dword
  |=>
  mldsa_ctrl.signature_reg.enc.h[dword] == ($past( mldsa_ctrl.signature_reg.enc.h[dword]) |  $past(pi_makehint_reg_wrdata_i))
;endproperty
for(genvar i =0;i< SIGNATURE_H_NUM_DWORDS;i++) begin
assert_signature_reg_h_update_makehint: assert property(disable iff(!pi_rst_b || po_zeroize) signature_reg_h_update_makehint(i));
end

property signature_reg_h_update_from_api;
  mldsa_ctrl.mldsa_ready &&
  fv_api_sig_h_dec &&
  pi_abr_reg_hwif_out_i.MLDSA_SIGNATURE.req_is_wr
  |=>
   mldsa_ctrl.signature_reg.enc.h[$past(fv_api_sig_h_addr)] == $past( pi_abr_reg_hwif_out_i.MLDSA_SIGNATURE.wr_data)
;endproperty

assert_signature_reg_h_update_from_api: assert property(disable iff(!pi_rst_b || po_zeroize) signature_reg_h_update_from_api);



property signature_reg_h_stable;
  !mldsa_ctrl.set_signature_valid &&
  !pi_makehint_reg_wren_i &&
  !(mldsa_ctrl.mldsa_ready &&
  fv_api_sig_h_dec &&
  pi_abr_reg_hwif_out_i.MLDSA_SIGNATURE.req_is_wr)
  |=>
  $stable( mldsa_ctrl.signature_reg.enc.h)
;endproperty

assert_signature_reg_h_stable: assert property(disable iff(!pi_rst_b || po_zeroize) signature_reg_h_stable);


// rho_p_reg

property rho_p_reg_k_update;
  pi_sampler_state_dv_i &&
  mldsa_ctrl.prim_instr.operand3 == MLDSA_DEST_K_RHO_REG_ID
  |=>
  mldsa_ctrl.rho_p_reg ==  $past(pi_sampler_state_data_i[0][767:256])
;endproperty

assert_rho_p_reg_k_update : assert property(disable iff(!pi_rst_b || po_zeroize) rho_p_reg_k_update);


property rho_p_reg_p_update;
  pi_sampler_state_dv_i &&
  mldsa_ctrl.prim_instr.operand3 == MLDSA_DEST_RHO_P_REG_ID
  |=>
  mldsa_ctrl.rho_p_reg ==  $past(pi_sampler_state_data_i[0][511:0])
;endproperty

assert_rho_p_reg_p_update : assert property(disable iff(!pi_rst_b || po_zeroize) rho_p_reg_p_update);


property rho_p_reg_stable;
  !pi_sampler_state_dv_i ||
  !((mldsa_ctrl.prim_instr.operand3 == MLDSA_DEST_RHO_P_REG_ID)
  ||(mldsa_ctrl.prim_instr.operand3 == MLDSA_DEST_K_RHO_REG_ID))
  |=>
  $stable(mldsa_ctrl.rho_p_reg)
;endproperty

assert_rho_p_reg_stable : assert property(disable iff(!pi_rst_b || po_zeroize) rho_p_reg_stable);

// lfsr_entropy_reg
  property set_entropy_reg;
    ((mldsa_ctrl.cmd_reg == MLDSA_KEYGEN) ||
    (mldsa_ctrl.cmd_reg == MLDSA_SIGN) ||
    (mldsa_ctrl.cmd_reg == MLDSA_KEYGEN_SIGN))&&
    mldsa_ctrl.mldsa_ready
    |=>
    mldsa_ctrl.lfsr_entropy_reg == $past(mldsa_ctrl.lfsr_entropy_reg ^ mldsa_ctrl.entropy_reg)
  ;endproperty
assert_set_entropy_reg: assert property(disable iff(!pi_rst_b || po_zeroize)set_entropy_reg);

// set lfsr when LFSR_SEED_REG_ID

property set_entropy_reg_from_sampler;
  pi_sampler_state_dv_i &&
  mldsa_ctrl.prim_instr.operand3 == MLDSA_DEST_LFSR_SEED_REG_ID
  |=>
  mldsa_ctrl.lfsr_entropy_reg ==  $past(pi_sampler_state_data_i[0][2*LFSR_W+511:2*LFSR_W])
;endproperty

assert_set_entropy_reg_from_sampler : assert property(disable iff(!pi_rst_b || po_zeroize) set_entropy_reg_from_sampler);

// readdata for signature

property signature_reg_rdata_api_P  ;
  mldsa_ctrl.mldsa_valid_reg &&
  pi_abr_reg_hwif_out_i.MLDSA_SIGNATURE.req &&
  !pi_abr_reg_hwif_out_i.MLDSA_SIGNATURE.req_is_wr
  |=>
  mldsa_ctrl.signature_reg_rdata == ({DATA_WIDTH{$past(fv_api_sig_c_dec)}} & $past(mldsa_ctrl.signature_reg.enc.c[fv_api_sig_c_addr]) |
                               {DATA_WIDTH{$past(fv_api_sig_h_dec)}} & $past(mldsa_ctrl.signature_reg.enc.h[fv_api_sig_h_addr]))
;endproperty

assert_signature_reg_rdata_api_P: assert property(disable iff(!pi_rst_b || po_zeroize) signature_reg_rdata_api_P);


// stable if there is no req from the api
property signature_reg_rdata_stable_P  ;
 !( mldsa_ctrl.mldsa_valid_reg &&
  pi_abr_reg_hwif_out_i.MLDSA_SIGNATURE.req &&
  !pi_abr_reg_hwif_out_i.MLDSA_SIGNATURE.req_is_wr)
  |=>
  $stable(mldsa_ctrl.signature_reg_rdata)
;endproperty

assert_signature_reg_rdata_stable_P: assert property(disable iff(!pi_rst_b || po_zeroize) signature_reg_rdata_stable_P);

// privkey reg rdata
logic[SK_MEM_BANK_ADDR_W:0] fv_api_sk_raddr;

assign fv_api_sk_raddr =  PRIVKEY_NUM_DWORDS-1-pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_OUT.addr[12:2];

property privkey_reg_rdata_set;
  fv_api_keymem_rd_vld &&
  pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_OUT.req &&
  (((fv_api_sk_raddr) inside {[0:31]}))
  |=>
  mldsa_ctrl.privkey_reg_rdata == $past(mldsa_ctrl.privatekey_reg.raw[(fv_api_sk_raddr[4:0])])
;endproperty

assert_privkey_reg_rdata_set: assert property(disable iff(!pi_rst_b || po_zeroize)privkey_reg_rdata_set);

// privkey_reg_rdata stable

property privkey_reg_rdata_stable;
  !(fv_api_keymem_rd_vld &&
  pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_OUT.req &&
  ((fv_api_sk_raddr) inside {[0:31]}))
  |=>
  $stable(mldsa_ctrl.privkey_reg_rdata)
;endproperty

assert_privkey_reg_rdata_stable: assert property(disable iff(!pi_rst_b || po_zeroize)privkey_reg_rdata_stable);

// api_sk_reg_rd_dec upadte
  property api_sk_reg_rd_dec_update_post_rd;
    fv_api_sk_raddr inside {[0:31]} &&
    pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_OUT.req
    |=>
    mldsa_ctrl.api_sk_reg_rd_dec_f
  ;endproperty

  assert_api_sk_reg_rd_dec_update_post_rd: assert property(disable iff(!pi_rst_b || po_zeroize) api_sk_reg_rd_dec_update_post_rd);

//api_key_mem upadte
  property api_keymem_re_upadte_post_rd;
    ##1
    mldsa_ctrl.api_keymem_re_bank_f == $past(fv_api_keymem_re_bank)
  ;endproperty

  assert_api_keymem_re_upadte_post_rd: assert property(disable iff(!pi_rst_b || po_zeroize) api_keymem_re_upadte_post_rd);

  
// error interface
`ifdef CALIPTRA
  property error_flag_pcr_or_error_decode;
    mldsa_ctrl.error_flag == pi_skdecode_error_i | (pi_abr_reg_hwif_out_i.MLDSA_CTRL.PCR_SIGN.value)
  ;endproperty

  assert_error_flag_pcr_or_error_decode: assert property(error_flag_pcr_or_error_decode);
`else
  property error_flag_from_decode;
     mldsa_ctrl.error_flag == pi_skdecode_error_i
  ;endproperty

  assert_error_flag_from_decode: assert property(error_flag_from_decode);

`endif

// valid reg assert

property valid_Reg_set_P;
  (mldsa_ctrl.prim_prog_cntr == MLDSA_KG_E) ||
  (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_E) ||
  (mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_E)
  |=>
  mldsa_ctrl.mldsa_valid_reg
;endproperty

assert_valid_Reg_set_P: assert property(disable iff(!pi_rst_b || po_zeroize) valid_Reg_set_P);


// msg_strobe_o

property msg_strobe_o_if_done;
  mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD &&
  ((mldsa_ctrl.msg_last &&
  pi_msg_rdy_i) )&&
  mldsa_ctrl.prim_instr.length[$clog2(MsgStrbW)-1:0] == '0
  |=>
  po_msg_strobe_o == '0
;endproperty
assert_msg_strobe_o_if_done: assert property (disable iff (!pi_rst_b || po_zeroize)msg_strobe_o_if_done);

property msg_strobe_o_full_if_not_last;
  mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD &&
  !mldsa_ctrl.msg_done &&
  !mldsa_ctrl.msg_last &&
  pi_msg_rdy_i
  |=>
  po_msg_strobe_o == '1
;endproperty
assert_msg_strobe_o_full_if_not_last: assert property (disable iff (!pi_rst_b || po_zeroize)msg_strobe_o_full_if_not_last);


property msg_strobe_o_if_last;
  mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD &&
  mldsa_ctrl.msg_last &&
  pi_msg_rdy_i &&
  (mldsa_ctrl.prim_instr.length[$clog2(MsgStrbW)-1:0] != '0)
  |=>
  po_msg_strobe_o == ~(MsgStrbW'('1) << mldsa_ctrl.prim_instr.length[$clog2(MsgStrbW)-1:0])
;endproperty
assert_msg_strobe_o_if_last: assert property (disable iff (!pi_rst_b || po_zeroize)msg_strobe_o_if_last);


property msg_strobe_o_stable_if_no_ready;
  mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD &&
  !pi_msg_rdy_i
  |=>
  $stable(po_msg_strobe_o)
;endproperty
assert_msg_strobe_o_stable_if_no_ready: assert property(disable iff(!pi_rst_b || po_zeroize)msg_strobe_o_stable_if_no_ready);


// synchronisation of the sequencers only if no abstraction is applied.
// First both the sequencers trigger and start running incase of the signing operation.
// secondary sequencer waits for the c_valid inorder to proceed and the primary sequencer 
// continues with the next round and apparently if the secondary sequencer sets the valid signature, then
// the primary sequencer would terminate the next c generation in specific states and jump to end state.
`ifdef NO_ABSTRACTION
  property c_valid_clear_eventually_P;
    mldsa_ctrl.c_valid
    |->
    s_eventually(!mldsa_ctrl.c_valid)
  ;endproperty

assert_c_valid_clear_eventually_P: assert property(disable iff(!pi_rst_b || po_zeroize || mldsa_ctrl.error_flag)c_valid_clear_eventually_P);


  property y_valid_clear_eventually_P;
    mldsa_ctrl.y_valid
    |->
    s_eventually(!mldsa_ctrl.y_valid)
  ;endproperty
assert_y_valid_clear_eventually_P: assert property(disable iff(!pi_rst_b || po_zeroize || mldsa_ctrl.error_flag)y_valid_clear_eventually_P);


  property w0_valid_clear_eventually_P;
    mldsa_ctrl.w0_valid
    |->
    s_eventually(!mldsa_ctrl.w0_valid)
  ;endproperty
  assert_w0_valid_clear_eventually_P: assert property(disable iff(!pi_rst_b || po_zeroize || mldsa_ctrl.error_flag)w0_valid_clear_eventually_P);



  property verify_valid_clear_eventually_P;
    mldsa_ctrl.verify_valid
    |->
    s_eventually(!mldsa_ctrl.verify_valid)
  ;endproperty
  assert_verify_valid_clear_eventually_P: assert property(disable iff(!pi_rst_b || po_zeroize || mldsa_ctrl.error_flag)verify_valid_clear_eventually_P);
`endif
// Mldsa valid register and ready

property valid_reg_set_only_if_done_P;
  (mldsa_ctrl.prim_prog_cntr == MLDSA_KG_E) ||
  (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_E) ||
  (mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_E)
  |=>
  mldsa_ctrl.mldsa_status_done_p
;endproperty

assert_valid_reg_set_only_if_done_P: assert property(disable iff(!pi_rst_b || po_zeroize)valid_reg_set_only_if_done_P);


property valid_reg_not_set_if_not_done_P;
  !((mldsa_ctrl.prim_prog_cntr == MLDSA_KG_E) ||
  (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_E) ||
  (mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_E))
  |=>
  !mldsa_ctrl.mldsa_status_done_p
;endproperty

assert_valid_reg_not_set_if_not_done_P: assert property(disable iff(!pi_rst_b || po_zeroize)valid_reg_not_set_if_not_done_P);

// Valid signaturee and valid verifying

`ifdef NO_ABSTRACTION
property valid_verify_set_P;
  (mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY)
  |=>
  mldsa_ctrl.verify_valid until_with (mldsa_ctrl.verifying_process & ((pi_normcheck_done_i & pi_normcheck_invalid_i) | 
                                   (mldsa_ctrl.prim_instr.opcode.aux_en & (mldsa_ctrl.prim_instr.opcode.mode.aux_mode == MLDSA_SIGDEC_H) & pi_sigdecode_h_invalid_i)))
;endproperty

assert_valid_verify_set_P: assert property (disable iff(!pi_rst_b || po_zeroize || mldsa_ctrl.error_flag) valid_verify_set_P);
`endif

property valid_verify_reset_P;
  (mldsa_ctrl.verifying_process & ((pi_normcheck_done_i & pi_normcheck_invalid_i) | 
                                   (mldsa_ctrl.prim_instr.opcode.aux_en & (mldsa_ctrl.prim_instr.opcode.mode.aux_mode == MLDSA_SIGDEC_H) & pi_sigdecode_h_invalid_i)))
  |=>
  !mldsa_ctrl.verify_valid
;endproperty

assert_valid_verify_reset_P: assert property (disable iff(!pi_rst_b || po_zeroize) valid_verify_reset_P);

property sign_valid_set_P;
  (mldsa_ctrl.sec_prog_cntr == MLDSA_SIGN_CHECK_C_VLD) &&
  mldsa_ctrl.c_valid &&
  mldsa_ctrl.signing_process
  |=>
  mldsa_ctrl.signature_valid until_with (mldsa_ctrl.signing_process & ((pi_makehint_done_i & pi_makehint_invalid_i) | (pi_normcheck_done_i & pi_normcheck_invalid_i)))
;endproperty

assert_sign_valid_set_P: assert property (disable iff(!pi_rst_b || po_zeroize) sign_valid_set_P);


property sign_valid_reset_P;
  (mldsa_ctrl.signing_process & ((pi_makehint_done_i & pi_makehint_invalid_i) | (pi_normcheck_done_i & pi_normcheck_invalid_i)))
  |=>
  !mldsa_ctrl.signature_valid
;endproperty

assert_sign_valid_reset_P: assert property (disable iff(!pi_rst_b || po_zeroize) sign_valid_reset_P);

// Keyvault registers

`ifdef CALIPTRA

  //kv_seed_data_present if there is a read en

  property kv_seed_data_present_set_P;
     mldsa_ctrl.kv_seed_read_ctrl_reg.read_en ||
    mldsa_ctrl.pcr_sign_mode
    |=>
    mldsa_ctrl.kv_seed_data_present until_with mldsa_ctrl.mldsa_valid_reg
  ;endproperty

  assert_kv_seed_data_present_set_P: assert property(disable iff(!pi_rst_b || po_zeroize) kv_seed_data_present_set_P);

  property kv_seed_read_ctrl_reg_P;
    mldsa_ctrl.kv_seed_read_ctrl_reg.rsvd == '0 &&
    mldsa_ctrl.kv_seed_read_ctrl_reg.pcr_hash_extend == pi_abr_reg_hwif_out_i.mldsa_kv_rd_seed_ctrl.pcr_hash_extend.value &&
    mldsa_ctrl.kv_seed_read_ctrl_reg.read_entry == pi_abr_reg_hwif_out_i.mldsa_kv_rd_seed_ctrl.read_entry.value &&
    mldsa_ctrl.kv_seed_read_ctrl_reg.read_en == pi_abr_reg_hwif_out_i.mldsa_kv_rd_seed_ctrl.read_en.value
  ;endproperty
  assert_kv_seed_read_ctrl_reg_P: assert property(disable iff(!pi_rst_b || po_zeroize) kv_seed_read_ctrl_reg_P);

`else 

  property kv_seed_data_present_P;
     mldsa_ctrl.kv_seed_data_present == '0 &&
     //ready when fsm is not busy
    po_abr_reg_hwif_in_o.mldsa_kv_rd_seed_status.ERROR.next == '0 &&
    //ready when fsm is not busy
    po_abr_reg_hwif_in_o.mldsa_kv_rd_seed_status.READY.next == '0 &&
    //set valid when fsm is done
    po_abr_reg_hwif_in_o.mldsa_kv_rd_seed_status.VALID.hwset == '0 &&
    //clear valid when new request is made
    po_abr_reg_hwif_in_o.mldsa_kv_rd_seed_status.VALID.hwclr == '0 &&
    //clear enable when busy
    po_abr_reg_hwif_in_o.mldsa_kv_rd_seed_ctrl.read_en.hwclr == '0;
  endproperty
  assert_kv_seed_data_present_A: assert property(disable iff(!pi_rst_b || po_zeroize) kv_seed_data_present_P);

`endif

property privkey_lock_reset_P;
  mldsa_ctrl.keygen_process &&
  (mldsa_ctrl.prim_prog_cntr == MLDSA_KG_E) &&
  !mldsa_ctrl.kv_seed_data_present
  |=>
  !mldsa_ctrl.mldsa_privkey_lock
;endproperty

assert_privkey_lock_reset_A: assert property(disable iff(!pi_rst_b || po_zeroize) privkey_lock_reset_P);



//////////////////////////
// msg_cnt increment    //
//////////////////////////

    logic [MLDSA_OPR_WIDTH-1:$clog2(MsgStrbW)] fv_msg_cnt;
    always_ff @( posedge pi_clk, negedge pi_rst_b ) begin : fv_msg_cnt_logic
        if(!pi_rst_b) begin
            fv_msg_cnt <= '0;
        end
        else if(po_zeroize) begin
            fv_msg_cnt <= '0;
        end
        else begin
            if(mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_IDLE) begin
                fv_msg_cnt <= '0;
            end
            else if(mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD &&  pi_msg_rdy_i && (fv_msg_cnt <= mldsa_ctrl.prim_instr.length[MLDSA_OPR_WIDTH-1:$clog2(MsgStrbW)]) ) begin
                fv_msg_cnt <= fv_msg_cnt + 1;
            end
            else if(mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD && !pi_msg_rdy_i) begin
                fv_msg_cnt <= fv_msg_cnt;
            end
            else begin
                 fv_msg_cnt <= '0;
            end
        end
    end

`ifdef NO_ABSTRACTION
     property msg_cnt_p;
         mldsa_ctrl.msg_cnt == fv_msg_cnt
    ;endproperty
    assert_msg_cnt: assert property(msg_cnt_p);
`endif

///////////////////////////////////////////
// For the api data out and ack proofs   //
///////////////////////////////////////////

property privkey_out_rd_ack_set_P;
  pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_OUT.req &&
  !pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_OUT.req_is_wr
  |=>
  mldsa_ctrl.privkey_out_rd_ack
;endproperty

assert_privkey_out_rd_ack_set_P: assert property(disable iff(!pi_rst_b || po_zeroize)privkey_out_rd_ack_set_P);


property privkey_out_rd_ack_reset_P;
  !(pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_OUT.req &&
  !pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_OUT.req_is_wr)
  |=>
  !mldsa_ctrl.privkey_out_rd_ack
;endproperty

assert_privkey_out_rd_ack_reset_P: assert property(disable iff(!pi_rst_b || po_zeroize)privkey_out_rd_ack_reset_P);



property signature_rd_ack_set_P;
  pi_abr_reg_hwif_out_i.MLDSA_SIGNATURE.req &&
  !pi_abr_reg_hwif_out_i.MLDSA_SIGNATURE.req_is_wr
  |=>
  mldsa_ctrl.signature_rd_ack
;endproperty

assert_signature_rd_ack_set_P: assert property(disable iff(!pi_rst_b || po_zeroize)signature_rd_ack_set_P);


property signature_rd_ack_reset_P;
  !(pi_abr_reg_hwif_out_i.MLDSA_SIGNATURE.req &&
  !pi_abr_reg_hwif_out_i.MLDSA_SIGNATURE.req_is_wr)
  |=>
  !mldsa_ctrl.signature_rd_ack
;endproperty

assert_signature_rd_ack_reset_P: assert property(disable iff(!pi_rst_b || po_zeroize)signature_rd_ack_reset_P);




property pubkey_rd_ack_set_P;
  pi_abr_reg_hwif_out_i.MLDSA_PUBKEY.req &&
  !pi_abr_reg_hwif_out_i.MLDSA_PUBKEY.req_is_wr
  |=>
  mldsa_ctrl.pubkey_rd_ack
;endproperty

assert_pubkey_rd_ack_set_P: assert property(disable iff(!pi_rst_b || po_zeroize)pubkey_rd_ack_set_P);


property pubkey_rd_ack_reset_P;
  !(pi_abr_reg_hwif_out_i.MLDSA_PUBKEY.req &&
  !pi_abr_reg_hwif_out_i.MLDSA_PUBKEY.req_is_wr)
  |=>
  !mldsa_ctrl.pubkey_rd_ack
;endproperty

assert_pubkey_rd_ack_reset_P: assert property(disable iff(!pi_rst_b || po_zeroize)pubkey_rd_ack_reset_P);




property mldsa_hwif_in_ack_P;
  po_abr_reg_hwif_in_o.MLDSA_PRIVKEY_OUT.rd_ack == mldsa_ctrl.privkey_out_rd_ack &&
  po_abr_reg_hwif_in_o.MLDSA_SIGNATURE.rd_ack ==  mldsa_ctrl.signature_rd_ack &&
  po_abr_reg_hwif_in_o.MLDSA_PUBKEY.rd_ack ==  mldsa_ctrl.pubkey_rd_ack &&
  po_abr_reg_hwif_in_o.MLDSA_PRIVKEY_IN.wr_ack == (pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_IN.req & pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_IN.req_is_wr) &&
  po_abr_reg_hwif_in_o.MLDSA_PRIVKEY_IN.rd_ack == (pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_IN.req & ~pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_IN.req_is_wr) &&
  po_abr_reg_hwif_in_o.MLDSA_PRIVKEY_OUT.wr_ack == (pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_OUT.req & pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_OUT.req_is_wr) &&
  po_abr_reg_hwif_in_o.MLDSA_SIGNATURE.wr_ack == (pi_abr_reg_hwif_out_i.MLDSA_SIGNATURE.req &  pi_abr_reg_hwif_out_i.MLDSA_SIGNATURE.req_is_wr) &&
  po_abr_reg_hwif_in_o.MLDSA_PUBKEY.wr_ack == (pi_abr_reg_hwif_out_i.MLDSA_PUBKEY.req &  pi_abr_reg_hwif_out_i.MLDSA_PUBKEY.req_is_wr)
;endproperty

assert_mldsa_hwif_in_ack_P : assert property (mldsa_hwif_in_ack_P);


property mldsa_hwif_rd_data_P;
   po_abr_reg_hwif_in_o.MLDSA_PRIVKEY_OUT.rd_data == ( mldsa_ctrl.privkey_out_rd_ack &  mldsa_ctrl.mldsa_valid_reg & ~ mldsa_ctrl.mldsa_privkey_lock ?  mldsa_ctrl.privkey_out_rdata : 0) &&
   po_abr_reg_hwif_in_o.MLDSA_SIGNATURE.rd_data == (mldsa_ctrl.api_sig_z_re_f ? pi_sig_z_mem_if_rdata_o[mldsa_ctrl.api_sig_z_addr_f.offset*DATA_WIDTH+:DATA_WIDTH] : mldsa_ctrl.signature_reg_rdata) &&
   po_abr_reg_hwif_in_o.MLDSA_PUBKEY.rd_data == (mldsa_ctrl.api_pubkey_re_f ? pi_pk_mem_if_rdata_o[mldsa_ctrl.api_pubkey_mem_addr_f.offset*DATA_WIDTH+:DATA_WIDTH] : mldsa_ctrl.pk_reg_rdata) &&
   po_abr_reg_hwif_in_o.MLDSA_PRIVKEY_IN.rd_data == '0
;endproperty

assert_mldsa_hwif_rd_data_P: assert property (mldsa_hwif_rd_data_P);


// read data for the primary outputs

  property skdecode_read_data_out_from_mem_P;
    po_skdecode_rd_data_o == ({pi_sk_bank1_mem_if_rdata_o,pi_sk_bank0_mem_if_rdata_o})
  ;endproperty
  assert_skdecode_read_data_out_from_mem_P: assert property(skdecode_read_data_out_from_mem_P);

// read_data for privkey
  property privkey_out_rdata_update_P;
    mldsa_ctrl.privkey_out_rdata == ({DATA_WIDTH{mldsa_ctrl.api_keymem_re_bank_f[0]}} & pi_sk_bank0_mem_if_rdata_o |
                                  {DATA_WIDTH{mldsa_ctrl.api_keymem_re_bank_f[1]}} & pi_sk_bank1_mem_if_rdata_o |
                                  {DATA_WIDTH{mldsa_ctrl.api_sk_reg_rd_dec_f}} & mldsa_ctrl.privkey_reg_rdata)
  ;endproperty
  assert_privkey_out_rdata_update_P: assert property(privkey_out_rdata_update_P);

  // flop the rd_offset for pkdecode
  logic [1:0] fv_pkdecode_rd_offset_f;
    always_ff @(posedge pi_clk, negedge pi_rst_b) begin
      if(!pi_rst_b || po_zeroize) begin
        fv_pkdecode_rd_offset_f <= '0;
      end
      else begin
        fv_pkdecode_rd_offset_f <= pi_pkdecode_rd_addr_i[1:0];
      end
    end
//read data out from mem to the pkdecode
logic [7:0][T1_COEFF_W-1:0] fv_pkdecode_rd_data_o;

  always_comb begin
    unique case (fv_pkdecode_rd_offset_f[1:0])
      2'b00: fv_pkdecode_rd_data_o = mldsa_ctrl.pubkey_ram_rdata_t1[7:0];
      2'b01: fv_pkdecode_rd_data_o = mldsa_ctrl.pubkey_ram_rdata_t1[15:8];
      2'b10: fv_pkdecode_rd_data_o = mldsa_ctrl.pubkey_ram_rdata_t1[23:16];
      2'b11: fv_pkdecode_rd_data_o = mldsa_ctrl.pubkey_ram_rdata_t1[31:24];
    endcase
  end
  property pkdecode_read_data_out_from_mem_P;
    po_pkdecode_rd_data_o == fv_pkdecode_rd_data_o &&
    mldsa_ctrl.pkdecode_rd_offset_f == fv_pkdecode_rd_offset_f
  ;endproperty
  assert_pkdecode_read_data_out_from_mem_P: assert property(pkdecode_read_data_out_from_mem_P);



  // Normcheck primary out from the sequencer checks sice it has both sequencers
  property norm_check_out_P;
    po_normcheck_mode_o == ((mldsa_ctrl.prim_instr.opcode.aux_en & (mldsa_ctrl.prim_instr.opcode.mode.aux_mode == MLDSA_NORMCHK)) ? mldsa_ctrl.prim_instr.imm[1:0] :
                                 (mldsa_ctrl.sec_instr.opcode.aux_en & (mldsa_ctrl.sec_instr.opcode.mode.aux_mode == MLDSA_NORMCHK)) ? mldsa_ctrl.sec_instr.imm[1:0] : '0) &&
    po_normcheck_src_addr_o == ((mldsa_ctrl.prim_instr.opcode.aux_en & (mldsa_ctrl.prim_instr.opcode.mode.aux_mode == MLDSA_NORMCHK)) ? mldsa_ctrl.aux_src0_base_addr_o[0] :
                                     (mldsa_ctrl.sec_instr.opcode.aux_en & (mldsa_ctrl.sec_instr.opcode.mode.aux_mode == MLDSA_NORMCHK)) ? mldsa_ctrl.aux_src0_base_addr_o[1] : '0) &&
    mldsa_ctrl.ntt_temp_address[0] == (mldsa_ctrl.prim_instr.imm[0] ? MLDSA_TEMP3_BASE : MLDSA_TEMP0_BASE)
  ;endproperty

  assert_norm_check_out_P: assert property(norm_check_out_P);


// ntt primary outputs combinational masking and shuffling
  property ntt_outputs_0_P;
    po_ntt_mode_o[0]==( mldsa_ctrl.prim_instr.opcode.ntt_en?mldsa_ctrl.prim_instr.opcode.mode.ntt_mode:'0) &&
    po_ntt_masking_en_o[0] == ( mldsa_ctrl.prim_instr.opcode.ntt_en?mldsa_ctrl.prim_instr.opcode.masking_en:'0) &&
    po_ntt_shuffling_en_o[0] == ( mldsa_ctrl.prim_instr.opcode.ntt_en?mldsa_ctrl.prim_instr.opcode.shuffling_en:'0)
  ;endproperty

  assert_ntt_outputs_0_P: assert property(ntt_outputs_0_P);
  // busy if the cntr is not ready

  property busy_o_P;
    po_busy_o == !(mldsa_ctrl.prim_prog_cntr == MLDSA_RESET);
  endproperty

  assert_busy_o_P:assert property(busy_o_P);


// signature output read from the register
logic [SIGNATURE_H_VALID_NUM_BYTES-1:0][7:0] fv_signature_h_o;
  always_comb begin
    //HW read h
    for (int i = 0; i < SIGNATURE_H_VALID_NUM_BYTES; i++) begin
      fv_signature_h_o[i] = mldsa_ctrl.signature_reg.enc.h[i/4][(i%4)*8 +: 8];
    end
  end
  property signature_h_o_P;
    po_signature_h_o == fv_signature_h_o;
  endproperty
  assert_signature_h_o_P: assert property(signature_h_o_P);

  //lfsr seed output is updated if the lsft seed reg id is the destination.
  property lfsr_seed_o_set;
    pi_sampler_state_dv_i &&
    mldsa_ctrl.prim_instr.operand3 == MLDSA_DEST_LFSR_SEED_REG_ID
    |=>
    po_lfsr_seed_o == $past(pi_sampler_state_data_i[0][2*LFSR_W-1:0])
  ;endproperty

  assert_lfsr_seed_o_set: assert property(disable iff(!pi_rst_b)lfsr_seed_o_set);

  property lfsr_seed_o_stable;
    !(pi_sampler_state_dv_i &&
    mldsa_ctrl.prim_instr.operand3 == MLDSA_DEST_LFSR_SEED_REG_ID)
    |=>
    $stable(po_lfsr_seed_o)
  ;endproperty

  assert_lfsr_seed_o_stable: assert property(disable iff(!pi_rst_b)lfsr_seed_o_stable);
  

  // decompose mode is set only if is in use hint

  property decompose_mode_P;
    po_decompose_mode_o == (mldsa_ctrl.prim_instr.opcode.aux_en & (mldsa_ctrl.prim_instr.opcode.mode.aux_mode == MLDSA_USEHINT))
  ;endproperty

  assert_decompose_mode_P: assert property(decompose_mode_P);
endmodule
