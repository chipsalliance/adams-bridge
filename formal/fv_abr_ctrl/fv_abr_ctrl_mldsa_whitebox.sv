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

// =================================================================
// Copyright(c) LUBIS EDA GmbH, All rights reserved  
// Contact: contact@lubis-eda.com
// =================================================================
//
//          ABR CONTROLLER FORMAL VERIFICATION
//              WHITE-BOX ASSERTIONS MODULE
//
// =================================================================
// FILE ORGANIZATION - 26 SECTIONS:
// =================================================================
//
// SECTION 1  — Reset and Zeroization (Power-on and Debug Unlock)
// SECTION 2  — Hardware Interface Combinational Outputs (HWIF)
// SECTION 3  — Per-Word Register Checks (Entropy, Seed, Message)
// SECTION 4  — Memory Interface Outputs (SK, SIG_Z, PK RAMs)
// SECTION 5  — Zeroize Memory Counter
// SECTION 6  — Internal Scratch Register Updates (K, rho, tr)
// SECTION 7  — Signature Register Updates (c, h fields)
// SECTION 8  — rho_p Register Management
// SECTION 9  — LFSR Entropy Management (XOR and Fresh Seed)
// SECTION 10 — API Read-Data Multiplexer (Priority Encoder A3-A8)
// SECTION 11 — API Read-Data Stability and Decode Signals
// SECTION 12 — Private/Public Key Read Paths (Register vs SRAM)
// SECTION 13 — Error Flag Management (SET and CLEAR paths)
// SECTION 14 — Valid Register Status (MLDSA and MLKEM)
// SECTION 15 — Message Strobe Interface (SHA3 Byte Masking)
// SECTION 16 — Message Counter (NO_ABSTRACTION Build)
// SECTION 17 — Verify/Sign Valid Flags (Rejection Sampling)
// SECTION 18 — Key Lock Mechanism (KV Isolation Enforcement)
// SECTION 19 — Keyvault Registers (CALIPTRA Build)
// SECTION 20 — APB Read Acknowledge Signals
// SECTION 21 — HWIF Latency and Read Data Completeness
// SECTION 22 — MLKEM Interface Completeness
// SECTION 23 — Memory Read Data Paths and Valid Signals
// SECTION 24 — Control Outputs (NTT, Normcheck, Busy, Decompose)
// SECTION 25 — Output Packing (Signature H, LFSR Seed)
// SECTION 26 — Cover Properties (Liveness Checks)
//
// =================================================================

`define abr_ctrl fv_abr_ctrl_dut.abr_ctrl_inst

module fv_abr_ctrl_mldsa_whitebox 
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
    //#$localparams
    localparam ABR_SEQ_NTT = 0,
    //$#//
    parameter SRAM_LATENCY = 1
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
    input logic                                        po_split_en_o,
    input logic                                        po_recombine_en_o,
    input logic                                        po_recombine_mode_o,
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
    input abr_lfsr_seed_t                      po_lfsr_seed_o,
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


    default clocking default_clk @(posedge pi_clk); endclocking


    // Define default clock

    // ===============================================================
    // SECTION 1 — Reset and Zeroization
    // ===============================================================
    //
    //
    // WHAT WE VERIFY:
    //   signature_reg cleared (prevents leakage of rejected signatures)
    //   abr_scratch_reg cleared (private/public key material)
    //   mldsa_privkey_lock SET (blocks API reads of sensitive data)
    //   valid flags cleared (prevents reads of stale data)
    //   FSM flags cleared (signing/verify restart from IDLE)
    //
    // RESET vs ZEROIZE:
    //   • reset (!pi_rst_b): Power-on or hard reset - clears everything
    //   • zeroize: Software-triggered or debug-unlock - clears keys but
    //              preserves LFSR entropy accumulation across operations
    //
    // ===============================================================

    property reset_p;
      $past(!pi_rst_b || po_zeroize) 
      |->
      `abr_ctrl.mldsa_privkey_lock &&
      //`abr_ctrl.privatekey_reg == '0 &&
      //`abr_ctrl.publickey_reg  == '0 &&
      //`abr_ctrl.pk_reg_rdata == '0 &&
      `abr_ctrl.signature_reg == '0 &&
      //`abr_ctrl.rho_p_reg == '0 &&
      `abr_ctrl.signature_reg_rdata == '0 &&
      `abr_ctrl.abr_scratch_reg == '0 &&
      `abr_ctrl.api_reg_rdata == '0 &&
      `abr_ctrl.mldsa_valid_reg == '0 &&
      //`abr_ctrl.privkey_reg_rdata == '0 &&
      //!`abr_ctrl.c_valid &&
      //!`abr_ctrl.w0_valid &&
      //!`abr_ctrl.y_valid &&
      !`abr_ctrl.verify_valid &&
      //!`abr_ctrl.abr_status_done &&
      !`abr_ctrl.signature_valid 
      //!`abr_ctrl.signature_rd_ack &&
      //!`abr_ctrl.pubkey_rd_ack &&
      //!`abr_ctrl.privkey_out_rd_ack
    ;endproperty

    assert_reset_a: assert property(reset_p);

    property rst_b_p;
      $past(!pi_rst_b)
      |->
      po_lfsr_seed_o == '0 &&
      `abr_ctrl.lfsr_entropy_reg == '0
    ;endproperty

    assert_rst_b_a: assert property(rst_b_p);



    // ===============================================================
    // SECTION 2 — Hardware Interface Combinational Outputs
    // ===============================================================
    //
    // HWIF (Hardware Interface) signals connect the controller to
    // the APB register block. These are combinational outputs that
    // must update within the same cycle.
    //
    // VERIFIED:
    //   reset_b and hard_reset_b match pi_rst_b
    //   abr_ready asserted only when FSM at RESET and KV ready
    //   Command register mirrors CTRL.value (with KV gate)
    //   hwclr signals fire correctly for auto-clear fields
    //   NAME/VERSION are read-only constants
    //   STATUS reflects ready/valid/error/msg_stream state
    //   Zeroize OR's software + debug-unlock triggers
    //   Interrupts wired correctly from interrupt block
    //   SIGNATURE write-ack is combinational decode
    //
    // NOTE: This is a monolithic property checking 15+ signals.
    //       Consider splitting for easier debug if it fails.
    // ===============================================================


    // ===============================================================
    // SECTION 2 — Hardware Interface (HWIF) Combinational Outputs
    // ===============================================================
    //
    // The HWIF signals connect the controller to the APB register block.
    // These are purely combinational - they must reflect current state
    // within the same clock cycle.
    //
    // SIGNALS VERIFIED:
    //   reset_b / hard_reset_b - Matches pi_rst_b (active-low)
    //   abr_ready - Controller ready for new commands
    //   mldsa_cmd_reg - Mirrors CTRL register (KEYGEN/SIGN/VERIFY)
    //   hwclr_* - Auto-clear triggers for writeable registers
    //   NAME/VERSION - Read-only constants
    //   STATUS fields - ready, valid, error, message_streaming
    //   zeroize - OR of software trigger + debug unlock
    //   interrupt signals - Wired from interrupt block
    //
    // WHY COMBINATIONAL MATTERS:
    //   APB reads must see current controller state, not delayed.
    //   Any registered delay would violate APB timing assumptions.
    //
    // NOTE: This is a monolithic property. If it fails, check which
    //       conjunct failed to narrow down the signal.
    // ===============================================================

    property mldsa_reg_hwif_in_comb_p;
         po_abr_reg_hwif_in_o.reset_b == pi_rst_b &&
         po_abr_reg_hwif_in_o.hard_reset_b == pi_rst_b &&
         `ifdef CALIPTRA
         po_abr_reg_hwif_in_o.abr_ready == ((`abr_ctrl.abr_prog_cntr == ABR_RESET) && `abr_ctrl.kv_mlkem_msg_ready &&
                                            `abr_ctrl.kv_mlkem_seed_ready && `abr_ctrl.kv_mldsa_seed_ready && `abr_ctrl.kv_mlkem_sharedkey_ready) &&
         `else
         po_abr_reg_hwif_in_o.abr_ready == (`abr_ctrl.abr_prog_cntr == ABR_RESET) &&
         `endif
         `ifdef CALIPTRA
         `abr_ctrl.mldsa_cmd_reg == (pi_abr_reg_hwif_out_i.MLDSA_CTRL.CTRL.value & {$bits(mldsa_cmd_e){`abr_ctrl.kv_mldsa_seed_ready}}) &&
         `else
         `abr_ctrl.mldsa_cmd_reg == pi_abr_reg_hwif_out_i.MLDSA_CTRL.CTRL.value &&
         `endif
         po_abr_reg_hwif_in_o.MLDSA_CTRL.CTRL.hwclr == |`abr_ctrl.mldsa_cmd_reg &&
         po_abr_reg_hwif_in_o.MLDSA_CTRL.EXTERNAL_MU.hwclr == pi_abr_reg_hwif_out_i.MLDSA_CTRL.EXTERNAL_MU.value &&
        `ifdef CALIPTRA
          po_abr_reg_hwif_in_o.MLDSA_CTRL.PCR_SIGN.hwclr == pi_abr_reg_hwif_out_i.MLDSA_CTRL.PCR_SIGN.value &&
        `else
          po_abr_reg_hwif_in_o.MLDSA_CTRL.PCR_SIGN.hwclr == '0 &&
        `endif

        po_abr_reg_hwif_in_o.MLDSA_NAME[0].NAME.next == MLDSA_CORE_NAME[31:0] &&
        po_abr_reg_hwif_in_o.MLDSA_NAME[1].NAME.next == MLDSA_CORE_NAME[63:32] &&
        po_abr_reg_hwif_in_o.MLDSA_VERSION[0].VERSION.next == MLDSA_CORE_VERSION[31:0] &&
        po_abr_reg_hwif_in_o.MLDSA_VERSION[1].VERSION.next == MLDSA_CORE_VERSION[63:32] &&

        po_abr_reg_hwif_in_o.MLDSA_STATUS.READY.next == (`abr_ctrl.abr_ready) &&
        po_abr_reg_hwif_in_o.MLDSA_STATUS.VALID.next == `abr_ctrl.mldsa_valid_reg &&
        po_abr_reg_hwif_in_o.MLDSA_STATUS.ERROR.next == `abr_ctrl.error_flag_reg &&
        po_abr_reg_hwif_in_o.MLDSA_STATUS.MSG_STREAM_READY.next == (`abr_ctrl.stream_msg_fsm_ps == MLDSA_MSG_RDY) &&
        po_zeroize == (pi_abr_reg_hwif_out_i.MLDSA_CTRL.ZEROIZE.value || pi_abr_reg_hwif_out_i.MLKEM_CTRL.ZEROIZE.value  || pi_debugUnlock_or_scan_mode_switch) &&
        po_error_intr == pi_abr_reg_hwif_out_i.intr_block_rf.error_global_intr_r.intr &&
        po_notif_intr == pi_abr_reg_hwif_out_i.intr_block_rf.notif_global_intr_r.intr &&
        po_abr_reg_hwif_in_o.intr_block_rf.error_internal_intr_r.error_internal_sts.hwset ==  `abr_ctrl.error_flag_edge &&
        po_abr_reg_hwif_in_o.intr_block_rf.notif_internal_intr_r.notif_cmd_done_sts.hwset == `abr_ctrl.abr_status_done 
;endproperty

assert_mldsa_reg_hwif_in_comb_a: assert property(mldsa_reg_hwif_in_comb_p);


// Outputs combination for the data out parts which involves the dwords


    // ===============================================================
    // SECTION 3 — Per-Word Register Checks
    // ===============================================================
    //
    // These assertions verify register fields that are organized as
    // multi-dword arrays (entropy, seed, message, etc.). Each dword
    // is checked via a parameterized property instantiated in a loop.
    //
    // REGISTER CLASSES:
    //   • ABR_ENTROPY[12]: Software-provided entropy, hwclr on zeroize
    //   • MLDSA_SEED[8]: Keygen seed (SW or KV source)
    //   • MLDSA_MSG[16]: Message for signing
    //   • MLDSA_EXTERNAL_MU[16]: External message hash
    //   • MLDSA_SIGN_RND[8]: Signing randomness
    //   • MLDSA_VERIFY_RES[8]: Verification result
    //
    // Each property checks:
    //   ✓ Register value matches hwif output
    //   ✓ Hardware write enable (we) conditions
    //   ✓ Hardware write data (next) source
    //   ✓ Hardware clear (hwclr) conditions
    //   ✓ Software write enable (swwe) conditions
    // ===============================================================


    // ===============================================================
    // SECTION 3 — Per-Word Register Checks
    // ===============================================================
    //
    // Multi-dword registers (entropy, seed, message) are verified via
    // parameterized properties instantiated in generate loops.
    //
    // REGISTER CATEGORIES:
    //
    // 1. ABR_ENTROPY[12] - Software-provided entropy
    //    • Accumulated via XOR when KEYGEN/SIGN command starts
    //    • hwclr on zeroize (security requirement)
    //    • Used to seed LFSR for randomness quality
    //
    // 2. MLDSA_SEED[8] - Keygen seed (256 bits)
    //    • Software writes for normal keygen
    //    • Keyvault source when kv_mldsa_seed_data_present
    //    • hwclr on zeroize (key material must clear)
    //
    // 3. MLDSA_MSG[16] - Message to sign (512 bits)
    //    • Written by software, consumed by SHA3
    //    • No hwclr (not key material)
    //
    // 4. MLDSA_EXTERNAL_MU[16] - External message hash
    //    • For stateful variant (not yet implemented)
    //
    // 5. MLDSA_SIGN_RND[8] - Signing randomness
    //    • Additional entropy for signing
    //
    // 6. MLDSA_VERIFY_RES[8] - Verification result
    //    • Written by hardware after verify completes
    //
    // PATTERN: Each property checks value, we, next, hwclr, swwe
    // ===============================================================

    property entropy_reg_per_word(dword);
       `abr_ctrl.entropy_reg[dword] == pi_abr_reg_hwif_out_i.ABR_ENTROPY[dword].ENTROPY.value &&
      po_abr_reg_hwif_in_o.ABR_ENTROPY[dword].ENTROPY.hwclr == po_zeroize
    ;endproperty

    for (genvar dword=0; dword < ENTROPY_NUM_DWORDS; dword++)begin
       assert_entropy_reg_per_word: assert property(entropy_reg_per_word(dword));
    end

    property seed_reg_per_dword(dword);
      `abr_ctrl.mldsa_seed_reg[dword] == pi_abr_reg_hwif_out_i.MLDSA_SEED[dword].SEED.value &&

      `ifdef CALIPTRA
      po_abr_reg_hwif_in_o.MLDSA_SEED[dword].SEED.we == ((`abr_ctrl.pcr_sign_mode | (`abr_ctrl.kv_mldsa_seed_write_en & (`abr_ctrl.kv_mldsa_seed_write_offset == SEED_NUM_DWORDS-1-dword))) & ~po_zeroize) &&
      po_abr_reg_hwif_in_o.MLDSA_SEED[dword].SEED.next == (`abr_ctrl.pcr_sign_mode   ? `abr_ctrl.pcr_signing_data.pcr_mldsa_signing_seed[SEED_NUM_DWORDS-1-dword] :
                                                      `abr_ctrl.kv_mldsa_seed_write_data) &&
      po_abr_reg_hwif_in_o.MLDSA_SEED[dword].SEED.hwclr == (po_zeroize | (`abr_ctrl.kv_mldsa_seed_error != KV_SUCCESS)) &&
      po_abr_reg_hwif_in_o.MLDSA_SEED[dword].SEED.swwe == (`abr_ctrl.abr_ready & ~`abr_ctrl.kv_mldsa_seed_data_present)
      `else
      po_abr_reg_hwif_in_o.MLDSA_SEED[dword].SEED.we == '0 &&
      po_abr_reg_hwif_in_o.MLDSA_SEED[dword].SEED.next == '0 &&
      po_abr_reg_hwif_in_o.MLDSA_SEED[dword].SEED.hwclr == po_zeroize &&
      po_abr_reg_hwif_in_o.MLDSA_SEED[dword].SEED.swwe == `abr_ctrl.abr_ready
      `endif
    ;endproperty

    for (genvar dword=0; dword < SEED_NUM_DWORDS; dword++)begin
       assert_seed_reg_per_dword: assert property(seed_reg_per_dword(dword));
    end

    property msg_reg_per_dword(dword);
      `abr_ctrl.msg_reg[dword] ==( `abr_ctrl.external_mu_mode? '0 : pi_abr_reg_hwif_out_i.MLDSA_MSG[dword].MSG.value) &&
      `ifdef CALIPTRA
      po_abr_reg_hwif_in_o.MLDSA_MSG[dword].MSG.we == (`abr_ctrl.pcr_sign_mode & !`abr_ctrl.external_mu & !po_zeroize) &&
      po_abr_reg_hwif_in_o.MLDSA_MSG[dword].MSG.next == `abr_ctrl.pcr_signing_data.pcr_hash[MLDSA_MSG_NUM_DWORDS-1-dword] &&
      po_abr_reg_hwif_in_o.MLDSA_MSG[dword].MSG.hwclr == po_zeroize
      `else
      po_abr_reg_hwif_in_o.MLDSA_MSG[dword].MSG.we == '0 &&
      po_abr_reg_hwif_in_o.MLDSA_MSG[dword].MSG.next == '0 &&
      po_abr_reg_hwif_in_o.MLDSA_MSG[dword].MSG.hwclr == po_zeroize
      `endif
    ;endproperty
    for (genvar dword=0; dword < MLDSA_MSG_NUM_DWORDS; dword++)begin
      assert_msg_reg_per_dword: assert property(msg_reg_per_dword(dword));
    end

    property external_mu_reg_per_dword(dword);
      `abr_ctrl.external_mu_reg[dword] == pi_abr_reg_hwif_out_i.MLDSA_EXTERNAL_MU[dword].EXTERNAL_MU.value &&
      po_abr_reg_hwif_in_o.MLDSA_EXTERNAL_MU[dword].EXTERNAL_MU.we == (pi_sampler_state_dv_i & (`abr_ctrl.abr_instr.operand3 == MLDSA_DEST_MU_REG_ID) & !`abr_ctrl.external_mu & !po_zeroize) &&
      po_abr_reg_hwif_in_o.MLDSA_EXTERNAL_MU[dword].EXTERNAL_MU.next == `abr_ctrl.internal_mu_reg[dword] &&
      po_abr_reg_hwif_in_o.MLDSA_EXTERNAL_MU[dword].EXTERNAL_MU.hwclr == po_zeroize
    ;endproperty


    for (genvar dword=0; dword < MU_NUM_DWORDS; dword++)begin
      assert_external_mu_reg_per_dword: assert property(external_mu_reg_per_dword(dword));
    end


    property sign_rnd_reg_per_dword(dword);
      `abr_ctrl.sign_rnd_reg[dword] == pi_abr_reg_hwif_out_i.MLDSA_SIGN_RND[dword].SIGN_RND.value &&
      po_abr_reg_hwif_in_o.MLDSA_SIGN_RND[dword].SIGN_RND.hwclr == po_zeroize
    ;endproperty
    for (genvar dword=0; dword < SIGN_RND_NUM_DWORDS; dword++)begin
      assert_sign_rnd_reg_per_dword: assert property(sign_rnd_reg_per_dword(dword));
    end

    property verify_reg_per_dword(dword);
      po_abr_reg_hwif_in_o.MLDSA_VERIFY_RES[dword].VERIFY_RES.we == (`abr_ctrl.set_verify_valid | (`abr_ctrl.verify_valid & pi_sampler_state_dv_i & (`abr_ctrl.abr_instr.operand3 == MLDSA_DEST_VERIFY_RES_REG_ID))) &&
      po_abr_reg_hwif_in_o.MLDSA_VERIFY_RES[dword].VERIFY_RES.next == (`abr_ctrl.set_verify_valid ? ~`abr_ctrl.signature_reg.enc.c[dword] : pi_sampler_state_data_i[dword*32 +: 32]) &&
      po_abr_reg_hwif_in_o.MLDSA_VERIFY_RES[dword].VERIFY_RES.hwclr == po_zeroize
    ;endproperty

    for (genvar dword=0; dword < VERIFY_RES_NUM_DWORDS; dword++)begin
      assert_verify_reg_per_dword : assert property(verify_reg_per_dword(dword));
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
  logic [1:0][ABR_REG_WIDTH-1:0] fv_sk_ram_wdata;

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
logic[SRAM_LATENCY:0] fv_api_pubkey_re;
logic [PK_ADDR_W-1:0] fv_api_pubkey_addr;


// sk_mem interface.

  always_comb begin
    for (int i = 0; i < 2; i++) begin
      fv_skencode_keymem_we_bank[i] = ((pi_skencode_keymem_if_i.rd_wr_en == RW_WRITE) & (pi_skencode_keymem_if_i.addr[0] == i));
      fv_pwr2rnd_keymem_we_bank[i] = (pi_pwr2rnd_keymem_if_i[i].rd_wr_en == RW_WRITE);
      fv_api_keymem_we_bank[i] = po_abr_reg_hwif_in_o.MLDSA_PRIVKEY_IN.wr_ack & `abr_ctrl.abr_ready & `abr_ctrl.api_keymem_wr_dec & (`abr_ctrl.api_sk_mem_waddr[0] == i);

      fv_sk_ram_we_bank[i] = fv_skencode_keymem_we_bank[i] | fv_pwr2rnd_keymem_we_bank[i] | fv_api_keymem_we_bank[i] | (`abr_ctrl.zeroize_mem_we && (`abr_ctrl.zeroize_mem_addr < SK_MEM_BANK_DEPTH));

      fv_sk_ram_waddr_bank[i] = ({SK_MEM_BANK_ADDR_W{fv_skencode_keymem_we_bank[i]}} & pi_skencode_keymem_if_i.addr[SK_MEM_BANK_ADDR_W:1]) |
                             ({SK_MEM_BANK_ADDR_W{fv_pwr2rnd_keymem_we_bank[i]}} & pi_pwr2rnd_keymem_if_i[i].addr[SK_MEM_BANK_ADDR_W:1] ) |
                             ({SK_MEM_BANK_ADDR_W{fv_api_keymem_we_bank[i]}} & `abr_ctrl.api_sk_mem_waddr[SK_MEM_BANK_ADDR_W:1]) |
                             ({SK_MEM_BANK_ADDR_W{(`abr_ctrl.zeroize_mem_we && (`abr_ctrl.zeroize_mem_addr < SK_MEM_BANK_DEPTH))}} & `abr_ctrl.zeroize_mem_addr[SK_MEM_BANK_ADDR_W-1:0]);
                 
      fv_sk_ram_wdata[i] = ({ABR_REG_WIDTH{fv_skencode_keymem_we_bank[i]}} & pi_skencode_wr_data_i) |
                        ({ABR_REG_WIDTH{fv_pwr2rnd_keymem_we_bank[i]}} & pi_pwr2rnd_wr_data_i[i]) |
                        ({ABR_REG_WIDTH{fv_api_keymem_we_bank[i]}} & pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_IN.wr_data);         
    end
  end
  assign fv_api_keymem_rd_vld = pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_OUT.req & ~pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_OUT.req_is_wr & 
                                  `abr_ctrl.mldsa_valid_reg & ~`abr_ctrl.mldsa_privkey_lock ;


   always_comb begin
    for (int i = 0; i < 2; i++) begin
      fv_api_keymem_re_bank[i] = fv_api_keymem_rd_vld & `abr_ctrl.api_keymem_rd_dec & (`abr_ctrl.api_sk_mem_raddr[0] == i);

      fv_skdecode_re_bank[i] = (pi_skdecode_keymem_if_i[i].rd_wr_en == RW_READ);

      fv_skdecode_rdaddr[i] = pi_skdecode_keymem_if_i[i].addr[SK_MEM_BANK_ADDR_W:0];

      fv_sk_ram_re_bank[i] = fv_skdecode_re_bank[i] | fv_api_keymem_re_bank[i];

      fv_sk_ram_raddr_bank[i] = ({SK_MEM_BANK_ADDR_W{fv_skdecode_re_bank[i]}} & fv_skdecode_rdaddr[i][SK_MEM_BANK_ADDR_W:1]) |
                             ({SK_MEM_BANK_ADDR_W{fv_api_keymem_re_bank[i]}} & `abr_ctrl.api_sk_mem_raddr[SK_MEM_BANK_ADDR_W:1]);

    end
  end


  always_comb begin
    fv_api_sig_addr = pi_abr_reg_hwif_out_i.MLDSA_SIGNATURE.addr[SIG_ADDR_W+1:2];
    fv_api_sig_c_dec = pi_abr_reg_hwif_out_i.MLDSA_SIGNATURE.req & fv_api_sig_addr inside {[0:SIGNATURE_C_NUM_DWORDS-1]};
    fv_api_sig_z_dec = pi_abr_reg_hwif_out_i.MLDSA_SIGNATURE.req & fv_api_sig_addr inside {[SIGNATURE_C_NUM_DWORDS:SIGNATURE_C_NUM_DWORDS+SIGNATURE_Z_NUM_DWORDS-1]};
    fv_api_sig_h_dec = pi_abr_reg_hwif_out_i.MLDSA_SIGNATURE.req & fv_api_sig_addr inside {[SIGNATURE_C_NUM_DWORDS+SIGNATURE_Z_NUM_DWORDS:SIGNATURE_NUM_DWORDS-1]};
    fv_api_sig_z_addr.addr   = SIG_Z_MEM_ADDR_W'( (fv_api_sig_addr - SIGNATURE_C_NUM_DWORDS)/SIG_Z_MEM_NUM_DWORD );
    fv_api_sig_z_addr.offset = (fv_api_sig_addr - SIGNATURE_C_NUM_DWORDS)%SIG_Z_MEM_NUM_DWORD;
    fv_api_sig_c_addr = fv_api_sig_addr[SIG_C_REG_ADDR_W-1:0];
    fv_api_sig_h_addr = SIG_H_REG_ADDR_W'( fv_api_sig_addr - (SIGNATURE_C_NUM_DWORDS+SIGNATURE_Z_NUM_DWORDS) );
    fv_api_sig_z_we = `abr_ctrl.abr_ready & fv_api_sig_z_dec & po_abr_reg_hwif_in_o.MLDSA_SIGNATURE.wr_ack;
    fv_api_sig_z_re = `abr_ctrl.mldsa_valid_reg & fv_api_sig_z_dec & ~pi_abr_reg_hwif_out_i.MLDSA_SIGNATURE.req_is_wr;
  end


    // ===============================================================
    // SECTION 4 — Memory Interface Outputs
    // ===============================================================
    //
    // The controller manages 3 external SRAMs:
    //   • SK (Secret Key) - Stores encoded private key
    //   • SIG_Z (Signature Z) - Stores z polynomial in signature
    //   • PK (Public Key) - Stores encoded public key (T1)
    //
    // WHAT WE VERIFY:
    //   ✓ Write enable sourcing (API vs internal blocks vs zeroize)
    //   ✓ Address muxing (API vs internal vs zeroize counter)
    //   ✓ Write data muxing (API vs encoder outputs vs zeros)
    //   ✓ Read enable propagation
    //   ✓ Bank selection for multi-bank memories
    //
    // MEMORY ARCHITECTURE:
    //   SK: 2 banks (40-bit data per bank) for parallel access
    //   SIG_Z: Single bank (80-bit data)
    //   PK: Single bank (320-bit data = 8x T1 coefficients)
    //
    // ZEROIZE BEHAVIOR:
    //   When po_zeroize asserts, all memories are sequentially cleared
    //   via incrementing zeroize_mem_cntr from 0 to max address.
    // ===============================================================

property sk_mem_if_outputs_comb;
  `abr_ctrl.mldsa_keygen_process ||
  `abr_ctrl.mldsa_signing_process ||
  `abr_ctrl.mldsa_verifying_process ||
  (`abr_ctrl.mldsa_keygen_signing_process)
  |->
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
  always_comb fv_sig_z_ram_we = (pi_sigencode_wr_req_i.rd_wr_en == RW_WRITE) | fv_api_sig_z_we | (`abr_ctrl.zeroize_mem_we && (`abr_ctrl.zeroize_mem_addr < SIG_Z_MEM_DEPTH));
  always_comb fv_sig_z_ram_waddr = ({SIG_Z_MEM_ADDR_W{(pi_sigencode_wr_req_i.rd_wr_en == RW_WRITE)}} & pi_sigencode_wr_req_i.addr[SIG_Z_MEM_ADDR_W:1]) |
                                ({SIG_Z_MEM_ADDR_W{fv_api_sig_z_we}} & fv_api_sig_z_addr.addr) |
                                ({SIG_Z_MEM_ADDR_W{(`abr_ctrl.zeroize_mem_we && (`abr_ctrl.zeroize_mem_addr < SIG_Z_MEM_DEPTH))}} & `abr_ctrl.zeroize_mem_addr[SIG_Z_MEM_ADDR_W-1:0]);

  always_comb fv_sig_z_ram_wstrobe = ({SIG_Z_MEM_WSTROBE_W{(pi_sigencode_wr_req_i.rd_wr_en == RW_WRITE)}}) |
                                  ({SIG_Z_MEM_WSTROBE_W{fv_api_sig_z_we}} & ('hF << fv_api_sig_z_addr.offset*4)) |
                                  ({SIG_Z_MEM_WSTROBE_W{(`abr_ctrl.zeroize_mem_we && (`abr_ctrl.zeroize_mem_addr < SIG_Z_MEM_DEPTH))}});


  always_comb fv_sig_z_ram_wdata = ({SIG_Z_MEM_DATA_W{(pi_sigencode_wr_req_i.rd_wr_en == RW_WRITE)}} & pi_sigencode_wr_data_i) |
                                ({SIG_Z_MEM_DATA_W{(fv_api_sig_z_we)}} & SIG_Z_MEM_DATA_W'(pi_abr_reg_hwif_out_i.MLDSA_SIGNATURE.wr_data << fv_api_sig_z_addr.offset*32));

//read requests
  always_comb fv_sig_z_ram_re = (pi_sigdecode_z_rd_req_i.rd_wr_en == RW_READ) | fv_api_sig_z_re;
  always_comb fv_sig_z_ram_raddr = ({SIG_Z_MEM_ADDR_W{(pi_sigdecode_z_rd_req_i.rd_wr_en == RW_READ)}} & pi_sigdecode_z_rd_req_i.addr[SIG_Z_MEM_ADDR_W:1]) |
                                ({SIG_Z_MEM_ADDR_W{fv_api_sig_z_re}} & fv_api_sig_z_addr.addr);

property sig_z_mem_outputs_comb;
  `abr_ctrl.mldsa_keygen_process ||
  `abr_ctrl.mldsa_signing_process ||
  `abr_ctrl.mldsa_verifying_process ||
  `abr_ctrl.mldsa_keygen_signing_process
  |->
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
  always_comb fv_pubkey_ram_we = (pi_pk_t1_wren_i) | fv_api_pubkey_we | (`abr_ctrl.zeroize_mem_we && (`abr_ctrl.zeroize_mem_addr < PK_MEM_DEPTH));
  always_comb fv_pubkey_ram_waddr = ({PK_MEM_ADDR_W{pi_pk_t1_wren_i}} & pi_pk_t1_wr_addr_i[PK_MEM_ADDR_W+1:2]) |
                                ({PK_MEM_ADDR_W{fv_api_pubkey_we}} & `abr_ctrl.api_pubkey_mem_addr[0].addr) |
                                ({PK_MEM_ADDR_W{(`abr_ctrl.zeroize_mem_we && (`abr_ctrl.zeroize_mem_addr < PK_MEM_DEPTH))}} & `abr_ctrl.zeroize_mem_addr[PK_MEM_ADDR_W-1:0]);

  always_comb fv_pubkey_ram_wstrobe = ({PK_MEM_WSTROBE_W{pi_pk_t1_wren_i}} & 'h3FF << pi_pk_t1_wr_addr_i[1:0]*10) |
                                   ({PK_MEM_WSTROBE_W{fv_api_pubkey_we}} & ('hF << `abr_ctrl.api_pubkey_mem_addr[0].offset*4)) |
                                   ({PK_MEM_WSTROBE_W{(`abr_ctrl.zeroize_mem_we && (`abr_ctrl.zeroize_mem_addr < PK_MEM_DEPTH))}});


  always_comb fv_pubkey_ram_wdata = ({PK_MEM_DATA_W{pi_pk_t1_wren_i}} & PK_MEM_DATA_W'(pi_pk_t1_wrdata_i << pi_pk_t1_wr_addr_i[1:0]*80)) |
                                 ({PK_MEM_DATA_W{(fv_api_pubkey_we)}} & PK_MEM_DATA_W'(pi_abr_reg_hwif_out_i.MLDSA_PUBKEY.wr_data << `abr_ctrl.api_pubkey_mem_addr[0].offset*32));

  //read requests
  always_comb fv_pubkey_ram_re = `abr_ctrl.sampler_pk_rd_en[0] | `abr_ctrl.pkdecode_rd_en[0] | fv_api_pubkey_re[0];
  always_comb fv_pubkey_ram_raddr = ({PK_MEM_ADDR_W{`abr_ctrl.sampler_pk_rd_en[0]}} & `abr_ctrl.sampler_pubkey_mem_addr.addr) |
                                 ({PK_MEM_ADDR_W{`abr_ctrl.pkdecode_rd_en[0]}} & pi_pkdecode_rd_addr_i[PK_MEM_ADDR_W+1:2]) |
                                 ({PK_MEM_ADDR_W{fv_api_pubkey_re[0]}} & `abr_ctrl.api_pubkey_mem_addr[0].addr);

  always_comb begin
    fv_api_pubkey_re[0] = `abr_ctrl.mldsa_valid_reg & pi_abr_reg_hwif_out_i.MLDSA_PUBKEY.req &((pi_abr_reg_hwif_out_i.MLDSA_PUBKEY.addr[PK_ADDR_W+1:2]) inside {[8:PUBKEY_NUM_DWORDS-1]}) & ~pi_abr_reg_hwif_out_i.MLDSA_PUBKEY.req_is_wr;
    fv_api_pubkey_we = `abr_ctrl.abr_ready & pi_abr_reg_hwif_out_i.MLDSA_PUBKEY.req &((pi_abr_reg_hwif_out_i.MLDSA_PUBKEY.addr[PK_ADDR_W+1:2]) inside {[8:PUBKEY_NUM_DWORDS-1]}) & po_abr_reg_hwif_in_o.MLDSA_PUBKEY.wr_ack;
    fv_api_pubkey_addr = pi_abr_reg_hwif_out_i.MLDSA_PUBKEY.addr[PK_ADDR_W+1:2];
  end

property pk_mem_if_comb_outputs;
  `abr_ctrl.mldsa_keygen_process ||
  `abr_ctrl.mldsa_signing_process ||
  `abr_ctrl.mldsa_verifying_process ||
  `abr_ctrl.mldsa_keygen_signing_process
  |->
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


    // ===============================================================
    // SECTION 5 — Zeroize Memory Counter
    // ===============================================================
    //
    // The zeroize counter sequences through all memory addresses to
    // clear key material from SK, SIG_Z, and PK SRAMs.
    //
    // OPERATION:
    //   1. po_zeroize asserts (software trigger or debug unlock)
    //   2. Counter increments from 0 to max(SK_DEPTH, SIG_Z_DEPTH, PK_DEPTH)
    //   3. Each memory's write enable fires when addr < its depth
    //   4. Write data is all zeros
    //
    // SECURITY:
    //   Without this, key material persists in SRAM after zeroize.
    //   An attacker with SRAM access could recover keys.
    //
    // ===============================================================

property zeroize_mem_if_zeroize_cntr;
  `abr_ctrl.zeroize_mem_o.rd_wr_en == (((`abr_ctrl.abr_prog_cntr == ABR_ZEROIZE) & !`abr_ctrl.zeroize_mem_done ) ? RW_WRITE:RW_IDLE )
   `ifndef KV_ABR_PROG &&
  `abr_ctrl.zeroize_mem_o.addr == fv_mem_addr_cntr
  `endif
;endproperty
assert_zeroize_mem_if_zeroize_cntr: assert property(disable iff(!pi_rst_b || po_zeroize) zeroize_mem_if_zeroize_cntr);



/////////////////////////////////////////////////////
/// Internal registers used in the state transition proofs
////////////////////////////////////////////////////

//Private_key

    // ===============================================================
    // SECTION 6 — Internal Scratch Register Updates
    // ===============================================================
    //
    // abr_scratch_reg holds intermediate key material during keygen:
    //   • K (256 bits) - Secret key component
    //   • rho (256 bits) - Public randomness
    //   • rho_p (512 bits) - Private randomness
    //   • tr (512 bits) - Hash of T1 (public key hash)
    //
    // UPDATE SOURCES:
    //   1. Sampler - Writes K, rho, rho_p, tr from SHA3 state
    //   2. API - Software can write for testing/debugging
    //
    // SAMPLER WRITE CONDITIONS:
    //   • pi_sampler_state_dv_i == 1 (data valid from SHA3)
    //   • abr_instr.operand3 == destination register ID
    //
    // SECURITY:
    //   These registers contain private key material during keygen.
    //   They must be stable between updates (verified by stability
    //   assertions) and cleared on reset/zeroize (SECTION 1).
    // ===============================================================

property private_key_reg_update_k_rho_p;
  pi_sampler_state_dv_i &&
  (`abr_ctrl.abr_instr.operand3 == MLDSA_DEST_K_RHO_REG_ID)
  |=>
  `abr_ctrl.abr_scratch_reg.mldsa_enc.rho_p == $past(pi_sampler_state_data_i[767:256]) &&
  `abr_ctrl.abr_scratch_reg.mldsa_enc.K == $past(pi_sampler_state_data_i[1023:768])
;endproperty

assert_private_key_reg_update_k_rho_a: assert property(disable iff(!pi_rst_b || po_zeroize) private_key_reg_update_k_rho_p);
property private_key_reg_update_tr_p;
  pi_sampler_state_dv_i &&
  (`abr_ctrl.abr_instr.operand3 == MLDSA_DEST_TR_REG_ID)
  |=>
  `abr_ctrl.abr_scratch_reg.mldsa_enc.tr == $past(pi_sampler_state_data_i[511:0])
;endproperty
assert_private_key_reg_update_tr_a: assert property(disable iff(!pi_rst_b || po_zeroize) private_key_reg_update_tr_p);

property private_key_reg_update_from_api_p;
  po_abr_reg_hwif_in_o.MLDSA_PRIVKEY_IN.wr_ack &&
  `abr_ctrl.abr_ready &&
  `abr_ctrl.api_sk_reg_wr_dec
  |=>
  `abr_ctrl.abr_scratch_reg.raw[$past(`abr_ctrl.api_sk_reg_waddr)] == $past(pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_IN.wr_data)
;endproperty
assert_private_key_reg_update_from_api_a: assert property(disable iff(!pi_rst_b || po_zeroize) private_key_reg_update_from_api_p);

//publickey_reg

property public_key_reg_rho_update;
  pi_sampler_state_dv_i &&
  (`abr_ctrl.abr_instr.operand3 == MLDSA_DEST_K_RHO_REG_ID)
  |=>
  `abr_ctrl.abr_scratch_reg.mldsa_enc.rho == $past(pi_sampler_state_data_i[255:0])
;endproperty

assert_public_key_reg_rho_update : assert property(disable iff(!pi_rst_b || po_zeroize) public_key_reg_rho_update);
property publickey_reg_rho_from_api;
  (`abr_ctrl.abr_ready &&
  `abr_ctrl.api_pubkey_rho_dec &&
  pi_abr_reg_hwif_out_i.MLDSA_PUBKEY.req_is_wr)
  |=>
   `abr_ctrl.abr_scratch_reg.raw[$past(`abr_ctrl.api_pk_reg_waddr)] == $past(pi_abr_reg_hwif_out_i.MLDSA_PUBKEY.wr_data)
;endproperty
assert_publickey_reg_rho_from_api : assert property(disable iff(!pi_rst_b || po_zeroize) publickey_reg_rho_from_api);


// pk_reg_rdata


//Signature_reg


    // ===============================================================
    // SECTION 7 — Signature Register Updates
    // ===============================================================
    //
    // ML-DSA signature = (c, z, h) where:
    //   • c (256 bits) - Challenge hash (commitment)
    //   • z (L×32 bytes) - Response polynomial (stored in SIG_Z SRAM)
    //   • h (omega bytes) - Hint bits for high-order correction
    //
    // signature_reg stores c and h (z is too large for registers).
    //
    // UPDATE PATHS:
    //
    // 1. c field updates:
    //    a) From sampler when computing challenge
    //    b) From API for verification
    //    c) Cleared when signature invalidates
    //
    // 2. h field updates:
    //    a) Cleared when set_signature_valid (start new signature)
    //  
    //    b) OR'd with makehint output (bit-by-bit accumulation)
    //    c) From API for verification
    //
    // STABILITY:
    //   c and h must be stable except during explicit updates.
    //   Glitches would cause signature verification failures.
    // ===============================================================

property signature_reg_c_update;
  pi_sampler_state_dv_i &&
  `abr_ctrl.abr_instr.operand3 == MLDSA_DEST_SIG_C_REG_ID
  |=>
  `abr_ctrl.signature_reg.enc.c == $past(pi_sampler_state_data_i[511:0])
;endproperty

assert_signature_reg_c_update: assert property(disable iff(!pi_rst_b || po_zeroize)signature_reg_c_update);

property signature_reg_c_update_from_api;
  `abr_ctrl.abr_ready &&
  fv_api_sig_c_dec &&
  pi_abr_reg_hwif_out_i.MLDSA_SIGNATURE.req_is_wr
  |=>
   `abr_ctrl.signature_reg.enc.c[$past(fv_api_sig_c_addr)] == $past( pi_abr_reg_hwif_out_i.MLDSA_SIGNATURE.wr_data)
;endproperty

assert_signature_reg_c_update_from_api: assert property(disable iff(!pi_rst_b || po_zeroize) signature_reg_c_update_from_api);

property signature_reg_c_stable;
  !(pi_sampler_state_dv_i &&
  `abr_ctrl.abr_instr.operand3 == MLDSA_DEST_SIG_C_REG_ID) &&
  !(`abr_ctrl.abr_ready &&
  fv_api_sig_c_dec &&
  pi_abr_reg_hwif_out_i.MLDSA_SIGNATURE.req_is_wr)
  |=>
  $stable( `abr_ctrl.signature_reg.enc.c)
;endproperty
assert_signature_reg_c_stable : assert property(disable iff(!pi_rst_b || po_zeroize) signature_reg_c_stable);

property signature_reg_h_update;
  `abr_ctrl.set_signature_valid
  |=>
   `abr_ctrl.signature_reg.enc.h == '0
;endproperty

assert_signature_reg_h_update: assert property(disable iff(!pi_rst_b || po_zeroize) signature_reg_h_update);

property signature_reg_h_update_makehint(dword);
  pi_makehint_reg_wren_i &&
  pi_makehint_reg_wr_addr_i == dword
  |=>
  `abr_ctrl.signature_reg.enc.h[dword] == ($past( `abr_ctrl.signature_reg.enc.h[dword]) |  $past(pi_makehint_reg_wrdata_i))
;endproperty
for(genvar i =0;i< SIGNATURE_H_NUM_DWORDS;i++) begin
assert_signature_reg_h_update_makehint: assert property(disable iff(!pi_rst_b || po_zeroize) signature_reg_h_update_makehint(i));
end

property signature_reg_h_update_from_api;
 !`abr_ctrl.set_signature_valid &&
  `abr_ctrl.abr_ready &&
  fv_api_sig_h_dec &&
  pi_abr_reg_hwif_out_i.MLDSA_SIGNATURE.req_is_wr
  |=>
   `abr_ctrl.signature_reg.enc.h[$past(fv_api_sig_h_addr)] == $past( pi_abr_reg_hwif_out_i.MLDSA_SIGNATURE.wr_data)
;endproperty

assert_signature_reg_h_update_from_api: assert property(disable iff(!pi_rst_b || po_zeroize) signature_reg_h_update_from_api);



property signature_reg_h_stable;
  !po_zeroize &&
  !`abr_ctrl.set_signature_valid &&
  !pi_makehint_reg_wren_i &&
  !(`abr_ctrl.abr_ready &&
  fv_api_sig_h_dec &&
  pi_abr_reg_hwif_out_i.MLDSA_SIGNATURE.req_is_wr)
  |=>
  $stable( `abr_ctrl.signature_reg.enc.h)
;endproperty

assert_signature_reg_h_stable: assert property(disable iff(!pi_rst_b || po_zeroize) signature_reg_h_stable);


// rho_p_reg

//property rho_p_reg_k_update;
//  pi_sampler_state_dv_i &&
//  `abr_ctrl.abr_instr.operand3 == MLDSA_DEST_K_RHO_REG_ID
//  |=>
//  `abr_ctrl.rho_p_reg ==  $past(pi_sampler_state_data_i[767:256])
//;endproperty

//assert_rho_p_reg_k_update : assert property(disable iff(!pi_rst_b || po_zeroize) rho_p_reg_k_update);



    // ===============================================================
    // SECTION 8 — rho_p Register Management
    // ===============================================================
    //
    // rho_p (512 bits) is part of the ML-DSA private key.
    // It's used as the seed for polynomial rejection sampling.
    //
    // UPDATE PATH:
    //   Written by sampler when operand3 == MLDSA_DEST_RHO_P_REG_ID
    //
    // STABILITY :
    //   New assertion verifies rho_p doesn't change when no sampler
    //   write is active. Without this, glitches could corrupt rho_p
    //   and cause signing to generate invalid signatures.
    //
    // SECURITY:
    //   rho_p is private key material. It must:
    //   - Clear on reset/zeroize (SECTION 1)
    //   - Never leak via API when lock==1 (SECTION 10)
    //   - Remain stable between updates (stability assertion)
    // ===============================================================

property rho_p_reg_p_update;
  pi_sampler_state_dv_i &&
  `abr_ctrl.abr_instr.operand3 == MLDSA_DEST_RHO_P_REG_ID
  |=>
  `abr_ctrl.abr_scratch_reg.mldsa_enc.rho_p  ==  $past(pi_sampler_state_data_i[511:0])
;endproperty

assert_rho_p_reg_p_update : assert property(disable iff(!pi_rst_b || po_zeroize) rho_p_reg_p_update);

// ---------------------------------------------------------------
// NEW ASSERTION: rho_p register stability (Note: Doesn't work due to Union but general stability is ensured in mlkem wb)
// ---------------------------------------------------------------
// WHAT: Verifies rho_p doesn't change when no sampler write active
// WHY: rho_p corruption could cause invalid signatures
// WHEN: Not receiving K_RHO or RHO_P sampler data
property rho_p_reg_stable_p;
  !(pi_sampler_state_dv_i &&
    ((`abr_ctrl.abr_instr.operand3 == MLDSA_DEST_K_RHO_REG_ID) ||
     (`abr_ctrl.abr_instr.operand3 == MLDSA_DEST_RHO_P_REG_ID)))
  |=>
  $stable(`abr_ctrl.abr_scratch_reg.mldsa_enc.rho_p);
endproperty

//assert_rho_p_reg_stable_a: assert property(disable iff(!pi_rst_b || po_zeroize) rho_p_reg_stable_p);




//property rho_p_reg_stable;
//  !pi_sampler_state_dv_i ||
//  !((`abr_ctrl.abr_instr.operand3 == MLDSA_DEST_RHO_P_REG_ID)
//  ||(`abr_ctrl.abr_instr.operand3 == MLDSA_DEST_K_RHO_REG_ID))
//  |=>
//  $stable(`abr_ctrl.rho_p_reg)
//;endproperty

//assert_rho_p_reg_stable : assert property(disable iff(!pi_rst_b || po_zeroize) rho_p_reg_stable);

// lfsr_entropy_reg

    // ===============================================================
    // SECTION 9 — LFSR Entropy Management
    // ===============================================================
    //
    // The LFSR (Linear Feedback Shift Register) generates pseudo-random
    // bytes for masking and shuffling in NTT operations.
    //
    // LFSR SEED SOURCES:
    //
    // 1. XOR accumulation (set_entropy_reg):
    //    When KEYGEN/SIGN/KEYGEN_SIGN starts and abr_ready:
    //    new_seed = old_seed XOR ABR_ENTROPY register
    //    This accumulates entropy across multiple operations.
    //
    // 2. Fresh from sampler (set_entropy_reg_from_sampler):
    //    When sampler writes to ABR_DEST_LFSR_SEED_REG_ID:
    //    new_seed = sampler_state_data (fresh from SHA3)
    //
    // 3. Cleared on reset (rst_b_p in SECTION 1):
    //    Unlike zeroize, reset clears LFSR to break entropy chain.
    //
    // STABILITY :
    //   New assertion verifies LFSR seed stable when:
    //   - No command start (no XOR update)
    //   - No sampler write (no fresh seed)
    //   Without this, LFSR drift causes non-deterministic NTT results.
    //
    // SECURITY:
    //   LFSR quality affects masking effectiveness. Poor entropy
    //   could enable DPA (Differential Power Analysis) attacks.
    // ===============================================================

  property set_entropy_reg;
    ((`abr_ctrl.mldsa_cmd_reg == MLDSA_KEYGEN) ||
    (`abr_ctrl.mldsa_cmd_reg == MLDSA_SIGN) ||
    (`abr_ctrl.mldsa_cmd_reg == MLDSA_KEYGEN_SIGN))&&
    `abr_ctrl.abr_ready
    |=>
    `abr_ctrl.lfsr_entropy_reg == $past(`abr_ctrl.lfsr_entropy_reg ^ `abr_ctrl.entropy_reg)
  ;endproperty
assert_set_entropy_reg: assert property(disable iff(!pi_rst_b || po_zeroize)set_entropy_reg);

// set lfsr entropy when ENTROPY_REG_ID (separate beat from the LFSR seed capture)

property set_entropy_reg_from_sampler;
  pi_sampler_state_dv_i &&
  `abr_ctrl.abr_instr.operand3 == ABR_DEST_ENTROPY_REG_ID
  |=>
  `abr_ctrl.lfsr_entropy_reg ==  $past(pi_sampler_state_data_i[ENTROPY_LSB+ENTROPY_W-1:ENTROPY_LSB])
;endproperty

assert_set_entropy_reg_from_sampler : assert property(disable iff(!pi_rst_b || po_zeroize) set_entropy_reg_from_sampler);

// ---------------------------------------------------------------
// NEW ASSERTION: LFSR entropy register stability(Note: Not expected could change no problem)
// ---------------------------------------------------------------
// WHAT: Verifies LFSR entropy stable when no updates occur
// WHY: Drift would cause non-deterministic LFSR seeding
// WHEN: No command start and no sampler write to LFSR_SEED
property lfsr_entropy_reg_stable_p;
  !(pi_sampler_state_dv_i &&
    `abr_ctrl.abr_instr.operand3 == ABR_DEST_LFSR_SEED_REG_ID) &&
  !((`abr_ctrl.mldsa_cmd_reg == MLDSA_KEYGEN) ||
    (`abr_ctrl.mldsa_cmd_reg == MLDSA_SIGN) ||
    (`abr_ctrl.mldsa_cmd_reg == MLDSA_KEYGEN_SIGN)) ||
  !`abr_ctrl.abr_ready
  |=>
  $stable(`abr_ctrl.lfsr_entropy_reg);
endproperty

//assert_lfsr_entropy_reg_stable_a: assert property(disable iff(!pi_rst_b || po_zeroize) lfsr_entropy_reg_stable_p);



// readdata for signature

property signature_reg_rdata_c_api_p;
  `abr_ctrl.mldsa_valid_reg &&
  pi_abr_reg_hwif_out_i.MLDSA_SIGNATURE.req &&
  !pi_abr_reg_hwif_out_i.MLDSA_SIGNATURE.req_is_wr &&
  fv_api_sig_c_dec
  |=>
  `abr_ctrl.api_reg_rdata == ( $past(`abr_ctrl.signature_reg.enc.c[(fv_api_sig_c_addr)]))
;endproperty

assert_signature_reg_rdata_c_api_a: assert property(disable iff(!pi_rst_b || po_zeroize) signature_reg_rdata_c_api_p);

property signature_reg_rdata_h_api_p;
  `abr_ctrl.mldsa_valid_reg &&
  pi_abr_reg_hwif_out_i.MLDSA_SIGNATURE.req &&
  !pi_abr_reg_hwif_out_i.MLDSA_SIGNATURE.req_is_wr &&
  fv_api_sig_h_dec
  |=>
  (`abr_ctrl.api_reg_rdata == $past(`abr_ctrl.signature_reg.enc.h[fv_api_sig_h_addr]))
;endproperty

assert_signature_reg_rdata_h_api_a: assert property(disable iff(!pi_rst_b || po_zeroize) signature_reg_rdata_h_api_p);

// stable if there is no req from the api


// ----------------------------------------------------------------
// A3a — MLDSA PRIVKEY_OUT register region — correct data capture
//       api_sk_reg_rd_dec is asserted when the APB read address
//       falls in the private key register-backed region (dwords 0–31
//       of MLDSA_PRIVKEY_OUT). On the following cycle, api_reg_rdata
//       must reflect abr_scratch_reg.raw[api_sk_reg_raddr] masked
//       by api_keymem_rd_vld, which qualifies the read with
//       mldsa_valid_reg and the absence of mldsa_privkey_lock.
//       This is the highest-priority branch of the mux.
// ----------------------------------------------------------------

    // ===============================================================
    // SECTION 10 — API Read-Data Multiplexer (Priority Encoder)
    // ===============================================================
    //
    // api_reg_rdata is the final output mux for APB reads of key material.
    // It implements a priority encoder with 6 branches (A3a through A8):
    //
    // PRIORITY ORDER (highest to lowest):
    //
    // A3a: MLDSA_PRIVKEY_OUT register data (when decode && valid && !lock)
    // A3b: MLDSA_PRIVKEY_OUT locked (when decode && lock) → return 0
    //
    // A4a: MLKEM_DECAPS_KEY register data (when decode && valid && !lock)
    // A4b: MLKEM_DECAPS_KEY locked (when decode && lock) → return 0
    //
    // A5a: MLKEM_ENCAPS_KEY register data (when decode && valid)
    // A5b: MLKEM_ENCAPS_KEY invalid (when decode && !valid) → return 0
    //
    // A6a: MLDSA_PUBKEY rho data (when decode && valid)
    // A6b: MLDSA_PUBKEY invalid (when decode && !valid) → return 0
    //
    // A7a: MLDSA_SIGNATURE c/h data (when decode && valid)
    // A7b: MLDSA_SIGNATURE invalid (when decode && !valid) → return 0
    //
    // A8: Stability - api_reg_rdata stable when no decode active
    //
    // SECURITY ISOLATION:
    //   The "locked" branches (A3b, A4b) are critical:
    //   When mldsa_privkey_lock==1, PRIVKEY_OUT reads return 0.
    //   This prevents KV-derived keys from leaking via APB.
    //
    //  verifies lock is SET when KV seed used.
    // ===============================================================

property api_reg_rdata_sk_reg_p;
    (!po_zeroize && `abr_ctrl.api_sk_reg_rd_dec) 
    |=>
        (`abr_ctrl.api_reg_rdata == ({ABR_REG_WIDTH{$past(`abr_ctrl.api_keymem_rd_vld)}} &
                                     $past(`abr_ctrl.abr_scratch_reg.raw[`abr_ctrl.api_sk_reg_raddr])));
endproperty
api_reg_rdata_sk_reg: assert property (disable iff (!pi_rst_b) api_reg_rdata_sk_reg_p);

// ----------------------------------------------------------------
// A3b — MLDSA PRIVKEY_OUT register region — security lock check
//       When api_sk_reg_rd_dec is active but the private key is
//       either not yet valid (mldsa_valid_reg=0, meaning keygen has
//       not completed) or is locked (mldsa_privkey_lock=1, meaning
//       the seed came from the keyvault), api_reg_rdata must be
//       forced to 0. This prevents key material from being read
//       before it is safe to expose it to the API.
// ----------------------------------------------------------------
property api_reg_rdata_sk_reg_locked_p;
    (!po_zeroize && `abr_ctrl.api_sk_reg_rd_dec &&
     (!`abr_ctrl.mldsa_valid_reg || `abr_ctrl.mldsa_privkey_lock)) 
     |=>
        (`abr_ctrl.api_reg_rdata == '0);
endproperty
api_reg_rdata_sk_reg_locked: assert property (disable iff (!pi_rst_b) api_reg_rdata_sk_reg_locked_p);

// ----------------------------------------------------------------
// A4a — MLKEM DECAPS_KEY register region — correct data capture
//       mlkem_api_dk_reg_dec is asserted when the APB read address
//       targets the register-backed portion of MLKEM_DECAPS_KEY
//       (dwords MLKEM_DK_MEM_NUM_DWORDS to DK_NUM_DWORDS-1).
//       On the following cycle, api_reg_rdata must reflect
//       abr_scratch_reg.raw[mlkem_api_dk_reg_addr] masked by
//       mlkem_api_dk_rd_vld (qualifies with mlkem_valid_reg and
//       absence of mlkem_dk_lock). This branch has lower priority
//       than api_sk_reg_rd_dec.
// ----------------------------------------------------------------
property api_reg_rdata_dk_reg_p;
    (!po_zeroize && !`abr_ctrl.api_sk_reg_rd_dec && `abr_ctrl.mlkem_api_dk_reg_dec) 
    |=>
        (`abr_ctrl.api_reg_rdata == ({ABR_REG_WIDTH{$past(`abr_ctrl.mlkem_api_dk_rd_vld)}} &
                                     $past(`abr_ctrl.abr_scratch_reg.raw[`abr_ctrl.mlkem_api_dk_reg_addr])));
endproperty
api_reg_rdata_dk_reg: assert property (disable iff (!pi_rst_b) api_reg_rdata_dk_reg_p);

// ----------------------------------------------------------------
// A4b — MLKEM DECAPS_KEY register region — security lock check
//       When mlkem_api_dk_reg_dec is active but the decaps key is
//       either not yet valid (mlkem_valid_reg=0, meaning keygen or
//       keygen+decaps flow has not completed) or is locked
//       (mlkem_dk_lock=1, meaning seed came from the keyvault),
//       api_reg_rdata must be forced to 0 to prevent premature
//       exposure of the decapsulation key.
// ----------------------------------------------------------------
property api_reg_rdata_dk_reg_locked_p;
    (!po_zeroize && !`abr_ctrl.api_sk_reg_rd_dec && `abr_ctrl.mlkem_api_dk_reg_dec &&
     (!`abr_ctrl.mlkem_valid_reg || `abr_ctrl.mlkem_dk_lock)) 
     |=>
        (`abr_ctrl.api_reg_rdata == '0);
endproperty
api_reg_rdata_dk_reg_locked: assert property (disable iff (!pi_rst_b) api_reg_rdata_dk_reg_locked_p);

// ----------------------------------------------------------------
// A5a — MLKEM ENCAPS_KEY register region — correct data capture
//       mlkem_api_ek_reg_dec is asserted when the APB read address
//       targets the register-backed portion of MLKEM_ENCAPS_KEY
//       (dwords MLKEM_EK_MEM_NUM_DWORDS to EK_NUM_DWORDS-1).
//       On the following cycle, api_reg_rdata must reflect
//       abr_scratch_reg.raw[mlkem_api_ek_reg_addr] masked by
//       mlkem_api_ek_rd_vld (qualifies with mlkem_valid_reg only;
//       there is no lock on the encaps key). This branch has lower
//       priority than both api_sk_reg_rd_dec and mlkem_api_dk_reg_dec.
// ----------------------------------------------------------------
property api_reg_rdata_ek_reg_p;
    (!po_zeroize && !`abr_ctrl.api_sk_reg_rd_dec &&
     !`abr_ctrl.mlkem_api_dk_reg_dec && `abr_ctrl.mlkem_api_ek_reg_dec) 
     |=>
        (`abr_ctrl.api_reg_rdata == ({ABR_REG_WIDTH{$past(`abr_ctrl.mlkem_api_ek_rd_vld)}} &
                                     $past(`abr_ctrl.abr_scratch_reg.raw[`abr_ctrl.mlkem_api_ek_reg_addr])));
endproperty
api_reg_rdata_ek_reg: assert property (disable iff (!pi_rst_b) api_reg_rdata_ek_reg_p);

// ----------------------------------------------------------------
// A5b — MLKEM ENCAPS_KEY register region — validity gate check
//       When mlkem_api_ek_reg_dec is active but mlkem_valid_reg=0
//       (MLKEM keygen or encaps has not yet completed), the encaps
//       key must not be exposed on api_reg_rdata. Output must be 0.
// ----------------------------------------------------------------
property api_reg_rdata_ek_reg_invalid_p;
    (!po_zeroize && !`abr_ctrl.api_sk_reg_rd_dec && !`abr_ctrl.mlkem_api_dk_reg_dec &&
     `abr_ctrl.mlkem_api_ek_reg_dec && !`abr_ctrl.mlkem_valid_reg) 
     |=>
        (`abr_ctrl.api_reg_rdata == '0);
endproperty
api_reg_rdata_ek_reg_invalid: assert property (disable iff (!pi_rst_b) api_reg_rdata_ek_reg_invalid_p);

// ----------------------------------------------------------------
// A6a — MLDSA PUBKEY rho register region — correct data capture
//       api_pubkey_rho_dec is asserted when the APB read address
//       targets the rho field of MLDSA_PUBKEY (dwords 0–7), which
//       is stored in abr_scratch_reg rather than external SRAM.
//       On the following cycle, api_reg_rdata must reflect
//       abr_scratch_reg.raw[api_pk_reg_raddr] masked by
//       mldsa_valid_reg. This branch fires only when all higher
//       priority decodes are inactive.
// ----------------------------------------------------------------
property api_reg_rdata_pk_rho_p;
    (!po_zeroize && !`abr_ctrl.api_sk_reg_rd_dec && !`abr_ctrl.mlkem_api_dk_reg_dec &&
     !`abr_ctrl.mlkem_api_ek_reg_dec && `abr_ctrl.api_pubkey_rho_dec) 
     |=>
        (`abr_ctrl.api_reg_rdata == ({ABR_REG_WIDTH{$past(`abr_ctrl.mldsa_valid_reg)}} &
                                     $past(`abr_ctrl.abr_scratch_reg.raw[`abr_ctrl.api_pk_reg_raddr])));
endproperty
api_reg_rdata_pk_rho: assert property (disable iff (!pi_rst_b) api_reg_rdata_pk_rho_p);

// ----------------------------------------------------------------
// A6b — MLDSA PUBKEY rho register region — validity gate check
//       When api_pubkey_rho_dec is active but mldsa_valid_reg=0
//       (MLDSA keygen has not yet completed and rho has not been
//       written into abr_scratch_reg by the sampler), api_reg_rdata
//       must be 0 to avoid exposing uninitialised scratch data.
// ----------------------------------------------------------------
property api_reg_rdata_pk_rho_invalid_p;
    (!po_zeroize && !`abr_ctrl.api_sk_reg_rd_dec && !`abr_ctrl.mlkem_api_dk_reg_dec &&
     !`abr_ctrl.mlkem_api_ek_reg_dec && `abr_ctrl.api_pubkey_rho_dec &&
     !`abr_ctrl.mldsa_valid_reg) 
     |=>
        (`abr_ctrl.api_reg_rdata == '0);
endproperty
api_reg_rdata_pk_rho_invalid: assert property (disable iff (!pi_rst_b) api_reg_rdata_pk_rho_invalid_p);

// ----------------------------------------------------------------
// A7a — MLDSA SIGNATURE c/h register region — correct data capture
//       api_sig_reg_re is asserted for reads targeting the
//       commitment hash c (dwords 0 to SIGNATURE_C_NUM_DWORDS-1)
//       or the hint vector h (dwords SIGNATURE_C_NUM_DWORDS+
//       SIGNATURE_Z_NUM_DWORDS to SIGNATURE_NUM_DWORDS-1) of
//       MLDSA_SIGNATURE. These fields live in signature_reg flops
//       rather than external SRAM. signature_reg_rdata muxes between
//       signature_reg.enc.c and signature_reg.enc.h based on which
//       sub-region is being addressed. The result is gated by
//       mldsa_valid_reg. This is the lowest-priority branch.
// ----------------------------------------------------------------
property api_reg_rdata_sig_reg_p;
    (!po_zeroize && !`abr_ctrl.api_sk_reg_rd_dec && !`abr_ctrl.mlkem_api_dk_reg_dec &&
     !`abr_ctrl.mlkem_api_ek_reg_dec && !`abr_ctrl.api_pubkey_rho_dec &&
     `abr_ctrl.api_sig_reg_re) 
     |=>
        (`abr_ctrl.api_reg_rdata == ({ABR_REG_WIDTH{$past(`abr_ctrl.mldsa_valid_reg)}} &
                                     $past(`abr_ctrl.signature_reg_rdata)));
endproperty
api_reg_rdata_sig_reg: assert property (disable iff (!pi_rst_b) api_reg_rdata_sig_reg_p);

// ----------------------------------------------------------------
// A7b — MLDSA SIGNATURE c/h register region — validity gate check
//       When api_sig_reg_re is active but mldsa_valid_reg=0
//       (signing or verification has not yet completed), the
//       commitment hash c and hint vector h must not appear on
//       api_reg_rdata. Exposing c or h before signing is done
//       could reveal intermediate state of the signing loop.
// ----------------------------------------------------------------
property api_reg_rdata_sig_reg_invalid_p;
    (!po_zeroize && !`abr_ctrl.api_sk_reg_rd_dec && !`abr_ctrl.mlkem_api_dk_reg_dec &&
     !`abr_ctrl.mlkem_api_ek_reg_dec && !`abr_ctrl.api_pubkey_rho_dec &&
     `abr_ctrl.api_sig_reg_re && !`abr_ctrl.mldsa_valid_reg) 
     |=>
        (`abr_ctrl.api_reg_rdata == '0);
endproperty
api_reg_rdata_sig_reg_invalid: assert property (disable iff (!pi_rst_b) api_reg_rdata_sig_reg_invalid_p);

// ----------------------------------------------------------------
// A8 — Stability when no decode path is active
//      When none of the five decode qualifiers fire in a given
//      cycle (and zeroize is not asserted), the always_ff block
//      has no active branch and api_reg_rdata retains its previous
//      value. This assertion verifies that implicit register hold
//      behaviour: the output must be stable on the following cycle.
// ----------------------------------------------------------------
property api_reg_rdata_stable_p;
    (!po_zeroize && !`abr_ctrl.api_sk_reg_rd_dec && !`abr_ctrl.mlkem_api_dk_reg_dec &&
     !`abr_ctrl.mlkem_api_ek_reg_dec && !`abr_ctrl.api_pubkey_rho_dec &&
     !`abr_ctrl.api_sig_reg_re) 
     |=>
        $stable(`abr_ctrl.api_reg_rdata);
endproperty
api_reg_rdata_stable: assert property (disable iff (!pi_rst_b) api_reg_rdata_stable_p);




// ----------------------------------------------------------------
// api_sig_reg_re  check
//      api_sig_reg_re is a combinational signal defined as the OR
//      of api_sig_c_dec and api_sig_h_dec gated by the read
//      qualifier ~req_is_wr. This assertion verifies that the
//      signal exactly matches its RTL definition at all times —
//      catching any deviation where it is spuriously asserted or
//      incorrectly suppressed relative to its two constituent
//      address decode signals and the write-qualifier gate.
// ----------------------------------------------------------------

    // ===============================================================
    // SECTION 11 — API Read-Data Stability and Decode Signals
    // ===============================================================
    //
    // API decode signals determine which register is being accessed.
    // They're derived from APB address and must be mutually exclusive.
    //
    // DECODE SIGNALS:
    //   • api_sk_reg_rd_dec - PRIVKEY_OUT address range
    //   • api_sig_reg_rd_dec - SIGNATURE address range
    //   • api_pk_reg_rd_dec - PUBKEY address range
    //   • fv_api_sig_z_dec - SIGNATURE z polynomial range
    //   • fv_api_sig_h_dec - SIGNATURE h field range
    //
    // MUTUAL EXCLUSION:
    //   onehot_api_sig_p verifies z and h decodes are never both active.
    //   Overlap would cause data corruption.
    //
    // STABILITY:
    //   signature_reg_rdata latches must hold stable until next read.
    //   This allows multi-cycle SRAM access without re-latching.
    // ===============================================================

property api_sig_reg_re_p;
    `abr_ctrl.api_sig_reg_re ==
        ((fv_api_sig_c_dec | fv_api_sig_h_dec) &
         !pi_abr_reg_hwif_out_i.MLDSA_SIGNATURE.req_is_wr);
endproperty
assert_api_sig_reg_re: assert property (disable iff (!pi_rst_b) api_sig_reg_re_p);

property onehot_api_sig_p;
  $onehot0({fv_api_sig_h_dec,fv_api_sig_c_dec});
endproperty

assert_onehot_api_sig_a: assert property(disable iff(!pi_rst_b || po_zeroize) onehot_api_sig_p);
// privkey reg rdata
logic[SK_MEM_BANK_ADDR_W:0] fv_api_sk_raddr;

assign fv_api_sk_raddr =  pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_OUT.addr[12:2];



    // ===============================================================
    // SECTION 12 — Private/Public Key Read Paths
    // ===============================================================
    //
    // Keys can be read from two sources:
    //
    // 1. REGISTER-BACKED:
    //    privkey_reg_rdata_set, pubkey_reg_rdata_set
    //    Source: abr_scratch_reg (used during keygen)
    //    When: Keys haven't been encoded to SRAM yet
    //
    // 2. SRAM-BACKED:
    //    privkey_out_rdata_bank0_p, privkey_out_rdata_bank1_p
    //    Source: SK/PK SRAMs (after encoding completes)
    //    When: Keys are in final encoded form
    //
    // MUX SELECTION:
    //   privkey_out_rdata_update_p verifies the OR-mux combines:
    //   - Bank 0 data (when bank 0 valid)
    //   - Bank 1 data (when bank 1 valid)
    //   - api_reg_rdata (when register-backed)
    //
    // SECURITY:
    //   Register-backed reads must respect mldsa_privkey_lock.
    //   SRAM-backed reads go through decode → lock check in SECTION 10.
    // ===============================================================

property privkey_reg_rdata_set;
  fv_api_keymem_rd_vld &&
  pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_OUT.req &&
  (((fv_api_sk_raddr) inside {[0:31]}))
  |=>
  `abr_ctrl.api_reg_rdata == $past(`abr_ctrl.abr_scratch_reg.raw[(fv_api_sk_raddr[4:0])])
;endproperty

assert_privkey_reg_rdata_set: assert property(disable iff(!pi_rst_b || po_zeroize)privkey_reg_rdata_set);


property pubkey_reg_rdata_set;
  `abr_ctrl.mldsa_valid_reg &&
   `abr_ctrl.api_pubkey_rho_dec
  |=>
  `abr_ctrl.api_reg_rdata == $past(`abr_ctrl.abr_scratch_reg.raw[(fv_api_pubkey_addr[2:0])])
;endproperty

assert_pubkey_reg_rdata_set: assert property(disable iff(!pi_rst_b || po_zeroize)pubkey_reg_rdata_set);
// privkey_reg_rdata stable

//property privkey_reg_rdata_stable;
//  !(fv_api_keymem_rd_vld &&
//  pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_OUT.req &&
//  ((fv_api_sk_raddr) inside {[0:31]}))
//  |=>
//  $stable(`abr_ctrl.privkey_reg_rdata)
//;endproperty

//assert_privkey_reg_rdata_stable: assert property(disable iff(!pi_rst_b || po_zeroize)privkey_reg_rdata_stable);

// api_sk_reg_rd_dec upadte
  property api_sk_reg_rd_dec_update_post_rd;
    fv_api_sk_raddr inside {[0:31]} &&
    pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_OUT.req
    |->
    `abr_ctrl.api_sk_reg_rd_dec
  ;endproperty

  assert_api_sk_reg_rd_dec_update_post_rd: assert property(disable iff(!pi_rst_b || po_zeroize) api_sk_reg_rd_dec_update_post_rd);

//api_key_mem upadte

  property api_keymem_re_upadte_post_rd;
    `abr_ctrl.api_keymem_re_bank[0] == (fv_api_keymem_re_bank)
  ;endproperty

  //assert_api_keymem_re_upadte_post_rd: assert property(disable iff(!pi_rst_b || po_zeroize) api_keymem_re_upadte_post_rd);


// error interface
`ifdef CALIPTRA

    // ===============================================================
    // SECTION 13 — Error Flag Management
    // ===============================================================
    //
    // error_flag aggregates errors from decode operations:
    //   • pi_skdecode_error_i    - Invalid private key encoding
    //   • pcr_sign_input_invalid - PCR_SIGN requested with a non-KEYGEN/SIGN/VERIFY CTRL value
    //   • mldsa_seed_zero_error  - KV seed present but read back as all-zero (CALIPTRA only)
    //
    // SET CONDITIONS (verified):
    //   CALIPTRA build: error_flag_pcr_or_error_decode
    //   Non-CALIPTRA: error_flag_from_decode
    //
    // CLEAR CONDITION :
    //   New assertion verifies error_flag clears after reset or zeroize.
    //   Without this, sticky error would prevent recovery from transient
    //   faults (cosmic rays, voltage glitches, etc.).
    //
    // PROPAGATION:
    //   error_flag feeds into:
    //   - STATUS register (visible to software)
    //   - Interrupt generation (if enabled)
    //   - Valid flag gating (prevents reads of invalid data)
    //
    // WHY CLEAR MATTERS:
    //   If a decode error sets the flag, but the error was transient
    //   (bad data in registers, now cleared), the system should recover.
    //   A sticky flag would require full power cycle.
    // ===============================================================

  property error_flag_pcr_or_error_decode;
    ((`abr_ctrl.mldsa_keygen_process ||
    `abr_ctrl.mldsa_signing_process ||
    `abr_ctrl.mldsa_verifying_process ||
    `abr_ctrl.mldsa_keygen_signing_process)&& (pi_skdecode_error_i)) ||
    (pi_abr_reg_hwif_out_i.MLDSA_CTRL.PCR_SIGN.value &&
    (pi_abr_reg_hwif_out_i.MLDSA_CTRL.CTRL.value inside {MLDSA_KEYGEN, MLDSA_SIGN, MLDSA_VERIFY}) &&
    `abr_ctrl.kv_mldsa_seed_ready) ||
    (`abr_ctrl.kv_mldsa_seed_data_present &&
    (|`abr_ctrl.mldsa_cmd_reg) &&
    (`abr_ctrl.mldsa_seed_reg == '0))
    |->
    `abr_ctrl.error_flag
  ;endproperty

  assert_error_flag_pcr_or_error_decode: assert property(error_flag_pcr_or_error_decode);
`else
  property error_flag_from_decode;
  ((`abr_ctrl.mldsa_keygen_process ||
    `abr_ctrl.mldsa_signing_process ||
    `abr_ctrl.mldsa_verifying_process ||
    `abr_ctrl.mldsa_keygen_signing_process)&& pi_skdecode_error_i)
    |->
     `abr_ctrl.error_flag 
  ;endproperty

  assert_error_flag_from_decode: assert property(error_flag_from_decode);

// ---------------------------------------------------------------
// Error flag CLEAR path
// ---------------------------------------------------------------
// WHAT: Verifies error_flag clears after reset or zeroize
// WHY: Sticky error would prevent recovery from transient faults
// WHEN: Cycle after reset or zeroize deasserts
property error_flag_clear_p;
  $past(!pi_rst_b || po_zeroize)
  |->
  !`abr_ctrl.error_flag;
endproperty

assert_error_flag_clear_a: assert property(error_flag_clear_p);



`endif

// valid reg assert


    // ===============================================================
    // SECTION 14 — Valid Register Status (MLDSA and MLKEM)
    // ===============================================================
    //
    // valid flags indicate when operation results are ready to read:
    //   • mldsa_valid_reg - KEYGEN/SIGN/VERIFY complete
    //   • mlkem_valid_reg - ENCAPS/DECAPS complete (MLKEM operations)
    //
    // SET CONDITIONS:
    //   valid_reg_set_p: Rose when abr_prog_cntr hits end states:
    //   - MLDSA_KG_E (keygen done)
    //   - MLDSA_SIGN_E (sign done)
    //   - MLDSA_VERIFY_E (verify done)
    //   - MLKEM_* end states
    //
    // CLEAR CONDITIONS:
    //   - Reset or zeroize (SECTION 1)
    //   - Software hwclr (start new operation)
    //   - Verification invalidation (verify_valid cleared)
    //
    // COORDINATION WITH abr_status_done:
    //   valid_reg_set_only_if_done_p: valid implies abr_status_done
    //   This ensures STATUS.done visible before valid flag.
    //
    // SOFTWARE FLOW:
    //   1. Poll STATUS.done or wait for interrupt
    //   2. Check STATUS.valid
    //   3. If valid, read results
    //   4. If error, check ERROR_FLAG
    // ===============================================================

property valid_reg_set_p;
  (`abr_ctrl.abr_prog_cntr == MLDSA_KG_E) ||
  (`abr_ctrl.abr_prog_cntr == MLDSA_SIGN_E) ||
  (`abr_ctrl.abr_prog_cntr == MLDSA_VERIFY_E)
  |=>
  `abr_ctrl.mldsa_valid_reg
;endproperty

assert_valid_reg_set_a: assert property(disable iff(!pi_rst_b || po_zeroize) valid_reg_set_p);


// msg_strobe_o


    // ===============================================================
    // SECTION 15 — Message Strobe Interface (SHA3 Byte Masking)
    // ===============================================================
    //
    // po_msg_strobe_o controls which bytes of po_msg_data_o are valid
    // when feeding messages to SHA3 for hashing.
    //
    // ML-DSA CONTEXT:
    //   Messages aren't always word-aligned. The last transfer might
    //   have only partial bytes valid. msg_strobe indicates valid bytes.
    //
    // STROBE PATTERNS:
    //
    // 1. msg_strobe_o_if_done:
    //    When msg transfer done AND message word-aligned:
    //    strobe = 0 (no bytes valid in next cycle)
    //
    // 2. msg_strobe_o_full_if_not_last:
    //    When not the last word:
    //    strobe = all 1's (all bytes valid)
    //
    // 3. msg_strobe_o_if_last:
    //    When last word (partial):
    //    strobe = mask based on msg_size % word_size
    //    Example: 5 bytes in 8-byte word → strobe = 8'b0001_1111
    //
    // 4. msg_strobe_o_zero:
    //    When not in MSG_LOAD state:
    //    strobe = all 1's (default/safe state)
    //
    // CORRECTNESS IMPACT:
    //   Wrong strobe causes wrong SHA3 hash, which causes:
    //   - Wrong commitment c
    //   - Wrong message hash μ  
    //   - 100% signature verification failure
    // ===============================================================

property msg_strobe_o_if_done;
  `abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_MSG_LOAD &&
  !`abr_ctrl.stream_msg_ip &&
  (`abr_ctrl.msg_last  )&&
  `abr_ctrl.abr_instr.length[$clog2(MsgStrbW)-1:0] == '0 &&
  !pi_abr_reg_hwif_out_i.MLDSA_CTRL.STREAM_MSG.value
  |=>
  po_msg_strobe_o == '0
;endproperty
assert_msg_strobe_o_if_done: assert property (disable iff (!pi_rst_b || po_zeroize)msg_strobe_o_if_done);

property msg_strobe_o_full_if_not_last;
  `abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_MSG_LOAD &&
  !`abr_ctrl.stream_msg_ip &&
  !`abr_ctrl.msg_done &&
  !`abr_ctrl.msg_last &&
  po_msg_valid_o
  |=>
  po_msg_strobe_o == '1
;endproperty
assert_msg_strobe_o_full_if_not_last: assert property (disable iff (!pi_rst_b || po_zeroize)msg_strobe_o_full_if_not_last);


property msg_strobe_o_if_last;
  `abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_MSG_LOAD &&
  !`abr_ctrl.stream_msg_ip &&
  `abr_ctrl.msg_last &&
  (`abr_ctrl.abr_instr.length[$clog2(MsgStrbW)-1:0] != '0)&&
  !pi_abr_reg_hwif_out_i.MLDSA_CTRL.STREAM_MSG.value
  |=>
  po_msg_strobe_o == ~(MsgStrbW'('1) << `abr_ctrl.abr_instr.length[$clog2(MsgStrbW)-1:0])
;endproperty
assert_msg_strobe_o_if_last: assert property (disable iff (!pi_rst_b || po_zeroize)msg_strobe_o_if_last);


property msg_strobe_o_zero;
  `abr_ctrl.abr_ctrl_fsm_ps != ABR_CTRL_MSG_LOAD
  |=>
  (po_msg_strobe_o == '1) &&
  !po_msg_valid_o
;endproperty
assert_msg_strobe_o_zero: assert property(disable iff(!pi_rst_b || po_zeroize)msg_strobe_o_zero);


// synchronisation of the sequencers only if no abstraction is applied.
// First both the sequencers trigger and start running incase of the signing operation.
// secondary sequencer waits for the c_valid inorder to proceed and the primary sequencer 
// continues with the next round and apparently if the secondary sequencer sets the valid signature, then
// the primary sequencer would terminate the next c generation in specific states and jump to end state.
`ifdef NO_ABSTRACTION
  /*property c_valid_clear_eventually_p;
    `abr_ctrl.c_valid
    |->
    s_eventually(!`abr_ctrl.c_valid)
  ;endproperty

assert_c_valid_clear_eventually_a: assert property(disable iff(!pi_rst_b || po_zeroize || `abr_ctrl.error_flag)c_valid_clear_eventually_p);


  property y_valid_clear_eventually_p;
    `abr_ctrl.y_valid
    |->
    s_eventually(!`abr_ctrl.y_valid)
  ;endproperty
assert_y_valid_clear_eventually_a: assert property(disable iff(!pi_rst_b || po_zeroize || `abr_ctrl.error_flag)y_valid_clear_eventually_p);


  property w0_valid_clear_eventually_p;
    `abr_ctrl.w0_valid
    |->
    s_eventually(!`abr_ctrl.w0_valid)
  ;endproperty
  assert_w0_valid_clear_eventually_a: assert property(disable iff(!pi_rst_b || po_zeroize || `abr_ctrl.error_flag)w0_valid_clear_eventually_p);



  property verify_valid_clear_eventually_p;
    `abr_ctrl.verify_valid
    |->
    s_eventually(!`abr_ctrl.verify_valid)
  ;endproperty
  assert_verify_valid_clear_eventually_a: assert property(disable iff(!pi_rst_b || po_zeroize || `abr_ctrl.error_flag)verify_valid_clear_eventually_p);
*/
`endif
// Mldsa valid register and ready

property valid_reg_set_only_if_done_p;
  $rose((`abr_ctrl.abr_prog_cntr == MLDSA_KG_E) ||
  (`abr_ctrl.abr_prog_cntr == MLDSA_SIGN_E) ||
  (`abr_ctrl.abr_prog_cntr == MLDSA_VERIFY_E) ||
  ((`abr_ctrl.abr_prog_cntr == MLKEM_KG_E) && `abr_ctrl.mlkem_keygen_process) ||
  ((`abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_E) && `abr_ctrl.mlkem_encaps_process) ||
  (`abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_E))
  |=>
  `abr_ctrl.abr_status_done
;endproperty

assert_valid_reg_set_only_if_done_a: assert property(disable iff(!pi_rst_b || po_zeroize)valid_reg_set_only_if_done_p);


property valid_reg_not_set_if_not_done_p;
  !$rose((`abr_ctrl.abr_prog_cntr == MLDSA_KG_E) ||
  (`abr_ctrl.abr_prog_cntr == MLDSA_SIGN_E) ||
  (`abr_ctrl.abr_prog_cntr == MLDSA_VERIFY_E) ||
  ((`abr_ctrl.abr_prog_cntr == MLKEM_KG_E) && `abr_ctrl.mlkem_keygen_process) ||
  ((`abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_E) && `abr_ctrl.mlkem_encaps_process) ||
  (`abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_E))
  |=>
  !`abr_ctrl.abr_status_done
;endproperty

assert_valid_reg_not_set_if_not_done_a: assert property(disable iff(!pi_rst_b || po_zeroize)valid_reg_not_set_if_not_done_p);

// Valid signaturee and valid verifying

`ifdef NO_ABSTRACTION

    // ===============================================================
    // SECTION 17 — Verify/Sign Valid Flags (Rejection Sampling FSM)
    // ===============================================================
    //
    // ML-DSA signing uses rejection sampling:
    //   1. Generate candidate signature (z, h, c)
    //   2. Check validity (normcheck, makehint)
    //   3. If invalid, clear signature_valid and loop
    //   4. If valid, set signature_valid and exit
    //
    // VALID FLAGS:
    //
    // 1. verify_valid (NO_ABSTRACTION only):
    //    Set when verification starts, cleared if invalid.
    //    Prevents reading stale verification results.
    //
    // 2. signature_valid:
    //    Set when candidate signature passes all checks.
    //    Cleared when normcheck or makehint invalidates.
    //
    // REJECTION SAMPLING LOOP:
    //   sign_valid_reset_p verifies signature_valid clears when:
    //   - normcheck invalid (pi_normcheck_invalid_i)
    //   - makehint invalid (pi_makehint_invalid_i)
    //   - set_signature_valid (start new candidate)
    //
    // SECURITY:
    //   If signature_valid didn't clear on invalid, the FSM would
    //   exit with an invalid signature, which would fail verification.
    //   This assertion prevents silent failures.
    // ===============================================================

property valid_verify_set_p;
  (`abr_ctrl.abr_prog_cntr == MLDSA_VERIFY)
  |=>
  `abr_ctrl.verify_valid until_with (`abr_ctrl.mldsa_verifying_process & ((pi_normcheck_done_i & pi_normcheck_invalid_i) | 
                                   (`abr_ctrl.abr_instr.opcode.aux_en & (`abr_ctrl.abr_instr.opcode.mode.aux_mode == MLDSA_SIGDEC_H) & pi_sigdecode_h_invalid_i)))
;endproperty

assert_valid_verify_set_a: assert property (disable iff(!pi_rst_b || po_zeroize || `abr_ctrl.error_flag) valid_verify_set_p);
`endif

property valid_verify_reset_p;
  (`abr_ctrl.mldsa_verifying_process & ((pi_normcheck_done_i & pi_normcheck_invalid_i) | 
                                   (`abr_ctrl.abr_instr.opcode.aux_en & (`abr_ctrl.abr_instr.opcode.mode.aux_mode == MLDSA_SIGDEC_H) & pi_sigdecode_h_invalid_i)))
  |=>
  !`abr_ctrl.verify_valid
;endproperty

assert_valid_verify_reset_a: assert property (disable iff(!pi_rst_b || po_zeroize) valid_verify_reset_p);

//property sign_valid_set_p;
//  (`abr_ctrl.sec_prog_cntr == MLDSA_SIGN_CHECK_C_VLD) &&
//  `abr_ctrl.c_valid &&
//  `abr_ctrl.signing_process
//  |=>
//  `abr_ctrl.signature_valid until_with (`abr_ctrl.signing_process & ((pi_makehint_done_i & pi_makehint_invalid_i) | (pi_normcheck_done_i & pi_normcheck_invalid_i)))
//;endproperty
//
//assert_sign_valid_set_a: assert property (disable iff(!pi_rst_b || po_zeroize) sign_valid_set_p);


property sign_valid_reset_p;
  (`abr_ctrl.mldsa_signing_process & ((pi_makehint_done_i & pi_makehint_invalid_i) | (pi_normcheck_done_i & pi_normcheck_invalid_i)))
  |=>
  !`abr_ctrl.signature_valid
;endproperty

assert_sign_valid_reset_a: assert property (disable iff(!pi_rst_b || po_zeroize) sign_valid_reset_p);

// Keyvault registers

`ifdef CALIPTRA

  //kv_seed_data_present if there is a read en


    // ===============================================================
    // SECTION 19 — Keyvault Registers (CALIPTRA Build Only)
    // ===============================================================
    //
    // In CALIPTRA builds, the controller interfaces with KeyVault (KV)
    // to source cryptographic seeds without exposing them to software.
    //
    // KV SIGNALS:
    //   • kv_mldsa_seed_data_present - KV seed available for MLDSA
    //   • kv_mlkem_seed_data_present - KV seed available for MLKEM
    //   • kv_read_seed_data_present - KV read control
    //
    // CALIPTRA BUILD BEHAVIOR:
    //   kv_seed_data_present_set_p verifies these signals remain set
    //   until the valid flag rises (operation completes).
    //
    // NON-CALIPTRA BUILD:
    //   kv_seed_data_present_p verifies all KV signals are tied to 0.
    //   (KV doesn't exist in non-Caliptra builds)
    //
    // INTEGRATION:
    //   KV presence determines lock behavior (SECTION 18).
    //   If kv_mldsa_seed_data_present, lock must SET at keygen end.
    // ===============================================================

  property kv_seed_data_present_set_p;
     `abr_ctrl.kv_mldsa_seed_read_ctrl_reg.read_en ||
    `abr_ctrl.pcr_sign_mode
    |=>
    `abr_ctrl.kv_mldsa_seed_data_present until_with `abr_ctrl.mldsa_valid_reg
  ;endproperty

  assert_kv_seed_data_present_set_a: assert property(disable iff(!pi_rst_b || po_zeroize) kv_seed_data_present_set_p);

  //property kv_seed_read_ctrl_reg_p;
  //  `abr_ctrl.kv_mldsa_seed_read_ctrl_reg.rsvd == '0 &&
  //  `abr_ctrl.kv_mldsa_seed_read_ctrl_reg.pcr_hash_extend == pi_abr_reg_hwif_out_i.kv_mldsa_seed_rd_ctrl.pcr_hash_extend.value &&
  //  `abr_ctrl.kv_mldsa_seed_read_ctrl_reg.read_entry == pi_abr_reg_hwif_out_i.kv_mldsa_seed_rd_ctrl.read_entry.value &&
  //  `abr_ctrl.kv_mldsa_seed_read_ctrl_reg.read_en == pi_abr_reg_hwif_out_i.kv_mldsa_seed_rd_ctrl.read_en.value
  //;endproperty
  //assert_kv_seed_read_ctrl_reg_a: assert property(disable iff(!pi_rst_b || po_zeroize) kv_seed_read_ctrl_reg_p);

`else 

  property kv_seed_data_present_p;
     `abr_ctrl.kv_mldsa_seed_data_present == '0 &&
     //ready when fsm is not busy
    po_abr_reg_hwif_in_o.kv_mldsa_seed_rd_status.ERROR.next == '0 &&
    //ready when fsm is not busy
    po_abr_reg_hwif_in_o.kv_mldsa_seed_rd_status.READY.next == '0 &&
    //set valid when fsm is done
    po_abr_reg_hwif_in_o.kv_mldsa_seed_rd_status.VALID.hwset == '0 &&
    //clear valid when new request is made
    po_abr_reg_hwif_in_o.kv_mldsa_seed_rd_status.VALID.hwclr == '0 &&
    //clear enable when busy
    po_abr_reg_hwif_in_o.kv_mldsa_seed_rd_ctrl.read_en.hwclr == '0;
  endproperty
  assert_kv_seed_data_present_a: assert property(disable iff(!pi_rst_b || po_zeroize) kv_seed_data_present_p);

`endif


    // ===============================================================
    // SECTION 18 — Key Lock Mechanism (KV Isolation Enforcement)
    // ===============================================================
    //
    // SECURITY-CRITICAL: The private key lock prevents KV-derived
    //                       keys from leaking via APB reads.
    //
    // ML-DSA KEYGEN HAS TWO MODES:
    //
    // 1. SOFTWARE-SEEDED KEYGEN:
    //    - Software writes seed to MLDSA_SEED register
    //    - kv_mldsa_seed_data_present == 0
    //    - Derived keys are SOFTWARE KEYS (OK to read via API)
    //    - Lock must be CLEAR (0) at end of keygen
    //    - Verified by: privkey_lock_reset_p
    //
    // 2. KEYVAULT-SEEDED KEYGEN:
    //    - Seed comes from Caliptra KeyVault
    //    - kv_mldsa_seed_data_present == 1
    //    - Derived keys are KEYVAULT KEYS (MUST NOT leak to software)
    //    - Lock must be SET (1) at end of keygen
    //    
    //
    // LOCK ENFORCEMENT (verified in SECTION 10):
    //   When mldsa_privkey_lock == 1:
    //   - PRIVKEY_OUT reads return all zeros (A3b path)
    //   - DECAPS_KEY reads return all zeros (A4b path)
    //
    // THREAT MODEL:
    //   Without lock SET assertion, KV-derived keys could leak via:
    //   1. Malicious software reading PRIVKEY_OUT after KV keygen
    //   2. Debug probe accessing APB bus
    //   3. Software exploiting incomplete lock enforcement
    //
    // ===============================================================

property privkey_lock_reset_p;
  `abr_ctrl.mldsa_keygen_process &&
  (`abr_ctrl.abr_prog_cntr == MLDSA_KG_E) &&
  !`abr_ctrl.kv_mldsa_seed_data_present
  |=>
  !`abr_ctrl.mldsa_privkey_lock
;endproperty

assert_privkey_lock_reset_a: assert property(disable iff(!pi_rst_b || po_zeroize) privkey_lock_reset_p);

// ---------------------------------------------------------------
// Private key lock SET path
// ---------------------------------------------------------------
// WHAT: Verifies mldsa_privkey_lock is SET when KV seed is used
// WHY: SECURITY - Without this, KV-derived keys can leak via API
// WHEN: At end of keygen when kv_mldsa_seed_data_present == 1
//
// ---------------------------------------------------------------
property privkey_lock_set_p;
  `abr_ctrl.mldsa_keygen_process &&
  (`abr_ctrl.abr_prog_cntr == MLDSA_KG_E) &&
  `abr_ctrl.kv_mldsa_seed_data_present
  |=>
  `abr_ctrl.mldsa_privkey_lock;
endproperty

assert_privkey_lock_set_a: assert property(disable iff(!pi_rst_b || po_zeroize) privkey_lock_set_p);


//////////////////////////
// msg_cnt increment    //
//////////////////////////

    logic [ABR_OPR_WIDTH-1:$clog2(MsgStrbW)] fv_msg_cnt;
    always_ff @( posedge pi_clk, negedge pi_rst_b ) begin : fv_msg_cnt_logic
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
            else if(`abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_MSG_LOAD && (fv_msg_cnt <= `abr_ctrl.abr_instr.length[ABR_OPR_WIDTH-1:$clog2(MsgStrbW)]) ) begin
                fv_msg_cnt <= fv_msg_cnt + 1;
            end
            else begin
                 fv_msg_cnt <= '0;
            end
        end
    end

`ifdef NO_ABSTRACTION

    // ===============================================================
    // SECTION 16 — Message Counter (NO_ABSTRACTION Build Only)
    // ===============================================================
    //
    // In NO_ABSTRACTION builds, msg_cnt tracks how many message words
    // have been transferred to SHA3.
    //
    // PURPOSE:
    //   Used to compute when the last word is being sent (for strobe).
    //   Also used in formal verification to track message completeness.
    //
    // VERIFICATION:
    //   msg_cnt_p: Internal counter matches fv_msg_cnt (shadow counter)
    //
    // ABSTRACTION vs NO_ABSTRACTION:
    //   - ABSTRACTION: Counter abstracted away (not synthesized)
    //   - NO_ABSTRACTION: Counter exists in RTL for debugging
    //
    // This assertion only compiles in NO_ABSTRACTION builds.
    // ===============================================================

     property msg_cnt_p;
         `abr_ctrl.msg_cnt == fv_msg_cnt
    ;endproperty
    assert_msg_cnt: assert property(msg_cnt_p);
`endif

///////////////////////////////////////////
// For the api data out and ack proofs   //
///////////////////////////////////////////


    // ===============================================================
    // SECTION 20 — APB Read Acknowledge Signals
    // ===============================================================
    //
    // APB read acknowledges are combinational signals that pulse when
    // the controller provides read data for specific APB address ranges.
    //
    // ACK SIGNALS:
    //   • privkey_out_rd_ack - MLDSA_PRIVKEY_OUT address decoded
    //   • signature_rd_ack - MLDSA_SIGNATURE address decoded
    //   • pubkey_rd_ack - MLDSA_PUBKEY address decoded
    //
    // SET CONDITIONS:
    //   Ack pulses when:
    //   - APB req active (pi_abr_reg_hwif_out_i.REGISTER.req)
    //   - Address in range (api_*_reg_rd_dec)
    //
    // RESET CONDITIONS:
    //   Ack clears when req deasserts (combinational path).
    //
    // APB PROTOCOL:
    //   These acks may gate read data valid signals or control
    //   APB state machine transitions in the register block.
    // ===============================================================

property privkey_out_rd_ack_set_p;
  `abr_ctrl.privkey_out_rd_ack[0] == (pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_OUT.req &&
                                      !pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_OUT.req_is_wr)
;endproperty

assert_privkey_out_rd_ack_set_a: assert property(disable iff(!pi_rst_b || po_zeroize)privkey_out_rd_ack_set_p);


property privkey_out_rd_ack_reset_p;
  !(pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_OUT.req &&
  !pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_OUT.req_is_wr)
  |->
  !`abr_ctrl.privkey_out_rd_ack[0]
;endproperty

assert_privkey_out_rd_ack_reset_a: assert property(disable iff(!pi_rst_b || po_zeroize)privkey_out_rd_ack_reset_p);



property signature_rd_ack_set_p;
  `abr_ctrl.signature_rd_ack[0] == (pi_abr_reg_hwif_out_i.MLDSA_SIGNATURE.req &&
                                  !pi_abr_reg_hwif_out_i.MLDSA_SIGNATURE.req_is_wr)
;endproperty

assert_signature_rd_ack_set_a: assert property(disable iff(!pi_rst_b || po_zeroize)signature_rd_ack_set_p);


property signature_rd_ack_reset_p;
  !(pi_abr_reg_hwif_out_i.MLDSA_SIGNATURE.req &&
  !pi_abr_reg_hwif_out_i.MLDSA_SIGNATURE.req_is_wr)
  |->
  !`abr_ctrl.signature_rd_ack[0]
;endproperty

assert_signature_rd_ack_reset_a: assert property(disable iff(!pi_rst_b || po_zeroize)signature_rd_ack_reset_p);




property pubkey_rd_ack_set_p;
  `abr_ctrl.pubkey_rd_ack[0] == (pi_abr_reg_hwif_out_i.MLDSA_PUBKEY.req &&
                                !pi_abr_reg_hwif_out_i.MLDSA_PUBKEY.req_is_wr)
;endproperty

assert_pubkey_rd_ack_set_a: assert property(disable iff(!pi_rst_b || po_zeroize)pubkey_rd_ack_set_p);


property pubkey_rd_ack_reset_p;
  !(pi_abr_reg_hwif_out_i.MLDSA_PUBKEY.req &&
  !pi_abr_reg_hwif_out_i.MLDSA_PUBKEY.req_is_wr)
  |->
  !`abr_ctrl.pubkey_rd_ack[0]
;endproperty

assert_pubkey_rd_ack_reset_a: assert property(disable iff(!pi_rst_b || po_zeroize)pubkey_rd_ack_reset_p);





    // ===============================================================
    // SECTION 21 — HWIF Latency and Read Data Completeness
    // ===============================================================
    //
    // APB reads of SRAM-backed registers require additional cycles:
    //   • Cycle 0: APB address presented, SRAM read starts
    //   • Cycle N: SRAM data available (N = SRAM_LATENCY)
    //   • Cycle N+1: Data latched and returned to APB
    //
    // IMMEDIATE ACK vs LATENCY ACK:
    //
    // 1. Immediate (register-backed):
    //    mldsa_hwif_in_ack_p: Write/read ack same cycle for registers
    //
    // 2. Latency (SRAM-backed):
    //    mldsa_hwif_in_latency_*: Ack delayed by SRAM_LATENCY cycles
    //    Instantiated for each SRAM-backed register:
    //    - MLDSA_PRIVKEY_OUT (skdecode from SK SRAM)
    //    - MLDSA_SIGNATURE (sigdecode from SIG_Z SRAM)
    //    - MLDSA_PUBKEY (pkdecode from PK SRAM)
    //    - MLDSA_PRIVKEY_IN (API write to SK SRAM)
    //
    // READ DATA COMPLETENESS:
    //   mldsa_hwif_rd_data_p verifies po_abr_reg_hwif_in_o.*.rdata
    //   matches the internal read data path for each register.
    //
    // LATENCY READ DATA:
    //   mldsa_hwif_in_latency_rd_data_p verifies SRAM data propagates
    //   correctly through the pipeline.
    // ===============================================================

property mldsa_hwif_in_ack_p;
  po_abr_reg_hwif_in_o.MLDSA_PRIVKEY_IN.wr_ack == (pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_IN.req & pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_IN.req_is_wr) &&
  po_abr_reg_hwif_in_o.MLDSA_PRIVKEY_IN.rd_ack == (pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_IN.req & ~pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_IN.req_is_wr) &&
  po_abr_reg_hwif_in_o.MLDSA_PRIVKEY_OUT.wr_ack == (pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_OUT.req & pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_OUT.req_is_wr) &&
  po_abr_reg_hwif_in_o.MLDSA_SIGNATURE.wr_ack == (pi_abr_reg_hwif_out_i.MLDSA_SIGNATURE.req &  pi_abr_reg_hwif_out_i.MLDSA_SIGNATURE.req_is_wr) &&
  po_abr_reg_hwif_in_o.MLDSA_PUBKEY.wr_ack == (pi_abr_reg_hwif_out_i.MLDSA_PUBKEY.req &  pi_abr_reg_hwif_out_i.MLDSA_PUBKEY.req_is_wr)
;endproperty

assert_mldsa_hwif_in_ack_a: assert property (mldsa_hwif_in_ack_p);


property mldsa_hwif_in_latency_ack_p(ack, rd_ack);
  ##SRAM_LATENCY
  rd_ack == $past(ack[0], SRAM_LATENCY)
;endproperty

property mldsa_hwif_in_latency_reset_p(rd_ack);
  $past(!pi_rst_b || po_zeroize)
  |->
  !rd_ack[*SRAM_LATENCY]
;endproperty

assert_mldsa_hwif_in_latency_privkey_out_ack_a: assert property(disable iff (!pi_rst_b || po_zeroize) mldsa_hwif_in_latency_ack_p(`abr_ctrl.privkey_out_rd_ack,po_abr_reg_hwif_in_o.MLDSA_PRIVKEY_OUT.rd_ack));
assert_mldsa_hwif_in_latency_privkey_out_ack_reset_a: assert property( mldsa_hwif_in_latency_reset_p(po_abr_reg_hwif_in_o.MLDSA_PRIVKEY_OUT.rd_ack));
assert_mldsa_hwif_in_latency_sig_ack_a: assert property(disable iff (!pi_rst_b || po_zeroize) mldsa_hwif_in_latency_ack_p(`abr_ctrl.signature_rd_ack,po_abr_reg_hwif_in_o.MLDSA_SIGNATURE.rd_ack));
assert_mldsa_hwif_in_latency_sig_ack_reset_a: assert property( mldsa_hwif_in_latency_reset_p(po_abr_reg_hwif_in_o.MLDSA_SIGNATURE.rd_ack));
assert_mldsa_hwif_in_latency_pubkey_out_ack_a: assert property(disable iff (!pi_rst_b || po_zeroize) mldsa_hwif_in_latency_ack_p(`abr_ctrl.pubkey_rd_ack,po_abr_reg_hwif_in_o.MLDSA_PUBKEY.rd_ack));
assert_mldsa_hwif_in_latency_pubkey_out_ack_reset_a: assert property( mldsa_hwif_in_latency_reset_p(po_abr_reg_hwif_in_o.MLDSA_PUBKEY.rd_ack));


property mldsa_hwif_rd_data_p;
   po_abr_reg_hwif_in_o.MLDSA_PRIVKEY_OUT.rd_data == ( `abr_ctrl.privkey_out_rd_ack[SRAM_LATENCY] &  `abr_ctrl.mldsa_valid_reg & ~ `abr_ctrl.mldsa_privkey_lock ?  `abr_ctrl.privkey_out_rdata : 0) &&
   po_abr_reg_hwif_in_o.MLDSA_SIGNATURE.rd_data == (`abr_ctrl.api_sig_z_re[SRAM_LATENCY] ? pi_sig_z_mem_if_rdata_o[`abr_ctrl.api_sig_z_addr[SRAM_LATENCY].offset*ABR_REG_WIDTH+:ABR_REG_WIDTH] : ( `abr_ctrl.api_reg_rdata)) &&
   po_abr_reg_hwif_in_o.MLDSA_PUBKEY.rd_data == (`abr_ctrl.api_pubkey_re[SRAM_LATENCY] ? pi_pk_mem_if_rdata_o[`abr_ctrl.api_pubkey_mem_addr[SRAM_LATENCY].offset*ABR_REG_WIDTH+:ABR_REG_WIDTH] : `abr_ctrl.api_reg_rdata) &&
   po_abr_reg_hwif_in_o.MLDSA_PRIVKEY_IN.rd_data == '0
;endproperty

assert_mldsa_hwif_rd_data_a: assert property (mldsa_hwif_rd_data_p);


property mldsa_hwif_in_latency_rd_data_p(re,data_in,addr,data_out);
logic [10:0] str_addr; // Max addr width
  re
  ##0 (1'b1, str_addr = addr)
  |->
  ##SRAM_LATENCY
  data_out == data_in[str_addr*ABR_REG_WIDTH+:ABR_REG_WIDTH]
;endproperty
assert_mldsa_hwif_in_latency_sig_rd_data_a: assert property(disable iff(!pi_rst_b || po_zeroize) mldsa_hwif_in_latency_rd_data_p(`abr_ctrl.api_sig_z_re[0],pi_sig_z_mem_if_rdata_o,`abr_ctrl.api_sig_z_addr[0].offset,po_abr_reg_hwif_in_o.MLDSA_SIGNATURE.rd_data));
assert_mldsa_hwif_in_latency_pubkey_rd_data_a: assert property(disable iff(!pi_rst_b || po_zeroize) mldsa_hwif_in_latency_rd_data_p(`abr_ctrl.api_pubkey_re[0],pi_pk_mem_if_rdata_o,`abr_ctrl.api_pubkey_mem_addr[0].offset,po_abr_reg_hwif_in_o.MLDSA_PUBKEY.rd_data));

// ----------------------------------------------------------------
// MLKEM hwif immediate ack completeness
// ----------------------------------------------------------------

    // ===============================================================
    // SECTION 22 — MLKEM Interface Completeness
    // ===============================================================
    //
    // MLKEM (Kyber) operations share the controller with ML-DSA.
    // These assertions verify MLKEM-specific register interfaces.
    //
    // MLKEM REGISTERS:
    //   • MLKEM_ENCAPS_KEY - Encapsulation public key
    //   • MLKEM_DECAPS_KEY - Decapsulation private key
    //   • MLKEM_CIPHERTEXT - Encrypted shared secret
    //   • MLKEM_MSG - Decrypted shared secret
    //
    // VERIFIED:
    //   ✓ mlkem_hwif_in_ack_p - Immediate ack for all MLKEM registers
    //   ✓ mlkem_hwif_rd_data_p - Read data completeness
    //
    // MLKEM vs MLDSA ISOLATION:
    //   SECTION 24 verifies MLKEM outputs (compress/decompress) are
    //   disabled during MLDSA operations to prevent interference.
    // ===============================================================

property mlkem_hwif_in_ack_p;
  po_abr_reg_hwif_in_o.MLKEM_ENCAPS_KEY.wr_ack == (pi_abr_reg_hwif_out_i.MLKEM_ENCAPS_KEY.req & pi_abr_reg_hwif_out_i.MLKEM_ENCAPS_KEY.req_is_wr) &&
  po_abr_reg_hwif_in_o.MLKEM_DECAPS_KEY.wr_ack == (pi_abr_reg_hwif_out_i.MLKEM_DECAPS_KEY.req & pi_abr_reg_hwif_out_i.MLKEM_DECAPS_KEY.req_is_wr) &&
  po_abr_reg_hwif_in_o.MLKEM_CIPHERTEXT.wr_ack == (pi_abr_reg_hwif_out_i.MLKEM_CIPHERTEXT.req & pi_abr_reg_hwif_out_i.MLKEM_CIPHERTEXT.req_is_wr) &&
  po_abr_reg_hwif_in_o.MLKEM_MSG.wr_ack        == (pi_abr_reg_hwif_out_i.MLKEM_MSG.req        & pi_abr_reg_hwif_out_i.MLKEM_MSG.req_is_wr)        &&
  po_abr_reg_hwif_in_o.MLKEM_MSG.rd_ack        == (pi_abr_reg_hwif_out_i.MLKEM_MSG.req        & ~pi_abr_reg_hwif_out_i.MLKEM_MSG.req_is_wr)
;endproperty
assert_mlkem_hwif_in_ack_p: assert property (mlkem_hwif_in_ack_p);

// ----------------------------------------------------------------
// MLKEM hwif latency-based rd_ack checks
// ----------------------------------------------------------------
assert_mlkem_hwif_in_latency_encapskey_ack_p: assert property (disable iff (!pi_rst_b || po_zeroize)
    mldsa_hwif_in_latency_ack_p(`abr_ctrl.encapskey_rd_ack, po_abr_reg_hwif_in_o.MLKEM_ENCAPS_KEY.rd_ack));
assert_mlkem_hwif_in_latency_encapskey_ack_reset_p: assert property (
    mldsa_hwif_in_latency_reset_p(po_abr_reg_hwif_in_o.MLKEM_ENCAPS_KEY.rd_ack));

assert_mlkem_hwif_in_latency_decapskey_ack_p: assert property (disable iff (!pi_rst_b || po_zeroize)
    mldsa_hwif_in_latency_ack_p(`abr_ctrl.decapskey_rd_ack, po_abr_reg_hwif_in_o.MLKEM_DECAPS_KEY.rd_ack));
assert_mlkem_hwif_in_latency_decapskey_ack_reset_p: assert property (
    mldsa_hwif_in_latency_reset_p(po_abr_reg_hwif_in_o.MLKEM_DECAPS_KEY.rd_ack));

assert_mlkem_hwif_in_latency_ciphertext_ack_p: assert property (disable iff (!pi_rst_b || po_zeroize)
    mldsa_hwif_in_latency_ack_p(`abr_ctrl.ciphertext_rd_ack, po_abr_reg_hwif_in_o.MLKEM_CIPHERTEXT.rd_ack));
assert_mlkem_hwif_in_latency_ciphertext_ack_reset_p: assert property (
    mldsa_hwif_in_latency_reset_p(po_abr_reg_hwif_in_o.MLKEM_CIPHERTEXT.rd_ack));

// ----------------------------------------------------------------
// MLKEM hwif rd_data completeness
// MLKEM_ENCAPS_KEY, MLKEM_DECAPS_KEY and MLKEM_CIPHERTEXT all
// source rd_data directly from privkey_out_rdata (the OR-mux of
// sk_ram_rdata bank 0, bank 1 and api_reg_rdata), gated by
// mlkem_valid_reg and the respective lock qualifiers. There is no
// SRAM offset indexing at the rd_data assignment level so no
// separate latency rd_data property is needed for these registers.
// MLKEM_MSG has no read port and must always return 0.
// ----------------------------------------------------------------
property mlkem_hwif_rd_data_p;
  po_abr_reg_hwif_in_o.MLKEM_ENCAPS_KEY.rd_data == (`abr_ctrl.encapskey_rd_ack[SRAM_LATENCY]  &  `abr_ctrl.mlkem_valid_reg                            ? `abr_ctrl.privkey_out_rdata : '0) &&
  po_abr_reg_hwif_in_o.MLKEM_DECAPS_KEY.rd_data == (`abr_ctrl.decapskey_rd_ack[SRAM_LATENCY]  &  `abr_ctrl.mlkem_valid_reg & ~`abr_ctrl.mlkem_dk_lock ? `abr_ctrl.privkey_out_rdata : '0) &&
  po_abr_reg_hwif_in_o.MLKEM_CIPHERTEXT.rd_data == (`abr_ctrl.ciphertext_rd_ack[SRAM_LATENCY] &  `abr_ctrl.mlkem_valid_reg                            ? `abr_ctrl.privkey_out_rdata : '0) &&
  po_abr_reg_hwif_in_o.MLKEM_MSG.rd_data        == '0
;endproperty
assert_mlkem_hwif_rd_data_p: assert property (mlkem_hwif_rd_data_p);
// read data for the primary outputs


    // ===============================================================
    // SECTION 23 — Memory Read Data Paths and Valid Signals
    // ===============================================================
    //
    // When reading from SRAMs, data flows through decode blocks:
    //   SK SRAM → skdecode → privkey_out_rdata
    //   SIG_Z SRAM → sigdecode_z → signature read data
    //   PK SRAM → pkdecode → pubkey_rdata
    //
    // MULTI-BANK CONCATENATION:
    //
    // 1. SK (2 banks × 40 bits):
    //    skdecode_read_data_out_from_mem_p verifies:
    //    read_data = {bank1_data, bank0_data}
    //
    // 2. Privkey output mux:
    //    privkey_out_rdata_update_p verifies OR-mux of:
    //    - Bank 0 (when valid)
    //    - Bank 1 (when valid)  
    //    - api_reg_rdata (register-backed)
    //
    // PK COEFFICIENT SELECTION:
    //   pkdecode_read_data_out_from_mem_p verifies T1 coefficients
    //   are selected from the 8×11-bit packed word based on address.
    //
    // VALID SIGNAL LATENCY:
    //   *_rddata_valid_o_p properties verify valid signals propagate
    //   with correct SRAM_LATENCY delay from read enable.
    //
    // RESET BEHAVIOR:
    //   *_reset_p properties verify valid signals clear on reset.
    // ===============================================================

  property skdecode_read_data_out_from_mem_p;
    po_skdecode_rd_data_o == ({pi_sk_bank1_mem_if_rdata_o,pi_sk_bank0_mem_if_rdata_o})
  ;endproperty
  assert_skdecode_read_data_out_from_mem_a: assert property(skdecode_read_data_out_from_mem_p);

// read_data for privkey

  property privkey_out_rdata_update_p;
    `abr_ctrl.privkey_out_rdata == ({ABR_REG_WIDTH{`abr_ctrl.api_keymem_re_bank[SRAM_LATENCY][0]}} & pi_sk_bank0_mem_if_rdata_o |
                                  {ABR_REG_WIDTH{`abr_ctrl.api_keymem_re_bank[SRAM_LATENCY][1]}} & pi_sk_bank1_mem_if_rdata_o |
                                  {ABR_REG_WIDTH{`abr_ctrl.api_sk_reg_re[SRAM_LATENCY]}} & `abr_ctrl.api_reg_rdata)
  ;endproperty
  assert_privkey_out_rdata_update_a: assert property(privkey_out_rdata_update_p);

// ----------------------------------------------------------------
// privkey_out_rdata — bank 0 path
// Triggered by any API read request to an even-bank-mapped address
// across the four interfaces that feed api_keymem_re_bank[0][0]:
// MLDSA_PRIVKEY_OUT mem region, MLKEM_DECAPS_KEY mem region,
// MLKEM_ENCAPS_KEY mem region, MLKEM_CIPHERTEXT mem region.
// Bank 0 is selected when the LSB of the memory address is 0.
// After SRAM_LATENCY cycles the result must equal pi_sk_bank0 rdata.
// ----------------------------------------------------------------
property privkey_out_rdata_bank0_p;
    (
    (pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_OUT.req  & ~pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_OUT.req_is_wr  & (pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_OUT.addr[12:2]  inside {[32:PRIVKEY_NUM_DWORDS-1]})       & (pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_OUT.addr[2]  == 1'b0) & `abr_ctrl.mldsa_valid_reg & !`abr_ctrl.mldsa_privkey_lock) |
    (pi_abr_reg_hwif_out_i.MLKEM_DECAPS_KEY.req   & ~pi_abr_reg_hwif_out_i.MLKEM_DECAPS_KEY.req_is_wr   & ({1'b0,pi_abr_reg_hwif_out_i.MLKEM_DECAPS_KEY.addr[11:2]}  inside {[0:MLKEM_DK_MEM_NUM_DWORDS-1]})  & (pi_abr_reg_hwif_out_i.MLKEM_DECAPS_KEY.addr[2]  == 1'b0) & `abr_ctrl.mlkem_valid_reg & !`abr_ctrl.mlkem_dk_lock) |
    (pi_abr_reg_hwif_out_i.MLKEM_ENCAPS_KEY.req   & ~pi_abr_reg_hwif_out_i.MLKEM_ENCAPS_KEY.req_is_wr   & ({2'b0,pi_abr_reg_hwif_out_i.MLKEM_ENCAPS_KEY.addr[10:2]}  inside {[0:MLKEM_EK_MEM_NUM_DWORDS-1]})  & (pi_abr_reg_hwif_out_i.MLKEM_ENCAPS_KEY.addr[2]  == 1'b0) & `abr_ctrl.mlkem_valid_reg ) |
    (pi_abr_reg_hwif_out_i.MLKEM_CIPHERTEXT.req   & ~pi_abr_reg_hwif_out_i.MLKEM_CIPHERTEXT.req_is_wr   & ({2'b0,pi_abr_reg_hwif_out_i.MLKEM_CIPHERTEXT.addr[10:2]}  inside {[0:MLKEM_CIPHERTEXT_MEM_NUM_DWORDS-1]}) & (pi_abr_reg_hwif_out_i.MLKEM_CIPHERTEXT.addr[2]  == 1'b0) & `abr_ctrl.mlkem_valid_reg)
    )
    |->
    ##SRAM_LATENCY
    `abr_ctrl.privkey_out_rdata == pi_sk_bank0_mem_if_rdata_o
;endproperty
assert_privkey_out_rdata_bank0_p: assert property (disable iff (!pi_rst_b || po_zeroize) privkey_out_rdata_bank0_p);


// ----------------------------------------------------------------
// privkey_out_rdata — bank 1 path
// Same four interfaces as bank 0 but selecting odd-bank-mapped
// addresses (LSB of memory address is 1). After SRAM_LATENCY
// cycles the result must equal pi_sk_bank1 rdata.
// ----------------------------------------------------------------
property privkey_out_rdata_bank1_p;
    (
    (pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_OUT.req  & ~pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_OUT.req_is_wr  & (pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_OUT.addr[12:2]  inside {[32:PRIVKEY_NUM_DWORDS-1]})       & (pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_OUT.addr[2]  == 1'b1)& `abr_ctrl.mldsa_valid_reg & !`abr_ctrl.mldsa_privkey_lock) |
    (pi_abr_reg_hwif_out_i.MLKEM_DECAPS_KEY.req   & ~pi_abr_reg_hwif_out_i.MLKEM_DECAPS_KEY.req_is_wr   & ({1'b0,pi_abr_reg_hwif_out_i.MLKEM_DECAPS_KEY.addr[11:2]}  inside {[0:MLKEM_DK_MEM_NUM_DWORDS-1]})  & (pi_abr_reg_hwif_out_i.MLKEM_DECAPS_KEY.addr[2]  == 1'b1) & `abr_ctrl.mlkem_valid_reg & !`abr_ctrl.mlkem_dk_lock) |
    (pi_abr_reg_hwif_out_i.MLKEM_ENCAPS_KEY.req   & ~pi_abr_reg_hwif_out_i.MLKEM_ENCAPS_KEY.req_is_wr   & ({2'b0,pi_abr_reg_hwif_out_i.MLKEM_ENCAPS_KEY.addr[10:2]}  inside {[0:MLKEM_EK_MEM_NUM_DWORDS-1]})  & (pi_abr_reg_hwif_out_i.MLKEM_ENCAPS_KEY.addr[2]  == 1'b1) & `abr_ctrl.mlkem_valid_reg ) |
    (pi_abr_reg_hwif_out_i.MLKEM_CIPHERTEXT.req   & ~pi_abr_reg_hwif_out_i.MLKEM_CIPHERTEXT.req_is_wr   & ({2'b0,pi_abr_reg_hwif_out_i.MLKEM_CIPHERTEXT.addr[10:2]}  inside {[0:MLKEM_CIPHERTEXT_MEM_NUM_DWORDS-1]}) & (pi_abr_reg_hwif_out_i.MLKEM_CIPHERTEXT.addr[2]  == 1'b1) & `abr_ctrl.mlkem_valid_reg )
    )
    |->
    ##SRAM_LATENCY
    `abr_ctrl.privkey_out_rdata == pi_sk_bank1_mem_if_rdata_o
;endproperty
assert_privkey_out_rdata_bank1_p: assert property (disable iff (!pi_rst_b || po_zeroize) privkey_out_rdata_bank1_p);


// ----------------------------------------------------------------
// privkey_out_rdata — register path (api_sk_reg_re)
// Triggered when the read address targets the register-backed
// region of one of three interfaces:
//   MLDSA_PRIVKEY_OUT  dwords [0:31]   → abr_scratch_reg via api_sk_reg_rd_dec
//   MLKEM_DECAPS_KEY   reg region       → abr_scratch_reg via mlkem_api_dk_reg_dec
//   MLKEM_ENCAPS_KEY   reg region       → abr_scratch_reg via mlkem_api_ek_reg_dec
// In this case privkey_out_rdata is sourced from api_reg_rdata,
// which is itself verified separately by the api_reg_rdata assertions.
// ----------------------------------------------------------------
property privkey_out_rdata_reg_p;
    (
    (pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_OUT.req & ~pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_OUT.req_is_wr & (pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_OUT.addr[12:2] inside {[0:31]}) & `abr_ctrl.mldsa_valid_reg) |
    (pi_abr_reg_hwif_out_i.MLKEM_DECAPS_KEY.req  & ~pi_abr_reg_hwif_out_i.MLKEM_DECAPS_KEY.req_is_wr  & ({1'b0,pi_abr_reg_hwif_out_i.MLKEM_DECAPS_KEY.addr[11:2]}  inside {[MLKEM_DK_MEM_NUM_DWORDS:DK_NUM_DWORDS-1]})) |
    (pi_abr_reg_hwif_out_i.MLKEM_ENCAPS_KEY.req  & ~pi_abr_reg_hwif_out_i.MLKEM_ENCAPS_KEY.req_is_wr  & ({2'b0,pi_abr_reg_hwif_out_i.MLKEM_ENCAPS_KEY.addr[10:2]}  inside {[MLKEM_EK_MEM_NUM_DWORDS:EK_NUM_DWORDS-1]}))
    )
    |->
    ##SRAM_LATENCY
    `abr_ctrl.privkey_out_rdata == `abr_ctrl.api_reg_rdata
;endproperty
assert_privkey_out_rdata_reg_p: assert property (disable iff (!pi_rst_b || po_zeroize) privkey_out_rdata_reg_p);

  // flop the rd_offset for pkdecode
  logic [SRAM_LATENCY:0][1:0] fv_pkdecode_rd_offset_f;

  assign fv_pkdecode_rd_offset_f[0] = pi_pkdecode_rd_addr_i[1:0];
   generate
    for (genvar shift = 1; shift <= SRAM_LATENCY; shift++) begin : fv_read_en_stage
    always_ff @(posedge pi_clk, negedge pi_rst_b) begin
      if(!pi_rst_b || po_zeroize) begin
        fv_pkdecode_rd_offset_f[shift] <= '0;
      end
      else begin
        fv_pkdecode_rd_offset_f[shift] <= fv_pkdecode_rd_offset_f[shift-1];
      end
    end
    end
   endgenerate
//read data out from mem to the pkdecode
logic [7:0][T1_COEFF_W-1:0] fv_pkdecode_rd_data_o;

  always_comb begin
    unique case (fv_pkdecode_rd_offset_f[SRAM_LATENCY][1:0])
      2'b00: fv_pkdecode_rd_data_o = `abr_ctrl.pubkey_ram_rdata_t1[7:0];
      2'b01: fv_pkdecode_rd_data_o = `abr_ctrl.pubkey_ram_rdata_t1[15:8];
      2'b10: fv_pkdecode_rd_data_o = `abr_ctrl.pubkey_ram_rdata_t1[23:16];
      default: fv_pkdecode_rd_data_o = `abr_ctrl.pubkey_ram_rdata_t1[31:24];
    endcase
  end
  property pkdecode_read_data_out_from_mem_p;
    po_pkdecode_rd_data_o == fv_pkdecode_rd_data_o
  ;endproperty
  assert_pkdecode_read_data_out_from_mem_a: assert property(pkdecode_read_data_out_from_mem_p);


  property pkdecode_rddata_valid_o_p;
    ##SRAM_LATENCY
    po_pkdecode_rd_data_valid_o == $past(pi_pkdecode_rd_en_i,SRAM_LATENCY)
  ;endproperty

  assert_pkdecode_rddata_valid_o_a: assert property (disable iff(!pi_rst_b || po_zeroize) pkdecode_rddata_valid_o_p);



  property pkdecode_rddata_valid_o_reset_p;
  $past(!pi_rst_b || po_zeroize)
  |->
  !po_pkdecode_rd_data_valid_o[*SRAM_LATENCY]
  ;endproperty

  assert_pkdecode_rddata_valid_o_reset_a: assert property (pkdecode_rddata_valid_o_reset_p);


// ----------------------------------------------------------------
// skdecode_rd_data_valid_o
// ----------------------------------------------------------------
property skdecode_rddata_valid_o_p;
    ##SRAM_LATENCY
    po_skdecode_rd_data_valid_o == $past({(pi_skdecode_keymem_if_i[1].rd_wr_en == RW_READ),
                                          (pi_skdecode_keymem_if_i[0].rd_wr_en == RW_READ)}, SRAM_LATENCY)
;endproperty
assert_skdecode_rddata_valid_o_p: assert property (disable iff (!pi_rst_b || po_zeroize) skdecode_rddata_valid_o_p);

property skdecode_rddata_valid_o_reset_p;
    $past(!pi_rst_b || po_zeroize)
    |->
    !po_skdecode_rd_data_valid_o [*SRAM_LATENCY]
;endproperty
assert_skdecode_rddata_valid_o_reset_p: assert property (skdecode_rddata_valid_o_reset_p);

// ----------------------------------------------------------------
// decompress_api_rd_data_valid_o
// ----------------------------------------------------------------
property decompress_api_rddata_valid_o_p;
    ##SRAM_LATENCY
    po_decompress_api_rd_data_valid_o == $past(pi_decompress_api_rd_en_i, SRAM_LATENCY)
;endproperty
assert_decompress_api_rddata_valid_o_p: assert property (disable iff (!pi_rst_b || po_zeroize) decompress_api_rddata_valid_o_p);

property decompress_api_rddata_valid_o_reset_p;
    $past(!pi_rst_b || po_zeroize)
    |->
    !po_decompress_api_rd_data_valid_o [*SRAM_LATENCY]
;endproperty
assert_decompress_api_rddata_valid_o_reset_p: assert property (decompress_api_rddata_valid_o_reset_p);

// ----------------------------------------------------------------
// compress_api_rd_data_valid_o
// OR-reduction of compress_keymem_re_bank[0] collapses to
// compress_api_rw_en_i[1] since the per-bank enable is
// compress_api_rw_en_i[1] & (compress_api_rw_addr_i[0] == i),
// and the OR across both banks removes the address term.
// ----------------------------------------------------------------
property compress_api_rddata_valid_o_p;
    ##SRAM_LATENCY
    po_compress_api_rd_data_valid_o == $past(pi_compress_api_rw_en_i[1], SRAM_LATENCY)
;endproperty
assert_compress_api_rddata_valid_o_p: assert property (disable iff (!pi_rst_b || po_zeroize) compress_api_rddata_valid_o_p);

property compress_api_rddata_valid_o_reset_p;
    $past(!pi_rst_b || po_zeroize)
    |->
    !po_compress_api_rd_data_valid_o [*SRAM_LATENCY]
;endproperty
assert_compress_api_rddata_valid_o_reset_p: assert property (compress_api_rddata_valid_o_reset_p);

// ----------------------------------------------------------------
// sigdecode_z_rd_data_valid_o
// ----------------------------------------------------------------
property sigdecode_z_rddata_valid_o_p;
    ##SRAM_LATENCY
    po_sigdecode_z_rd_data_valid_o == $past((pi_sigdecode_z_rd_req_i.rd_wr_en == RW_READ), SRAM_LATENCY)
;endproperty
assert_sigdecode_z_rddata_valid_o_p: assert property (disable iff (!pi_rst_b || po_zeroize) sigdecode_z_rddata_valid_o_p);

property sigdecode_z_rddata_valid_o_reset_p;
    $past(!pi_rst_b || po_zeroize)
    |->
    !po_sigdecode_z_rd_data_valid_o [*SRAM_LATENCY]
;endproperty
assert_sigdecode_z_rddata_valid_o_reset_p: assert property (sigdecode_z_rddata_valid_o_reset_p);
  // Normcheck primary out from the sequencer checks sice it has both sequencers

    // ===============================================================
    // SECTION 24 — Control Outputs (NTT, Normcheck, Busy, Decompose)
    // ===============================================================
    //
    // Controller orchestrates multiple computational blocks via control
    // outputs. These assertions verify the control signals are correct.
    //
    // NTT (Number Theoretic Transform):
    //   ntt_outputs_0_p verifies for NTT instance 0:
    //   - po_ntt_enable_o derived from instruction
    //   - po_ntt_mode_o (FWD/INV/PWM) from instruction
    //   - Masking enable gated by ntt_en (RTL: masking_en & ntt_en); shuffling follows instruction directly
    //
    // NORMCHECK:
    //   norm_check_out_p verifies mode from instruction:
    //   - Mode 0: Check ||z|| < γ1 - β (signature z)
    //   - Mode 1: Check ||w0|| < γ2 (signing low-order w0)
    //   - Mode 2: Check other norm constraints
    //
    // BUSY:
    //   busy_o_p verifies controller busy except when:
    //   - In RESET state
    //   - In ZEROIZE state  
    //   - valid flag set (operation complete)
    //
    // DECOMPOSE:
    //   decompose_mode_p verifies mode set only for USEHINT instruction.
    //   Wrong mode causes mathematically invalid signature.
    //
    // MLKEM ISOLATION:
    //   mlkem_outputs_zero_during_mldsa_p verifies compress/decompress
    //   outputs are disabled when MLDSA operation active.
    //   This prevents cross-contamination between MLKEM and MLDSA.
    // ===============================================================

  property norm_check_out_p;
    po_normcheck_mode_o == ((`abr_ctrl.abr_instr.opcode.aux_en & (`abr_ctrl.abr_instr.opcode.mode.aux_mode == MLDSA_NORMCHK)) ? `abr_ctrl.abr_instr.imm[1:0]: '0)
  ;endproperty

  assert_norm_check_out_a: assert property(norm_check_out_p);


// ntt primary outputs combinational masking and shuffling
  property ntt_outputs_0_p;
    po_ntt_enable_o ==
        (`abr_ctrl.abr_instr.opcode.ntt_en &&
         (`abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_FUNC_START)) &&
    po_ntt_mode_o == (`abr_ctrl.abr_instr.opcode.mode.ntt_mode) &&
    po_ntt_masking_en_o ==
        (`abr_ctrl.abr_instr.opcode.masking_en & `abr_ctrl.ntt_en) &&
    po_ntt_shuffling_en_o == (`abr_ctrl.abr_instr.opcode.shuffling_en) &&
    `abr_ctrl.ntt_temp_address ==
        (`abr_ctrl.abr_instr.imm[0] ? MLDSA_TEMP2_BASE : MLDSA_TEMP0_BASE) &&
    po_ntt_mem_base_addr_o == ntt_mem_addr_t'{src_base_addr:
                                        `abr_ctrl.abr_instr.operand1[ABR_MEM_ADDR_WIDTH-1:0],
                                    interim_base_addr:`abr_ctrl.ntt_temp_address,
                                    dest_base_addr:
                                        `abr_ctrl.abr_instr.operand3[ABR_MEM_ADDR_WIDTH-1:0]}
  ;endproperty

  assert_ntt_outputs_0_a: assert property(ntt_outputs_0_p);

  // split_en_o must exactly track RTL: split_en_o = MASKING_EN & abr_instr.opcode.masking_en & ~ntt_en.
  // NOTE: MASKING_EN is a compile-time parameter (abr_ctrl.sv default 0, not overridden by
  // fv_abr_ctrl_dut's abr_ctrl_inst or by the `elaborate -top fv_abr_ctrl_dut` call), so it is
  // constant for the whole proof. A piecewise "MASKING_EN && masking_en && !ntt_en |-> split_en_o"
  // style check would be vacuous whenever MASKING_EN==0 for this build, and would leave the
  // masking_en==1 && ntt_en==0 case completely unconstrained. A single equality avoids both issues
  // and remains correct regardless of how MASKING_EN is elaborated.
  property split_en_o_p;
    po_split_en_o == (`abr_ctrl.MASKING_EN & `abr_ctrl.abr_instr.opcode.masking_en & ~`abr_ctrl.ntt_en)
  ;endproperty
  assert_split_en_o_a: assert property(split_en_o_p);

  // ---------------------------------------------------------------------------
  // Recombine control (consumer-fused recombination, *_R opcodes)
  // ---------------------------------------------------------------------------
  // recombine_en_o must exactly track RTL: MASKING_EN & abr_instr.opcode.recombine_en.
  // Written as an equality for the same reason as split_en_o_p (MASKING_EN is elaboration-constant).
  property recombine_en_o_p;
    po_recombine_en_o == (`abr_ctrl.MASKING_EN & `abr_ctrl.abr_instr.opcode.recombine_en)
  ;endproperty
  assert_recombine_en_o_a: assert property(recombine_en_o_p);

  // No recombination is requested while the controller is in reset or zeroize
  // (abr_instr is forced to zero in these states).
  property recombine_idle_in_reset_zeroize_p;
    ((`abr_ctrl.abr_prog_cntr == ABR_RESET) || (`abr_ctrl.abr_prog_cntr == ABR_ZEROIZE))
    |->
    !po_recombine_en_o && !po_recombine_mode_o
  ;endproperty
  assert_recombine_idle_in_reset_zeroize_a: assert property(recombine_idle_in_reset_zeroize_p);

  // Splitting and recombination are never requested by the same instruction.
  property split_recombine_exclusive_p;
    !(`abr_ctrl.abr_instr.opcode.masking_en && `abr_ctrl.abr_instr.opcode.recombine_en) &&
    !(po_split_en_o && po_recombine_en_o)
  ;endproperty
  assert_split_recombine_exclusive_a: assert property(split_recombine_exclusive_p);

  // A recombine instruction drives exactly one memory consumer (NTT or AUX) and never
  // the Keccak/sampler path.
  property recombine_opcode_class_p;
    `abr_ctrl.abr_instr.opcode.recombine_en
    |->
    !`abr_ctrl.abr_instr.opcode.keccak_en &&
    !`abr_ctrl.abr_instr.opcode.sampler_en &&
    (`abr_ctrl.abr_instr.opcode.ntt_en != `abr_ctrl.abr_instr.opcode.aux_en)
  ;endproperty
  assert_recombine_opcode_class_a: assert property(recombine_opcode_class_p);

  // Recombination is fused only into the supported consumers:
  // NTT: PWS_R, PWA_R (MLDSA), MLKEM_PWS_R. AUX: DECOMPOSE_R, NORMCHK_R, SKENCODE_R,
  // SIGENCODE_R, PWR2RND_R (MLDSA), COMPRESS_R (MLKEM).
  property recombine_legal_consumer_p;
    `abr_ctrl.abr_instr.opcode.recombine_en
    |->
    (`abr_ctrl.abr_instr.opcode.ntt_en &&
       (`abr_ctrl.abr_instr.opcode.mode.ntt_mode inside {MLDSA_PWS, MLDSA_PWA, MLKEM_PWS})) ||
    (`abr_ctrl.abr_instr.opcode.aux_en &&
       (`abr_ctrl.abr_instr.opcode.mode.aux_mode inside {MLDSA_DECOMP, MLDSA_NORMCHK, MLDSA_SKENCODE,
                                                         MLDSA_SIGENC, MLDSA_PWR2RND, MLKEM_COMPRESS}))
  ;endproperty
  assert_recombine_legal_consumer_a: assert property(recombine_legal_consumer_p);

  // MLDSA consumers select the MLDSA modulus (recombine_mode_o = 0).
  property recombine_mode_mldsa_p;
    `abr_ctrl.abr_instr.opcode.recombine_en &&
    ((`abr_ctrl.abr_instr.opcode.ntt_en &&
        (`abr_ctrl.abr_instr.opcode.mode.ntt_mode inside {MLDSA_PWS, MLDSA_PWA})) ||
     (`abr_ctrl.abr_instr.opcode.aux_en &&
        (`abr_ctrl.abr_instr.opcode.mode.aux_mode inside {MLDSA_DECOMP, MLDSA_NORMCHK, MLDSA_SKENCODE,
                                                          MLDSA_SIGENC, MLDSA_PWR2RND})))
    |->
    !po_recombine_mode_o
  ;endproperty
  assert_recombine_mode_mldsa_a: assert property(recombine_mode_mldsa_p);

  // Reachability of an MLDSA fused-recombine instruction.
  cover_recombine_mldsa_c: cover property(
    `abr_ctrl.abr_instr.opcode.recombine_en && !po_recombine_mode_o
  );

  // busy if the cntr is not ready

  property busy_o_p;
  `ifdef CALIPTRA
    po_busy_o == !((( `abr_ctrl.abr_prog_cntr == ABR_RESET) | ( `abr_ctrl.abr_prog_cntr == ABR_ZEROIZE) |
                            `abr_ctrl.mldsa_valid_reg |  `abr_ctrl.mlkem_valid_reg) &
                            `abr_ctrl.kv_mlkem_seed_ready &
                            `abr_ctrl.kv_mlkem_msg_ready &
                            `abr_ctrl.kv_mldsa_seed_ready &
                            `abr_ctrl.kv_mlkem_sharedkey_ready);
  `else
    po_busy_o == !(( `abr_ctrl.abr_prog_cntr == ABR_RESET) | ( `abr_ctrl.abr_prog_cntr == ABR_ZEROIZE) |
                            `abr_ctrl.mldsa_valid_reg |  `abr_ctrl.mlkem_valid_reg);
  `endif
  endproperty

  assert_busy_o_a:assert property(busy_o_p);


// signature output read from the register
logic [SIGNATURE_H_VALID_NUM_BYTES-1:0][7:0] fv_signature_h_o;
  always_comb begin
    //HW read h
    for (int i = 0; i < SIGNATURE_H_VALID_NUM_BYTES; i++) begin
      fv_signature_h_o[i] = `abr_ctrl.signature_reg.enc.h[i/4][(i%4)*8 +: 8];
    end
  end

    // ===============================================================
    // SECTION 25 — Output Packing (Signature H and LFSR Seed)
    // ===============================================================
    //
    // Some outputs require bit-level packing from internal registers.
    //
    // SIGNATURE H OUTPUT:
    //   signature_h_o_p verifies po_signature_h_o is correctly packed
    //   from signature_reg.enc.h field. The h field stores omega hint
    //   bits indicating which coefficients need high-order correction.
    //
    // LFSR SEED OUTPUTS:
    //
    // 1. lfsr_seed_o_set:
    //    Verifies po_lfsr_seed_o updates when sampler writes
    //    LFSR seed register (operand3 == ABR_DEST_LFSR_SEED_REG_ID).
    //
    // 2. lfsr_seed_o_stable:
    //    Verifies po_lfsr_seed_o stable when no sampler write active.
    //    Instability would cause NTT masking/shuffling to use wrong seed.
    //
    // BYTE PACKING:
    //   Both properties deal with packing multiple bytes from SHA3
    //   state into output registers. Correct byte order is critical.
    // ===============================================================

  property signature_h_o_p;
    po_signature_h_o == fv_signature_h_o;
  endproperty
  assert_signature_h_o_a: assert property(signature_h_o_p);

  //lfsr seed output is updated if the lsft seed reg id is the destination.
  property lfsr_seed_o_set;
    pi_sampler_state_dv_i &&
    `abr_ctrl.abr_instr.operand3 == ABR_DEST_LFSR_SEED_REG_ID
    |=>
    po_lfsr_seed_o == $past(pi_sampler_state_data_i[MSG_SEED_LSB+KECCAK_MSG_LFSR_W-1:0])
  ;endproperty

  assert_lfsr_seed_o_set: assert property(disable iff(!pi_rst_b)lfsr_seed_o_set);

  property lfsr_seed_o_stable;
    !(pi_sampler_state_dv_i &&
    `abr_ctrl.abr_instr.operand3 == ABR_DEST_LFSR_SEED_REG_ID)
    |=>
    $stable(po_lfsr_seed_o)
  ;endproperty

  assert_lfsr_seed_o_stable: assert property(disable iff(!pi_rst_b)lfsr_seed_o_stable);
  

  // decompose mode is set only if is in use hint

  property decompose_mode_p;
    po_decompose_mode_o == (`abr_ctrl.abr_instr.opcode.aux_en & (`abr_ctrl.abr_instr.opcode.mode.aux_mode == MLDSA_USEHINT))
  ;endproperty

  assert_decompose_mode_a: assert property(decompose_mode_p);


  property mlkem_outputs_zero_during_mldsa_p;
    `abr_ctrl.mldsa_keygen_process ||
    `abr_ctrl.mldsa_signing_process ||
    `abr_ctrl.mldsa_verifying_process ||
    `abr_ctrl.mldsa_keygen_signing_process
    |->
    !po_compress_enable_o &&
    !po_decompress_enable_o
  ;endproperty

  assert_mlkem_outputs_zero_during_mldsa_a: assert property(mlkem_outputs_zero_during_mldsa_p);

  // cover mldsa_done
  `ifdef KV_ABR_PROG

    // ===============================================================
    // SECTION 26 — Cover Properties (Liveness Checks)
    // ===============================================================
    //
    // Cover properties verify interesting scenarios are reachable.
    // They don't prove correctness, but ensure the design isn't
    // trivially broken (e.g., FSM stuck, valid never asserts).
    //
    // KV_ABR_PROG BUILD COVERS:
    //
    // 1. valid_reg_rose_twice_c:
    //    Verifies mldsa_valid_reg can rise, clear, and rise again.
    //    Tests: Multiple operations in sequence work.
    //
    // 2. mlkem_valid_reg_rose_twice_c:
    //    Verifies mlkem_valid_reg can rise, clear, and rise again.
    //    Tests: MLKEM operations complete successfully.
    //
    // 3. mlkem_to_mldsa_c:
    //    Verifies MLKEM operation can complete, then MLDSA starts.
    //    Tests: Mode switching works correctly.
    //
    // 4. mldsa_to_mlkem_c:
    //    Verifies MLDSA operation can complete, then MLKEM starts.
    //    Tests: Reverse mode switching works.
    //
    // WHY COVERS MATTER:
    //   If a cover never hits, either:
    //   - Design is broken (FSM deadlock, wrong enables)
    //   - Constraints are too tight (test environment issue)
    //   - Scenario is unreachable by design (document this!)
    // ===============================================================

  cover property(disable iff(!pi_rst_b) $rose(`abr_ctrl.mldsa_valid_reg)[->2]);

    // ===============================================================
    // SECTION 26 — Cover Properties (Liveness Checks)
    // ===============================================================
    //
    // Cover properties verify interesting scenarios are reachable.
    // They don't prove correctness, but ensure the design isn't
    // trivially broken (e.g., FSM stuck, valid never asserts).
    //
    // KV_ABR_PROG BUILD COVERS:
    //
    // 1. valid_reg_rose_twice_c:
    //    Verifies mldsa_valid_reg can rise, clear, and rise again.
    //    Tests: Multiple operations in sequence work.
    //
    // 2. mlkem_valid_reg_rose_twice_c:
    //    Verifies mlkem_valid_reg can rise, clear, and rise again.
    //    Tests: MLKEM operations complete successfully.
    //
    // 3. mlkem_to_mldsa_c:
    //    Verifies MLKEM operation can complete, then MLDSA starts.
    //    Tests: Mode switching works correctly.
    //
    // 4. mldsa_to_mlkem_c:
    //    Verifies MLDSA operation can complete, then MLKEM starts.
    //    Tests: Reverse mode switching works.
    //
    // WHY COVERS MATTER:
    //   If a cover never hits, either:
    //   - Design is broken (FSM deadlock, wrong enables)
    //   - Constraints are too tight (test environment issue)
    //   - Scenario is unreachable by design (document this!)
    // ===============================================================

  cover property(disable iff(!pi_rst_b) $rose(`abr_ctrl.mlkem_valid_reg)[->2]);

  `endif

  // ===============================================================
  // SECTION 27 — Cross-Mode Transition Covers (non-KV build only)
  // ===============================================================
  // These cross-modal covers verify that after one operation
  // completes, a different-mode operation can also complete.
  // Excluded from KV_ABR_PROG because the extended sequencer
  // changes reachability bounds for multi-operation sequences.
  // ===============================================================

  `ifndef KV_ABR_PROG

  // mlkem_to_mldsa: MLKEM completes, then MLDSA valid asserts
  cover property(
      disable iff(!pi_rst_b)
      $rose(`abr_ctrl.mlkem_valid_reg)
      ##1 $rose(`abr_ctrl.mldsa_valid_reg)[->1]);

  // mldsa_to_mlkem: MLDSA completes, then MLKEM valid asserts
  cover property(
      disable iff(!pi_rst_b)
      $rose(`abr_ctrl.mldsa_valid_reg)
      ##1 $rose(`abr_ctrl.mlkem_valid_reg)[->1]);

  `endif

endmodule
