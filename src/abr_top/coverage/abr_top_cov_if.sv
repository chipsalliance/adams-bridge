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

`ifndef VERILATOR

interface abr_top_cov_if
    import abr_params_pkg::*;
    import abr_ctrl_pkg::*;
    import abr_sampler_pkg::*;
    `ifdef CALIPTRA
    import kv_defines_pkg::*; 
    `endif  
    (

    `ifdef CALIPTRA
    input logic           ocp_lock_in_progress,
    `endif

    input logic           clk,
    input logic           rst_b,
    input logic           debugUnlock_or_scan_mode_switch

);

    logic [2 : 0] mldsa_cmd;
    logic [2 : 0] mlkem_cmd;
    logic [2 : 0] mldsa_sw_cmd;
    logic zeroize;
    logic ready;
    logic mldsa_valid;
    logic mlkem_valid;
    logic pcr_process;

    logic error_flag;
    logic skdecode_error;
    logic mldsa_keygen_process;
    logic mldsa_signing_process;
    logic mldsa_verifying_process;
    logic mldsa_keygen_signing_process;
    logic mlkem_keygen_process;
    logic mlkem_encaps_process;
    logic mlkem_decaps_process;
    logic mlkem_keygen_decaps_process;

    logic verify_failure;
    logic normcheck_failure;
    logic [2 : 0] normcheck_mode;
    logic makehint_failure;
    logic invalid_hint;
    logic external_mu_mode;
    logic stream_msg_mode;
    logic stream_msg_ip;

    `ifdef CALIPTRA
    logic pcr_sign_mode;
    logic pcr_sign_input_invalid;
    logic kv_mldsa_seed_data_present;
    logic kv_mlkem_seed_data_present;
    logic kv_mlkem_msg_data_present;

    assign pcr_sign_input_invalid = abr_top.abr_ctrl_inst.pcr_sign_input_invalid;
    assign pcr_sign_mode = abr_top.abr_ctrl_inst.pcr_sign_mode;
    
    assign kv_mldsa_seed_data_present = abr_top.abr_ctrl_inst.kv_mldsa_seed_data_present;
    assign kv_mlkem_seed_data_present = abr_top.abr_ctrl_inst.kv_mlkem_seed_data_present;
    assign kv_mlkem_msg_data_present  = abr_top.abr_ctrl_inst.kv_mlkem_msg_data_present;

    logic mldsa_seed_zero_error;
    logic mlkem_seed_zero_error;
    logic mlkem_msg_zero_error;

    assign mldsa_seed_zero_error = abr_top.abr_ctrl_inst.mldsa_seed_zero_error;
    assign mlkem_seed_zero_error = abr_top.abr_ctrl_inst.mlkem_seed_zero_error;
    assign mlkem_msg_zero_error  = abr_top.abr_ctrl_inst.mlkem_msg_zero_error;

    always_ff @(posedge clk) begin
        if (!rst_b) begin
            pcr_process <= '0;
        end
        else if (pcr_sign_mode) begin
            pcr_process <= '1;
        end
        else if (!mldsa_signing_process & !mldsa_keygen_signing_process) begin
            pcr_process <= '0;
        end
    end

    kv_write_filter_metrics_t kv_write_metrics;
    kv_write_ctrl_reg_t kv_write_ctrl_reg;
    kv_read_ctrl_reg_t kv_read_ctrl_reg;

    assign kv_write_metrics = abr_top.abr_ctrl_inst.kv_mlkem_sharedkey_write_metrics;
    assign kv_write_ctrl_reg = abr_top.abr_ctrl_inst.kv_mlkem_sharedkey_write_ctrl_reg;
    assign kv_read_ctrl_reg = abr_top.abr_ctrl_inst.kv_mldsa_seed_read_ctrl_reg;
    `endif

    assign mldsa_cmd = abr_top.abr_ctrl_inst.mldsa_cmd_reg;
    assign mlkem_cmd = abr_top.abr_ctrl_inst.mlkem_cmd_reg;
    assign zeroize = abr_top.abr_ctrl_inst.zeroize;
    assign ready = abr_top.abr_ctrl_inst.abr_ready;
    assign mldsa_valid = abr_top.abr_ctrl_inst.mldsa_valid_reg;
    assign mlkem_valid = abr_top.abr_ctrl_inst.mlkem_valid_reg;

    always_ff @(posedge clk) begin
        if (!rst_b) begin
            mldsa_sw_cmd <= '0;
        end
        else if (abr_top.abr_reg_inst.decoded_reg_strb.MLDSA_CTRL && abr_top.abr_reg_inst.decoded_req_is_wr) begin // SW write
            mldsa_sw_cmd <= (abr_top.abr_reg_inst.field_storage.MLDSA_CTRL.CTRL.value & ~abr_top.abr_reg_inst.decoded_wr_biten[2:0]) | (abr_top.abr_reg_inst.decoded_wr_data[2:0] & abr_top.abr_reg_inst.decoded_wr_biten[2:0]);
        end
    end


    assign error_flag = abr_top.abr_ctrl_inst.error_flag | abr_top.abr_ctrl_inst.error_flag_reg;
    assign skdecode_error = abr_top.abr_ctrl_inst.skdecode_error_i;

    assign mldsa_keygen_process = abr_top.abr_ctrl_inst.mldsa_keygen_process;
    assign mldsa_signing_process = abr_top.abr_ctrl_inst.mldsa_signing_process;
    assign mldsa_verifying_process = abr_top.abr_ctrl_inst.mldsa_verifying_process;
    assign mldsa_keygen_signing_process = abr_top.abr_ctrl_inst.mldsa_keygen_signing_process;
    assign mlkem_keygen_process = abr_top.abr_ctrl_inst.mlkem_keygen_process;
    assign mlkem_encaps_process = abr_top.abr_ctrl_inst.mlkem_encaps_process;
    assign mlkem_decaps_process = abr_top.abr_ctrl_inst.mlkem_decaps_process;
    assign mlkem_keygen_decaps_process = abr_top.abr_ctrl_inst.mlkem_keygen_decaps_process;

    assign verify_failure = abr_top.abr_ctrl_inst.clear_verify_valid;
    assign normcheck_failure = abr_top.abr_ctrl_inst.normcheck_done_i & abr_top.abr_ctrl_inst.normcheck_invalid_i;
    assign normcheck_mode[0] = (abr_top.abr_ctrl_inst.normcheck_mode_o == 2'b00);
    assign normcheck_mode[1] = (abr_top.abr_ctrl_inst.normcheck_mode_o == 2'b01);
    assign normcheck_mode[2] = (abr_top.abr_ctrl_inst.normcheck_mode_o == 2'b10);
    assign makehint_failure = abr_top.abr_ctrl_inst.makehint_done_i & abr_top.abr_ctrl_inst.makehint_invalid_i;
    assign invalid_hint = abr_top.abr_ctrl_inst.sigdecode_h_invalid_i;
    assign external_mu_mode = abr_top.abr_ctrl_inst.external_mu_mode;
    assign stream_msg_mode = abr_top.abr_ctrl_inst.stream_msg_mode;
    assign stream_msg_ip = abr_top.abr_ctrl_inst.stream_msg_ip;

    // =========================================================================
    // SCA / Masking Coverage Signals
    // =========================================================================

    // Masking control signals from abr_ctrl
    logic sca_ntt_masking_en;
    logic sca_ntt_shuffling_en;
    logic sca_split_en;
    logic sca_recombine_en;

    assign sca_ntt_masking_en   = abr_top.ntt_masking_en_ctrl;
    assign sca_ntt_shuffling_en = abr_top.ntt_shuffling_en_ctrl;
    assign sca_split_en         = abr_top.split_en;
    assign sca_recombine_en     = abr_top.recombine_en;

    // NTT[1] enable (dual-NTT activation) — only exists when MASKING_EN=1
    logic sca_ntt1_enable;
    assign sca_ntt1_enable = (abr_top.ABR_NUM_NTT > 1) ? abr_top.ntt_enable[abr_top.MASKED_IDX] : 1'b0;

    // NTT[0] enable (primary NTT — always active for NTT ops)
    logic sca_ntt0_enable;
    assign sca_ntt0_enable = abr_top.ntt_enable[0];

    // NTT mode for NTT[0] (primary) — covers all operation types including RECOMBINE
    abr_ntt_mode_e sca_ntt0_mode;
    assign sca_ntt0_mode = abr_top.ntt_mode[0];

    // NTT mode for NTT[1] — should exercise subset of modes when MASKING_EN=1
    abr_ntt_mode_e sca_ntt1_mode;
    assign sca_ntt1_mode = (abr_top.ABR_NUM_NTT > 1) ? abr_top.ntt_mode[abr_top.MASKED_IDX] : ABR_NTT_NONE;

    // Opcode masking/shuffling bits from the instruction
    logic sca_opcode_masking_en;
    logic sca_opcode_shuffling_en;
    logic sca_opcode_ntt_en;

    assign sca_opcode_masking_en   = abr_top.abr_ctrl_inst.abr_instr.opcode.masking_en;
    assign sca_opcode_shuffling_en = abr_top.abr_ctrl_inst.abr_instr.opcode.shuffling_en;
    assign sca_opcode_ntt_en       = abr_top.abr_ctrl_inst.abr_instr.opcode.ntt_en;

    // Splitter activity — sampler splitter (one of the three splitter instances)
    logic sca_sampler_splitter_en;
    logic sca_sampler_splitter_ready;
    assign sca_sampler_splitter_en    = abr_top.sampler_top_inst.u_splitter.en_i;
    assign sca_sampler_splitter_ready = abr_top.sampler_top_inst.u_splitter.ready_o;

    // Splitter activity — skdecode has two splitters (port A and port B)
    logic sca_skdecode_splitter_a_en;
    logic sca_skdecode_splitter_b_en;
    assign sca_skdecode_splitter_a_en = abr_top.skdecode_inst.u_splitter_a.en_i;
    assign sca_skdecode_splitter_b_en = abr_top.skdecode_inst.u_splitter_b.en_i;

    // Splitter activity — decompress splitter
    logic sca_decompress_splitter_en;
    assign sca_decompress_splitter_en = abr_top.decompress_top_inst.u_splitter.en_i;

    // Splitter rand reduction — detect when LFSR rand >= q (reduction path exercised)
    logic sca_splitter_rand_reduced;
    assign sca_splitter_rand_reduced = abr_top.sampler_top_inst.u_splitter.rand_raw[0] >=
                                       abr_top.sampler_top_inst.u_splitter.prime;

    // Recombine pipeline depth tracking
    logic sca_recombine_en_pipe_last;
    assign sca_recombine_en_pipe_last = abr_top.recombine_en_pipe[abr_top.SRAM_LATENCY];

    // skip_recombine — when MASKING_EN=0, recombine ops are NOP'd
    logic sca_skip_recombine;
    assign sca_skip_recombine = abr_top.abr_ctrl_inst.skip_recombine;

    // NTT[1] SIB read pipeline (bug 9 fix — ntt_sib_rd_detect_d1[0] gates NTT[1] valid)
    logic sca_ntt_sib_rd_detect_d1;
    assign sca_ntt_sib_rd_detect_d1 = abr_top.ntt_sib_rd_detect_d1[0];

    // Recombine pipeline first stage (bug 3 fix — recombine_en_pipe timing)
    logic sca_recombine_en_pipe_first;
    assign sca_recombine_en_pipe_first = abr_top.recombine_en_pipe[0];

    // Sampler opcode mode (covers masked-sampling dispatch)
    abr_sampler_mode_e sca_sampler_mode;
    assign sca_sampler_mode = abr_top.sampler_mode;

    // NTT[0]/NTT[1] mode match indicator — when masking, modes should be identical
    logic sca_ntt_modes_match;
    assign sca_ntt_modes_match = (abr_top.ABR_NUM_NTT > 1) ?
                                 (abr_top.ntt_mode[0] == abr_top.ntt_mode[abr_top.MASKED_IDX]) : 1'b1;

    // MASKED_NTT_NOSHUF detection (bug 6 fix — masking=1, shuffling=0, mode=MLDSA_NTT for NTT(c))
    // Distinguished from REJS_MASKED_* which also have masking=1,shuffling=0 but use PWM_SMPL modes.
    logic sca_masked_noshuf;
    assign sca_masked_noshuf = sca_opcode_masking_en & ~sca_opcode_shuffling_en &
                               sca_opcode_ntt_en &
                               (abr_top.abr_ctrl_inst.abr_instr.opcode.mode.ntt_mode == MLDSA_NTT);

    // Zeroize signal (re-tap for SCA covergroup local use)
    logic sca_zeroize;
    assign sca_zeroize = abr_top.abr_ctrl_inst.zeroize;

    // VERIFY_RES poison-init: re-tap signals that drive `clear_verify_valid`
    // so we can cover that both abort paths fire. By design (abr_ctrl.sv:806-810,
    // hwclr = zeroize only), VERIFY_RES retains the poison `~c~` whenever
    // clear_verify_valid asserts — coverage on the two source bits is sufficient.
    logic sca_clear_verify_valid;
    logic sca_normcheck_invalid;
    logic sca_sigdecode_h_invalid;
    assign sca_clear_verify_valid  = abr_top.abr_ctrl_inst.clear_verify_valid;
    assign sca_normcheck_invalid   = abr_top.abr_ctrl_inst.normcheck_invalid_i;
    assign sca_sigdecode_h_invalid = abr_top.abr_ctrl_inst.sigdecode_h_invalid_i;

    // =========================================================================
    // SCA Covergroup
    // =========================================================================

    covergroup abr_sca_cov_grp @(posedge clk);

        // --- Process coverpoints (declared first so crosses can reference them) ---
        sca_mldsa_keygen_cp:  coverpoint mldsa_keygen_process;
        sca_mldsa_signing_cp: coverpoint mldsa_signing_process;
        sca_mlkem_keygen_cp:  coverpoint mlkem_keygen_process;
        sca_mlkem_encaps_cp:  coverpoint mlkem_encaps_process;
        sca_mlkem_decaps_cp:  coverpoint mlkem_decaps_process;

        // --- Masking activation ---
        ntt_masking_en_cp: coverpoint sca_ntt_masking_en;
        ntt_shuffling_en_cp: coverpoint sca_ntt_shuffling_en;
        split_en_cp: coverpoint sca_split_en;
        recombine_en_cp: coverpoint sca_recombine_en;
        ntt0_enable_cp: coverpoint sca_ntt0_enable;
        ntt1_enable_cp: coverpoint sca_ntt1_enable;
        skip_recombine_cp: coverpoint sca_skip_recombine;

        // --- NTT[0] mode (covers all operation types) ---
        ntt0_mode_cp: coverpoint sca_ntt0_mode {
            bins ntt_none        = {ABR_NTT_NONE};
            bins mldsa_ntt       = {MLDSA_NTT};
            bins mldsa_intt      = {MLDSA_INTT};
            bins mldsa_pwm       = {MLDSA_PWM};
            bins mldsa_pwm_accum = {MLDSA_PWM_ACCUM};
            bins mldsa_pwm_smpl  = {MLDSA_PWM_SMPL};
            bins mldsa_pwm_accum_smpl = {MLDSA_PWM_ACCUM_SMPL};
            bins mldsa_pwa       = {MLDSA_PWA};
            bins mldsa_pws       = {MLDSA_PWS};
            bins mldsa_recombine = {MLDSA_RECOMBINE};
            bins mlkem_ntt       = {MLKEM_NTT};
            bins mlkem_intt      = {MLKEM_INTT};
            bins mlkem_pwm       = {MLKEM_PWM};
            bins mlkem_pwm_accum = {MLKEM_PWM_ACCUM};
            bins mlkem_pwm_smpl  = {MLKEM_PWM_SMPL};
            bins mlkem_pwm_accum_smpl = {MLKEM_PWM_ACCUM_SMPL};
            bins mlkem_pwa       = {MLKEM_PWA};
            bins mlkem_pws       = {MLKEM_PWS};
            bins mlkem_recombine = {MLKEM_RECOMBINE};
        }

        // --- NTT[1] mode (subset — only sampled when NTT[1] is actually firing) ---
        ntt1_mode_cp: coverpoint sca_ntt1_mode iff (sca_ntt1_enable) {
            bins mldsa_ntt       = {MLDSA_NTT};
            bins mldsa_intt      = {MLDSA_INTT};
            bins mldsa_pwm       = {MLDSA_PWM};
            bins mldsa_pwm_accum = {MLDSA_PWM_ACCUM};
            bins mldsa_pwm_smpl  = {MLDSA_PWM_SMPL};
            bins mldsa_pwm_accum_smpl = {MLDSA_PWM_ACCUM_SMPL};
            bins mldsa_pwa       = {MLDSA_PWA};
            bins mldsa_pws       = {MLDSA_PWS};
            bins mlkem_ntt       = {MLKEM_NTT};
            bins mlkem_intt      = {MLKEM_INTT};
            bins mlkem_pwm       = {MLKEM_PWM};
            bins mlkem_pwm_accum = {MLKEM_PWM_ACCUM};
            bins mlkem_pwm_smpl  = {MLKEM_PWM_SMPL};
            bins mlkem_pwm_accum_smpl = {MLKEM_PWM_ACCUM_SMPL};
            bins mlkem_pwa       = {MLKEM_PWA};
            bins mlkem_pws       = {MLKEM_PWS};
        }

        // --- Opcode-level masking/shuffling bits ---
        opcode_masking_en_cp: coverpoint sca_opcode_masking_en;
        opcode_shuffling_en_cp: coverpoint sca_opcode_shuffling_en;

        // --- Splitter coverage ---
        sampler_splitter_en_cp: coverpoint sca_sampler_splitter_en;
        sampler_splitter_ready_cp: coverpoint sca_sampler_splitter_ready;
        skdecode_splitter_a_en_cp: coverpoint sca_skdecode_splitter_a_en;
        skdecode_splitter_b_en_cp: coverpoint sca_skdecode_splitter_b_en;
        decompress_splitter_en_cp: coverpoint sca_decompress_splitter_en;
        splitter_rand_reduced_cp: coverpoint sca_splitter_rand_reduced {
            bins not_reduced = {1'b0};
            bins reduced     = {1'b1};
        }

        // --- Recombine pipeline ---
        recombine_pipe_first_cp: coverpoint sca_recombine_en_pipe_first;
        recombine_pipe_last_cp:  coverpoint sca_recombine_en_pipe_last;

        // --- NTT[1] SIB read detect (bug 9 fix) ---
        ntt_sib_rd_detect_cp: coverpoint sca_ntt_sib_rd_detect_d1;

        // --- NTT[0]/NTT[1] mode coherence — when masked, must match ---
        ntt_modes_match_cp: coverpoint sca_ntt_modes_match;
        modes_matchXmasking: cross ntt_modes_match_cp, ntt_masking_en_cp {
            // Modes MUST match whenever masking is active (bug 2 invariant)
            illegal_bins masked_mode_mismatch =
                binsof(ntt_modes_match_cp) intersect {0} &&
                binsof(ntt_masking_en_cp)  intersect {1};
        }

        // --- MASKED_NTT_NOSHUF (bug 6 fix — NTT(c) sign) ---
        masked_noshuf_cp: coverpoint sca_masked_noshuf;
        noshufXmasking: cross sca_masked_noshuf, opcode_masking_en_cp;

        // --- Sampler mode (covers MASKED_REJB / MASKED_EXP_MASK / MASKED_CBD dispatch) ---
        sampler_mode_cp: coverpoint sca_sampler_mode {
            bins none      = {ABR_SAMPLER_NONE};
            bins mldsa_rej = {MLDSA_REJ_SAMPLER};
            bins mlkem_rej = {MLKEM_REJ_SAMPLER};
            bins exp_mask  = {ABR_EXP_MASK};
            bins rej_bnd   = {ABR_REJ_BOUNDED};
            bins sib       = {ABR_SAMPLE_IN_BALL};
            bins cbd       = {ABR_CBD_SAMPLER};
            bins shake256  = {ABR_SHAKE256};
            bins shake128  = {ABR_SHAKE128};
            bins sha3_512  = {ABR_SHA512};
            bins sha3_256  = {ABR_SHA256};
        }
        // Crosses isolate the *masked* dispatch path for each sampler mode
        masked_sampler_mode: cross sampler_mode_cp, opcode_masking_en_cp {
            // Only the maskable sampling modes are interesting
            ignore_bins not_maskable = binsof(sampler_mode_cp) intersect
                {ABR_SAMPLER_NONE, ABR_SHAKE256, ABR_SHAKE128, ABR_SHA512, ABR_SHA256,
                 ABR_SAMPLE_IN_BALL, MLDSA_REJ_SAMPLER, MLKEM_REJ_SAMPLER};
        }

        // --- Per-process splitter exercise — each splitter must fire in its algorithm ---
        sampler_splitterXkeygen:    cross sampler_splitter_en_cp,    sca_mldsa_keygen_cp;
        sampler_splitterXsigning:   cross sampler_splitter_en_cp,    sca_mldsa_signing_cp;
        sampler_splitterXmlkem:     cross sampler_splitter_en_cp,    sca_mlkem_keygen_cp;
        skdecode_splitter_aXsign:   cross skdecode_splitter_a_en_cp, sca_mldsa_signing_cp;
        skdecode_splitter_bXsign:   cross skdecode_splitter_b_en_cp, sca_mldsa_signing_cp;
        decompress_splitterXenc:    cross decompress_splitter_en_cp, sca_mlkem_encaps_cp;
        decompress_splitterXdec:    cross decompress_splitter_en_cp, sca_mlkem_decaps_cp;

        // --- Zeroize interaction with SCA components (safety) ---
        zeroize_cp_sca: coverpoint sca_zeroize;
        zeroizeXmasking:   cross zeroize_cp_sca, ntt_masking_en_cp;
        zeroizeXsplit:     cross zeroize_cp_sca, split_en_cp;
        zeroizeXrecombine: cross zeroize_cp_sca, recombine_en_cp;
        zeroizeXntt1:      cross zeroize_cp_sca, ntt1_enable_cp;

        // --- Cross coverage: masking × operation type ---
        maskingXntt_mode: cross ntt_masking_en_cp, ntt0_mode_cp {
            ignore_bins idle = binsof(ntt0_mode_cp.ntt_none);
        }

        // --- Cross coverage: masking × process (keygen/sign/encaps/decaps) ---
        maskingXmldsa_keygen: cross ntt_masking_en_cp, sca_mldsa_keygen_cp;
        maskingXmldsa_signing: cross ntt_masking_en_cp, sca_mldsa_signing_cp;
        maskingXmlkem_keygen: cross ntt_masking_en_cp, sca_mlkem_keygen_cp;
        maskingXmlkem_encaps: cross ntt_masking_en_cp, sca_mlkem_encaps_cp;
        maskingXmlkem_decaps: cross ntt_masking_en_cp, sca_mlkem_decaps_cp;

        // --- Cross coverage: shuffling × NTT active ---
        shufflingXmasking: cross ntt_shuffling_en_cp, opcode_masking_en_cp;

        // --- Cross coverage: recombine × operation ---
        recombineXmldsa_keygen:  cross recombine_en_cp, sca_mldsa_keygen_cp;   // Bug 4: s1 RECOMBINE in keygen
        recombineXmldsa_signing: cross recombine_en_cp, sca_mldsa_signing_cp;
        recombineXmlkem_keygen:  cross recombine_en_cp, sca_mlkem_keygen_cp;   // public-key gen recombine
        recombineXmlkem_encaps:  cross recombine_en_cp, sca_mlkem_encaps_cp;
        recombineXmlkem_decaps:  cross recombine_en_cp, sca_mlkem_decaps_cp;   // implicit-reject re-encrypt

        // --- Cross coverage: split × algorithm type ---
        splitXmldsa_keygen:  cross split_en_cp, sca_mldsa_keygen_cp;
        splitXmldsa_signing: cross split_en_cp, sca_mldsa_signing_cp;
        splitXmlkem_keygen:  cross split_en_cp, sca_mlkem_keygen_cp;
        splitXmlkem_encaps:  cross split_en_cp, sca_mlkem_encaps_cp;
        splitXmlkem_decaps:  cross split_en_cp, sca_mlkem_decaps_cp;

        // --- Cross coverage: NTT[1] active × recombine (must be mutually exclusive) ---
        // RTL invariant: ntt_enable[1] = ntt_masking_en_ctrl & !recombine_en_ctrl ? ...
        //                recombine_en  = ntt_mode[0] inside {MLDSA/MLKEM_RECOMBINE}
        // Both are driven by the same dispatch-time mode_ctrl, so they are strictly exclusive.
        ntt1Xrecombine: cross ntt1_enable_cp, recombine_en_cp {
            illegal_bins ntt1_during_recombine =
                binsof(ntt1_enable_cp) intersect {1} &&
                binsof(recombine_en_cp) intersect {1};
        }

        // --- Cross coverage: NTT[0] enable × masking ---
        ntt0Xmasking: cross ntt0_enable_cp, ntt_masking_en_cp;

        // --- Invariant: SCA components must not fire when opcode.masking_en=0 ---
        // Note: ntt_masking_en_ctrl = opcode.masking_en & ntt_en
        //       split_en           = opcode.masking_en & ~ntt_en
        //       So ntt_masking_en_ctrl and split_en are MUTUALLY EXCLUSIVE.
        //       The correct gating signal for "masking is requested" is opcode.masking_en.

        // NTT[1] must stay disabled when opcode.masking_en=0
        ntt1Xopcode_masking: cross ntt1_enable_cp, opcode_masking_en_cp {
            illegal_bins ntt1_on_masking_off = binsof(ntt1_enable_cp) intersect {1} &&
                                               binsof(opcode_masking_en_cp) intersect {0};
        }

        // Splitter must not fire when opcode.masking_en=0
        splitXopcode_masking: cross split_en_cp, opcode_masking_en_cp {
            illegal_bins split_on_masking_off = binsof(split_en_cp) intersect {1} &&
                                                binsof(opcode_masking_en_cp) intersect {0};
        }

        // Recombine must not fire when opcode.masking_en=0
        // (RECOMBINE opcode itself sets masking_en=1; recombine_en is derived from ntt_mode)
        recombineXopcode_masking: cross recombine_en_cp, opcode_masking_en_cp {
            illegal_bins recombine_on_masking_off = binsof(recombine_en_cp) intersect {1} &&
                                                    binsof(opcode_masking_en_cp) intersect {0};
        }

        // --- Per-splitter masking-off invariant ---
        // Each splitter instance (sampler / skdecode_a / skdecode_b / decompress) is
        // driven by local module logic, NOT directly by the top-level split_en.
        // The local enable is allowed only during a masked opcode → en_i=1 with
        // opcode.masking_en=0 indicates the local gate is broken.
        sampler_splitterXopcode_masking: cross sampler_splitter_en_cp, opcode_masking_en_cp {
            illegal_bins sampler_split_on_masking_off =
                binsof(sampler_splitter_en_cp) intersect {1} &&
                binsof(opcode_masking_en_cp) intersect {0};
        }
        skdecode_splitter_aXopcode_masking: cross skdecode_splitter_a_en_cp, opcode_masking_en_cp {
            illegal_bins skdecode_a_split_on_masking_off =
                binsof(skdecode_splitter_a_en_cp) intersect {1} &&
                binsof(opcode_masking_en_cp) intersect {0};
        }
        skdecode_splitter_bXopcode_masking: cross skdecode_splitter_b_en_cp, opcode_masking_en_cp {
            illegal_bins skdecode_b_split_on_masking_off =
                binsof(skdecode_splitter_b_en_cp) intersect {1} &&
                binsof(opcode_masking_en_cp) intersect {0};
        }
        decompress_splitterXopcode_masking: cross decompress_splitter_en_cp, opcode_masking_en_cp {
            illegal_bins decompress_split_on_masking_off =
                binsof(decompress_splitter_en_cp) intersect {1} &&
                binsof(opcode_masking_en_cp) intersect {0};
        }

        // VERIFY_RES poison-init coverage (abr_ctrl.sv:806-810). With hwclr = zeroize
        // only, the poison `~c~` survives any abort; covering both abort sources
        // proves the retention path was exercised.
        verify_abort_path_cp: coverpoint {sca_normcheck_invalid, sca_sigdecode_h_invalid}
                              iff (sca_clear_verify_valid) {
            bins by_normcheck         = {2'b10};
            bins by_sigdec_h          = {2'b01};
            illegal_bins both_aborts  = {2'b11};
        }

    endgroup

    // =========================================================================
    // Standard covergroup
    // =========================================================================

    covergroup abr_top_cov_grp @(posedge clk);
        reset_cp: coverpoint rst_b;
        debugUnlock_or_scan_mode_switch_cp: coverpoint debugUnlock_or_scan_mode_switch;

        mldsa_cmd_cp: coverpoint mldsa_cmd{
            illegal_bins illegal_values = {5, 6, 7};
        }
        mlkem_cmd_cp: coverpoint mlkem_cmd{
            illegal_bins illegal_values = {5, 6, 7};
        }
        zeroize_cp: coverpoint zeroize;
        ready_cp: coverpoint ready;
        mldsa_valid_cp: coverpoint mldsa_valid;
        mlkem_valid_cp: coverpoint mlkem_valid;
        mldsa_keygen_process_cp: coverpoint mldsa_keygen_process;
        mldsa_signing_process_cp: coverpoint mldsa_signing_process;
        mldsa_verifying_process_cp: coverpoint mldsa_verifying_process;
        mldsa_keygen_signing_process_cp: coverpoint mldsa_keygen_signing_process;

        mlkem_keygen_process_cp: coverpoint mlkem_keygen_process;
        mlkem_encaps_process_cp: coverpoint mlkem_encaps_process;
        mlkem_decaps_process_cp: coverpoint mlkem_decaps_process;
        mlkem_keygen_decaps_process_cp: coverpoint mlkem_keygen_decaps_process;

        error_flag_cp: coverpoint error_flag;
        skdecode_error_cp: coverpoint skdecode_error;
        verify_failure_cp: coverpoint verify_failure;
        normcheck_mode_sign_cp: coverpoint normcheck_mode {
            bins mode_0 = {1};
            bins mode_1 = {2};
            bins mode_2 = {4};
        }
        normcheck_mode_verify_cp: coverpoint normcheck_mode {
            bins mode_0 = {1};
        }
        normcheck_failure_cp: coverpoint normcheck_failure;
        makehint_failure_cp: coverpoint makehint_failure;
        invalid_hint_cp: coverpoint invalid_hint;
        clear_decaps_valid_cp: coverpoint abr_top.abr_ctrl_inst.clear_decaps_valid;
        encaps_input_check_failure_cp: coverpoint abr_top.abr_ctrl_inst.encaps_input_check_failure;
        decaps_input_check_failure_cp: coverpoint abr_top.abr_ctrl_inst.decaps_input_check_failure;

        stream_msg_strobe_cp: coverpoint abr_top.abr_ctrl_inst.stream_msg_strobe {
            bins one_byte = {4'b0001};
            bins two_bytes = {4'b0011};
            bins three_bytes = {4'b0111};
            bins four_bytes = {4'b1111};
        }

        mldsa_sw_cmd_cp: coverpoint mldsa_sw_cmd {
            illegal_bins illegal_values = {5, 6, 7};
        }

        mldsa_cmdXready: cross mldsa_sw_cmd_cp, ready_cp;

        zeroizeXerror: cross zeroize_cp, error_flag_cp;
        readyXzeroize: cross ready_cp, zeroize_cp;
        mldsa_validXzeroize: cross mldsa_valid_cp, zeroize_cp;
        mlkem_validXzeroize: cross mlkem_valid_cp, zeroize_cp;
        errorXmldsa_signing: cross error_flag_cp, mldsa_signing_process_cp;

        normcheckXsigning_failure: cross normcheck_mode_sign_cp, normcheck_failure_cp iff (mldsa_signing_process | mldsa_keygen_signing_process);
        normcheckXverifying_failure: cross normcheck_mode_verify_cp, normcheck_failure_cp iff (mldsa_verifying_process);

        `ifdef CALIPTRA
        kv_mldsa_seed_data_present_cp: coverpoint kv_mldsa_seed_data_present;
        mldsa_keygenXkv: cross mldsa_keygen_process_cp, kv_mldsa_seed_data_present_cp;

        kv_mlkem_seed_data_present_cp: coverpoint kv_mlkem_seed_data_present;
        mlkem_keygenXkv: cross mlkem_keygen_process_cp, kv_mlkem_seed_data_present_cp;
        mlkem_keygen_decapsXkv: cross mlkem_keygen_decaps_process_cp, kv_mlkem_seed_data_present_cp;

        kv_mlkem_msg_data_present_cp: coverpoint kv_mlkem_msg_data_present;
        mlkem_encapsXkv: cross mlkem_encaps_process_cp, kv_mlkem_msg_data_present_cp;

        mldsa_seed_zero_error_cp: coverpoint mldsa_seed_zero_error;
        mlkem_seed_zero_error_cp: coverpoint mlkem_seed_zero_error;
        mlkem_msg_zero_error_cp:  coverpoint mlkem_msg_zero_error;

        mldsa_seed_zero_errorXcmd: cross mldsa_seed_zero_error_cp, mldsa_cmd_cp {
            ignore_bins illegal_crosses = binsof(mldsa_cmd_cp.illegal_values);
            ignore_bins irrelevant_cmds = binsof(mldsa_cmd_cp) intersect {0, MLDSA_SIGN, MLDSA_VERIFY};
        }
        mlkem_seed_zero_errorXcmd: cross mlkem_seed_zero_error_cp, mlkem_cmd_cp {
            ignore_bins illegal_crosses = binsof(mlkem_cmd_cp.illegal_values);
            ignore_bins irrelevant_cmds = binsof(mlkem_cmd_cp) intersect {0, MLKEM_ENCAPS, MLKEM_DECAPS};
        }
        mlkem_msg_zero_errorXcmd:  cross mlkem_msg_zero_error_cp, mlkem_cmd_cp {
            ignore_bins illegal_crosses = binsof(mlkem_cmd_cp.illegal_values);
            ignore_bins irrelevant_cmds = binsof(mlkem_cmd_cp) intersect {0, MLKEM_KEYGEN, MLKEM_DECAPS, MLKEM_KEYGEN_DEC};
        }

        pcr_sign_cp: coverpoint pcr_sign_mode;
        pcr_sign_input_invalid_cp: coverpoint pcr_sign_input_invalid;

        readyXpcr_sign: cross ready_cp, pcr_sign_cp;
        pcr_signXmldsa_cmd: cross pcr_sign_cp, mldsa_cmd_cp {
            ignore_bins illegal_crosses = binsof(mldsa_cmd_cp.illegal_values);
        }
        zeroizeXpcr_sign: cross zeroize_cp, pcr_sign_cp;

        errorXmldsa_keygen: cross error_flag_cp, mldsa_keygen_process_cp; // due to pcr_sign_input_invalid
        errorXmldsa_verifying: cross error_flag_cp, mldsa_verifying_process_cp; // due to pcr_sign_input_invalid
        errorXmldsa_keygen_signing: cross error_flag_cp, mldsa_keygen_signing_process_cp; // due to pcr_sign_input_invalid
        
        normcheck_fail_signXpcr_sign: cross normcheck_mode_sign_cp, normcheck_failure_cp iff (pcr_process);
        makehint_failXpcr_sign: cross makehint_failure_cp, pcr_sign_cp;
        `endif

        // External MU mode coverage
        external_mu_mode_cp: coverpoint external_mu_mode;
        stream_msg_mode_cp: coverpoint stream_msg_mode;
        stream_msg_ip_cp: coverpoint stream_msg_ip;

        // External MU crossed with operations
        external_muXsigning: cross external_mu_mode_cp, mldsa_signing_process_cp {
            ignore_bins no_ext_mu_signing = binsof(external_mu_mode_cp) intersect {0} && binsof(mldsa_signing_process_cp) intersect {1};
            ignore_bins ext_mu_no_signing = binsof(external_mu_mode_cp) intersect {1} && binsof(mldsa_signing_process_cp) intersect {0};
        }
        external_muXkeygen_signing: cross external_mu_mode_cp, mldsa_keygen_signing_process_cp;
        external_muXverifying: cross external_mu_mode_cp, mldsa_verifying_process_cp;

        // Stream msg crossed with operations
        stream_msgXsigning: cross stream_msg_mode_cp, mldsa_signing_process_cp;
        stream_msgXkeygen_signing: cross stream_msg_mode_cp, mldsa_keygen_signing_process_cp;
        stream_msgXverifying: cross stream_msg_mode_cp, mldsa_verifying_process_cp;

        // Zeroize during stream msg in-progress
        zeroizeXstream_msg_ip: cross zeroize_cp, stream_msg_ip_cp;

        // Makehint failure during signing (h rejection path)
        makehintXsigning_failure: cross makehint_failure_cp, mldsa_signing_process_cp;
        makehintXkeygen_signing_failure: cross makehint_failure_cp, mldsa_keygen_signing_process_cp;

    endgroup




    // SIGN Z encoding
    localparam int NUM_ENC  = 4;
    localparam int GAMMA1   = 19;
    localparam int REG_SIZE = 23;
    localparam int MLDSA_GAMMA1_RANGE = 2**GAMMA1;
    localparam int MLDSA_Q  = 8380417;

    logic [(NUM_ENC*2)-1:0] eq_flags;
    logic [(NUM_ENC*2)-1:0] less_flags;
    logic [(NUM_ENC*2)-1:0] greater_flags;
    logic enc_unit_equal;
    logic enc_unit_less;
    logic enc_unit_greater;

    genvar sig_enc_i;
    generate
        for(sig_enc_i = 0; sig_enc_i < NUM_ENC; sig_enc_i++) begin : enc_loop
        // For the upper instance
        assign eq_flags[sig_enc_i*2]   = (abr_top.sigencode_z_inst.enc_unit[sig_enc_i].upper_encode.data_i == MLDSA_GAMMA1_RANGE);
        assign less_flags[sig_enc_i*2] = (abr_top.sigencode_z_inst.enc_unit[sig_enc_i].upper_encode.data_i <  MLDSA_GAMMA1_RANGE);
        assign greater_flags[sig_enc_i*2] = (abr_top.sigencode_z_inst.enc_unit[sig_enc_i].upper_encode.data_i > MLDSA_GAMMA1_RANGE);
        
        // For the lower instance
        assign eq_flags[sig_enc_i*2+1]   = (abr_top.sigencode_z_inst.enc_unit[sig_enc_i].lower_encode.data_i == MLDSA_GAMMA1_RANGE);
        assign less_flags[sig_enc_i*2+1] = (abr_top.sigencode_z_inst.enc_unit[sig_enc_i].lower_encode.data_i <  MLDSA_GAMMA1_RANGE);
        assign greater_flags[sig_enc_i*2+1] = (abr_top.sigencode_z_inst.enc_unit[sig_enc_i].lower_encode.data_i > MLDSA_GAMMA1_RANGE);
        end
    endgenerate

    // OR-reduce the flags: if any instance meets the condition, the corresponding signal is 1.
    assign enc_unit_equal   = (|eq_flags) & (abr_top.sigencode_z_inst.state != abr_top.sigencode_z_inst.SIGENCODE_IDLE);
    assign enc_unit_less    = (|less_flags) & (abr_top.sigencode_z_inst.state != abr_top.sigencode_z_inst.SIGENCODE_IDLE);
    assign enc_unit_greater = (|greater_flags) & (abr_top.sigencode_z_inst.state != abr_top.sigencode_z_inst.SIGENCODE_IDLE);
    // Sign_z to cover the aggregated conditions
    covergroup mldsa_sign_z_enc_agg_cg @(posedge clk);
        coverpoint enc_unit_equal {
            bins hit = {1'b1};
        }
        coverpoint enc_unit_less {
            bins hit = {1'b1};
        }
        coverpoint enc_unit_greater {
            bins hit = {1'b1};
        }
    endgroup

    // The FSM cases are: 'h0, 'h1, 'h2, MLDSA_Q-1, MLDSA_Q-2, and default.
    logic [(NUM_ENC*2)-1:0] skenc_state0_flags;
    logic [(NUM_ENC*2)-1:0] skenc_state1_flags;
    logic [(NUM_ENC*2)-1:0] skenc_state2_flags;
    logic [(NUM_ENC*2)-1:0] skenc_state_mq1_flags;
    logic [(NUM_ENC*2)-1:0] skenc_state_mq2_flags;
    logic skenc_state0_agg, skenc_state1_agg, skenc_state2_agg, skenc_state_mq1_agg, skenc_state_mq2_agg;

    genvar sk_enc_i;
    generate
    for (sk_enc_i = 0; sk_enc_i < NUM_ENC; sk_enc_i++) begin : sk_enc_loop
        // For mem_a_rd_data element
        assign skenc_state0_flags[sk_enc_i*2]    = (abr_top.skencode_inst.mem_a_rd_data[sk_enc_i] == 'h0);
        assign skenc_state1_flags[sk_enc_i*2]    = (abr_top.skencode_inst.mem_a_rd_data[sk_enc_i] == 'h1);
        assign skenc_state2_flags[sk_enc_i*2]    = (abr_top.skencode_inst.mem_a_rd_data[sk_enc_i] == 'h2);
        assign skenc_state_mq1_flags[sk_enc_i*2] = (abr_top.skencode_inst.mem_a_rd_data[sk_enc_i] == MLDSA_Q - 1);
        assign skenc_state_mq2_flags[sk_enc_i*2] = (abr_top.skencode_inst.mem_a_rd_data[sk_enc_i] == MLDSA_Q - 2);
        // For mem_b_rd_data element
        assign skenc_state0_flags[sk_enc_i*2+1]    = (abr_top.skencode_inst.mem_b_rd_data[sk_enc_i] == 'h0);
        assign skenc_state1_flags[sk_enc_i*2+1]    = (abr_top.skencode_inst.mem_b_rd_data[sk_enc_i] == 'h1);
        assign skenc_state2_flags[sk_enc_i*2+1]    = (abr_top.skencode_inst.mem_b_rd_data[sk_enc_i] == 'h2);
        assign skenc_state_mq1_flags[sk_enc_i*2+1] = (abr_top.skencode_inst.mem_b_rd_data[sk_enc_i] == MLDSA_Q - 1);
        assign skenc_state_mq2_flags[sk_enc_i*2+1] = (abr_top.skencode_inst.mem_b_rd_data[sk_enc_i] == MLDSA_Q - 2);
    end
    endgenerate

    // OR-reduce each set of flags and ensure the FSM is not in IDLE.
    // (Assuming abr_top.skencode_inst.state and its IDLE constant are accessible.)
    assign skenc_state0_agg    = (|skenc_state0_flags)    & (abr_top.skencode_inst.main_state != abr_top.skencode_inst.SKENC_IDLE);
    assign skenc_state1_agg    = (|skenc_state1_flags)    & (abr_top.skencode_inst.main_state != abr_top.skencode_inst.SKENC_IDLE);
    assign skenc_state2_agg    = (|skenc_state2_flags)    & (abr_top.skencode_inst.main_state != abr_top.skencode_inst.SKENC_IDLE);
    assign skenc_state_mq1_agg = (|skenc_state_mq1_flags) & (abr_top.skencode_inst.main_state != abr_top.skencode_inst.SKENC_IDLE);
    assign skenc_state_mq2_agg = (|skenc_state_mq2_flags) & (abr_top.skencode_inst.main_state != abr_top.skencode_inst.SKENC_IDLE);

    // Now create a covergroup that samples these aggregated flags.
    covergroup mldsa_skencode_agg_cg @(posedge clk);
        coverpoint skenc_state0_agg    { bins hit = {1'b1}; }
        coverpoint skenc_state1_agg    { bins hit = {1'b1}; }
        coverpoint skenc_state2_agg    { bins hit = {1'b1}; }
        coverpoint skenc_state_mq1_agg { bins hit = {1'b1}; }
        coverpoint skenc_state_mq2_agg { bins hit = {1'b1}; }
    endgroup
    
    `ifdef CALIPTRA
    covergroup abr_ocp_lock_cov_grp @(posedge clk);

        ocp_lock_in_progress_cp: coverpoint ocp_lock_in_progress;

        kv_read_entry_mldsa_cp: coverpoint {kv_mldsa_seed_data_present, kv_read_ctrl_reg.read_entry } 
        iff (mldsa_cmd inside {MLDSA_KEYGEN, MLDSA_KEYGEN_SIGN}) {
            bins fw = {1'b0, [0:$]};
            bins lower_slots = {1'b1, [0:15]};
            bins upper_slots = {1'b1, [16:22]};
            bins slot_23 = {1'b1, 23};
        }

        kv_read_entry_0_cp: coverpoint {kv_write_metrics.kv_data0_present, kv_write_metrics.kv_data0_entry} 
        iff (mlkem_cmd inside {MLKEM_KEYGEN_DEC}) {
            bins fw = {1'b0, [0:$]};
            bins lower_slots = {1'b1, [0:15]};
            bins upper_slots = {1'b1, [16:22]};
            bins slot_23 = {1'b1, 23};
        }

        kv_read_entry_1_cp: coverpoint {kv_write_metrics.kv_data1_present, kv_write_metrics.kv_data1_entry} 
        iff (mlkem_cmd inside {MLKEM_ENCAPS}) {
            bins fw = {1'b0, [0:$]};
            bins lower_slots = {1'b1, [0:15]};
            bins upper_slots = {1'b1, [16:22]};
            bins slot_23 = {1'b1, 23};
        }

        kv_write_entry_cp: coverpoint {kv_write_ctrl_reg.write_en, kv_write_metrics.kv_write_entry} 
        iff (mlkem_encaps_process | mlkem_keygen_decaps_process) {
            bins fw = {1'b0, [0:$]};
            bins lower_slots = {1'b1, [0:15]};
            bins upper_slots = {1'b1, [16:22]};
            bins slot_23 = {1'b1, 23};
        }

        ocp_lock_X_kv_read_entry0: cross ocp_lock_in_progress_cp, kv_write_entry_cp, kv_read_entry_0_cp;
        ocp_lock_X_kv_read_entry1: cross ocp_lock_in_progress_cp, kv_write_entry_cp, kv_read_entry_1_cp;
        ocp_lock_X_kv_read_entry_mldsa: cross ocp_lock_in_progress_cp, kv_read_entry_mldsa_cp;
    endgroup  
    abr_ocp_lock_cov_grp abr_ocp_lock_cov_grp1 = new();
    `endif

    // Instantiate the covergroups
    mldsa_skencode_agg_cg mldsa_skencode_agg_cov = new();
    mldsa_sign_z_enc_agg_cg mldsa_sign_z_enc_agg_cov_grp1 = new();

    abr_top_cov_grp abr_top_cov_grp1 = new();
    abr_sca_cov_grp abr_sca_cov_grp1 = new();

endinterface

`endif
