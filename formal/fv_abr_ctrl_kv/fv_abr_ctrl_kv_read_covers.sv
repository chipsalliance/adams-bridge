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


module fv_abr_ctrl_kv_read_covers
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
)(
    ////////////////////////////
    // Input / Output signals //
    ////////////////////////////
    input logic                                                         pi_clk,
    input logic                                                         pi_rst_b,
    input logic                                                         po_zeroize,

    input abr_reg__in_t                                                 po_abr_reg_hwif_in_o,
    input abr_reg__out_t                                                pi_abr_reg_hwif_out_i,


    // KV interface
    input kv_read_t [2:0]                                               po_kv_read,
    input kv_rd_resp_t [2:0]                                            pi_kv_rd_resp,
    //PCR Signing
    input pcr_signing_t                                                 pi_pcr_signing_data,

    input logic                                                         pi_debugUnlock_or_scan_mode_switch,
    input logic                                                         po_busy_o,

    //Interrupts
    input logic                                                         po_error_intr,
    input logic                                                         po_notif_intr
);

    // Define default clock
    default clocking default_clk @(posedge pi_clk); endclocking

    //should be asserted when kv_fsm is in the KV_DONE state, after the data chunks have been read in KV_RW state or padded in KV_PAD state (1 cycle after last is asserted)
    // or asserted 1 cycle after the offset is equal to the number of words for that client
    property kv_mldsa_seed_done;
        abr_ctrl.kv_mldsa_seed_done && (abr_ctrl.kv_mldsa_seed_error == KV_SUCCESS)
    endproperty
    cover_kv_mldsa_seed_done: cover property(disable iff(!pi_rst_b || po_zeroize) kv_mldsa_seed_done);


    property kv_mldsa_seed_write_en;
        abr_ctrl.kv_mldsa_seed_write_en
    endproperty
    cover_kv_mldsa_seed_write_en: cover property(disable iff(!pi_rst_b || po_zeroize) kv_mldsa_seed_write_en);


    property kv_mlkem_seed_done;
        abr_ctrl.kv_mlkem_seed_done && (abr_ctrl.kv_mlkem_seed_error == KV_SUCCESS)
    endproperty
    cover_kv_mlkem_seed_done: cover property(disable iff(!pi_rst_b || po_zeroize) kv_mlkem_seed_done);


    property kv_mlkem_msg_done;
        abr_ctrl.kv_mlkem_msg_done && (abr_ctrl.kv_mlkem_msg_error == KV_SUCCESS)
    endproperty
    cover_kv_mlkem_msg_done: cover property(disable iff(!pi_rst_b || po_zeroize) kv_mlkem_msg_done);


    property kv_mldsa_seed_read_offset;
        po_kv_read[0].read_offset == SEED_NUM_DWORDS-1 && (abr_ctrl.kv_mldsa_seed_error == KV_SUCCESS)
    endproperty
    cover_kv_mldsa_seed_read_offset: cover property(disable iff(!pi_rst_b || po_zeroize) kv_mldsa_seed_read_offset);


    property kv_mlkem_seed_read_offset;
        po_kv_read[1].read_offset == (2*SEED_NUM_DWORDS)-1 && (abr_ctrl.kv_mlkem_seed_error == KV_SUCCESS)
    endproperty
    cover_kv_mlkem_seed_read_offset: cover property(disable iff(!pi_rst_b || po_zeroize) kv_mlkem_seed_read_offset);


    property kv_mlkem_msg_read_offset;
       po_kv_read[2].read_offset == MLKEM_MSG_MEM_NUM_DWORDS-1 && (abr_ctrl.kv_mlkem_msg_error == KV_SUCCESS)
    endproperty
    cover_kv_mlkem_msg_read_offset: cover property(disable iff(!pi_rst_b || po_zeroize) kv_mlkem_msg_read_offset);


    property kv_mlkem_seed_read_en_and_busy;
        pi_abr_reg_hwif_out_i.kv_mlkem_seed_rd_ctrl.read_en && po_busy_o
    endproperty
    cover_kv_mlkem_seed_read_en_and_busy: cover property(disable iff(!pi_rst_b || po_zeroize) kv_mlkem_seed_read_en_and_busy);


    cover_mldsa_valid_twice: cover property(disable iff(!pi_rst_b) $rose(abr_ctrl.mldsa_valid_reg)[->2]);
    cover_mlkem_valid_twice: cover property(disable iff(!pi_rst_b) $rose(abr_ctrl.mlkem_valid_reg)[->2]);
    cover_mlkem_then_mldsa_valid: cover property(disable iff(!pi_rst_b) $rose(abr_ctrl.mlkem_valid_reg) ##1 $rose(abr_ctrl.mldsa_valid_reg)[->1]);
    cover_mldsa_then_mlkem_valid: cover property(disable iff(!pi_rst_b) $rose(abr_ctrl.mldsa_valid_reg) ##1 $rose(abr_ctrl.mlkem_valid_reg)[->1]);


    property kv_mldsa_seed_mlkem_seed_mlkem_msg_consecutive_requests;
        pi_abr_reg_hwif_out_i.kv_mldsa_seed_rd_ctrl.read_en ##[15:$]
        pi_abr_reg_hwif_out_i.kv_mlkem_seed_rd_ctrl.read_en ##[15:$]
        pi_abr_reg_hwif_out_i.kv_mlkem_msg_rd_ctrl.read_en
    endproperty
    cover_kv_mldsa_seed_mlkem_seed_mlkem_msg_consecutive_requests: cover property(disable iff(!pi_rst_b || po_zeroize) kv_mldsa_seed_mlkem_seed_mlkem_msg_consecutive_requests);


    cover_kv_mldsa_seed_done_twice: cover property(disable iff(!pi_rst_b) $rose(abr_ctrl.kv_mldsa_seed_done && (abr_ctrl.kv_mldsa_seed_error == KV_SUCCESS))[->2]);
    cover_kv_mlkem_seed_done_twice: cover property(disable iff(!pi_rst_b) $rose(abr_ctrl.kv_mlkem_seed_done && (abr_ctrl.kv_mlkem_seed_error == KV_SUCCESS))[->2]);
    cover_kv_mlkem_msg_done_twice: cover property(disable iff(!pi_rst_b) $rose(abr_ctrl.kv_mlkem_msg_done && (abr_ctrl.kv_mlkem_msg_error == KV_SUCCESS))[->2]);

endmodule
