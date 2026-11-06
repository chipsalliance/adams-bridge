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

module fv_abr_ctrl_kv_write_covers
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
    input kv_write_t                                                    po_kv_write,
    input kv_wr_resp_t                                                  pi_kv_wr_resp,
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


    cover_kv_write_en: cover property (disable iff (!pi_rst_b) po_kv_write.write_en);

    cover_kv_write_entry: cover property (disable iff (!pi_rst_b) po_kv_write.write_entry == 'h10);

    cover_kv_write_offset: cover property (disable iff (!pi_rst_b) po_kv_write.write_offset == SHAREDKEY_NUM_DWORDS-1);

    cover_kv_write_data: cover property (disable iff (!pi_rst_b) po_kv_write.write_data == 32'd100);

    cover_kv_write_dest_valid: cover property (disable iff (!pi_rst_b) po_kv_write.write_dest_valid == 'd8);

    cover_kv_write_en_and_dest_valid: cover property (disable iff (!pi_rst_b) po_kv_write.write_en && po_kv_write.write_dest_valid == 'd4);

    cover_arc_rw_done: cover property (disable iff (!pi_rst_b) abr_ctrl.kv_mlkem_sharedkey_write_inst.kv_dest_write_fsm.arc_KV_RW_KV_DONE);

    cover_write_last: cover property (disable iff (!pi_rst_b) abr_ctrl.kv_mlkem_sharedkey_write_inst.kv_dest_write_fsm.write_last);

    cover_kv_dest_data_avail: cover property (disable iff (!pi_rst_b) abr_ctrl.kv_dest_data_avail);

    cover_dest_keyvault: cover property (disable iff (!pi_rst_b) abr_ctrl.dest_keyvault);


endmodule
