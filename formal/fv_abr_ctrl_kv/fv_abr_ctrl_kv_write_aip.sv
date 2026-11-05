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
//#$includes

//$#//

module fv_abr_ctrl_kv_write_aip
    //#$imports
    import abr_params_pkg::*;
    import abr_sampler_pkg::*;
    import abr_ctrl_pkg::*;
    import abr_sha3_pkg::*;
    import abr_reg_pkg::*;
    import ntt_defines_pkg::*;
    import compress_defines_pkg::*;
    import decompress_defines_pkg::*;
    import kv_defines_pkg::*;
    //$#//
#(
    parameter SRAM_LATENCY = 1

) (
    //#$ports
    input logic                                        pi_clk,
    input logic                                        pi_rst_b,
    input logic                                        po_zeroize,
    input abr_reg__in_t                                po_abr_reg_hwif_in_o,
    input abr_reg__out_t                               pi_abr_reg_hwif_out_i,
    input kv_write_t                                   po_kv_write,
    input kv_wr_resp_t                                 pi_kv_wr_resp,
    input logic                                        pi_ocp_lock_in_progress,
    input logic                                        po_busy_o
    //$#//
);

    // Define default clock
    default clocking default_clk @(posedge pi_clk); endclocking

    ////////////////////////////////////////////////////////////////////////////////////////////////MLKEM mode//////////////////////////////////////////////////////////////////////////////////////////////////
    ///////////////////////////////////////////////////////////////////////Modeling of state machine and write rules and equivalence checks/////////////////////////////////////////////////////////////////////

    // Aux logic to model KV MLKEM sharedkey client write state machine
    typedef enum logic [1:0] {
        fv_st_idle_type,
        fv_st_write_type,
        fv_st_done_type
    } fvFsmState;

    fvFsmState                              fv_kv_mlkem_sharedkey_cs, fv_kv_mlkem_sharedkey_ns;
    logic [$clog2(SHAREDKEY_NUM_DWORDS):0]      fv_kv_mlkem_sharedkey_words_cntr;
    logic                                       fv_kv_mlkem_sharedkey_write_rules_fail;
    logic                                       fv_kv_mlkem_sharedkey_write_start;
    logic                                       fv_kv_mlkem_sharedkey_write_rules_allow;
    logic                                       fv_kv_mlkem_sharedkey_complete;
    logic                                       fv_kv_mlkem_sharedkey_done;
    logic                                       fv_kv_mlkem_sharedkey_we;
    logic                                       fv_kv_mlkem_sharedkey_ready;
    logic                                       fv_mlkem_seed_in_std_slot;
    logic                                       fv_mlkem_msg_in_std_slot;
    logic                                       fv_kv_dest_in_std_slot;
    logic                                       fv_mlkem_seed_in_lock_slot;
    logic                                       fv_mlkem_msg_in_lock_slot;
    logic                                       fv_kv_dest_in_lock_slot;

    always_ff @(posedge pi_clk or negedge pi_rst_b) begin: fv_kv_mlkem_sharedkey_state_update
        if (!pi_rst_b || po_zeroize) begin
            fv_kv_mlkem_sharedkey_cs <= fv_st_idle_type;
        end else begin
            fv_kv_mlkem_sharedkey_cs <= fv_kv_mlkem_sharedkey_ns;
        end
    end

    //KV is divided into three regions: standard slots, lock slots, and a key release slot
    //No client can write to the OCP_LOCK_KEY_RELASE_KV_SLOT except AES
    //If either of the KV source registers are in the standard slot range - the dest must be in the standard slot range also
    //If either of the KV source registers are in the lock slot range - the dest must also be in the lock slot range
    //If AES is doing decrypt ecb operation and the data0 entry is OCP_LOCK_RT_OBF_KEY_KV_SLOT then the dest must be OCP_LOCK_KEY_RELEASE_KV_SLOT
    //NOTE: AES is disabled

    assign fv_mlkem_seed_in_std_slot    = abr_ctrl.kv_mlkem_seed_data_present && ((pi_abr_reg_hwif_out_i.kv_mlkem_seed_rd_ctrl.read_entry >= KV_STANDARD_SLOT_LOW)
                                                                                    && (pi_abr_reg_hwif_out_i.kv_mlkem_seed_rd_ctrl.read_entry <= KV_STANDARD_SLOT_HI));
    assign fv_mlkem_msg_in_std_slot     = abr_ctrl.kv_mlkem_msg_data_present && ((pi_abr_reg_hwif_out_i.kv_mlkem_msg_rd_ctrl.read_entry >= KV_STANDARD_SLOT_LOW)
                                                                                    && (pi_abr_reg_hwif_out_i.kv_mlkem_msg_rd_ctrl.read_entry <= KV_STANDARD_SLOT_HI));
    assign fv_kv_dest_in_std_slot       = (pi_abr_reg_hwif_out_i.kv_mlkem_sharedkey_wr_ctrl.write_entry >= KV_STANDARD_SLOT_LOW)
                                            && (pi_abr_reg_hwif_out_i.kv_mlkem_sharedkey_wr_ctrl.write_entry <= KV_STANDARD_SLOT_HI);

    assign fv_mlkem_seed_in_lock_slot   = abr_ctrl.kv_mlkem_seed_data_present && ((pi_abr_reg_hwif_out_i.kv_mlkem_seed_rd_ctrl.read_entry >= KV_OCP_LOCK_SLOT_LOW)
                                                                                    && (pi_abr_reg_hwif_out_i.kv_mlkem_seed_rd_ctrl.read_entry <= KV_OCP_LOCK_SLOT_HI));
    assign fv_mlkem_msg_in_lock_slot    = abr_ctrl.kv_mlkem_msg_data_present && ((pi_abr_reg_hwif_out_i.kv_mlkem_msg_rd_ctrl.read_entry >= KV_OCP_LOCK_SLOT_LOW)
                                                                                    && (pi_abr_reg_hwif_out_i.kv_mlkem_msg_rd_ctrl.read_entry <= KV_OCP_LOCK_SLOT_HI));
    assign fv_kv_dest_in_lock_slot      = (pi_abr_reg_hwif_out_i.kv_mlkem_sharedkey_wr_ctrl.write_entry >= KV_OCP_LOCK_SLOT_LOW)
                                            && (pi_abr_reg_hwif_out_i.kv_mlkem_sharedkey_wr_ctrl.write_entry <= KV_OCP_LOCK_SLOT_HI);

    assign fv_kv_mlkem_sharedkey_write_rules_fail = pi_ocp_lock_in_progress && (pi_abr_reg_hwif_out_i.kv_mlkem_sharedkey_wr_ctrl.write_entry == OCP_LOCK_KEY_RELEASE_KV_SLOT)
                                                        || (pi_ocp_lock_in_progress && (fv_mlkem_seed_in_std_slot || fv_mlkem_msg_in_std_slot) && !fv_kv_dest_in_std_slot)
                                                            || (pi_ocp_lock_in_progress && (fv_mlkem_seed_in_lock_slot || fv_mlkem_msg_in_lock_slot) && !fv_kv_dest_in_lock_slot);

    //No need to pipeline the start as it will be long stabilized before the write operation
    assign fv_kv_mlkem_sharedkey_write_start = (abr_ctrl.mlkem_encaps_done || abr_ctrl.mlkem_decaps_done) && pi_abr_reg_hwif_out_i.kv_mlkem_sharedkey_wr_ctrl.write_en;

    always_ff @(posedge pi_clk or negedge pi_rst_b) begin: fv_kv_mlkem_sharedkey_conditions_update
        if (!pi_rst_b || po_zeroize) begin
            fv_kv_mlkem_sharedkey_write_rules_allow  <= '0;
        end
        else begin
            fv_kv_mlkem_sharedkey_write_rules_allow  <= !fv_kv_mlkem_sharedkey_write_rules_fail;
        end
    end


    assign fv_kv_mlkem_sharedkey_complete = (fv_kv_mlkem_sharedkey_words_cntr == SHAREDKEY_NUM_DWORDS);

    //Aux logic to count the number of words received from KV to know when to terminate the state machine if maximum has reached
    always_ff @(posedge pi_clk or negedge pi_rst_b) begin: fv_kv_mlkem_sharedkey_cntr_update
        if (!pi_rst_b || po_zeroize) begin
            fv_kv_mlkem_sharedkey_words_cntr <= 'd0;
        end
        //RTL kv_fsm also resets its offset on abort (offset_rst includes abort_i in KV_RW)
        else if(fv_kv_mlkem_sharedkey_complete || ((fv_kv_mlkem_sharedkey_cs == fv_st_write_type) && pi_kv_wr_resp.error)) begin
            fv_kv_mlkem_sharedkey_words_cntr <= 'd0;
        end else if (fv_kv_mlkem_sharedkey_ns == fv_st_write_type) begin
            fv_kv_mlkem_sharedkey_words_cntr <= fv_kv_mlkem_sharedkey_words_cntr + 'd1;
        end
    end

    //Aux logic for the KV state machine to model the done signal
    always_comb begin: fv_kv_mlkem_sharedkey_fsm
        fv_kv_mlkem_sharedkey_ns     = fv_kv_mlkem_sharedkey_cs;
        fv_kv_mlkem_sharedkey_done   = 1'b0;
        fv_kv_mlkem_sharedkey_we     = 1'b0;
        unique case (fv_kv_mlkem_sharedkey_cs)
            fv_st_idle_type: begin
                if (fv_kv_mlkem_sharedkey_write_start) begin
                    if (fv_kv_mlkem_sharedkey_write_rules_allow) begin
                        fv_kv_mlkem_sharedkey_ns = fv_st_write_type;
                    end else begin
                        fv_kv_mlkem_sharedkey_ns = fv_st_done_type;
                    end
                end
            end
            fv_st_write_type: begin
                fv_kv_mlkem_sharedkey_we = 1'b1;
                //RTL kv_fsm aborts the transfer on a KV write error (abort_i = kv_resp.error),
                //jumping to KV_DONE on that beat regardless of how many dwords were written
                if (pi_kv_wr_resp.error || fv_kv_mlkem_sharedkey_complete) begin
                    fv_kv_mlkem_sharedkey_ns = fv_st_done_type;
                end
            end
            fv_st_done_type: begin
                fv_kv_mlkem_sharedkey_done = 1'b1;
                fv_kv_mlkem_sharedkey_ns = fv_st_idle_type;
            end
            default: begin
                fv_kv_mlkem_sharedkey_ns = fv_st_idle_type;
            end
        endcase
    end


    //Aux logic to model and latch kv_mlkem_sharedkey error responses
    logic                 fv_kv_mlkem_sharedkey_error;
    kv_error_code_e       fv_kv_mlkem_sharedkey_error_code;

    assign fv_kv_mlkem_sharedkey_error = ((fv_kv_mlkem_sharedkey_cs == fv_st_write_type) && pi_kv_wr_resp.error) || (fv_kv_mlkem_sharedkey_write_rules_fail && fv_kv_mlkem_sharedkey_write_start);

    always_ff @(posedge pi_clk or negedge pi_rst_b) begin: fv_reg_kv_mlkem_sharedkey_error
        if (!pi_rst_b || po_zeroize) begin
            fv_kv_mlkem_sharedkey_error_code <= KV_SUCCESS;
        end else if (fv_kv_mlkem_sharedkey_error) begin
            fv_kv_mlkem_sharedkey_error_code <= KV_WRITE_FAIL;
        end
    end

    //Model ready signal for mlkem_sharedkey kv client
    assign fv_kv_mlkem_sharedkey_ready = (fv_kv_mlkem_sharedkey_cs == fv_st_idle_type);


    //Checking equivalence of modeled mlkem_sharedkey_done and RTL
    property kv_mlkem_sharedkey_done_eq;
        abr_ctrl.kv_mlkem_sharedkey_done == fv_kv_mlkem_sharedkey_done;
    endproperty
    assert_kv_mlkem_sharedkey_done_eq: assert property (disable iff (!pi_rst_b | po_zeroize) kv_mlkem_sharedkey_done_eq);

    //Checking equivalence of modeled kv_mlkem_sharedkey_ready and RTL
    property kv_mlkem_sharedkey_ready_eq;
        abr_ctrl.kv_mlkem_sharedkey_ready == fv_kv_mlkem_sharedkey_ready
    endproperty

    assert_kv_mlkem_sharedkey_ready_eq: assert property (disable iff (!pi_rst_b | po_zeroize) kv_mlkem_sharedkey_ready_eq);

    //Checking equivalence of error responses
    property kv_mlkem_sharedkey_error;
        abr_ctrl.kv_mlkem_sharedkey_error == fv_kv_mlkem_sharedkey_error_code
    endproperty

    assert_kv_mlkem_sharedkey_error: assert property (disable iff (!pi_rst_b | po_zeroize) kv_mlkem_sharedkey_error);




    ///////////////////////////////////////////////////////////////////Requirement 3: Once the write is triggered it ends up in specific slot of mlkem/////////////////////////////////////////////////////////////////
    //////////////////////////////////////////////////////////////////////////////////////Assertions for kv_write PO///////////////////////////////////////////////////////////////////////////////////////////////////


    //Assertion for kv_write.write_entry PO
    property kv_mlkem_sharedkey_write_entry;
        pi_abr_reg_hwif_out_i.kv_mlkem_sharedkey_wr_ctrl.write_en
    |->
        po_kv_write.write_entry == pi_abr_reg_hwif_out_i.kv_mlkem_sharedkey_wr_ctrl.write_entry
    endproperty

    assert_kv_mlkem_sharedkey_write_entry: assert property (disable iff (!pi_rst_b | po_zeroize) kv_mlkem_sharedkey_write_entry);


    //Assertion for kv_write.write_enable PO
    property kv_mlkem_sharedkey_write_en;
        po_kv_write.write_en == fv_kv_mlkem_sharedkey_we;
    endproperty
    assert_kv_mlkem_sharedkey_write_en: assert property (disable iff (!pi_rst_b | po_zeroize) kv_mlkem_sharedkey_write_en);

    //Assertion for kv_write.write_offset PO
    property kv_mlkem_sharedkey_offset;
        fv_kv_mlkem_sharedkey_we
    |->
        (fv_kv_mlkem_sharedkey_words_cntr - 1) == po_kv_write.write_offset
    endproperty
    assert_kv_mlkem_sharedkey_offset: assert property (disable iff (!pi_rst_b | po_zeroize) kv_mlkem_sharedkey_offset);

    //Assertions for kv_write.write_dest_valid PO
    property kv_mlkem_sharedkey_write_dest_valid_high;
        fv_kv_mlkem_sharedkey_words_cntr == SHAREDKEY_NUM_DWORDS
    |->
        po_kv_write.write_dest_valid[0] == pi_abr_reg_hwif_out_i.kv_mlkem_sharedkey_wr_ctrl.hmac_key_dest_valid.value &&
        po_kv_write.write_dest_valid[1] == pi_abr_reg_hwif_out_i.kv_mlkem_sharedkey_wr_ctrl.hmac_block_dest_valid.value &&
        po_kv_write.write_dest_valid[2] == pi_abr_reg_hwif_out_i.kv_mlkem_sharedkey_wr_ctrl.mldsa_seed_dest_valid.value &&
        po_kv_write.write_dest_valid[3] == pi_abr_reg_hwif_out_i.kv_mlkem_sharedkey_wr_ctrl.ecc_pkey_dest_valid.value &&
        po_kv_write.write_dest_valid[4] == pi_abr_reg_hwif_out_i.kv_mlkem_sharedkey_wr_ctrl.ecc_seed_dest_valid.value &&
        po_kv_write.write_dest_valid[5] == pi_abr_reg_hwif_out_i.kv_mlkem_sharedkey_wr_ctrl.aes_key_dest_valid.value &&
        po_kv_write.write_dest_valid[6] == pi_abr_reg_hwif_out_i.kv_mlkem_sharedkey_wr_ctrl.mlkem_seed_dest_valid.value &&
        po_kv_write.write_dest_valid[7] == pi_abr_reg_hwif_out_i.kv_mlkem_sharedkey_wr_ctrl.mlkem_msg_dest_valid.value &&
        po_kv_write.write_dest_valid[8] == pi_abr_reg_hwif_out_i.kv_mlkem_sharedkey_wr_ctrl.dma_data_dest_valid.value
    endproperty

    assert_kv_mlkem_sharedkey_write_dest_valid_high: assert property (disable iff (!pi_rst_b | po_zeroize) kv_mlkem_sharedkey_write_dest_valid_high);

    //kv_write.write_dest_valid should remain low until it gets asserted at the last word
    property kv_mlkem_sharedkey_write_dest_valid_low;
        fv_kv_mlkem_sharedkey_words_cntr != SHAREDKEY_NUM_DWORDS
    |->
        po_kv_write.write_dest_valid == 'd0
    endproperty

    assert_kv_mlkem_sharedkey_write_dest_valid_low: assert property (disable iff (!pi_rst_b | po_zeroize) kv_mlkem_sharedkey_write_dest_valid_low);




    ////////////////////////////////////////////////////////////////////////////Requirement 4: Write data value written to the KV is valid///////////////////////////////////////////////////////////////////////

    logic [SHAREDKEY_NUM_DWORDS-1:0][31:0] fv_kv_mlkem_sharedkey_data;

    //reverse words to match endianness
    always_comb begin: fv_populate_mlkem_sharedkey_data
        for(int i = 0; i < SHAREDKEY_NUM_DWORDS; i++) begin
                fv_kv_mlkem_sharedkey_data[i] = abr_ctrl.abr_scratch_reg.mlkem_enc.shared_key[SHAREDKEY_NUM_DWORDS-1-i];
        end
    end

    //Assertion to verify the kv_write.write_data data integrity
    property kv_mlkem_sharedkey_write_data_integrity;
        fv_kv_mlkem_sharedkey_we
    |->
        po_kv_write.write_data == fv_kv_mlkem_sharedkey_data[fv_kv_mlkem_sharedkey_words_cntr-1]
    endproperty

    assert_kv_mlkem_sharedkey_write_data_integrity: assert property (disable iff (!pi_rst_b | po_zeroize) kv_mlkem_sharedkey_write_data_integrity);

    //abr_scratch_reg.mlkem_enc.shared_key should remain stable during KV write operation
    property kv_mlkem_sharedkey_data_stable;
        fv_kv_mlkem_sharedkey_we
    |->
        $stable(abr_ctrl.abr_scratch_reg.mlkem_enc.shared_key)
    endproperty

    assert_kv_mlkem_sharedkey_data_stable: assert property (disable iff (!pi_rst_b | po_zeroize) kv_mlkem_sharedkey_data_stable);



    ///////////////////////////////////////////////////////////////////////Requirement 6: Reset/Zeroize erase the entire data to/from KV////////////////////////////////////////////////////////////////////////////

    property kv_write_reset;
        !pi_rst_b | po_zeroize
    |->
        ##1 po_kv_write.write_en == '0 &&
            po_kv_write.write_dest_valid == '0 &&
            po_kv_write.write_data == '0 &&
            po_kv_write.write_offset == '0
    endproperty

    assert_kv_write_reset: assert property (kv_write_reset);


    /////////////////////////////////////////////////////////////////////////Requirement 9: Primary Outputs assertions////////////////////////////////////////////////////////////////////////////////////////////////

    property kv_mlkem_sharedkey_swwe(swwe);
        po_abr_reg_hwif_in_o.abr_ready == swwe
    endproperty

    assert_kv_mlkem_sharedkey_write_en_swwe: assert property (disable iff (!pi_rst_b | po_zeroize) kv_mlkem_sharedkey_swwe(po_abr_reg_hwif_in_o.kv_mlkem_sharedkey_wr_ctrl.write_en.swwe));
    assert_kv_mlkem_sharedkey_write_entry_swwe: assert property (disable iff (!pi_rst_b | po_zeroize) kv_mlkem_sharedkey_swwe(po_abr_reg_hwif_in_o.kv_mlkem_sharedkey_wr_ctrl.write_entry.swwe));
    assert_kv_mlkem_sharedkey_hmac_key_dest_valid_swwe: assert property (disable iff (!pi_rst_b | po_zeroize) kv_mlkem_sharedkey_swwe(po_abr_reg_hwif_in_o.kv_mlkem_sharedkey_wr_ctrl.hmac_key_dest_valid.swwe));
    assert_kv_mlkem_sharedkey_hmac_block_dest_valid_swwe: assert property (disable iff (!pi_rst_b | po_zeroize) kv_mlkem_sharedkey_swwe(po_abr_reg_hwif_in_o.kv_mlkem_sharedkey_wr_ctrl.hmac_block_dest_valid.swwe));
    assert_kv_mlkem_sharedkey_mldsa_seed_dest_valid_swwe: assert property (disable iff (!pi_rst_b | po_zeroize) kv_mlkem_sharedkey_swwe(po_abr_reg_hwif_in_o.kv_mlkem_sharedkey_wr_ctrl.mldsa_seed_dest_valid.swwe));
    assert_kv_mlkem_sharedkey_ecc_pkey_dest_valid_swwe: assert property (disable iff (!pi_rst_b | po_zeroize) kv_mlkem_sharedkey_swwe(po_abr_reg_hwif_in_o.kv_mlkem_sharedkey_wr_ctrl.ecc_pkey_dest_valid.swwe));
    assert_kv_mlkem_sharedkey_ecc_seed_dest_valid_swwe: assert property (disable iff (!pi_rst_b | po_zeroize) kv_mlkem_sharedkey_swwe(po_abr_reg_hwif_in_o.kv_mlkem_sharedkey_wr_ctrl.ecc_seed_dest_valid.swwe));
    assert_kv_mlkem_sharedkey_aes_key_dest_valid_swwe: assert property (disable iff (!pi_rst_b | po_zeroize) kv_mlkem_sharedkey_swwe(po_abr_reg_hwif_in_o.kv_mlkem_sharedkey_wr_ctrl.aes_key_dest_valid.swwe));
    assert_kv_mlkem_sharedkey_mlkem_seed_dest_valid_swwe: assert property (disable iff (!pi_rst_b | po_zeroize) kv_mlkem_sharedkey_swwe(po_abr_reg_hwif_in_o.kv_mlkem_sharedkey_wr_ctrl.mlkem_seed_dest_valid.swwe));
    assert_kv_mlkem_sharedkey_mlkem_msg_dest_valid_swwe: assert property (disable iff (!pi_rst_b | po_zeroize) kv_mlkem_sharedkey_swwe(po_abr_reg_hwif_in_o.kv_mlkem_sharedkey_wr_ctrl.mlkem_msg_dest_valid.swwe));
    assert_kv_mlkem_sharedkey_dma_data_dest_valid_swwe: assert property (disable iff (!pi_rst_b | po_zeroize) kv_mlkem_sharedkey_swwe(po_abr_reg_hwif_in_o.kv_mlkem_sharedkey_wr_ctrl.dma_data_dest_valid.swwe));
    assert_kv_mlkem_sharedkey_rsvd_swwe: assert property (disable iff (!pi_rst_b | po_zeroize) po_abr_reg_hwif_in_o.kv_mlkem_sharedkey_wr_ctrl.rsvd.swwe == '0);
    assert_kv_mlkem_sharedkey_wr_status_ready: assert property (disable iff (!pi_rst_b | po_zeroize) po_abr_reg_hwif_in_o.kv_mlkem_sharedkey_wr_status.READY.next == abr_ctrl.kv_mlkem_sharedkey_ready);
    assert_kv_mlkem_sharedkey_write_en_hwclr: assert property (disable iff (!pi_rst_b | po_zeroize) po_abr_reg_hwif_in_o.kv_mlkem_sharedkey_wr_ctrl.write_en.hwclr == !abr_ctrl.kv_mlkem_sharedkey_ready);
    assert_kv_mlkem_sharedkey_wr_status_valid_hwclr: assert property (disable iff (!pi_rst_b | po_zeroize) po_abr_reg_hwif_in_o.kv_mlkem_sharedkey_wr_status.VALID.hwclr == pi_abr_reg_hwif_out_i.kv_mlkem_sharedkey_wr_ctrl.write_en);
    assert_kv_mlkem_sharedkey_wr_status_valid_hwset: assert property (disable iff (!pi_rst_b | po_zeroize) po_abr_reg_hwif_in_o.kv_mlkem_sharedkey_wr_status.VALID.hwset == abr_ctrl.kv_mlkem_sharedkey_done);
    assert_kv_mlkem_sharedkey_wr_status_error: assert property (disable iff (!pi_rst_b | po_zeroize) po_abr_reg_hwif_in_o.kv_mlkem_sharedkey_wr_status.ERROR.next == abr_ctrl.kv_mlkem_sharedkey_error);



    //////////////////////////////////////////////////////////Requirement 10: No writing to SHARED_KEY api if data is being written to or reading from KV////////////////////////////////////////////////////////////////


    property no_sharedkey_api_write(data);
        (fv_abr_ctrl_kv.fv_abr_ctrl_kv_read_aip_i.fv_mlkem_busy && !abr_ctrl.mlkem_process_done) ||
        pi_abr_reg_hwif_out_i.kv_mlkem_sharedkey_wr_ctrl.write_en ||
        fv_abr_ctrl_kv.fv_abr_ctrl_kv_read_aip_i.fv_kv_mlkem_seed_data_present_flag ||
        fv_abr_ctrl_kv.fv_abr_ctrl_kv_read_aip_i.fv_kv_mlkem_msg_data_present_flag
    |->
        data == '0
    endproperty

    genvar fv_sharedkey_var;
    generate
        for(fv_sharedkey_var=0; fv_sharedkey_var<SHAREDKEY_NUM_DWORDS; fv_sharedkey_var++) begin: gen_mlkem_sharedkey_api_assertions
            assert_no_sharedkey_api_write: assert property (disable iff (!pi_rst_b | po_zeroize) no_sharedkey_api_write(po_abr_reg_hwif_in_o.MLKEM_SHARED_KEY[fv_sharedkey_var].rd_data));
        end
    endgenerate


    //////////////////////////////////////////////////////////Requirement 11: If crypto engine is busy, no writes should occur unless rules are satisfied////////////////////////////////////////////////////////////////

    //In MLDSA mode, the MLKEM sharedkey writes should not occur
    property no_mlkem_sharedkey_write_during_mldsa;
        fv_abr_ctrl_kv.fv_abr_ctrl_kv_read_aip_i.fv_mldsa_busy
    |->
        abr_ctrl.kv_mlkem_sharedkey_ready &&
        po_kv_write.write_en == '0 &&
        po_kv_write.write_dest_valid == '0 &&
        po_kv_write.write_offset == '0
    endproperty

    assert_no_mlkem_sharedkey_write_during_mldsa: assert property (disable iff (!pi_rst_b | po_zeroize) no_mlkem_sharedkey_write_during_mldsa);

    //If fv_mlkem_busy and not valid, no writes should occur
    property mlkem_busy_not_valid_no_sharedkey_write;
        fv_abr_ctrl_kv.fv_abr_ctrl_kv_read_aip_i.fv_mlkem_busy && !abr_ctrl.mlkem_process_done
    |->
        abr_ctrl.kv_mlkem_sharedkey_ready &&
        po_kv_write.write_en == '0 &&
        po_kv_write.write_dest_valid == '0 &&
        po_kv_write.write_offset == '0
    endproperty

    assert_mlkem_busy_not_valid_no_sharedkey_write: assert property (disable iff (!pi_rst_b | po_zeroize) mlkem_busy_not_valid_no_sharedkey_write);

endmodule
