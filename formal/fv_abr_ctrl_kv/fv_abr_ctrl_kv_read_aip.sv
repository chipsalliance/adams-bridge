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

module fv_abr_ctrl_kv_read_aip
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
    input logic [ABR_MEM_ADDR_WIDTH-1:0]               po_aux_src0_base_addr_o,
    input logic                                        pi_sampler_state_dv_i,
    input logic [abr_sha3_pkg::StateW-1:0]             pi_sampler_state_data_i,
    input kv_read_t [2:0]                              po_kv_read,
    input kv_rd_resp_t [2:0]pi_kv_rd_resp,
    input kv_write_t                                   po_kv_write,
    input kv_wr_resp_t                                 pi_kv_wr_resp,
    input logic                                        pi_ocp_lock_in_progress,
    input pcr_signing_t                                pi_pcr_signing_data,
    input logic                                        po_busy_o
    //$#//
);

    // Define default clock
    default clocking default_clk @(posedge pi_clk); endclocking

    ////////////////////////////////////////////////////////////////////////////////////////////////MLDSA mode//////////////////////////////////////////////////////////////////////////////////////////////////
    ///////////////////////////////////////////////////////////////////////Requirement 1: Before computation starts, data from KV is read///////////////////////////////////////////////////////////////////////

    // Aux logic to model KV MLDSA seed client read state machine
    typedef enum logic [1:0] {
        fv_st_idle_type,
        fv_st_read_type,
        fv_st_done_type
    } fvFsmState;

    fvFsmState                      fv_kv_mldsa_seed_cs, fv_kv_mldsa_seed_ns;
    logic [$clog2(SEED_NUM_DWORDS):0]   fv_kv_mldsa_seed_words_cntr;
    logic                               fv_kv_mldsa_seed_read_rules_fail;
    logic                               fv_kv_mldsa_seed_read_start;
    logic                               fv_kv_mldsa_seed_read_rules_allow;
    logic                               fv_kv_mldsa_seed_complete;
    logic                               fv_kv_mldsa_seed_done;
    logic                               fv_kv_mldsa_seed_we;
    logic [SEED_NUM_DWORDS-1:0][31:0]   fv_kv_mldsa_seed_data;
    logic                               fv_kv_mldsa_seed_ready;

    always_ff @(posedge pi_clk or negedge pi_rst_b) begin: fv_kv_mldsa_seed_state_update
        if (!pi_rst_b || po_zeroize) begin
            fv_kv_mldsa_seed_cs <= fv_st_idle_type;
        end else begin
            fv_kv_mldsa_seed_cs <= fv_kv_mldsa_seed_ns;
        end
    end

    //if ocp_lock_in_progress, the crypto-engine shall not read from OCP_LOCK_KEY_RELEASE_KV_SLOT
    assign fv_kv_mldsa_seed_read_rules_fail = pi_ocp_lock_in_progress && (pi_abr_reg_hwif_out_i.kv_mldsa_seed_rd_ctrl.read_entry == OCP_LOCK_KEY_RELEASE_KV_SLOT);

    //Modeling of read_start signal and rules_allow signal to trigger the KV read process correctly
    always_ff @(posedge pi_clk or negedge pi_rst_b) begin: fv_kv_mldsa_seed_conditions_update
        if (!pi_rst_b) begin
            fv_kv_mldsa_seed_read_start        <= '0;
            fv_kv_mldsa_seed_read_rules_allow  <= '0;
        end
        else if (fv_kv_mldsa_seed_done) begin
            fv_kv_mldsa_seed_read_start        <= '0;
            fv_kv_mldsa_seed_read_rules_allow  <= '0;
        end
        else if (pi_abr_reg_hwif_out_i.kv_mldsa_seed_rd_ctrl.read_en.value) begin
            fv_kv_mldsa_seed_read_start        <= '1;
            fv_kv_mldsa_seed_read_rules_allow  <= !fv_kv_mldsa_seed_read_rules_fail;
        end
        else if (po_zeroize) begin
            fv_kv_mldsa_seed_read_start        <= '0;
            fv_kv_mldsa_seed_read_rules_allow  <= '0;
        end
    end

    assign fv_kv_mldsa_seed_complete    = (fv_kv_mldsa_seed_words_cntr == SEED_NUM_DWORDS) || pi_kv_rd_resp[0].last;

    //Aux logic to count the number of words received from KV to know when to terminate the state machine if maximum has reached
    always_ff @(posedge pi_clk or negedge pi_rst_b) begin: fv_kv_mldsa_seed_cntr_update
        if (!pi_rst_b || po_zeroize) begin
            fv_kv_mldsa_seed_words_cntr <= 'd0;
        end else if(fv_kv_mldsa_seed_done) begin
            fv_kv_mldsa_seed_words_cntr <= 'd0;
        end else if (fv_kv_mldsa_seed_ns == fv_st_read_type) begin
            fv_kv_mldsa_seed_words_cntr <= fv_kv_mldsa_seed_words_cntr + 'd1;
        end
    end

    //Aux logic for the KV state machine to model the done signal
    always_comb begin: fv_kv_mldsa_seed_fsm
        fv_kv_mldsa_seed_ns     = fv_kv_mldsa_seed_cs;
        fv_kv_mldsa_seed_done   = 1'b0;
        fv_kv_mldsa_seed_we     = 1'b0;
        unique case (fv_kv_mldsa_seed_cs)
            fv_st_idle_type: begin
                if (fv_kv_mldsa_seed_read_start) begin
                    if (fv_kv_mldsa_seed_read_rules_allow) begin
                        fv_kv_mldsa_seed_ns = fv_st_read_type;
                    end else begin
                        fv_kv_mldsa_seed_ns = fv_st_done_type;
                    end
                end
            end
            fv_st_read_type: begin
                fv_kv_mldsa_seed_we = 1'b1;
                //RTL kv_fsm aborts the transfer on a KV read error (abort_i = kv_resp.error),
                //jumping to KV_DONE on that beat regardless of how many dwords were read
                if (pi_kv_rd_resp[0].error || fv_kv_mldsa_seed_complete) begin
                    fv_kv_mldsa_seed_ns = fv_st_done_type;
                end
            end
            fv_st_done_type: begin
                fv_kv_mldsa_seed_done = 1'b1;
                fv_kv_mldsa_seed_ns = fv_st_idle_type;
            end
            default: begin
                fv_kv_mldsa_seed_ns = fv_st_idle_type;
            end
        endcase
    end

    //Model data present signal for kv_mldsa_seed
    logic fv_kv_mldsa_seed_data_present;
    assign fv_kv_mldsa_seed_data_present = pi_abr_reg_hwif_out_i.kv_mldsa_seed_rd_ctrl.read_en.value || pi_abr_reg_hwif_out_i.MLDSA_CTRL.PCR_SIGN.value;

    //flag for mldsa_data_present
    logic fv_kv_mldsa_seed_data_present_flag;
    always_ff @(posedge pi_clk or negedge pi_rst_b) begin: fv_flag_kv_mldsa_seed_data_present
        if (!pi_rst_b || po_zeroize) begin
            fv_kv_mldsa_seed_data_present_flag <= '0;
        end else if (fv_kv_mldsa_seed_data_present) begin
            fv_kv_mldsa_seed_data_present_flag <= '1;
        end
    end

    //Aux logic to model and latch kv_mldsa_seed error responses
    logic fv_kv_mldsa_error_flag;
    logic fv_kv_mldsa_error;

    //Aux logic to model RTL's stored_last_dword/length_mismatch check (kv_read_client.sv):
    //the KV entry's actual size (entry_last_dword) is latched on each write beat, and checked
    //against the client's expected_key_size (SEED_NUM_DWORDS-1) once the read completes.
    //A short entry (e.g. an early kv_resp.last on the first beat) fails this check even though
    //no per-beat kv_resp.error was ever seen.
    logic [KV_ENTRY_SIZE_W-1:0] fv_kv_mldsa_seed_stored_last_dword;
    always_ff @(posedge pi_clk or negedge pi_rst_b) begin: fv_reg_kv_mldsa_seed_stored_last_dword
        if (!pi_rst_b || po_zeroize) begin
            fv_kv_mldsa_seed_stored_last_dword <= '0;
        end else if (fv_kv_mldsa_seed_we) begin
            fv_kv_mldsa_seed_stored_last_dword <= pi_kv_rd_resp[0].entry_last_dword;
        end
    end

    logic fv_kv_mldsa_seed_length_mismatch;
    assign fv_kv_mldsa_seed_length_mismatch = fv_kv_mldsa_seed_done && (fv_kv_mldsa_seed_stored_last_dword < (SEED_NUM_DWORDS-1));

    assign fv_kv_mldsa_error = ((fv_kv_mldsa_seed_cs == fv_st_read_type) && pi_kv_rd_resp[0].error) || (!fv_kv_mldsa_seed_read_rules_allow && fv_kv_mldsa_seed_read_start) || fv_kv_mldsa_seed_length_mismatch;

    always_ff @(posedge pi_clk or negedge pi_rst_b) begin: fv_reg_kv_mldsa_error
        if (!pi_rst_b || po_zeroize) begin
            fv_kv_mldsa_error_flag <= '0;
        end else if (fv_kv_mldsa_error) begin
            fv_kv_mldsa_error_flag <= '1;
        end
        //Per spec (CaliptraHardwareSpecification.md, KV key-length-mismatch detection / KV cryptographic functional block):
        //the KV read error self-holds and is cleared only by rst_b or zeroize. A new read request must NOT clear it.
    end

    //Model ready signal for mldsa seed kv client
    assign fv_kv_mldsa_seed_ready = (fv_kv_mldsa_seed_cs == fv_st_idle_type) && !fv_kv_mldsa_seed_read_start && !fv_kv_mldsa_error_flag;

    //Model swwe for mldsa_seed
    logic [SEED_NUM_DWORDS-1:0][31:0]   fv_mldsa_seed_swwe_data;
    logic                               fv_mldsa_seed_swwe;
    logic                               fv_mldsa_seed_swwe_ff;

    assign fv_mldsa_seed_swwe = !fv_kv_mldsa_seed_data_present_flag && po_abr_reg_hwif_in_o.abr_ready;

    //Latch the swwe for mldsa_seed
    always_ff @(posedge pi_clk or negedge pi_rst_b) begin: fv_mldsa_seed_swwe_ff_process
        if (!pi_rst_b) begin
            fv_mldsa_seed_swwe_ff <= 'd0;
        end else begin
            fv_mldsa_seed_swwe_ff <= fv_mldsa_seed_swwe;
        end
    end

    //model the sw writes, if swwe, the MLDSA_SEED input is the data to feed into the temp reg
    //has to be modeled combinatorially
    always_comb begin: fv_mldsa_seed_sw_data
        fv_mldsa_seed_swwe_data = '0;
        if (fv_mldsa_seed_swwe_ff) begin
            for (int i=0; i<SEED_NUM_DWORDS; i++) begin
                fv_mldsa_seed_swwe_data[i] = pi_abr_reg_hwif_out_i.MLDSA_SEED[i].SEED.value;
            end
        end
    end


    //Checking equivalence of modeled mldsa_seed_done and RTL
    property kv_done_eq(fv_done, client_done);
        fv_done == client_done;
    endproperty

    assert_kv_mldsa_seed_done_eq: assert property (disable iff (!pi_rst_b | po_zeroize) kv_done_eq(fv_kv_mldsa_seed_done, abr_ctrl.kv_mldsa_seed_done));


    //Checking equivalence between the aux logic of offset and kv_read.read_offset
    property kv_offset_eq(write_en, fv_offset, kv_offset);
        write_en
    |->
        (fv_offset - 1) == kv_offset
    endproperty

    assert_kv_mldsa_offset_eq: assert property (disable iff (!pi_rst_b | po_zeroize) kv_offset_eq(abr_ctrl.kv_mldsa_seed_write_en, fv_kv_mldsa_seed_words_cntr, po_kv_read[0].read_offset));


    //Checking equivalence of modeled kv_mldsa_seed_ready and RTL
    property kv_ready_eq(fv_ready, client_ready);
        fv_ready == client_ready;
    endproperty

    assert_kv_mldsa_seed_ready_eq: assert property (disable iff (!pi_rst_b | po_zeroize) kv_ready_eq(fv_kv_mldsa_seed_ready, abr_ctrl.kv_mldsa_seed_ready));


    //Model MLDSA busy signal
    logic fv_mldsa_busy;
    assign fv_mldsa_busy = abr_ctrl.mldsa_keygen_process | abr_ctrl.mldsa_signing_process | abr_ctrl.mldsa_verifying_process | abr_ctrl.mldsa_keygen_signing_process;


    //If computation has started, no more kv reads should happen.
    property if_busy_no_more_kv_read(busy, kv_read);
        busy
    |->
        !kv_read
    endproperty

    assert_if_busy_no_more_mldsa_seed_kv_read: assert property (disable iff (!pi_rst_b | po_zeroize) if_busy_no_more_kv_read(fv_mldsa_busy, abr_ctrl.kv_mldsa_seed_write_en));


    // Aux logic to latch the value of kv_mldsa_seed_rd_ctrl.read_en until the end of MLDSA operation
    logic fv_kv_mldsa_seed_req;

    always_ff @(posedge pi_clk or negedge pi_rst_b) begin: fv_reg_kv_mldsa_seed_req
        if (!pi_rst_b) begin
            fv_kv_mldsa_seed_req <= '0;
        end else if (pi_abr_reg_hwif_out_i.kv_mldsa_seed_rd_ctrl.read_en.value) begin
            fv_kv_mldsa_seed_req <= '1;
        end
        //read_en has precedence over zeroize to cover the case when read enables come in the same cc as zeroize
        else if (po_zeroize) begin
            fv_kv_mldsa_seed_req <= '0;
        end else if (abr_ctrl.mldsa_process_done) begin
            fv_kv_mldsa_seed_req <= '0;
        end
    end

   //Save the kv client done signal until end of operation
    logic fv_kv_mldsa_seed_done_flag;
    always_ff @(posedge pi_clk or negedge pi_rst_b) begin: fv_kv_mldsa_seed_done_flag_ff
        if (!pi_rst_b || po_zeroize) begin
            fv_kv_mldsa_seed_done_flag <= '0;
        end else if (fv_kv_mldsa_seed_done) begin
            fv_kv_mldsa_seed_done_flag <= '1;
        end else if (abr_ctrl.mldsa_process_done) begin
            fv_kv_mldsa_seed_done_flag <= '0;
        end
    end



    //Save the kv response data into a temp register to match KV endianness
    always_ff @(posedge pi_clk or negedge pi_rst_b) begin: fv_kv_mldsa_seed_data_ff
        if (!pi_rst_b) begin
            fv_kv_mldsa_seed_data <= 'd0;
        end else begin
            if (fv_mldsa_seed_swwe_ff) begin
                fv_kv_mldsa_seed_data <= fv_mldsa_seed_swwe_data;
            end
            if (fv_kv_mldsa_seed_we) begin
                fv_kv_mldsa_seed_data[SEED_NUM_DWORDS - fv_kv_mldsa_seed_words_cntr] <= pi_kv_rd_resp[0].read_data;
            end
            if (po_zeroize || fv_kv_mldsa_error_flag) begin
                fv_kv_mldsa_seed_data <= 'd0;
            end
        end
    end



    //Before busy is asserted, KV state machine should have completed
    property before_busy_kv_done(busy, kv_req, kv_done);
        busy && kv_req
    |->
        kv_done
    endproperty

    assert_before_busy_kv_mldsa_seed_done: assert property (disable iff (!pi_rst_b | po_zeroize) before_busy_kv_done(fv_mldsa_busy, fv_kv_mldsa_seed_req, fv_kv_mldsa_seed_done_flag));


    //When the KV is done, MLDSA_SEED[].SEED.value should have the correct data
    //Exception: Not checking the case where read_en arrives at the same cc with zeroize
    property kv_data_rd_integrity(kv_done, pcr_sign_mode, data_present, data, fv_data);
        kv_done && !pcr_sign_mode && data_present
    |->
        ##1 data == fv_data
    endproperty

    genvar fv_mldsa_seed_var;
    generate
        for(fv_mldsa_seed_var=0; fv_mldsa_seed_var<SEED_NUM_DWORDS; fv_mldsa_seed_var++) begin: gen_mldsa_seed_data_assertions
            assert_kv_mldsa_seed_data_rd_integrity: assert property (disable iff (!pi_rst_b | po_zeroize) kv_data_rd_integrity(fv_kv_mldsa_seed_done, pi_abr_reg_hwif_out_i.MLDSA_CTRL.PCR_SIGN.value,
                                                                                                                                    fv_kv_mldsa_seed_data_present_flag,
                                                                                                                                        abr_ctrl.mldsa_seed_reg[fv_mldsa_seed_var],
                                                                                                                                            fv_kv_mldsa_seed_data[fv_mldsa_seed_var]));
        end
    endgenerate

    //Data read from KV should be stable the moment a cmd is received (mldsa_busy) till end of operation
    property kv_data_stable(kv_done, busy, hw_reg);
        kv_done && busy
    |->
        ##1 $stable(hw_reg)
    endproperty

    assert_kv_mldsa_seed_data_stable: assert property (disable iff (!pi_rst_b | po_zeroize) kv_data_stable(fv_kv_mldsa_seed_done_flag, fv_mldsa_busy, abr_ctrl.mldsa_seed_reg));

    //HW write enable is asserted with its corresponding write offset
    property hwwe_kv_write_offset_match_high(kv_we, offset, max_words, index, we);
        kv_we && (offset == (max_words - index))
    |->
        we
    endproperty

    genvar fv_mldsa_seed_we_var0;
    generate
        for(fv_mldsa_seed_we_var0=0; fv_mldsa_seed_we_var0<SEED_NUM_DWORDS; fv_mldsa_seed_we_var0++) begin: gen_mldsa_seed_offset_high_assertions
            assert_mldsa_seed_we_kv_mldsa_seed_write_offset_high_match: assert property (disable iff (!pi_rst_b | po_zeroize) hwwe_kv_write_offset_match_high(abr_ctrl.kv_mldsa_seed_write_en, fv_kv_mldsa_seed_words_cntr,
                                                                                                                                                        SEED_NUM_DWORDS, fv_mldsa_seed_we_var0,
                                                                                                                                                            po_abr_reg_hwif_in_o.MLDSA_SEED[fv_mldsa_seed_we_var0].SEED.we));
        end
    endgenerate


    //HW write enable is low when the write offset is not the corresponding one
    property hwwe_kv_write_offset_match_low(kv_we, offset, max_words, index, pcr_sign, we);
        !(kv_we && (offset == (max_words - index))) && !pcr_sign
    |->
        !we
    endproperty

    genvar fv_mldsa_seed_we_var1;
    generate
        for(fv_mldsa_seed_we_var1=0; fv_mldsa_seed_we_var1<SEED_NUM_DWORDS; fv_mldsa_seed_we_var1++) begin: gen_mldsa_seed_offset_low_assertions
            assert_mldsa_seed_we_kv_mldsa_seed_write_offset_low_match: assert property (disable iff (!pi_rst_b | po_zeroize) hwwe_kv_write_offset_match_low(abr_ctrl.kv_mldsa_seed_write_en, fv_kv_mldsa_seed_words_cntr,
                                                                                                                                                        SEED_NUM_DWORDS, fv_mldsa_seed_we_var1, pi_abr_reg_hwif_out_i.MLDSA_CTRL.PCR_SIGN.value,
                                                                                                                                                            po_abr_reg_hwif_in_o.MLDSA_SEED[fv_mldsa_seed_we_var1].SEED.we));
        end
    endgenerate



    ///////////////////////////////////////////////////////////////////////Requirement 2: Choose the specific slot meant for KV if it's a read///////////////////////////////////////////////////////////////////////

    property kv_rd_entry(read_en, kv_entry_in, kv_entry_out);
        read_en
    |->
        kv_entry_out == kv_entry_in
    endproperty

    assert_kv_mldsa_seed_rd_entry: assert property (disable iff (!pi_rst_b | po_zeroize) kv_rd_entry(pi_abr_reg_hwif_out_i.kv_mldsa_seed_rd_ctrl.read_en.value, pi_abr_reg_hwif_out_i.kv_mldsa_seed_rd_ctrl.read_entry.value,
                                                                                                        po_kv_read[0].read_entry));




    ///////////////////////////////////////////////////////////////////////Requirement 5: If a secret is read from KV then the associated writes shouldn't be from api////////////////////////////////////////////////

    //If the read request was for KV, the private key lock should be asserted, and no data should be leaked to API
    //Spec (AdamsBridge_MLDSA.md sk_out / AdamsBridge_MLKEM.md decaps_key): if the seed comes from KV, the register will not contain
    //the private key. Checked with the sticky data_present flag (held until zeroize), so the check also covers the window after
    //keygen completes, when the private key would otherwise become readable.
    property no_secret_leaked_to_api(kv_req, lock, private_key);
        kv_req
    |->
        lock && (private_key == 'd0)
    endproperty

    assert_no_mldsa_secret_leaked_to_api: assert property (disable iff (!pi_rst_b | po_zeroize) no_secret_leaked_to_api(fv_kv_mldsa_seed_data_present_flag, abr_ctrl.mldsa_privkey_lock, po_abr_reg_hwif_in_o.MLDSA_PRIVKEY_OUT.rd_data));

    //MLDSA privkey lock is asserted by default
    property default_lock_assertion(busy, keygen_done, lock);
        po_zeroize | !pi_rst_b | (busy & !keygen_done)
    |->
        ##1 lock
    endproperty

    assert_mldsa_default_lock_assertion: assert property (default_lock_assertion(fv_mldsa_busy, abr_ctrl.mldsa_keygen_done, abr_ctrl.mldsa_privkey_lock));

    //If the request was not for KV, and the keygen operation has finished, the private lock should be released
    property lock_deasserted(kv_req, keygen_done, lock);
        !kv_req && keygen_done
    |->
        ##1 !lock
    endproperty

    assert_lock_deasserted_after_mldsa_keygen: assert property (disable iff (!pi_rst_b | po_zeroize) lock_deasserted(fv_kv_mldsa_seed_data_present_flag, abr_ctrl.mldsa_keygen_done, abr_ctrl.mldsa_privkey_lock));


    ///////////////////////////////////////////////////////////////////////Requirement 6: Reset/Zeroize erase the entire data to/from KV////////////////////////////////////////////////////////////////////////////

    //MLDSA_SEED.SEED.we is reset properly
    property erase_hw_write_enable(we);
        po_zeroize
    |->
        !we
    endproperty

    genvar fv_mldsa_seed_we_var2;
    generate
        for(fv_mldsa_seed_we_var2=0; fv_mldsa_seed_we_var2<SEED_NUM_DWORDS; fv_mldsa_seed_we_var2++) begin: gen_mldsa_seed_write_enable_assertions
            assert_erase_mldsa_seed_hw_write_enable: assert property (erase_hw_write_enable(po_abr_reg_hwif_in_o.MLDSA_SEED[fv_mldsa_seed_we_var2].SEED.we));
        end
    endgenerate

    //KV read_client write enable should be reset properly
    property kv_erase_write_enable(we);
        !pi_rst_b || po_zeroize
    |->
        ##1 !we
    endproperty

    assert_kv_erase_mldsa_seed_write_enable: assert property (kv_erase_write_enable(abr_ctrl.kv_mldsa_seed_write_en));

    //KV read_client read_offset should be reset properly
    property kv_erase_read_offset(offset);
        !pi_rst_b || po_zeroize
    |->
        ##1 offset == '0
    endproperty

    assert_kv_erase_mldsa_seed_read_offset: assert property (kv_erase_read_offset(po_kv_read[0].read_offset));

    //hwclr is asserted in case of errored responses or zeroize
    property seed_hwclr(hwclr, error_flag);
        hwclr == (po_zeroize | error_flag)
    endproperty

    genvar fv_mldsa_seed_hwclr_var;
    generate
        for(fv_mldsa_seed_hwclr_var=0; fv_mldsa_seed_hwclr_var<SEED_NUM_DWORDS; fv_mldsa_seed_hwclr_var++) begin: gen_mldsa_seed_hwclr_assertions
            assert_mldsa_seed_hwclrs: assert property (seed_hwclr(po_abr_reg_hwif_in_o.MLDSA_SEED[fv_mldsa_seed_hwclr_var].SEED.hwclr, fv_kv_mldsa_error_flag));
        end
    endgenerate



    ///////////////////////////////////////////////////////////////////////Requirement 7: No operation in the crypto engine without full read or write/////////////////////////////////////////////////////////


    property no_crypto_engine_op_without_full_read(kv_req, done);
        kv_req && !done
    |->
        abr_ctrl.abr_prog_cntr == ABR_RESET || abr_ctrl.abr_prog_cntr == ABR_ZEROIZE
    endproperty

    assert_no_crypto_engine_op_without_full_mldsa_read: assert property (no_crypto_engine_op_without_full_read(fv_kv_mldsa_seed_req, fv_kv_mldsa_seed_done_flag));

    //Spec (CaliptraHardwareSpecification.md, KV cryptographic functional block): "Key vault read errors will prevent the crypto engine
    //from accepting new commands. The engine will require zeroization in order to clear the error and resume normal operation."
    //The error flag self-holds until zeroize, so while it is set no operation of that algorithm may start.
    property no_cmd_after_kv_error(error_flag, busy);
        error_flag
    |->
        !busy
    endproperty

    assert_no_mldsa_cmd_after_kv_mldsa_seed_error: assert property (disable iff (!pi_rst_b | po_zeroize) no_cmd_after_kv_error(fv_kv_mldsa_error_flag, fv_mldsa_busy));




    ///////////////////////////////////////////////////////////////////////////Requirement 8: In MLSDA mode, all KV MLKEM outputs are deasserted//////////////////////////////////////////////////////////////

    //KV MLKEM write POs are deasserted in case of MLDSA read
    property no_mlkem_write_if_mldsa_mode;
        fv_mldsa_busy
    |->
        !po_kv_write.write_dest_valid && !po_kv_write.write_en && po_kv_write.write_offset == '0
    endproperty

    assert_no_mlkem_write_if_mldsa_mode: assert property (disable iff (!pi_rst_b | po_zeroize) no_mlkem_write_if_mldsa_mode);

    //KV MLKEM read POs are deasserted in case of MLDSA read
    property no_mlkem_read_if_mldsa_mode;
        fv_mldsa_busy
    |->
        (po_kv_read[1].read_offset == '0) && (po_kv_read[2].read_offset == '0) && !abr_ctrl.kv_mlkem_seed_write_en && !abr_ctrl.kv_mlkem_msg_write_en
    endproperty

    assert_no_mlkem_read_if_mldsa_mode: assert property (disable iff (!pi_rst_b | po_zeroize) no_mlkem_read_if_mldsa_mode);


    ////////////////////////////////////////////////////////////////////////////Primary Outputs assertions/////////////////////////////////////////////////////////////////////////////////////////////////////

    property kv_rd_ctrl_swwe(swwe, fv_swwe);
        swwe == fv_swwe
    endproperty

    assert_kv_mldsa_seed_rd_ctrl_read_en_swwe: assert property (disable iff (!pi_rst_b | po_zeroize) kv_rd_ctrl_swwe(po_abr_reg_hwif_in_o.kv_mldsa_seed_rd_ctrl.read_en.swwe, fv_mldsa_seed_swwe));
    assert_kv_mldsa_seed_rd_ctrl_read_entry_swwe: assert property (disable iff (!pi_rst_b | po_zeroize) kv_rd_ctrl_swwe(po_abr_reg_hwif_in_o.kv_mldsa_seed_rd_ctrl.read_entry.swwe, fv_mldsa_seed_swwe));
    assert_kv_mldsa_seed_rd_ctrl_rsvd_swwe: assert property (disable iff (!pi_rst_b | po_zeroize) kv_rd_ctrl_swwe(po_abr_reg_hwif_in_o.kv_mldsa_seed_rd_ctrl.rsvd.swwe, 0));
    assert_kv_mldsa_seed_rd_ctrl_pcr_hash_extend_swwe: assert property (disable iff (!pi_rst_b | po_zeroize) kv_rd_ctrl_swwe(po_abr_reg_hwif_in_o.kv_mldsa_seed_rd_ctrl.pcr_hash_extend.swwe, 0));

    property kv_rd_ctrl_read_en_hwclr(hwclr, client_ready);
        hwclr == !client_ready
    endproperty

    assert_kv_mldsa_seed_rd_ctrl_read_en_hwclr: assert property (disable iff (!pi_rst_b | po_zeroize) kv_rd_ctrl_read_en_hwclr(po_abr_reg_hwif_in_o.kv_mldsa_seed_rd_ctrl.read_en.hwclr, abr_ctrl.kv_mldsa_seed_ready));


    property kv_rd_status_ready(status_ready, client_ready);
        status_ready == client_ready
    endproperty

    assert_kv_mldsa_seed_rd_status_ready: assert property (disable iff (!pi_rst_b | po_zeroize) kv_rd_status_ready(po_abr_reg_hwif_in_o.kv_mldsa_seed_rd_status.READY.next, abr_ctrl.kv_mldsa_seed_ready));


    property kv_rd_status_valid_hwclr(hwclr, read_en);
        hwclr == read_en
    endproperty

    assert_kv_mldsa_seed_rd_status_valid_hwclr: assert property (disable iff (!pi_rst_b | po_zeroize) kv_rd_status_valid_hwclr(po_abr_reg_hwif_in_o.kv_mldsa_seed_rd_status.VALID.hwclr, pi_abr_reg_hwif_out_i.kv_mldsa_seed_rd_ctrl.read_en.value));


    property kv_rd_status_valid_hwset(hwset, client_done);
        hwset == client_done
    endproperty

    assert_kv_mldsa_seed_rd_status_valid_hwset: assert property (disable iff (!pi_rst_b | po_zeroize) kv_rd_status_valid_hwset(po_abr_reg_hwif_in_o.kv_mldsa_seed_rd_status.VALID.hwset, abr_ctrl.kv_mldsa_seed_done));


    property kv_rd_status_error(status_error, client_error);
        status_error == client_error
    endproperty

    assert_kv_mldsa_seed_rd_status_error: assert property (disable iff (!pi_rst_b | po_zeroize) kv_rd_status_error(po_abr_reg_hwif_in_o.kv_mldsa_seed_rd_status.ERROR.next, abr_ctrl.kv_mldsa_seed_error));




    ////////////////////////////////////////////////////////////////////////////////////////////////MLKEM seed//////////////////////////////////////////////////////////////////////////////////////////////////
    ///////////////////////////////////////////////////////////////////////Requirement 1: Before computation starts, data from KV is read///////////////////////////////////////////////////////////////////////


    // Aux logic to model KV MLKEM seed client read state machine
    fvFsmState                      fv_kv_mlkem_seed_cs, fv_kv_mlkem_seed_ns;
    logic [$clog2(2*SEED_NUM_DWORDS):0] fv_kv_mlkem_seed_words_cntr;
    logic                               fv_kv_mlkem_seed_read_rules_fail;
    logic                               fv_kv_mlkem_seed_read_start;
    logic                               fv_kv_mlkem_seed_read_rules_allow;
    logic                               fv_kv_mlkem_seed_complete;
    logic                               fv_kv_mlkem_seed_done;
    logic                               fv_kv_mlkem_seed_we;
    logic [2*SEED_NUM_DWORDS-1:0][31:0] fv_kv_mlkem_seed_data;
    logic                               fv_kv_mlkem_seed_ready;

    always_ff @(posedge pi_clk or negedge pi_rst_b) begin: fv_kv_mlkem_seed_state_update
        if (!pi_rst_b || po_zeroize) begin
            fv_kv_mlkem_seed_cs <= fv_st_idle_type;
        end else begin
            fv_kv_mlkem_seed_cs <= fv_kv_mlkem_seed_ns;
        end
    end

    //if ocp_lock_in_progress, the crypto-engine shall not read from OCP_LOCK_KEY_RELEASE_KV_SLOT
    assign fv_kv_mlkem_seed_read_rules_fail = pi_ocp_lock_in_progress && (pi_abr_reg_hwif_out_i.kv_mlkem_seed_rd_ctrl.read_entry == OCP_LOCK_KEY_RELEASE_KV_SLOT);

    //Modeling of read_start signal and rules_allow signal to trigger the KV read process correctly
    always_ff @(posedge pi_clk or negedge pi_rst_b) begin: fv_kv_mlkem_seed_conditions_update
        if (!pi_rst_b) begin
            fv_kv_mlkem_seed_read_start        <= '0;
            fv_kv_mlkem_seed_read_rules_allow  <= '0;
        end
        else if (fv_kv_mlkem_seed_done) begin
            fv_kv_mlkem_seed_read_start        <= '0;
            fv_kv_mlkem_seed_read_rules_allow  <= '0;
        end
        else if (pi_abr_reg_hwif_out_i.kv_mlkem_seed_rd_ctrl.read_en.value) begin
            fv_kv_mlkem_seed_read_start        <= '1;
            fv_kv_mlkem_seed_read_rules_allow  <= !fv_kv_mlkem_seed_read_rules_fail;
        end
        else if (po_zeroize) begin
            fv_kv_mlkem_seed_read_start        <= '0;
            fv_kv_mlkem_seed_read_rules_allow  <= '0;
        end

    end

    assign fv_kv_mlkem_seed_complete    = (fv_kv_mlkem_seed_words_cntr == 2*SEED_NUM_DWORDS) || pi_kv_rd_resp[1].last;


    //Aux logic to count the number of words received from KV to know when to terminate the state machine if maximum has reached
    always_ff @(posedge pi_clk or negedge pi_rst_b) begin: fv_kv_mlkem_seed_cntr_update
        if (!pi_rst_b || po_zeroize) begin
            fv_kv_mlkem_seed_words_cntr <= 'd0;
        end else if(fv_kv_mlkem_seed_done) begin
            fv_kv_mlkem_seed_words_cntr <= 'd0;
        end else if (fv_kv_mlkem_seed_ns == fv_st_read_type) begin
            fv_kv_mlkem_seed_words_cntr <= fv_kv_mlkem_seed_words_cntr + 'd1;
        end
    end

    //Aux logic for the KV state machine to model the done signal
    always_comb begin: fv_kv_mlkem_seed_fsm
        fv_kv_mlkem_seed_ns     = fv_kv_mlkem_seed_cs;
        fv_kv_mlkem_seed_done   = 1'b0;
        fv_kv_mlkem_seed_we     = 1'b0;
        unique case (fv_kv_mlkem_seed_cs)
            fv_st_idle_type: begin
                if (fv_kv_mlkem_seed_read_start) begin
                    if (fv_kv_mlkem_seed_read_rules_allow) begin
                        fv_kv_mlkem_seed_ns = fv_st_read_type;
                    end else begin
                        fv_kv_mlkem_seed_ns = fv_st_done_type;
                    end
                end
            end
            fv_st_read_type: begin
                fv_kv_mlkem_seed_we = 1'b1;
                //RTL kv_fsm aborts the transfer on a KV read error (abort_i = kv_resp.error),
                //jumping to KV_DONE on that beat regardless of how many dwords were read
                if (pi_kv_rd_resp[1].error || fv_kv_mlkem_seed_complete) begin
                    fv_kv_mlkem_seed_ns = fv_st_done_type;
                end
            end
            fv_st_done_type: begin
                fv_kv_mlkem_seed_done = 1'b1;
                fv_kv_mlkem_seed_ns = fv_st_idle_type;
            end
            default: begin
                fv_kv_mlkem_seed_ns = fv_st_idle_type;
            end
        endcase
    end

    logic fv_kv_mlkem_seed_data_present;
    assign fv_kv_mlkem_seed_data_present = pi_abr_reg_hwif_out_i.kv_mlkem_seed_rd_ctrl.read_en.value;

    //flag for mlkem_seed_data_present
    logic fv_kv_mlkem_seed_data_present_flag;
    always_ff @(posedge pi_clk or negedge pi_rst_b) begin: fv_flag_kv_mlkem_seed_data_present
        if (!pi_rst_b || po_zeroize) begin
            fv_kv_mlkem_seed_data_present_flag <= '0;
        end else if (fv_kv_mlkem_seed_data_present) begin
            fv_kv_mlkem_seed_data_present_flag <= '1;
        end
    end

    //Aux logic to model and latch kv mlkem seed error responses
    logic fv_kv_mlkem_seed_error_flag;
    logic fv_kv_mlkem_seed_error;

    //Aux logic to model RTL's stored_last_dword/length_mismatch check (kv_read_client.sv):
    //the KV entry's actual size (entry_last_dword) is latched on each write beat, and checked
    //against the client's expected_key_size (2*SEED_NUM_DWORDS-1) once the read completes.
    //A short entry (e.g. an early kv_resp.last) fails this check even though no per-beat
    //kv_resp.error was ever seen.
    logic [KV_ENTRY_SIZE_W-1:0] fv_kv_mlkem_seed_stored_last_dword;
    always_ff @(posedge pi_clk or negedge pi_rst_b) begin: fv_reg_kv_mlkem_seed_stored_last_dword
        if (!pi_rst_b || po_zeroize) begin
            fv_kv_mlkem_seed_stored_last_dword <= '0;
        end else if (fv_kv_mlkem_seed_we) begin
            fv_kv_mlkem_seed_stored_last_dword <= pi_kv_rd_resp[1].entry_last_dword;
        end
    end

    logic fv_kv_mlkem_seed_length_mismatch;
    assign fv_kv_mlkem_seed_length_mismatch = fv_kv_mlkem_seed_done && (fv_kv_mlkem_seed_stored_last_dword < (2*SEED_NUM_DWORDS-1));

    assign fv_kv_mlkem_seed_error = ((fv_kv_mlkem_seed_cs == fv_st_read_type) && pi_kv_rd_resp[1].error) || (!fv_kv_mlkem_seed_read_rules_allow && fv_kv_mlkem_seed_read_start) || fv_kv_mlkem_seed_length_mismatch;

    always_ff @(posedge pi_clk or negedge pi_rst_b) begin: fv_reg_kv_mlkem_seed_error
        if (!pi_rst_b || po_zeroize) begin
            fv_kv_mlkem_seed_error_flag <= '0;
        end else if (fv_kv_mlkem_seed_error) begin
            fv_kv_mlkem_seed_error_flag <= '1;
        end
        //Per spec (CaliptraHardwareSpecification.md, KV key-length-mismatch detection / KV cryptographic functional block):
        //the KV read error self-holds and is cleared only by rst_b or zeroize. A new read request must NOT clear it.
    end

    //Model ready signal for mldsa seed kv client
    assign fv_kv_mlkem_seed_ready = (fv_kv_mlkem_seed_cs == fv_st_idle_type) && !fv_kv_mlkem_seed_read_start && !fv_kv_mlkem_seed_error_flag;


    //Model swwe for mlkem_seed_d
    logic [SEED_NUM_DWORDS-1:0][31:0]   fv_mldsa_seed_d_swwe_data;
    logic                               fv_mlkem_seed_swwe;
    logic                               fv_mlkem_seed_swwe_ff;

    assign fv_mlkem_seed_swwe = !fv_kv_mlkem_seed_data_present_flag && po_abr_reg_hwif_in_o.abr_ready;

    //Latch the swwe for mldsa_seed
    always_ff @(posedge pi_clk or negedge pi_rst_b) begin: fv_mlkem_seed_swwe_ff_process
        if (!pi_rst_b) begin
            fv_mlkem_seed_swwe_ff <= 'd0;
        end else begin
            fv_mlkem_seed_swwe_ff <= fv_mlkem_seed_swwe;
        end
    end

    //model the sw writes, if swwe, the MLDSA_SEED input is the data to feed into the temp reg
    //has to be modeled combinatorially
    always_comb begin: fv_mlkem_seed_d_sw_data
        fv_mldsa_seed_d_swwe_data = '0;
        if (fv_mlkem_seed_swwe_ff) begin
            for (int i=0; i<SEED_NUM_DWORDS; i++) begin
                fv_mldsa_seed_d_swwe_data[i] = pi_abr_reg_hwif_out_i.MLKEM_SEED_D[i].SEED.value;
            end
        end
    end


    //Checking equivalence of modeled mlkem_seed_done and RTL
    assert_kv_mlkem_seed_done_eq: assert property (disable iff (!pi_rst_b | po_zeroize) kv_done_eq(fv_kv_mlkem_seed_done, abr_ctrl.kv_mlkem_seed_done));

    //Checking equivalence between the aux logic of offset and kv_read.read_offset
    assert_kv_mlkem_seed_offset_eq: assert property (disable iff (!pi_rst_b | po_zeroize) kv_offset_eq(abr_ctrl.kv_mlkem_seed_write_en, fv_kv_mlkem_seed_words_cntr, po_kv_read[1].read_offset));

    //Checking equivalence of modeled kv_mlkem_seed_ready and RTL
    assert_kv_mlkem_seed_ready_eq: assert property (disable iff (!pi_rst_b | po_zeroize) kv_ready_eq(fv_kv_mlkem_seed_ready, abr_ctrl.kv_mlkem_seed_ready));


    //Model MLKEM busy signal
    logic fv_mlkem_busy;
    assign fv_mlkem_busy = abr_ctrl.mlkem_keygen_process | abr_ctrl.mlkem_encaps_process | abr_ctrl.mlkem_decaps_process | abr_ctrl.mlkem_keygen_decaps_process;


    //Assertion: If computation has started, no more kv reads should happen.
    assert_if_busy_no_more_mlkem_seed_kv_read: assert property (disable iff (!pi_rst_b | po_zeroize) if_busy_no_more_kv_read(fv_mlkem_busy, abr_ctrl.kv_mlkem_seed_write_en));


    // Aux logic to latch the value of kv_mlkem_seed_rd_ctrl.read_en until the end of MLKEM operation
    logic fv_kv_mlkem_seed_req;

    always_ff @(posedge pi_clk or negedge pi_rst_b) begin: fv_reg_kv_mlkem_seed_req
        if (!pi_rst_b) begin
            fv_kv_mlkem_seed_req <= '0;
        end else if (pi_abr_reg_hwif_out_i.kv_mlkem_seed_rd_ctrl.read_en.value) begin
            fv_kv_mlkem_seed_req <= '1;
        end
        //read_en has precedence over zeroize to cover the case when read enables come in the same cc as zeroize
        else if (po_zeroize) begin
            fv_kv_mlkem_seed_req <= '0;
        end else if (abr_ctrl.mlkem_process_done) begin
            fv_kv_mlkem_seed_req <= '0;
        end
    end

   //Save the kv client done signal until end of operation
    logic fv_kv_mlkem_seed_done_flag;
    always_ff @(posedge pi_clk or negedge pi_rst_b) begin: fv_kv_mlkem_seed_done_flag_ff
        if (!pi_rst_b || po_zeroize) begin
            fv_kv_mlkem_seed_done_flag <= '0;
        end else if (fv_kv_mlkem_seed_done) begin
            fv_kv_mlkem_seed_done_flag <= '1;
        end else if (abr_ctrl.mlkem_process_done) begin
            fv_kv_mlkem_seed_done_flag <= '0;
        end
    end

    //Conditions that can write to abr_scratch register that affect the mlkem_enc.seed_z (union bits overlap)
    logic fv_ek_hit, fv_dk_hit, fv_sk_hit, fv_pk_hit;
    assign fv_ek_hit = po_abr_reg_hwif_in_o.MLKEM_ENCAPS_KEY.wr_ack & po_abr_reg_hwif_in_o.abr_ready & abr_ctrl.mlkem_api_ek_reg_dec;
    assign fv_dk_hit = po_abr_reg_hwif_in_o.MLKEM_DECAPS_KEY.wr_ack & po_abr_reg_hwif_in_o.abr_ready & abr_ctrl.mlkem_api_dk_reg_dec;
    assign fv_sk_hit = po_abr_reg_hwif_in_o.MLDSA_PRIVKEY_IN.wr_ack & po_abr_reg_hwif_in_o.abr_ready & abr_ctrl.api_sk_reg_wr_dec;
    assign fv_pk_hit = po_abr_reg_hwif_in_o.abr_ready & abr_ctrl.api_pubkey_rho_dec & pi_abr_reg_hwif_out_i.MLDSA_PUBKEY.req_is_wr;

    //only need to update fv_mlkem_seed_z if the bits of "mlkem_enc.seed_z" overlap with the ones being updated in the union
    logic fv_ek_in_range, fv_dk_in_range, fv_sk_in_range, fv_pk_in_range;
    assign fv_ek_in_range = (abr_ctrl.mlkem_api_ek_reg_addr inside {[16:23]});
    assign fv_dk_in_range = (abr_ctrl.mlkem_api_dk_reg_addr inside {[16:23]});
    assign fv_sk_in_range = (abr_ctrl.api_sk_reg_waddr inside {[16:23]});
    assign fv_pk_in_range = (abr_ctrl.api_pk_reg_waddr inside {[16:23]});

    //Save the kv response data into a temp register to match KV endianness
    //First 8 words received from KV are for mldsa_seed_d
    //Second 8 words received from KV are for mldsa_seed_z
    //The fv_mlkem_seed_data aux logic switches up the order of those words
    always_ff @(posedge pi_clk or negedge pi_rst_b) begin: fv_kv_mlkem_seed_data_ff
        if (!pi_rst_b) begin
            fv_kv_mlkem_seed_data <= 'd0;
        end else begin
            //model sw write for mlkem_d
            if (fv_mlkem_seed_swwe_ff) begin
                fv_kv_mlkem_seed_data[(2*SEED_NUM_DWORDS)-1:SEED_NUM_DWORDS] <= fv_mldsa_seed_d_swwe_data;
            end
            //model sw write for mlkem_z (it can be populated by many sources, since abr_scratch is of type union)
            if (pi_sampler_state_dv_i) begin
                if (abr_ctrl.abr_instr.operand3 == MLDSA_DEST_TR_REG_ID) begin
                    fv_kv_mlkem_seed_data[SEED_NUM_DWORDS-1:0] <= pi_sampler_state_data_i[255:0];
                end
            end
            else if (fv_ek_hit) begin
                if (fv_ek_in_range) begin
                    fv_kv_mlkem_seed_data[abr_ctrl.mlkem_api_ek_reg_addr - 16] <= pi_abr_reg_hwif_out_i.MLKEM_ENCAPS_KEY.wr_data;
                end
            end
            else if (fv_dk_hit) begin
                if (fv_dk_in_range) begin
                    fv_kv_mlkem_seed_data[abr_ctrl.mlkem_api_dk_reg_addr - 16] <= pi_abr_reg_hwif_out_i.MLKEM_DECAPS_KEY.wr_data;
                end
            end
            else if (fv_sk_hit) begin
                if (fv_sk_in_range) begin
                    fv_kv_mlkem_seed_data[abr_ctrl.api_sk_reg_waddr - 16] <=pi_abr_reg_hwif_out_i.MLDSA_PRIVKEY_IN.wr_data;
                end
            end
            else if (fv_pk_hit) begin
                if (fv_pk_in_range) begin
                    fv_kv_mlkem_seed_data[16-abr_ctrl.api_pk_reg_waddr - 16] <= pi_abr_reg_hwif_out_i.MLDSA_PUBKEY.wr_data;
                end
            end
            else begin
                for (int j=0; j<SEED_NUM_DWORDS; j++) begin
                    if (pi_abr_reg_hwif_out_i.MLKEM_SEED_Z[j].req & pi_abr_reg_hwif_out_i.MLKEM_SEED_Z[j].req_is_wr & fv_mlkem_seed_swwe) begin
                        fv_kv_mlkem_seed_data[j] <= pi_abr_reg_hwif_out_i.MLKEM_SEED_Z[j].wr_data;
                    end
                end
            end
            if (fv_kv_mlkem_seed_we) begin
                fv_kv_mlkem_seed_data[2*SEED_NUM_DWORDS - fv_kv_mlkem_seed_words_cntr] <= pi_kv_rd_resp[1].read_data;
            end
            //errors erase the MLKEM_SEED_D from API
            if (fv_kv_mlkem_seed_error_flag) begin
                fv_kv_mlkem_seed_data[(2*SEED_NUM_DWORDS)-1:SEED_NUM_DWORDS] <= 'd0;
            end
            if (po_zeroize) begin
                fv_kv_mlkem_seed_data <= 'd0;
            end
        end
    end


    //Assertion: Before busy is asserted, KV state machine should have completed
    assert_before_busy_kv_mlkem_seed_done: assert property (disable iff (!pi_rst_b | po_zeroize) before_busy_kv_done(fv_mlkem_busy, fv_kv_mlkem_seed_req, fv_kv_mlkem_seed_done_flag));


    //Assertions: When the KV is done, MLKEM_SEED_D[].SEED.value should have the correct data
    //Exception: Not checking the case where read_en arrives at the same cc with zeroize
    genvar fv_mlkem_seed_d_var;
    generate
        for(fv_mlkem_seed_d_var=0; fv_mlkem_seed_d_var<SEED_NUM_DWORDS; fv_mlkem_seed_d_var++) begin: gen_mlkem_seed_d_data_assertions
            assert_kv_mlkem_seed_d_data_rd_integrity: assert property (disable iff (!pi_rst_b | po_zeroize) kv_data_rd_integrity(fv_kv_mlkem_seed_done, 1'b0,
                                                                                                                                        fv_kv_mlkem_seed_data_present_flag,
                                                                                                                                            abr_ctrl.mlkem_seed_d_reg[fv_mlkem_seed_d_var],
                                                                                                                                                fv_kv_mlkem_seed_data[fv_mlkem_seed_d_var + SEED_NUM_DWORDS]));
        end
    endgenerate

    //Assertions: When the KV is done, abr_scratch_reg.mlkem_enc.seed_z[i] should have the correct data
    genvar fv_mlkem_seed_z_var;
    generate
        for(fv_mlkem_seed_z_var=0; fv_mlkem_seed_z_var<SEED_NUM_DWORDS; fv_mlkem_seed_z_var++) begin: gen_mlkem_seed_z_data_assertions
            assert_kv_mlkem_seed_z_data_rd_integrity: assert property (disable iff (!pi_rst_b | po_zeroize) kv_data_rd_integrity(fv_kv_mlkem_seed_done, 1'b0,
                                                                                                                                    fv_kv_mlkem_seed_data_present_flag,
                                                                                                                                        abr_ctrl.abr_scratch_reg.mlkem_enc.seed_z[fv_mlkem_seed_z_var],
                                                                                                                                            fv_kv_mlkem_seed_data[fv_mlkem_seed_z_var]));
        end
    endgenerate

    //Assertions: HW write enable is asserted with its corresponding write offset
    genvar fv_mlkem_seed_we_var0;
    generate
        for(fv_mlkem_seed_we_var0=0; fv_mlkem_seed_we_var0<SEED_NUM_DWORDS; fv_mlkem_seed_we_var0++) begin: gen_mlkem_seed_offset_high_assertions
            assert_mlkem_seed_we_kv_mlkem_seed_write_offset_high_match: assert property (disable iff (!pi_rst_b | po_zeroize) hwwe_kv_write_offset_match_high(abr_ctrl.kv_mlkem_seed_write_en, fv_kv_mlkem_seed_words_cntr,
                                                                                                                                                        SEED_NUM_DWORDS, fv_mlkem_seed_we_var0,
                                                                                                                                                            po_abr_reg_hwif_in_o.MLKEM_SEED_D[fv_mlkem_seed_we_var0].SEED.we));
        end
    endgenerate

    //Assertions: HW write enable is deasserted when write offset doesn't correspond
    genvar fv_mlkem_seed_we_var1;
    generate
        for(fv_mlkem_seed_we_var1=0; fv_mlkem_seed_we_var1<SEED_NUM_DWORDS; fv_mlkem_seed_we_var1++) begin: gen_mlkem_seed_offset_low_assertions
            assert_mlkem_seed_we_kv_mlkem_seed_write_offset_low_match: assert property (disable iff (!pi_rst_b | po_zeroize) hwwe_kv_write_offset_match_low(abr_ctrl.kv_mlkem_seed_write_en, fv_kv_mlkem_seed_words_cntr,
                                                                                                                                                        SEED_NUM_DWORDS, fv_mlkem_seed_we_var1, 1'b0,
                                                                                                                                                            po_abr_reg_hwif_in_o.MLKEM_SEED_D[fv_mlkem_seed_we_var1].SEED.we));
        end
    endgenerate


    //Assertion: Data read from KV should be stable the moment a cmd is received (mlkem_busy) till end of operation
    //seed_d
    assert_kv_mlkem_seed_d_data_stable: assert property (disable iff (!pi_rst_b | po_zeroize) kv_data_stable(fv_kv_mlkem_seed_done_flag, fv_mlkem_busy, abr_ctrl.mlkem_seed_d_reg));



    ///////////////////////////////////////////////////////////////////////Requirement 2: Choose the specific slot meant for KV if it's a read///////////////////////////////////////////////////////////////////////

    assert_kv_mlkem_seed_rd_entry: assert property (disable iff (!pi_rst_b | po_zeroize) kv_rd_entry(pi_abr_reg_hwif_out_i.kv_mlkem_seed_rd_ctrl.read_en.value, pi_abr_reg_hwif_out_i.kv_mlkem_seed_rd_ctrl.read_entry.value,
                                                                                                        po_kv_read[1].read_entry));



    ///////////////////////////////////////////////////////////////////////Requirement 5: If a secret is read from KV then the associated writes shouldn't be from api////////////////////////////////////////////////

    //If the read request was for KV, the private key lock should be asserted, and no data should be leaked to API
    assert_no_mlkem_secret_leaked_to_api: assert property (disable iff (!pi_rst_b | po_zeroize) no_secret_leaked_to_api(fv_kv_mlkem_seed_data_present_flag, abr_ctrl.mlkem_dk_lock, po_abr_reg_hwif_in_o.MLKEM_DECAPS_KEY.rd_data));

    //By default, lock is asserted
    assert_mlkem_default_lock_assertion: assert property (default_lock_assertion(fv_mlkem_busy, abr_ctrl.mlkem_keygen_done, abr_ctrl.mlkem_dk_lock));

    //If the request was not for KV, and the keygen operation has finished, the private lock should be released
    assert_lock_deasserted_after_mlkem_keygen: assert property (disable iff (!pi_rst_b | po_zeroize) lock_deasserted(fv_kv_mlkem_seed_data_present_flag, abr_ctrl.mlkem_keygen_done, abr_ctrl.mlkem_dk_lock));



    ///////////////////////////////////////////////////////////////////////Requirement 6: Reset/Zeroize erase the entire data to/from KV////////////////////////////////////////////////////////////////////////////

    genvar fv_mlkem_seed_we_var2;
    generate
        for(fv_mlkem_seed_we_var2=0; fv_mlkem_seed_we_var2<SEED_NUM_DWORDS; fv_mlkem_seed_we_var2++) begin: gen_mlkem_seed_write_enable_assertions
            assert_erase_mlkem_seed_hw_write_enable: assert property (erase_hw_write_enable(po_abr_reg_hwif_in_o.MLKEM_SEED_D[fv_mlkem_seed_we_var2].SEED.we));
        end
    endgenerate


    //MLKEM seed KV client write_en should be cleared on zeroize or reset
    assert_kv_erase_mlkem_seed_write_enable: assert property (kv_erase_write_enable(abr_ctrl.kv_mlkem_seed_write_en));


    //kv_read[].read_offset should be cleared on zeroize or reset
    assert_kv_erase_mlkem_seed_read_offset: assert property (kv_erase_read_offset(po_kv_read[1].read_offset));


    //MLKEM_SEED_D[].SEED.hwclr is asserted either in zeroize or when KV responds with error
    genvar fv_mlkem_seed_hwclr_var;
    generate
        for(fv_mlkem_seed_hwclr_var=0; fv_mlkem_seed_hwclr_var<SEED_NUM_DWORDS; fv_mlkem_seed_hwclr_var++) begin: gen_mlkem_seed_hwclr_assertions
            assert_mlkem_seed_hwclrs: assert property (seed_hwclr(po_abr_reg_hwif_in_o.MLKEM_SEED_D[fv_mlkem_seed_hwclr_var].SEED.hwclr, fv_kv_mlkem_seed_error_flag));
        end
    endgenerate


    ///////////////////////////////////////////////////////////////////////Requirement 7: No operation in the crypto engine without full read or write/////////////////////////////////////////////////////////

    assert_no_crypto_engine_op_without_full_mlkem_seed_read: assert property (no_crypto_engine_op_without_full_read(fv_kv_mlkem_seed_req, fv_kv_mlkem_seed_done_flag));

    //KV read error on mlkem seed blocks MLKEM commands until zeroize
    assert_no_mlkem_cmd_after_kv_mlkem_seed_error: assert property (disable iff (!pi_rst_b | po_zeroize) no_cmd_after_kv_error(fv_kv_mlkem_seed_error_flag, fv_mlkem_busy));




    ///////////////////////////////////////////////////////////////////////////Requirement 8: In MLKEM mode, all KV MLDSA outputs are deasserted//////////////////////////////////////////////////////////////


    property no_mldsa_read_if_mlkem_mode;
        fv_mlkem_busy
    |->
        (po_kv_read[0].read_offset == '0) && !abr_ctrl.kv_mldsa_seed_write_en
    endproperty

    assert_no_mldsa_read_if_mlkem_mode: assert property (disable iff (!pi_rst_b | po_zeroize) no_mldsa_read_if_mlkem_mode);


    ////////////////////////////////////////////////////////////////////////////Requirement 9: Primary Outputs assertions/////////////////////////////////////////////////////////////////////////////////////////////////////

    //Assertions for swwe for each rd_ctrl_reg field of kv_mlkem_seed
    assert_kv_mlkem_seed_rd_ctrl_read_en_swwe: assert property (disable iff (!pi_rst_b | po_zeroize) kv_rd_ctrl_swwe(po_abr_reg_hwif_in_o.kv_mlkem_seed_rd_ctrl.read_en.swwe, fv_mlkem_seed_swwe));
    assert_kv_mlkem_seed_rd_ctrl_read_entry_swwe: assert property (disable iff (!pi_rst_b | po_zeroize) kv_rd_ctrl_swwe(po_abr_reg_hwif_in_o.kv_mlkem_seed_rd_ctrl.read_entry.swwe, fv_mlkem_seed_swwe));
    assert_kv_mlkem_seed_rd_ctrl_rsvd_swwe: assert property (disable iff (!pi_rst_b | po_zeroize) kv_rd_ctrl_swwe(po_abr_reg_hwif_in_o.kv_mlkem_seed_rd_ctrl.rsvd.swwe, 0));
    assert_kv_mlkem_seed_rd_ctrl_pcr_hash_extend_swwe: assert property (disable iff (!pi_rst_b | po_zeroize) kv_rd_ctrl_swwe(po_abr_reg_hwif_in_o.kv_mlkem_seed_rd_ctrl.pcr_hash_extend.swwe, 0));


    //Assertion for hwclr for kv_mlkem_seed_rd_ctrl.read_en
    assert_kv_mlkem_seed_rd_ctrl_read_en_hwclr: assert property (disable iff (!pi_rst_b | po_zeroize) kv_rd_ctrl_read_en_hwclr(po_abr_reg_hwif_in_o.kv_mlkem_seed_rd_ctrl.read_en.hwclr, abr_ctrl.kv_mlkem_seed_ready));

    //Assertion for kv_mlkem_seed_rd_status.READY
    assert_kv_mlkem_seed_rd_status_ready: assert property (disable iff (!pi_rst_b | po_zeroize) kv_rd_status_ready(po_abr_reg_hwif_in_o.kv_mlkem_seed_rd_status.READY.next, abr_ctrl.kv_mlkem_seed_ready));

    //Assertion for kv_mlkem_seed_rd_status.VALID.hwclr
    assert_kv_mlkem_seed_rd_status_valid_hwclr: assert property (disable iff (!pi_rst_b | po_zeroize) kv_rd_status_valid_hwclr(po_abr_reg_hwif_in_o.kv_mlkem_seed_rd_status.VALID.hwclr, pi_abr_reg_hwif_out_i.kv_mlkem_seed_rd_ctrl.read_en.value));

    //Assertion for kv_mlkem_seed_rd_status.VALID.hwset
    assert_kv_mlkem_seed_rd_status_valid_hwset: assert property (disable iff (!pi_rst_b | po_zeroize) kv_rd_status_valid_hwset(po_abr_reg_hwif_in_o.kv_mlkem_seed_rd_status.VALID.hwset, abr_ctrl.kv_mlkem_seed_done));

    //Assertion for kv_mlkem_seed_rd_status.ERROR
    assert_kv_mlkem_seed_rd_status_error: assert property (disable iff (!pi_rst_b | po_zeroize) kv_rd_status_error(po_abr_reg_hwif_in_o.kv_mlkem_seed_rd_status.ERROR.next, abr_ctrl.kv_mlkem_seed_error));





    ////////////////////////////////////////////////////////////////////////////////////////////////MLKEM msg//////////////////////////////////////////////////////////////////////////////////////////////////
    ///////////////////////////////////////////////////////////////////////Requirement 1: Before computation starts, data from KV is read///////////////////////////////////////////////////////////////////////


    // Aux logic to model KV MLKEM seed client read state machine
    fvFsmState                              fv_kv_mlkem_msg_cs, fv_kv_mlkem_msg_ns;
    logic [$clog2(MLKEM_MSG_MEM_NUM_DWORDS):0]  fv_kv_mlkem_msg_words_cntr;
    logic                                       fv_kv_mlkem_msg_read_rules_fail;
    logic                                       fv_kv_mlkem_msg_read_start;
    logic                                       fv_kv_mlkem_msg_read_rules_allow;
    logic                                       fv_kv_mlkem_msg_complete;
    logic                                       fv_kv_mlkem_msg_done;
    logic                                       fv_kv_mlkem_msg_we;
    logic [MLKEM_MSG_MEM_NUM_DWORDS-1:0][31:0]  fv_kv_mlkem_msg_data;
    logic                                       fv_kv_mlkem_msg_ready;

    always_ff @(posedge pi_clk or negedge pi_rst_b) begin: fv_kv_mlkem_msg_state_update
        if (!pi_rst_b || po_zeroize) begin
            fv_kv_mlkem_msg_cs <= fv_st_idle_type;
        end else begin
            fv_kv_mlkem_msg_cs <= fv_kv_mlkem_msg_ns;
        end
    end

    //if ocp_lock_in_progress, the crypto-engine shall not read from OCP_LOCK_KEY_RELEASE_KV_SLOT
    assign fv_kv_mlkem_msg_read_rules_fail = pi_ocp_lock_in_progress && (pi_abr_reg_hwif_out_i.kv_mlkem_msg_rd_ctrl.read_entry == OCP_LOCK_KEY_RELEASE_KV_SLOT);

    //Modeling of read_start signal and rules_allow signal to trigger the KV read process correctly
    always_ff @(posedge pi_clk or negedge pi_rst_b) begin: fv_kv_mlkem_msg_conditions_update
        if (!pi_rst_b) begin
            fv_kv_mlkem_msg_read_start        <= '0;
            fv_kv_mlkem_msg_read_rules_allow  <= '0;
        end
        else if (fv_kv_mlkem_msg_done) begin
            fv_kv_mlkem_msg_read_start        <= '0;
            fv_kv_mlkem_msg_read_rules_allow  <= '0;
        end
        else if (pi_abr_reg_hwif_out_i.kv_mlkem_msg_rd_ctrl.read_en.value) begin
            fv_kv_mlkem_msg_read_start        <= '1;
            fv_kv_mlkem_msg_read_rules_allow  <= !fv_kv_mlkem_msg_read_rules_fail;
        end
        else if (po_zeroize) begin
            fv_kv_mlkem_msg_read_start        <= '0;
            fv_kv_mlkem_msg_read_rules_allow  <= '0;
        end

    end

    assign fv_kv_mlkem_msg_complete    = (fv_kv_mlkem_msg_words_cntr == MLKEM_MSG_MEM_NUM_DWORDS) || pi_kv_rd_resp[2].last;


    //Aux logic to count the number of words received from KV to know when to terminate the state machine if maximum has reached
    always_ff @(posedge pi_clk or negedge pi_rst_b) begin: fv_kv_mlkem_msg_cntr_update
        if (!pi_rst_b || po_zeroize) begin
            fv_kv_mlkem_msg_words_cntr <= 'd0;
        end else if(fv_kv_mlkem_msg_done) begin
            fv_kv_mlkem_msg_words_cntr <= 'd0;
        end else if (fv_kv_mlkem_msg_ns == fv_st_read_type) begin
            fv_kv_mlkem_msg_words_cntr <= fv_kv_mlkem_msg_words_cntr + 'd1;
        end
    end

    //Aux logic for the KV state machine to model the done signal
    always_comb begin: fv_kv_mlkem_msg_fsm
        fv_kv_mlkem_msg_ns     = fv_kv_mlkem_msg_cs;
        fv_kv_mlkem_msg_done   = 1'b0;
        fv_kv_mlkem_msg_we     = 1'b0;
        unique case (fv_kv_mlkem_msg_cs)
            fv_st_idle_type: begin
                if (fv_kv_mlkem_msg_read_start) begin
                    if (fv_kv_mlkem_msg_read_rules_allow) begin
                        fv_kv_mlkem_msg_ns = fv_st_read_type;
                    end else begin
                        fv_kv_mlkem_msg_ns = fv_st_done_type;
                    end
                end
            end
            fv_st_read_type: begin
                fv_kv_mlkem_msg_we = 1'b1;
                //RTL kv_fsm aborts the transfer on a KV read error (abort_i = kv_resp.error),
                //jumping to KV_DONE on that beat regardless of how many dwords were read
                if (pi_kv_rd_resp[2].error || fv_kv_mlkem_msg_complete) begin
                    fv_kv_mlkem_msg_ns = fv_st_done_type;
                end
            end
            fv_st_done_type: begin
                fv_kv_mlkem_msg_done = 1'b1;
                fv_kv_mlkem_msg_ns = fv_st_idle_type;
            end
            default: begin
                fv_kv_mlkem_msg_ns = fv_st_idle_type;
            end
        endcase
    end

    logic fv_kv_mlkem_msg_data_present;
    assign fv_kv_mlkem_msg_data_present = pi_abr_reg_hwif_out_i.kv_mlkem_msg_rd_ctrl.read_en.value;

    //flag for mlkem_seed_data_present
    logic fv_kv_mlkem_msg_data_present_flag;
    always_ff @(posedge pi_clk or negedge pi_rst_b) begin: fv_flag_kv_mlkem_msg_data_present
        if (!pi_rst_b || po_zeroize) begin
            fv_kv_mlkem_msg_data_present_flag <= '0;
        end else if (fv_kv_mlkem_msg_data_present) begin
            fv_kv_mlkem_msg_data_present_flag <= '1;
        end
    end

    //Aux logic to model and latch kv mlkem msg error responses
    logic fv_kv_mlkem_msg_error_flag;
    logic fv_kv_mlkem_msg_error;

    //Aux logic to model RTL's stored_last_dword/length_mismatch check (kv_read_client.sv):
    //the KV entry's actual size (entry_last_dword) is latched on each write beat, and checked
    //against the client's expected_key_size (MLKEM_MSG_MEM_NUM_DWORDS-1) once the read completes.
    //A short entry fails this check even though no per-beat kv_resp.error was ever seen.
    logic [KV_ENTRY_SIZE_W-1:0] fv_kv_mlkem_msg_stored_last_dword;
    always_ff @(posedge pi_clk or negedge pi_rst_b) begin: fv_reg_kv_mlkem_msg_stored_last_dword
        if (!pi_rst_b || po_zeroize) begin
            fv_kv_mlkem_msg_stored_last_dword <= '0;
        end else if (fv_kv_mlkem_msg_we) begin
            fv_kv_mlkem_msg_stored_last_dword <= pi_kv_rd_resp[2].entry_last_dword;
        end
    end

    logic fv_kv_mlkem_msg_length_mismatch;
    assign fv_kv_mlkem_msg_length_mismatch = fv_kv_mlkem_msg_done && (fv_kv_mlkem_msg_stored_last_dword < (MLKEM_MSG_MEM_NUM_DWORDS-1));

    assign fv_kv_mlkem_msg_error = ((fv_kv_mlkem_msg_cs == fv_st_read_type) && pi_kv_rd_resp[2].error) || (!fv_kv_mlkem_msg_read_rules_allow && fv_kv_mlkem_msg_read_start) || fv_kv_mlkem_msg_length_mismatch;

    always_ff @(posedge pi_clk or negedge pi_rst_b) begin: fv_reg_kv_mlkem_msg_error
        if (!pi_rst_b || po_zeroize) begin
            fv_kv_mlkem_msg_error_flag <= '0;
        end else if (fv_kv_mlkem_msg_error) begin
            fv_kv_mlkem_msg_error_flag <= '1;
        end
        //Per spec (CaliptraHardwareSpecification.md, KV key-length-mismatch detection / KV cryptographic functional block):
        //the KV read error self-holds and is cleared only by rst_b or zeroize. A new read request must NOT clear it.
    end

    //Model ready signal for mldsa seed kv client
    assign fv_kv_mlkem_msg_ready = (fv_kv_mlkem_msg_cs == fv_st_idle_type) && !fv_kv_mlkem_msg_read_start && !fv_kv_mlkem_msg_error_flag;

    logic fv_mlkem_msg_swwe;
    assign fv_mlkem_msg_swwe = !fv_kv_mlkem_msg_data_present_flag && po_abr_reg_hwif_in_o.abr_ready;

    //Save the kv response data into a temp register
    always_comb begin: fv_kv_mlkem_msg_data_comb
        if (fv_kv_mlkem_msg_we) begin
            fv_kv_mlkem_msg_data[fv_kv_mlkem_msg_words_cntr - 'd1] = pi_kv_rd_resp[2].read_data;
        end else begin
            fv_kv_mlkem_msg_data = 'd0;
        end
    end


    //Checking equivalence of modeled mlkem_msg_done and RTL
    assert_kv_mlkem_msg_done_eq: assert property (disable iff (!pi_rst_b | po_zeroize) kv_done_eq(fv_kv_mlkem_msg_done, abr_ctrl.kv_mlkem_msg_done));

    //Checking equivalence between the aux logic of offset and kv_read.read_offset
    assert_kv_mlkem_msg_offset_eq: assert property (disable iff (!pi_rst_b | po_zeroize) kv_offset_eq(abr_ctrl.kv_mlkem_msg_write_en, fv_kv_mlkem_msg_words_cntr, po_kv_read[2].read_offset));

    //Checking equivalence of modeled kv_mlkem_seed_ready and RTL
    assert_kv_mlkem_msg_ready_eq: assert property (disable iff (!pi_rst_b | po_zeroize) kv_ready_eq(fv_kv_mlkem_msg_ready, abr_ctrl.kv_mlkem_msg_ready));

    //Assertion: If computation has started, no more kv reads should happen.
    assert_if_busy_no_more_mlkem_msg_kv_read: assert property (disable iff (!pi_rst_b | po_zeroize) if_busy_no_more_kv_read(fv_mlkem_busy, abr_ctrl.kv_mlkem_msg_write_en));


    // Aux logic to latch the value of kv_mlkem_msg_rd_ctrl.read_en until the end of MLKEM operation
    logic fv_kv_mlkem_msg_req;

    always_ff @(posedge pi_clk or negedge pi_rst_b) begin: fv_reg_kv_mlkem_msg_req
        if (!pi_rst_b) begin
            fv_kv_mlkem_msg_req <= '0;
        end else if (pi_abr_reg_hwif_out_i.kv_mlkem_msg_rd_ctrl.read_en.value) begin
            fv_kv_mlkem_msg_req <= '1;
        end
        //read_en has precedence over zeroize to cover the case when read enables come in the same cc as zeroize
        else if (po_zeroize) begin
            fv_kv_mlkem_msg_req <= '0;
        end else if (abr_ctrl.mlkem_process_done) begin
            fv_kv_mlkem_msg_req <= '0;
        end
    end

   //Save the kv client done signal until end of operation
    logic fv_kv_mlkem_msg_done_flag;
    always_ff @(posedge pi_clk or negedge pi_rst_b) begin: fv_kv_mlkem_msg_done_flag_ff
        if (!pi_rst_b || po_zeroize) begin
            fv_kv_mlkem_msg_done_flag <= '0;
        end else if (fv_kv_mlkem_msg_done) begin
            fv_kv_mlkem_msg_done_flag <= '1;
        end else if (abr_ctrl.mlkem_process_done) begin
            fv_kv_mlkem_msg_done_flag <= '0;
        end
    end

    //Assertion: Before busy is asserted, KV state machine should have completed
    assert_before_busy_kv_mlkem_msg_done: assert property (disable iff (!pi_rst_b | po_zeroize) before_busy_kv_done(fv_mlkem_busy, fv_kv_mlkem_msg_req, fv_kv_mlkem_msg_done_flag));


    //Assertion, check that KV read data is being written into temp reg mlkem_msg_wdata.
    //Each word is written at a time
    property kv_mlkem_msg_rd_integrity(i);
        fv_kv_mlkem_msg_we && (fv_kv_mlkem_msg_words_cntr - 'd1 == i)
    |->
        fv_kv_mlkem_msg_data[i] == abr_ctrl.mlkem_msg_wdata
    endproperty

    genvar fv_mlkem_msg_var;
    generate
        for(fv_mlkem_msg_var = 0; fv_mlkem_msg_var < MLKEM_MSG_MEM_NUM_DWORDS; fv_mlkem_msg_var++) begin: gen_mlkem_msg_data_integrity_assertions
            assert_kv_mlkem_msg_rd_integrity: assert property (disable iff (!pi_rst_b | po_zeroize) kv_mlkem_msg_rd_integrity(fv_mlkem_msg_var));
        end
    endgenerate

    //Spec-based check of where the KV mlkem msg lands in SK RAM and where the consumer reads it from.
    //Expected values are derived independently of the RTL address/bank muxing:
    // - CaliptraHardwareSpecification.md (KV endianness): ML-KEM KV reads are DWORD-reversed, MSG[d] = KV[N-1-d],
    //   i.e. the KV beat at read_offset o is msg dword N-1-o
    // - AdamsBridge_MLKEM.md: msg is 8 little-endian dwords, same layout as the MLKEM_MSG API register (MSG[d] -> msg region + d)
    // - msg region base in SK RAM is the design memory-map parameter MLKEM_DEST_MSG_MEM_OFFSET (flat dword address);
    //   SK RAM is split in 2 banks by flat address bit 0, bank address = flat address >> 1
    //fv_kv_mlkem_msg_words_cntr = read_offset + 1 on a write beat, so msg dword index = N - words_cntr
    logic [ABR_OPR_WIDTH-1:0]   fv_sk_ram_msg_exp_waddr;
    logic                       fv_sk_ram_msg_exp_bank;

    assign fv_sk_ram_msg_exp_waddr = MLKEM_DEST_MSG_MEM_OFFSET + ABR_OPR_WIDTH'(MLKEM_MSG_MEM_NUM_DWORDS - fv_kv_mlkem_msg_words_cntr);
    assign fv_sk_ram_msg_exp_bank  = fv_sk_ram_msg_exp_waddr[0];

    //Each non-errored KV msg beat is written to exactly the expected bank, at the expected bank address, with the KV read data
    property sk_ram_msg_wr;
        fv_kv_mlkem_msg_we && !pi_kv_rd_resp[2].error && (abr_ctrl.abr_prog_cntr != ABR_ZEROIZE)
    |->
        abr_ctrl.sk_ram_we_bank[fv_sk_ram_msg_exp_bank] && !abr_ctrl.sk_ram_we_bank[!fv_sk_ram_msg_exp_bank] &&
        (abr_ctrl.sk_ram_waddr_bank[fv_sk_ram_msg_exp_bank] == fv_sk_ram_msg_exp_waddr[SK_MEM_BANK_ADDR_W:1]) &&
        (abr_ctrl.sk_ram_wdata[fv_sk_ram_msg_exp_bank] == pi_kv_rd_resp[2].read_data)
    endproperty

    assert_sk_ram_msg_wr: assert property (disable iff (!pi_rst_b | po_zeroize) sk_ram_msg_wr);

    //Modeling whether a KV mlkem_msg read request completed successfully (no rule failure, per-beat KV error abort or length mismatch)
    //Cleared on a new valid read request so a later aborted transfer can't reuse a previous successful one.
    logic fv_mlkem_msg_wrote_to_sk_ram;

    always_ff @(posedge pi_clk or negedge pi_rst_b) begin: fv_mlkem_msg_wrote_to_sk_ram_ff
        if (!pi_rst_b || po_zeroize) begin
            fv_mlkem_msg_wrote_to_sk_ram  <= '0;
        end else if (fv_kv_mlkem_msg_read_rules_allow && fv_kv_mlkem_msg_read_start && (fv_kv_mlkem_msg_cs == fv_st_idle_type)) begin
            fv_mlkem_msg_wrote_to_sk_ram  <= '0;
        end else if (fv_kv_mlkem_msg_done && !fv_kv_mlkem_msg_error && !fv_kv_mlkem_msg_error_flag) begin
            fv_mlkem_msg_wrote_to_sk_ram  <= '1;
        end
    end

    //The msg consumer is "Decompress(msg) -> MU" (AdamsBridge_MLKEM.md, Encaps data flow step 7).
    //Identified by opcode + destination rather than a fixed abr_prog_cntr index, since the ROM layout shifts between
    //RTL versions (DECOMPRESS is also used in encaps for ek, hence the operand3 qualifier).
    logic fv_mlkem_msg_decompress_instr;
    assign fv_mlkem_msg_decompress_instr = (abr_ctrl.abr_instr.opcode == ABR_UOP_DECOMPRESS) && (abr_ctrl.abr_instr.operand3 == MLKEM_MU_BASE);

    //Decompress(msg) must start reading at msg dword 0, i.e. the bank address of the msg region base.
    //Together with assert_sk_ram_msg_wr this proves the consumer sees the KV msg in spec order.
    property sk_ram_addr;
        fv_mlkem_msg_decompress_instr
    |->
        po_aux_src0_base_addr_o == ABR_MEM_ADDR_WIDTH'(MLKEM_DEST_MSG_MEM_OFFSET >> 1)
    endproperty

    assert_sk_ram_addr: assert property (disable iff (!pi_rst_b | po_zeroize) sk_ram_addr);


    ///////////////////////////////////////////////////////////////////////Requirement 2: Choose the specific slot meant for KV if it's a read///////////////////////////////////////////////////////////////////////

    assert_kv_mlkem_msg_rd_entry: assert property (disable iff (!pi_rst_b | po_zeroize) kv_rd_entry(pi_abr_reg_hwif_out_i.kv_mlkem_msg_rd_ctrl.read_en.value, pi_abr_reg_hwif_out_i.kv_mlkem_msg_rd_ctrl.read_entry.value,
                                                                                                        po_kv_read[2].read_entry));



    ///////////////////////////////////////////////////////////////////////Requirement 6: Reset/Zeroize erase the entire data to/from KV////////////////////////////////////////////////////////////////////////////


    //MLKEM msg KV client write_en should be cleared on zeroize or reset
    assert_kv_erase_mlkem_msg_write_enable: assert property (kv_erase_write_enable(abr_ctrl.kv_mlkem_msg_write_en));


    //kv_read[].read_offset should be cleared on zeroize or reset
    assert_kv_erase_mlkem_msg_read_offset: assert property (kv_erase_read_offset(po_kv_read[2].read_offset));


    ///////////////////////////////////////////////////////////////////////Requirement 7: No operation in the crypto engine without full read or write/////////////////////////////////////////////////////////

    assert_no_crypto_engine_op_without_full_mlkem_msg_read: assert property (no_crypto_engine_op_without_full_read(fv_kv_mlkem_msg_req, fv_kv_mlkem_msg_done_flag));

    //KV read error on mlkem msg blocks MLKEM commands until zeroize
    assert_no_mlkem_cmd_after_kv_mlkem_msg_error: assert property (disable iff (!pi_rst_b | po_zeroize) no_cmd_after_kv_error(fv_kv_mlkem_msg_error_flag, fv_mlkem_busy));


     ////////////////////////////////////////////////////////////////////////////Primary Outputs assertions/////////////////////////////////////////////////////////////////////////////////////////////////////

    //Assertions for swwe for each rd_ctrl_reg field of kv_mlkem_msg
    assert_kv_mlkem_msg_rd_ctrl_read_en_swwe: assert property (disable iff (!pi_rst_b | po_zeroize) kv_rd_ctrl_swwe(po_abr_reg_hwif_in_o.kv_mlkem_msg_rd_ctrl.read_en.swwe, fv_mlkem_msg_swwe));
    assert_kv_mlkem_msg_rd_ctrl_read_entry_swwe: assert property (disable iff (!pi_rst_b | po_zeroize) kv_rd_ctrl_swwe(po_abr_reg_hwif_in_o.kv_mlkem_msg_rd_ctrl.read_entry.swwe, fv_mlkem_msg_swwe));
    assert_kv_mlkem_msg_rd_ctrl_rsvd_swwe: assert property (disable iff (!pi_rst_b | po_zeroize) kv_rd_ctrl_swwe(po_abr_reg_hwif_in_o.kv_mlkem_msg_rd_ctrl.rsvd.swwe, 0));
    assert_kv_mlkem_msg_rd_ctrl_pcr_hash_extend_swwe: assert property (disable iff (!pi_rst_b | po_zeroize) kv_rd_ctrl_swwe(po_abr_reg_hwif_in_o.kv_mlkem_msg_rd_ctrl.pcr_hash_extend.swwe, 0));


    //Assertion for hwclr for kv_mlkem_msg_rd_ctrl.read_en
    assert_kv_mlkem_msg_rd_ctrl_read_en_hwclr: assert property (disable iff (!pi_rst_b | po_zeroize) kv_rd_ctrl_read_en_hwclr(po_abr_reg_hwif_in_o.kv_mlkem_msg_rd_ctrl.read_en.hwclr, abr_ctrl.kv_mlkem_msg_ready));

    //Assertion for kv_mlkem_msg_rd_status.READY
    assert_kv_mlkem_msg_rd_status_ready: assert property (disable iff (!pi_rst_b | po_zeroize) kv_rd_status_ready(po_abr_reg_hwif_in_o.kv_mlkem_msg_rd_status.READY.next, abr_ctrl.kv_mlkem_msg_ready));

    //Assertion for kv_mlkem_msg_rd_status.VALID.hwclr
    assert_kv_mlkem_msg_rd_status_valid_hwclr: assert property (disable iff (!pi_rst_b | po_zeroize) kv_rd_status_valid_hwclr(po_abr_reg_hwif_in_o.kv_mlkem_msg_rd_status.VALID.hwclr, pi_abr_reg_hwif_out_i.kv_mlkem_msg_rd_ctrl.read_en.value));

    //Assertion for kv_mlkem_msg_rd_status.VALID.hwset
    assert_kv_mlkem_msg_rd_status_valid_hwset: assert property (disable iff (!pi_rst_b | po_zeroize) kv_rd_status_valid_hwset(po_abr_reg_hwif_in_o.kv_mlkem_msg_rd_status.VALID.hwset, abr_ctrl.kv_mlkem_msg_done));

    //Assertion for kv_mlkem_msg_rd_status.ERROR
    assert_kv_mlkem_msg_rd_status_error: assert property (disable iff (!pi_rst_b | po_zeroize) kv_rd_status_error(po_abr_reg_hwif_in_o.kv_mlkem_msg_rd_status.ERROR.next, abr_ctrl.kv_mlkem_msg_error));

endmodule
