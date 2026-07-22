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


module fv_abr_sha3pad
    import abr_sha3_pkg::*;
    import abr_prim_mubi_pkg::*;
#(
    parameter Width             = 1600,
    parameter EnMasking         = 0,
    //#$localparams
    localparam Share            = (EnMasking) ? 2 : 1,
    localparam StateWidthPad    = 7
    //$#//
) (
    //#$ports
    input                            pi_clk_i,
    input                            pi_rst_b,
    input logic                      pi_zeroize,
    input                            pi_msg_valid_i,
    input [MsgWidth-1:0]             pi_msg_data_i[Share],
    input [MsgStrbW-1:0]             pi_msg_strb_i,
    input logic                      po_msg_ready_o,
    input [NSRegisterSize*8-1:0]     pi_ns_data_i,
    input logic [Width-1:0]          po_keccak_data_o[Share],
    input logic                      pi_keccak_ready_i,
    input logic                      po_keccak_run_o,
    input                            pi_keccak_complete_i,
    input sha3_mode_e                pi_mode_i,
    input keccak_strength_e          pi_strength_i,
    input                            pi_start_i,
    input                            pi_process_i,
    input abr_prim_mubi_pkg::mubi4_t po_absorbed_o,
    input logic                      po_sparse_fsm_error_o,
    input logic                      po_msg_count_error_o
    //$#//
);

    default clocking default_clk @(posedge pi_clk_i); endclocking

    fv_abr_sha3pad_constraints #(
        .Width(Width),
        .EnMasking(EnMasking)
    ) fv_abr_sha3pad_constraints_i (.*);

    // Run command
    logic fv_keccak_run;

    // There is a run command that is pending because the keccak module is busy
    logic fv_keccak_run_pend;
    logic fv_keccak_run_pend_ff;

    // Run command to the keccak round that can be gated due to the pending signal
    logic fv_keccak_run_o;

    // Keccak round is ongoing
    logic fv_keccak_run_in_prog;
    logic fv_keccak_run_in_prog_ff;

    // Captures the start_i signal
    logic fv_start_i;
    logic fv_start_i_ff;

    // Captures process_i signal
    logic fv_process_i;
    logic fv_process_i_ff;

    // Set the limit of the expected number of packets
    logic [4:0] fv_packet_num_limit;
    assign fv_packet_num_limit = (pi_strength_i == L128 ? 21 : 17);

    // Holds the current number if received packets
    logic [4:0] fv_incoming_msg_cntr_val;

    logic fv_incoming_msg_cntr_incr;
    assign fv_incoming_msg_cntr_incr = pi_msg_valid_i && (fv_incoming_msg_cntr_val < fv_packet_num_limit) && fv_start_i && !fv_keccak_run_o && !fv_keccak_run_pend && !fv_process_i;

    logic fv_incoming_msg_cntr_rst;
    assign fv_incoming_msg_cntr_rst = (pi_zeroize || fv_keccak_run_o);

    fv_abr_sha3pad_incr_counter_m #(
        .COUNTER_WIDTH  (5                          )
    ) fv_incoming_msg_cntr (
        .clk             (pi_clk_i                   ),
        .rst             (!pi_rst_b                  ),
        .soft_rst        (fv_incoming_msg_cntr_rst   ),
        .incr_en         (fv_incoming_msg_cntr_incr  ), 
        .incr_val        (5'h1                       ), 
        .count_next      (        /* open */         ),
        .count           (fv_incoming_msg_cntr_val   )
    );

    // Holds the current number of received packets
    logic [10:0] fv_incoming_bits_cntr_val;

    // Increment value of the bits counter
    logic [10:0] fv_incoming_bits_cntr_incr_val;
    assign fv_incoming_bits_cntr_incr_val = ($countones(pi_msg_strb_i)) * 8;

    logic fv_incoming_bits_cntr_incr;
    assign fv_incoming_bits_cntr_incr = fv_incoming_msg_cntr_incr;

    logic fv_incoming_bits_cntr_rst;
    assign fv_incoming_bits_cntr_rst = fv_incoming_msg_cntr_rst;

    fv_abr_sha3pad_incr_counter_m #(
        .COUNTER_WIDTH  (11                             )
    ) fv_incoming_bits_cntr (
        .clk             (pi_clk_i                       ),
        .rst             (!pi_rst_b                      ),
        .soft_rst        (fv_incoming_bits_cntr_rst      ),
        .incr_en         (fv_incoming_bits_cntr_incr     ), 
        .incr_val        (fv_incoming_bits_cntr_incr_val ), 
        .count_next      (        /* open */             ),
        .count           (fv_incoming_bits_cntr_val      )
    );

    // Calculates how many padding bits are needed
    logic [10:0] fv_padding_space;
    assign fv_padding_space = ((pi_strength_i == L128) ? (1344 - fv_incoming_bits_cntr_val) : (1088 - fv_incoming_bits_cntr_val));

    // Used to store the padding bits
    logic [Width-1:0] fv_padding_bits;

    // Holds the padded message to be sent to the keccak rounds
    logic [Width-1:0] fv_padded_msg;
    logic [Width-1:0] fv_padded_msg_ff;

    logic [Width-1:0] fv_expected_data;

    // Keccak rate based on the strength 
    logic [10:0] fv_rate;
    assign fv_rate = ((pi_strength_i == L128) ? 1344 : 1088);

    // True if an extra padding block is required
    logic fv_extra_block;
    logic fv_extra_block_ff;

    // Vector of bits that contains a data mask based on the write strobe
    logic [MsgWidth-1:0] fv_data_mask;
    
    // Capture when the last block of a message is sent
    logic fv_last_msg_sent;
    logic fv_last_msg_sent_ff;

    // Create data mask based on the strobe
    // Masks out the invalid bytes then shift the message
    for (genvar n = 0; n < MsgWidth/8; n++) begin
        assign fv_data_mask[(8*n)+7:(8*n)] = {8{pi_msg_strb_i[n]}};
    end

    // Flag to accept an extra partial message
    logic fv_accepted_partial;
    logic fv_accepted_partial_ff;
    logic [Width-1:0] fv_accepted_partial_msg;
    logic [Width-1:0] fv_accepted_partial_msg_ff;

    always_comb begin
        fv_padded_msg           = fv_padded_msg_ff;
        fv_start_i              = fv_start_i_ff;
        fv_extra_block          = fv_extra_block_ff;
        fv_keccak_run_pend      = fv_keccak_run_pend_ff;
        fv_keccak_run_in_prog   = fv_keccak_run_in_prog_ff;
        fv_process_i            = fv_process_i_ff;
        fv_last_msg_sent        = fv_last_msg_sent_ff;
        fv_accepted_partial     = fv_accepted_partial_ff;
        fv_accepted_partial_msg = fv_accepted_partial_msg_ff;
        fv_keccak_run           = 1'b0;
        fv_keccak_run_o         = 1'b0;

        // Once the padding gets a start, we set the C section to all zeros
        // The number of C bits is based on the strength
        if(pi_start_i) begin
            if(pi_strength_i == L128) begin
                fv_padded_msg[1599:1344] = '0;
            end else if(pi_strength_i == L256) begin
                fv_padded_msg[1599:1088] = '0;
            end
        end

        // Capture the process signal
        if(pi_process_i) begin
            fv_process_i = 1'b1;
        end

        // If there is no pending run and the last message was not sent yet, then continue padding
        if(!fv_keccak_run_pend && !fv_last_msg_sent) begin
            // If fv_extra_block is true, it means that we need an additional padding block
            if(!fv_extra_block) begin
                // Insert every received message into the padded message
                if(fv_incoming_msg_cntr_incr) begin
                   fv_padded_msg = fv_padded_msg | ((pi_msg_data_i[0] & fv_data_mask) << (fv_incoming_msg_cntr_val*64));
                end
                
                // If process_i is received, then padding should be done
                // Other wise, run keccak if all packets are received
                if(pi_process_i || fv_process_i) begin
                    // If there is space for padding, then add the padding bits
                    // Otherwise, an extra block of padding is required
                    if(fv_accepted_partial) begin
                        fv_padded_msg = fv_accepted_partial_msg;
                        fv_accepted_partial = 1'b0;
                        fv_accepted_partial_msg = '0;
                    end else if(fv_padding_space != 0) begin
                        // 5'b11111 is the domain operator and the LSB 1 of the 10*1 padding
                        fv_padding_bits = ((1'b1 << (fv_rate - 1)) | (5'b11111 << fv_incoming_bits_cntr_val));
                        fv_padded_msg = fv_padded_msg | fv_padding_bits;
                    end else begin
                        fv_extra_block = 1'b1;
                    end
                    fv_keccak_run = 1'b1;
                    fv_last_msg_sent = !fv_extra_block;
                end else begin
                    fv_keccak_run = (fv_incoming_msg_cntr_val == fv_packet_num_limit);
                end
            end else begin
                // The contents of the extra padding block
                if(pi_strength_i == L128) begin
                    fv_padded_msg[1343]     = 1'b1;
                    fv_padded_msg[1342:5]   = '0;
                end else if(pi_strength_i == L256) begin
                  fv_padded_msg[1087]     = 1'b1;
                  fv_padded_msg[1086:5]   = '0;
                end
                fv_padded_msg[4]        = 1'b1;
                fv_padded_msg[3:0]      = 4'b1111;
                fv_keccak_run           = 1'b1;
                fv_extra_block          = 1'b0;
                fv_last_msg_sent        = 1'b1;
            end
        end

        // If there is a keccak_run command to be sent, check if the keccak rounds block is ready
        // If not ready, set the pending bit to 1 and wait
        // Otherwise, send out the command
        if(fv_keccak_run && (!pi_keccak_ready_i || fv_keccak_run_in_prog)) begin
            fv_keccak_run_o = 1'b0;
            fv_keccak_run_pend = 1'b1;
        end else if((fv_keccak_run_pend || fv_keccak_run) && pi_keccak_ready_i && !fv_keccak_run_in_prog) begin
            fv_keccak_run_o = 1'b1;
            fv_keccak_run_pend = 1'b0;
        end

        // If the keccak run command is sent out, then set the in_progress bit to 1
        // Otherwise, wait for a keccak_complete_i to reset the bit to zero
        if(fv_keccak_run_o) begin
            fv_keccak_run_in_prog   = 1'b1;
        end else if(pi_keccak_complete_i) begin
            fv_keccak_run_in_prog   = 1'b0;
        end

        // If there is a pending keccak run, without padding space (17 or 21 full packets), accept partial messages that can come in
        if ((fv_keccak_run_pend || fv_keccak_run_o) && fv_padding_space == 0) begin
            if(pi_msg_valid_i && pi_msg_strb_i != '1) begin
                fv_accepted_partial = 1'b1;
                fv_accepted_partial_msg =  ((1'b1 << (fv_rate - 1)) | (5'b11111 << ($countones(pi_msg_strb_i)) * 8)) | (pi_msg_data_i[0] & fv_data_mask);
            end
        end

        // Capture the start signal and set it to true upon start
        // Otherwise, if process_i is received, keccak rounds are all done and the last message is sent,
        // reset the flags
        if(pi_start_i) begin
            fv_start_i = 1'b1;
        end else if(fv_process_i && !fv_keccak_run_in_prog && !fv_keccak_run_pend && fv_last_msg_sent) begin // The last block is sent out and now the process is done
            fv_start_i = 1'b0;
            fv_process_i = 1'b0;
            fv_last_msg_sent = 1'b0;
        end
    end
    
    always_ff @(posedge pi_clk_i or negedge pi_rst_b) begin
        if (!pi_rst_b || pi_zeroize) begin
            fv_padded_msg_ff            <= '0;
            fv_start_i_ff               <= '0;
            fv_extra_block_ff           <= '0;
            fv_process_i_ff             <= '0;
            fv_keccak_run_pend_ff       <= '0;
            fv_keccak_run_in_prog_ff    <= '0;
            fv_last_msg_sent_ff         <= '0;
            fv_accepted_partial_ff      <= '0;
            fv_accepted_partial_msg_ff  <= '0;
        end else begin
            fv_start_i_ff               <= fv_start_i;
            fv_extra_block_ff           <= fv_extra_block;
            fv_keccak_run_pend_ff       <= fv_keccak_run_pend;
            fv_last_msg_sent_ff         <= fv_last_msg_sent;
            fv_keccak_run_in_prog_ff    <= fv_keccak_run_in_prog;
            fv_process_i_ff             <= fv_process_i;
            fv_accepted_partial_ff      <= fv_accepted_partial;
            fv_accepted_partial_msg_ff  <= fv_accepted_partial_msg;

            // If keccak_run command is sent out, reset the padded message register
            if(fv_keccak_run_o) begin
                fv_padded_msg_ff        <= '0;
            end else begin
                fv_padded_msg_ff        <= fv_padded_msg;
            end   
        end
    end

    ////////////////////////////////////
    // Requirement 1: abr_sha3pad sends
    // out correctly padded messages in
    // the correct order
    /////////////////

    fv_abr_sha3pad_scoreboard
    #(
        .DATA_WIDTH            ($bits(fv_padded_msg)   ),
        .DEPTH                 (1                      ),
        .BYPASS                (1'b1                   )
    ) fv_keccak_data_sb
    (
        .clk                   (pi_clk_i               ),
        .rst                   (!pi_rst_b || pi_zeroize),
        .soft_rst              (1'b0                   ),
        .full                  (1'b0                   ),
        .empty                 (1'b0                   ),
        .data_in               (fv_padded_msg          ),
        .data_out              (po_keccak_data_o[0]    ),
        .push                  (fv_keccak_run_o        ),
        .pop                   (po_keccak_run_o        ),
        .expected_data         (fv_expected_data       ),
        .incr_val              (1'b1                   ),
        // Outputs
        .sampled_out           ( /* open */            ),
        .sampled_in            ( /* open */            ),
        .sampled_in_reg        ( /* open */            ),
        .sampled_out_reg       ( /* open */            ),
        .chosen_symbolic_data  (fv_expected_data       ),
        .tracking_counter_out  ( /* open */            )
    );

    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    // Requirement 2: msg_ready_o value
    // Cases at which ready is high, otherwise low
    // 1. When a partial message is received if process_i was not already received
    // 2. When the system was started, process_i was not received and the block didn't receive all packets (17/21) based on the mode
    // The value of the ready is relevant only if the valid is high, which is the reason behind pi_msg_valid_i in the assumption part
    /////////////////

    logic fv_msg_partial;
    assign fv_msg_partial = (pi_msg_valid_i && pi_msg_strb_i != '1);

    logic fv_case1_high;
    assign fv_case1_high = fv_msg_partial && fv_start_i && !fv_process_i ;

    logic fv_case2_high;
    assign fv_case2_high = ((fv_incoming_msg_cntr_val < fv_packet_num_limit) && fv_start_i && !pi_start_i && !fv_process_i);

    assert_msg_ready_o_high: assert property(disable iff(!pi_rst_b || pi_zeroize)
        pi_msg_valid_i
    |->
        po_msg_ready_o == (fv_case1_high || fv_case2_high)
    );

    /////////////////////////////////////
    // Requirement 3: Absorbed signal
    // should be set when keccak rounds
    // are done
    /////////////////

    assert_absorbed_o_high: assert property(disable iff(!pi_rst_b || pi_zeroize)
        pi_start_i
    |->
        s_eventually(po_absorbed_o == abr_prim_mubi_pkg::MuBi4True)
    );

    assert_absorbed_o_low: assert property(disable iff(!pi_rst_b || pi_zeroize)
        pi_start_i ||
        fv_start_i
    |->
        po_absorbed_o == abr_prim_mubi_pkg::MuBi4False
    );

    assert_absorbed_o_pulse: assert property(disable iff(!pi_rst_b || pi_zeroize)
        po_absorbed_o == abr_prim_mubi_pkg::MuBi4True
    |->
        ##1 po_absorbed_o == abr_prim_mubi_pkg::MuBi4False
    );

    assert_absorbed_o_reset: assert property(
        !pi_rst_b || pi_zeroize
    |->
        ##1 po_absorbed_o == abr_prim_mubi_pkg::MuBi4False
    );

    /////////////////////////////////////
    // Requirement 4: sparse_fsm_error_o
    // never happens 
    /////////////////

    assert_sparse_fsm_error_o: assert property(
        po_sparse_fsm_error_o == 1'b0
    );

    /////////////////////////////////////
    // Requirement 5: msg_count_error_o
    // never happens 
    /////////////////
    
    assert_msg_count_error_o: assert property(
        po_msg_count_error_o == 1'b0
    );

endmodule


bind abr_sha3pad fv_abr_sha3pad fv_abr_sha3pad_i(
    .*,
    //#$bind
    .pi_clk_i (clk_i),
    .pi_rst_b (rst_b),
    .pi_zeroize (zeroize),
    .pi_msg_valid_i (msg_valid_i),
    .pi_msg_data_i (msg_data_i),
    .pi_msg_strb_i (msg_strb_i),
    .po_msg_ready_o (msg_ready_o),
    .pi_ns_data_i (ns_data_i),
    .po_keccak_data_o (keccak_data_o),
    .pi_keccak_ready_i (keccak_ready_i),
    .po_keccak_run_o (keccak_run_o),
    .pi_keccak_complete_i (keccak_complete_i),
    .pi_mode_i (mode_i),
    .pi_strength_i (strength_i),
    .pi_start_i (start_i),
    .pi_process_i (process_i),
    .po_absorbed_o (absorbed_o),
    .po_sparse_fsm_error_o (sparse_fsm_error_o),
    .po_msg_count_error_o (msg_count_error_o)
    //$#//
);