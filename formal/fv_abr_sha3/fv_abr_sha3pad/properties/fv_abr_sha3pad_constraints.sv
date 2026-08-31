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


module fv_abr_sha3pad_constraints
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
    
    // Mode can only be shake
    assume_mode_i: assume property (disable iff(!pi_rst_b)
        pi_mode_i == 2'b10
    );

    // Strength can be L128 or L256
    assume_strength_i: assume property (disable iff(!pi_rst_b)
        pi_strength_i inside {L128, L256}
    );

    ////////////////////////////////////////
    // Count the number of incoming messages
    ///////////////////

    // Set the limit of the expected number of packets
    logic [4:0] fv_packet_num_limit;
    assign fv_packet_num_limit = (pi_strength_i == L128 ? 21 : 17);

    // Holds the current number if received packets
    logic [4:0] fv_incoming_msg_cntr_val;

    // The packets counter increment signal
    logic fv_incoming_msg_cntr_incr;
    assign fv_incoming_msg_cntr_incr = pi_msg_valid_i && (fv_incoming_msg_cntr_val < fv_packet_num_limit) && po_msg_ready_o;

    logic fv_incoming_msg_cntr_rst;
    assign fv_incoming_msg_cntr_rst = (pi_zeroize || (fv_incoming_msg_cntr_val == fv_packet_num_limit) || pi_process_i);

    lubis_incr_counter_m #(
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

    // If no messages were received, process_i cannot be set to true
    assume_process_i: assume property(disable iff(!pi_rst_b)
        fv_incoming_msg_cntr_val == 0
    |->
        !pi_process_i
    );

    // process_i is a pulse signal
    assume_process_i_pulse: assume property(disable iff(!pi_rst_b)
        pi_process_i
    |->
        ##1 !pi_process_i
    );

    // If a partial message is received, no new messages can be received before getting a new start
    assume_no_msgs_after_partial: assume property(disable iff(!pi_rst_b)
        pi_msg_valid_i &&
        pi_msg_strb_i != '1
    |->
        ##1 !pi_msg_valid_i until_with pi_start_i
    );

    // There can't be valid messages at the same cycle as the start
    assume_no_msg_at_start: assume property(disable iff(!pi_rst_b)
        pi_start_i
    |->
        !pi_msg_valid_i
    );

    // Once a start comes in, it cannot come in again until the blocks were absorbed
    assume_no_several_starts: assume property(disable iff(!pi_rst_b)
        pi_start_i
    |->
        ##1 (!pi_start_i) until (po_absorbed_o == abr_prim_mubi_pkg::MuBi4True)
    );

    // If start_i is high, then eventually process_i comes in
    assume_process_fairness: assume property(disable iff(!pi_rst_b)
        pi_start_i
    |->
        s_eventually(pi_process_i)
    );

    // After process_i, no valid messages can come in until after the next start
    assume_msg_valid_after_process_i: assume property(disable iff(!pi_rst_b)
        pi_process_i
    |->
        !pi_msg_valid_i until_with pi_start_i
    );

    // If keccak_run_o is high, then keccak_complete_i is set after 12 cycles
    // 11 cycles is the amount of cycles required by the keccak_round to finish at which it is busy during
    assume_complete_after_run: assume property(disable iff(!pi_rst_b)
        po_keccak_run_o
    |->
        !pi_keccak_complete_i [*11]
        ##12 pi_keccak_complete_i
        ##1 !pi_keccak_complete_i
    );

    // Strength should be stable as long as there is still packets pending
    assume_stable_strength_i: assume property (disable iff(!pi_rst_b)
        ##1 !pi_start_i
    |->
        $stable(pi_strength_i)
    );

    logic fv_keccak_run_o_ff;
    always_ff @(posedge pi_clk_i or negedge pi_rst_b) begin
        if (!pi_rst_b || pi_zeroize) begin
            fv_keccak_run_o_ff <= 1'b0;
        end else begin
            if(po_keccak_run_o) begin
                fv_keccak_run_o_ff <= 1'b1;
            end else if(pi_keccak_complete_i) begin
                fv_keccak_run_o_ff <= 1'b0;
            end
        end
    end

    // If keccak_run_o was not high, keccak_complete_i cannot be high
    assume_no_complete_without_run: assume property(disable iff(!pi_rst_b)
        !fv_keccak_run_o_ff
    |->
        !pi_keccak_complete_i
    );

    // Ready is low as long as there was a run without a complete
    assume_keccak_ready: assume property(disable iff(!pi_rst_b)
        fv_keccak_run_o_ff
    |->
        !pi_keccak_ready_i
    );

    // Ready is always eventually ready 
    assume_keccak_ready_fairness: assume property(disable iff(!pi_rst_b)
        s_eventually(pi_keccak_ready_i)
    );

    // Message strobe cannot have bubbles
    assume_no_bubbles: assume property(disable iff(!pi_rst_b)
        pi_msg_strb_i inside {8'b00000000, 8'b00000001, 8'b00000011, 8'b00000111, 8'b00001111,
                              8'b00011111, 8'b00111111, 8'b01111111, 8'b11111111}
    );
endmodule

