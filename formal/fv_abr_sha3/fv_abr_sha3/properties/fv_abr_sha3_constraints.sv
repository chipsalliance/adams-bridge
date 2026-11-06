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


module fv_abr_sha3_constraints
    import abr_sha3_pkg::*;
    import abr_prim_mubi_pkg::*;
#(
    parameter ROUNDS_PER_CLOCK = 1,
    parameter EN_MASKING       = 0,
    //#$localparams
    localparam SHARE = (EN_MASKING)?2:1
    //$#//
) (
    //#$ports
    input logic                        pi_clk_i,
    input logic                        pi_rst_b,
    input logic                        pi_zeroize,
    input logic                        pi_msg_start_i,
    input logic                        pi_msg_valid_i,
    input logic [MsgWidth-1:0]         pi_msg_data_i[SHARE],
    input logic [MsgStrbW-1:0]         pi_msg_strb_i,
    input logic                        po_msg_ready_o,
    input logic                        pi_rand_valid_i,
    input logic                        pi_rand_early_i,
    input logic [StateW/2-1:0]         pi_rand_data_i,
    input logic                        pi_rand_aux_i,
    input logic                        po_rand_consumed_o,
    input sha3_mode_e                  pi_mode_i,
    input keccak_strength_e            pi_strength_i,
    input logic                        pi_start_i,
    input logic                        pi_masked_i,
    input logic                        pi_process_i,
    input logic                        pi_run_i,
    input abr_prim_mubi_pkg::mubi4_t   po_absorbed_o,
    input logic                        po_squeezing_o,
    input logic                        po_block_processed_o,
    input sha3_st_e                    po_sha3_fsm_o,
    input logic                        po_state_valid_o,
    input logic                        pi_state_valid_hold_i,
    input logic [StateW-1:0]           po_state_o[SHARE],
    input err_t                        po_error_o,
    input logic                        po_sparse_fsm_error_o,
    input logic                        po_count_error_o,
    input logic                        po_keccak_storage_rst_error_o
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

    // Masked datapath only exists when EN_MASKING=1; masked_i must stay low otherwise
    if (!EN_MASKING) begin : gen_no_masking_hw
        assume_masked_requires_masking_hw: assume property(!pi_masked_i);
    end

    // Randomness (LFSR) is eventually available, so the masked keccak FSM can leave Phase1
    assume_rand_progress: assume property(
        s_eventually (pi_rand_early_i || pi_rand_valid_i)
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
    property assume_process_i_p;
        disable iff(!pi_rst_b)
        fv_incoming_msg_cntr_val == 0
    |->
        !pi_process_i
    endproperty
    assume_process_i: assume property (assume_process_i_p);

    //process_i cannot be set to true unless the state is StAbsorb
    property assume_process_i_low_p;
        disable iff(!pi_rst_b)
        po_sha3_fsm_o != StAbsorb
    |->
        !pi_process_i
    endproperty
    assume_process_i_low: assume property (assume_process_i_low_p);

    // process_i is a pulse signal
    property assume_process_i_pulse_p;
        disable iff(!pi_rst_b)
        pi_process_i
    |->
        ##1 !pi_process_i
    endproperty
    assume_process_i_pulse: assume property (assume_process_i_pulse_p);

    // After an accepted partial message, no new messages can be received before a new start
    property assume_no_msgs_after_partial_p;
        disable iff(!pi_rst_b)
        pi_msg_valid_i &&
        po_msg_ready_o &&
        pi_msg_strb_i != '1
    |->
        ##1 !pi_msg_valid_i until_with pi_start_i
    endproperty
    assume_no_msgs_after_partial: assume property (assume_no_msgs_after_partial_p);

    // There can't be valid messages at the same cycle as the start
    property assume_no_msg_at_start_p;
        disable iff(!pi_rst_b)
        pi_msg_start_i
    |->
        !pi_msg_valid_i
    endproperty
    assume_no_msg_at_start: assume property (assume_no_msg_at_start_p);

    // Once a start comes in, it cannot come in again until the blocks were absorbed
    property assume_no_several_starts_p;
        disable iff(!pi_rst_b)
        pi_msg_start_i
    |->
        ##1 (!pi_msg_start_i) until (po_absorbed_o == abr_prim_mubi_pkg::MuBi4True)
    endproperty
    assume_no_several_starts: assume property (assume_no_several_starts_p);

    // If start_i is high, then eventually process_i comes in
    property assume_process_fairness_p;
        disable iff(!pi_rst_b)
        pi_msg_start_i
    |->
        s_eventually(pi_process_i)
    endproperty
    assume_process_fairness: assume property (assume_process_fairness_p);

    // After process_i, no valid messages can come in until after the next start
    property assume_msg_valid_after_process_i_p;
        disable iff(!pi_rst_b)
        pi_process_i
    |->
        !pi_msg_valid_i until_with pi_msg_start_i
    endproperty
    assume_msg_valid_after_process_i: assume property (assume_msg_valid_after_process_i_p);

    // Strength should be stable as long as there is still packets pending
    property assume_stable_strength_i_p;
        disable iff(!pi_rst_b)
        ##1 !pi_msg_start_i
    |->
        $stable(pi_strength_i)
    endproperty
    assume_stable_strength_i: assume property (assume_stable_strength_i_p);

    // start_i is a pulse
    property assume_start_i_pulse_p;
        disable iff(!pi_rst_b)
        pi_start_i
    |->
        ##1 !pi_start_i
    endproperty
    assume_start_i_pulse: assume property (assume_start_i_pulse_p);

    // msg_start_i is a pulse
    property assume_msg_start_i_pulse_p;
        disable iff(!pi_rst_b)
        pi_msg_start_i
    |->
        ##1 !pi_msg_start_i
    endproperty
    assume_msg_start_i_pulse: assume property (assume_msg_start_i_pulse_p);

    // msg_start_i is set immediately after start_i
    property assume_msg_start_i_after_start_i_p;
        disable iff(!pi_rst_b)
        pi_start_i
    |->
        ##1 pi_msg_start_i
    endproperty
    assume_msg_start_i_after_start_i: assume property (assume_msg_start_i_after_start_i_p);

    // Message strobe cannot have bubbles
    assume_no_bubbles: assume property(disable iff(!pi_rst_b)
        pi_msg_strb_i inside {8'b00000000, 8'b00000001, 8'b00000011, 8'b00000111, 8'b00001111,
                              8'b00011111, 8'b00111111, 8'b01111111, 8'b11111111}
    );

    // logic fv_run_i_ff;
    // always_ff @(posedge pi_clk_i or negedge pi_rst_b) begin
    //     if (!pi_rst_b || pi_zeroize) begin
    //         fv_run_i_ff <= 1'b0;
    //     end else if(pi_run_i) begin
    //             fv_run_i_ff <= 1'b1;
    //     end
    // end

    // If state_valid_o and state_valid_hold_i are high, then run_i cannot go high
    property assume_run_i_during_hold_p;
        disable iff(!pi_rst_b)
        po_state_valid_o &&
        pi_state_valid_hold_i
    |->
        !pi_run_i
    endproperty
    assume_run_i_during_hold: assume property (assume_run_i_during_hold_p);

endmodule

bind abr_sha3 fv_abr_sha3_constraints #(.EN_MASKING(EnMasking)) fv_abr_sha3_constraints_i (
    .pi_clk_i(clk_i),
    .pi_rst_b(rst_b),
    .pi_zeroize(zeroize),
    .pi_msg_start_i(msg_start_i),
    .pi_msg_valid_i(msg_valid_i),
    .pi_msg_data_i(msg_data_i),
    .pi_msg_strb_i(msg_strb_i),
    .po_msg_ready_o(msg_ready_o),
    .pi_rand_valid_i(rand_valid_i),
    .pi_rand_early_i(rand_early_i),
    .pi_rand_data_i(rand_data_i),
    .pi_rand_aux_i(rand_aux_i),
    .po_rand_consumed_o(rand_consumed_o),
   // .pi_ns_data_i(ns_data_i),
    .pi_mode_i(mode_i),
    .pi_strength_i(strength_i),
    .pi_start_i(start_i),
    .pi_masked_i(masked_i),
    .pi_process_i(process_i),
    .pi_run_i(run_i),
    .po_absorbed_o(absorbed_o),
    .po_squeezing_o(squeezing_o),
    .po_block_processed_o(block_processed_o),
    .po_sha3_fsm_o(sha3_fsm_o),
    .po_state_valid_o(state_valid_o),
    .pi_state_valid_hold_i(state_valid_hold_i),
    .po_state_o(state_o),
    .po_error_o(error_o),
    .po_sparse_fsm_error_o(sparse_fsm_error_o),
    .po_count_error_o(count_error_o),
    .po_keccak_storage_rst_error_o(keccak_storage_rst_error_o)
);
