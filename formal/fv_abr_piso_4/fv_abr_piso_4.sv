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


module fv_abr_piso_4
#(
    parameter PISO_BUFFER_W        = 1344,
    parameter PISO_PTR_W           = $clog2(PISO_BUFFER_W),
    parameter PISO_INPUT_RATE0     = 1088,
    parameter PISO_INPUT_RATE1     = 1088,
    parameter PISO_INPUT_RATE2     = 1088,
    parameter PISO_INPUT_RATE3     = 1088,
    parameter PISO_OUTPUT_RATE0    = 80,
    parameter PISO_OUTPUT_RATE1    = 80,
    parameter PISO_OUTPUT_RATE2    = 80,
    parameter PISO_OUTPUT_RATE3    = 80,
    parameter PISO_ACT_INPUT_RATE  = 1088,
    parameter PISO_ACT_OUTPUT_RATE = 80,
    parameter BUFFER_W_DELTA       = PISO_BUFFER_W-PISO_ACT_INPUT_RATE,
    // This parameter should be set to the division of the highest input rate
    // and lowest output rate. The default is set based on the rates provided in
    // mlsda_sampler_pkg.sv
    parameter SCOREBOARD_DEPTH     = PISO_INPUT_RATE0/PISO_OUTPUT_RATE3
    //#$localparams
    //$#//
) (
    //#$ports
    input logic                            pi_clk,
    input logic                            pi_rst_b,
    input logic                            pi_zeroize,
    input logic [1:0]                      pi_mode,
    input logic                            pi_valid_i,
    input logic                            po_hold_o,
    input logic [PISO_ACT_INPUT_RATE-1:0]  pi_data_i,
    input logic                            po_valid_o,
    input logic                            pi_hold_i,
    input logic [PISO_ACT_OUTPUT_RATE-1:0] po_data_o,

    input logic [PISO_PTR_W-1:0]           input_rate,
    input logic [PISO_PTR_W-1:0]           output_rate
    //$#//
);

    default clocking default_clock @(posedge pi_clk); endclocking

    logic                            sampled_in;
    logic                            sampled_in_reg;
    logic                            has_leftover_bits_reg;
    logic [PISO_PTR_W-1:0]           num_of_beats_reg;
    logic [PISO_PTR_W-1:0]           num_of_beats_nxt;
    // This symbolic is used to pick which valid_o to track out of all the valid_o's
    // that will be sent.
    logic [PISO_PTR_W-1:0]           sym_beat_select;
    logic [PISO_PTR_W-1:0]           abr_piso_4_sb_incr_val;
    logic [PISO_PTR_W-1:0]           num_leftover_bits_nxt;
    logic [PISO_PTR_W-1:0]           num_leftover_bits_reg;
    logic [PISO_PTR_W  :0]           num_bits_in_buffer;
    logic [PISO_BUFFER_W-1:0]        buffer_reg;
    logic [PISO_BUFFER_W-1:0]        buffer_nxt;
    logic [PISO_BUFFER_W-1:0]        data_i_masked_extended;
    logic [PISO_ACT_INPUT_RATE-1:0]  data_i_masked;
    logic [PISO_ACT_OUTPUT_RATE-1:0] abr_piso_4_sb_exp_data;

    // ------------------------------------------------------------------------------------------
    // SUPPORTING LOGIC
    // ------------------------------------------------------------------------------------------

    assume_sym_beat_select: assume property (disable iff(!pi_rst_b || pi_zeroize)
        pi_valid_i
    |->
        sym_beat_select < num_of_beats_nxt
    );

    assume_stable_sym_beat_select: assume property (disable iff(!pi_rst_b || pi_zeroize)
       sampled_in
    |->
        ##1
        $stable(sym_beat_select)
    );

    // Calculate the amount of leftover bits from the previous request, when data_i
    // cannot be fully sent based on the input rate and the output rate.
    assign num_leftover_bits_nxt  = (input_rate + num_leftover_bits_reg) % output_rate;
    // Calculate the total number of valids that will be sent out based on the input rate and the
    // output rate and the amount of leftover bits
    assign num_of_beats_nxt       = (input_rate + num_leftover_bits_reg) / output_rate;
    // Increment the tracking counter of the scoreboard depending on the sampled_in. When
    // we sample in the data to be tracked, increment the tracking counter of the scoreboard
    // by the number of valid_o that will be sent out before the valid_o that we are tracking
    // appears at the valid_o interface. Otherwise increment it by the total amount of valid_o
    // for that transaction including the previous leftover.
    assign abr_piso_4_sb_incr_val = sampled_in ? sym_beat_select + 1 : num_of_beats_nxt;
    assign abr_piso_4_sb_exp_data = buffer_reg >> (sym_beat_select * output_rate);
    assign buffer_nxt             = (buffer_reg >> (num_of_beats_reg * output_rate)) | data_i_masked_extended;

    always_comb begin
        // Remove the bits that will not be sampled when current input rate is smaller
        // than actual input rate.
        data_i_masked          = pi_data_i & ~({PISO_ACT_INPUT_RATE{1'b1}} << input_rate);
        data_i_masked_extended = {{BUFFER_W_DELTA{1'b0}}, data_i_masked};
        if (has_leftover_bits_reg) begin
            data_i_masked_extended = data_i_masked_extended << num_leftover_bits_reg;
        end
    end

    always_ff @(posedge pi_clk) begin
        if (!pi_rst_b || pi_zeroize) begin
            buffer_reg            <= '0;
            num_leftover_bits_reg <= '0;
            num_of_beats_reg      <= '0;
            has_leftover_bits_reg <= 1'b0;
            sampled_in_reg        <= 1'b0;
        end
        else begin
            if (pi_valid_i && !po_hold_o && !sampled_in_reg) begin
                buffer_reg            <= buffer_nxt;
                num_leftover_bits_reg <= num_leftover_bits_nxt;
                num_of_beats_reg      <= num_of_beats_nxt;
                has_leftover_bits_reg <= num_leftover_bits_nxt != 0;
            end
            if (sampled_in) begin
                sampled_in_reg <= 1'b1;
            end
        end
    end

    // Count the number of valid bits that are inside the buffer
    lubis_incr_decr_counter_m #(
        .INCR_VAL_WIDTH(PISO_PTR_W),
        .DECR_VAL_WIDTH(PISO_PTR_W),
        .COUNTER_WIDTH(PISO_PTR_W+1),
        .NUM_INC_SRCS (1)
    ) num_bits_in_buffer_counter
    (
        .clk       (pi_clk                  ),
        .rst       (!pi_rst_b || pi_zeroize ),
        .soft_rst  (1'b0                    ),
        .incr_en   (pi_valid_i && !po_hold_o),
        .decr_en   (po_valid_o && !pi_hold_i),
        .incr_val  (input_rate              ),
        .decr_val  (output_rate             ),
        .count     (num_bits_in_buffer      ),
        .count_next(/*open*/                )
    );

    // ------------------------------------------------------------------------------------------
    // DATA_O CHECKER
    // ------------------------------------------------------------------------------------------

    // Scoreboard instantiation
    lubis_scoreboard_unroll_ext_m #(
        .WIDTH            (PISO_ACT_INPUT_RATE ),
        .EXP_WIDTH        (PISO_ACT_OUTPUT_RATE),
        .DEPTH            (SCOREBOARD_DEPTH    ),
        .ENABLE_INVARIANCE(1'b0                ),
        .ENABLE_CMD_UNROLL(1'b1                )
    ) abr_piso_4_scoreboard
    (
        .clk          (pi_clk                                            ),
        .rst          (!pi_rst_b || pi_zeroize                           ),
        .soft_rst     (1'b0                                              ),
        .full         (1'b0                                              ),
        .empty        (1'b0                                              ),
        .data_in      (pi_data_i                                         ),
        .data_out     (po_data_o                                         ),
        .expected_data(abr_piso_4_sb_exp_data                            ),
        .incr_val     (abr_piso_4_sb_incr_val                            ),
        .push         (pi_valid_i && !po_hold_o                          ),
        .pop          (po_valid_o && !pi_hold_i                          ),
        .num_elements (/*open*/                                          ),
        .sampled_out  (/*open*/                                          ),
        .sym_data     (/*open*/                                          ),
        .must_read    (/*open*/                                          ),
        .sampled_in   (sampled_in                                        )
    );

    // ------------------------------------------------------------------------------------------
    // HOLD_O CHECKER
    // ------------------------------------------------------------------------------------------
    // When valid_i is asserted, hold_o is asserted if there is no spoce in the buffer
    // for the incoming data_i based on the current input_rate.
    assert_hold_o: assert property (disable iff(!pi_rst_b || pi_zeroize)
        pi_valid_i
    |->
        po_hold_o == ((PISO_BUFFER_W - num_bits_in_buffer) < input_rate)
    );

     // ------------------------------------------------------------------------------------------
    // VALID_O CHECKER
    // -------------------------------------------------------------------------------------------
    assert_valid_o: assert property (disable iff(!pi_rst_b || pi_zeroize)
        num_bits_in_buffer >= output_rate
    |->
        po_valid_o
    );

    assert_not_valid_o: assert property (disable iff(!pi_rst_b || pi_zeroize)
        num_bits_in_buffer < output_rate
    |->
        !po_valid_o
    );

    //  Add liveness property for the po_valid_o.
    assert_liveness_valid_o: assert property (disable iff(!pi_rst_b || pi_zeroize)
        num_bits_in_buffer > 0
    |->
        s_eventually(po_valid_o)
    );

endmodule

