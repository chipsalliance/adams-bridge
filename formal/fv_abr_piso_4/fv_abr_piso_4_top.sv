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


module fv_abr_piso_4_top
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
    parameter BUFFER_W_DELTA       = PISO_BUFFER_W-PISO_ACT_INPUT_RATE
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
    input logic [PISO_ACT_OUTPUT_RATE-1:0] po_data_o
    //$#//
);

    logic [PISO_PTR_W-1:0] input_rate;
    logic [PISO_PTR_W-1:0] output_rate;

    always_comb begin
        unique case (pi_mode)
        2'b00: input_rate = PISO_INPUT_RATE0;
        2'b01: input_rate = PISO_INPUT_RATE1;
        2'b10: input_rate = PISO_INPUT_RATE2;
        2'b11: input_rate = PISO_INPUT_RATE3;
        endcase

        unique case (pi_mode)
        2'b00: output_rate = PISO_OUTPUT_RATE0;
        2'b01: output_rate = PISO_OUTPUT_RATE1;
        2'b10: output_rate = PISO_OUTPUT_RATE2;
        2'b11: output_rate = PISO_OUTPUT_RATE3;
        endcase
    end

    fv_abr_piso_4_constraints #(
        .PISO_BUFFER_W(PISO_BUFFER_W),
        .PISO_PTR_W(PISO_PTR_W),
        .PISO_INPUT_RATE0(PISO_INPUT_RATE0),
        .PISO_INPUT_RATE1(PISO_INPUT_RATE1),
        .PISO_INPUT_RATE2(PISO_INPUT_RATE2),
        .PISO_INPUT_RATE3(PISO_INPUT_RATE3),
        .PISO_OUTPUT_RATE0(PISO_OUTPUT_RATE0),
        .PISO_OUTPUT_RATE1(PISO_OUTPUT_RATE1),
        .PISO_OUTPUT_RATE2(PISO_OUTPUT_RATE2),
        .PISO_OUTPUT_RATE3(PISO_OUTPUT_RATE3),
        .PISO_ACT_INPUT_RATE(PISO_ACT_INPUT_RATE),
        .PISO_ACT_OUTPUT_RATE(PISO_ACT_OUTPUT_RATE),
        .BUFFER_W_DELTA(BUFFER_W_DELTA)
    ) fv_abr_piso_4_constraints_i (.*);

    // Functional AIP of the abr_piso_4 block
    // Assertions on all outputs.
    fv_abr_piso_4 #(
        .PISO_BUFFER_W(PISO_BUFFER_W),
        .PISO_PTR_W(PISO_PTR_W),
        .PISO_INPUT_RATE0(PISO_INPUT_RATE0),
        .PISO_INPUT_RATE1(PISO_INPUT_RATE1),
        .PISO_INPUT_RATE2(PISO_INPUT_RATE2),
        .PISO_INPUT_RATE3(PISO_INPUT_RATE3),
        .PISO_OUTPUT_RATE0(PISO_OUTPUT_RATE0),
        .PISO_OUTPUT_RATE1(PISO_OUTPUT_RATE1),
        .PISO_OUTPUT_RATE2(PISO_OUTPUT_RATE2),
        .PISO_OUTPUT_RATE3(PISO_OUTPUT_RATE3),
        .PISO_ACT_INPUT_RATE(PISO_ACT_INPUT_RATE),
        .PISO_ACT_OUTPUT_RATE(PISO_ACT_OUTPUT_RATE),
        .BUFFER_W_DELTA(BUFFER_W_DELTA)
    ) fv_abr_piso_4_i (
        .*,
        .input_rate (input_rate ),
        .output_rate(output_rate)
    );

    // Handshake protocol AIP
    // Constrains valid_i input and asserts that hold_o
    // is eventually deasserted when valid_i is high.
    lubis_vld_rdy_hsk_aip #(
        .DATA_WIDTH(PISO_ACT_INPUT_RATE+2),
        .SOURCE    (0)
    ) destination_valid_i_hold_o
    (
        .clk        (pi_clk                 ),
        .rst_n      (pi_rst_b && !pi_zeroize),
        .valid      (pi_valid_i             ),
        .ready      (!po_hold_o             ),
        .data       ({pi_data_i, mode}      ),
        .disable_sig(1'b0)
    );

    // Handshake protocol AIP
    // Constrains hold_i input such that it is eventually
    // deasserted when valid_o is high. Asserts that valid_o
    // behaves according to handshaking protocol.
    logic [PISO_ACT_OUTPUT_RATE-1:0] data_o_masked;
    // Only the output rate bits should remain stable during the handshake
    assign data_o_masked = po_data_o & ~({PISO_ACT_OUTPUT_RATE{1'b1}} << output_rate);

    lubis_vld_rdy_hsk_aip #(
        .DATA_WIDTH(PISO_ACT_OUTPUT_RATE),
        .SOURCE    (1)
    ) source_valid_o_hold_i
    (
        .clk        (pi_clk                 ),
        .rst_n      (pi_rst_b && !pi_zeroize),
        .valid      (po_valid_o             ),
        .ready      (!pi_hold_i             ),
        .data       (data_o_masked          ),
        .disable_sig(1'b0                   )
    );

endmodule


bind abr_piso_4 fv_abr_piso_4_top  #(
    .PISO_BUFFER_W       (PISO_BUFFER_W       ),
    .PISO_PTR_W          (PISO_PTR_W          ),
    .PISO_INPUT_RATE0    (PISO_INPUT_RATE0    ),
    .PISO_INPUT_RATE1    (PISO_INPUT_RATE1    ),
    .PISO_INPUT_RATE2    (PISO_INPUT_RATE2    ),
    .PISO_INPUT_RATE3    (PISO_INPUT_RATE3    ),
    .PISO_OUTPUT_RATE0   (PISO_OUTPUT_RATE0   ),
    .PISO_OUTPUT_RATE1   (PISO_OUTPUT_RATE1   ),
    .PISO_OUTPUT_RATE2   (PISO_OUTPUT_RATE2   ),
    .PISO_OUTPUT_RATE3   (PISO_OUTPUT_RATE3   ),
    .PISO_ACT_INPUT_RATE (PISO_ACT_INPUT_RATE ),
    .PISO_ACT_OUTPUT_RATE(PISO_ACT_OUTPUT_RATE),
    .BUFFER_W_DELTA      (BUFFER_W_DELTA      )
) fv_abr_piso_4_top_i
(
    //#$bind
    .pi_clk (clk),
    .pi_rst_b (rst_b),
    .pi_zeroize (zeroize),
    .pi_mode (mode),
    .pi_valid_i (valid_i),
    .po_hold_o (hold_o),
    .pi_data_i (data_i),
    .po_valid_o (valid_o),
    .pi_hold_i (hold_i),
    .po_data_o (data_o)
    //$#//
);
