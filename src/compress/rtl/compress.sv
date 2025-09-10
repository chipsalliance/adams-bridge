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
//======================================================================
//
// compress.sv
// --------
// Converts 12-bit coefficients into d-bit representation where d is the compression level.
// Based on input mode, d is selected and the following equation is performed:
// ((data[11:0] << d) + q/2) / q
// To efficiently perform /q operation, barrett reduction is used.

module compress
    import abr_params_pkg::*;
    import compress_defines_pkg::*;
    (
        input wire [MLKEM_Q_WIDTH-1:0] op_i,
        input compress_mode_t mode,
        output logic [MLKEM_Q_WIDTH-1:0] op_o
    );

    localparam HALF_Q = MLKEM_Q / 2;

    logic [3:0] d;
    logic [(2*MLKEM_Q_WIDTH)-1:0] data_lsh_d, lsh_plus_halfq;
    logic [MLKEM_Q_WIDTH-1:0] red_o;
    
    always_comb begin
        unique case(mode)
            0: d = 1;
            1: d = 5;
            2: d = 11;
            default: d = 1;
        endcase
    end

    always_comb data_lsh_d = (2*MLKEM_Q_WIDTH)'(op_i << d);
    always_comb lsh_plus_halfq = data_lsh_d + HALF_Q;

    always_comb op_o = (mode == 3) ? op_i : red_o; // No compression, just pass through if mode == 3

    barrett_reduction #(
        .prime(MLKEM_Q)
    ) compress_barret_reduction_inst (
        .x(lsh_plus_halfq),
        .inv(red_o),
        .r()
    );
endmodule