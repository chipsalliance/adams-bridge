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
// decompress.sv
// --------
// Converts d-bit coefficients into 12-bit representation where d is the decompression level.

module decompress
    import abr_params_pkg::*;
    import decompress_defines_pkg::*;
    (
        input wire [MLKEM_Q_WIDTH-1:0] op_i,
        input decompress_mode_t mode,
        output logic [MLKEM_Q_WIDTH-1:0] op_o
    );

    logic [3:0] d;
    logic [(2*MLKEM_Q_WIDTH)-1:0] op_mult_add;
    
    always_comb begin
        if (mode == 3) begin
            op_o = (op_i < MLKEM_Q) ? op_i : '0; // No decompression, just pass through if < MLKEM_Q
        end else begin
            unique case(mode)
                DECOMPRESS1:  d = 1;
                DECOMPRESS5:  d = 5;
                DECOMPRESS11: d = 11;
                default: d = 1;
            endcase

            op_mult_add = (MLKEM_Q * op_i) + 2**(d - 1);
            op_o = MLKEM_Q_WIDTH'(op_mult_add >> d);
        end
    end
endmodule