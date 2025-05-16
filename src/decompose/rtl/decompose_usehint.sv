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
// decompose_usehint.sv
// ------------
// Consumes output of decompose and hint bit from makehint to modify w1 component
// before performing w1Encode on it
// This unit performs the following calc:
// (w0 == 0 || w0 > gamma2) ? (w1 = (w1-1) mod 16) : (w1 = (w1 + 1) mod 16)
// If makehint hint bit is 0, w1 is directly passed onto w1 encode. If makehint hint bit is 1,
// above modified w1 is passed onto w1 encode

module decompose_usehint
    import abr_params_pkg::*;
    #(
        parameter REG_SIZE = 23
    )
    (
        input wire clk,
        input wire reset_n,
        input wire zeroize,

        input wire usehint_enable,
        input wire [REG_SIZE-1:0] w0_i, 
        input wire [3:0] w1_i, 
        input wire hint_i,

        //output to w1 encode
        output logic [3:0] w1_o,
        output logic ready_o
    );

    logic [3:0] w1_plus_one, w1_minus_one;
    logic [3:0] w1_mux;
    logic ready;
    logic [REG_SIZE-1:0] w0_reg;
    logic [3:0] w1_reg;
    logic hint_reg;

    //Delay flops
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            w0_reg <= 'h0;
            w1_reg <= 'h0;
            hint_reg <= 'h0;
        end
        else if (zeroize) begin
            w0_reg <= 'h0;
            w1_reg <= 'h0;
            hint_reg <= 'h0;
        end
        else begin
            w0_reg <= w0_i;
            w1_reg <= w1_i;
            hint_reg <= hint_i;
        end
    end

    abr_add_sub_mod #(
        .REG_SIZE(4)
    ) 
    usehint_add_inst (
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .add_en_i(usehint_enable),
        .sub_i(1'b0),
        .opa_i(w1_i),
        .opb_i(4'(1)),
        .prime_i(4'(16)),
        .res_o(w1_plus_one),
        .ready_o()
    );

    abr_add_sub_mod #(
        .REG_SIZE(4)
    ) 
    usehint_sub_inst (
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .add_en_i(usehint_enable),
        .sub_i(1'b1),
        .opa_i(w1_i),
        .opb_i(4'(1)),
        .prime_i(4'(16)),
        .res_o(w1_minus_one),
        .ready_o()
    );

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            ready <= 'b0;
        else if (zeroize)
            ready <= 'b0;
        else
            ready <= usehint_enable;
    end

    always_comb begin
        if (ready) begin
            w1_mux = ((w0_reg == 'h0) | (w0_reg > MLDSA_GAMMA2)) ? w1_minus_one : w1_plus_one;
            w1_o   = hint_reg ? w1_mux : w1_reg;
        end
        else begin
            w1_mux = 'h0;
            w1_o   = 'h0;
        end
    end

    always_comb ready_o = ready;
endmodule
