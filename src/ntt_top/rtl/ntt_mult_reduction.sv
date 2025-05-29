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
//
//======================================================================
//
// ntt_mult_reduction.sv
// --------
// Performs (input mod MLDSA_Q) where the input comes from multiplier in the BF. 
// This is a custom reduction block that is specific to MLDSA_Q.
// 
// 
//======================================================================

module ntt_mult_reduction #(
    parameter REG_SIZE = 23,
    parameter PRIME = 23'd8380417
)
(
    input wire clk,
    input wire reset_n,
    input wire zeroize,

    input wire [(2*REG_SIZE)-1:0] opa_i,
    output logic [REG_SIZE-1:0] res_o,
    output logic ready_o
);

    logic [2*REG_SIZE-1:0] z;
    logic [2*REG_SIZE-1:0] z_f;
    // logic [REG_SIZE:0] c,d;
    logic [11:0] c;
    logic [10:0] d;
    logic [REG_SIZE-1:0] e;
    logic [13:0] f;
    logic [REG_SIZE-1:0] g_reduced;
    logic [REG_SIZE-1:0] res;
    logic ready;
    logic ready_e, ready_g_reduced;
    logic enable_reg;
    logic [1:0] push_result_reg;


    //Perform modular reduction on mult output
    //-----------------------------------------

    //Flop mult result
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            z_f <= 'h0;
        end
        else if (zeroize) begin
            z_f <= 'h0;
        end
        else begin
            z_f <= opa_i;
        end
    end

    //Calculate c, d, e, f
    //---------------------

    always_comb begin
        c = z_f[45:43] + z_f[42:33] + z_f[32:23] + z_f[22:13];
        d = c[11:10] + c[9:0];
        f = z_f[45:43] + z_f[45:33] + c[11:10];
    end

    //Mod add
    abr_ntt_add_sub_mod #(
        .REG_SIZE(REG_SIZE)
        )
        mod_add_inst_0(
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .add_en_i(1'b1), //(enable_reg),
        .sub_i(1'b0),
        .opa_i({{REG_SIZE-14{1'b0}},f[13:0]}),
        .opb_i(z_f[45:23]),
        .prime_i(PRIME),
        .mlkem(1'b0),
        .res_o(e),
        .ready_o() //(ready_e)
    );

    //Mod add
    ntt_special_adder #(
        .REG_SIZE(REG_SIZE)
        )
        mod_add_inst_1(
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .add_en_i(1'b1), //(enable_reg),
        .opa_i(d[10:0]),
        .opb_i(z_f[12:0]), //24 bit input
        .prime_i(PRIME),
        .res_o(g_reduced),
        .ready_o() //(ready_g_reduced)
    );

    //Calculate ab mod q
    //--------------------
    //Mod sub
    abr_ntt_add_sub_mod #(
        .REG_SIZE(REG_SIZE)
        )
        mod_sub_inst_0(
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .add_en_i(1'b1), //(ready_e && ready_g_reduced),
        .sub_i(1'b1),
        .opa_i(g_reduced),
        .opb_i(e[22:0]),
        .prime_i(PRIME),
        .mlkem(1'b0),
        .res_o(res),
        .ready_o() //(ready)
    );

    //Flop res to avoid timing issues
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            res_o <= 'h0;
        end
        else if (zeroize) begin
            res_o <= 'h0;
        end
        else begin //if (ready) begin
            res_o <= res;
        end
    end

endmodule
