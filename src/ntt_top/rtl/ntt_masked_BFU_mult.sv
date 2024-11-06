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
// ntt_masked_BFU_mult
// Performs two share multiplication and reduction
//======================================================================

module ntt_masked_BFU_mult
    import ntt_defines_pkg::*;
    import mldsa_params_pkg::*;
#(
    parameter WIDTH = 46,
    parameter HALF_WIDTH = WIDTH/2,
    parameter ROLLER = WIDTH'(2**13-1)
)
(
    input wire clk,
    input wire reset_n,
    input wire zeroize,
    input wire [1:0][WIDTH-1:0] u,
    input wire [1:0][WIDTH-1:0] v,
    input wire [WIDTH-1:0] rnd0, rnd1, rnd2, rnd3, rnd4,
    output logic [1:0] res [HALF_WIDTH-1:0]
);

    //Internal signals
    logic [1:0] mul_res [WIDTH-1:0];
    logic [1:0] mul_res_bool [WIDTH-1:0];
    logic [1:0] mul_res_bool_reduced [WIDTH-1:0];
    logic [1:0] mul_res_reduced [HALF_WIDTH-1:0];

    //Perform mul on input shares
    abr_masked_N_bit_mult_two_share #(
        .WIDTH(WIDTH)
    ) masked_mult_inst (
        .clk(clk),
        .rst_n(reset_n),
        .zeroize(zeroize),
        .random(rnd0),
        .x(u),
        .y(v),
        .s(mul_res)
    );

    abr_masked_A2B_conv #(
        .WIDTH(WIDTH)
    ) a2b_inst (
        .clk(clk),
        .rst_n(reset_n),
        .zeroize(zeroize),
        .x(mul_res),
        .rnd(rnd1),
        .rnd_for_Boolean0(rnd2),
        .rnd_for_Boolean1(rnd3),
        .s(mul_res_bool)
    );

    //redux46
    abr_masked_N_bit_Boolean_adder #(
        .WIDTH(10) //TODO: ask Emre - inputs are 10 bit, output should be 12 bits. Is it ok to put inputs at 12 too?
    ) bool_adder_inst0 (
        .clk(clk),
        .rst_n(reset_n),
        .zeroize(zeroize),
        .x({12'(mul_res_bool[22:13][1]), 12'(mul_res_bool[22:13][0])}),
        .y({12'(mul_res_bool[32:23][1]), 12'(mul_res_bool[32:23][0])}),
        .rnd(rnd4),
        .s()
    );

    //B2A
    abr_masked_B2A_conv #(
        .WIDTH(WIDTH)
    ) b2a_inst (
        .clk(clk),
        .rst_n(reset_n),
        .zeroize(zeroize),
        .rnd(),
        .x_boolean(mul_res_bool_reduced),
        .x_arith(mul_res_reduced)
    );

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            for (int i = 0; i < WIDTH; i++)
                res[i] <= 2'h0;
        end
        else if (zeroize) begin
            for (int i = 0; i < WIDTH; i++)
                res[i] <= 2'h0;
        end
        else begin
            res <= mul_res_reduced;
        end
    end


endmodule