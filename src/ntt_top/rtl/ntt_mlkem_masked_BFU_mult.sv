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
// ntt_mlkem_masked_BFU_mult
// Performs two share multiplication and reduction - total latency = 8 clks
//======================================================================

module ntt_mlkem_masked_BFU_mult
    import ntt_defines_pkg::*;
    import abr_params_pkg::*;
#(
    parameter WIDTH = 24,
    parameter HALF_WIDTH = WIDTH/2
)
(
    input wire clk,
    input wire reset_n,
    input wire zeroize,
    input wire [1:0][WIDTH-1:0] u,
    input wire [1:0][WIDTH-1:0] v,
    input wire [4:0][13:0] rnd,
    input wire [WIDTH-1:0] rnd_24bit,
    output logic [1:0][WIDTH-1:0] res
);

    //Internal signals
    logic [1:0] mul_res [WIDTH-1:0];
    logic [WIDTH-1:0] mul_res0, mul_res1;
    logic [1:0][WIDTH-1:0] final_res;
    logic [1:0][WIDTH-1:0] mul_res_reduced;

    //Perform mul on input shares - 2 clk
    abr_masked_N_bit_mult_two_share #(
        .WIDTH(WIDTH)
    ) masked_two_share_mult_inst (
        .clk(clk),
        .rst_n(reset_n),
        .zeroize(zeroize),
        .random({rnd[1][9:0], rnd[0]}),
        .x(u),
        .y(v),
        .z(mul_res)
    );

    always_comb begin
        for(int i = 0; i < WIDTH; i++) begin
            mul_res0[i] = mul_res[i][0];
            mul_res1[i] = mul_res[i][1];
        end
    end

    //6 clks
    masked_barrett_reduction masked_barrett_mult_inst (
        .clk(clk),
        .rst_n(reset_n),
        .zeroize(zeroize),
        .x({mul_res1, mul_res0}),
        .rnd_12bit(rnd[1][11:0]),
        .rnd_14bit(rnd[2]),
        .rnd_24bit(rnd_24bit),
        .rnd_for_Boolean0(rnd[3]),
        .rnd_for_Boolean1(rnd[4]),
        .rnd_1bit(rnd[0][0]),
        .y(mul_res_reduced)
    );
    
    always_comb res = mul_res_reduced;


endmodule