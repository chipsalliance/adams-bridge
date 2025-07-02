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
// ntt_mlkem_masked_BFU_adder - total end-to-end latency = 7 clks
//======================================================================

module ntt_mlkem_masked_BFU_add_sub
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
    input wire sub,
    input wire [1:0][WIDTH-1:0] u,
    input wire [1:0][WIDTH-1:0] v,
    input wire [3:0][13:0] rnd,
    input wire [WIDTH-1:0] rnd_24bit,
    output logic [1:0][WIDTH-1:0] res
);

    //Internal signals
    logic [1:0][WIDTH-1:0] v_int, add_res;
    logic [1:0][WIDTH-1:0] add_res_reduced;

    //Add flops to inputs to avoid pruning TODO
    always_comb begin
        if (sub) begin
            v_int[0] = MLKEM_Q - v[0];
            v_int[1] = (~v[1] + 'h1); 
        end
        else begin
            v_int[0] = v[0];
            v_int[1] = v[1];
        end
    end

    //Perform addition on input shares - 1 clk latency
    abr_masked_N_bit_Arith_adder #(
        .WIDTH(WIDTH)
    ) masked_adder_inst (
        .clk(clk),
        .rst_n(reset_n),
        .zeroize(zeroize),
        .x(u),
        .y(v_int),
        .s(add_res)
    );

    //6 clks
    masked_barrett_reduction masked_barrett_add_sub_inst (
        .clk(clk),
        .rst_n(reset_n),
        .zeroize(zeroize),
        .x(add_res),
        .rnd_12bit(rnd[0][11:0]),
        .rnd_14bit(rnd[1]),
        .rnd_24bit(rnd_24bit),
        .rnd_for_Boolean0(rnd[2]),
        .rnd_for_Boolean1(rnd[3]),
        .rnd_1bit(rnd[0][12]),
        .y(add_res_reduced)
    );

    always_comb begin
        res = add_res_reduced;
    end


endmodule