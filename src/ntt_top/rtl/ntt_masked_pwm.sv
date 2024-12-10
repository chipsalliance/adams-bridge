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
// ntt_masked_pwm.sv
// --------
// This module performs masked pwm operation with or without accumulate
// on input shares. Always performs (u*v)+w (top level needs to drive 0
// to the w input if not in accumulate mode)
// 210 clks if PWM, 263 clks if PWMA

module ntt_masked_pwm
    import mldsa_params_pkg::*;
    import ntt_defines_pkg::*;
#(
    parameter WIDTH = 46
)
(
    input wire clk,
    input wire reset_n,
    input wire zeroize,
    input wire accumulate,
    input wire [1:0][WIDTH-1:0] u,
    input wire [1:0][WIDTH-1:0] v,
    input wire [1:0][WIDTH-1:0] w,
    input wire [4:0][WIDTH-1:0] rnd,
    output logic [1:0][WIDTH-1:0] res
);

    logic [1:0] mul_res [WIDTH-1:0];
    logic [1:0] w_reg [WIDTH-1:0];
    logic [1:0] w_unpacked [WIDTH-1:0];
    logic [1:0][WIDTH-1:0] mul_res_packed, w_reg_packed;
    logic [1:0] res_unpacked [WIDTH-1:0];

    always_comb begin
        for (int i = 0; i < WIDTH; i++) begin
            w_unpacked[i][0] = w[0][i];
            w_unpacked[i][1] = w[1][i];

            w_reg_packed[0][i] = w_reg[i][0];
            w_reg_packed[1][i] = w_reg[i][1];

            mul_res_packed[0][i] = mul_res[i][0];
            mul_res_packed[1][i] = mul_res[i][1];
        end
    end

    //210 clks
    ntt_masked_BFU_mult #(
        .WIDTH(WIDTH)
    ) mult_inst0 (
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .u(u),
        .v(v),
        .rnd0(rnd[0]),
        .rnd1(rnd[1]),
        .rnd2(rnd[2]),
        .rnd3(rnd[3]),
        .rnd4(rnd[4]),
        .res(mul_res)
    );

    //Delay reading addr until after PWM is done to do accumulate
    abr_delay_masked_shares #(
        .WIDTH(WIDTH),
        .N(MASKED_PWM_LATENCY)
    ) w_delay (
        .clk(clk),
        .rst_n(reset_n),
        .zeroize(zeroize),
        .input_reg(w_unpacked),
        .delayed_reg(w_reg)
    );

    //53 clks (accumulate case)
    ntt_masked_BFU_add_sub #(
        .WIDTH(WIDTH)
    ) add_inst0 (
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .sub(1'b0),
        .u(mul_res_packed),
        .v(w_reg_packed),
        .rnd0(rnd[0]),
        .rnd1(rnd[1]),
        .rnd2(rnd[2]),
        .rnd3(rnd[3]),
        .res(res_unpacked)
    );

    always_comb begin
        for (int i = 0; i < WIDTH; i++) begin
            res[0][i] = accumulate ? res_unpacked[i][0] : mul_res[i][0];
            res[1][i] = accumulate ? res_unpacked[i][1] : mul_res[i][1];
        end
    end

endmodule