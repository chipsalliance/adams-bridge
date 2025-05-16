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
// Performs two share multiplication and reduction - total latency = 210 clks
//======================================================================

module ntt_masked_BFU_mult
    import ntt_defines_pkg::*;
    import abr_params_pkg::*;
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
    output logic [1:0] res [WIDTH-1:0]
);

    //Internal signals
    logic [1:0] mul_res [WIDTH-1:0];
    logic [WIDTH-1:0] mul_res0, mul_res1, mul_res_combined, mul_res_combined_share0;
    logic [1:0] mul_res_refresh [WIDTH-1:0];
    logic [1:0] mul_res_bool [WIDTH-1:0];
    logic [WIDTH-1:0] mul_res_bool0, mul_res_bool1;
    logic [1:0][WIDTH-1:0] temp, final_res;
    logic [1:0] mul_res_bool_reduced [HALF_WIDTH-1:0];
    logic [1:0] mul_res_bool_reduced_padded [WIDTH-1:0];
    logic [1:0] mul_res_reduced [WIDTH-1:0];
    logic [WIDTH-1:0] mul_res_bool_redux0, mul_res_bool_redux1, mul_res_redux0, mul_res_redux1;

    //Perform mul on input shares - 2 clk
    abr_masked_N_bit_mult_two_share #(
        .WIDTH(WIDTH)
    ) masked_two_share_mult_inst (
        .clk(clk),
        .rst_n(reset_n),
        .zeroize(zeroize),
        .random(rnd0),
        .x(u),
        .y(v),
        .z(mul_res)
    );

    always_comb begin
        for(int i = 0; i < WIDTH; i++) begin
            mul_res0[i] = mul_res[i][0];
            mul_res1[i] = mul_res[i][1];
        end
        mul_res_combined = (mul_res0 + mul_res1) % MLDSA_Q;
        mul_res_combined_share0 = mul_res_combined - rnd0;
        for (int i = 0; i < WIDTH; i++) begin
            mul_res_refresh[i][0] = mul_res_combined_share0[i];
            mul_res_refresh[i][1] = rnd0[i];
        end
    end

    //48 clks
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

    //Mult reduction46 - 157 clks
    ntt_masked_mult_redux46 #(
        .WIDTH(WIDTH)
    ) mult_redux46_inst (
        .clk(clk),
        .rst_n(reset_n),
        .zeroize(zeroize),
        .rnd0_11(rnd0[10:0]),
        .rnd1_11(rnd0[21:11]),
        .rnd2_11(rnd0[32:22]),
        .rnd0_12(rnd0[44:33]),
        .rnd0_4(rnd1[3:0]),
        .rnd0_14(rnd1[17:4]),
        .rnd_3WIDTH({rnd4[HALF_WIDTH-1:0], rnd3[HALF_WIDTH-1:0], rnd2[HALF_WIDTH-1:0]}),
        .x(mul_res_bool),
        .y(mul_res_bool_reduced)
    );
    
    always_comb begin
        for (int i = 0; i < HALF_WIDTH; i++) begin
            mul_res_bool_reduced_padded[i][0] = mul_res_bool_reduced[i][0];
            mul_res_bool_reduced_padded[i][1] = mul_res_bool_reduced[i][1];
        end
        for (int i = HALF_WIDTH; i < WIDTH; i++) begin
            mul_res_bool_reduced_padded[i] = 2'b00;
        end
    end

    //B2A - 2 clks
    abr_masked_B2A_conv #(
        .WIDTH(WIDTH)
    ) b2a_inst (
        .clk(clk),
        .rst_n(reset_n),
        .zeroize(zeroize),
        .rnd(rnd0),
        .x_boolean(mul_res_bool_reduced_padded),
        .x_arith(mul_res_reduced)
    );

    always_comb begin
        
        for (int i = 0; i < WIDTH; i++) begin
            mul_res_redux0[i] = mul_res_reduced[i][0];
            mul_res_redux1[i] = mul_res_reduced[i][1];
        end
    end

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

    always_comb begin
        for ( int i = 0; i < WIDTH; i++) begin
            final_res[0][i] = res[i][0];
            final_res[1][i] = res[i][1];
        end
        
    end


endmodule