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
// ntt_masked_pairwm.sv
// --------
// This module performs masked pwm operation with or without accumulate
// on input shares. Always performs (u*v)+w (top level needs to drive 0
// to the w input if not in accumulate mode)
// latency with accumulate: 24 clks
// latency without accumulate: 17 clks

module ntt_masked_pairwm
    import abr_params_pkg::*;
    import ntt_defines_pkg::*;
#(
    parameter MASKED_WIDTH = 2 * MLKEM_Q_WIDTH
)
(
    input wire clk,
    input wire reset_n,
    input wire zeroize,
    input wire accumulate,
    input wire [1:0][MASKED_WIDTH-1:0] u0,
    input wire [1:0][MASKED_WIDTH-1:0] v0,
    input wire [1:0][MASKED_WIDTH-1:0] w0,
    input wire [1:0][MASKED_WIDTH-1:0] u1,
    input wire [1:0][MASKED_WIDTH-1:0] v1,
    input wire [1:0][MASKED_WIDTH-1:0] w1,
    input wire [1:0][MASKED_WIDTH-1:0] zeta,
    input wire [4:0][13:0] rnd, //TODO: how many bits?
    output logic [1:0][MASKED_WIDTH-1:0] res0,
    output logic [1:0][MASKED_WIDTH-1:0] res1
);

//Multiply results
logic [1:0] u0v0 [MASKED_WIDTH-1:0];
logic [1:0] u0v1 [MASKED_WIDTH-1:0];
logic [1:0] u1v0 [MASKED_WIDTH-1:0];
logic [1:0] zeta_v1 [MASKED_WIDTH-1:0];
logic [1:0] u1v1 [MASKED_WIDTH-1:0];
logic [1:0] zeta_v1_reduced_unpacked [MASKED_WIDTH-1:0];
logic [1:0][MASKED_WIDTH-1:0] u0v0_packed, u0v1_packed, u1v0_packed, zeta_v1_packed, u1v1_packed;

//Reduction results
logic [1:0][MLKEM_Q_WIDTH-1:0] u0v0_reduced, u0v1_reduced, u1v0_reduced, zeta_v1_reduced, u1v1_reduced;
logic [1:0][MASKED_WIDTH:0] uv0, uv1; //TODO: check width
logic [1:0][MASKED_WIDTH:0] uvw0, uvw1; //TODO: check width

//Delay regs
logic [1:0][MASKED_WIDTH-1:0] u1_reg           [MLKEM_MASKED_MULT_LATENCY-1:0];
logic [1:0][MASKED_WIDTH-1:0] u0v0_reduced_reg [MLKEM_MASKED_MULT_LATENCY-1:0];
logic [1:0][MASKED_WIDTH-1:0] u0v1_reduced_reg [MLKEM_MASKED_MULT_LATENCY-1:0];
logic [1:0][MASKED_WIDTH-1:0] u1v0_reduced_reg [MLKEM_MASKED_MULT_LATENCY-1:0];

always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        for (int i = 0; i < MLKEM_MASKED_MULT_LATENCY; i++) begin
            u1_reg[i] <= '0;
            u0v0_reduced_reg[i] <= '0;
            u0v1_reduced_reg[i] <= '0;
            u1v0_reduced_reg[i] <= '0;
        end
    end
    else if (zeroize) begin
        for (int i = 0; i < MLKEM_MASKED_MULT_LATENCY; i++) begin
            u1_reg[i] <= '0;
            u0v0_reduced_reg[i] <= '0;
            u0v1_reduced_reg[i] <= '0;
            u1v0_reduced_reg[i] <= '0;
        end
    end
    else begin
        u1_reg <= {u1, u1_reg[MLKEM_MASKED_MULT_LATENCY-1:1]};
        u0v0_reduced_reg <= {u0v0_reduced, u0v0_reduced_reg[MLKEM_MASKED_MULT_LATENCY-1:1]};
        u0v1_reduced_reg <= {u0v1_reduced, u0v1_reduced_reg[MLKEM_MASKED_MULT_LATENCY-1:1]};
        u1v0_reduced_reg <= {u1v0_reduced, u1v0_reduced_reg[MLKEM_MASKED_MULT_LATENCY-1:1]};
    end
end

//u0 * v0 - 2 clk
abr_masked_N_bit_mult_two_share #(
    .WIDTH(MASKED_WIDTH)
) masked_mult_u0_v0 (
    .clk(clk),
    .rst_n(reset_n),
    .zeroize(zeroize),
    .random(rnd[0]),
    .x(u0),
    .y(v0),
    .res(u0v0)
);

always_comb begin
    for (int i = 0; i < MASKED_WIDTH; i++) begin
        u0v0_packed[0][i] = u0v0[i][0];
        u0v0_packed[1][i] = u0v0[i][1];
    end
end

//6 clk
masked_barrett_reduction masked_u0v0_redux_inst (
    .clk(clk),
    .rst_n(reset_n),
    .zeroize(zeroize),
    .x(u0v0_packed),
    .rnd_12bit(rnd[0][11:0]),
    .rnd_14bit(rnd[1][13:0]),
    .rnd_for_Boolean0(rnd[2][13:0]),
    .rnd_for_Boolean1(rnd[3][13:0]),
    .rnd_1bit(rnd[4][0]),
    .y(u0v0_reduced)
);

//--------------------------------------
//u0 * v1
abr_masked_N_bit_mult_two_share #(
    .WIDTH(MASKED_WIDTH)
) masked_mult_u0_v1 (
    .clk(clk),
    .rst_n(reset_n),
    .zeroize(zeroize),
    .random(rnd[1]),
    .x(u0),
    .y(v1),
    .res(u0v1)
);

always_comb begin
    for (int i = 0; i < MASKED_WIDTH; i++) begin
        u0v1_packed[0][i] = u0v1[i][0];
        u0v1_packed[1][i] = u0v1[i][1];
    end
end

masked_barrett_reduction masked_u0v1_redux_inst (
    .clk(clk),
    .rst_n(reset_n),
    .zeroize(zeroize),
    .x(u0v1_packed),
    .rnd_12bit(rnd[1][11:0]),
    .rnd_14bit(rnd[2][13:0]),
    .rnd_for_Boolean0(rnd[3][13:0]),
    .rnd_for_Boolean1(rnd[4][13:0]),
    .rnd_1bit(rnd[0][0]),
    .y(u0v1_reduced)
);

//--------------------------------------
//u1 * v0
abr_masked_N_bit_mult_two_share #(
    .WIDTH(MASKED_WIDTH)
) masked_mult_u1_v0 (
    .clk(clk),
    .rst_n(reset_n),
    .zeroize(zeroize),
    .random(rnd[2]),
    .x(u1),
    .y(v0),
    .res(u1v0)
);

always_comb begin
    for (int i = 0; i < MASKED_WIDTH; i++) begin
        u1v0_packed[0][i] = u1v0[i][0];
        u1v0_packed[1][i] = u1v0[i][1];
    end
end

masked_barrett_reduction masked_u1v0_redux_inst (
    .clk(clk),
    .rst_n(reset_n),
    .zeroize(zeroize),
    .x(u1v0_packed),
    .rnd_12bit(rnd[2][11:0]),
    .rnd_14bit(rnd[3][13:0]),
    .rnd_for_Boolean0(rnd[4][13:0]),
    .rnd_for_Boolean1(rnd[0][13:0]),
    .rnd_1bit(rnd[1][0]),
    .y(u1v0_reduced)
);

//--------------------------------------
//zeta * v1
abr_masked_N_bit_mult_two_share #(
    .WIDTH(MASKED_WIDTH)
) masked_mult_zeta_v1 (
    .clk(clk),
    .rst_n(reset_n),
    .zeroize(zeroize),
    .random(rnd[3]),
    .x(zeta),
    .y(v1),
    .res(zeta_v1)
);

always_comb begin
    for (int i = 0; i < MASKED_WIDTH; i++) begin
        zeta_v1_packed[0][i] = zeta_v1[i][0];
        zeta_v1_packed[1][i] = zeta_v1[i][1];
    end
end

masked_barrett_reduction masked_zeta_v1_redux_inst (
    .clk(clk),
    .rst_n(reset_n),
    .zeroize(zeroize),
    .x(zeta_v1_packed),
    .rnd_12bit(rnd[3][11:0]),
    .rnd_14bit(rnd[4][13:0]),
    .rnd_for_Boolean0(rnd[0][13:0]),
    .rnd_for_Boolean1(rnd[1][13:0]),
    .rnd_1bit(rnd[2][0]),
    .y(zeta_v1_reduced)
);

always_comb begin
    for (int i = 0; i < MASKED_WIDTH; i++) begin
        zeta_v1_reduced_unpacked[i][0] = zeta_v1_reduced[0][i];
        zeta_v1_reduced_unpacked[i][1] = zeta_v1_reduced[1][i];
    end
end

//--------------------------------------
//u1 * (zeta * v1)
abr_masked_N_bit_mult_two_share #(
    .WIDTH(MASKED_WIDTH)
) masked_mult_u1v1 (
    .clk(clk),
    .rst_n(reset_n),
    .zeroize(zeroize),
    .random(rnd[4]),
    .x(u1_reg[0]), //delayed by 25 clks
    .y(zeta_v1_reduced_unpacked),
    .res(u1v1)
);

always_comb begin
    for (int i = 0; i < MASKED_WIDTH; i++) begin
        u1v1_packed[0][i] = u1v1[i][0];
        u1v1_packed[1][i] = u1v1[i][1];
    end
end

masked_barrett_reduction masked_u1v1_redux_inst (
    .clk(clk),
    .rst_n(reset_n),
    .zeroize(zeroize),
    .x(u1v1_packed),
    .rnd_12bit(rnd[4][11:0]),
    .rnd_14bit(rnd[0][13:0]),
    .rnd_for_Boolean0(rnd[1][13:0]),
    .rnd_for_Boolean1(rnd[2][13:0]),
    .rnd_1bit(rnd[3][0]),
    .y(u1v1_reduced)
);

//--------------------------------------
//Compute coefficients - 1 clk
abr_masked_N_bit_Arith_adder #(
    .WIDTH(MASKED_WIDTH)
) masked_uv0_coeff_adder_inst (
    .clk(clk),
    .rst_n(reset_n),
    .zeroize(zeroize),
    .x(u0v0_reduced_reg[0]), //delayed by 25 clks
    .y(u1v1_reduced),
    .s(uv0)
);

abr_masked_N_bit_Arith_adder #(
    .WIDTH(MASKED_WIDTH)
) masked_uv1_coeff_adder_inst (
    .clk(clk),
    .rst_n(reset_n),
    .zeroize(zeroize),
    .x(u0v1_reduced_reg[0]),
    .y(u1v0_reduced_reg[0]),
    .s(uv1)
);

//--------------------------------------
//Accumulate - 1 clk
abr_masked_N_bit_Arith_adder #(
    .WIDTH(MASKED_WIDTH)
) masked_uv0w0_acc_adder_inst (
    .clk(clk),
    .rst_n(reset_n),
    .zeroize(zeroize),
    .x(uv0),
    .y(w0), //TODO: make sure w0 is delayed to match latency of uv0
    .s(uvw0)
);

//6 clks
masked_barrett_reduction masked_uvw0_redux_inst (
    .clk(clk),
    .rst_n(reset_n),
    .zeroize(zeroize),
    .x(uvw0),
    .rnd_12bit(rnd[0][11:0]),
    .rnd_14bit(rnd[1][13:0]),
    .rnd_for_Boolean0(rnd[2][13:0]),
    .rnd_for_Boolean1(rnd[3][13:0]),
    .rnd_1bit(rnd[4][0]),
    .y(res0_acc)
);

abr_masked_N_bit_Arith_adder #(
    .WIDTH(MASKED_WIDTH)
) masked_uv1w1_acc_adder_inst (
    .clk(clk),
    .rst_n(reset_n),
    .zeroize(zeroize),
    .x(uv1),
    .y(w1), //TODO: make sure w1 is delayed to match latency of uv0
    .s(uvw1)
);

masked_barrett_reduction masked_uvw1_redux_inst (
    .clk(clk),
    .rst_n(reset_n),
    .zeroize(zeroize),
    .x(uvw1),
    .rnd_12bit(rnd[1][11:0]),
    .rnd_14bit(rnd[2][13:0]),
    .rnd_for_Boolean0(rnd[3][13:0]),
    .rnd_for_Boolean1(rnd[4][13:0]),
    .rnd_1bit(rnd[0][0]),
    .y(res1_acc)
);

always_comb begin
    res0 = accumulate ? res0_acc : uv0;
    res1 = accumulate ? res1_acc : uv1;
end

endmodule