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
// masked_barrett_if_cond_v2.sv
// -----------
// Checks if input is greater than 2^12.
// Latency: 3 cycles

module masked_barrett_if_cond_v2
    import abr_params_pkg::*;
    import ntt_defines_pkg::*;
    #(
        parameter MASKED_REG_SIZE = 2 * MLKEM_Q_WIDTH
    )
    (
        input wire clk,
        input wire rst_n,
        input wire zeroize,
        input wire [1:0][13:0] c_rolled,
        input wire [11:0] rnd_12bit,
        input wire [13:0] rnd_14bit,
        input wire [13:0] rnd_for_Boolean0,
        input wire [13:0] rnd_for_Boolean1,
        input wire rnd_1bit,
        output logic [1:0][MLKEM_Q_WIDTH-1:0] arith_Q
    );

    logic [1:0] c_rolled_unpacked [13:0];
    logic [1:0] c_boolean [13:0];
    logic [1:0] c_carry;
    logic [1:0][MLKEM_Q_WIDTH-1:0] q_share ;
    logic [1:0][MLKEM_Q_WIDTH-1:0] boolean_y;
    logic [1:0] boolean_y_unpacked [MLKEM_Q_WIDTH-1:0];
    logic [1:0] arith_Q_unpacked [MLKEM_Q_WIDTH-1:0];

    logic [14:0] c_rolled_comb;
    logic carry0, carry1;
    logic c_carry_comb;

    always_comb begin
        for (int i = 0; i < 14; i++) begin
            c_rolled_unpacked[i][1] = c_rolled[1][i];
            c_rolled_unpacked[i][0] = c_rolled[0][i];
        end
    end

    always_comb begin
        c_rolled_comb = c_rolled[0] + c_rolled[1];
        carry0 = c_rolled_comb[12];
        carry1 = c_rolled_comb[13];
        c_carry_comb = carry0 | carry1;

        //Refresh randomness
        c_carry[0] = c_carry_comb ^ rnd_1bit;
        c_carry[1] = rnd_1bit;
    end

    //Split q into shares
    always_comb begin
        q_share[0] = MLKEM_Q ^ rnd_12bit;
        q_share[1] = rnd_12bit;
    end

    //And q with carry - 1 cycle
    // Instantiate masked AND gates (DOM) for each bit
    genvar i_AND;
    generate
        for (i_AND = 0; i_AND < MLKEM_Q_WIDTH; i_AND++) begin : gen_DOM_AND
            abr_masked_AND and_gate_inst (
                .clk(clk),
                .rst_n(rst_n),
                .zeroize(zeroize),
                .x(c_carry),
                .y({q_share[1][i_AND], q_share[0][i_AND]}),
                .rnd(rnd_14bit[i_AND]),
                .c(boolean_y_unpacked[i_AND])
            );
        end
    endgenerate

    //Convert boolean_y to arithmetic domain - 2 cycles
    abr_masked_B2A_conv #(
        .WIDTH(MLKEM_Q_WIDTH)
    ) barrett_b2a_inst (
        .clk(clk),
        .rst_n(rst_n),
        .zeroize(zeroize),
        .x_boolean(boolean_y_unpacked),
        .rnd(rnd_14bit[MLKEM_Q_WIDTH-1:0]),
        .x_arith(arith_Q_unpacked)
    );

    //Convert arithQ to packed
    always_comb begin
        for (int i = 0; i < MLKEM_Q_WIDTH; i++) begin
            arith_Q[0][i] = arith_Q_unpacked[i][0];
            arith_Q[1][i] = arith_Q_unpacked[i][1];
        end
    end
endmodule