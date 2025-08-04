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
// masked_barrett_reduction.sv
// -----------
// Performs masked Barrett reduction on a given input x.
// Latency: 6 cycles

module masked_barrett_reduction
    import abr_params_pkg::*;
    import ntt_defines_pkg::*;
    #(
        parameter MASKED_REG_SIZE = 2 * MLKEM_Q_WIDTH
    )
    (
        input wire clk,
        input wire rst_n,
        input wire zeroize,
        input wire [1:0][MASKED_REG_SIZE-1:0] x,
        input wire [11:0] rnd_12bit,
        input wire [13:0] rnd_14bit,
        input wire [MASKED_REG_SIZE-1:0] rnd_24bit,
        input wire [13:0] rnd_for_Boolean0,
        input wire [13:0] rnd_for_Boolean1,
        input wire rnd_1bit,
        output logic [1:0][MASKED_REG_SIZE-1:0] y
    );
    localparam ROLLER = (2**9)+(2**8)-1;

    logic [1:0][MASKED_REG_SIZE+13-1:0] tmp ;
    logic [1:0][12:0] t_int, c_int, c, t;

    logic [13:0] t0_plus_carry, t0_plus_t1, c0_plus_c1;
    logic [1:0][13:0] c_rolled;
    logic carry_x, carry_tmp, carry_t, carry_c, carry_y_int;
    logic [1:0][MASKED_REG_SIZE:0] qt;
    logic [1:0][MASKED_REG_SIZE-1:0] x_reg;
    logic [1:0][11:0] arith_Q;
    logic [2:0][1:0][12:0] c_reg ;
    logic [13:0] carry_t_int;

    logic [1:0][MASKED_REG_SIZE+13-1:0] correction;
    logic [MASKED_REG_SIZE:0] carry_x_ext;

    logic [1:0][MLKEM_Q_WIDTH-1:0] y_int;
    logic [MLKEM_Q_WIDTH:0] carry_y_int_ext;

    logic [MLKEM_Q_WIDTH:0] y_int_comb;
    logic [MASKED_REG_SIZE:0] x_comb;

    always_comb begin
        //Calculate carry_x
        x_comb = x[0] + x[1];
        carry_x = x_comb[MASKED_REG_SIZE]; //(x[0] + x[1]) >> MASKED_REG_SIZE;
        carry_x_ext = {carry_x, {(MASKED_REG_SIZE){1'b0}}};

        //Calculate correction
        correction[0] = 37'((carry_x_ext << 5) + (carry_x_ext << 3) + (carry_x_ext << 2) + (carry_x_ext << 1) + carry_x_ext);
        correction[1] = 37'((carry_x_ext << 12) + (carry_x_ext << 9) + (carry_x_ext << 8) + (carry_x_ext << 7));

        // x*mu
        tmp[0] = (x[0] << 12) + (x[0] << 9) + (x[0] << 8) + (x[0] << 7) + (x[0] << 5) + (x[0] << 3) + (x[0] << 2) + (x[0] << 1) + x[0];
        tmp[1] = (x[1] << 12) + (x[1] << 9) + (x[1] << 8) + (x[1] << 7) + (x[1] << 5) + (x[1] << 3) + (x[1] << 2) + (x[1] << 1) + x[1];

        //Apply correction to tmp
        tmp[0] = (tmp[0] - correction[0]);
        tmp[1] = (tmp[1] - correction[1]);

        // Calculate carry_tmp and mask tmp to 13 bits (tmp >> K)
        carry_tmp  = 25'(tmp[0][MASKED_REG_SIZE-1:0] + tmp[1][MASKED_REG_SIZE-1:0]) >> MASKED_REG_SIZE;
        t_int[0] = (tmp[0] >> MASKED_REG_SIZE);
        t_int[1] = (tmp[1] >> MASKED_REG_SIZE);

        // Add carry_tmp to t0
        t0_plus_carry = (t_int[0] + {{MLKEM_Q_WIDTH{1'b0}},carry_tmp});
    end

    //Flop t0 and t1
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            t <= '0;
            x_reg <= '0;
            c <= '0;

            for (int i = 0; i < 3; i++) begin
                c_reg[i] <= '0;
            end
        end
        else if (zeroize) begin
            t <= '0;
            x_reg <= '0;
            c <= '0;
            for (int i = 0; i < 3; i++) begin
                c_reg[i] <= '0;
            end
        end 
        else begin
            // Update t0 and t1 with the new values
            t[0] <= t0_plus_carry[12:0];
            t[1] <= t_int[1];
            x_reg <= x;
            c <= c_int;
            c_reg <= {c, c_reg[2:1]};
        end
    end

    // Calculate q * t
    always_comb begin
        t0_plus_t1 = t[0] + t[1];
        carry_t = t0_plus_t1[13];
        carry_t_int = carry_t ? 'h2000 : 'h0;
        qt[0] = ((t[0] << 11) + (t[0] << 10) + (t[0] << 8) + t[0] - carry_t_int - (carry_t_int << 10));
        qt[1] = 25'(((t[1] << 11) + (t[1] << 10) + (t[1] << 8) + t[1] - (carry_t_int << 8))) - (carry_t_int << 11);

        //Calculate c = x-t; - 13-bits
        c_int[0] = 13'(25'(x_reg[0]) - qt[0]);
        c_int[1] = 13'(25'(x_reg[1]) - qt[1]);

        //Use registered version of c0 and c1 to calculate carry_c and add roller
        c0_plus_c1 = (c[0] + c[1]);
        carry_c = c0_plus_c1[13];

        c_rolled[0] = c[0] + (ROLLER-(carry_c ? 'h2000 : 'h0));
        c_rolled[1] = {1'b0, c[1]};
    end

    //Barrett if condition masked instance - 3 cycles
    masked_barrett_if_cond_v2 masked_barrett_if_cond_inst (
        .clk(clk),
        .rst_n(rst_n),
        .zeroize(zeroize),
        .c_rolled(c_rolled),
        .rnd_12bit(rnd_12bit),
        .rnd_14bit(rnd_14bit),
        .rnd_for_Boolean0(rnd_for_Boolean0),
        .rnd_for_Boolean1(rnd_for_Boolean1),
        .rnd_1bit(rnd_1bit),
        .arith_Q(arith_Q)
    );

    //Calculate t = y - q

    always_comb begin
        y_int[0] = MLKEM_Q_WIDTH'(c_reg[0][0] - 13'(arith_Q[0]));
        y_int[1] = MLKEM_Q_WIDTH'(c_reg[0][1] - 13'(arith_Q[1]));

        y_int_comb = y_int[0] + y_int[1];
        carry_y_int = y_int_comb[MLKEM_Q_WIDTH];
        carry_y_int_ext = {carry_y_int, {(MLKEM_Q_WIDTH){1'b0}}};
    end

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            y <= '0;
        end
        else if (zeroize) begin
            y <= '0;
        end
        else begin
            y[0] <= MASKED_REG_SIZE'(MASKED_REG_SIZE'(y_int[0]) - rnd_24bit - MASKED_REG_SIZE'(carry_y_int_ext));
            y[1] <= MASKED_REG_SIZE'(MASKED_REG_SIZE'(y_int[1]) + rnd_24bit);
        end
    end


endmodule