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
<<<<<<< HEAD
// Latency: 6 cycles
=======
// Latency: 23 cycles
>>>>>>> main

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
        input wire [13:0] rnd_for_Boolean0,
        input wire [13:0] rnd_for_Boolean1,
        input wire rnd_1bit,
        output logic [1:0][MLKEM_Q_WIDTH-1:0] y
    );
    localparam ROLLER = (2**9)+(2**8)-1;

    logic [1:0][MASKED_REG_SIZE+13-1:0] tmp ;
    logic [1:0][12:0] t_int, c_int, c, t;

    logic [13:0] t0_plus_carry, t0_plus_t1, c0_plus_c1;
    logic [1:0][13:0] c_rolled;
    logic carry, carry2, carry3;
    logic [1:0][MASKED_REG_SIZE:0] qt;
    logic [1:0][MASKED_REG_SIZE-1:0] x_reg;
    logic [1:0][11:0] arith_Q;
<<<<<<< HEAD
    logic [1:0][12:0] c_reg [2:0];
=======
    logic [1:0][12:0] c_reg [20:0];
    // logic [MASKED_REG_SIZE+13:0] tmp_comb;
>>>>>>> main

    always_comb begin
        // x*mu
        tmp[0] = (x[0] << 12) + (x[0] << 9) + (x[0] << 8) + (x[0] << 7) + (x[0] << 5) + (x[0] << 3) + (x[0] << 2) + (x[0] << 1) + x[0];
        tmp[1] = (x[1] << 12) + (x[1] << 9) + (x[1] << 8) + (x[1] << 7) + (x[1] << 5) + (x[1] << 3) + (x[1] << 2) + (x[1] << 1) + x[1];

        // Calculate carry and mask tmp to 13 bits (tmp >> K)
<<<<<<< HEAD
=======
        // tmp_comb = tmp[0] + tmp[1];
>>>>>>> main
        carry  = (tmp[0][MASKED_REG_SIZE-1:0] + tmp[1][MASKED_REG_SIZE-1:0]) >> MASKED_REG_SIZE;
        t_int[0] = (tmp[0] >> MASKED_REG_SIZE);
        t_int[1] = (tmp[1] >> MASKED_REG_SIZE);

        // Add carry to t0
        t0_plus_carry = (t_int[0] + {{MLKEM_Q_WIDTH{1'b0}},carry});
    end

    //Flop t0 and t1
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            t <= '0;
            x_reg <= '0;
            c <= '0;

<<<<<<< HEAD
            for (int i = 0; i < 3; i++) begin
=======
            for (int i = 0; i < 21; i++) begin
>>>>>>> main
                c_reg[i] <= '0;
            end
        end
        else if (zeroize) begin
            t <= '0;
            x_reg <= '0;
            c <= '0;
<<<<<<< HEAD
            for (int i = 0; i < 3; i++) begin
=======
            for (int i = 0; i < 21; i++) begin
>>>>>>> main
                c_reg[i] <= '0;
            end
        end 
        else begin
            // Update t0 and t1 with the new values
            t[0] <= t0_plus_carry[12:0];
            t[1] <= t_int[1];
            x_reg <= x;
            c <= c_int;
<<<<<<< HEAD
            c_reg <= {{c[1], c[0]}, c_reg[2:1]};
=======
            c_reg <= {{c_int[1], c_int[0]}, c_reg[20:1]};
>>>>>>> main
        end
    end

    // Calculate q * t
    always_comb begin
        t0_plus_t1 = t[0] + t[1];
        carry2 = t0_plus_t1[13];
        qt[0] = ((t[0] << 11) + (t[0] << 10) + (t[0] << 8) + t[0] - carry2 - (carry2 << 10));
        qt[1] = ((t[1] << 11) + (t[1] << 10) + (t[1] << 8) + t[1] - (carry2 << 8) - (carry2 << 11));

        //Calculate c = x-t; - 13-bits
        c_int = x_reg - qt;

        //Use registered version of c0 and c1 to calculate carry and add roller
        c0_plus_c1 = (c[0] + c[1]);
        carry3 = c0_plus_c1[13];

        c_rolled[0] = c[0] + (ROLLER-carry3);
        c_rolled[1] = c[1];
    end

<<<<<<< HEAD
    //Barrett if condition masked instance - 3 cycles
    masked_barrett_if_cond_v2 masked_barrett_if_cond_inst (
=======
    //Barrett if condition masked instance - 20 cycles
    masked_barrett_if_cond masked_barrett_if_cond_inst (
>>>>>>> main
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
<<<<<<< HEAD
=======
    // always_comb begin
    //     y[0] = MLKEM_Q_WIDTH'(c_reg[0][0] - 13'(arith_Q[0]));
    //     y[1] = MLKEM_Q_WIDTH'(c_reg[0][1] - 13'(arith_Q[1]));
    // end
>>>>>>> main
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            y <= '0;
        end
        else if (zeroize) begin
            y <= '0;
        end
        else begin
            y[0] <= MLKEM_Q_WIDTH'(c_reg[0][0] - 13'(arith_Q[0]));
            y[1] <= MLKEM_Q_WIDTH'(c_reg[0][1] - 13'(arith_Q[1]));
        end
    end


endmodule