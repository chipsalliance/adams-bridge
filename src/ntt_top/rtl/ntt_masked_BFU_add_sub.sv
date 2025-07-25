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
// ntt_masked_BFU_adder - total end-to-end latency = 53 clks
//======================================================================

module ntt_masked_BFU_add_sub
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
    input wire sub,
    input wire [1:0][WIDTH-1:0] u,
    input wire [1:0][WIDTH-1:0] v,
    input wire [WIDTH-1:0] rnd0, rnd1, rnd2, rnd3,
    output logic [1:0] res [WIDTH-1:0]
);

    //Internal signals
    logic [1:0][WIDTH-1:0] v_int, add_res;
    logic [WIDTH+4:0][1:0][WIDTH-1:0] add_res_reg; //TODO parameterize
    logic [1:0] add_res_rolled [WIDTH-1:0];
    logic [1:0] add_res_bool [WIDTH-1:0];
    logic [1:0] add_res_arith [WIDTH-1:0];
    logic [WIDTH-1:0] prime0, prime1, add_res_rolled0, add_res_rolled1;
    logic [1:0][WIDTH-1:0] add_res_reduced, prime_packed;
    logic [1:0] prime [WIDTH-1:0];
    logic [WIDTH-1:0] add_res_bool0, add_res_bool1, add_res_arith0, add_res_arith1;

    always_comb begin
        if (sub) begin
            v_int[0] = MLDSA_Q - v[0];
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

    //Adder delay flops
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            for (int i = 0; i <= WIDTH+4; i++) begin
                add_res_reg[i] <= 'h0;
            end
        end
        else if (zeroize) begin
            for (int i = 0; i <= WIDTH+4; i++) begin
                add_res_reg[i] <= 'h0;
            end
        end
        else begin
            add_res_reg <= {add_res, add_res_reg[WIDTH+4:1]};
        end
    end

    //maskedAdder + reduction:
    always_comb begin
        add_res_rolled0 = add_res[0] + ROLLER;
        add_res_rolled1 = add_res[1];
        for (int i = 0; i < WIDTH; i++) begin
            add_res_rolled[i][0] = add_res_rolled0[i];
            add_res_rolled[i][1] = add_res_rolled1[i];
        end
    end

    //Takes 48 clks
    abr_masked_A2B_conv #(
        .WIDTH(WIDTH)
    ) a2b_inst (
        .clk(clk),
        .rst_n(reset_n),
        .zeroize(zeroize),
        .x(add_res_rolled),
        .rnd(rnd1),
        .rnd_for_Boolean0(rnd2),
        .rnd_for_Boolean1(rnd3),
        .s(add_res_bool)
    );

    logic [1:0] temp0 [WIDTH-1:0]; 

    //Convert 1 bit to 46 bit to pass to B2A converter - 1 clk
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            for (int i = 0; i < WIDTH; i++) begin
                temp0[i] <= 2'b0;
            end
        end
        else if (zeroize) begin
            for (int i = 0; i < WIDTH; i++) begin
                temp0[i] <= 2'b0;
            end
        end
        else begin
            for (int i = 0; i < WIDTH; i++) begin
                if (i==0) begin
                    temp0[i] <= {add_res_bool[HALF_WIDTH][1], add_res_bool[HALF_WIDTH][0]};
                end 
                else begin
                    temp0[i] <= '0;
                end
            end
        end
    end

    //Convert 24th bit to arithmetic domain - 2 clks
    abr_masked_B2A_conv #(
        .WIDTH(WIDTH)
    ) b2a_inst (
        .clk(clk),
        .rst_n(reset_n),
        .zeroize(zeroize),
        .rnd(rnd0),
        .x_boolean(temp0),
        .x_arith(add_res_arith)
    );

    //Organize wires for easier use and debug
    always_comb begin
        for(int i = 0; i< WIDTH; i++)  begin
            add_res_bool0[i] = add_res_bool[i][0];
            add_res_bool1[i] = add_res_bool[i][1];
            add_res_arith0[i] = add_res_arith[i][0];
            add_res_arith1[i] = add_res_arith[i][1]; 
        end
    
        //If bit[23] = 1, subtract Q from adder result
        prime0 = WIDTH'(add_res_arith0 * (~MLDSA_Q+'h1));
        prime1 = WIDTH'(add_res_arith1 * (~MLDSA_Q+'h1));
        prime_packed[0] = prime0;
        prime_packed[1] = prime1;
        add_res_reduced[0] = add_res_reg[0][0]+prime_packed[0];
        add_res_reduced[1] = add_res_reg[0][1]+prime_packed[1];
    end

    //Output flop - 1 clk
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
            for (int i = 0; i < WIDTH; i++) begin
                res[i] <= {add_res_reduced[1][i],add_res_reduced[0][i]};
            end
        end
    end


endmodule