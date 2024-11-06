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
// ntt_masked_BFU_adder
//======================================================================

module ntt_masked_BFU_add_sub
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
    input wire [WIDTH-1:0] rnd0, rnd1, rnd2, rnd3,
    output logic [1:0] res [WIDTH-1:0]
);

    //Internal signals
    logic [1:0][WIDTH-1:0] add_res;
    logic [1:0][WIDTH-1:0] add_res_reg [2*WIDTH+1:0];
    logic [1:0] add_res_rolled [WIDTH-1:0];
    logic [1:0] add_res_bool [WIDTH-1:0];
    logic [1:0] add_res_arith [WIDTH-1:0];
    logic [WIDTH-1:0] prime0, prime1, add_res_rolled0, add_res_rolled1;
    logic [1:0] add_res_reduced [WIDTH-1:0];
    logic [1:0] prime [WIDTH-1:0];

    //Perform addition on input shares
    abr_masked_N_bit_Arith_adder #(
        .WIDTH(WIDTH)
    ) masked_adder_inst (
        .clk(clk),
        .rst_n(reset_n),
        .zeroize(zeroize),
        .x(u),
        .y(v),
        .s(add_res)
    );

    //Adder delay flops
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            for (int i = 0; i < 2*WIDTH+1; i++) begin
                add_res_reg[i] <= 'h0;
            end
        end
        else if (zeroize) begin
            for (int i = 0; i < 2*WIDTH+1; i++) begin
                    add_res_reg[i] <= 'h0;
            end
        end
        else begin
            add_res_reg <= {add_res, add_res_reg[2*WIDTH+1:1]};
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

    // always_comb begin
    //     for(int i = 0; i< WIDTH; i++)  begin
    //         if (i==0) begin
    //             temp0[i] = {add_res_bool[HALF_WIDTH][1], add_res_bool[HALF_WIDTH][0]};
    //         end 
    //         else begin
    //             temp0[i] = '0;
    //         end
    //     end
    // end

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

    always_comb begin
        
        // prime0 = add_res_arith[HALF_WIDTH][0] * ('0 - MLDSA_Q);
        // prime1 = add_res_arith[HALF_WIDTH][1] * ('0 - MLDSA_Q);
        for (int i = 0; i < WIDTH; i++) begin
            prime[i][0] = add_res_arith[i][0] * ('0 - WIDTH'(MLDSA_Q));
            prime[i][1] = add_res_arith[i][1] * ('0 - WIDTH'(MLDSA_Q));
            add_res_reduced[i][0] = add_res_reg[0][0][i] + prime[i][0];
            add_res_reduced[i][1] = add_res_reg[0][1][i] + prime[i][1];
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
            res <= add_res_reduced; //TODO: check with Emre - shares XORed together give actual result. Is this correct? Or should they be added instead?
        end
    end


endmodule