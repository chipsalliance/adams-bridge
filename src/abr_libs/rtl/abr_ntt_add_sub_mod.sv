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
// abr_ntt_add_sub_mod.sv
// --------
// modular addtion/subtraction module to compute opa+-opb % prime
// This is intended specifically for ntt usage, where input sizes differ for MLDSA vs MLKEM
//
//======================================================================

module abr_ntt_add_sub_mod 
    import abr_params_pkg::*;
    #(
    parameter REG_SIZE      = 384
    )
    (
    // Clock and reset.
    input wire           clk,
    input wire           reset_n,
    input wire           zeroize,

    // DATA PORT
    input  wire                 add_en_i,
    input  wire                 sub_i,
    input  wire  [REG_SIZE-1:0] opa_i,
    input  wire  [REG_SIZE-1:0] opb_i,
    input  wire  [REG_SIZE-1:0] prime_i,
    input  wire                 mlkem,
    output logic [REG_SIZE-1:0] res_o,
    output logic                ready_o
);
  
    logic [REG_SIZE-1 : 0] opb0;
    logic [REG_SIZE-1 : 0] opb1;
    logic [REG_SIZE-1 : 0] r0;
    logic [REG_SIZE-1 : 0] r1;
    logic                  carry0; 
    logic                  carry0_int; 

    logic                  sub_n;
    logic [REG_SIZE-1 : 0] r0_reg;
    logic                  carry0_reg;

    logic                  carry1;
    logic                  carry1_int;
    logic [1 : 0]          push_result_reg;

    abr_adder #(
        .RADIX(REG_SIZE)
        ) 
        adder_inst_0(
        .a_i(opa_i),
        .b_i(mlkem ? {{(REG_SIZE-MLKEM_REG_SIZE){1'b0}}, opb0[MLKEM_REG_SIZE-1:0]} : opb0),
        .cin_i(sub_i),
        .s_o(r0),
        .cout_o(carry0_int)
    );

    abr_adder #(
        .RADIX(REG_SIZE)
        ) 
        adder_inst_1(
        .a_i(mlkem ? {{(REG_SIZE-MLKEM_REG_SIZE){1'b0}}, r0_reg[MLKEM_REG_SIZE-1:0]} : r0_reg), //discard carry bit (bit 12) in mlkem
        .b_i(mlkem ? {{(REG_SIZE-MLKEM_REG_SIZE){1'b0}}, opb1[MLKEM_REG_SIZE-1:0]} : opb1),
        .cin_i(sub_n),
        .s_o(r1),
        .cout_o(carry1_int)
    );

    assign carry0 = mlkem ? r0[MLKEM_REG_SIZE] : carry0_int;
    assign carry1 = mlkem ? r1[MLKEM_REG_SIZE] : carry1_int;

    assign opb0 = sub_i ? ~opb_i : opb_i;

    always_ff @(posedge clk or negedge reset_n) 
    begin
        if(!reset_n) begin
            r0_reg <= '0;
            carry0_reg <= '0;
            sub_n <= '0;
            opb1 <= '0;
        end
        else if (zeroize) begin
            r0_reg <= '0;
            carry0_reg <= '0;
            sub_n <= '0;
            opb1 <= '0;
        end
        else if (add_en_i) begin 
            r0_reg <= r0;
            carry0_reg <= carry0;
            sub_n <= !sub_i;
            if (sub_i)
                opb1 <= prime_i;
            else
                opb1 <= ~prime_i;
        end
    end

    // Determines when results are ready
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            push_result_reg <= 2'b0;
        else if (zeroize)
            push_result_reg <= 2'b0;
        else if (add_en_i)
            push_result_reg <= 2'b10;
        else // one shift to right
            push_result_reg <= 2'(push_result_reg >> 1);
    end

    assign ready_o = push_result_reg[0];

    always_comb begin
        if (mlkem)
            res_o = sub_n ? (carry0_reg ^ carry1)? {{(REG_SIZE-MLKEM_REG_SIZE){1'b0}}, r1[MLKEM_REG_SIZE-1:0]} : {{(REG_SIZE-MLKEM_REG_SIZE){1'b0}}, r0_reg[MLKEM_REG_SIZE-1:0]} : (carry0_reg) ? {{(REG_SIZE-MLKEM_REG_SIZE){1'b0}}, r0_reg[MLKEM_REG_SIZE-1:0]} : {{(REG_SIZE-MLKEM_REG_SIZE){1'b0}}, r1[MLKEM_REG_SIZE-1:0]};
        else
            res_o = sub_n ? (carry0_reg ^ carry1)? r1 : r0_reg : (carry0_reg) ? r0_reg : r1;
    end
    
endmodule
