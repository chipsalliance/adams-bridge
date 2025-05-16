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
//======================================================================
//
// decompose_mod_2gamma2.sv
// ------------
// computes r0 mod (2gamma2). Input is 23 bit and produces r0 mod 2gamma2 is 19 bits


module decompose_mod_2gamma2
    import abr_params_pkg::*;
    #(
        parameter REG_SIZE = abr_params_pkg::REG_SIZE-1,
        localparam MLDSA_2GAMMA2_SIZE = $clog2(2*MLDSA_GAMMA2)
    )
    (
        // Clock and reset.
    input wire           clk,
    input wire           reset_n,
    input wire           zeroize,

    // DATA PORT
    input  wire                 add_en_i,
    input  wire  [REG_SIZE-1:0] opa_i,
    output logic [MLDSA_2GAMMA2_SIZE-1:0]         res_o,
    output logic                ready_o
);
  
    logic [12:0] opa0;
    logic [MLDSA_2GAMMA2_SIZE-1:0] opb0;
    logic [MLDSA_2GAMMA2_SIZE-1:0] opb1;
    logic [MLDSA_2GAMMA2_SIZE-1:0] r0;
    logic [MLDSA_2GAMMA2_SIZE-1:0] r1;
    logic carry0; 

    logic [MLDSA_2GAMMA2_SIZE-1:0] r0_reg;
    logic carry0_reg;

    logic carry1;

    assign opa0 = 13'(opa_i[22:19] << 9);
    assign opb0 = opa_i[MLDSA_2GAMMA2_SIZE-1:0];

    abr_adder #(
        .RADIX(MLDSA_2GAMMA2_SIZE)
        ) 
        adder_inst_0(
        .a_i({6'h0,opa0}),
        .b_i(opb0),
        .cin_i(1'b0),
        .s_o(r0),
        .cout_o(carry0)
    );

    abr_adder #(
        .RADIX(MLDSA_2GAMMA2_SIZE)
        ) 
        adder_inst_1(
        .a_i(r0_reg),
        .b_i(opb1),
        .cin_i(1'b1),
        .s_o(r1),
        .cout_o(carry1)
    );


    always_ff @(posedge clk or negedge reset_n) 
    begin
        if(!reset_n) begin
            r0_reg <= '0;
            carry0_reg <= '0;
            opb1 <= '0;
        end
        else if (zeroize) begin
            r0_reg <= '0;
            carry0_reg <= '0;
            opb1 <= '0;
        end
        else if (add_en_i) begin 
            r0_reg <= r0;
            carry0_reg <= carry0;
            opb1 <= ~MLDSA_2GAMMA2_SIZE'(2*MLDSA_GAMMA2);
        end
    end

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) ready_o <= 'b0;
        else if (zeroize) ready_o <= 'b0;
        else ready_o <= add_en_i;
    end

    assign res_o = (carry0_reg ^ carry1) ? r1 : r0_reg;
    

endmodule