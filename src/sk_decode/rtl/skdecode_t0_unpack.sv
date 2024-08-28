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
// skdecode_t0_unpack.sv
// ----------------------------
// Unpacks t0 from sk by calculating the following equation:
// coeff = (2**(d-1)) - data[d-1:0] where d is a Mldsa param = 13
// The result of this modular subtraction is a 24-bit value (2**12-a mod q)
// that is stored in memory as coefficients for further processing

module skdecode_t0_unpack
    #(
        parameter REG_SIZE = 23,
        parameter MLDSA_Q = 8380417,
        parameter MLDSA_D = 13
    )
    (
        input wire clk,
        input wire reset_n,
        input wire zeroize,

        input wire enable,
        input wire sub_i,
        input wire [MLDSA_D-1:0] data_i,
        output logic [REG_SIZE:0] data_o, //TODO: clean up. At top level, data_o is 24-bits, so add 1 more bit here and assign 0
        output logic valid_o
    );

    logic [REG_SIZE-1:0] opa0;
    logic [REG_SIZE-1:0] opb0;
    logic [REG_SIZE-1:0] r0;
    logic [REG_SIZE-1:0] opb1;
    logic [REG_SIZE-1:0] r1;
    logic [REG_SIZE-1:0] r0_reg;
    
    logic carry0;
    logic carry1;
    logic carry0_reg;
    logic sub_n;

    assign opa0 = (1 << (MLDSA_D-1));
    assign opb0 = sub_i ? REG_SIZE'(~data_i) : REG_SIZE'(data_i);

    abr_adder #(
        .RADIX(REG_SIZE)
        ) 
        adder_inst_0(
        .a_i(opa0),
        .b_i(opb0),
        .cin_i(sub_i),
        .s_o(r0),
        .cout_o(carry0)
    );

    abr_adder #(
        .RADIX(REG_SIZE)
        ) 
        adder_inst_1(
        .a_i(r0_reg),
        .b_i(opb1),
        .cin_i(sub_n),
        .s_o(r1),
        .cout_o(carry1)
    );

    always_ff @(posedge clk or negedge reset_n) 
    begin
        if(!reset_n) begin
            r0_reg      <= '0;
            carry0_reg  <= '0;
            opb1        <= '0;
            sub_n       <= '0;
        end
        else if (zeroize) begin
            r0_reg      <= '0;
            carry0_reg  <= '0;
            opb1        <= '0;
            sub_n       <= '0;
        end
        else if (enable) begin 
            r0_reg      <= r0;
            carry0_reg  <= carry0;
            opb1        <= sub_i ? MLDSA_Q : ~MLDSA_Q;
            sub_n       <= !sub_i;
        end
    end

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) 
            valid_o <= 'b0;
        else if (zeroize) 
            valid_o <= 'b0;
        else 
            valid_o <= enable;
    end

    assign data_o = sub_n ? (carry0_reg ^ carry1) ? (REG_SIZE+1)'(r1) : (REG_SIZE+1)'(r0_reg)
                          : (carry0_reg) ? (REG_SIZE+1)'(r0_reg) : (REG_SIZE+1)'(r1);

endmodule