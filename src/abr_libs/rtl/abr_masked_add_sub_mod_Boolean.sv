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
// abr_masked_add_sub_mod_Boolean.sv
// --------
// modular addtion/subtraction module to compute opa+-opb % prime
// but this module performs this operation with masking method
//
//======================================================================

module abr_masked_add_sub_mod_Boolean #(
    parameter WIDTH      = 23,
    parameter PRIME = 23'd8380417
    )
    (
    // Clock and reset.
    input wire           clk,
    input wire           rst_n,
    input wire           zeroize,
    input logic [3*WIDTH-1:0] rnd,

    input  wire        sub_i,
    input  wire  [1:0] opa_i_masked [WIDTH-1:0],
    input  wire  [1:0] opb_i_masked [WIDTH-1:0],
    output logic [1:0] res_o_masked [WIDTH-1:0]
);


    // The rest of your variables
    logic  [1:0] opa_i_masked_padded [WIDTH:0];
    logic  [1:0] opb_i_masked_padded [WIDTH:0];
    logic  [1:0] opa_2_masked_padded [WIDTH:0];
    logic  [1:0] prime [WIDTH:0];
    logic  [1:0] r0_c0 [WIDTH:0];
    logic  [1:0] r1_c1 [WIDTH:0];
    logic  [1:0] r0_c0_delayed [WIDTH:0];

    // Reconstruct unmasked inputs and prepare padded masked operands
    always_comb begin
        for (int i = 0; i < WIDTH; i = i + 1) begin
            // Combine the masked shares to get unmasked values
            opa_i_masked_padded[i]  = opa_i_masked[i];
            // Prepare padded masked operands
            if (sub_i) begin
                opb_i_masked_padded[i][0]   = opb_i_masked[i][0];
                opb_i_masked_padded[i][1]   = ~opb_i_masked[i][1];
                prime[i]                    = {1'b0, PRIME[i]};
            end
            else begin
                opb_i_masked_padded[i]      = opb_i_masked[i];
                prime[i]                    = {1'b0, ~PRIME[i]};
            end

        end
        // Padded bits
        opa_i_masked_padded[WIDTH] = 2'b00;
        opb_i_masked_padded[WIDTH] = 2'b00;
        prime[WIDTH] = 2'b00;
    end

    // Assign opa_2_masked_padded after r0_c0 is available
    always_comb begin
        for (int i = 0; i < WIDTH; i = i + 1) begin
            opa_2_masked_padded[i] = r0_c0[i];
        end
        opa_2_masked_padded[WIDTH] = 2'b00;
    end

    // Instantiate the masked subtractor
    abr_masked_N_bit_Boolean_sub #(
        .WIDTH(WIDTH+1)
    ) r0_sub_or_add (
        .clk(clk),
        .rst_n(rst_n),
        .zeroize(zeroize),
        .sub_i(sub_i),
        .x(opa_i_masked_padded),
        .y(opb_i_masked_padded),
        .rnd(rnd[WIDTH:0]),
        .s(r0_c0)
    );


    // Delay the masked outputs
    abr_delay_masked_shares #(
        .WIDTH(WIDTH+1),
        .N(WIDTH+3) // Delays 26 cycles
    ) delay_r0_c0 (
        .clk(clk),
        .rst_n(rst_n),
        .zeroize(zeroize),
        .input_reg(r0_c0),
        .delayed_reg(r0_c0_delayed)
    );


    // Instantiate the masked adder
    abr_masked_N_bit_Boolean_sub #(
        .WIDTH(WIDTH+1)
    ) r1_sub_or_add (
        .clk(clk),
        .rst_n(rst_n),
        .zeroize(zeroize),
        .sub_i(~sub_i),
        .x(opa_2_masked_padded),
        .y(prime),
        .rnd(rnd[WIDTH:0]),
        .s(r1_c1)
    );

    // Instantiate the masked MUX
    abr_masked_MUX #(
        .WIDTH(WIDTH)
    ) r0_MUX_r0 (
        .clk(clk),
        .rst_n(rst_n),
        .zeroize(zeroize),
        .sub_i(sub_i),
        .carry0(r0_c0_delayed[WIDTH]),
        .carry1(r1_c1[WIDTH]),
        .r0(r0_c0_delayed[WIDTH-1:0]),
        .r1(r1_c1[WIDTH-1:0]),
        .rnd_xor(rnd[WIDTH*2-1:WIDTH]),
        .rnd_and(rnd[WIDTH*3-1:2*WIDTH]),
        .res_o_masked(res_o_masked)
    );

endmodule: abr_masked_add_sub_mod_Boolean