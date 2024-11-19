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
// abr_masked_MUX
// Selects either r0 or r1 based on the carry bit input.
// This selection mechanism is masked and performed without combining
// the masked shares.
//======================================================================

module abr_masked_MUX #(
    parameter WIDTH = 23
)(
    input wire                  clk,         // Clock signal
    input wire                  rst_n,       // Active low reset signal
    input wire                  zeroize,     // Zeroize signal
    input wire                  sub_i,       // Subtract signal (unmasked)
    input wire  [1:0]           carry0,      // Masked carry0 input
    input wire  [1:0]           carry1,      // Masked carry1 input
    input wire  [1:0]           r0 [WIDTH-1:0], // Masked input r0
    input wire  [1:0]           r1 [WIDTH-1:0], // Masked input r1
    input wire  [WIDTH-1:0]     rnd_xor,     // Randomness for XOR masking
    input wire  [WIDTH-1:0]     rnd_and,     // Randomness for AND gates
    output logic [1:0]          res_o_masked [WIDTH-1:0] // Masked output
);

    // Internal signals
    logic [1:0] s;
    logic [1:0] c0c1;
    // Compute the masked differences x0y0 and x1y1
    logic [1:0] xy [WIDTH-1:0];
    logic [1:0] xyk [WIDTH-1:0];
    logic [1:0] xy_and_s [WIDTH-1:0];
    logic [1:0] r1_k [WIDTH-1:0];
    logic [1:0] r1_delayed [WIDTH-1:0];

    // Compute the masked select bits s0 and s1
    always_comb begin
        if (sub_i) begin
            // When subtracting, select bits are based on carry0
            s = carry0;
            c0c1 = 2'h0; //verilator
        end
        else begin
            // When adding, select bits are based on inverted (carry0 ^ carry1)
            c0c1 = carry0 ^ carry1;
            s[0] = ~c0c1[0];
            s[1] = c0c1[1];
        end
    end
    always_comb begin //verilator
        for (int i = 0; i < WIDTH; i++) begin
            xy[i] = r0[i] ^ r1[i];
            xyk[i][0] = xy[i][0] ^ rnd_xor[i];
            xyk[i][1] = xy[i][1] ^ rnd_xor[i];
            r1_k[i][0] = r1[i][0] ^ rnd_xor[i];
            r1_k[i][1] = r1[i][1] ^ rnd_xor[i];
        end
    end

    // Instantiate masked AND gates (DOM) for each bit
    genvar i_AND;
    generate
        for (i_AND = 0; i_AND < WIDTH; i_AND = i_AND + 1) begin : gen_DOM_AND
            abr_masked_AND and_gate_inst (
                .clk(clk),
                .rst_n(rst_n),
                .zeroize(zeroize),
                .x(xyk[i_AND]),
                .y(s),
                .rnd(rnd_and[i_AND]),
                .c(xy_and_s[i_AND])
            );
        end
    endgenerate

    // Delay r1_k to align with masked AND gate outputs
    abr_delay_masked_shares #(
        .WIDTH(WIDTH),
        .N(1) // Delays 1 cycle
    ) delay_r1_k (
        .clk(clk),
        .rst_n(rst_n),
        .zeroize(zeroize),
        .input_reg(r1_k),
        .delayed_reg(r1_delayed)
    );

    // Compute the final masked result
    // Resharing logic to apply masking
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int i = 0; i < WIDTH; i++) begin
                res_o_masked[i] <= 2'b0;
            end
        end
        else if (zeroize) begin
            for (int i = 0; i < WIDTH; i++) begin
                res_o_masked[i] <= 2'b0;
            end
        end
        else begin
            for (int i = 0; i < WIDTH; i++) begin
                res_o_masked[i] <= xy_and_s[i] ^ r1_delayed[i];
            end
        end
    end

endmodule: abr_masked_MUX