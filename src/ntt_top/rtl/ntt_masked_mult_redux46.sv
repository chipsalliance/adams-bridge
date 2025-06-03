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
// ntt_masked_mult_redux46
// Performs masked multiplication reduction for MLDSA
// It has 157 Cycle Latency
//======================================================================

module ntt_masked_mult_redux46
    import ntt_defines_pkg::*;
    import abr_params_pkg::*;
#(
    parameter WIDTH = 46
)
(
    input wire clk,
    input wire rst_n,
    input wire zeroize,
    input wire [10:0] rnd0_11,
    input wire [10:0] rnd1_11,
    input wire [10:0] rnd2_11,
    input wire [11:0] rnd0_12,
    input wire [3:0] rnd0_4,
    input wire [13:0] rnd0_14,
    input wire [3*(WIDTH/2)-1:0] rnd_3WIDTH,
    input wire [1:0] x [WIDTH-1:0],
    output logic [1:0] y [WIDTH/2-1:0]
);

    // Intermediate wires for the sliced values
    logic [4:0] cnt;
    logic [1:0] z_45_23 [22:0];
    logic [1:0] z_45_23_delayed [22:0];
    logic [1:0] z_45_33 [13:0];
    logic [1:0] z_45_33_delayed [13:0];
    logic [1:0] z_45_43 [3:0];
    logic [1:0] z_45_43_delayed [3:0];
    logic [1:0] z_45_43_padded_8 [10:0];
    logic [1:0] z_12_0 [12:0];
    logic [1:0] z_12_0_delayed [12:0];
    logic [1:0] z_22_13 [10:0];
    logic [1:0] z_32_23 [10:0];
    logic [1:0] z_42_33 [10:0];

    logic [1:0] tmp [10:0];
    logic [1:0] tmp_padded [11:0];
    logic [1:0] tmp0 [10:0];
    logic [1:0] tmp0_padded [11:0];
    logic [1:0] c0_11 [11:0];
    logic [1:0] c11_10 [1:0];
    logic [1:0] c11_10_padded_9 [10:0];
    logic [1:0] c11_10_padded_2 [3:0];
    logic [1:0] c9_0 [9:0];
    logic [1:0] c9_0_padded [10:0];

    logic [1:0] d10_0 [10:0];
    logic [1:0] d22_0 [22:0];
    logic [1:0] d22_0_delayed [22:0];

    
    logic [1:0] f3_0 [3:0];
    logic [1:0] f3_0_padded_10 [13:0];
    logic [1:0] f13_0 [13:0];
    logic [1:0] f13_0_padded_9 [22:0];

    
    logic [1:0] e22_0 [22:0];

    // Use always_comb block to split x into various z arrays using for loops
    always_comb begin
        // Counter for z_45_23
        cnt = 0;
        for (int i = 23; i <= 45; i = i + 1) begin
            z_45_23[cnt] = x[i];
            cnt = cnt + 1;
        end

        // Counter for z_45_33
        cnt = 0;
        for (int i = 33; i <= 45; i = i + 1) begin
            z_45_33[cnt[3:0]] = x[i];
            cnt = cnt + 1;
        end
        z_45_33[13] = 2'b00;

        // Counter for z_45_43
        cnt = 0;
        for (int i = 43; i <= 45; i = i + 1) begin
            z_45_43[cnt[1:0]] = x[i];
            z_45_43_padded_8[cnt[3:0]] = x[i];
            cnt = cnt + 1;
        end
        z_45_43[3] = 2'b00;
        z_45_43_padded_8[3] = 2'b00;
        for (int i = 0; i < 7; i = i + 1) //i < 8
            z_45_43_padded_8[i+4] = 2'b00;

        // Counter for z_12_0
        cnt = 0;
        for (int i = 0; i <= 12; i = i + 1) begin
            z_12_0[cnt[3:0]] = x[i];
            cnt = cnt + 1;
        end

        // Counter for z_22_13
        cnt = 0;
        for (int i = 13; i <= 22; i = i + 1) begin
            z_22_13[cnt[3:0]] = x[i];
            cnt = cnt + 1;
        end
        z_22_13[10] = 2'b00;

        // Counter for z_32_23
        cnt = 0;
        for (int i = 23; i <= 32; i = i + 1) begin
            z_32_23[cnt[3:0]] = x[i];
            cnt = cnt + 1;
        end
        z_32_23[10] = 2'b00;

        // Counter for z_42_33
        cnt = 0;
        for (int i = 33; i <= 42; i = i + 1) begin
            z_42_33[cnt[3:0]] = x[i];
            cnt = cnt + 1;
        end
        z_42_33[10] = 2'b00;

        cnt = 0;
        for (int i = 10; i <= 11; i = i + 1) begin
            c11_10[cnt[0]] = c0_11[i];
            c11_10_padded_9[cnt[3:0]] = c0_11[i];
            c11_10_padded_2[cnt[1:0]] = c0_11[i];
            cnt = cnt + 1;
        end
        c11_10_padded_2[2] = 2'b00;
        c11_10_padded_2[3] = 2'b00;
        for (int i = 0; i < 9; i = i + 1)
            c11_10_padded_9[i+2] = 2'b00;

        cnt = 0;
        for (int i = 0; i <= 9; i = i + 1) begin
            c9_0[cnt[3:0]] = c0_11[i];
            c9_0_padded[cnt[3:0]] = c0_11[i];
            cnt = cnt + 1;
        end
        c9_0_padded[10] = 2'b00;

        
        for (int i = 0; i < 4; i = i + 1)
            f3_0_padded_10[i] = f3_0[i];
        for (int i = 0; i < 10; i = i + 1)
            f3_0_padded_10[i+4] = 2'b00;

        for (int i = 0; i < 14; i = i + 1)
            f13_0_padded_9[i] = f13_0[i];
        for (int i = 0; i < 9; i = i + 1)
            f13_0_padded_9[i+14] = 2'b00;

        for (int i = 0; i < 11; i = i + 1) begin
            tmp_padded[i] = tmp[i];
            tmp0_padded[i] = tmp0[i];
        end
        tmp_padded[11] = 2'b00;
        tmp0_padded[11] = 2'b00;
    end

    // Cycle 0 to 12
    abr_masked_N_bit_Boolean_adder #(
        .WIDTH(11)
    ) bool_adder_22_13_and_32_23 (
        .clk(clk),
        .rst_n(rst_n),
        .zeroize(zeroize),
        .x(z_22_13),
        .y(z_32_23),
        .rnd(rnd0_11),
        .s(tmp)
    );

    // Cycle 0 to 12
    abr_masked_N_bit_Boolean_adder #(
        .WIDTH(11)
    ) bool_adder_45_43_and_42_33 (
        .clk(clk),
        .rst_n(rst_n),
        .zeroize(zeroize),
        .x(z_42_33),
        .y(z_45_43_padded_8),
        .rnd(rnd1_11),
        .s(tmp0)
    );

    // Cycle 12+1 to 26
    abr_masked_N_bit_Boolean_adder #(
        .WIDTH(12)
    ) bool_adder_tmp_and_tmp0 (
        .clk(clk),
        .rst_n(rst_n),
        .zeroize(zeroize),
        .x(tmp_padded),
        .y(tmp0_padded),
        .rnd(rnd0_12),
        .s(c0_11)
    );


    // Cycle 26+1 to 39
    abr_masked_N_bit_Boolean_adder #(
        .WIDTH(11)
    ) bool_adder_c0_9_and_c11_10 (
        .clk(clk),
        .rst_n(rst_n),
        .zeroize(zeroize),
        .x(c11_10_padded_9),
        .y(c9_0_padded),
        .rnd(rnd2_11),
        .s(d10_0)
    );

    // Cycle 0 to 40
    abr_delay_masked_shares #(
        .WIDTH(13),
        .N(40) // Delays 36 cycles
    ) delay_z12_0 (
        .clk(clk),
        .rst_n(rst_n),
        .zeroize(zeroize),
        .input_reg(z_12_0),
        .delayed_reg(z_12_0_delayed)
    );

    //28 cycles
    ntt_masked_special_adder  add_with_conc_d10_and_z12(
        .clk(clk),
        .rst_n(rst_n),
        .zeroize(zeroize),
        .rnd(rnd_3WIDTH),
        .d10_0(d10_0),
        .z_12_0(z_12_0_delayed),
        .res_o_masked(d22_0)
    );

    // Cycle 0 to 26+1
    abr_delay_masked_shares #(
        .WIDTH(4),
        .N(27) // Delays 36 cycles
    ) delay_z_45_43 (
        .clk(clk),
        .rst_n(rst_n),
        .zeroize(zeroize),
        .input_reg(z_45_43),
        .delayed_reg(z_45_43_delayed)
    );

    // Cycle 26 to 33
    abr_masked_N_bit_Boolean_adder #(
        .WIDTH(4)
    ) bool_adder_c11_10_and_z_45_43 (
        .clk(clk),
        .rst_n(rst_n),
        .zeroize(zeroize),
        .x(c11_10_padded_2),
        .y(z_45_43_delayed),
        .rnd(rnd0_4),
        .s(f3_0)
    );


    // Cycle 0 to 33
    abr_delay_masked_shares #(
        .WIDTH(14),
        .N(33) // Delays 36 cycles
    ) delay_z_45_33 (
        .clk(clk),
        .rst_n(rst_n),
        .zeroize(zeroize),
        .input_reg(z_45_33),
        .delayed_reg(z_45_33_delayed)
    );

    // Cycle 33 to 48
    abr_masked_N_bit_Boolean_adder #(
        .WIDTH(14)
    ) bool_adder_c11_10_and_z_45_33 (
        .clk(clk),
        .rst_n(rst_n),
        .zeroize(zeroize),
        .x(f3_0_padded_10),
        .y(z_45_33_delayed),
        .rnd(rnd0_14),
        .s(f13_0)
    );

    // Cycle 0 to 48+1
    abr_delay_masked_shares #(
        .WIDTH(23),
        .N(49) // Delays 36 cycles
    ) delay_z_45_23 (
        .clk(clk),
        .rst_n(rst_n),
        .zeroize(zeroize),
        .input_reg(z_45_23),
        .delayed_reg(z_45_23_delayed)
    );
    
    //54 cycles
    abr_masked_add_sub_mod_Boolean mod_adder_z_45_23_and_f13_0 (
        .clk(clk),
        .rst_n(rst_n),
        .zeroize(zeroize),
        .rnd(rnd_3WIDTH),
        .sub_i       (1'b0),
        .opa_i_masked(z_45_23_delayed),
        .opb_i_masked(f13_0_padded_9),
        .res_o_masked(e22_0)
    );

    // Cycle 39 to 94
    abr_delay_masked_shares #(
        .WIDTH(23),
        .N(35) // Delays 34 cycles
    ) delay_d_22_0 (
        .clk(clk),
        .rst_n(rst_n),
        .zeroize(zeroize),
        .input_reg(d22_0),
        .delayed_reg(d22_0_delayed)
    );

    //54 cycles
    abr_masked_add_sub_mod_Boolean  mod_adder_d22_0_and_e22_0 (
        .clk(clk),
        .rst_n(rst_n),
        .zeroize(zeroize),
        .rnd(rnd_3WIDTH),
        .sub_i       (1'b1),
        .opa_i_masked(d22_0_delayed),
        .opb_i_masked(e22_0),
        .res_o_masked(y)
    );


endmodule: ntt_masked_mult_redux46




// module abr_masked_add_sub_mod_Boolean #(
//     parameter WIDTH      = 23,
//     parameter PRIME = 23'd8380417
//     )
//     (
//     // Clock and reset.
//     input wire           clk,
//     input wire           rst_n,
//     input wire           zeroize,
//     input logic [3*WIDTH-1:0] rnd,

//     input  wire        sub_i,
//     input  wire  [1:0] opa_i_masked [WIDTH-1:0],
//     input  wire  [1:0] opb_i_masked [WIDTH-1:0],
//     output logic [1:0] res_o_masked [WIDTH-1:0]
// );


//     // The rest of your variables
//     logic  [1:0] opa_i_masked_padded [WIDTH:0];
//     logic  [1:0] opb_i_masked_padded [WIDTH:0];
//     logic  [1:0] opa_2_masked_padded [WIDTH:0];
//     logic  [1:0] prime [WIDTH:0];
//     logic  [1:0] r0_c0 [WIDTH:0];
//     logic  [1:0] r1_c1 [WIDTH:0];
//     logic  [1:0] r0_c0_delayed [WIDTH:0];

//     // Reconstruct unmasked inputs and prepare padded masked operands
//     always_comb begin
//         for (int i = 0; i < WIDTH; i = i + 1) begin
//             // Combine the masked shares to get unmasked values
//             opa_i_masked_padded[i]  = opa_i_masked[i];
//             // Prepare padded masked operands
//             if (sub_i) begin
//                 opb_i_masked_padded[i][0]   = opb_i_masked[i][0];
//                 opb_i_masked_padded[i][1]   = ~opb_i_masked[i][1];
//                 prime[i]                    = {1'b0, PRIME[i]};
//             end
//             else begin
//                 opb_i_masked_padded[i]      = opb_i_masked[i];
//                 prime[i]                    = {1'b0, ~PRIME[i]};
//             end

//         end
//         // Padded bits
//         opa_i_masked_padded[WIDTH] = 2'b00;
//         opb_i_masked_padded[WIDTH] = 2'b00;
//         prime[WIDTH] = 2'b00;
//     end

//     // Assign opa_2_masked_padded after r0_c0 is available
//     always_comb begin
//         for (int i = 0; i < WIDTH; i = i + 1) begin
//             opa_2_masked_padded[i] = r0_c0[i];
//         end
//         opa_2_masked_padded[WIDTH] = 2'b00;
//     end

//     // Instantiate the masked subtractor
//     abr_masked_N_bit_Boolean_sub #(
//         .WIDTH(WIDTH+1)
//     ) r0_sub_or_add (
//         .clk(clk),
//         .rst_n(rst_n),
//         .zeroize(zeroize),
//         .sub_i(sub_i),
//         .x(opa_i_masked_padded),
//         .y(opb_i_masked_padded),
//         .rnd(rnd[WIDTH:0]),
//         .s(r0_c0)
//     );


//     // Delay the masked outputs
//     abr_delay_masked_shares #(
//         .WIDTH(WIDTH+1),
//         .N(WIDTH+3) // Delays 26 cycles
//     ) delay_r0_c0 (
//         .clk(clk),
//         .rst_n(rst_n),
//         .zeroize(zeroize),
//         .input_reg(r0_c0),
//         .delayed_reg(r0_c0_delayed)
//     );


//     // Instantiate the masked adder
//     abr_masked_N_bit_Boolean_sub #(
//         .WIDTH(WIDTH+1)
//     ) r1_sub_or_add (
//         .clk(clk),
//         .rst_n(rst_n),
//         .zeroize(zeroize),
//         .sub_i(~sub_i),
//         .x(opa_2_masked_padded),
//         .y(prime),
//         .rnd(rnd[WIDTH:0]),
//         .s(r1_c1)
//     );

//     // Instantiate the masked MUX
//     abr_masked_MUX #(
//         .WIDTH(WIDTH)
//     ) r0_MUX_r0 (
//         .clk(clk),
//         .rst_n(rst_n),
//         .zeroize(zeroize),
//         .sub_i(sub_i),
//         .carry0(r0_c0_delayed[WIDTH]),
//         .carry1(r1_c1[WIDTH]),
//         .r0(r0_c0_delayed[WIDTH-1:0]),
//         .r1(r1_c1[WIDTH-1:0]),
//         .rnd_xor(rnd[WIDTH*2-1:WIDTH]),
//         .rnd_and(rnd[WIDTH*3-1:2*WIDTH]),
//         .res_o_masked(res_o_masked)
//     );

// endmodule


