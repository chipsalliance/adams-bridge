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
// ntt_mlkem_masked_gs_butterfly.sv
// --------
// Only performs gs (INTT) mode of operation. All blocks are masked
// Latency = 7+8 = 15 clks

module ntt_mlkem_masked_gs_butterfly
    import abr_params_pkg::*;
    import ntt_defines_pkg::*;
    #(
        parameter WIDTH = 24
    )
    (
        input wire clk,
        input wire reset_n,
        input wire zeroize,

        input wire [1:0][WIDTH-1:0] opu_i,
        input wire [1:0][WIDTH-1:0] opv_i,
        input wire [1:0][WIDTH-1:0] opw_i,
        input wire [4:0][13:0] rnd_i,

        output logic [1:0][WIDTH-1:0] u_o,
        output logic [1:0][WIDTH-1:0] v_o
    );

    logic [MLKEM_MASKED_ADD_SUB_LATENCY-1:0][1:0][WIDTH-1:0] w_reg;
    logic [1:0][WIDTH-1:0] add_res, add_res_reg ;
    logic [1:0][WIDTH-1:0] sub_res ;
    logic [1:0][WIDTH-1:0] mul_res ;

    logic [1:0] add_res_unpacked [WIDTH-1:0];
    logic [1:0] add_res_unpacked_reg [WIDTH-1:0];

    logic [1:0][WIDTH-1:0] u_o_reg;
    logic [1:0][WIDTH-1:0] v_o_reg;

    //MLKEM: 7 clks
    ntt_mlkem_masked_BFU_add_sub #(
        .WIDTH(WIDTH)
    ) add_inst_0 (
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .sub(1'b0),
        .u(opu_i),
        .v(opv_i),
        .rnd(rnd_i[3:0]),
        .rnd_24bit({rnd_i[0][9:0], rnd_i[4]}),
        .res(add_res)
    );

    //Convert to unpacked
    always_comb begin
        for (int i = 0; i < WIDTH; i++) begin
            add_res_unpacked[i][0] = add_res[0][i];
            add_res_unpacked[i][1] = add_res[1][i];
        end
    end

    abr_delay_masked_shares #(
        .WIDTH(WIDTH),
        .N(MLKEM_MASKED_MULT_LATENCY-1) //Inputs to BF multiplier are internal to this block. There's no input flop in the path, so latency is 1 clk less than the mult latency defined in the pkg
    ) add_res_delay_inst (
        .clk(clk),
        .rst_n(reset_n),
        .zeroize(zeroize),
        .input_reg(add_res_unpacked),
        .delayed_reg(add_res_unpacked_reg)
    );

    //Convert to packed
    always_comb begin
        for (int i = 0; i < WIDTH; i++) begin
            add_res_reg[0][i] = add_res_unpacked_reg[i][0];
            add_res_reg[1][i] = add_res_unpacked_reg[i][1];
        end
    end

    //MLKEM: 7 clks
    ntt_mlkem_masked_BFU_add_sub #(
        .WIDTH(WIDTH)
    ) sub_inst_0 (
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .sub(1'b1),
        .u(opu_i),
        .v(opv_i),
        .rnd(rnd_i[4:1]), //Different rand order
        .rnd_24bit({rnd_i[1][9:0], rnd_i[0]}),
        .res(sub_res) //u-v
    );

    //w delay flops
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            for (int i = 0; i < MLKEM_MASKED_ADD_SUB_LATENCY; i++) begin
                w_reg[i] <= 'h0;
            end
        end
        else if (zeroize) begin
            for (int i = 0; i < MLKEM_MASKED_ADD_SUB_LATENCY; i++) begin
                w_reg[i] <= 'h0;
            end
        end
        else begin
            w_reg <= {opw_i, w_reg[MLKEM_MASKED_ADD_SUB_LATENCY-1:1]};
        end
    end

    //MLKEM: 8 clks
    ntt_mlkem_masked_BFU_mult #(
        .WIDTH(WIDTH)
    ) mult_inst_0 (
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .u(sub_res),
        .v(w_reg[0]),
        .rnd({rnd_i[0], rnd_i[1], rnd_i[2], rnd_i[3], rnd_i[4]}),
        .rnd_24bit({rnd_i[4][9:0], rnd_i[0]}),
        .res(mul_res)
    );

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            u_o_reg <= 'h0;
        end
        else if (zeroize) begin
            u_o_reg <= 'h0;
        end
        else begin
            u_o_reg <= add_res_reg;
        end
    end

    always_comb begin
        u_o = u_o_reg;
        v_o = mul_res;
    end 

endmodule
