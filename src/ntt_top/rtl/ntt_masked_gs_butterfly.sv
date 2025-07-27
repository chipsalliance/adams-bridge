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
// ntt_masked_gs_butterfly.sv
// --------
// Only performs gs (INTT) mode of operation. All blocks are masked
// Latency = 264 clks

module ntt_masked_gs_butterfly
    import abr_params_pkg::*;
    import ntt_defines_pkg::*;
    #(
        parameter WIDTH = 46,
        parameter MASKED_ADD_SUB_LATENCY = 53 //Latency of add/sub block
    )
    (
        input wire clk,
        input wire reset_n,
        input wire zeroize,

        input wire [1:0][WIDTH-1:0] opu_i,
        input wire [1:0][WIDTH-1:0] opv_i,
        input wire [1:0][WIDTH-1:0] opw_i,
        input wire [4:0][WIDTH-1:0] rnd_i,
        input mode_t mode,
        input wire accumulate,

        output logic [1:0] u_o [WIDTH-1:0],
        output logic [1:0] v_o [WIDTH-1:0]
    );

    logic [MASKED_ADD_SUB_LATENCY-1:0][1:0][WIDTH-1:0] w_reg;
    logic [1:0] add_res [WIDTH-1:0];
    logic [1:0] sub_res [WIDTH-1:0];
    logic [1:0] mul_res [WIDTH-1:0];
    logic [1:0][WIDTH-1:0] sub_res_packed;

    logic [1:0] add_res_reg [WIDTH-1:0];
    logic [WIDTH-1:0] add_res_reg0, add_res_reg1;

    logic [WIDTH-1:0] add_res0, add_res1, mul_res0, mul_res1, mul_res0_reg, mul_res1_reg, u_o_0, u_o_1, v_o_0, v_o_1;
    logic pwm_mode;
    logic [1:0] u_o_reg [WIDTH-1:0];
    logic [1:0] v_o_reg [WIDTH-1:0];

    assign pwm_mode = (mode == pwm);

    //MLDSA: 53 clks
    //MLKEM: 21 clks
    ntt_masked_BFU_add_sub #(
        .WIDTH(WIDTH)
    ) add_inst_0 (
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .sub(1'b0),
        .u((pwm_mode & accumulate) ? {mul_res1_reg, mul_res0_reg} : opu_i),
        .v((pwm_mode & accumulate) ? opw_i : opv_i),
        .rnd0(rnd_i[0]),
        .rnd1(rnd_i[1]),
        .rnd2(rnd_i[2]),
        .rnd3(rnd_i[3]),
        .res(add_res) //pwm_mode & accumulate ? uv+w : u+v
    );

    abr_delay_masked_shares #(
        .WIDTH(WIDTH),
        .N(MASKED_PWM_LATENCY-1) //Inputs to BF multiplier are internal to this block. There's no input flop in the path, so latency is 1 clk less than the mult latency defined in the pkg
    ) add_res_delay_inst (
        .clk(clk),
        .rst_n(reset_n),
        .zeroize(zeroize),
        .input_reg(add_res),
        .delayed_reg(add_res_reg)
    );

    //MLDSA: 53 clks
    //MLKEM: 21 clks
    ntt_masked_BFU_add_sub #(
        .WIDTH(WIDTH)
    ) sub_inst_0 (
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .sub(1'b1),
        .u(opu_i),
        .v(opv_i),
        .rnd0(rnd_i[1]), //Different rand order
        .rnd1(rnd_i[2]),
        .rnd2(rnd_i[3]),
        .rnd3(rnd_i[0]),
        .res(sub_res) //u-v
    );

    always_comb begin
        for (int i = 0; i < WIDTH; i++) begin
            add_res0[i] = add_res[i][0];
            add_res1[i] = add_res[i][1];
            sub_res_packed[0][i] = sub_res[i][0];
            sub_res_packed[1][i] = sub_res[i][1];

            add_res_reg0[i] = add_res_reg[i][0];
            add_res_reg1[i] = add_res_reg[i][1];
        end
    end

    //w delay flops
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            for (int i = 0; i < MASKED_ADD_SUB_LATENCY; i++) begin
                w_reg[i] <= 'h0;
            end
        end
        else if (zeroize) begin
            for (int i = 0; i < MASKED_ADD_SUB_LATENCY; i++) begin
                w_reg[i] <= 'h0;
            end
        end
        else begin
            w_reg <= {opw_i, w_reg[MASKED_ADD_SUB_LATENCY-1:1]};
        end
    end

    //MLDSA: 210 clks
    ntt_masked_BFU_mult #(
        .WIDTH(WIDTH)
    ) mult_inst_0 (
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .u(pwm_mode ? opu_i : sub_res_packed),
        .v(pwm_mode ? opv_i : w_reg[0]),
        .rnd0(rnd_i[2]),
        .rnd1(rnd_i[3]),
        .rnd2(rnd_i[0]),
        .rnd3(rnd_i[1]),
        .rnd4(WIDTH'(rnd_i[2]+rnd_i[3])),
        .res(mul_res)
    );

    always_comb begin
        for (int i = 0; i < WIDTH; i++) begin
            mul_res0[i] = mul_res[i][0];
            mul_res1[i] = mul_res[i][1];
        end
    end

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            for (int i = 0; i < WIDTH; i++) begin
                u_o_reg[i] <= 2'b0;
                v_o_reg[i] <= 2'b0;
                mul_res0_reg[i] <= '0;
                mul_res1_reg[i] <= '0;
            end
        end
        else if (zeroize) begin
            for (int i = 0; i < WIDTH; i++) begin
                u_o_reg[i] <= 2'b0;
                v_o_reg[i] <= 2'b0;
                mul_res0_reg[i] <= '0;
                mul_res1_reg[i] <= '0;
            end
        end
        else begin
            for (int i =0; i < WIDTH; i++) begin
                mul_res0_reg[i] <= mul_res0[i];
                mul_res1_reg[i] <= mul_res1[i];
            end
            u_o_reg <= add_res_reg;
            v_o_reg <= mul_res;
        end
    end

    always_comb begin
        for (int i = 0; i < WIDTH; i++) begin
            u_o[i]   = pwm_mode ? accumulate ? add_res[i] : mul_res[i] : u_o_reg[i];
            v_o[i]   = pwm_mode ? 2'b0 : v_o_reg[i];

            u_o_0[i] = u_o[i][0];
            u_o_1[i] = u_o[i][1];

            v_o_0[i] = v_o[i][0];
            v_o_1[i] = v_o[i][1];
        end
    end 

endmodule
