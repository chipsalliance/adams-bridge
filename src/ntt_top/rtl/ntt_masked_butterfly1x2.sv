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
// ntt_masked_butterfly1x2.sv
// --------
// 1. Performs 1st stage of masked INTT operation
// 2. Combines output shares
// 3. Performs div2 on combined outputs (unmasked)
// Total latency = 264 clks

module ntt_masked_butterfly1x2
    import abr_params_pkg::*;
    import ntt_defines_pkg::*;
    #(
        parameter WIDTH = 46,
        parameter HALF_WIDTH = WIDTH/2
    )
    (
        input wire clk,
        input wire reset_n,
        input wire zeroize,
        // input wire enable,
        input masked_bf_uvwi_t uvw_i,
        input [4:0][WIDTH-1:0] rnd_i,
        input mode_t mode,
        input accumulate,
        
        output bf_uvo_t uv_o,
        output pwm_shares_uvo_t bf_pwm_uv_o
    );

    logic [1:0][WIDTH-1:0] u00, v00, w00;
    logic [1:0][WIDTH-1:0] u01, v01, w01;
    logic [1:0] u10_int [WIDTH-1:0];
    logic [1:0] v10_int [WIDTH-1:0];
    logic [1:0] u11_int [WIDTH-1:0];
    logic [1:0] v11_int [WIDTH-1:0];
    logic [1:0][WIDTH-1:0] u10_packed, v10_packed, u11_packed, v11_packed, u10_packed_reg, u11_packed_reg;
    logic [HALF_WIDTH-1:0] u10_combined, v10_combined, u11_combined, v11_combined;
    logic [HALF_WIDTH-1:0] u10_div2, v10_div2, u11_div2, v11_div2;
    logic pwm_mode;

    always_comb begin
        u00 = uvw_i.u00_i;
        v00 = uvw_i.v00_i;
        w00 = uvw_i.w00_i;

        u01 = uvw_i.u01_i;
        v01 = uvw_i.v01_i;
        w01 = uvw_i.w01_i;

        pwm_mode = (mode == pwm);
    end

    //264
    ntt_masked_gs_butterfly #(
        .WIDTH(WIDTH)
    ) masked_bf_inst00 (
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .opu_i(u00),
        .opv_i(v00),
        .opw_i(w00),
        .rnd_i({rnd_i[4], rnd_i[3], rnd_i[2], rnd_i[1], rnd_i[0]}),
        .mode(mode),
        .accumulate(accumulate),
        .u_o(u10_int),
        .v_o(v10_int)
    );

    ntt_masked_gs_butterfly #(
        .WIDTH(WIDTH)
    ) masked_bf_inst01 (
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .opu_i(u01),
        .opv_i(v01),
        .opw_i(w01),
        .rnd_i({rnd_i[0], rnd_i[4], rnd_i[3], rnd_i[2], rnd_i[1]}),
        .mode(mode),
        .accumulate(accumulate),
        .u_o(u11_int),
        .v_o(v11_int)
    );

    always_comb begin
        for (int i = 0; i < WIDTH; i++) begin
            u10_packed[0][i] = u10_int[i][0];
            u10_packed[1][i] = u10_int[i][1];
            u11_packed[0][i] = u11_int[i][0];
            u11_packed[1][i] = u11_int[i][1];
            v10_packed[0][i] = v10_int[i][0];
            v10_packed[1][i] = v10_int[i][1];
            v11_packed[0][i] = v11_int[i][0];
            v11_packed[1][i] = v11_int[i][1];
        end
        u10_combined = pwm_mode ? '0 : HALF_WIDTH'(u10_packed[0] + u10_packed[1]);
        v10_combined = pwm_mode ? '0 : HALF_WIDTH'(v10_packed[0] + v10_packed[1]);
        u11_combined = pwm_mode ? '0 : HALF_WIDTH'(u11_packed[0] + u11_packed[1]);
        v11_combined = pwm_mode ? '0 : HALF_WIDTH'(v11_packed[0] + v11_packed[1]);
    end

    //Perform div2 on combined outputs
    ntt_div2 #(
        .REG_SIZE(HALF_WIDTH),
        .PRIME(abr_params_pkg::MLDSA_Q)
    ) div2_inst0 (
        .op_i(u10_combined),
        .res_o(u10_div2)
    );

    ntt_div2 #(
        .REG_SIZE(HALF_WIDTH),
        .PRIME(abr_params_pkg::MLDSA_Q)
    ) div2_inst1 (
        .op_i(v10_combined),
        .res_o(v10_div2)
    );

    ntt_div2 #(
        .REG_SIZE(HALF_WIDTH),
        .PRIME(abr_params_pkg::MLDSA_Q)
    ) div2_inst2 (
        .op_i(u11_combined),
        .res_o(u11_div2)
    );

    ntt_div2 #(
        .REG_SIZE(HALF_WIDTH),
        .PRIME(abr_params_pkg::MLDSA_Q)
    ) div2_inst3 (
        .op_i(v11_combined),
        .res_o(v11_div2)
    );

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            uv_o <= 'h0;
            u10_packed_reg <= '0;
            u11_packed_reg <= '0;
        end
        else if (zeroize) begin
            uv_o <= 'h0;
            u10_packed_reg <= '0;
            u11_packed_reg <= '0;
        end
        else begin
            uv_o.u20_o <= u10_div2;
            uv_o.u21_o <= v10_div2;
            uv_o.v20_o <= u11_div2;
            uv_o.v21_o <= v11_div2;
            u10_packed_reg <= u10_packed;
            u11_packed_reg <= u11_packed;
        end
    end

    always_comb begin
        bf_pwm_uv_o.uv0 = 0; //TODO: optimize
        bf_pwm_uv_o.uv1 = 0;
        bf_pwm_uv_o.uv2 = u10_packed;
        bf_pwm_uv_o.uv3 = u11_packed;
    end


endmodule