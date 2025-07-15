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
// ntt_mlkem_masked_butterfly1x2.sv
// --------
// 1. Performs 1st stage of masked INTT operation
// 2. Combines output shares
// 3. Performs div2 on combined outputs (unmasked)
// Total latency = 15+1 = 16 clks

module ntt_mlkem_masked_butterfly1x2
    import abr_params_pkg::*;
    import ntt_defines_pkg::*;
    #(
        parameter MLKEM_SHARE_WIDTH = 24,
        parameter MLKEM_Q_WIDTH = MLKEM_SHARE_WIDTH/2
    )
    (
        input wire clk,
        input wire reset_n,
        input wire zeroize,
        input mlkem_masked_bf_uvwi_t uvw_i,
        input [4:0][13:0] rnd_i,
        
        output bf_uvo_t uv_o
    );

    logic [1:0][MLKEM_SHARE_WIDTH-1:0] u00, v00, w00;
    logic [1:0][MLKEM_SHARE_WIDTH-1:0] u01, v01, w01;
    logic [1:0][MLKEM_SHARE_WIDTH-1:0] u10_int;
    logic [1:0][MLKEM_SHARE_WIDTH-1:0] v10_int;
    logic [1:0][MLKEM_SHARE_WIDTH-1:0] u11_int;
    logic [1:0][MLKEM_SHARE_WIDTH-1:0] v11_int;
    logic [MLKEM_Q_WIDTH-1:0] u10_combined, v10_combined, u11_combined, v11_combined;
    logic [MLKEM_Q_WIDTH-1:0] u10_div2, v10_div2, u11_div2, v11_div2;

    always_comb begin
        u00 = uvw_i.u00_i;
        v00 = uvw_i.v00_i;
        w00 = uvw_i.w00_i;

        u01 = uvw_i.u01_i;
        v01 = uvw_i.v01_i;
        w01 = uvw_i.w01_i;
    end

    //15
    ntt_mlkem_masked_gs_butterfly #(
        .WIDTH(MLKEM_SHARE_WIDTH)
    ) mlkem_masked_bf_inst00 (
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .opu_i(u00),
        .opv_i(v00),
        .opw_i(w00),
        .rnd_i({rnd_i[4], rnd_i[3], rnd_i[2], rnd_i[1], rnd_i[0]}),
        .u_o(u10_int),
        .v_o(v10_int)
    );

    ntt_mlkem_masked_gs_butterfly #(
        .WIDTH(MLKEM_SHARE_WIDTH)
    ) mlkem_masked_bf_inst01 (
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .opu_i(u01),
        .opv_i(v01),
        .opw_i(w01),
        .rnd_i({rnd_i[0], rnd_i[4], rnd_i[3], rnd_i[2], rnd_i[1]}),
        .u_o(u11_int),
        .v_o(v11_int)
    );

    always_comb begin
        u10_combined = MLKEM_Q_WIDTH'(u10_int[0] + u10_int[1]);
        v10_combined = MLKEM_Q_WIDTH'(v10_int[0] + v10_int[1]);
        u11_combined = MLKEM_Q_WIDTH'(u11_int[0] + u11_int[1]);
        v11_combined = MLKEM_Q_WIDTH'(v11_int[0] + v11_int[1]);
    end

    //Perform div2 on combined outputs
    ntt_div2 #(
        .REG_SIZE(MLKEM_Q_WIDTH),
        .PRIME(abr_params_pkg::MLKEM_Q)
    ) div2_inst0 (
        .op_i(u10_combined),
        .res_o(u10_div2)
    );

    ntt_div2 #(
        .REG_SIZE(MLKEM_Q_WIDTH),
        .PRIME(abr_params_pkg::MLKEM_Q)
    ) div2_inst1 (
        .op_i(v10_combined),
        .res_o(v10_div2)
    );

    ntt_div2 #(
        .REG_SIZE(MLKEM_Q_WIDTH),
        .PRIME(abr_params_pkg::MLKEM_Q)
    ) div2_inst2 (
        .op_i(u11_combined),
        .res_o(u11_div2)
    );

    ntt_div2 #(
        .REG_SIZE(MLKEM_Q_WIDTH),
        .PRIME(abr_params_pkg::MLKEM_Q)
    ) div2_inst3 (
        .op_i(v11_combined),
        .res_o(v11_div2)
    );

    //1 clk
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            uv_o <= 'h0;
        end
        else if (zeroize) begin
            uv_o <= 'h0;
        end
        else begin
            uv_o.u20_o <= NTT_REG_SIZE'(u10_div2);
            uv_o.u21_o <= NTT_REG_SIZE'(v10_div2);
            uv_o.v20_o <= NTT_REG_SIZE'(u11_div2);
            uv_o.v21_o <= NTT_REG_SIZE'(v11_div2);
        end
    end

endmodule