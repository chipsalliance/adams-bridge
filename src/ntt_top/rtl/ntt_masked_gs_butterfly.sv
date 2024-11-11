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

module ntt_masked_gs_butterfly
    import mldsa_params_pkg::*;
    import ntt_defines_pkg::*;
    #(
        parameter WIDTH = 46
    )
    (
        input wire clk,
        input wire reset_n,
        input wire zeroize,

        input wire [1:0][WIDTH-1:0] opu_i,
        input wire [1:0][WIDTH-1:0] opv_i,
        input wire [1:0][WIDTH-1:0] opw_i, //benefit from splitting? Or should we use one share mult?
        input wire [4:0][WIDTH-1:0] rnd_i,

        output logic [1:0] u_o [WIDTH-1:0], //TODO: make packed?
        output logic [1:0] v_o [WIDTH-1:0]
    );

    logic [1:0][WIDTH-1:0] w_reg [52:0]; //TODO parameterize
    logic [1:0] add_res [WIDTH-1:0];
    logic [1:0] sub_res [WIDTH-1:0];
    logic [1:0] mul_res [WIDTH-1:0];
    logic [1:0][WIDTH-1:0] sub_res_packed;

    logic [WIDTH-1:0] add_res0, add_res1, mul_res0, mul_res1;

    ntt_masked_BFU_add_sub #(
        .WIDTH(WIDTH)
    ) add_inst_0 (
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .sub('b0),
        .u(opu_i),
        .v(opv_i),
        .rnd0(rnd_i[0]),
        .rnd1(rnd_i[1]),
        .rnd2(rnd_i[2]),
        .rnd3(rnd_i[3]),
        .res(add_res) //u+v
    );

    ntt_masked_BFU_add_sub #(
        .WIDTH(WIDTH)
    ) sub_inst_0 (
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .sub('b1),
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
        end
    end

    //w delay flops
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            for (int i = 0; i < 53; i++) begin
                w_reg[i] <= 'h0;
            end
        end
        else if (zeroize) begin
            for (int i = 0; i < 53; i++) begin
                w_reg[i] <= 'h0;
            end
        end
        else begin
            w_reg <= {opw_i, w_reg[52:1]};
        end
    end

    ntt_masked_BFU_mult #(
        .WIDTH(WIDTH)
    ) mult_inst_0 (
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .u(sub_res_packed),
        .v(w_reg[0]),
        .rnd0(rnd_i[2]),
        .rnd1(rnd_i[3]),
        .rnd2(rnd_i[0]),
        .rnd3(rnd_i[1]),
        .rnd4(rnd_i[2]+rnd_i[3]),
        .res(mul_res)
    );

    always_comb begin
        for (int i = 0; i < WIDTH; i++) begin
            mul_res0[i] = mul_res[i][0];
            mul_res1[i] = mul_res[i][1];
        end
    end

endmodule
