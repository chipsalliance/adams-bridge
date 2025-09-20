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
// ntt_masked_BFU_mult_with_barrett
// Performs two share multiplication and reduction using barrett reduction - total latency = X clks
// Total latency = 8+1 = 9 clks
//======================================================================

module ntt_masked_BFU_mult_with_barrett
    import ntt_defines_pkg::*;
    import abr_params_pkg::*;
#(
    parameter WIDTH = 46,
    parameter HALF_WIDTH = WIDTH/2,
    parameter ROLLER = WIDTH'(2**13-1)
)
(
    input wire clk,
    input wire reset_n,
    input wire zeroize,
    input wire [1:0][WIDTH-1:0] u,
    input wire [1:0][WIDTH-1:0] v,
    input wire [WIDTH-1:0] rnd0, rnd1, rnd2, rnd3, rnd4,
    output logic [1:0] res [WIDTH-1:0]
);

//Internal signals
logic [1:0] mul_res [WIDTH-1:0];
logic [1:0][WIDTH-1:0] mul_res_packed, mul_res_reduced;


//Perform mul on input shares - 2 clk
abr_masked_N_bit_mult_two_share #(
    .WIDTH(WIDTH)
) masked_two_share_mult_inst (
    .clk(clk),
    .rst_n(reset_n),
    .zeroize(zeroize),
    .random(rnd0),
    .x(u),
    .y(v),
    .z(mul_res)
);

always_comb begin
    for (int i = 0; i < WIDTH; i++) begin
        mul_res_packed[0][i] = mul_res[i][0];
        mul_res_packed[1][i] = mul_res[i][1];
    end
end

//Perform barrett reduction on mul res - 6 clks
mldsa_masked_barrett_reduction masked_mul_res_redux_inst (
    .clk(clk),
    .rst_n(reset_n),
    .zeroize(zeroize),
    .x(mul_res_packed),
    //TODO: fix rnd inputs - using mlkem version for poc
    .rnd_12bit(rnd1[11:0]),
    .rnd_14bit(rnd2[13:0]),
    .rnd_24bit(rnd3[23:0]),
    .rnd_for_Boolean0(rnd4[13:0]),
    .rnd_for_Boolean1(rnd1[25:12]),
    .rnd_1bit(rnd1[26]),
    .y(mul_res_reduced)
);

always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        for (int i = 0; i < WIDTH; i++)
            res[i] <= 2'b0;
    end
    else if (zeroize) begin
        for (int i = 0; i < WIDTH; i++)
            res[i] <= 2'b0;
    end
    else begin
        for (int i = 0; i < WIDTH; i++) begin
            res[i][0] <= mul_res_reduced[0][i];
            res[i][1] <= mul_res_reduced[1][i];
        end
    end
end

endmodule