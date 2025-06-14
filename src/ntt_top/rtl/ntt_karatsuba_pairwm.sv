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
// ntt_karatsuba_pairwm.sv
// --------
// Unmasked MLKEM Karatsuba pairwise multiplier. Receives 4 coefficients - 2 from memory, 2 from sampler/memory
// and generates 2 corresponding outputs. Also needs an additional zeta input. All operations are modular.
// Supports accumulation as an additional input.
// This module uses Karatsuba technique for an optimized implementation of pairwise multiplication. However,
// in a masked version, normal multiplication is performed for a better masking structure
// (a2i, a2i+1) * (b2i, b2i+1) =>
// c2i = (a2i*b2i) + (a2i+1*b2i+1*zeta) 
// c2i+1 = [{(a2i+a2i+1)*(b2i+b2i+1)} - (a2i*b2i)] - (a2i+1*b2i+1)
// Total end-to-end latency without accumulate = 4 cycles
// Total end-to-end latency with accumulate    = 5 cycles

module ntt_karatsuba_pairwm
    import ntt_defines_pkg::*;
    import abr_params_pkg::*;
(
    //Clock and reset
    input wire clk,
    input wire reset_n,
    input wire zeroize,

    //Data ports
    input wire accumulate,
    input mlkem_pwo_uvwzi_t pwo_uvw_i,
    input [MLKEM_REG_SIZE-1:0] pwo_z_i,
    output mlkem_pwo_t pwo_uv_o
);

logic [MLKEM_REG_SIZE-1:0] u0, u1, v0, v1, w0, w1, z1;

logic [(2*MLKEM_REG_SIZE)-1:0] uv00, uv01, uv11, mul_res_uv12, uvz11;
logic [MLKEM_REG_SIZE-1:0] uv00_reduced, uv11_reduced, mul_res_uv12_reduced, sub_res1, uvz11_reduced;
logic [REG_SIZE-1:0] add_res_u, add_res_v, sub_res0;

always_comb begin
    u0 = pwo_uvw_i.u0_i;
    u1 = pwo_uvw_i.u1_i;

    v0 = pwo_uvw_i.v0_i;
    v1 = pwo_uvw_i.v1_i;

    w0 = pwo_uvw_i.w0_i;
    w1 = pwo_uvw_i.w1_i;

    z1 = pwo_z_i;
end

//--------------------------------
ntt_mult_dsp #(
    .RADIX(MLKEM_REG_SIZE)
    )
    mul_inst_0 (
    .A_i(u0),
    .B_i(v0),
    .P_o(uv00)
);

barrett_reduction #(
    .REG_SIZE(MLKEM_REG_SIZE),
    .prime(MLKEM_Q)
)
mul_redux_inst_0 (
    .x(uv00),
    .inv(),
    .r(uv00_reduced)
);

logic [2:0][MLKEM_REG_SIZE-1:0] uv00_reduced_reg, uv11_reduced_reg, z1_reg;
logic [3:0][MLKEM_REG_SIZE-1:0] w0_reg, w1_reg;
logic [REG_SIZE-1:0] uv0_o_int, uv1_o_int, uv1_o_int_reg, uv0_o_acc, uv1_o_acc;
always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        uv00_reduced_reg <= '0;
        uv11_reduced_reg <= '0;
        z1_reg <= '0;
        w0_reg <= '0;
        w1_reg <= '0;
        uv1_o_int_reg <= '0;
    end
    else if (zeroize) begin
        uv00_reduced_reg <= '0;
        uv11_reduced_reg <= '0;
        z1_reg <= '0;
        w0_reg <= '0;
        w1_reg <= '0;
        uv1_o_int_reg <= '0;
    end
    else begin
        uv00_reduced_reg <= {uv00_reduced_reg[1:0], uv00_reduced};
        uv11_reduced_reg <= {uv11_reduced_reg[1:0], uv11_reduced};
        z1_reg <= {z1_reg[1:0], z1};
        w0_reg <= {w0_reg[2:0], w0};
        w1_reg <= {w1_reg[2:0], w1};
        uv1_o_int_reg <= uv1_o_int;
    end
end
//--------------------------------

//--------------------------------
ntt_mult_dsp #(
    .RADIX(MLKEM_REG_SIZE)
    )
    mul_inst_3 (
    .A_i(u1),
    .B_i(v1),
    .P_o(uv11)
);

barrett_reduction #(
    .REG_SIZE(MLKEM_REG_SIZE),
    .prime(MLKEM_Q)
)
mul_redux_inst_3 (
    .x(uv11),
    .inv(),
    .r(uv11_reduced)
);

ntt_mult_dsp #(
    .RADIX(MLKEM_REG_SIZE)
)
mul_inst_zeta (
    .A_i(uv11_reduced_reg[2]),
    .B_i(z1_reg[2]),
    .P_o(uvz11)
);

barrett_reduction #(
    .REG_SIZE(MLKEM_REG_SIZE),
    .prime(MLKEM_Q)
)
mul_zeta_redux_inst (
    .x(uvz11),
    .inv(),
    .r(uvz11_reduced)
);

//1 cycle
abr_ntt_add_sub_mod #(
    .REG_SIZE(REG_SIZE) //generic adder works with MLDSA reg size. In MLKEM, we're keeping the same reg size and just checking [12] for carry bit to reuse butterfly units. However, this instance is specific to MLKEM, so we need to pass reg size + 1 to preserve functionality
)
add_inst_uvz11(
    .clk(clk),
    .reset_n(reset_n),
    .zeroize(zeroize),
    .add_en_i(1'b1),
    .sub_i(1'b0),
    .opa_i(REG_SIZE'(uvz11_reduced)),
    .opb_i(REG_SIZE'(uv00_reduced_reg[2])),
    .prime_i(REG_SIZE'(MLKEM_Q)),
    .mlkem(1'b1),
    .res_o(uv0_o_int),
    .ready_o()
);
//--------------------------------

//--------------------------------
//1 cycle
abr_ntt_add_sub_mod #(
    .REG_SIZE(REG_SIZE)
)
add_inst_u(
    .clk(clk),
    .reset_n(reset_n),
    .zeroize(zeroize),
    .add_en_i(1'b1),
    .sub_i(1'b0),
    .opa_i(REG_SIZE'(u0)),
    .opb_i(REG_SIZE'(u1)),
    .prime_i(REG_SIZE'(MLKEM_Q)),
    .mlkem(1'b1),
    .res_o(add_res_u),
    .ready_o()
);

//1 cycle
abr_ntt_add_sub_mod #(
    .REG_SIZE(REG_SIZE)
)
add_inst_v(
    .clk(clk),
    .reset_n(reset_n),
    .zeroize(zeroize),
    .add_en_i(1'b1),
    .sub_i(1'b0),
    .opa_i(REG_SIZE'(v0)),
    .opb_i(REG_SIZE'(v1)),
    .prime_i(REG_SIZE'(MLKEM_Q)),
    .mlkem(1'b1),
    .res_o(add_res_v),
    .ready_o()
);
//--------------------------------

//--------------------------------
ntt_mult_dsp #(
    .RADIX(MLKEM_REG_SIZE)
    )
    mul_inst_12 (
    .A_i(add_res_u[MLKEM_REG_SIZE-1:0]),
    .B_i(add_res_v[MLKEM_REG_SIZE-1:0]),
    .P_o(mul_res_uv12)
);

barrett_reduction #(
    .REG_SIZE(MLKEM_REG_SIZE),
    .prime(MLKEM_Q)
)
mul_redux_inst_12 (
    .x(mul_res_uv12),
    .inv(),
    .r(mul_res_uv12_reduced)
);
//--------------------------------
//1 cycle
abr_ntt_add_sub_mod #(
    .REG_SIZE(REG_SIZE)
)
sub_inst_0(
    .clk(clk),
    .reset_n(reset_n),
    .zeroize(zeroize),
    .add_en_i(1'b1),
    .sub_i(1'b1),
    .opa_i(REG_SIZE'(mul_res_uv12_reduced)),
    .opb_i(REG_SIZE'(uv00_reduced_reg[0])),
    .prime_i(REG_SIZE'(MLKEM_Q)),
    .mlkem(1'b1),
    .res_o(sub_res0),
    .ready_o()
);

//1 cycle
abr_ntt_add_sub_mod #(
    .REG_SIZE(REG_SIZE)
)
sub_inst_1(
    .clk(clk),
    .reset_n(reset_n),
    .zeroize(zeroize),
    .add_en_i(1'b1),
    .sub_i(1'b1),
    .opa_i(sub_res0),
    .opb_i(REG_SIZE'(uv11_reduced_reg[1])),
    .prime_i(REG_SIZE'(MLKEM_Q)),
    .mlkem(1'b1),
    .res_o(uv1_o_int),
    .ready_o()
);

//--------------------------------
//accumulation
abr_ntt_add_sub_mod #(
    .REG_SIZE(REG_SIZE)
)
add_uv0_acc_inst(
    .clk(clk),
    .reset_n(reset_n),
    .zeroize(zeroize),
    .add_en_i(1'b1),
    .sub_i(1'b0),
    .opa_i(uv0_o_int),
    .opb_i(REG_SIZE'(w0_reg[3])),
    .prime_i(REG_SIZE'(MLKEM_Q)),
    .mlkem(1'b1),
    .res_o(uv0_o_acc),
    .ready_o()
);

abr_ntt_add_sub_mod #(
    .REG_SIZE(REG_SIZE)
)
add_uv1_acc_inst(
    .clk(clk),
    .reset_n(reset_n),
    .zeroize(zeroize),
    .add_en_i(1'b1),
    .sub_i(1'b0),
    .opa_i(uv1_o_int_reg),
    .opb_i(REG_SIZE'(w1_reg[3])),
    .prime_i(REG_SIZE'(MLKEM_Q)),
    .mlkem(1'b1),
    .res_o(uv1_o_acc),
    .ready_o()
);

assign pwo_uv_o.uv0_o = accumulate ? uv0_o_acc[MLKEM_REG_SIZE-1:0] : uv0_o_int[MLKEM_REG_SIZE-1:0];
assign pwo_uv_o.uv1_o = accumulate ? uv1_o_acc[MLKEM_REG_SIZE-1:0] : uv1_o_int_reg[MLKEM_REG_SIZE-1:0];

endmodule