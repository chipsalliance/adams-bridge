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
// ntt_karatsuba_pairwm.sv
// MLKEM Karatsuba pair-wise multiplier.
//   c0 = (m0 + m1*zeta) mod q
//   c1 = (m2 - m0 - m1) mod q,  m2 = (a0+a1)*(b0+b1)
// m0, m1 come from BF mults (taps); only m2 and m1*zeta computed here.
// Latency from pwo_uvw_i to pwo_uv_o:
//   - 4 cycles when accumulate = 0
//   - 5 cycles when accumulate = 1 (one extra mod-add stage on +w)
// ntt_ctrl uses MLKEM_PAIRWM_LATENCY = 4 and shifts the write
// address tap by -1 when accumulate is asserted.
//======================================================================

module ntt_karatsuba_pairwm
    import ntt_defines_pkg::*;
    import abr_params_pkg::*;
(
    input  wire                          clk,
    input  wire                          reset_n,
    input  wire                          zeroize,

    input  wire                          accumulate,
    input  mlkem_pwo_uvwzi_t             pwo_uvw_i,
    input  wire [MLKEM_REG_SIZE-1:0]     pwo_z_i,

    // BF-tapped reduced base products (registered, 2-cycle from pwo_uvw_i).
    input  wire [MLKEM_REG_SIZE-1:0]     m0_red_i,
    input  wire [MLKEM_REG_SIZE-1:0]     m1_red_i,

    output mlkem_pwo_t                   pwo_uv_o
);

    logic [MLKEM_REG_SIZE-1:0] u0, u1, v0, v1, w0, w1, z1;

    always_comb begin
        u0 = pwo_uvw_i.u0_i;
        u1 = pwo_uvw_i.u1_i;
        v0 = pwo_uvw_i.v0_i;
        v1 = pwo_uvw_i.v1_i;
        w0 = pwo_uvw_i.w0_i;
        w1 = pwo_uvw_i.w1_i;
        z1 = pwo_z_i;
    end

    // Pre-add: sum_a = u0+u1 mod q, sum_b = v0+v1 mod q (1 cycle).
    logic [REG_SIZE-1:0] add_res_u, add_res_v;

    abr_ntt_add_sub_mod #(.REG_SIZE(REG_SIZE)) add_inst_u (
        .clk(clk), .reset_n(reset_n), .zeroize(zeroize),
        .add_en_i(1'b1), .sub_i(1'b0),
        .opa_i(REG_SIZE'(u0)), .opb_i(REG_SIZE'(u1)),
        .prime_i(REG_SIZE'(MLKEM_Q)), .mlkem(1'b1),
        .res_o(add_res_u), .ready_o()
    );

    abr_ntt_add_sub_mod #(.REG_SIZE(REG_SIZE)) add_inst_v (
        .clk(clk), .reset_n(reset_n), .zeroize(zeroize),
        .add_en_i(1'b1), .sub_i(1'b0),
        .opa_i(REG_SIZE'(v0)), .opb_i(REG_SIZE'(v1)),
        .prime_i(REG_SIZE'(MLKEM_Q)), .mlkem(1'b1),
        .res_o(add_res_v), .ready_o()
    );

    // m2 = sum_a * sum_b (comb mult + comb barrett, registered to m2_red_reg).
    logic [(2*MLKEM_REG_SIZE)-1:0] m2_raw;
    logic [MLKEM_REG_SIZE-1:0]     m2_red_comb, m2_red_reg;

    ntt_mult_dsp #(.RADIX(MLKEM_REG_SIZE)) m2_mul (
        .A_i(add_res_u[MLKEM_REG_SIZE-1:0]),
        .B_i(add_res_v[MLKEM_REG_SIZE-1:0]),
        .P_o(m2_raw)
    );

    barrett_reduction #(.REG_SIZE(MLKEM_REG_SIZE), .prime(MLKEM_Q)) m2_barrett (
        .x(m2_raw), .inv(), .r(m2_red_comb)
    );

    // m1*zeta = m1_red_i * z (comb mult + comb barrett, registered).
    logic [1:0][MLKEM_REG_SIZE-1:0] z_reg;
    logic [(2*MLKEM_REG_SIZE)-1:0]  m1z_raw;
    logic [MLKEM_REG_SIZE-1:0]      m1z_red_comb, m1z_red_reg;

    ntt_mult_dsp #(.RADIX(MLKEM_REG_SIZE)) m1z_mul (
        .A_i(m1_red_i), .B_i(z_reg[1]), .P_o(m1z_raw)
    );

    barrett_reduction #(.REG_SIZE(MLKEM_REG_SIZE), .prime(MLKEM_Q)) m1z_barrett (
        .x(m1z_raw), .inv(), .r(m1z_red_comb)
    );

    // w delay (4 cycles for accumulate); 1-cycle BF tap delay for c0/c1 stage 2.
    logic [3:0][MLKEM_REG_SIZE-1:0] w0_reg, w1_reg;
    logic [MLKEM_REG_SIZE-1:0]      m0_red_d1, m1_red_d1;

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            z_reg       <= '0;
            m2_red_reg  <= '0;
            m1z_red_reg <= '0;
            w0_reg      <= '0;
            w1_reg      <= '0;
            m0_red_d1   <= '0;
            m1_red_d1   <= '0;
        end
        else if (zeroize) begin
            z_reg       <= '0;
            m2_red_reg  <= '0;
            m1z_red_reg <= '0;
            w0_reg      <= '0;
            w1_reg      <= '0;
            m0_red_d1   <= '0;
            m1_red_d1   <= '0;
        end
        else begin
            z_reg       <= {z_reg[0], z1};
            m2_red_reg  <= m2_red_comb;
            m1z_red_reg <= m1z_red_comb;
            w0_reg      <= {w0_reg[2:0], w0};
            w1_reg      <= {w1_reg[2:0], w1};
            m0_red_d1   <= m0_red_i;
            m1_red_d1   <= m1_red_i;
        end
    end

    // c1_int = m2 - m0; c1 = c1_int - m1; c0 = m1*zeta + m0.
    logic [REG_SIZE-1:0] c1_int, uv1_o_int, uv0_o_int;

    abr_ntt_add_sub_mod #(.REG_SIZE(REG_SIZE)) sub_c1_int (
        .clk(clk), .reset_n(reset_n), .zeroize(zeroize),
        .add_en_i(1'b1), .sub_i(1'b1),
        .opa_i(REG_SIZE'(m2_red_reg)), .opb_i(REG_SIZE'(m0_red_i)),
        .prime_i(REG_SIZE'(MLKEM_Q)), .mlkem(1'b1),
        .res_o(c1_int), .ready_o()
    );

    abr_ntt_add_sub_mod #(.REG_SIZE(REG_SIZE)) sub_c1 (
        .clk(clk), .reset_n(reset_n), .zeroize(zeroize),
        .add_en_i(1'b1), .sub_i(1'b1),
        .opa_i(c1_int), .opb_i(REG_SIZE'(m1_red_d1)),
        .prime_i(REG_SIZE'(MLKEM_Q)), .mlkem(1'b1),
        .res_o(uv1_o_int), .ready_o()
    );

    abr_ntt_add_sub_mod #(.REG_SIZE(REG_SIZE)) add_c0 (
        .clk(clk), .reset_n(reset_n), .zeroize(zeroize),
        .add_en_i(1'b1), .sub_i(1'b0),
        .opa_i(REG_SIZE'(m1z_red_reg)), .opb_i(REG_SIZE'(m0_red_d1)),
        .prime_i(REG_SIZE'(MLKEM_Q)), .mlkem(1'b1),
        .res_o(uv0_o_int), .ready_o()
    );

    // Accumulate path: c{0,1} + w{0,1}.
    logic [REG_SIZE-1:0] uv0_o_acc, uv1_o_acc;

    abr_ntt_add_sub_mod #(.REG_SIZE(REG_SIZE)) add_uv0_acc_inst (
        .clk(clk), .reset_n(reset_n), .zeroize(zeroize),
        .add_en_i(1'b1), .sub_i(1'b0),
        .opa_i(uv0_o_int), .opb_i(REG_SIZE'(w0_reg[3])),
        .prime_i(REG_SIZE'(MLKEM_Q)), .mlkem(1'b1),
        .res_o(uv0_o_acc), .ready_o()
    );

    abr_ntt_add_sub_mod #(.REG_SIZE(REG_SIZE)) add_uv1_acc_inst (
        .clk(clk), .reset_n(reset_n), .zeroize(zeroize),
        .add_en_i(1'b1), .sub_i(1'b0),
        .opa_i(uv1_o_int), .opb_i(REG_SIZE'(w1_reg[3])),
        .prime_i(REG_SIZE'(MLKEM_Q)), .mlkem(1'b1),
        .res_o(uv1_o_acc), .ready_o()
    );

    assign pwo_uv_o.uv0_o = accumulate ? uv0_o_acc[MLKEM_REG_SIZE-1:0]
                                       : uv0_o_int[MLKEM_REG_SIZE-1:0];
    assign pwo_uv_o.uv1_o = accumulate ? uv1_o_acc[MLKEM_REG_SIZE-1:0]
                                       : uv1_o_int[MLKEM_REG_SIZE-1:0];

endmodule
