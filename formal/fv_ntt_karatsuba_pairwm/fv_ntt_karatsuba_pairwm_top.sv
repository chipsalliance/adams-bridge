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

// -------------------------------------------------
// Copyright(c) LUBIS EDA GmbH, All rights reserved
// Contact: contact@lubis-eda.com
// -------------------------------------------------


module fv_ntt_karatsuba_pairwm_top
    import ntt_defines_pkg::*;
    import abr_params_pkg::*;
#(
    //#$localparams
    //$#//
) (
    //#$ports
    input                      pi_clk,
    input                      pi_reset_n,
    input                      pi_zeroize,
    input                      pi_accumulate,
    input mlkem_pwo_uvwzi_t    pi_pwo_uvw_i,
    input [MLKEM_REG_SIZE-1:0] pi_pwo_z_i,
    input mlkem_pwo_t          po_pwo_uv_o,
    input [MLKEM_REG_SIZE-1:0] pi_m0_red_i,
    input [MLKEM_REG_SIZE-1:0] pi_m1_red_i
    //$#//
);
    default clocking default_clk @(posedge pi_clk); endclocking

    fv_ntt_karatsuba_pairwm_constraints #(
    ) fv_ntt_karatsuba_pairwm_constraints_i (.*);

    //Function that multiplies two inputs and returns the result modulus Q
    function automatic logic[MLKEM_REG_SIZE-1:0] fv_mult_mod_q (
        logic[MLKEM_REG_SIZE-1:0] u,
        logic[MLKEM_REG_SIZE-1:0] v
    );
        logic [(2*MLKEM_REG_SIZE)-1:0] fv_mult_res;
        fv_mult_res = u * v;
        fv_mult_mod_q = MLKEM_REG_SIZE'(fv_mult_res % MLKEM_Q);
    endfunction

    //Function that adds two inputs and returns the result modulus Q
    function automatic logic[MLKEM_REG_SIZE-1:0] fv_add_mod_q (
        logic[MLKEM_REG_SIZE-1:0] u,
        logic[MLKEM_REG_SIZE-1:0] v
    );
        logic [MLKEM_REG_SIZE:0] fv_add_res;
        fv_add_res = {1'b0, u} + {1'b0, v};
        fv_add_mod_q = MLKEM_REG_SIZE'(fv_add_res % MLKEM_Q);
    endfunction

    //Function that subtracts two inputs and returns the result modulus Q
    function automatic logic[MLKEM_REG_SIZE-1:0] fv_sub_mod_q (
        logic[MLKEM_REG_SIZE-1:0] u,
        logic[MLKEM_REG_SIZE-1:0] v
    );
        logic [MLKEM_REG_SIZE:0] fv_sub_res;
        fv_sub_res = {1'b0, u} - {1'b0, v};

        if (fv_sub_res[MLKEM_REG_SIZE]) begin //negative number, wrap around
            fv_sub_mod_q = MLKEM_REG_SIZE'((fv_sub_res + {1'b0, MLKEM_Q}) % MLKEM_Q);
        end
        else begin
            fv_sub_mod_q = MLKEM_REG_SIZE'(fv_sub_res % MLKEM_Q);
        end
    endfunction



    // Gold model for m2 = (u0+u1)*(v0+v1) mod q.
    // m0 and m1 are no longer computed here; they come from pi_m0_red_i / pi_m1_red_i
    // (BF-tap inputs) which arrive 2 cycles after pwo_uvw_i.

    logic [MLKEM_REG_SIZE-1:0] fv_add_u_mod_q;
    assign fv_add_u_mod_q = fv_add_mod_q(pi_pwo_uvw_i.u0_i, pi_pwo_uvw_i.u1_i);

    logic [MLKEM_REG_SIZE-1:0] fv_add_v_mod_q;
    assign fv_add_v_mod_q = fv_add_mod_q(pi_pwo_uvw_i.v0_i, pi_pwo_uvw_i.v1_i);

    logic [MLKEM_REG_SIZE-1:0] fv_m2_mod_q;
    assign fv_m2_mod_q = fv_mult_mod_q(fv_add_u_mod_q, fv_add_v_mod_q);

    //──────────── white-box checks ────────────

    // Pre-add: sum_a = u0+u1 mod q, sum_b = v0+v1 mod q (1 cycle).
    property ntt_karatsuba_pwm_add_res_u;
        ##1 ntt_karatsuba_pairwm.add_res_u == $past(fv_add_u_mod_q, 1)
    ;endproperty
    assert_ntt_karatsuba_pwm_add_res_u: assert property (
        disable iff(!pi_reset_n | pi_zeroize) ntt_karatsuba_pwm_add_res_u);

    property ntt_karatsuba_pwm_add_res_v;
        ##1 ntt_karatsuba_pairwm.add_res_v == $past(fv_add_v_mod_q, 1)
    ;endproperty
    assert_ntt_karatsuba_pwm_add_res_v: assert property (
        disable iff(!pi_reset_n | pi_zeroize) ntt_karatsuba_pwm_add_res_v);


    // m2 = res_u * res_v % (comb mult + comb barrett)
    property ntt_karatsuba_pwm_m2;
        ##1 ntt_karatsuba_pairwm.m2_red_comb ==
            fv_mult_mod_q(ntt_karatsuba_pairwm.add_res_u[MLKEM_REG_SIZE-1:0],
                  ntt_karatsuba_pairwm.add_res_v[MLKEM_REG_SIZE-1:0])
    ;endproperty
    assert_ntt_karatsuba_pwm_m2: assert property (
        disable iff(!pi_reset_n | pi_zeroize) ntt_karatsuba_pwm_m2);

    // m1z_red_comb = (m1_red_i * z_reg[1]) mod Q
    property ntt_karatsuba_pwm_m1z_red_comb;
        ##1 ntt_karatsuba_pairwm.m1z_red_comb ==
            fv_mult_mod_q(pi_m1_red_i, ntt_karatsuba_pairwm.z_reg[1])
    ;endproperty
    assert_ntt_karatsuba_pwm_m1z_red_comb: assert property (
        disable iff(!pi_reset_n | pi_zeroize) ntt_karatsuba_pwm_m1z_red_comb);


    // 1-cycle delay registers for BF-tap inputs

    property ntt_karatsuba_pwm_m0_red_d1;
        ##1 ntt_karatsuba_pairwm.m0_red_d1 == $past(pi_m0_red_i, 1)
    ;endproperty
    assert_ntt_karatsuba_pwm_m0_red_d1: assert property (
        disable iff(!pi_reset_n | pi_zeroize) ntt_karatsuba_pwm_m0_red_d1);

    property ntt_karatsuba_pwm_m1_red_d1;
        ##1 ntt_karatsuba_pairwm.m1_red_d1 == $past(pi_m1_red_i, 1)
    ;endproperty
    assert_ntt_karatsuba_pwm_m1_red_d1: assert property (
        disable iff(!pi_reset_n | pi_zeroize) ntt_karatsuba_pwm_m1_red_d1);

    // sub_c1_int: c1_int = m2_red_reg - m0_red_i mod Q
    property ntt_karatsuba_pwm_c1_int;
        ##1 ntt_karatsuba_pairwm.c1_int[MLKEM_REG_SIZE-1:0] ==
            fv_sub_mod_q($past(ntt_karatsuba_pairwm.m2_red_reg, 1),
                        $past(pi_m0_red_i, 1))
    ;endproperty
    assert_ntt_karatsuba_pwm_c1_int: assert property (
        disable iff(!pi_reset_n | pi_zeroize) ntt_karatsuba_pwm_c1_int);

    // uv0/uv1 before output mux

    // add_c0: uv0_o_int = m1z_red_reg + m0_red_d1 mod Q
    property ntt_karatsuba_pwm_uv0_o_int;
        ##1 ntt_karatsuba_pairwm.uv0_o_int[MLKEM_REG_SIZE-1:0] ==
            fv_add_mod_q($past(ntt_karatsuba_pairwm.m1z_red_reg, 1),
                        $past(ntt_karatsuba_pairwm.m0_red_d1, 1))
    ;endproperty
    assert_ntt_karatsuba_pwm_uv0_o_int: assert property (
        disable iff(!pi_reset_n | pi_zeroize) ntt_karatsuba_pwm_uv0_o_int);

    // sub_c1: uv1_o_int = c1_int - m1_red_d1 mod Q
    property ntt_karatsuba_pwm_uv1_o_int;
        ##1 ntt_karatsuba_pairwm.uv1_o_int[MLKEM_REG_SIZE-1:0] ==
            fv_sub_mod_q($past(ntt_karatsuba_pairwm.c1_int[MLKEM_REG_SIZE-1:0], 1),
                        $past(ntt_karatsuba_pairwm.m1_red_d1, 1))
    ;endproperty
    assert_ntt_karatsuba_pwm_uv1_o_int: assert property (
        disable iff(!pi_reset_n | pi_zeroize) ntt_karatsuba_pwm_uv1_o_int);

    // w_reg delay chain: verify tap [3] used by accumulate path

    property ntt_karatsuba_pwm_w0_reg_3;
        ##4 ntt_karatsuba_pairwm.w0_reg[3] == $past(pi_pwo_uvw_i.w0_i, 4)
    ;endproperty
    assert_ntt_karatsuba_pwm_w0_reg_3: assert property (
        disable iff(!pi_reset_n | pi_zeroize) ntt_karatsuba_pwm_w0_reg_3);

    property ntt_karatsuba_pwm_w1_reg_3;
        ##4 ntt_karatsuba_pairwm.w1_reg[3] == $past(pi_pwo_uvw_i.w1_i, 4)
    ;endproperty
    assert_ntt_karatsuba_pwm_w1_reg_3: assert property (
        disable iff(!pi_reset_n | pi_zeroize) ntt_karatsuba_pwm_w1_reg_3);

    // z delay alignment: z_reg[1] = zeta delayed 2 cycles
    property ntt_karatsuba_pwm_z_reg_1;
        ##2 ntt_karatsuba_pairwm.z_reg[1] == $past(pi_pwo_z_i, 2)
    ;endproperty
    assert_ntt_karatsuba_pwm_z_reg_1: assert property (
        disable iff(!pi_reset_n | pi_zeroize) ntt_karatsuba_pwm_z_reg_1);

    // accumulate path

    // add_uv0_acc: uv0_o_acc = uv0_o_int + w0_reg[3] mod Q
    property ntt_karatsuba_pwm_uv0_o_acc;
        ##1 ntt_karatsuba_pairwm.uv0_o_acc[MLKEM_REG_SIZE-1:0] ==
            fv_add_mod_q($past(ntt_karatsuba_pairwm.uv0_o_int[MLKEM_REG_SIZE-1:0], 1),
                        $past(ntt_karatsuba_pairwm.w0_reg[3], 1))
    ;endproperty
    assert_ntt_karatsuba_pwm_uv0_o_acc: assert property (
        disable iff(!pi_reset_n | pi_zeroize) ntt_karatsuba_pwm_uv0_o_acc);

    // add_uv1_acc: uv1_o_acc = uv1_o_int + w1_reg[3] mod Q
    property ntt_karatsuba_pwm_uv1_o_acc;
        ##1 ntt_karatsuba_pairwm.uv1_o_acc[MLKEM_REG_SIZE-1:0] ==
            fv_add_mod_q($past(ntt_karatsuba_pairwm.uv1_o_int[MLKEM_REG_SIZE-1:0], 1),
                        $past(ntt_karatsuba_pairwm.w1_reg[3], 1))
    ;endproperty
    assert_ntt_karatsuba_pwm_uv1_o_acc: assert property (
        disable iff(!pi_reset_n | pi_zeroize) ntt_karatsuba_pwm_uv1_o_acc);


// ──────────── End-to-end checks ────────────

    // Verify pwo_uv_o.uv0_o after the configured latency.
    // Expected: uv0 = (m0 + m1*z) mod q
    property ntt_karatsuba_pwm_uv0_o_no_accumulate;
        logic [MLKEM_REG_SIZE-1:0] m0_red;
        logic [MLKEM_REG_SIZE-1:0] m1_red;
        logic [MLKEM_REG_SIZE-1:0] zeta;

        ##2 $past(pi_accumulate,2) == 1'b0
        ##0 (1'b1, m0_red = pi_m0_red_i)
        ##0 (1'b1, m1_red = pi_m1_red_i)
        ##0 (1'b1, zeta = $past(pi_pwo_z_i, 2))

    |->
        ##(MLKEM_PAIRWM_LATENCY - 2) po_pwo_uv_o.uv0_o == fv_add_mod_q(m0_red, fv_mult_mod_q(m1_red, zeta))
    ;endproperty
    assert_ntt_karatsuba_pwm_uv0_o_no_accumulate: assert property (
        disable iff(!pi_reset_n | pi_zeroize) ntt_karatsuba_pwm_uv0_o_no_accumulate);


    // Verify pwo_uv_o.uv1_o in case of no accumulate after the configured latency.
    // Expected: uv1 = m2 - m0 - m1  mod q
    property ntt_karatsuba_pwm_uv1_o_no_accumulate;
        logic [MLKEM_REG_SIZE-1:0] m0_red;
        logic [MLKEM_REG_SIZE-1:0] m1_red;
        logic [MLKEM_REG_SIZE-1:0] m2;

        ##2 $past(pi_accumulate, 2) == 1'b0
        ##0 (1, m0_red = pi_m0_red_i)
        ##0 (1, m1_red = pi_m1_red_i)
        ##0 (1, m2     = $past(fv_m2_mod_q, 2))

    |->
        ##(MLKEM_PAIRWM_LATENCY - 2) po_pwo_uv_o.uv1_o == fv_sub_mod_q(fv_sub_mod_q(m2, m0_red), m1_red)
    ;endproperty
    assert_ntt_karatsuba_pwm_uv1_o_no_accumulate: assert property (
        disable iff(!pi_reset_n | pi_zeroize) ntt_karatsuba_pwm_uv1_o_no_accumulate);


    // Verify pwo_uv_o.uv0_o in case of accumulate after the configured latency.
    // Expected: uv0 = (m0 + m1*z) + w0  mod q
    property ntt_karatsuba_pwm_uv0_o_accumulate;
        logic [MLKEM_REG_SIZE-1:0] m0_red;
        logic [MLKEM_REG_SIZE-1:0] m1_red;
        logic [MLKEM_REG_SIZE-1:0] zeta;
        logic [MLKEM_REG_SIZE-1:0] w0;

        ##2 $past(pi_accumulate, 2) == 1'b1
        ##0 (1, m0_red = pi_m0_red_i)
        ##0 (1, m1_red = pi_m1_red_i)
        ##0 (1, zeta   = $past(pi_pwo_z_i, 2))
        ##0 (1, w0     = $past(pi_pwo_uvw_i.w0_i, 2))

    |->
        ##(MLKEM_PAIRWM_ACC_LATENCY - 2) po_pwo_uv_o.uv0_o == fv_add_mod_q(
            fv_add_mod_q(m0_red, fv_mult_mod_q(m1_red, zeta)), w0)

    ;endproperty
    assert_ntt_karatsuba_pwm_uv0_o_accumulate: assert property (
        disable iff(!pi_reset_n | pi_zeroize) ntt_karatsuba_pwm_uv0_o_accumulate);


    // Verify pwo_uv_o.uv1_o in case of accumulate after the configured latency.
    // Expected: uv1 = (m2 - m0 - m1) + w1  mod q
    property ntt_karatsuba_pwm_uv1_o_accumulate;
        logic [MLKEM_REG_SIZE-1:0] m0_red;
        logic [MLKEM_REG_SIZE-1:0] m1_red;
        logic [MLKEM_REG_SIZE-1:0] m2;
        logic [MLKEM_REG_SIZE-1:0] w1;

        ##2 $past(pi_accumulate, 2) == 1'b1
        ##0 (1, m0_red = pi_m0_red_i)
        ##0 (1, m1_red = pi_m1_red_i)
        ##0 (1, m2     = $past(fv_m2_mod_q, 2))
        ##0 (1, w1     = $past(pi_pwo_uvw_i.w1_i, 2))

    |->
        ##(MLKEM_PAIRWM_ACC_LATENCY - 2) po_pwo_uv_o.uv1_o == fv_add_mod_q(
            fv_sub_mod_q(fv_sub_mod_q(m2, m0_red), m1_red), w1)

    ;endproperty
    assert_ntt_karatsuba_pwm_uv1_o_accumulate: assert property (
        disable iff(!pi_reset_n | pi_zeroize) ntt_karatsuba_pwm_uv1_o_accumulate);

    //Property to check output after reset
    property ntt_karatsuba_pwm_reset;
        $past(!pi_reset_n | pi_zeroize)
    |->
        po_pwo_uv_o == 'd0
    ;endproperty
    assert_ntt_karatsuba_pwm_reset: assert property (ntt_karatsuba_pwm_reset);

    //Data integrity check: verify that the output is always less than Q
    property ntt_karatsuba_pwm_output_range;
    po_pwo_uv_o.uv0_o < MLKEM_Q &&
    po_pwo_uv_o.uv1_o < MLKEM_Q
    ;endproperty

    assert_ntt_karatsuba_pwm_output_range: assert property (
        disable iff(!pi_reset_n | pi_zeroize) ntt_karatsuba_pwm_output_range);


endmodule


bind ntt_karatsuba_pairwm fv_ntt_karatsuba_pairwm_top #(
    //#$bind
) fv_ntt_karatsuba_pairwm_top_i (
    .pi_clk (clk),
    .pi_reset_n (reset_n),
    .pi_zeroize (zeroize),
    .pi_accumulate (accumulate),
    .pi_pwo_uvw_i (pwo_uvw_i),
    .pi_pwo_z_i (pwo_z_i),
    .po_pwo_uv_o (pwo_uv_o),
    .pi_m0_red_i (m0_red_i),
    .pi_m1_red_i (m1_red_i)
    //$#//
);
