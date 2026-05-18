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
// ntt_hybrid_noncascade_butterfly_2x2.sv
// --------
// This module consists of PWMs followed by two stages of BFUs.
// Final outputs are 23-bit values.

module ntt_hybrid_butterfly_2x2
    import abr_params_pkg::*;
    import ntt_defines_pkg::*;
(
    input wire clk,
    input wire reset_n,
    input wire zeroize,

    input mode_t mode,
    input wire enable,
    input wire shuffle_en,
    input wire mlkem,
    input bf_uvwi_t uvw_i,      //Inputs are original form
    input pwo_uvwi_t pw_uvw_i,  //PWO inputs are original form - reuse for MLKEM PairWM
    input wire accumulate,
    input mlkem_pairwm_zeta_t mlkem_pairwm_zeta13_i,
    input wire ntt_passthrough,
    input wire intt_passthrough,

    output bf_uvo_t uv_o,       //Outputs are original form
    output pwo_t pwo_uv_o,
    output logic ready_o
);

//Inputs to 1st stage
logic [NTT_REG_SIZE-1:0] u00, u01, v00, v01;
logic [NTT_REG_SIZE-1:0] w00, w01, w10, w11;
//Outputs of 1st stage
logic [NTT_REG_SIZE-1:0] u10_int, u11_int, v10_int, v11_int;
//Inputs to 2nd stage
logic [NTT_REG_SIZE-1:0] u10, u11, v10, v11;

pwo_t mldsa_pwo_uv_o;

logic gs_mode;
logic pairwm_mode;

//Other internal wires
logic [BF_STAGE1_LATENCY-1:0][NTT_REG_SIZE-1:0] mldsa_w10_reg, mldsa_w11_reg; //Shift w10 by 3 cycles to match 1st stage BF latency
logic [MLKEM_BF_STAGE1_LATENCY-1:0][MLKEM_REG_SIZE-1:0] mlkem_w10_reg, mlkem_w11_reg;
logic pwo_mode;

//w delay flops
//Flop the twiddle factor 3x to correctly pass in values to the 2nd set of bf units
always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        mldsa_w10_reg <= 'h0;
        mldsa_w11_reg <= 'h0;
        mlkem_w10_reg <= 'h0;
        mlkem_w11_reg <= 'h0;
    end
    else if (zeroize) begin
        mldsa_w10_reg <= 'h0;
        mldsa_w11_reg <= 'h0;
        mlkem_w10_reg <= 'h0;
        mlkem_w11_reg <= 'h0;
    end
    else begin
        mldsa_w10_reg <= {uvw_i.w10_i, mldsa_w10_reg[BF_STAGE1_LATENCY-1:1]};
        mldsa_w11_reg <= {uvw_i.w11_i, mldsa_w11_reg[BF_STAGE1_LATENCY-1:1]};

        mlkem_w10_reg <= {uvw_i.w10_i[MLKEM_REG_SIZE-1:0], mlkem_w10_reg[MLKEM_BF_STAGE1_LATENCY-1:1]};
        mlkem_w11_reg <= {uvw_i.w11_i[MLKEM_REG_SIZE-1:0], mlkem_w11_reg[MLKEM_BF_STAGE1_LATENCY-1:1]};
    end
end

assign pwo_mode = (mode inside {pwm, pwa, pws});
assign gs_mode = (mode == gs);
assign pairwm_mode = mlkem & (mode == pairwm);

//Input assignments - TODO: add input flops for u, v, w, and rnd?
always_comb begin
    if (pwo_mode | pairwm_mode) begin
        u00 = pw_uvw_i.u0_i;
        v00 = pw_uvw_i.v0_i;
        w00 = pw_uvw_i.w0_i;

        u01 = pw_uvw_i.u1_i;
        v01 = pw_uvw_i.v1_i;
        w01 = pw_uvw_i.w1_i;

        u10 = pw_uvw_i.u2_i;
        v10 = pw_uvw_i.v2_i;
        w10 = pw_uvw_i.w2_i;

        u11 = pw_uvw_i.u3_i;
        v11 = pw_uvw_i.v3_i;
        w11 = pw_uvw_i.w3_i;
    end
    else begin
        u00 = uvw_i.u00_i;
        v00 = uvw_i.v00_i;
        w00 = uvw_i.w00_i;

        u01 = uvw_i.u01_i;
        v01 = uvw_i.v01_i;
        w01 = uvw_i.w01_i;

        u10 = u10_int;
        v10 = v10_int;
        w10 = mlkem ? NTT_REG_SIZE'(mlkem_w10_reg[0]) : mldsa_w10_reg[0];

        u11 = u11_int;
        v11 = v11_int;
        w11 = mlkem ? NTT_REG_SIZE'(mlkem_w11_reg[0]) : mldsa_w11_reg[0];
    end
end



//----------------------------------------------------
//MLDSA/MLKEM - BFU stage 1 - Used in all other modes
//----------------------------------------------------
//BF taps for Karatsuba pairwm: m0/m1 per pair from each BF's reduced MLKEM mult.
logic [NTT_REG_SIZE-1:0] bf00_pairwm_mul_red, bf01_pairwm_mul_red;
logic [NTT_REG_SIZE-1:0] bf10_pairwm_mul_red, bf11_pairwm_mul_red;

ntt_butterfly #(
    .REG_SIZE(NTT_REG_SIZE)
) bf_inst00 (
    .clk(clk),
    .reset_n(reset_n),
    .zeroize(zeroize),
    .mode(mode),
    .mlkem(mlkem),
    .opu_i(intt_passthrough ? u00 : u00),
    .opv_i(intt_passthrough ? u01 : v00),
    .opw_i(intt_passthrough ? NTT_REG_SIZE'(uvw_i.w10_i[MLKEM_REG_SIZE-1:0]) : w00),
    .accumulate(accumulate),
    .u_o(u10_int),
    .v_o(u11_int),
    .pwm_res_o(mldsa_pwo_uv_o.uv0),
    .pairwm_mul_red_o(bf00_pairwm_mul_red)
);

ntt_butterfly #(
    .REG_SIZE(NTT_REG_SIZE)
) bf_inst01 (
    .clk(clk),
    .reset_n(reset_n),
    .zeroize(zeroize),
    .mode(mode),
    .mlkem(mlkem),
    .opu_i(intt_passthrough ? v00 : u01),
    .opv_i(intt_passthrough ? v01 : v01),
    .opw_i(intt_passthrough ? NTT_REG_SIZE'(uvw_i.w11_i[MLKEM_REG_SIZE-1:0]) : w01),
    .accumulate(accumulate),
    .u_o(v10_int),
    .v_o(v11_int),
    .pwm_res_o(mldsa_pwo_uv_o.uv1),
    .pairwm_mul_red_o(bf01_pairwm_mul_red)
);

//----------------------------------------------------
//MLDSA/MLKEM - BFU stage 2
//----------------------------------------------------
logic [NTT_REG_SIZE-1:0] u20_int, v20_int, u21_int, v21_int;
logic [MLKEM_BF_STAGE1_LATENCY-1:0][NTT_REG_SIZE-1:0] u10_reg, u11_reg;
logic [MLKEM_BF_STAGE1_LATENCY-1:0][NTT_REG_SIZE-1:0] v10_reg, v11_reg;

always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        u10_reg <= '0;
        u11_reg <= '0;

        v10_reg <= '0;
        v11_reg <= '0;
    end
    else if (zeroize) begin
        u10_reg <= '0;
        u11_reg <= '0;

        v10_reg <= '0;
        v11_reg <= '0;
    end
    else begin
        u10_reg <= {u10, u10_reg[MLKEM_BF_STAGE1_LATENCY-1:1]};
        u11_reg <= {u11, u11_reg[MLKEM_BF_STAGE1_LATENCY-1:1]};

        v10_reg <= {v10, v10_reg[MLKEM_BF_STAGE1_LATENCY-1:1]};
        v11_reg <= {v11, v11_reg[MLKEM_BF_STAGE1_LATENCY-1:1]};
    end
end

logic [NTT_REG_SIZE-1:0] bf_opu10, bf_opv10, bf_opw10;
logic [NTT_REG_SIZE-1:0] bf_opu11, bf_opv11, bf_opw11;

always_comb begin
        //Assign u, v inputs
        bf_opu10 = u10;
        bf_opv10 = v10;

        bf_opu11 = u11;
        bf_opv11 = v11;

        //Assign w inputs
        if (pwo_mode) begin
            bf_opw10 = w10;
            bf_opw11 = w11;
        end
        else if (mlkem) begin
            bf_opw10 = NTT_REG_SIZE'(mlkem_w10_reg[0]);
            bf_opw11 = NTT_REG_SIZE'(mlkem_w11_reg[0]);
        end
        else begin
            bf_opw10 = mldsa_w10_reg[0];
            bf_opw11 = mldsa_w11_reg[0];
        end
end

ntt_butterfly #(
    .REG_SIZE(NTT_REG_SIZE)
) bf_inst10 (
    .clk(clk),
    .reset_n(reset_n),
    .zeroize(zeroize),
    .mode(mode),
    .mlkem(mlkem),
    .opu_i(bf_opu10),
    .opv_i(bf_opv10),
    .opw_i(bf_opw10),
    .accumulate(accumulate),
    .u_o(u20_int),
    .v_o(v20_int),
    .pwm_res_o(mldsa_pwo_uv_o.uv2),
    .pairwm_mul_red_o(bf10_pairwm_mul_red)
);

ntt_butterfly #(
    .REG_SIZE(NTT_REG_SIZE)
) bf_inst11 (
    .clk(clk),
    .reset_n(reset_n),
    .zeroize(zeroize),
    .mode(mode),
    .mlkem(mlkem),
    .opu_i(bf_opu11),
    .opv_i(bf_opv11),
    .opw_i(bf_opw11),
    .accumulate(accumulate),
    .u_o(u21_int),
    .v_o(v21_int),
    .pwm_res_o(mldsa_pwo_uv_o.uv3),
    .pairwm_mul_red_o(bf11_pairwm_mul_red)
);

always_comb begin
    uv_o.u20_o =    ntt_passthrough ? u10_reg[0]
                 : intt_passthrough ? u10_reg[0]
                                    : u20_int;
    uv_o.v20_o =    ntt_passthrough ? v10_reg[0]
                 : intt_passthrough ? u11_reg[0]
                                    : v20_int;

    uv_o.u21_o =    ntt_passthrough ? u11_reg[0]
                 : intt_passthrough ? v10_reg[0]
                                    : u21_int;
    uv_o.v21_o =    ntt_passthrough ? v11_reg[0]
                 : intt_passthrough ? v11_reg[0]
                                    : v21_int;
end

//----------------------------------------------------
//MLKEM - PairWM
//----------------------------------------------------
mlkem_pwo_uvwzi_t pairwm_uvw01_i, pairwm_uvw23_i;
mlkem_pwo_t pairwm_uv01_o, pairwm_uv23_o;

always_comb begin
    if (pairwm_mode) begin
        pairwm_uvw01_i.u0_i = pw_uvw_i.u0_i[MLKEM_REG_SIZE-1:0];
        pairwm_uvw01_i.v0_i = pw_uvw_i.v0_i[MLKEM_REG_SIZE-1:0];
        pairwm_uvw01_i.w0_i = pw_uvw_i.w0_i[MLKEM_REG_SIZE-1:0];

        pairwm_uvw01_i.u1_i = pw_uvw_i.u1_i[MLKEM_REG_SIZE-1:0];
        pairwm_uvw01_i.v1_i = pw_uvw_i.v1_i[MLKEM_REG_SIZE-1:0];
        pairwm_uvw01_i.w1_i = pw_uvw_i.w1_i[MLKEM_REG_SIZE-1:0];

        pairwm_uvw23_i.u0_i = pw_uvw_i.u2_i[MLKEM_REG_SIZE-1:0];
        pairwm_uvw23_i.v0_i = pw_uvw_i.v2_i[MLKEM_REG_SIZE-1:0];
        pairwm_uvw23_i.w0_i = pw_uvw_i.w2_i[MLKEM_REG_SIZE-1:0];

        pairwm_uvw23_i.u1_i = pw_uvw_i.u3_i[MLKEM_REG_SIZE-1:0];
        pairwm_uvw23_i.v1_i = pw_uvw_i.v3_i[MLKEM_REG_SIZE-1:0];
        pairwm_uvw23_i.w1_i = pw_uvw_i.w3_i[MLKEM_REG_SIZE-1:0];
    end
    else begin
        pairwm_uvw01_i = '0;
        pairwm_uvw23_i = '0;
    end
end

//MLKEM Karatsuba pair-wise multiplier. BFs provide m0/m1; this module computes m2 and m1*zeta.
ntt_karatsuba_pairwm mlkem_pawm_inst0 (
    .clk(clk),
    .reset_n(reset_n),
    .zeroize(zeroize),
    .accumulate(accumulate),
    .pwo_uvw_i(pairwm_uvw01_i),
    .pwo_z_i(mlkem_pairwm_zeta13_i.z0_i),
    .m0_red_i(bf00_pairwm_mul_red[MLKEM_REG_SIZE-1:0]),
    .m1_red_i(bf01_pairwm_mul_red[MLKEM_REG_SIZE-1:0]),
    .pwo_uv_o(pairwm_uv01_o)
);

ntt_karatsuba_pairwm mlkem_pawm_inst1 (
    .clk(clk),
    .reset_n(reset_n),
    .zeroize(zeroize),
    .accumulate(accumulate),
    .pwo_uvw_i(pairwm_uvw23_i),
    .pwo_z_i(mlkem_pairwm_zeta13_i.z1_i),
    .m0_red_i(bf10_pairwm_mul_red[MLKEM_REG_SIZE-1:0]),
    .m1_red_i(bf11_pairwm_mul_red[MLKEM_REG_SIZE-1:0]),
    .pwo_uv_o(pairwm_uv23_o)
);

always_comb begin
    pwo_uv_o.uv0 = pairwm_mode ? NTT_REG_SIZE'(pairwm_uv01_o.uv0_o) : mldsa_pwo_uv_o.uv0;
    pwo_uv_o.uv1 = pairwm_mode ? NTT_REG_SIZE'(pairwm_uv01_o.uv1_o) : mldsa_pwo_uv_o.uv1;
    pwo_uv_o.uv2 = pairwm_mode ? NTT_REG_SIZE'(pairwm_uv23_o.uv0_o) : mldsa_pwo_uv_o.uv2;
    pwo_uv_o.uv3 = pairwm_mode ? NTT_REG_SIZE'(pairwm_uv23_o.uv1_o) : mldsa_pwo_uv_o.uv3;
end

//----------------------------------------------------
//Determine when results are ready
//----------------------------------------------------

    logic [BF_LATENCY-1:0] ready_reg;

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            ready_reg <= 'b0;
        else if (zeroize)
            ready_reg <= 'b0;
        else begin
            if (mlkem) begin
                unique case(mode)
                    ct: ready_reg <= {{(BF_LATENCY-MLKEM_BF_LATENCY){1'b0}}, enable, ready_reg[MLKEM_BF_LATENCY-1:1]};
                    gs: ready_reg <= {{(BF_LATENCY-MLKEM_BF_LATENCY){1'b0}}, enable, ready_reg[MLKEM_BF_LATENCY-1:1]};
                    pwm: ready_reg <= 'b0;
                    pwa: ready_reg <= {{BF_LATENCY-1{1'b0}}, enable};
                    pws: ready_reg <= {{BF_LATENCY-1{1'b0}}, enable};
                    pairwm: ready_reg <= accumulate ? {{(BF_LATENCY-MLKEM_PAIRWM_ACC_LATENCY){1'b0}}, enable, ready_reg[MLKEM_PAIRWM_ACC_LATENCY-1:1]}
                                                   : {{(BF_LATENCY-MLKEM_PAIRWM_LATENCY){1'b0}}, enable, ready_reg[MLKEM_PAIRWM_LATENCY-1:1]};
                    default: ready_reg <= 'b0;
                endcase
            end
            else begin
                unique case(mode)
                    ct: ready_reg <= {enable, ready_reg[BF_LATENCY-1:1]};
                    gs: ready_reg <= {enable, ready_reg[BF_LATENCY-1:1]};
                    pwm: ready_reg <= accumulate ? {{(BF_LATENCY-PWM_LATENCY){1'b0}}, enable, ready_reg[PWM_LATENCY-1:1]} : {{(BF_LATENCY-(PWM_LATENCY-1)){1'b0}}, enable, ready_reg[PWM_LATENCY-2:1]};
                    pwa: ready_reg <= {{BF_LATENCY-1{1'b0}}, enable};
                    pws: ready_reg <= {{BF_LATENCY-1{1'b0}}, enable};
                    pairwm: ready_reg <= 'b0;
                    default: ready_reg <= 'b0;
                endcase
            end
        end
    end

    assign ready_o = ready_reg[0];

endmodule
