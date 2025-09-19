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
// This module consists of masked PWMs, followed by 1st stage of masked and unmasked BFUs followed by
// 2nd stage of unmasked BFUs. In case of masking_en, PWMs are triggered and 
// masked branch is taken for computing 1st stage outputs. In case of unmasked operation, 
// both branches are enabled but unmasked outputs are passed to next stage. Final outputs are 23-bit values

module ntt_hybrid_butterfly_2x2
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

    input mode_t mode,
    input wire enable,
    input wire masking_en,
    input wire shuffle_en,
    input wire mlkem,
    input bf_uvwi_t uvw_i,      //Inputs are original form
    input pwo_uvwi_t pw_uvw_i,  //PWO inputs are original form - reuse for MLKEM PairWM
    input pwm_shares_uvwi_t pwm_shares_uvw_i, //masked PWM/PairWM inputs
    input wire [4:0][WIDTH-1:0] rnd_i,
    input wire accumulate,
    input masked_intt_uvwi_t bf_shares_uvw_i, //masked INTT inputs
    input mlkem_pairwm_zeta_t mlkem_pairwm_zeta13_i,
    input mlkem_masked_pairwm_zeta_shares_t mlkem_shares_pairwm_zeta13_i,
    input wire ntt_passthrough,
    input wire intt_passthrough,

    output bf_uvo_t uv_o,       //Outputs are original form
    output pwo_t pwo_uv_o,
    output pwm_shares_uvo_t pwm_shares_uvo, //masked PWM output
    output logic ready_o
);

//----------------------
//Unmasked wires
//----------------------
//Inputs to 1st stage
logic [HALF_WIDTH-1:0] u00, u01, v00, v01;
logic [HALF_WIDTH-1:0] w00, w01, w10, w11;
//Outputs of 1st stage
logic [HALF_WIDTH-1:0] u10_int, u11_int, v10_int, v11_int;
//Inputs to 2nd stage
logic [HALF_WIDTH-1:0] u10, u11, v10, v11;

pwo_t mldsa_pwo_uv_o;

logic gs_mode;
logic pairwm_mode;

//Other internal wires
logic [UNMASKED_BF_STAGE1_LATENCY-1:0][HALF_WIDTH-1:0] mldsa_w10_reg, mldsa_w11_reg; //Shift w10 by 5 cycles to match 1st stage BF latency
logic [MLKEM_UNMASKED_BF_STAGE1_LATENCY-1:0][MLKEM_REG_SIZE-1:0] mlkem_w10_reg, mlkem_w11_reg;
logic [MASKED_BF_STAGE1_LATENCY-1:0][HALF_WIDTH-1:0] masked_w10_reg, masked_w11_reg;
logic [MLKEM_MASKED_BF_STAGE1_LATENCY-1:0][HALF_WIDTH-1:0] mlkem_masked_w10_reg, mlkem_masked_w11_reg;
logic pwo_mode, masked_pwm_mode;

//Shares - TODO replace with struct?
logic [1:0][WIDTH-1:0] u00_share, u01_share, v00_share, v01_share, u10_share, v10_share, u11_share, v11_share;
logic [1:0][WIDTH-1:0] w00_share, w01_share, w10_share, w11_share;
logic [1:0][WIDTH-1:0] uv00_share, uv01_share, uv10_share, uv11_share;
logic [1:0][WIDTH-1:0] uv00_share_reg, uv01_share_reg, uv10_share_reg, uv11_share_reg;
logic [1:0][WIDTH-1:0] twiddle_w00_share, twiddle_w01_share;
bf_uvo_t mldsa_masked_gs_stage1_uvo, mlkem_masked_gs_stage1_uvo;

//pwm output shares
logic [1:0][WIDTH-1:0] mldsa_uv0_share, mldsa_uv1_share;
pwm_shares_uvo_t bf_pwm_shares_uvo;

//zeta shares for pairwm
logic [1:0][MLKEM_MASKED_WIDTH-1:0] z0_share, z1_share;
//pairwm output shares
logic [1:0][MLKEM_MASKED_WIDTH-1:0] mlkem_uv0_share, mlkem_uv1_share, mlkem_uv2_share, mlkem_uv3_share;

//w delay flops
//Flop the twiddle factor 5x to correctly pass in values to the 2nd set of bf units
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
        mldsa_w10_reg <= {uvw_i.w10_i, mldsa_w10_reg[UNMASKED_BF_STAGE1_LATENCY-1:1]};
        mldsa_w11_reg <= {uvw_i.w11_i, mldsa_w11_reg[UNMASKED_BF_STAGE1_LATENCY-1:1]};

        mlkem_w10_reg <= {uvw_i.w10_i[MLKEM_REG_SIZE-1:0], mlkem_w10_reg[MLKEM_UNMASKED_BF_STAGE1_LATENCY-1:1]};
        mlkem_w11_reg <= {uvw_i.w11_i[MLKEM_REG_SIZE-1:0], mlkem_w11_reg[MLKEM_UNMASKED_BF_STAGE1_LATENCY-1:1]};
    end
end

//TODO: optimize by removing this flop and delaying twiddle addr?
always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        masked_w10_reg <= 'h0;
    end
    else if (zeroize) begin
        masked_w10_reg <= 'h0;
    end
    else begin
        masked_w10_reg <= {bf_shares_uvw_i.w10_i, masked_w10_reg[MASKED_BF_STAGE1_LATENCY-1:1]};
    end
end

assign masked_w11_reg = masked_w10_reg; //used only in masked INTT, both are equal, so can opt num of flops

assign pwo_mode = (mode inside {pwm, pwa, pws});
assign masked_pwm_mode = (mode == pwm) & masking_en;
assign gs_mode = (mode == gs);
assign pairwm_mode = mlkem & (mode == pairwm);

//Input assignments - TODO: add input flops for u, v, w, and rnd?
always_comb begin
    if (pwo_mode) begin
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
    else begin //Only applies to unmasked ops since in masking, intt receives inputs from pwm and not from the API
        u00 = uvw_i.u00_i;
        v00 = uvw_i.v00_i;
        w00 = uvw_i.w00_i;

        u01 = uvw_i.u01_i;
        v01 = uvw_i.v01_i;
        w01 = uvw_i.w01_i;

        u10 = (masking_en & intt_passthrough) ? mlkem_masked_gs_stage1_uvo.u20_o : u10_int;
        v10 = (masking_en & intt_passthrough) ? mlkem_masked_gs_stage1_uvo.v20_o : v10_int;
        w10 = mlkem ? HALF_WIDTH'(mlkem_w10_reg[0]) : mldsa_w10_reg[0];

        u11 = (masking_en & intt_passthrough) ? mlkem_masked_gs_stage1_uvo.u21_o : u11_int;
        v11 = (masking_en & intt_passthrough) ? mlkem_masked_gs_stage1_uvo.v21_o : v11_int;
        w11 = mlkem ? HALF_WIDTH'(mlkem_w11_reg[0]) : mldsa_w11_reg[0];
    end
end

always_comb begin
    u00_share = pwm_shares_uvw_i.u0_i;
    u01_share = pwm_shares_uvw_i.u1_i;
    u10_share = pwm_shares_uvw_i.u2_i;
    u11_share = pwm_shares_uvw_i.u3_i;

    v00_share = pwm_shares_uvw_i.v0_i;
    v01_share = pwm_shares_uvw_i.v1_i;
    v10_share = pwm_shares_uvw_i.v2_i;
    v11_share = pwm_shares_uvw_i.v3_i;

    w00_share = pwm_shares_uvw_i.w0_i;
    w01_share = pwm_shares_uvw_i.w1_i;
    w10_share = pwm_shares_uvw_i.w2_i;
    w11_share = pwm_shares_uvw_i.w3_i;

    z0_share  = pairwm_mode ? mlkem_shares_pairwm_zeta13_i.z0_i : '0;
    z1_share  = pairwm_mode ? mlkem_shares_pairwm_zeta13_i.z1_i : '0;
end

//----------------------------------------------------
//Masked PWMs - Used in masked PWM+INTT mode only - 210 clks
//----------------------------------------------------
ntt_masked_pwm #(
    .WIDTH(WIDTH)
) pwm_inst00 (
    .clk(clk),
    .reset_n(reset_n),
    .zeroize(zeroize),
    .accumulate(accumulate),
    .u(u00_share),
    .v(v00_share),
    .w(w00_share),
    .rnd({rnd_i[4], rnd_i[3], rnd_i[2], rnd_i[1], rnd_i[0]}),
    .res(mldsa_uv0_share)
);

ntt_masked_pwm #(
    .WIDTH(WIDTH)
) pwm_inst01 (
    .clk(clk),
    .reset_n(reset_n),
    .zeroize(zeroize),
    .accumulate(accumulate),
    .u(u01_share),
    .v(v01_share),
    .w(w01_share),
    .rnd({rnd_i[0], rnd_i[4], rnd_i[3], rnd_i[2], rnd_i[1]}),
    .res(mldsa_uv1_share)
);

//---------------------------
//Refresh randomness
//---------------------------
always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        for (int i = 0; i < 2; i++) begin
            uv00_share_reg[i] <= 'h0;
            uv01_share_reg[i] <= 'h0;
            uv10_share_reg[i] <= 'h0;
            uv11_share_reg[i] <= 'h0;

            twiddle_w00_share[i]     <= 'h0;
            twiddle_w01_share[i]     <= 'h0;
        end
    end
    else if (zeroize) begin
        for (int i = 0; i < 2; i++) begin
            uv00_share_reg[i] <= 'h0;
            uv01_share_reg[i] <= 'h0;
            uv10_share_reg[i] <= 'h0;
            uv11_share_reg[i] <= 'h0;

            twiddle_w00_share[i]     <= 'h0;
            twiddle_w01_share[i]     <= 'h0;
        end
    end
    else begin
        uv00_share_reg <= bf_shares_uvw_i.u00_i;
        uv01_share_reg <= (gs_mode & masking_en & !intt_passthrough) ? bf_shares_uvw_i.v00_i : bf_shares_uvw_i.u01_i;
        uv10_share_reg <= (gs_mode & masking_en & !intt_passthrough) ? bf_shares_uvw_i.u01_i : bf_shares_uvw_i.v00_i;
        uv11_share_reg <= bf_shares_uvw_i.v01_i;

        //In passthrough mode, 1st stage is used instead of bypassed and 2nd stage is bypassed. Swap twiddles to ensure correct output
        twiddle_w00_share[0] <= intt_passthrough ? WIDTH'(bf_shares_uvw_i.w10_i - rnd_i[0][HALF_WIDTH-1:0]) : bf_shares_uvw_i.w00_i[0];
        twiddle_w00_share[1] <= intt_passthrough ? WIDTH'(rnd_i[0][HALF_WIDTH-1:0]) : bf_shares_uvw_i.w00_i[1];

        twiddle_w01_share[0] <= intt_passthrough ? WIDTH'(bf_shares_uvw_i.w11_i - rnd_i[0][HALF_WIDTH-1:0]) : bf_shares_uvw_i.w01_i[0];
        twiddle_w01_share[1] <= intt_passthrough ? WIDTH'(rnd_i[0][HALF_WIDTH-1:0]) : bf_shares_uvw_i.w01_i[1];
    end
end

//----------------------------------------------------
//MLDSA Masked BFU stage 1 - Used in masked PWM/INTT mode only - 264 clks
//PWM outputs: uv00[1:0], uv01[1:0], uv10[1:0], uv11[1:0]
//----------------------------------------------------
ntt_masked_butterfly1x2 #(
    .WIDTH(WIDTH)
) masked_bf_1x2_inst0 (
    .clk(clk),
    .reset_n(reset_n),
    .zeroize(zeroize),
    .uvw_i(masked_pwm_mode ? {u10_share, u11_share, v10_share, v11_share, w10_share, w11_share} : {uv00_share_reg, uv10_share_reg, uv01_share_reg, uv11_share_reg, twiddle_w00_share, twiddle_w01_share}),
    .rnd_i({rnd_i[1], rnd_i[0], rnd_i[4], rnd_i[3], rnd_i[2]}),
    .mode(mode),
    .accumulate(accumulate),
    .uv_o(mldsa_masked_gs_stage1_uvo),
    .bf_pwm_uv_o(bf_pwm_shares_uvo)
);

//----------------------------------------------------
//MLKEM Masked BFU stage 1 - Used in MLKEM masked INTT mode only - 16 clks
//----------------------------------------------------
ntt_mlkem_masked_butterfly1x2 mlkem_masked_bf_1x2_inst0 
(
    .clk(clk),
    .reset_n(reset_n),
    .zeroize(zeroize),
    .uvw_i({{uv00_share_reg[1][MLKEM_MASKED_WIDTH-1:0], uv00_share_reg[0][MLKEM_MASKED_WIDTH-1:0]},
            {uv10_share_reg[1][MLKEM_MASKED_WIDTH-1:0], uv10_share_reg[0][MLKEM_MASKED_WIDTH-1:0]}, 
            {uv01_share_reg[1][MLKEM_MASKED_WIDTH-1:0], uv01_share_reg[0][MLKEM_MASKED_WIDTH-1:0]}, 
            {uv11_share_reg[1][MLKEM_MASKED_WIDTH-1:0], uv11_share_reg[0][MLKEM_MASKED_WIDTH-1:0]}, 
            {twiddle_w00_share[1][MLKEM_MASKED_WIDTH-1:0], twiddle_w00_share[0][MLKEM_MASKED_WIDTH-1:0]}, 
            {twiddle_w01_share[1][MLKEM_MASKED_WIDTH-1:0], twiddle_w01_share[0][MLKEM_MASKED_WIDTH-1:0]}}),
    .rnd_i({rnd_i[1][13:0], rnd_i[0][13:0], rnd_i[4][13:0], rnd_i[3][13:0], rnd_i[2][13:0]}),
    .uv_o(mlkem_masked_gs_stage1_uvo)
);

//----------------------------------------------------
//MLDSA/MLKEM - Unmasked BFU stage 1 - Used in all other modes
//----------------------------------------------------
ntt_butterfly #(
    .REG_SIZE(HALF_WIDTH)
) unmasked_bf_inst00 (
    .clk(clk),
    .reset_n(reset_n),
    .zeroize(zeroize),
    .mode(mode),
    .mlkem(mlkem),
    .opu_i(masking_en ? HALF_WIDTH'(0) : intt_passthrough ? u00 : u00),
    .opv_i(masking_en ? HALF_WIDTH'(0) : intt_passthrough ? u01 : v00),
    .opw_i(masking_en ? HALF_WIDTH'(0) : intt_passthrough ? HALF_WIDTH'(uvw_i.w10_i[MLKEM_REG_SIZE-1:0]) : w00),
    .accumulate(accumulate),
    .u_o(u10_int),
    .v_o(u11_int),
    .pwm_res_o(mldsa_pwo_uv_o.uv0)
);

ntt_butterfly #(
    .REG_SIZE(HALF_WIDTH)
) unmasked_bf_inst01 (
    .clk(clk),
    .reset_n(reset_n),
    .zeroize(zeroize),
    .mode(mode),
    .mlkem(mlkem),
    .opu_i(masking_en ? HALF_WIDTH'(0) : intt_passthrough ? v00 : u01),
    .opv_i(masking_en ? HALF_WIDTH'(0) : intt_passthrough ? v01 : v01),
    .opw_i(masking_en ? HALF_WIDTH'(0) : intt_passthrough ? HALF_WIDTH'(uvw_i.w11_i[MLKEM_REG_SIZE-1:0]) : w01),
    .accumulate(accumulate),
    .u_o(v10_int),
    .v_o(v11_int),
    .pwm_res_o(mldsa_pwo_uv_o.uv1)
);

//----------------------------------------------------
//MLDSA/MLKEM - Unmasked BFU stage 2 - Used in all modes (irrespective of masking_en)
//----------------------------------------------------
logic [HALF_WIDTH-1:0] u20_int, v20_int, u21_int, v21_int;
logic [MLKEM_MASKED_BF_STAGE1_LATENCY-1:0][HALF_WIDTH-1:0] u10_reg, u11_reg;
logic [MLKEM_MASKED_BF_STAGE1_LATENCY-1:0][HALF_WIDTH-1:0] v10_reg, v11_reg;

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
        u10_reg <= {u10, u10_reg[MLKEM_MASKED_BF_STAGE1_LATENCY-1:1]};
        u11_reg <= {u11, u11_reg[MLKEM_MASKED_BF_STAGE1_LATENCY-1:1]};

        v10_reg <= {v10, v10_reg[MLKEM_MASKED_BF_STAGE1_LATENCY-1:1]};
        v11_reg <= {v11, v11_reg[MLKEM_MASKED_BF_STAGE1_LATENCY-1:1]};
    end
end

logic [HALF_WIDTH-1:0] bf_opu10, bf_opv10, bf_opw10;
logic [HALF_WIDTH-1:0] bf_opu11, bf_opv11, bf_opw11;

always_comb begin
    if (masking_en) begin
        //Assign u, v inputs - masked mode
        if (mlkem) begin //during passthrough 2nd stage is not used - assigning inputs to generate noise
            bf_opu10 = mlkem_masked_gs_stage1_uvo.u20_o;
            bf_opv10 = mlkem_masked_gs_stage1_uvo.v20_o;
            bf_opw10 = masked_w10_reg[MASKED_BF_STAGE1_LATENCY-MLKEM_MASKED_BF_STAGE1_LATENCY]; //assuming mldsa bf stage 1 latency > mlkem bf stage 1 latency

            bf_opu11 = mlkem_masked_gs_stage1_uvo.u21_o;
            bf_opv11 = mlkem_masked_gs_stage1_uvo.v21_o;
            bf_opw11 = masked_w11_reg[MASKED_BF_STAGE1_LATENCY-MLKEM_MASKED_BF_STAGE1_LATENCY];
        end
        else begin
            bf_opu10 = mldsa_masked_gs_stage1_uvo.u20_o;
            bf_opv10 = mldsa_masked_gs_stage1_uvo.v20_o;
            bf_opw10 = masked_w10_reg[0];

            bf_opu11 = mldsa_masked_gs_stage1_uvo.u21_o;
            bf_opv11 = mldsa_masked_gs_stage1_uvo.v21_o;
            bf_opw11 = masked_w11_reg[0];
        end

    end
    else begin
        //Assign u, v inputs - unmasked mode
        bf_opu10 = u10;
        bf_opv10 = v10;

        bf_opu11 = u11;
        bf_opv11 = v11;

        //Assign w inputs - unmasked mode
        if (pwo_mode) begin
            bf_opw10 = w10;
            bf_opw11 = w11;
        end
        else if (mlkem) begin
            bf_opw10 = HALF_WIDTH'(mlkem_w10_reg[0]);
            bf_opw11 = HALF_WIDTH'(mlkem_w11_reg[0]);
        end
        else begin
            bf_opw10 = mldsa_w10_reg[0];
            bf_opw11 = mldsa_w11_reg[0];
        end
        
    end
end

ntt_butterfly #(
    .REG_SIZE(HALF_WIDTH)
) unmasked_bf_inst10 (
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
    .pwm_res_o(mldsa_pwo_uv_o.uv2)
);

ntt_butterfly #(
    .REG_SIZE(HALF_WIDTH)
) unmasked_bf_inst11 (
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
    .pwm_res_o(mldsa_pwo_uv_o.uv3)
);

always_comb begin
    uv_o.u20_o = ntt_passthrough ? u10_reg[MLKEM_MASKED_BF_STAGE1_LATENCY-MLKEM_UNMASKED_BF_STAGE1_LATENCY] 
                 : intt_passthrough ? masking_en ? u10 : u10_reg[MLKEM_MASKED_BF_STAGE1_LATENCY-MLKEM_UNMASKED_BF_STAGE1_LATENCY]
                                 : u20_int;
    uv_o.v20_o = ntt_passthrough ? v10_reg[MLKEM_MASKED_BF_STAGE1_LATENCY-MLKEM_UNMASKED_BF_STAGE1_LATENCY]
                 : intt_passthrough ? masking_en ? u11 : u11_reg[MLKEM_MASKED_BF_STAGE1_LATENCY-MLKEM_UNMASKED_BF_STAGE1_LATENCY]
                                 : v20_int;

    uv_o.u21_o = ntt_passthrough ? u11_reg[MLKEM_MASKED_BF_STAGE1_LATENCY-MLKEM_UNMASKED_BF_STAGE1_LATENCY] 
                 : intt_passthrough ? masking_en ? v10 : v10_reg[MLKEM_MASKED_BF_STAGE1_LATENCY-MLKEM_UNMASKED_BF_STAGE1_LATENCY]
                                 : u21_int;
    uv_o.v21_o = ntt_passthrough ? v11_reg[MLKEM_MASKED_BF_STAGE1_LATENCY-MLKEM_UNMASKED_BF_STAGE1_LATENCY] 
                 : intt_passthrough ? masking_en ? v11 : v11_reg[MLKEM_MASKED_BF_STAGE1_LATENCY-MLKEM_UNMASKED_BF_STAGE1_LATENCY]
                                 : v21_int;
end

//----------------------------------------------------
//MLKEM - Unmasked PairWM
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

ntt_karatsuba_pairwm mlkem_pawm_inst0 (
    .clk(clk),
    .reset_n(reset_n),
    .zeroize(zeroize),
    .accumulate(accumulate),
    .pwo_uvw_i(pairwm_uvw01_i),
    .pwo_z_i(mlkem_pairwm_zeta13_i.z0_i),
    .pwo_uv_o(pairwm_uv01_o)
);

ntt_karatsuba_pairwm mlkem_pawm_inst1 (
    .clk(clk),
    .reset_n(reset_n),
    .zeroize(zeroize),
    .accumulate(accumulate),
    .pwo_uvw_i(pairwm_uvw23_i),
    .pwo_z_i(mlkem_pairwm_zeta13_i.z1_i),
    .pwo_uv_o(pairwm_uv23_o)
);

always_comb begin
    pwo_uv_o.uv0 = pairwm_mode ? HALF_WIDTH'(pairwm_uv01_o.uv0_o) : mldsa_pwo_uv_o.uv0;
    pwo_uv_o.uv1 = pairwm_mode ? HALF_WIDTH'(pairwm_uv01_o.uv1_o) : mldsa_pwo_uv_o.uv1;
    pwo_uv_o.uv2 = pairwm_mode ? HALF_WIDTH'(pairwm_uv23_o.uv0_o) : mldsa_pwo_uv_o.uv2;
    pwo_uv_o.uv3 = pairwm_mode ? HALF_WIDTH'(pairwm_uv23_o.uv1_o) : mldsa_pwo_uv_o.uv3;
end

//----------------------------------------------------
//MLKEM - Unmasked PairWM - TODO: check input/output widths
//----------------------------------------------------
ntt_masked_pairwm mlkem_masked_pawm_inst0 (
    .clk(clk),
    .reset_n(reset_n),
    .zeroize(zeroize),
    .accumulate(accumulate),
    .u0({u00_share[1][MLKEM_MASKED_WIDTH-1:0], u00_share[0][MLKEM_MASKED_WIDTH-1:0]}),
    .v0({v00_share[1][MLKEM_MASKED_WIDTH-1:0], v00_share[0][MLKEM_MASKED_WIDTH-1:0]}),
    .w0({w00_share[1][MLKEM_MASKED_WIDTH-1:0], w00_share[0][MLKEM_MASKED_WIDTH-1:0]}),
    .u1({u01_share[1][MLKEM_MASKED_WIDTH-1:0], u01_share[0][MLKEM_MASKED_WIDTH-1:0]}),
    .v1({v01_share[1][MLKEM_MASKED_WIDTH-1:0], v01_share[0][MLKEM_MASKED_WIDTH-1:0]}),
    .w1({w01_share[1][MLKEM_MASKED_WIDTH-1:0], w01_share[0][MLKEM_MASKED_WIDTH-1:0]}),
    .zeta(z0_share),
    .rnd({rnd_i[4][13:0], rnd_i[3][13:0], rnd_i[2][13:0], rnd_i[1][13:0], rnd_i[0][13:0]}),
    .rnd_24bit({rnd_i[0][37:14]}),
    .res0(mlkem_uv0_share),
    .res1(mlkem_uv1_share)
);

ntt_masked_pairwm mlkem_masked_pawm_inst1 (
    .clk(clk),
    .reset_n(reset_n),
    .zeroize(zeroize),
    .accumulate(accumulate),
    .u0({u10_share[1][MLKEM_MASKED_WIDTH-1:0], u10_share[0][MLKEM_MASKED_WIDTH-1:0]}),
    .v0({v10_share[1][MLKEM_MASKED_WIDTH-1:0], v10_share[0][MLKEM_MASKED_WIDTH-1:0]}),
    .w0({w10_share[1][MLKEM_MASKED_WIDTH-1:0], w10_share[0][MLKEM_MASKED_WIDTH-1:0]}),
    .u1({u11_share[1][MLKEM_MASKED_WIDTH-1:0], u11_share[0][MLKEM_MASKED_WIDTH-1:0]}),
    .v1({v11_share[1][MLKEM_MASKED_WIDTH-1:0], v11_share[0][MLKEM_MASKED_WIDTH-1:0]}),
    .w1({w11_share[1][MLKEM_MASKED_WIDTH-1:0], w11_share[0][MLKEM_MASKED_WIDTH-1:0]}),
    .zeta(z1_share),
    .rnd({rnd_i[0][13:0], rnd_i[4][13:0], rnd_i[3][13:0], rnd_i[2][13:0], rnd_i[1][13:0]}),
    .rnd_24bit({rnd_i[1][37:14]}),
    .res0(mlkem_uv2_share),
    .res1(mlkem_uv3_share)
);

//Assign PWM output
always_comb begin
    pwm_shares_uvo.uv0 = pairwm_mode ? {WIDTH'(mlkem_uv0_share[1]), WIDTH'(mlkem_uv0_share[0])} : mldsa_uv0_share;
    pwm_shares_uvo.uv1 = pairwm_mode ? {WIDTH'(mlkem_uv1_share[1]), WIDTH'(mlkem_uv1_share[0])} : mldsa_uv1_share;
    pwm_shares_uvo.uv2 = pairwm_mode ? {WIDTH'(mlkem_uv2_share[1]), WIDTH'(mlkem_uv2_share[0])} : bf_pwm_shares_uvo.uv2;
    pwm_shares_uvo.uv3 = pairwm_mode ? {WIDTH'(mlkem_uv3_share[1]), WIDTH'(mlkem_uv3_share[0])} : bf_pwm_shares_uvo.uv3;
end

//----------------------------------------------------
//Determine when results are ready
//----------------------------------------------------
//ready_o logic

// `ifdef MLDSA_NTT_MASKING //TODO: optimize shift reg size based on masking en/dis
    logic [MASKED_INTT_LATENCY-1:0] masked_ready_reg; //masked INTT is longest op

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            masked_ready_reg <= 'b0;
        else if (zeroize)
            masked_ready_reg <= 'b0;
        else begin
            if (mlkem) begin
                unique case(mode)
                    ct: masked_ready_reg <= {{(MASKED_INTT_LATENCY-MLKEM_UNMASKED_BF_LATENCY){1'b0}}, enable, masked_ready_reg[MLKEM_UNMASKED_BF_LATENCY-1:1]};
                    gs: begin
                        if (masking_en)
                            masked_ready_reg <= {{(MASKED_INTT_LATENCY-MLKEM_MASKED_INTT_LATENCY){1'b0}}, enable, masked_ready_reg[MLKEM_MASKED_INTT_LATENCY-1:1]};
                        else
                            masked_ready_reg <= {{(MASKED_INTT_LATENCY-MLKEM_UNMASKED_BF_LATENCY){1'b0}}, enable, masked_ready_reg[MLKEM_UNMASKED_BF_LATENCY-1:1]};
                    end
                    pwm: masked_ready_reg <= 'b0;
                    pwa: masked_ready_reg <= {{MASKED_INTT_LATENCY-1{1'b0}}, enable};
                    pws: masked_ready_reg <= {{MASKED_INTT_LATENCY-1{1'b0}}, enable};
                    pairwm: begin
                        if (masking_en)
                            masked_ready_reg <= accumulate ? {{(MASKED_INTT_LATENCY-MLKEM_MASKED_PAIRWM_ACC_LATENCY){1'b0}}, enable, masked_ready_reg[MLKEM_MASKED_PAIRWM_ACC_LATENCY-1:1]}
                                                            : {{(MASKED_INTT_LATENCY-MLKEM_MASKED_PAIRWM_LATENCY){1'b0}}, enable, masked_ready_reg[MLKEM_MASKED_PAIRWM_LATENCY-1:1]};
                        else
                            masked_ready_reg <= accumulate ? {{(MASKED_INTT_LATENCY-MLKEM_UNMASKED_PAIRWM_ACC_LATENCY){1'b0}}, enable, masked_ready_reg[MLKEM_UNMASKED_PAIRWM_ACC_LATENCY-1:1]}
                                                                               : {{(MASKED_INTT_LATENCY-MLKEM_UNMASKED_PAIRWM_LATENCY){1'b0}}, enable, masked_ready_reg[MLKEM_UNMASKED_PAIRWM_LATENCY-1:1]};
                    end
                    default: masked_ready_reg <= 'b0;
                endcase
            end
            else begin
                unique case(mode) //270:0 delay flop for enable
                    //Add masking_en mux for gs, pwm modes
                    ct:  masked_ready_reg <= {{(MASKED_INTT_LATENCY-UNMASKED_BF_LATENCY){1'b0}}, enable, masked_ready_reg[UNMASKED_BF_LATENCY-1:1]};
                    gs: begin 
                        if (masking_en)
                            masked_ready_reg <= {1'b0, enable, masked_ready_reg[MASKED_INTT_LATENCY-1:1]};
                        else
                            masked_ready_reg <= {{(MASKED_INTT_LATENCY-UNMASKED_BF_LATENCY){1'b0}}, enable, masked_ready_reg[UNMASKED_BF_LATENCY-1:1]};
                    end
                    pwm: begin
                        if (masking_en) begin
                            if (shuffle_en)
                                masked_ready_reg <= accumulate ? {{(MASKED_INTT_LATENCY-MASKED_PWM_ACC_LATENCY){1'b0}}, enable, masked_ready_reg[MASKED_PWM_ACC_LATENCY-1:1]} : {{(MASKED_INTT_LATENCY-MASKED_PWM_LATENCY-1){1'b0}}, enable, masked_ready_reg[MASKED_PWM_LATENCY-2:1]};
                            else
                                masked_ready_reg <= accumulate ? {{(MASKED_INTT_LATENCY-MASKED_PWM_ACC_LATENCY){1'b0}}, enable, masked_ready_reg[MASKED_PWM_ACC_LATENCY-1:1]} : {{(MASKED_INTT_LATENCY-MASKED_PWM_LATENCY-1){1'b0}}, enable, masked_ready_reg[MASKED_PWM_LATENCY-2:1]};
                        end
                        else
                            masked_ready_reg <= accumulate ? {{(MASKED_INTT_LATENCY-UNMASKED_PWM_LATENCY){1'b0}}, enable, masked_ready_reg[UNMASKED_PWM_LATENCY-1:1]} : {6'h0, enable, masked_ready_reg[UNMASKED_PWM_LATENCY-2:1]};
                    end
                    pwa: masked_ready_reg <= {{MASKED_INTT_LATENCY-1{1'b0}}, enable};
                    pws: masked_ready_reg <= {{MASKED_INTT_LATENCY-1{1'b0}}, enable};
                    pairwm: masked_ready_reg <= 'b0;
                    default: masked_ready_reg <= 'h0;
                endcase
            end
        end
    end

    assign ready_o = masked_ready_reg[0];

endmodule
