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
    input pwm_shares_uvwi_t pwm_shares_uvw_i, //masked PWM inputs
    input wire [4:0][WIDTH-1:0] rnd_i,
    input wire accumulate,
    input masked_intt_uvwi_t bf_shares_uvw_i, //masked INTT inputs
    input mlkem_pairwm_zeta_t mlkem_pairwm_zeta13_i,
    // input mlkem_pairwm_zeta_t mlkem_pairwm_zeta23_i,
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
logic pwo_mode, masked_pwm_mode;

//Shares - TODO replace with struct?
logic [1:0][WIDTH-1:0] u00_share, u01_share, v00_share, v01_share, u10_share, v10_share, u11_share, v11_share;
logic [1:0][WIDTH-1:0] w00_share, w01_share, w10_share, w11_share;
logic [1:0][WIDTH-1:0] uv00_share, uv01_share, uv10_share, uv11_share;
logic [1:0][WIDTH-1:0] uv00_share_reg, uv01_share_reg, uv10_share_reg, uv11_share_reg;
logic [1:0][WIDTH-1:0] twiddle_w00_share, twiddle_w01_share;
bf_uvo_t masked_gs_stage1_uvo;
pwm_shares_uvo_t bf_pwm_shares_uvo;

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

        u10 = u10_int;
        v10 = v10_int;
        w10 = mlkem ? HALF_WIDTH'(mlkem_w10_reg[0]) : mldsa_w10_reg[0];

        u11 = u11_int;
        v11 = v11_int;
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
    .res(pwm_shares_uvo.uv0)
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
    .res(pwm_shares_uvo.uv1)
);

always_comb begin //TODO: optimize
    pwm_shares_uvo.uv2 = bf_pwm_shares_uvo.uv2;
    pwm_shares_uvo.uv3 = bf_pwm_shares_uvo.uv3;
end

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
        uv01_share_reg <= (gs_mode & masking_en) ? bf_shares_uvw_i.v00_i : bf_shares_uvw_i.u01_i;
        uv10_share_reg <= (gs_mode & masking_en) ? bf_shares_uvw_i.u01_i : bf_shares_uvw_i.v00_i;
        uv11_share_reg <= bf_shares_uvw_i.v01_i;

        twiddle_w00_share <= bf_shares_uvw_i.w00_i;
        twiddle_w01_share <= bf_shares_uvw_i.w01_i;
    end
end

//----------------------------------------------------
//Masked BFU stage 1 - Used in masked PWM+INTT mode only - 264 clks
//PWM outputs: uv00[1:0], uv01[1:0], uv10[1:0], uv11[1:0]
//TODO: optimize 2 of the masked PWM multipliers and use 1x2 multipliers instead
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
    .uv_o(masked_gs_stage1_uvo),
    .bf_pwm_uv_o(bf_pwm_shares_uvo)
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
    .opu_i(masking_en ? HALF_WIDTH'(0) : u00),
    .opv_i(masking_en ? HALF_WIDTH'(0) : v00),
    .opw_i(masking_en ? HALF_WIDTH'(0) : w00),
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
    .opu_i(masking_en ? HALF_WIDTH'(0) : u01),
    .opv_i(masking_en ? HALF_WIDTH'(0) : v01),
    .opw_i(masking_en ? HALF_WIDTH'(0) : w01),
    .accumulate(accumulate),
    .u_o(v10_int),
    .v_o(v11_int),
    .pwm_res_o(mldsa_pwo_uv_o.uv1)
);

//----------------------------------------------------
//MLDSA/MLKEM - Unmasked BFU stage 2 - Used in all modes (irrespective of masking_en)
//----------------------------------------------------
logic [HALF_WIDTH-1:0] u20_int, v20_int, u21_int, v21_int;
logic [MLKEM_UNMASKED_BF_STAGE1_LATENCY-1:0][HALF_WIDTH-1:0] u00_reg, u01_reg, u10_reg, u11_reg;
logic [MLKEM_UNMASKED_BF_STAGE1_LATENCY-1:0][HALF_WIDTH-1:0] v00_reg, v01_reg, v10_reg, v11_reg;

always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        u00_reg <= '0;
        u01_reg <= '0;
        u10_reg <= '0;
        u11_reg <= '0;

        v00_reg <= '0;
        v01_reg <= '0;
        v10_reg <= '0;
        v11_reg <= '0;
    end
    else if (zeroize) begin
        u00_reg <= '0;
        u01_reg <= '0;
        u10_reg <= '0;
        u11_reg <= '0;

        v00_reg <= '0;
        v01_reg <= '0;
        v10_reg <= '0;
        v11_reg <= '0;
    end
    else begin
        u00_reg <= {u00_reg[1:0], u00};
        u01_reg <= {u01_reg[1:0], u01};
        u10_reg <= {u10_reg[1:0], u10};
        u11_reg <= {u11_reg[1:0], u11};

        v00_reg <= {v00_reg[1:0], v00};
        v01_reg <= {v01_reg[1:0], v01};
        v10_reg <= {v10_reg[1:0], v10};
        v11_reg <= {v11_reg[1:0], v11};
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
    .opu_i(masking_en ? masked_gs_stage1_uvo.u20_o /*TODO: masking passthrough*/ : intt_passthrough ? u00_reg[2] : u10),
    .opv_i(masking_en ? masked_gs_stage1_uvo.v20_o /*TODO: masking passthrough*/ : intt_passthrough ? u01_reg[2] : v10),
    .opw_i(masking_en ? masked_w10_reg[0] /*TODO: masking mlkem*/ : pwo_mode ? w10 : mlkem ? mlkem_w10_reg[0] : mldsa_w10_reg[0]),
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
    .opu_i(masking_en ? masked_gs_stage1_uvo.u21_o /*TODO: passthrough*/ : intt_passthrough ? v00_reg[2] : u11),
    .opv_i(masking_en ? masked_gs_stage1_uvo.v21_o : intt_passthrough ? v01_reg[2] : v11),
    .opw_i(masking_en ? masked_w11_reg[0] : pwo_mode ? w11 : mlkem ? mlkem_w11_reg[0] : mldsa_w11_reg[0]),
    .accumulate(accumulate),
    .u_o(u21_int),
    .v_o(v21_int),
    .pwm_res_o(mldsa_pwo_uv_o.uv3)
);

always_comb begin
    uv_o.u20_o = ntt_passthrough ? u10_reg[2] : u20_int;
    uv_o.v20_o = ntt_passthrough ? v10_reg[2]  :v20_int;

    uv_o.u21_o = ntt_passthrough ? u11_reg[2] : u21_int;
    uv_o.v21_o = ntt_passthrough ? v11_reg[2] : v21_int;
end

//----------------------------------------------------
//MLKEM - Unmasked PairWM
//----------------------------------------------------
mlkem_pwo_uvwzi_t pairwm_uvw01_i, pairwm_uvw23_i;
mlkem_pwo_t pairwm_uv01_o, pairwm_uv23_o;

always_comb begin
    if (mlkem & (mode == pairwm)) begin
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
                        // if (masking_en)
                        //     //TODO
                        // else
                            masked_ready_reg <= {{(MASKED_INTT_LATENCY-MLKEM_UNMASKED_BF_LATENCY){1'b0}}, enable, masked_ready_reg[MLKEM_UNMASKED_BF_LATENCY-1:1]};
                    end
                    pwm: masked_ready_reg <= 'b0;
                    pwa: masked_ready_reg <= {{MASKED_INTT_LATENCY-1{1'b0}}, enable};
                    pws: masked_ready_reg <= {{MASKED_INTT_LATENCY-1{1'b0}}, enable};
                    pairwm: begin
                        // if (masking_en)
                        //     //TODO
                        // else
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
