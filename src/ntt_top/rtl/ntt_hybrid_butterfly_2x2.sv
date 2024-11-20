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
// ntt_hybrid_butterfly_2x2.sv
// --------
// This module consists of masked PWMs, followed by 1st stage of masked and unmasked BFUs followed by
// 2nd stage of unmasked BFUs. In case of masking_en, PWMs are triggered and 
// masked branch is taken for computing 1st stage outputs. In case of unmasked operation, 
// both branches are enabled but unmasked outputs are passed to next stage. Final outputs are 23-bit values

module ntt_hybrid_butterfly_2x2
    import mldsa_params_pkg::*;
    import ntt_defines_pkg::*;
#(
    parameter WIDTH = 46,
    parameter HALF_WIDTH = WIDTH/2,
    parameter UNMASKED_BF_LATENCY = 10, //5 cycles per butterfly * 2 instances in serial = 10 clks
    parameter UNMASKED_PWM_LATENCY = 5, //latency of modular multiplier + modular addition to perform accumulation
    parameter UNMASKED_PWA_LATENCY = 1, //latency of modular addition
    parameter UNMASKED_PWS_LATENCY = 1,  //latency of modular subtraction
    parameter UNMASKED_BF_STAGE1_LATENCY = UNMASKED_BF_LATENCY/2,
    parameter MASKED_BF_STAGE1_LATENCY = 260, //For 1 masked butterfly
    parameter MASKED_PWM_LATENCY = 207, //For 1 masked pwm operation
    parameter MASKED_INTT_LATENCY = MASKED_BF_STAGE1_LATENCY + UNMASKED_BF_STAGE1_LATENCY,
    parameter MASKED_PWM_INTT_LATENCY = MASKED_PWM_LATENCY + MASKED_INTT_LATENCY
)
(
    input wire clk,
    input wire reset_n,
    input wire zeroize,

    input mode_t mode,
    input wire enable,
    input wire masking_en,
    input bf_uvwi_t uvw_i,      //Inputs are original form
    input pwo_uvwi_t pw_uvw_i,  //PWO inputs are original form
    input hybrid_bf_uvwi_t hybrid_pw_uvw_i, //PWM+INTT inputs. TODO: combine and mux with pwo inputs?
    input wire [4:0][WIDTH-1:0] rnd_i,
    input wire accumulate,

    output bf_uvo_t uv_o,       //Outputs are original form
    output pwo_t pwo_uv_o,
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
//Outputs of 2nd stage
// logic [HALF_WIDTH-1:0] u20, u21, v20, v21;

//Other internal wires
logic [UNMASKED_BF_STAGE1_LATENCY-1:0][HALF_WIDTH-1:0] w10_reg, w11_reg; //Shift w10 by 5 cycles to match 1st stage BF latency
logic [MASKED_PWM_LATENCY-1:0][HALF_WIDTH-1:0] masked_w00_reg, masked_w01_reg;
logic [MASKED_BF_STAGE1_LATENCY-1:0][HALF_WIDTH-1:0] masked_w10_reg, masked_w11_reg;
logic pwo_mode, pwm_intt_mode;
// logic [UNMASKED_BF_LATENCY-1:0] ready_reg;
logic [MASKED_PWM_INTT_LATENCY-1:0] masked_ready_reg;

//Shares - TODO replace with struct?
logic [1:0][WIDTH-1:0] u00_share, u01_share, v00_share, v01_share, u10_share, v10_share, u11_share, v11_share;
logic [1:0][WIDTH-1:0] w00_share, w01_share, w10_share, w11_share; //, w10_reg_share, w11_reg_share;
logic [1:0][WIDTH-1:0] uv00_share, uv01_share, uv10_share, uv11_share;
logic [1:0][WIDTH-1:0] twiddle_w00_share, twiddle_w01_share, twiddle_w10_share, twiddle_w11_share;
bf_uvo_t masked_gs_stage1_uvo;

//w delay flops
//Flop the twiddle factor 5x to correctly pass in values to the 2nd set of bf units
always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        w10_reg <= 'h0;
        w11_reg <= 'h0;
    end
    else if (zeroize) begin
        w10_reg <= 'h0;
        w11_reg <= 'h0;
    end
    else begin
        w10_reg <= {uvw_i.w10_i, w10_reg[UNMASKED_BF_STAGE1_LATENCY-1:1]};
        w11_reg <= {uvw_i.w11_i, w11_reg[UNMASKED_BF_STAGE1_LATENCY-1:1]};
    end
end

always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        masked_w00_reg <= 'h0;
        masked_w01_reg <= 'h0;
        masked_w10_reg <= 'h0;
        masked_w11_reg <= 'h0;
    end
    else if (zeroize) begin
        masked_w00_reg <= 'h0;
        masked_w01_reg <= 'h0;
        masked_w10_reg <= 'h0;
        masked_w11_reg <= 'h0;
    end
    else begin
        masked_w00_reg <= {hybrid_pw_uvw_i.twiddle_w0_i, masked_w00_reg[MASKED_PWM_LATENCY-1:1]};
        masked_w01_reg <= {hybrid_pw_uvw_i.twiddle_w1_i, masked_w01_reg[MASKED_PWM_LATENCY-1:1]};
        masked_w10_reg <= {hybrid_pw_uvw_i.twiddle_w2_i, masked_w10_reg[MASKED_BF_STAGE1_LATENCY-1:1]};
        masked_w11_reg <= {hybrid_pw_uvw_i.twiddle_w3_i, masked_w11_reg[MASKED_BF_STAGE1_LATENCY-1:1]};
    end
end

assign pwo_mode = (mode inside {pwm, pwa, pws});
assign pwm_intt_mode = (mode == pwm_intt) & masking_en;

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
    else if (pwm_intt_mode) begin //TODO: clean up
        u00 = hybrid_pw_uvw_i.u0_i;
        v00 = hybrid_pw_uvw_i.v0_i;
        w00 = hybrid_pw_uvw_i.w0_i;

        u01 = hybrid_pw_uvw_i.u1_i;
        v01 = hybrid_pw_uvw_i.v1_i;
        w01 = hybrid_pw_uvw_i.w1_i;

        u10 = hybrid_pw_uvw_i.u2_i;
        v10 = hybrid_pw_uvw_i.v2_i;
        w10 = hybrid_pw_uvw_i.w2_i;

        u11 = hybrid_pw_uvw_i.u3_i;
        v11 = hybrid_pw_uvw_i.v3_i;
        w11 = hybrid_pw_uvw_i.w3_i;
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
        w10 = w10_reg[0];

        u11 = u11_int;
        v11 = v11_int;
        w11 = w11_reg[0];
    end
end

//Split into shares
always_comb begin
    //TODO: check randomness with Emre
    //TODO: add flops here (input side)
    //Split u inputs
    if (masking_en) begin
        u00_share[0] = WIDTH'(u00) - rnd_i[0];
        u00_share[1] = rnd_i[0];

        u01_share[0] = WIDTH'(u01) - rnd_i[1];
        u01_share[1] = rnd_i[1];

        u10_share[0] = WIDTH'(u10) - rnd_i[0];
        u10_share[1] = rnd_i[0];

        u11_share[0] = WIDTH'(u11) - rnd_i[0];
        u11_share[1] = rnd_i[0];

        //Split v inputs
        v00_share[0] = WIDTH'(v00) - rnd_i[2];
        v00_share[1] = rnd_i[2];

        v01_share[0] = WIDTH'(v01) - rnd_i[3];
        v01_share[1] = rnd_i[3];

        v10_share[0] = WIDTH'(v10) - rnd_i[2];
        v10_share[1] = rnd_i[2];

        v11_share[0] = WIDTH'(v11) - rnd_i[2];
        v11_share[1] = rnd_i[2];

        //Split w inputs
        w00_share[0] = WIDTH'(w00) - rnd_i[4];
        w00_share[1] = rnd_i[4];

        w01_share[0] = WIDTH'(w01) - rnd_i[0];
        w01_share[1] = rnd_i[0];

        w10_share[0] = WIDTH'(w10) - rnd_i[1];
        w10_share[1] = rnd_i[1];

        w11_share[0] = WIDTH'(w11) - rnd_i[2];
        w11_share[1] = rnd_i[2];

        twiddle_w00_share[0] = WIDTH'(masked_w00_reg[0]) - rnd_i[0];
        twiddle_w00_share[1] = rnd_i[0];

        twiddle_w01_share[0] = WIDTH'(masked_w01_reg[0]) - rnd_i[1];
        twiddle_w01_share[1] = rnd_i[1];  

    end
    else begin
        u00_share[0] = 'h0;
        u00_share[1] = 'h0;

        u01_share[0] = 'h0;
        u01_share[1] = 'h0;

        u10_share[0] = 'h0;
        u10_share[1] = 'h0;

        u11_share[0] = 'h0;
        u11_share[1] = 'h0;

        //Split v input
        v00_share[0] = 'h0;
        v00_share[1] = 'h0;

        v01_share[0] = 'h0;
        v01_share[1] = 'h0;

        v10_share[0] = 'h0;
        v10_share[1] = 'h0;

        v11_share[0] = 'h0;
        v11_share[1] = 'h0;

        //Split w input
        w00_share[0] = 'h0;
        w00_share[1] = 'h0;

        w01_share[0] = 'h0;
        w01_share[1] = 'h0;

        w10_share[0] = 'h0;
        w10_share[1] = 'h0;

        w11_share[0] = 'h0;
        w11_share[1] = 'h0;

        twiddle_w00_share[0] = 'h0;
        twiddle_w00_share[1] = 'h0;

        twiddle_w01_share[0] = 'h0;
        twiddle_w01_share[1] = 'h0;  
    end
end

//----------------------------------------------------
//Masked PWMs - Used in masked PWM+INTT mode only - 207 clks
//----------------------------------------------------
// `ifdef MASKING
ntt_masked_pwm #(
    .WIDTH(WIDTH)
) pwm_inst00 (
    .clk(clk),
    .reset_n(reset_n),
    .zeroize(zeroize),
    .u(u00_share),
    .v(v00_share),
    .w(w00_share),
    .rnd({rnd_i[4], rnd_i[3], rnd_i[2], rnd_i[1], rnd_i[0]}),
    .res(uv00_share)
);

ntt_masked_pwm #(
    .WIDTH(WIDTH)
) pwm_inst01 (
    .clk(clk),
    .reset_n(reset_n),
    .zeroize(zeroize),
    .u(u01_share),
    .v(v01_share),
    .w(w01_share),
    .rnd({rnd_i[0], rnd_i[4], rnd_i[3], rnd_i[2], rnd_i[1]}),
    .res(uv01_share)
);

ntt_masked_pwm #(
    .WIDTH(WIDTH)
) pwm_inst10 (
    .clk(clk),
    .reset_n(reset_n),
    .zeroize(zeroize),
    .u(u10_share),
    .v(v10_share),
    .w(w10_share),
    .rnd({rnd_i[1], rnd_i[0], rnd_i[4], rnd_i[3], rnd_i[2]}),
    .res(uv10_share)
);

ntt_masked_pwm #(
    .WIDTH(WIDTH)
) pwm_inst11 (
    .clk(clk),
    .reset_n(reset_n),
    .zeroize(zeroize),
    .u(u11_share),
    .v(v11_share),
    .w(w11_share),
    .rnd({rnd_i[2], rnd_i[1], rnd_i[0], rnd_i[4], rnd_i[3]}),
    .res(uv11_share)
);
// `endif 
//----------------------------------------------------
//Masked BFU stage 1 - Used in masked PWM+INTT mode only - 260 clks
//PWM outputs: uv00[1:0], uv01[1:0], uv10[1:0], uv11[1:0]
//----------------------------------------------------
ntt_masked_butterfly1x2 #(
    .WIDTH(WIDTH)
) masked_bf_1x2_inst0 (
    .clk(clk),
    .reset_n(reset_n),
    .zeroize(zeroize),
    .uvw_i({uv00_share, uv01_share, uv10_share, uv11_share, twiddle_w00_share, twiddle_w01_share}), //TODO check connection
    .rnd_i({rnd_i[4], rnd_i[3], rnd_i[2], rnd_i[1], rnd_i[0]}),
    .uv_o(masked_gs_stage1_uvo)
);
// `endif
//----------------------------------------------------
//Unmasked BFU stage 1 - Used in all other modes
//----------------------------------------------------
ntt_butterfly #(
    .REG_SIZE(HALF_WIDTH)
) unmasked_bf_inst00 (
    .clk(clk),
    .reset_n(reset_n),
    .zeroize(zeroize),
    .mode(mode),
    .opu_i(masking_en ? HALF_WIDTH'(0) : u00),
    .opv_i(masking_en ? HALF_WIDTH'(0) : v00),
    .opw_i(masking_en ? HALF_WIDTH'(0) : w00),
    .accumulate(accumulate),
    .u_o(u10_int),
    .v_o(u11_int),
    .pwm_res_o(pwo_uv_o.uv0)
);

ntt_butterfly #(
    .REG_SIZE(HALF_WIDTH)
) unmasked_bf_inst01 (
    .clk(clk),
    .reset_n(reset_n),
    .zeroize(zeroize),
    .mode(mode),
    .opu_i(masking_en ? HALF_WIDTH'(0) : u01),
    .opv_i(masking_en ? HALF_WIDTH'(0) : v01),
    .opw_i(masking_en ? HALF_WIDTH'(0) : w01),
    .accumulate(accumulate),
    .u_o(v10_int),
    .v_o(v11_int),
    .pwm_res_o(pwo_uv_o.uv1)
);

//----------------------------------------------------
//Unmasked BFU stage 2 - Used in all modes (irrespective of masking_en)
//----------------------------------------------------
ntt_butterfly #(
    .REG_SIZE(HALF_WIDTH)
) unmasked_bf_inst10 (
    .clk(clk),
    .reset_n(reset_n),
    .zeroize(zeroize),
    .mode(mode),
    .opu_i(masking_en ? masked_gs_stage1_uvo.u20_o : u10),
    .opv_i(masking_en ? masked_gs_stage1_uvo.v20_o : v10),
    .opw_i(masking_en ? masked_w10_reg[0] : pwo_mode ? w10 : w10_reg[0]),
    .accumulate(accumulate),
    .u_o(uv_o.u20_o),
    .v_o(uv_o.v20_o),
    .pwm_res_o(pwo_uv_o.uv2)
);

ntt_butterfly #(
    .REG_SIZE(HALF_WIDTH)
) unmasked_bf_inst11 (
    .clk(clk),
    .reset_n(reset_n),
    .zeroize(zeroize),
    .mode(mode),
    .opu_i(masking_en ? masked_gs_stage1_uvo.u21_o : u11),
    .opv_i(masking_en ? masked_gs_stage1_uvo.v21_o : v11),
    .opw_i(masking_en ? masked_w11_reg[0] : pwo_mode ? w11 : w11_reg[0]),
    .accumulate(accumulate),
    .u_o(uv_o.u21_o),
    .v_o(uv_o.v21_o),
    .pwm_res_o(pwo_uv_o.uv3)
);

//----------------------------------------------------
//Determine when results are ready
//----------------------------------------------------
//ready_o logic
always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n)
        masked_ready_reg <= 'b0;
    else if (zeroize)
        masked_ready_reg <= 'b0;
    else begin
        unique case(mode) //471:0 delay flop for enable - TODO: optimize
            ct:  masked_ready_reg <= {462'h0, enable, masked_ready_reg[UNMASKED_BF_LATENCY-1:1]};
            gs:  masked_ready_reg <= {462'h0, enable, masked_ready_reg[UNMASKED_BF_LATENCY-1:1]};
            pwm: masked_ready_reg <= accumulate ? {467'h0, enable, masked_ready_reg[UNMASKED_PWM_LATENCY-1:1]} : {6'h0, enable, masked_ready_reg[UNMASKED_PWM_LATENCY-2:1]};
            pwm_intt: masked_ready_reg <= accumulate ? {enable, masked_ready_reg[MASKED_PWM_INTT_LATENCY-1:1]} : {1'b0, enable, masked_ready_reg[MASKED_PWM_INTT_LATENCY-2:1]}; //TODO revisit
            pwa: masked_ready_reg <= {471'h0, enable};
            pws: masked_ready_reg <= {471'h0, enable};
            default: masked_ready_reg <= 'h0;
        endcase
    end
end

assign ready_o = masked_ready_reg[0];
    

endmodule
