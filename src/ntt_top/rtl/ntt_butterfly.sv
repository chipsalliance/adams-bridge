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
// ntt_butterfly.sv
// --------
// Combined butterfly unit that performs NTT and INTT. All operations
// are modular. This unit operates in 5 modes - NTT, INTT and PWM, PWA, PWS
// Inputs u and v are fetched from s memory, w values come from ROM
// containing required twiddle factors.
// PWM mode performs point-wise multiplication and accumulation
//======================================================================

module ntt_butterfly 
    import ntt_defines_pkg::*;
    import abr_params_pkg::*;
#(
    parameter REG_SIZE  = 23,
    parameter MLDSA_Q     = 23'd8380417,
    parameter MLDSA_Q_DIV2_ODD = (MLDSA_Q + 1) / 2,
    parameter MLKEM_Q = 12'd3329,
    parameter MLKEM_Q_DIV2_ODD = (MLKEM_Q + 1) / 2
)
(
    //Clock and reset
    input wire clk,
    input wire reset_n,
    input wire zeroize,
    
    //Data ports
    input mode_t mode,
    input wire accumulate,
    input wire mlkem,

    input wire   [REG_SIZE-1:0] opu_i,
    input wire   [REG_SIZE-1:0] opv_i,
    input wire   [REG_SIZE-1:0] opw_i,

    output logic [REG_SIZE-1:0]   u_o,
    output logic [REG_SIZE-1:0]   v_o,
    output logic [REG_SIZE-1:0]   pwm_res_o
);

    //Input wires
    logic [REG_SIZE-1:0] u_reg, u_reg_d2, u_reg_d3, u_reg_d4;
    // logic [REG_SIZE-1:0] v_reg, v_reg_d2, v_reg_d3, v_reg_d4;
    logic [REG_SIZE-1:0] w_reg, w_reg_d2, w_reg_d3, w_reg_d4; //w_reg_d4 only used in pwm mode

    //Multiplier wires
    logic [(2*REG_SIZE)-1:0] vw, vw_reg, mul_res; 
    logic [(2*MLKEM_REG_SIZE)-1:0] mul_res_reg; //used in MLKEM
    logic [MLKEM_REG_SIZE-1:0] mlkem_mul_res_reduced;
    logic [22:0] mldsa_mul_res_reduced;
    logic [MLKEM_REG_SIZE-1:0] mlkem_mul_res_reduced_reg; //used in MLKEM
    logic [REG_SIZE-1:0] mul_opa, mul_opb;

    //Subtractor wires
    logic [REG_SIZE-1:0] u_minus_v, mldsa_u_minus_v_div2;
    logic [MLKEM_REG_SIZE-1:0] mlkem_u_minus_v_div2;

    //Adder wires
    logic [REG_SIZE-1:0] add_opa, add_opb;
    logic [REG_SIZE-1:0] add_res, add_res_d1, add_res_d2, add_res_d3, add_res_d4, sub_res;
    logic [REG_SIZE-1:0] mldsa_add_res_div2, sub_res_div2, mul_res_reduced_div2;
    logic [MLKEM_REG_SIZE-1:0] mlkem_add_res_div2;

    //Flop u input to match multiplier output (4 cycle delay)
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            u_reg    <= 'h0;
            u_reg_d2 <= 'h0;
            u_reg_d3 <= 'h0; 
            u_reg_d4 <= 'h0;
            
            w_reg    <= 'h0; 
            w_reg_d2 <= 'h0; 
            w_reg_d3 <= 'h0; 
            w_reg_d4 <= 'h0;

            mul_res_reg <= '0;
            mlkem_mul_res_reduced_reg <= '0;
        end
        else if (zeroize) begin
            u_reg    <= 'h0;
            u_reg_d2 <= 'h0;
            u_reg_d3 <= 'h0; 
            u_reg_d4 <= 'h0;
            
            w_reg    <= 'h0; 
            w_reg_d2 <= 'h0; 
            w_reg_d3 <= 'h0; 
            w_reg_d4 <= 'h0;

            mul_res_reg <= '0;
            mlkem_mul_res_reduced_reg <= '0;
        end
        else begin
            u_reg    <= opu_i;
            u_reg_d2 <= u_reg;
            u_reg_d3 <= u_reg_d2; 
            u_reg_d4 <= u_reg_d3;
            
            //Used in GS/PWM mode only
            w_reg    <= opw_i; 
            w_reg_d2 <= w_reg; 
            w_reg_d3 <= w_reg_d2; 
            w_reg_d4 <= w_reg_d3;

            //Used in MLKEM
            mul_res_reg <= (2*MLKEM_REG_SIZE)'(mul_res);
            mlkem_mul_res_reduced_reg <= mlkem_mul_res_reduced;
        end
    end

    //4 cycle delay to match critical path
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            add_res_d1 <= 'h0;
            add_res_d2 <= 'h0;
            add_res_d3 <= 'h0;
            add_res_d4 <= 'h0;
        end
        else if (zeroize) begin
            add_res_d1 <= 'h0;
            add_res_d2 <= 'h0;
            add_res_d3 <= 'h0;
            add_res_d4 <= 'h0;
        end
        else begin
            add_res_d1 <= add_res;
            add_res_d2 <= add_res_d1;
            add_res_d3 <= add_res_d2;
            add_res_d4 <= add_res_d3;
        end
    end

    //Mode mux for outputs
    always_comb begin
        unique case(mode)
            ct: begin
                u_o = add_res;
                v_o = sub_res;
                pwm_res_o = 'h0;
            end
            gs: begin
                u_o = mlkem ? REG_SIZE'(mlkem_add_res_div2) : mldsa_add_res_div2;
                v_o = mlkem ? REG_SIZE'(mlkem_mul_res_reduced_reg) : mldsa_mul_res_reduced[REG_SIZE-1:0]; //_div2;
                pwm_res_o = 'h0;
            end
            pwm:begin
                u_o = 'h0; //accumulate ? add_res : mlkem ? REG_SIZE'(mlkem_mul_res_reduced_reg) : mldsa_mul_res_reduced[REG_SIZE-1:0]; //TODO: see if pwm_res_o is good enough or reuse u_o to save routing/area
                v_o = 'h0;
                pwm_res_o = mlkem ? 'h0 : accumulate ? add_res : mldsa_mul_res_reduced[REG_SIZE-1:0];
            end
            pwa:begin
                u_o = 'h0; //add_res;
                v_o = 'h0;
                pwm_res_o = add_res;
            end
            pws:begin
                u_o = 'h0; //u_minus_v;
                v_o = 'h0;
                pwm_res_o = u_minus_v;
            end
            pairwm: begin //Karatsuba pairwm is used instead of this butterfly
                u_o = 'h0;
                v_o = 'h0;
                pwm_res_o = 'h0;
            end
            default: begin
                u_o = 'h0;
                v_o = 'h0;
                pwm_res_o = 'h0;
            end
        endcase
    end

    //Mode mux for inputs
    //0 - NTT, 1 - INTT, 2 - PWM
    always_comb begin
        unique case(mode)
            ct: begin
                add_opa = mlkem ? u_reg_d2 : u_reg_d4;
                add_opb = mlkem ? REG_SIZE'(mlkem_mul_res_reduced_reg) : mldsa_mul_res_reduced[REG_SIZE-1:0];
                mul_opa = opv_i;
                mul_opb = opw_i;
            end
            gs: begin
                add_opa = opu_i;
                add_opb = opv_i;
                mul_opa = mlkem ? REG_SIZE'(mlkem_u_minus_v_div2) : mldsa_u_minus_v_div2; //u_minus_v
                mul_opb = w_reg;
            end
            pwm:begin
                add_opa = mlkem ? 'h0 : w_reg_d4;
                add_opb = mlkem ? 'h0 : mldsa_mul_res_reduced[REG_SIZE-1:0];
                mul_opa = opu_i;
                mul_opb = opv_i;
            end
            pwa:begin
                add_opa = opu_i;
                add_opb = opv_i;
                mul_opa = 'h0;
                mul_opb = 'h0;
            end
            default: begin
                add_opa = 'h0;
                add_opb = 'h0;
                mul_opa = 'h0;
                mul_opb = 'h0;
            end
        endcase
    end

    //Mod sub - used in GS
    abr_ntt_add_sub_mod #(
        .REG_SIZE(REG_SIZE)
        )
        sub_inst_0(
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .add_en_i(1'b1),
        .sub_i(1'b1),
        .opa_i(opu_i),
        .opb_i(opv_i),
        .prime_i(mlkem ? REG_SIZE'(MLKEM_Q) : REG_SIZE'(MLDSA_Q)),
        .mlkem(mlkem),
        .res_o(u_minus_v),
        .ready_o()
    );

    //Mod sub - used in CT
    abr_ntt_add_sub_mod #(
        .REG_SIZE(REG_SIZE)
        )
        sub_inst_1(
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .add_en_i(1'b1),
        .sub_i(1'b1),
        .opa_i(mlkem ? u_reg_d2 : u_reg_d4),
        .opb_i(mlkem ?  REG_SIZE'(mlkem_mul_res_reduced_reg) : mldsa_mul_res_reduced[REG_SIZE-1:0]),
        .prime_i(mlkem ? REG_SIZE'(MLKEM_Q) : REG_SIZE'(MLDSA_Q)),
        .mlkem(mlkem),
        .res_o(sub_res),
        .ready_o()
    );

    //Mod add - used in CT and GS, PWM
    abr_ntt_add_sub_mod #(
        .REG_SIZE(REG_SIZE)
        )
        add_inst_0(
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .add_en_i(1'b1),
        .sub_i(1'b0),
        .opa_i(add_opa),
        .opb_i(add_opb),
        .prime_i(mlkem ? REG_SIZE'(MLKEM_Q) : REG_SIZE'(MLDSA_Q)),
        .mlkem(mlkem),
        .res_o(add_res),
        .ready_o()
    );

    //Mod mult - used in CT, GS, PWM

    ntt_mult_dsp #(
        .RADIX(REG_SIZE)
        )
        mul_inst_0 (
        .A_i(mul_opa),
        .B_i(mul_opb),
        .P_o(mul_res)
    );
    
    ntt_mult_reduction #(
        .REG_SIZE(23),
        .PRIME(MLDSA_Q)
        )
        mldsa_mul_redux_inst_0 (
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .opa_i(mlkem ? '0 : 46'(mul_res)),
        .res_o(mldsa_mul_res_reduced),
        .ready_o()
    );

    barrett_reduction #(
        .REG_SIZE(MLKEM_REG_SIZE),
        .prime(MLKEM_Q)
        )
        mlkem_mul_redux_inst_0 (
        .x(mlkem ? mul_res_reg : '0),
        .inv(),
        .r(mlkem_mul_res_reduced)
    );

    //Output div2 - used in MLDSA GS
    ntt_div2 #(
        .REG_SIZE(REG_SIZE),
        .PRIME(MLDSA_Q)
    )
    mldsa_div2_inst_0 (
        .op_i (add_res_d4),
        .res_o (mldsa_add_res_div2)
    );

    ntt_div2 #(
        .REG_SIZE(REG_SIZE),
        .PRIME(MLDSA_Q)
    )
    mldsa_div2_inst_2 (
        .op_i (u_minus_v),
        .res_o (mldsa_u_minus_v_div2)
    );

    //Output div2 - used in MLKEM GS
    ntt_div2 #(
        .REG_SIZE(MLKEM_REG_SIZE),
        .PRIME(MLKEM_Q)
    )
    mlkem_div2_inst_0 (
        .op_i (add_res_d2[MLKEM_REG_SIZE-1:0]),
        .res_o (mlkem_add_res_div2)
    );

    ntt_div2 #(
        .REG_SIZE(MLKEM_REG_SIZE),
        .PRIME(MLKEM_Q)
    )
    mlkem_div2_inst_2 (
        .op_i (u_minus_v[MLKEM_REG_SIZE-1:0]),
        .res_o (mlkem_u_minus_v_div2)
    );

endmodule
