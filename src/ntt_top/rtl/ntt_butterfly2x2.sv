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
// ntt_butterfly2x2.sv
// --------
// Network of 4 butterfly units connected in a 2x2 layout. Inputs to these
// are u00, v00, u01, v01, w00, w01 (as an example), coming from a buffer. Outputs of 
// the 1st stage are passed onto the second stage (u10, v10, u11, v11, w10, w11). 
// The final outputs are buffered and written back to memory at the top level
//======================================================================

module ntt_butterfly2x2
    import ntt_defines_pkg::*;
#(
    parameter REG_SIZE = 23,
    parameter MLDSA_Q = 23'd8380417,
    parameter MLDSA_Q_DIV2_ODD = (MLDSA_Q + 1) / 2,
    parameter BF_LATENCY = 10, //5 cycles per butterfly * 2 instances in serial = 10 clks
    parameter PWM_LATENCY = 5, //latency of modular multiplier + modular addition to perform accumulation
    parameter PWA_LATENCY = 1, //latency of modular addition
    parameter PWS_LATENCY = 1,  //latency of modular subtraction
    parameter BF_STAGE1_LATENCY = BF_LATENCY/2
)
(
    //Clock and reset
    input wire clk,
    input wire reset_n,
    input wire zeroize,

    //Data ports
    input mode_t mode,
    input wire enable,
    input bf_uvwi_t uvw_i,
    input pwo_uvwi_t pw_uvw_i,
    input wire accumulate,
    
    output bf_uvo_t uv_o,
    output pwo_t pwo_uv_o,
    output logic ready_o
);
   
    logic [REG_SIZE-1:0] u00;
    logic [REG_SIZE-1:0] u01;
    logic [REG_SIZE-1:0] v00;
    logic [REG_SIZE-1:0] v01;

    logic [REG_SIZE-1:0] u10_int, u10;
    logic [REG_SIZE-1:0] u11_int, u11;
    logic [REG_SIZE-1:0] v10_int, v10;
    logic [REG_SIZE-1:0] v11_int, v11;

    logic [REG_SIZE-1:0] w00;
    logic [REG_SIZE-1:0] w01;
    logic [REG_SIZE-1:0] w10; 
    logic [REG_SIZE-1:0] w11;
    logic [BF_STAGE1_LATENCY-1:0][REG_SIZE-1:0] w10_reg, w11_reg; //Shift w10 by 5 cycles to match 1st stage BF latency
    logic pwo_mode;
    logic [BF_LATENCY-1:0] ready_reg;

    //Each butterfly unit takes u, v, w inputs and produces
    //u, v outputs for the next stage to consume. Each butterfly
    //has a maximum latency of 5 clks
    //Each worst-case path (ct or gs) contains a modular multiplication
    //and a modular add/sub. Multiplication takes a max of 4 clks 
    //(Multiplication module has 2 flops + 2 add/sub reductions in a single path).
    //Add/sub takes 1 clk to produce results.
    //So, worst case latency = 4 + 1 = 5 clks

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
            w10_reg <= {uvw_i.w10_i, w10_reg[BF_STAGE1_LATENCY-1:1]};
            w11_reg <= {uvw_i.w11_i, w11_reg[BF_STAGE1_LATENCY-1:1]};
        end
    end

    assign pwo_mode = (mode inside {pwm, pwa, pws});

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
        else begin
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

    ntt_butterfly #(
        .REG_SIZE(REG_SIZE),
        .MLDSA_Q(MLDSA_Q)
    )
    bf_inst00(
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .mode(mode),
        .opu_i(u00),
        .opv_i(v00),
        .opw_i(w00),
        .accumulate(accumulate),
        .u_o(u10_int),
        .v_o(u11_int),
        .pwm_res_o(pwo_uv_o.uv0)
    );

    ntt_butterfly #(
        .REG_SIZE(REG_SIZE),
        .MLDSA_Q(MLDSA_Q)
    )
    bf_inst01(
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .mode(mode),
        .opu_i(u01),
        .opv_i(v01),
        .opw_i(w01),
        .accumulate(accumulate),
        .u_o(v10_int),
        .v_o(v11_int),
        .pwm_res_o(pwo_uv_o.uv1)
    );

    ntt_butterfly #(
        .REG_SIZE(REG_SIZE),
        .MLDSA_Q(MLDSA_Q)
    )
    bf_inst10(
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .mode(mode),
        .opu_i(u10),
        .opv_i(v10),
        .opw_i(w10), //(uvw_i.w10_i),
        .accumulate(accumulate),
        .u_o(uv_o.u20_o),
        .v_o(uv_o.v20_o),
        .pwm_res_o(pwo_uv_o.uv2)
    );

    ntt_butterfly #(
        .REG_SIZE(REG_SIZE),
        .MLDSA_Q(MLDSA_Q)
    )
    bf_inst11(
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .mode(mode),
        .opu_i(u11),
        .opv_i(v11),
        .opw_i(w11), //(uvw_i.w11_i),
        .accumulate(accumulate),
        .u_o(uv_o.u21_o),
        .v_o(uv_o.v21_o),
        .pwm_res_o(pwo_uv_o.uv3)
    );

    //Determine when results are ready
    //---------------------------------------------
    //For the first 10 cycles, ntt_butterfly2x2 does not produce any valid  output.
    //We wait for 10 clks before asserting ready. After that, there's a valid output every clk.
    //ntt_top controller will disable bf2x2 and that will reset ready while transitioning 
    //from one stage to next after all writes of current stage have finished.

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            ready_reg <= 'b0;
        else if (zeroize)
            ready_reg <= 'b0;
        else begin
            unique case(mode)
                ct:  ready_reg <= {enable, ready_reg[BF_LATENCY-1:1]};
                gs:  ready_reg <= {enable, ready_reg[BF_LATENCY-1:1]};
                pwm: ready_reg <= accumulate ? {5'h0, enable, ready_reg[PWM_LATENCY-1:1]} : {6'h0, enable, ready_reg[PWM_LATENCY-2:1]};
                pwa: ready_reg <= {9'h0, enable};
                pws: ready_reg <= {9'h0, enable};
                default: ready_reg <= 'h0;
            endcase
        end
    end

    assign ready_o = ready_reg[0];
    

endmodule
