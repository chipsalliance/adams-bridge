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
    input mlkem_pwo_t          po_pwo_uv_o
    //$#//
);
    default clocking default_clk @(posedge pi_clk); endclocking

    fv_ntt_karatsuba_pairwm_constraints #(
    ) fv_ntt_karatsuba_pairwm_constraints_i (.*);

    //Function that multiplies two inputs and returns the result modulus Q
    function automatic logic[MLKEM_REG_SIZE-1:0] fv_mult_modQ (
        logic[MLKEM_REG_SIZE-1:0] u, 
        logic[MLKEM_REG_SIZE-1:0] v
    );
        logic [(2*MLKEM_REG_SIZE)-1:0] fv_mult_res;
        fv_mult_res = u * v;
        fv_mult_modQ = MLKEM_REG_SIZE'(fv_mult_res % MLKEM_Q);
    endfunction

    //Function that adds two inputs and returns the result modulus Q
    function automatic logic[MLKEM_REG_SIZE-1:0] fv_add_modQ (
        logic[MLKEM_REG_SIZE-1:0] u, 
        logic[MLKEM_REG_SIZE-1:0] v
    );
        logic [MLKEM_REG_SIZE:0] fv_add_res;
        fv_add_res = {1'b0, u} + {1'b0, v};
        fv_add_modQ = MLKEM_REG_SIZE'(fv_add_res % MLKEM_Q);
    endfunction

    //Function that subtracts two inputs and returns the result modulus Q
    function automatic logic[MLKEM_REG_SIZE-1:0] fv_sub_modQ (
        logic[MLKEM_REG_SIZE-1:0] u, 
        logic[MLKEM_REG_SIZE-1:0] v
    );
        logic [MLKEM_REG_SIZE:0] fv_sub_res;
        fv_sub_res = {1'b0, u} - {1'b0, v};

        if (fv_sub_res[MLKEM_REG_SIZE]) //negative number, wrap around
            fv_sub_modQ = MLKEM_REG_SIZE'((fv_sub_res + {1'b0, MLKEM_Q}) % MLKEM_Q);
        else
            fv_sub_modQ = MLKEM_REG_SIZE'(fv_sub_res % MLKEM_Q);
    endfunction

    //Calculations for uv0 output
    
    logic [MLKEM_REG_SIZE-1:0] fv_uv11_modQ;
    assign fv_uv11_modQ = fv_mult_modQ(pi_pwo_uvw_i.u1_i, pi_pwo_uvw_i.v1_i);

    logic [MLKEM_REG_SIZE-1:0] fv_uvz11_modQ;
    assign fv_uvz11_modQ = fv_mult_modQ(fv_uv11_modQ, pi_pwo_z_i);

    logic [MLKEM_REG_SIZE-1:0] fv_uv00_modQ;
    assign fv_uv00_modQ = fv_mult_modQ(pi_pwo_uvw_i.u0_i, pi_pwo_uvw_i.v0_i);

    logic [MLKEM_REG_SIZE-1:0] fv_uv0_modQ_o;
    assign fv_uv0_modQ_o = fv_add_modQ(fv_uvz11_modQ, fv_uv00_modQ);

    
    //Calculations for uv1 output

    logic [MLKEM_REG_SIZE-1:0] fv_add_u_modQ;
    assign fv_add_u_modQ = fv_add_modQ(pi_pwo_uvw_i.u0_i, pi_pwo_uvw_i.u1_i);

    logic [MLKEM_REG_SIZE-1:0] fv_add_v_modQ;
    assign fv_add_v_modQ = fv_add_modQ(pi_pwo_uvw_i.v0_i, pi_pwo_uvw_i.v1_i);

    logic [MLKEM_REG_SIZE-1:0] fv_uv_modQ;
    assign fv_uv_modQ = fv_mult_modQ(fv_add_u_modQ, fv_add_v_modQ);

    logic [MLKEM_REG_SIZE-1:0] fv_sub_uv00_modQ;
    assign fv_sub_uv00_modQ = fv_sub_modQ(fv_uv_modQ, fv_uv00_modQ);

    logic [MLKEM_REG_SIZE-1:0] fv_uv1_modQ_o;
    assign fv_uv1_modQ_o = fv_sub_modQ(fv_sub_uv00_modQ, fv_uv11_modQ);


    //Verify pwo_uv_o.uv0_o in case of no accumulate after the configured latency
    assert_ntt_karatsuba_pwm_uv0_o_no_accumulate: assert property (disable iff(!pi_reset_n | pi_zeroize)
        !pi_accumulate
    |->
        ##MLKEM_UNMASKED_PAIRWM_LATENCY
        po_pwo_uv_o.uv0_o == $past(fv_uv0_modQ_o, MLKEM_UNMASKED_PAIRWM_LATENCY)
    );

    //Verify pwo_uv_o.uv1_o in case of no accumulate after the configured latency
    assert_ntt_karatsuba_pwm_uv1_o_no_accumulate: assert property (disable iff(!pi_reset_n | pi_zeroize)
        !pi_accumulate
    |->
        ##MLKEM_UNMASKED_PAIRWM_LATENCY
        po_pwo_uv_o.uv1_o == $past(fv_uv1_modQ_o, MLKEM_UNMASKED_PAIRWM_LATENCY)
    );


    //Accumulation calculations of uv0 and uv1 outputs

    logic [MLKEM_REG_SIZE-1:0] fv_acc_uv0_modQ_o;
    assign fv_acc_uv0_modQ_o = fv_add_modQ(fv_uv0_modQ_o, pi_pwo_uvw_i.w0_i);

    logic [MLKEM_REG_SIZE-1:0] fv_acc_uv1_modQ_o;
    assign fv_acc_uv1_modQ_o = fv_add_modQ(fv_uv1_modQ_o, pi_pwo_uvw_i.w1_i);
    

    //Verify pwo_uv_o.uv0_o in case of accumulate after the configured latency
    assert_ntt_karatsuba_pwm_uv0_o_accumulate: assert property (disable iff(!pi_reset_n | pi_zeroize)
        pi_accumulate
    |->
        ##MLKEM_UNMASKED_PAIRWM_ACC_LATENCY
        po_pwo_uv_o.uv0_o == $past(fv_acc_uv0_modQ_o, MLKEM_UNMASKED_PAIRWM_ACC_LATENCY)
    );

    //Verify pwo_uv_o.uv1_o in case of accumulate after the configured latency
    assert_ntt_karatsuba_pwm_uv1_o_accumulate: assert property (disable iff(!pi_reset_n | pi_zeroize)
        pi_accumulate
    |->
        ##MLKEM_UNMASKED_PAIRWM_ACC_LATENCY
        po_pwo_uv_o.uv1_o == $past(fv_acc_uv1_modQ_o, MLKEM_UNMASKED_PAIRWM_ACC_LATENCY)
    );

    //Property to check output after reset
    assert_ntt_karatsuba_pwm_reset: assert property ( 
        $past(!pi_reset_n | pi_zeroize)
    |-> 
        po_pwo_uv_o == 'd0
    );


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
    .po_pwo_uv_o (pwo_uv_o)
    //$#//
);