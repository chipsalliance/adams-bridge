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
//======================================================================
//
// ntt_defines_pkg.sv
// --------
// NTT interface parameters for the digital signature algorithm (DSA).
//
//
//======================================================================

`ifndef MLDSA_NTT_DEFINES
`define MLDSA_NTT_DEFINES

package ntt_defines_pkg;
    import mldsa_params_pkg::*;

// `define MLDSA_MASKING

parameter NTT_REG_SIZE = REG_SIZE-1;
parameter MASKED_WIDTH = 46;
// parameter MEM_DEPTH = 2**MLDSA_MEM_ADDR_WIDTH;

//----------------------
//Latency params for NTT
//----------------------
parameter INTT_WRBUF_LATENCY         = 13;
parameter UNMASKED_BF_LATENCY        = 10;         //5 cycles per butterfly * 2 instances in serial = 10 clks
parameter UNMASKED_PWM_LATENCY       = 5;         //latency of modular multiplier + modular addition to perform accumulation
parameter UNMASKED_PWA_LATENCY       = 1;         //latency of modular addition
parameter UNMASKED_PWS_LATENCY       = 1;         //latency of modular subtraction
parameter UNMASKED_BF_STAGE1_LATENCY = UNMASKED_BF_LATENCY/2;

parameter MASKED_ADD_SUB_LATENCY            = 53;      //For 1 masked add/sub operation
parameter MASKED_PWM_LATENCY                = 211;     //For 1 masked pwm operation
parameter MASKED_PWM_ACC_LATENCY            = MASKED_PWM_LATENCY + MASKED_ADD_SUB_LATENCY;     //For 1 masked pwm + accumulate operation
parameter MASKED_BF_STAGE1_LATENCY          = 266;     //For 1 masked butterfly operation
parameter MASKED_PWM_MASKED_INTT_LATENCY    = MASKED_PWM_LATENCY + MASKED_BF_STAGE1_LATENCY;   //PWM+stage1 INTT latency
parameter MASKED_INTT_LATENCY               = MASKED_BF_STAGE1_LATENCY + UNMASKED_BF_STAGE1_LATENCY;  //masked INTT latency
parameter MASKED_PWM_INTT_LATENCY           = MASKED_PWM_LATENCY + MASKED_INTT_LATENCY + 1;           //TODO: adjust for PWMA case. Adding 1 cyc as a placeholder for it
parameter MASKED_INTT_WRBUF_LATENCY         = /*MASKED_PWM_LATENCY +*/ MASKED_INTT_LATENCY + 3;       //masked PWM+INTT latency + mem latency for shuffled reads to begin (does not include PWMA case)

// typedef enum logic [2:0] {ct, gs, pwm, pwa, pws} mode_t;
//TODO: tb has issue with enums in top level ports. For now, using this workaround
//Need to try something like bundling enable and mode into a struct to support enum.
localparam ct =3'd0,
           gs =3'd1,
           pwm=3'd2,
           pwa=3'd3,
           pws=3'd4,
           pwm_intt = 3'd5;
 
typedef logic [2:0] mode_t;

//NTT ports
typedef struct packed {
    logic [NTT_REG_SIZE-1:0] u00_i;
    logic [NTT_REG_SIZE-1:0] u01_i;
    logic [NTT_REG_SIZE-1:0] v00_i;
    logic [NTT_REG_SIZE-1:0] v01_i;
    logic [NTT_REG_SIZE-1:0] w00_i;
    logic [NTT_REG_SIZE-1:0] w01_i;
    logic [NTT_REG_SIZE-1:0] w10_i;
    logic [NTT_REG_SIZE-1:0] w11_i;
} bf_uvwi_t;

typedef struct packed {
    //input a
    logic [NTT_REG_SIZE-1:0] u0_i;
    logic [NTT_REG_SIZE-1:0] u1_i;
    logic [NTT_REG_SIZE-1:0] u2_i;
    logic [NTT_REG_SIZE-1:0] u3_i;
    //input b
    logic [NTT_REG_SIZE-1:0] v0_i;
    logic [NTT_REG_SIZE-1:0] v1_i;
    logic [NTT_REG_SIZE-1:0] v2_i;
    logic [NTT_REG_SIZE-1:0] v3_i;
    //accumulated input c (comes from dest mem)
    logic [NTT_REG_SIZE-1:0] w0_i;
    logic [NTT_REG_SIZE-1:0] w1_i;
    logic [NTT_REG_SIZE-1:0] w2_i;
    logic [NTT_REG_SIZE-1:0] w3_i;
    //input w for INTT operation that follows pwm. TODO: for only PWM/PWMA ops, this needs to be 0
    logic [NTT_REG_SIZE-1:0] twiddle_w0_i;
    logic [NTT_REG_SIZE-1:0] twiddle_w1_i;
    logic [NTT_REG_SIZE-1:0] twiddle_w2_i;
    logic [NTT_REG_SIZE-1:0] twiddle_w3_i;
} hybrid_bf_uvwi_t;

typedef struct packed {
    logic [NTT_REG_SIZE-1:0] u20_o;
    logic [NTT_REG_SIZE-1:0] u21_o;
    logic [NTT_REG_SIZE-1:0] v20_o;
    logic [NTT_REG_SIZE-1:0] v21_o;
} bf_uvo_t;

typedef struct packed {
    logic [1:0][MASKED_WIDTH-1:0] u00_i;
    logic [1:0][MASKED_WIDTH-1:0] u01_i;
    logic [1:0][MASKED_WIDTH-1:0] v00_i;
    logic [1:0][MASKED_WIDTH-1:0] v01_i;
    logic [1:0][MASKED_WIDTH-1:0] w00_i;
    logic [1:0][MASKED_WIDTH-1:0] w01_i;
} masked_bf_uvwi_t; //Only used in masked INTT stage 1

typedef struct packed {
    logic [1:0][MASKED_WIDTH-1:0] u00_i;
    logic [1:0][MASKED_WIDTH-1:0] u01_i;
    logic [1:0][MASKED_WIDTH-1:0] v00_i;
    logic [1:0][MASKED_WIDTH-1:0] v01_i;
    logic [1:0][MASKED_WIDTH-1:0] w00_i;
    logic [1:0][MASKED_WIDTH-1:0] w01_i;
    logic [NTT_REG_SIZE-1:0] w10_i;
    logic [NTT_REG_SIZE-1:0] w11_i;
} masked_intt_uvwi_t; //Only used in masked INTT

typedef struct packed {
    logic [MLDSA_MEM_ADDR_WIDTH-1:0] src_base_addr;
    logic [MLDSA_MEM_ADDR_WIDTH-1:0] interim_base_addr;
    logic [MLDSA_MEM_ADDR_WIDTH-1:0] dest_base_addr;
} ntt_mem_addr_t;

typedef struct packed {
    logic [MLDSA_MEM_ADDR_WIDTH-1:0] pw_base_addr_a;
    logic [MLDSA_MEM_ADDR_WIDTH-1:0] pw_base_addr_b;
    logic [MLDSA_MEM_ADDR_WIDTH-1:0] pw_base_addr_c;
} pwo_mem_addr_t;

//PWO ports
typedef struct packed {
    //input a
    logic [NTT_REG_SIZE-1:0] u0_i;
    logic [NTT_REG_SIZE-1:0] u1_i;
    logic [NTT_REG_SIZE-1:0] u2_i;
    logic [NTT_REG_SIZE-1:0] u3_i;
    //input b
    logic [NTT_REG_SIZE-1:0] v0_i;
    logic [NTT_REG_SIZE-1:0] v1_i;
    logic [NTT_REG_SIZE-1:0] v2_i;
    logic [NTT_REG_SIZE-1:0] v3_i;
    //accumulated input c (comes from dest mem)
    logic [NTT_REG_SIZE-1:0] w0_i;
    logic [NTT_REG_SIZE-1:0] w1_i;
    logic [NTT_REG_SIZE-1:0] w2_i;
    logic [NTT_REG_SIZE-1:0] w3_i;
} pwo_uvwi_t;

typedef struct packed {
    //input a
    logic [1:0][MASKED_WIDTH-1:0] u0_i;
    logic [1:0][MASKED_WIDTH-1:0] u1_i;
    logic [1:0][MASKED_WIDTH-1:0] u2_i;
    logic [1:0][MASKED_WIDTH-1:0] u3_i;
    //input b
    logic [1:0][MASKED_WIDTH-1:0] v0_i;
    logic [1:0][MASKED_WIDTH-1:0] v1_i;
    logic [1:0][MASKED_WIDTH-1:0] v2_i;
    logic [1:0][MASKED_WIDTH-1:0] v3_i;
    //accumulated input c (comes from dest mem)
    logic [1:0][MASKED_WIDTH-1:0] w0_i;
    logic [1:0][MASKED_WIDTH-1:0] w1_i;
    logic [1:0][MASKED_WIDTH-1:0] w2_i;
    logic [1:0][MASKED_WIDTH-1:0] w3_i;
} pwm_shares_uvwi_t;

typedef struct packed {
    logic [NTT_REG_SIZE-1:0] uv0;
    logic [NTT_REG_SIZE-1:0] uv1;
    logic [NTT_REG_SIZE-1:0] uv2;
    logic [NTT_REG_SIZE-1:0] uv3;
} pwo_t;

typedef struct packed {
    //input a
    logic [1:0][MASKED_WIDTH-1:0] uv0;
    logic [1:0][MASKED_WIDTH-1:0] uv1;
    logic [1:0][MASKED_WIDTH-1:0] uv2;
    logic [1:0][MASKED_WIDTH-1:0] uv3;
} pwm_shares_uvo_t;

typedef enum logic [2:0] {RD_IDLE, RD_STAGE, RD_BUF, RD_EXEC, EXEC_WAIT} ntt_read_state_t;
typedef enum logic [2:0] {WR_IDLE, WR_STAGE, WR_BUF, WR_MEM, WR_WAIT} ntt_write_state_t;

endpackage

`endif
