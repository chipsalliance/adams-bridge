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
// mldsa_seq_pkg.sv
// --------
// MLDSA instructions for MLDSA.
//
//
//======================================================================

`ifndef MLDSA_CTRL_PKG
`define MLDSA_CTRL_PKG

package mldsa_ctrl_pkg;
    import mldsa_params_pkg::*;
    import mldsa_sampler_pkg::*;

    localparam integer MLDSA_OPR_WIDTH       = 15;
    localparam integer MLDSA_IMM_WIDTH       = 16;
    localparam MLDSA_PROG_ADDR_W             = 9;

    localparam SEED_NUM_DWORDS = 8;
    localparam MSG_NUM_DWORDS = 16;
    localparam PRIVKEY_NUM_DWORDS = 1224;
    localparam PRIVKEY_REG_NUM_DWORDS = 32;
    localparam SIGN_RND_NUM_DWORDS = 8;
    localparam PUBKEY_NUM_DWORDS = 648;
    localparam PUBKEY_NUM_BYTES = PUBKEY_NUM_DWORDS * 4;
    localparam SIGNATURE_H_NUM_DWORDS = 21;
    localparam SIGNATURE_H_VALID_NUM_BYTES = 83;
    localparam SIGNATURE_Z_NUM_DWORDS = 1120;
    localparam SIGNATURE_C_NUM_DWORDS = 16;
    localparam SIGNATURE_NUM_DWORDS = SIGNATURE_H_NUM_DWORDS + SIGNATURE_Z_NUM_DWORDS + SIGNATURE_C_NUM_DWORDS;
    localparam VERIFY_RES_NUM_DWORDS = 16;
    localparam ENTROPY_NUM_DWORDS = 16;

    localparam T1_NUM_COEFF = 2048;
    localparam T1_COEFF_W = 10;

    localparam SK_MEM_DEPTH = 1192;
    localparam SK_MEM_BANK_DEPTH = 596;
    localparam SK_MEM_ADDR_W = $clog2(SK_MEM_BANK_DEPTH);

    typedef struct packed {
        logic [7:0][63:0] tr;
        logic [3:0][63:0] K;
        logic [3:0][63:0] rho;
    } mldsa_privkey_t;

    typedef union packed {
        mldsa_privkey_t enc;
        logic [PRIVKEY_REG_NUM_DWORDS-1:0][31:0] raw;
    } mldsa_privkey_u;

    typedef struct packed {
        logic [SIGNATURE_H_NUM_DWORDS-1:0][31:0] h;
        logic [SIGNATURE_Z_NUM_DWORDS-1:0][31:0] z;
        logic [SIGNATURE_C_NUM_DWORDS-1:0][31:0] c;
    } mldsa_signature_t;

    typedef union packed {
        mldsa_signature_t enc;
        logic [SIGNATURE_NUM_DWORDS-1:0][31:0] raw;
    } mldsa_signature_u;

    typedef struct packed {
        logic [T1_NUM_COEFF-1:0][T1_COEFF_W-1:0] t1;
        logic [7:0][31:0] rho;
    } mldsa_pubkey_t;

    typedef union packed {
        mldsa_pubkey_t enc;
        logic [PUBKEY_NUM_DWORDS-1:0][31:0] raw;
    } mldsa_pubkey_u;

    //FSM Controller for driving sampler 
    typedef enum logic [2:0] {
        MLDSA_CTRL_IDLE,
        MLDSA_CTRL_SHA3_START,
        MLDSA_CTRL_MSG_START,
        MLDSA_CTRL_MSG_LOAD,
        MLDSA_CTRL_MSG_WAIT,
        MLDSA_CTRL_FUNC_START,
        MLDSA_CTRL_DONE,
        MLDSA_CTRL_ERROR
      } mldsa_ctrl_fsm_state_e;

    typedef enum logic[3:0] {
        MLDSA_NTT_NONE,
        MLDSA_NTT,
        MLDSA_INTT,
        MLDSA_PWM,
        MLDSA_PWM_ACCUM,
        MLDSA_PWM_SMPL,
        MLDSA_PWM_ACCUM_SMPL,
        MLDSA_PWA,
        MLDSA_PWS
    } mldsa_ntt_mode_e;

    typedef enum logic[3:0] {
        MLDSA_AUX_NONE,
        MLDSA_SKDECODE,
        MLDSA_SKENCODE,
        MLDSA_PKDECODE,
        MLDSA_MAKEHINT,
        MLDSA_USEHINT,
        MLDSA_NORMCHK,
        MLDSA_PWR2RND,
        MLDSA_SIGENC,
        MLDSA_SIGDEC_H,
        MLDSA_SIGDEC_Z,
        MLDSA_HINTSUM,
        MLDSA_DECOMP
    } mldsa_aux_mode_e;


    typedef union packed {
        mldsa_sampler_mode_e sampler_mode;
        mldsa_aux_mode_e     aux_mode;
        mldsa_ntt_mode_e     ntt_mode;
    } mldsa_opcode_mode_u;

    typedef struct packed {
        logic keccak_en;
        logic sampler_en;
        logic ntt_en;
        logic aux_en;
        mldsa_opcode_mode_u mode;
        logic sca_en;
    } mldsa_opcode_t;

    typedef struct packed {
        mldsa_opcode_t                   opcode;
        logic [MLDSA_IMM_WIDTH-1 : 0]    imm;
        logic [MLDSA_OPR_WIDTH-1 : 0]    length;
        logic [MLDSA_OPR_WIDTH-1 : 0]    operand1;
        logic [MLDSA_OPR_WIDTH-1 : 0]    operand2;
        logic [MLDSA_OPR_WIDTH-1 : 0]    operand3;
    } mldsa_seq_instr_t;

    // MLDSA ISA
    localparam mldsa_opcode_t MLDSA_UOP_NOP       = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b0, aux_en: 1'b0, mode:MLDSA_SAMPLER_NONE,   sca_en:1'b0};
    localparam mldsa_opcode_t MLDSA_UOP_SHAKE256  = '{keccak_en: 1'b1, sampler_en:1'b1, ntt_en:1'b0, aux_en: 1'b0, mode:MLDSA_SHAKE256,       sca_en:1'b0};
    localparam mldsa_opcode_t MLDSA_UOP_SHAKE128  = '{keccak_en: 1'b1, sampler_en:1'b1, ntt_en:1'b0, aux_en: 1'b0, mode:MLDSA_SHAKE128,       sca_en:1'b0};
    localparam mldsa_opcode_t MLDSA_UOP_REJB      = '{keccak_en: 1'b1, sampler_en:1'b1, ntt_en:1'b0, aux_en: 1'b0, mode:MLDSA_REJ_BOUNDED,    sca_en:1'b0};
    localparam mldsa_opcode_t MLDSA_UOP_REJS_PWM  = '{keccak_en: 1'b1, sampler_en:1'b1, ntt_en:1'b1, aux_en: 1'b0, mode:MLDSA_PWM_SMPL,       sca_en:1'b0};
    localparam mldsa_opcode_t MLDSA_UOP_REJS_PWMA = '{keccak_en: 1'b1, sampler_en:1'b1, ntt_en:1'b1, aux_en: 1'b0, mode:MLDSA_PWM_ACCUM_SMPL, sca_en:1'b0};
    localparam mldsa_opcode_t MLDSA_UOP_SIB       = '{keccak_en: 1'b1, sampler_en:1'b1, ntt_en:1'b0, aux_en: 1'b0, mode:MLDSA_SAMPLE_IN_BALL, sca_en:1'b0};
    localparam mldsa_opcode_t MLDSA_UOP_EXP_MASK  = '{keccak_en: 1'b1, sampler_en:1'b1, ntt_en:1'b0, aux_en: 1'b0, mode:MLDSA_EXP_MASK,       sca_en:1'b0};
    localparam mldsa_opcode_t MLDSA_UOP_NTT       = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b1, aux_en: 1'b0, mode:MLDSA_NTT,            sca_en:1'b0};
    localparam mldsa_opcode_t MLDSA_UOP_INTT      = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b1, aux_en: 1'b0, mode:MLDSA_INTT,           sca_en:1'b0};
    localparam mldsa_opcode_t MLDSA_UOP_PWM       = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b1, aux_en: 1'b0, mode:MLDSA_PWM,            sca_en:1'b0};
    localparam mldsa_opcode_t MLDSA_UOP_PWA       = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b1, aux_en: 1'b0, mode:MLDSA_PWA,            sca_en:1'b0};
    localparam mldsa_opcode_t MLDSA_UOP_PWS       = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b1, aux_en: 1'b0, mode:MLDSA_PWS,            sca_en:1'b0};
    //Load Keccak with data but don't run it yet
    localparam mldsa_opcode_t MLDSA_UOP_LD_SHAKE256 = '{keccak_en: 1'b1, sampler_en:1'b0, ntt_en:1'b0, aux_en: 1'b0, mode:MLDSA_SHAKE256, sca_en:1'b0};
    localparam mldsa_opcode_t MLDSA_UOP_LD_SHAKE128 = '{keccak_en: 1'b1, sampler_en:1'b0, ntt_en:1'b0, aux_en: 1'b0, mode:MLDSA_SHAKE128, sca_en:1'b0};
    //Run Keccak but don't load it
    localparam mldsa_opcode_t MLDSA_UOP_RUN_SHAKE256 = '{keccak_en: 1'b0, sampler_en:1'b1, ntt_en:1'b0, aux_en: 1'b0, mode:MLDSA_SHAKE256, sca_en:1'b0};
    localparam mldsa_opcode_t MLDSA_UOP_RUN_SHAKE128 = '{keccak_en: 1'b0, sampler_en:1'b1, ntt_en:1'b0, aux_en: 1'b0, mode:MLDSA_SHAKE128, sca_en:1'b0};
    // Aux functions
    localparam mldsa_opcode_t MLDSA_UOP_DECOMP     = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b0, aux_en: 1'b1, mode:MLDSA_DECOMP, sca_en:1'b0};
    localparam mldsa_opcode_t MLDSA_UOP_SKDECODE   = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b0, aux_en: 1'b1, mode:MLDSA_SKDECODE, sca_en:1'b0};
    localparam mldsa_opcode_t MLDSA_UOP_SKENCODE   = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b0, aux_en: 1'b1, mode:MLDSA_SKENCODE, sca_en:1'b0};
    localparam mldsa_opcode_t MLDSA_UOP_MAKEHINT   = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b0, aux_en: 1'b1, mode:MLDSA_MAKEHINT, sca_en:1'b0};
    localparam mldsa_opcode_t MLDSA_UOP_NORMCHK    = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b0, aux_en: 1'b1, mode:MLDSA_NORMCHK,  sca_en:1'b0};
    localparam mldsa_opcode_t MLDSA_UOP_SIGENCODE  = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b0, aux_en: 1'b1, mode:MLDSA_SIGENC,  sca_en:1'b0};
    localparam mldsa_opcode_t MLDSA_UOP_PKDECODE   = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b0, aux_en: 1'b1, mode:MLDSA_PKDECODE,  sca_en:1'b0};
    localparam mldsa_opcode_t MLDSA_UOP_SIGDEC_H   = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b0, aux_en: 1'b1, mode:MLDSA_SIGDEC_H,  sca_en:1'b0};
    localparam mldsa_opcode_t MLDSA_UOP_SIGDEC_Z   = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b0, aux_en: 1'b1, mode:MLDSA_SIGDEC_Z,  sca_en:1'b0};
    localparam mldsa_opcode_t MLDSA_UOP_HINTSUM    = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b0, aux_en: 1'b1, mode:MLDSA_HINTSUM,  sca_en:1'b0};
    localparam mldsa_opcode_t MLDSA_UOP_USEHINT    = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b0, aux_en: 1'b1, mode:MLDSA_USEHINT,  sca_en:1'b0};
    localparam mldsa_opcode_t MLDSA_UOP_PWR2RND    = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b0, aux_en: 1'b1, mode:MLDSA_PWR2RND,  sca_en:1'b0};

    //Immediate encodings
    localparam [MLDSA_IMM_WIDTH-1:0] MLDSA_NORMCHK_Z = 'h0000;
    localparam [MLDSA_IMM_WIDTH-1:0] MLDSA_NORMCHK_R0 = 'h0001;
    localparam [MLDSA_IMM_WIDTH-1:0] MLDSA_NORMCHK_CT0 = 'h0002;


    // MLDSA REGISTERS ID listing
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_NOP           = 'd0;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_CONST_ZERO_ID = 'd0;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_CONST_ONE_ID  = 'd1;

    // DEST register IDs
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_DEST_K_RHO_REG_ID = 'd2;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_DEST_MU_REG_ID    = 'd3;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_DEST_RHO_P_REG_ID = 'd4;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_DEST_SIG_C_REG_ID = 'd5;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_DEST_TR_REG_ID    = 'd6;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_DEST_VERIFY_RES_REG_ID = 'd7;

    //SRC register IDs
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_MSG_ID         = 'd15;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_SEED_ID        = 'd16;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_SIGN_RND_ID    = 'd17;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_K_ID           = 'd18;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_RHO_ID         = 'd19;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_RHO_P_ID       = 'd20;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_MU_ID          = 'd21;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_TR_ID          = 'd22;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_RHO_P_KAPPA_ID = 'd23;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_SIG_C_REG_ID   = 'd24;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_PK_REG_ID      = 'd25;
    
    //SK offsets in dwords
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_SK_S1_OFFSET = 'd32;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_SK_T0_OFFSET = 'd360;

    // MLDSA MEMORY LOCATIONS
    //COEFF DEPTH is 256/4
    localparam MLDSA_COEFF_DEPTH = MLDSA_N/COEFF_PER_CLK;
    //MEMORY INST 0
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_INST0_BASE = 0 << (MLDSA_MEM_ADDR_WIDTH-3);
    //S1 / NTT(S1)
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_S1_0_BASE = MLDSA_INST0_BASE;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_S1_1_BASE = MLDSA_S1_0_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_S1_2_BASE = MLDSA_S1_1_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_S1_3_BASE = MLDSA_S1_2_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_S1_4_BASE = MLDSA_S1_3_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_S1_5_BASE = MLDSA_S1_4_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_S1_6_BASE = MLDSA_S1_5_BASE + MLDSA_COEFF_DEPTH;
    // z for VERIFY
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_Z_0_BASE = MLDSA_INST0_BASE;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_Z_1_BASE = MLDSA_Z_0_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_Z_2_BASE = MLDSA_Z_1_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_Z_3_BASE = MLDSA_Z_2_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_Z_4_BASE = MLDSA_Z_3_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_Z_5_BASE = MLDSA_Z_4_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_Z_6_BASE = MLDSA_Z_5_BASE + MLDSA_COEFF_DEPTH;
    // z NTT for VERIFY
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_Z_NTT_0_BASE = MLDSA_INST0_BASE;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_Z_NTT_1_BASE = MLDSA_Z_NTT_0_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_Z_NTT_2_BASE = MLDSA_Z_NTT_1_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_Z_NTT_3_BASE = MLDSA_Z_NTT_2_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_Z_NTT_4_BASE = MLDSA_Z_NTT_3_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_Z_NTT_5_BASE = MLDSA_Z_NTT_4_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_Z_NTT_6_BASE = MLDSA_Z_NTT_5_BASE + MLDSA_COEFF_DEPTH;
    //s2 / NTT(s2)
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_S2_0_BASE = MLDSA_S1_6_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_S2_1_BASE = MLDSA_S2_0_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_S2_2_BASE = MLDSA_S2_1_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_S2_3_BASE = MLDSA_S2_2_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_S2_4_BASE = MLDSA_S2_3_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_S2_5_BASE = MLDSA_S2_4_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_S2_6_BASE = MLDSA_S2_5_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_S2_7_BASE = MLDSA_S2_6_BASE + MLDSA_COEFF_DEPTH;
    //t0 / NTT(t0) t1 / NTT(t1)
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_T0_BASE = MLDSA_S2_7_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_T1_BASE = MLDSA_T0_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_T2_BASE = MLDSA_T1_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_T3_BASE = MLDSA_T2_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_T4_BASE = MLDSA_T3_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_T5_BASE = MLDSA_T4_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_T6_BASE = MLDSA_T5_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_T7_BASE = MLDSA_T6_BASE + MLDSA_COEFF_DEPTH;
    //c.s1
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_CS1_BASE = MLDSA_T7_BASE + MLDSA_COEFF_DEPTH;
    // z
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_Z_BASE = MLDSA_T7_BASE + MLDSA_COEFF_DEPTH;
    // CT for VERIFY
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_CT_BASE = MLDSA_T7_BASE + MLDSA_COEFF_DEPTH;
    //c.s2
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_CS2_BASE = MLDSA_CS1_BASE + MLDSA_COEFF_DEPTH;
    // R0
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_R0_BASE = MLDSA_CS1_BASE + MLDSA_COEFF_DEPTH;
    //TEMP storage for NTT ops
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_TEMP0_BASE = MLDSA_CS2_BASE + MLDSA_COEFF_DEPTH;

    //MEMORY INST 1
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_INST1_BASE = 1 << (MLDSA_MEM_ADDR_WIDTH-3);
    // NTT(C)
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_C_NTT_BASE = MLDSA_INST1_BASE;
    // NTT(s1) for KEYGEN
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_S1_0_NTT_BASE = MLDSA_C_NTT_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_S1_1_NTT_BASE = MLDSA_S1_0_NTT_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_S1_2_NTT_BASE = MLDSA_S1_1_NTT_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_S1_3_NTT_BASE = MLDSA_S1_2_NTT_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_S1_4_NTT_BASE = MLDSA_S1_3_NTT_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_S1_5_NTT_BASE = MLDSA_S1_4_NTT_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_S1_6_NTT_BASE = MLDSA_S1_5_NTT_BASE + MLDSA_COEFF_DEPTH;
    // c.t0 for SIGNING
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_CT_0_BASE = MLDSA_C_NTT_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_CT_1_BASE = MLDSA_CT_0_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_CT_2_BASE = MLDSA_CT_1_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_CT_3_BASE = MLDSA_CT_2_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_CT_4_BASE = MLDSA_CT_3_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_CT_5_BASE = MLDSA_CT_4_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_CT_6_BASE = MLDSA_CT_5_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_CT_7_BASE = MLDSA_CT_6_BASE + MLDSA_COEFF_DEPTH;
    //hint_r
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_HINT_R_0_BASE = MLDSA_C_NTT_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_HINT_R_1_BASE = MLDSA_HINT_R_0_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_HINT_R_2_BASE = MLDSA_HINT_R_1_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_HINT_R_3_BASE = MLDSA_HINT_R_2_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_HINT_R_4_BASE = MLDSA_HINT_R_3_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_HINT_R_5_BASE = MLDSA_HINT_R_4_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_HINT_R_6_BASE = MLDSA_HINT_R_5_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_HINT_R_7_BASE = MLDSA_HINT_R_6_BASE + MLDSA_COEFF_DEPTH;

    //MEMORY INST 2
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_INST2_BASE = 2 << (MLDSA_MEM_ADDR_WIDTH-3);
    //Y
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_Y_0_BASE = MLDSA_INST2_BASE;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_Y_1_BASE = MLDSA_Y_0_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_Y_2_BASE = MLDSA_Y_1_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_Y_3_BASE = MLDSA_Y_2_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_Y_4_BASE = MLDSA_Y_3_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_Y_5_BASE = MLDSA_Y_4_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_Y_6_BASE = MLDSA_Y_5_BASE + MLDSA_COEFF_DEPTH;
    //NTT(Y)
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_Y_0_NTT_BASE = MLDSA_Y_6_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_Y_1_NTT_BASE = MLDSA_Y_0_NTT_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_Y_2_NTT_BASE = MLDSA_Y_1_NTT_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_Y_3_NTT_BASE = MLDSA_Y_2_NTT_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_Y_4_NTT_BASE = MLDSA_Y_3_NTT_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_Y_5_NTT_BASE = MLDSA_Y_4_NTT_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_Y_6_NTT_BASE = MLDSA_Y_5_NTT_BASE + MLDSA_COEFF_DEPTH;
    //W0
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_W0_0_BASE = MLDSA_Y_6_NTT_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_W0_1_BASE = MLDSA_W0_0_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_W0_2_BASE = MLDSA_W0_1_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_W0_3_BASE = MLDSA_W0_2_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_W0_4_BASE = MLDSA_W0_3_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_W0_5_BASE = MLDSA_W0_4_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_W0_6_BASE = MLDSA_W0_5_BASE + MLDSA_COEFF_DEPTH;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_W0_7_BASE = MLDSA_W0_6_BASE + MLDSA_COEFF_DEPTH;

    //MEMORY INST 3
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_INST3_BASE = 3 << (MLDSA_MEM_ADDR_WIDTH-3);

    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_AS0_BASE = MLDSA_INST3_BASE;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_AS0_INTT_BASE = MLDSA_AS0_BASE;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_AY0_BASE = MLDSA_INST3_BASE;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_AZ0_BASE = MLDSA_INST3_BASE;
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_TEMP3_BASE = MLDSA_INST3_BASE + MLDSA_COEFF_DEPTH;
    
    //SIB MEMORY
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_INST4_BASE = 4 << (MLDSA_MEM_ADDR_WIDTH-3);
    //C
    localparam [MLDSA_OPR_WIDTH-1 : 0] MLDSA_C_BASE = MLDSA_INST4_BASE;

    // MLDSA Subroutine listing
    //KG
    localparam [MLDSA_PROG_ADDR_W-1 : 0] MLDSA_RESET        = 'd0;
    localparam [MLDSA_PROG_ADDR_W-1 : 0] MLDSA_KG_S         = MLDSA_RESET + 2;
    localparam [MLDSA_PROG_ADDR_W-1 : 0] MLDSA_KG_JUMP_SIGN = MLDSA_KG_S + 98;
    localparam [MLDSA_PROG_ADDR_W-1 : 0] MLDSA_KG_E         = MLDSA_KG_S + 99;
    //Signing
    localparam [MLDSA_PROG_ADDR_W-1 : 0] MLDSA_SIGN_S            = MLDSA_KG_E + 2;
    localparam [MLDSA_PROG_ADDR_W-1 : 0] MLDSA_SIGN_CHECK_Y_CLR  = MLDSA_SIGN_S+ 5;
    localparam [MLDSA_PROG_ADDR_W-1 : 0] MLDSA_SIGN_MAKE_Y_S     = MLDSA_SIGN_CHECK_Y_CLR + 1;
    localparam [MLDSA_PROG_ADDR_W-1 : 0] MLDSA_SIGN_CHECK_W0_CLR = MLDSA_SIGN_MAKE_Y_S+ 14;
    localparam [MLDSA_PROG_ADDR_W-1 : 0] MLDSA_SIGN_MAKE_W_S     = MLDSA_SIGN_MAKE_Y_S+ 15;
    localparam [MLDSA_PROG_ADDR_W-1 : 0] MLDSA_SIGN_SET_Y        = MLDSA_SIGN_MAKE_W_S+ 64;
    localparam [MLDSA_PROG_ADDR_W-1 : 0] MLDSA_SIGN_MAKE_W       = MLDSA_SIGN_MAKE_W_S+ 66;
    localparam [MLDSA_PROG_ADDR_W-1 : 0] MLDSA_SIGN_SET_W0       = MLDSA_SIGN_MAKE_W+ 1;
    localparam [MLDSA_PROG_ADDR_W-1 : 0] MLDSA_SIGN_CHECK_C_CLR  = MLDSA_SIGN_SET_W0+ 1;
    localparam [MLDSA_PROG_ADDR_W-1 : 0] MLDSA_SIGN_MAKE_C       = MLDSA_SIGN_CHECK_C_CLR+ 1;
    localparam [MLDSA_PROG_ADDR_W-1 : 0] MLDSA_SIGN_SET_C        = MLDSA_SIGN_MAKE_C+ 2;
    localparam [MLDSA_PROG_ADDR_W-1 : 0] MLDSA_SIGN_E            = MLDSA_SIGN_SET_C + 1;
    //Verify
    localparam [MLDSA_PROG_ADDR_W-1 : 0] MLDSA_VERIFY_S          = MLDSA_SIGN_E + 2;
    localparam [MLDSA_PROG_ADDR_W-1 : 0] MLDSA_VERIFY_H_TR       = MLDSA_VERIFY_S + 9;
    localparam [MLDSA_PROG_ADDR_W-1 : 0] MLDSA_VERIFY_H_MU       = MLDSA_VERIFY_H_TR + 1;
    localparam [MLDSA_PROG_ADDR_W-1 : 0] MLDSA_VERIFY_MAKE_C     = MLDSA_VERIFY_H_MU + 2;
    localparam [MLDSA_PROG_ADDR_W-1 : 0] MLDSA_VERIFY_NTT_C      = MLDSA_VERIFY_MAKE_C + 1;
    localparam [MLDSA_PROG_ADDR_W-1 : 0] MLDSA_VERIFY_NTT_T1     = MLDSA_VERIFY_NTT_C + 1;
    localparam [MLDSA_PROG_ADDR_W-1 : 0] MLDSA_VERIFY_NTT_Z      = MLDSA_VERIFY_NTT_T1 + 8;
    localparam [MLDSA_PROG_ADDR_W-1 : 0] MLDSA_VERIFY_EXP_A      = MLDSA_VERIFY_NTT_Z + 7;
    localparam [MLDSA_PROG_ADDR_W-1 : 0] MLDSA_VERIFY_RES        = MLDSA_VERIFY_EXP_A + 80;
    localparam [MLDSA_PROG_ADDR_W-1 : 0] MLDSA_VERIFY_E          = MLDSA_VERIFY_RES + 4;

    localparam [MLDSA_PROG_ADDR_W-1 : 0] MLDSA_ERROR             = '1;

    //Signing Sequencer Subroutine listing
    localparam [MLDSA_PROG_ADDR_W-1 : 0] MLDSA_SIGN_INIT_S       = MLDSA_RESET + 2;
    localparam [MLDSA_PROG_ADDR_W-1 : 0] MLDSA_SIGN_CHECK_C_VLD  = MLDSA_SIGN_INIT_S + 24;
    localparam [MLDSA_PROG_ADDR_W-1 : 0] MLDSA_SIGN_VALID_S      = MLDSA_SIGN_CHECK_C_VLD + 1;
    localparam [MLDSA_PROG_ADDR_W-1 : 0] MLDSA_SIGN_CHECK_Y_VLD  = MLDSA_SIGN_VALID_S + 1;
    localparam [MLDSA_PROG_ADDR_W-1 : 0] MLDSA_SIGN_CLEAR_Y      = MLDSA_SIGN_VALID_S + 37;
    localparam [MLDSA_PROG_ADDR_W-1 : 0] MLDSA_SIGN_CHECK_W0_VLD = MLDSA_SIGN_VALID_S + 54;
    localparam [MLDSA_PROG_ADDR_W-1 : 0] MLDSA_SIGN_CLEAR_W0     = MLDSA_SIGN_VALID_S + 103;
    localparam [MLDSA_PROG_ADDR_W-1 : 0] MLDSA_SIGN_GEN_S        = MLDSA_SIGN_VALID_S + 105;
    localparam [MLDSA_PROG_ADDR_W-1 : 0] MLDSA_SIGN_CLEAR_C      = MLDSA_SIGN_GEN_S + 1;
    localparam [MLDSA_PROG_ADDR_W-1 : 0] MLDSA_SIGN_GEN_E        = MLDSA_SIGN_GEN_S + 9;


endpackage

`endif