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
// abr_seq_pkg.sv
// --------
// ABR instructions for Dilithium.
//
//
//======================================================================

`ifndef ABR_CTRL_PKG
`define ABR_CTRL_PKG

package abr_ctrl_pkg;
    import abr_params_pkg::*;
    import sampler_pkg::*;

    localparam integer ABR_OPR_WIDTH       = 15;
    localparam integer ABR_IMM_WIDTH       = 16;
    localparam ABR_PROG_ADDR_W             = 9;

    localparam SEED_NUM_DWORDS = 8;
    localparam MSG_NUM_DWORDS = 16;
    localparam PRIVKEY_NUM_DWORDS = 1224;
    localparam SIGN_RND_NUM_DWORDS = 8;
    localparam PUBKEY_NUM_DWORDS = 648;
    localparam PUBKEY_NUM_BYTES = PUBKEY_NUM_DWORDS * 4;
    localparam SIGNATURE_H_NUM_DWORDS = 21;
    localparam SIGNATURE_H_VALID_NUM_BYTES = 83;
    localparam SIGNATURE_Z_NUM_DWORDS = 1120;
    localparam SIGNATURE_C_NUM_DWORDS = 16;
    localparam SIGNATURE_NUM_DWORDS = SIGNATURE_H_NUM_DWORDS + SIGNATURE_Z_NUM_DWORDS + SIGNATURE_C_NUM_DWORDS;
    localparam VERIFY_RES_NUM_DWORDS = 16;
    localparam IV_NUM_DWORDS = 16;

    localparam T1_NUM_COEFF = 2048;
    localparam T1_COEFF_W = 10;

    typedef struct packed {
        logic [3:0][63:0] roh;
        logic [3:0][63:0] K;
        logic [7:0][63:0] tr;
        logic [83:0][63:0] s1;
        logic [95:0][63:0] s2;
        logic [415:0][63:0] t0;
    } abr_privkey_t;

    typedef union packed {
        abr_privkey_t enc;
        logic [1223:0][31:0] raw;
    } abr_privkey_u;

    typedef struct packed {
        logic [SIGNATURE_H_NUM_DWORDS-1:0][31:0] h;
        logic [SIGNATURE_Z_NUM_DWORDS-1:0][31:0] z;
        logic [SIGNATURE_C_NUM_DWORDS-1:0][31:0] c;
    } abr_signature_t;

    typedef union packed {
        abr_signature_t enc;
        logic [SIGNATURE_NUM_DWORDS-1:0][31:0] raw;
    } abr_signature_u;

    typedef struct packed {
        logic [T1_NUM_COEFF-1:0][T1_COEFF_W-1:0] t1;
        logic [7:0][31:0] roh;
    } abr_pubkey_t;

    typedef union packed {
        abr_pubkey_t enc;
        logic [PUBKEY_NUM_DWORDS-1:0][31:0] raw;
    } abr_pubkey_u;

    //FSM Controller for driving sampler 
    typedef enum logic [2:0] {
        ABR_CTRL_IDLE,
        ABR_CTRL_SHA3_START,
        ABR_CTRL_MSG_START,
        ABR_CTRL_MSG_LOAD,
        ABR_CTRL_MSG_WAIT,
        ABR_CTRL_FUNC_START,
        ABR_CTRL_DONE,
        ABR_CTRL_ERROR
      } abr_ctrl_fsm_state_e;

    typedef enum logic[3:0] {
        ABR_NTT_NONE,
        ABR_NTT,
        ABR_INTT,
        ABR_PWM,
        ABR_PWM_ACCUM,
        ABR_PWM_SMPL,
        ABR_PWM_ACCUM_SMPL,
        ABR_PWA,
        ABR_PWS
    } abr_ntt_mode_e;

    typedef enum logic[3:0] {
        ABR_AUX_NONE,
        ABR_SKDECODE,
        ABR_SKENCODE,
        ABR_PKDECODE,
        ABR_MAKEHINT,
        ABR_USEHINT,
        ABR_NORMCHK,
        ABR_PWR2RND,
        ABR_SIGENC,
        ABR_SIGDEC_H,
        ABR_SIGDEC_Z,
        ABR_HINTSUM,
        ABR_DECOMP
    } abr_aux_mode_e;


    typedef union packed {
        abr_sampler_mode_e sampler_mode;
        abr_aux_mode_e     aux_mode;
        abr_ntt_mode_e     ntt_mode;
    } abr_opcode_mode_u;

    typedef struct packed {
        logic keccak_en;
        logic sampler_en;
        logic ntt_en;
        logic aux_en;
        abr_opcode_mode_u mode;
        logic sca_en;
    } abr_opcode_t;

    typedef struct packed {
        abr_opcode_t                   opcode;
        logic [ABR_IMM_WIDTH-1 : 0]    imm;
        logic [ABR_OPR_WIDTH-1 : 0]    length;
        logic [ABR_OPR_WIDTH-1 : 0]    operand1;
        logic [ABR_OPR_WIDTH-1 : 0]    operand2;
        logic [ABR_OPR_WIDTH-1 : 0]    operand3;
    } abr_seq_instr_t;

    // DILITHIUM ISA
    localparam abr_opcode_t ABR_UOP_NOP       = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b0, aux_en: 1'b0, mode:ABR_SAMPLER_NONE,   sca_en:1'b0};
    localparam abr_opcode_t ABR_UOP_SHAKE256  = '{keccak_en: 1'b1, sampler_en:1'b1, ntt_en:1'b0, aux_en: 1'b0, mode:ABR_SHAKE256,       sca_en:1'b0};
    localparam abr_opcode_t ABR_UOP_SHAKE128  = '{keccak_en: 1'b1, sampler_en:1'b1, ntt_en:1'b0, aux_en: 1'b0, mode:ABR_SHAKE128,       sca_en:1'b0};
    localparam abr_opcode_t ABR_UOP_REJB      = '{keccak_en: 1'b1, sampler_en:1'b1, ntt_en:1'b0, aux_en: 1'b0, mode:ABR_REJ_BOUNDED,    sca_en:1'b0};
    localparam abr_opcode_t ABR_UOP_REJS_PWM  = '{keccak_en: 1'b1, sampler_en:1'b1, ntt_en:1'b1, aux_en: 1'b0, mode:ABR_PWM_SMPL,       sca_en:1'b0};
    localparam abr_opcode_t ABR_UOP_REJS_PWMA = '{keccak_en: 1'b1, sampler_en:1'b1, ntt_en:1'b1, aux_en: 1'b0, mode:ABR_PWM_ACCUM_SMPL, sca_en:1'b0};
    localparam abr_opcode_t ABR_UOP_SIB       = '{keccak_en: 1'b1, sampler_en:1'b1, ntt_en:1'b0, aux_en: 1'b0, mode:ABR_SAMPLE_IN_BALL, sca_en:1'b0};
    localparam abr_opcode_t ABR_UOP_EXP_MASK  = '{keccak_en: 1'b1, sampler_en:1'b1, ntt_en:1'b0, aux_en: 1'b0, mode:ABR_EXP_MASK,       sca_en:1'b0};
    localparam abr_opcode_t ABR_UOP_NTT       = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b1, aux_en: 1'b0, mode:ABR_NTT,            sca_en:1'b0};
    localparam abr_opcode_t ABR_UOP_INTT      = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b1, aux_en: 1'b0, mode:ABR_INTT,           sca_en:1'b0};
    localparam abr_opcode_t ABR_UOP_PWM       = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b1, aux_en: 1'b0, mode:ABR_PWM,            sca_en:1'b0};
    localparam abr_opcode_t ABR_UOP_PWA       = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b1, aux_en: 1'b0, mode:ABR_PWA,            sca_en:1'b0};
    localparam abr_opcode_t ABR_UOP_PWS       = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b1, aux_en: 1'b0, mode:ABR_PWS,            sca_en:1'b0};
    //Load Keccak with data but don't run it yet
    localparam abr_opcode_t ABR_UOP_LD_SHAKE256 = '{keccak_en: 1'b1, sampler_en:1'b0, ntt_en:1'b0, aux_en: 1'b0, mode:ABR_SHAKE256, sca_en:1'b0};
    localparam abr_opcode_t ABR_UOP_LD_SHAKE128 = '{keccak_en: 1'b1, sampler_en:1'b0, ntt_en:1'b0, aux_en: 1'b0, mode:ABR_SHAKE128, sca_en:1'b0};
    //Run Keccak but don't load it
    localparam abr_opcode_t ABR_UOP_RUN_SHAKE256 = '{keccak_en: 1'b0, sampler_en:1'b1, ntt_en:1'b0, aux_en: 1'b0, mode:ABR_SHAKE256, sca_en:1'b0};
    localparam abr_opcode_t ABR_UOP_RUN_SHAKE128 = '{keccak_en: 1'b0, sampler_en:1'b1, ntt_en:1'b0, aux_en: 1'b0, mode:ABR_SHAKE128, sca_en:1'b0};
    // Aux functions
    localparam abr_opcode_t ABR_UOP_DECOMP     = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b0, aux_en: 1'b1, mode:ABR_DECOMP, sca_en:1'b0};
    localparam abr_opcode_t ABR_UOP_SKDECODE   = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b0, aux_en: 1'b1, mode:ABR_SKDECODE, sca_en:1'b0};
    localparam abr_opcode_t ABR_UOP_SKENCODE   = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b0, aux_en: 1'b1, mode:ABR_SKENCODE, sca_en:1'b0};
    localparam abr_opcode_t ABR_UOP_MAKEHINT   = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b0, aux_en: 1'b1, mode:ABR_MAKEHINT, sca_en:1'b0};
    localparam abr_opcode_t ABR_UOP_NORMCHK    = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b0, aux_en: 1'b1, mode:ABR_NORMCHK,  sca_en:1'b0};
    localparam abr_opcode_t ABR_UOP_SIGENCODE  = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b0, aux_en: 1'b1, mode:ABR_SIGENC,  sca_en:1'b0};
    localparam abr_opcode_t ABR_UOP_PKDECODE   = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b0, aux_en: 1'b1, mode:ABR_PKDECODE,  sca_en:1'b0};
    localparam abr_opcode_t ABR_UOP_SIGDEC_H   = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b0, aux_en: 1'b1, mode:ABR_SIGDEC_H,  sca_en:1'b0};
    localparam abr_opcode_t ABR_UOP_SIGDEC_Z   = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b0, aux_en: 1'b1, mode:ABR_SIGDEC_Z,  sca_en:1'b0};
    localparam abr_opcode_t ABR_UOP_HINTSUM    = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b0, aux_en: 1'b1, mode:ABR_HINTSUM,  sca_en:1'b0};
    localparam abr_opcode_t ABR_UOP_USEHINT    = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b0, aux_en: 1'b1, mode:ABR_USEHINT,  sca_en:1'b0};

    //Immediate encodings
    localparam [ABR_IMM_WIDTH-1:0] ABR_NORMCHK_Z = 'h0000;
    localparam [ABR_IMM_WIDTH-1:0] ABR_NORMCHK_R0 = 'h0001;
    localparam [ABR_IMM_WIDTH-1:0] ABR_NORMCHK_CT0 = 'h0002;


    // DILITHIUM REGISTERS ID listing
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_NOP           = 'd0;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_CONST_ZERO_ID = 'd0;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_CONST_ONE_ID  = 'd1;

    // DEST register IDs
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_DEST_K_ROH_REG_ID = 'd2;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_DEST_MU_REG_ID    = 'd3;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_DEST_ROH_P_REG_ID = 'd4;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_DEST_SIG_C_REG_ID = 'd5;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_DEST_TR_REG_ID    = 'd6;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_DEST_VERIFY_RES_REG_ID = 'd7;

    //SRC register IDs
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_MSG_ID         = 'd15;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_SEED_ID        = 'd16;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_SIGN_RND_ID    = 'd17;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_K_ID           = 'd18;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_ROH_ID         = 'd19;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_ROH_P_ID       = 'd20;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_MU_ID          = 'd21;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_TR_ID          = 'd22;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_ROH_P_KAPPA_ID = 'd23;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_SIG_C_REG_ID   = 'd24;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_PK_REG_ID      = 'd24;
    
    // DILITHIUM MEMORY LOCATIONS
    //COEFF DEPTH is 256/4
    localparam ABR_COEFF_DEPTH = DILITHIUM_N/COEFF_PER_CLK;
    //MEMORY INST 0
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_INST0_BASE = 0 << (ABR_MEM_ADDR_WIDTH-3);
    //S1 / NTT(S1)
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_S1_0_BASE = ABR_INST0_BASE;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_S1_1_BASE = ABR_S1_0_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_S1_2_BASE = ABR_S1_1_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_S1_3_BASE = ABR_S1_2_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_S1_4_BASE = ABR_S1_3_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_S1_5_BASE = ABR_S1_4_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_S1_6_BASE = ABR_S1_5_BASE + ABR_COEFF_DEPTH;
    //s2 / NTT(s2)
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_S2_0_BASE = ABR_S1_6_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_S2_1_BASE = ABR_S2_0_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_S2_2_BASE = ABR_S2_1_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_S2_3_BASE = ABR_S2_2_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_S2_4_BASE = ABR_S2_3_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_S2_5_BASE = ABR_S2_4_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_S2_6_BASE = ABR_S2_5_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_S2_7_BASE = ABR_S2_6_BASE + ABR_COEFF_DEPTH;
    //t0 / NTT(t0) t1 / NTT(t1)
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_T0_BASE = ABR_S2_7_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_T1_BASE = ABR_T0_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_T2_BASE = ABR_T1_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_T3_BASE = ABR_T2_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_T4_BASE = ABR_T3_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_T5_BASE = ABR_T4_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_T6_BASE = ABR_T5_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_T7_BASE = ABR_T6_BASE + ABR_COEFF_DEPTH;
    // NTT(s1) for KEYGEN
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_S1_0_NTT_BASE = ABR_INST0_BASE;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_S1_1_NTT_BASE = ABR_S1_0_NTT_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_S1_2_NTT_BASE = ABR_S1_1_NTT_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_S1_3_NTT_BASE = ABR_S1_2_NTT_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_S1_4_NTT_BASE = ABR_S1_3_NTT_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_S1_5_NTT_BASE = ABR_S1_4_NTT_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_S1_6_NTT_BASE = ABR_S1_5_NTT_BASE + ABR_COEFF_DEPTH;
    //c.s1
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_CS1_0_BASE = ABR_T7_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_CS1_1_BASE = ABR_CS1_0_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_CS1_2_BASE = ABR_CS1_1_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_CS1_3_BASE = ABR_CS1_2_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_CS1_4_BASE = ABR_CS1_3_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_CS1_5_BASE = ABR_CS1_4_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_CS1_6_BASE = ABR_CS1_5_BASE + ABR_COEFF_DEPTH;
    // z
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_Z_0_BASE = ABR_T7_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_Z_1_BASE = ABR_Z_0_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_Z_2_BASE = ABR_Z_1_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_Z_3_BASE = ABR_Z_2_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_Z_4_BASE = ABR_Z_3_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_Z_5_BASE = ABR_Z_4_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_Z_6_BASE = ABR_Z_5_BASE + ABR_COEFF_DEPTH;
    // z NTT
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_Z_NTT_0_BASE = ABR_Z_0_BASE;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_Z_NTT_1_BASE = ABR_Z_NTT_0_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_Z_NTT_2_BASE = ABR_Z_NTT_1_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_Z_NTT_3_BASE = ABR_Z_NTT_2_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_Z_NTT_4_BASE = ABR_Z_NTT_3_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_Z_NTT_5_BASE = ABR_Z_NTT_4_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_Z_NTT_6_BASE = ABR_Z_NTT_5_BASE + ABR_COEFF_DEPTH;
    //c.s2 //c.t1
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_CS2_0_BASE = ABR_CS1_6_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_CS2_1_BASE = ABR_CS2_0_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_CS2_2_BASE = ABR_CS2_1_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_CS2_3_BASE = ABR_CS2_2_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_CS2_4_BASE = ABR_CS2_3_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_CS2_5_BASE = ABR_CS2_4_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_CS2_6_BASE = ABR_CS2_5_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_CS2_7_BASE = ABR_CS2_6_BASE + ABR_COEFF_DEPTH;

    localparam [ABR_OPR_WIDTH-1 : 0] ABR_CT1_0_BASE = ABR_CS1_6_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_CT1_1_BASE = ABR_CT1_0_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_CT1_2_BASE = ABR_CT1_1_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_CT1_3_BASE = ABR_CT1_2_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_CT1_4_BASE = ABR_CT1_3_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_CT1_5_BASE = ABR_CT1_4_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_CT1_6_BASE = ABR_CT1_5_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_CT1_7_BASE = ABR_CT1_6_BASE + ABR_COEFF_DEPTH;
    // R0
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_R0_0_BASE = ABR_CS1_6_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_R0_1_BASE = ABR_R0_0_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_R0_2_BASE = ABR_R0_1_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_R0_3_BASE = ABR_R0_2_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_R0_4_BASE = ABR_R0_3_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_R0_5_BASE = ABR_R0_4_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_R0_6_BASE = ABR_R0_5_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_R0_7_BASE = ABR_R0_6_BASE + ABR_COEFF_DEPTH;
    //TEMP storage for NTT ops
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_TEMP0_BASE = ABR_CS2_7_BASE + ABR_COEFF_DEPTH;

    //MEMORY INST 1
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_INST1_BASE = 1 << (ABR_MEM_ADDR_WIDTH-3);
    // NTT(C)
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_C_NTT_BASE = ABR_INST1_BASE;
    // c.t0
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_CT_0_BASE = ABR_C_NTT_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_CT_1_BASE = ABR_CT_0_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_CT_2_BASE = ABR_CT_1_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_CT_3_BASE = ABR_CT_2_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_CT_4_BASE = ABR_CT_3_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_CT_5_BASE = ABR_CT_4_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_CT_6_BASE = ABR_CT_5_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_CT_7_BASE = ABR_CT_6_BASE + ABR_COEFF_DEPTH;
    //hint_r
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_HINT_R_0_BASE = ABR_CT_7_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_HINT_R_1_BASE = ABR_HINT_R_0_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_HINT_R_2_BASE = ABR_HINT_R_1_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_HINT_R_3_BASE = ABR_HINT_R_2_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_HINT_R_4_BASE = ABR_HINT_R_3_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_HINT_R_5_BASE = ABR_HINT_R_4_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_HINT_R_6_BASE = ABR_HINT_R_5_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_HINT_R_7_BASE = ABR_HINT_R_6_BASE + ABR_COEFF_DEPTH;

    //MEMORY INST 2
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_INST2_BASE = 2 << (ABR_MEM_ADDR_WIDTH-3);
    //Y
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_Y_0_BASE = ABR_INST2_BASE;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_Y_1_BASE = ABR_Y_0_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_Y_2_BASE = ABR_Y_1_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_Y_3_BASE = ABR_Y_2_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_Y_4_BASE = ABR_Y_3_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_Y_5_BASE = ABR_Y_4_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_Y_6_BASE = ABR_Y_5_BASE + ABR_COEFF_DEPTH;
    //NTT(Y)
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_Y_0_NTT_BASE = ABR_Y_6_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_Y_1_NTT_BASE = ABR_Y_0_NTT_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_Y_2_NTT_BASE = ABR_Y_1_NTT_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_Y_3_NTT_BASE = ABR_Y_2_NTT_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_Y_4_NTT_BASE = ABR_Y_3_NTT_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_Y_5_NTT_BASE = ABR_Y_4_NTT_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_Y_6_NTT_BASE = ABR_Y_5_NTT_BASE + ABR_COEFF_DEPTH;
    //W0
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_W0_0_BASE = ABR_Y_6_NTT_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_W0_1_BASE = ABR_W0_0_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_W0_2_BASE = ABR_W0_1_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_W0_3_BASE = ABR_W0_2_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_W0_4_BASE = ABR_W0_3_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_W0_5_BASE = ABR_W0_4_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_W0_6_BASE = ABR_W0_5_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_W0_7_BASE = ABR_W0_6_BASE + ABR_COEFF_DEPTH;

    //MEMORY INST 3
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_INST3_BASE = 3 << (ABR_MEM_ADDR_WIDTH-3);
    // As / INTT(As) / Ay / W / Az
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_AS0_BASE = ABR_INST3_BASE;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_AS1_BASE = ABR_AS0_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_AS2_BASE = ABR_AS1_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_AS3_BASE = ABR_AS2_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_AS4_BASE = ABR_AS3_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_AS5_BASE = ABR_AS4_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_AS6_BASE = ABR_AS5_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_AS7_BASE = ABR_AS6_BASE + ABR_COEFF_DEPTH;

    localparam [ABR_OPR_WIDTH-1 : 0] ABR_AY0_BASE = ABR_INST3_BASE;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_AY1_BASE = ABR_AY0_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_AY2_BASE = ABR_AY1_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_AY3_BASE = ABR_AY2_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_AY4_BASE = ABR_AY3_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_AY5_BASE = ABR_AY4_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_AY6_BASE = ABR_AY5_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_AY7_BASE = ABR_AY6_BASE + ABR_COEFF_DEPTH;

    localparam [ABR_OPR_WIDTH-1 : 0] ABR_W_0_BASE = ABR_INST3_BASE;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_W_1_BASE = ABR_W_0_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_W_2_BASE = ABR_W_1_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_W_3_BASE = ABR_W_2_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_W_4_BASE = ABR_W_3_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_W_5_BASE = ABR_W_4_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_W_6_BASE = ABR_W_5_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_W_7_BASE = ABR_W_6_BASE + ABR_COEFF_DEPTH;

    localparam [ABR_OPR_WIDTH-1 : 0] ABR_AZ0_BASE = ABR_INST3_BASE;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_AZ1_BASE = ABR_AZ0_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_AZ2_BASE = ABR_AZ1_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_AZ3_BASE = ABR_AZ2_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_AZ4_BASE = ABR_AZ3_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_AZ5_BASE = ABR_AZ4_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_AZ6_BASE = ABR_AZ5_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_AZ7_BASE = ABR_AZ6_BASE + ABR_COEFF_DEPTH;

    localparam [ABR_OPR_WIDTH-1 : 0] ABR_AS0_INTT_BASE = ABR_AS0_BASE;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_AS1_INTT_BASE = ABR_AS0_INTT_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_AS2_INTT_BASE = ABR_AS1_INTT_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_AS3_INTT_BASE = ABR_AS2_INTT_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_AS4_INTT_BASE = ABR_AS3_INTT_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_AS5_INTT_BASE = ABR_AS4_INTT_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_AS6_INTT_BASE = ABR_AS5_INTT_BASE + ABR_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_AS7_INTT_BASE = ABR_AS6_INTT_BASE + ABR_COEFF_DEPTH;

    localparam [ABR_OPR_WIDTH-1 : 0] ABR_TEMP3_BASE = ABR_AS7_INTT_BASE + ABR_COEFF_DEPTH;
    
    //SIB MEMORY
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_INST4_BASE = 4 << (ABR_MEM_ADDR_WIDTH-3);
    //C
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_C_BASE = ABR_INST4_BASE;

    // DILITHIUM Subroutine listing
    //KG
    localparam [ABR_PROG_ADDR_W-1 : 0] DILITHIUM_RESET        = 'd0;
    localparam [ABR_PROG_ADDR_W-1 : 0] DILITHIUM_KG_S         = DILITHIUM_RESET + 2;
    localparam [ABR_PROG_ADDR_W-1 : 0] DILITHIUM_KG_JUMP_SIGN = DILITHIUM_KG_S + 97;
    localparam [ABR_PROG_ADDR_W-1 : 0] DILITHIUM_KG_E         = DILITHIUM_KG_S + 99;
    //Signing
    localparam [ABR_PROG_ADDR_W-1 : 0] DILITHIUM_SIGN_S            = DILITHIUM_KG_E + 2;
    localparam [ABR_PROG_ADDR_W-1 : 0] DILITHIUM_SIGN_CHECK_Y_CLR  = DILITHIUM_SIGN_S+ 5;
    localparam [ABR_PROG_ADDR_W-1 : 0] DILITHIUM_SIGN_MAKE_Y_S     = DILITHIUM_SIGN_CHECK_Y_CLR + 1;
    localparam [ABR_PROG_ADDR_W-1 : 0] DILITHIUM_SIGN_MAKE_W_S     = DILITHIUM_SIGN_MAKE_Y_S+ 14;
    localparam [ABR_PROG_ADDR_W-1 : 0] DILITHIUM_SIGN_SET_Y        = DILITHIUM_SIGN_MAKE_W_S+ 56;
    localparam [ABR_PROG_ADDR_W-1 : 0] DILITHIUM_SIGN_CHECK_W0_CLR = DILITHIUM_SIGN_MAKE_W_S+ 57;
    localparam [ABR_PROG_ADDR_W-1 : 0] DILITHIUM_SIGN_MAKE_W       = DILITHIUM_SIGN_MAKE_W_S+ 67;
    localparam [ABR_PROG_ADDR_W-1 : 0] DILITHIUM_SIGN_SET_W0       = DILITHIUM_SIGN_MAKE_W+ 1;
    localparam [ABR_PROG_ADDR_W-1 : 0] DILITHIUM_SIGN_CHECK_C_CLR  = DILITHIUM_SIGN_SET_W0+ 1;
    localparam [ABR_PROG_ADDR_W-1 : 0] DILITHIUM_SIGN_MAKE_C       = DILITHIUM_SIGN_CHECK_C_CLR+ 1;
    localparam [ABR_PROG_ADDR_W-1 : 0] DILITHIUM_SIGN_SET_C        = DILITHIUM_SIGN_MAKE_C+ 2;
    localparam [ABR_PROG_ADDR_W-1 : 0] DILITHIUM_SIGN_E            = DILITHIUM_SIGN_SET_C + 1;
    //Verify
    localparam [ABR_PROG_ADDR_W-1 : 0] DILITHIUM_VERIFY_S          = DILITHIUM_SIGN_E + 2;
    localparam [ABR_PROG_ADDR_W-1 : 0] DILITHIUM_VERIFY_NTT_Z      = DILITHIUM_VERIFY_S + 4;
    localparam [ABR_PROG_ADDR_W-1 : 0] DILITHIUM_VERIFY_EXP_A      = DILITHIUM_VERIFY_NTT_Z + 7;
    localparam [ABR_PROG_ADDR_W-1 : 0] DILITHIUM_VERIFY_H_TR       = DILITHIUM_VERIFY_EXP_A + 56;
    localparam [ABR_PROG_ADDR_W-1 : 0] DILITHIUM_VERIFY_H_MU       = DILITHIUM_VERIFY_H_TR + 1;
    localparam [ABR_PROG_ADDR_W-1 : 0] DILITHIUM_VERIFY_MAKE_C     = DILITHIUM_VERIFY_H_MU + 2;
    localparam [ABR_PROG_ADDR_W-1 : 0] DILITHIUM_VERIFY_NTT_C      = DILITHIUM_VERIFY_MAKE_C + 1;
    localparam [ABR_PROG_ADDR_W-1 : 0] DILITHIUM_VERIFY_NTT_T1     = DILITHIUM_VERIFY_NTT_C + 1;
    localparam [ABR_PROG_ADDR_W-1 : 0] DILITHIUM_VERIFY_AZ_CT1     = DILITHIUM_VERIFY_NTT_T1 + 8;
    localparam [ABR_PROG_ADDR_W-1 : 0] DILITHIUM_VERIFY_MAKE_W     = DILITHIUM_VERIFY_AZ_CT1 + 16;
    localparam [ABR_PROG_ADDR_W-1 : 0] DILITHIUM_VERIFY_E          = DILITHIUM_VERIFY_MAKE_W + 11;

    localparam [ABR_PROG_ADDR_W-1 : 0] DILITHIUM_ERROR             = '1;

    //Signing Sequencer Subroutine listing
    localparam [ABR_PROG_ADDR_W-1 : 0] DILITHIUM_SIGN_INIT_S       = DILITHIUM_RESET + 2;
    localparam [ABR_PROG_ADDR_W-1 : 0] DILITHIUM_SIGN_CHECK_C_VLD  = DILITHIUM_SIGN_INIT_S + 24;
    localparam [ABR_PROG_ADDR_W-1 : 0] DILITHIUM_SIGN_VALID_S      = DILITHIUM_SIGN_CHECK_C_VLD + 1;
    localparam [ABR_PROG_ADDR_W-1 : 0] DILITHIUM_SIGN_CHECK_Y_VLD  = DILITHIUM_SIGN_VALID_S + 16;
    localparam [ABR_PROG_ADDR_W-1 : 0] DILITHIUM_SIGN_CLEAR_Y      = DILITHIUM_SIGN_VALID_S + 24;
    localparam [ABR_PROG_ADDR_W-1 : 0] DILITHIUM_SIGN_CHECK_W0_VLD = DILITHIUM_SIGN_VALID_S + 41;
    localparam [ABR_PROG_ADDR_W-1 : 0] DILITHIUM_SIGN_CLEAR_W0     = DILITHIUM_SIGN_VALID_S + 50;
    localparam [ABR_PROG_ADDR_W-1 : 0] DILITHIUM_SIGN_GEN_S        = DILITHIUM_SIGN_VALID_S + 79;
    localparam [ABR_PROG_ADDR_W-1 : 0] DILITHIUM_SIGN_CLEAR_C      = DILITHIUM_SIGN_GEN_S + 1;
    localparam [ABR_PROG_ADDR_W-1 : 0] DILITHIUM_SIGN_GEN_E        = DILITHIUM_SIGN_GEN_S + 3;


endpackage

`endif
