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
// abr_ctrl_pkg.sv
// --------
// ABR instructions for MLDSA.
//
//
//======================================================================

`ifndef ABR_CTRL_PKG
`define ABR_CTRL_PKG

package abr_ctrl_pkg;
    import abr_params_pkg::*;
    import abr_sampler_pkg::*;

    localparam integer ABR_OPR_WIDTH       = 15;
    localparam integer ABR_IMM_WIDTH       = 16;
    localparam ABR_PROG_ADDR_W             = 10;

    localparam SEED_NUM_DWORDS = 8;
    localparam MLDSA_MSG_NUM_DWORDS = 16;
    localparam MLKEM_MSG_NUM_DWORDS = 8;
    localparam MU_NUM_DWORDS = 16;
    localparam PRIVKEY_NUM_DWORDS = 1224;
    localparam PRIVKEY_REG_NUM_DWORDS = 32;
    localparam PRIVKEY_REG_RHO_NUM_DWORDS = 8;
    localparam PRIVKEY_MEM_NUM_DWORDS = PRIVKEY_NUM_DWORDS - PRIVKEY_REG_NUM_DWORDS;
    localparam SIGN_RND_NUM_DWORDS = 8;
    localparam PUBKEY_NUM_DWORDS = 648;
    localparam PUBKEY_NUM_BYTES = PUBKEY_NUM_DWORDS * 4;
    localparam SIGNATURE_H_NUM_DWORDS = 21;
    localparam SIGNATURE_H_VALID_NUM_BYTES = 83;
    localparam SIGNATURE_Z_NUM_DWORDS = 1120;
    localparam SIGNATURE_C_NUM_DWORDS = 16;
    localparam SIGNATURE_NUM_DWORDS = SIGNATURE_H_NUM_DWORDS + SIGNATURE_Z_NUM_DWORDS + SIGNATURE_C_NUM_DWORDS;
    localparam SIGNATURE_REG_NUM_DWORDS = SIGNATURE_H_NUM_DWORDS + SIGNATURE_C_NUM_DWORDS;
    localparam VERIFY_RES_NUM_DWORDS = 16;
    localparam ENTROPY_NUM_DWORDS = 16;
    localparam CTX_NUM_DWORDS = 64;
    localparam CTX_SIZE_W = $clog2(CTX_NUM_DWORDS*4);
    localparam STREAM_MSG_W = 32;
    localparam STREAM_MSG_STROBE_W = STREAM_MSG_W/8;
    localparam SHAREDKEY_NUM_DWORDS = 8;
    localparam EK_NUM_DWORDS = 392;
    localparam EK_NUM_BYTES = EK_NUM_DWORDS * 4;
    localparam DK_NUM_DWORDS = 792;
    localparam DK_NUM_BYTES = DK_NUM_DWORDS * 4;
    localparam MLKEM_EK_MEM_NUM_DWORDS = 384;
    localparam MLKEM_DK_MEM_NUM_DWORDS = 768;
    localparam MLKEM_CIPHERTEXT_MEM_NUM_DWORDS = 392;
    localparam CT_NUM_BYTES = MLKEM_CIPHERTEXT_MEM_NUM_DWORDS*4;
    localparam MLKEM_MSG_MEM_NUM_DWORDS = 8;
    localparam SCRATCH_REG_NUM_DWORDS = 48;

    localparam T1_NUM_COEFF = 2048;
    localparam T1_COEFF_W = 10;
    
    localparam RND_W = 236; //5*46 + 6
    localparam LFSR_W = RND_W / 2;

    localparam SK_MEM_DEPTH = 1192;
    localparam SK_MEM_BANK_DEPTH = SK_MEM_DEPTH/2;
    localparam SK_MEM_BANK_ADDR_W = $clog2(SK_MEM_BANK_DEPTH);
    localparam SK_MEM_BANK_DATA_W = DATA_WIDTH;

    localparam SIG_Z_MEM_DATA_W = 160;
    localparam SIG_Z_MEM_NUM_DWORD = SIG_Z_MEM_DATA_W/32;
    localparam SIG_Z_MEM_WSTROBE_W = SIG_Z_MEM_DATA_W/8;
    localparam SIG_Z_MEM_DEPTH = (SIGNATURE_Z_NUM_DWORDS*32)/SIG_Z_MEM_DATA_W;
    localparam SIG_ADDR_W = $clog2(SIGNATURE_NUM_DWORDS);
    localparam SIG_Z_MEM_ADDR_W = $clog2(SIG_Z_MEM_DEPTH);
    localparam SIG_Z_MEM_OFFSET_W = $clog2(SIG_Z_MEM_DATA_W/32);
    localparam SIG_H_REG_ADDR_W = $clog2(SIGNATURE_H_NUM_DWORDS);
    localparam SIG_C_REG_ADDR_W = $clog2(SIGNATURE_C_NUM_DWORDS);

    localparam PK_MEM_DEPTH = 64;
    localparam PK_MEM_DATA_W = 320;
    localparam PK_MEM_NUM_DWORDS = (PK_MEM_DATA_W)/32;
    localparam PK_MEM_WSTROBE_W = PK_MEM_DATA_W/8;
    localparam PK_ADDR_W = $clog2(PUBKEY_NUM_DWORDS);
    localparam PK_MEM_ADDR_W = $clog2(PK_MEM_DEPTH);
    localparam PK_MEM_OFFSET_W = $clog2(PK_MEM_DATA_W/32);
    localparam PK_RHO_REG_ADDR_W = $clog2(PRIVKEY_REG_RHO_NUM_DWORDS);
    
    typedef struct packed {
        logic [SIGNATURE_H_NUM_DWORDS-1:0][31:0] h;
        logic [SIGNATURE_C_NUM_DWORDS-1:0][31:0] c;
    } mldsa_signature_t; //37 dwords

    typedef union packed {
        mldsa_signature_t enc;
        logic [SIGNATURE_REG_NUM_DWORDS-1:0][31:0] raw;
    } mldsa_signature_u;

    typedef struct packed {
        logic [SIG_Z_MEM_ADDR_W-1:0] addr;
        logic [SIG_Z_MEM_OFFSET_W-1:0] offset;
    } mldsa_signature_z_addr_t;

    typedef struct packed {
        logic [PK_MEM_ADDR_W-1:0] addr;
        logic [PK_MEM_OFFSET_W-1:0] offset;
    } mldsa_pubkey_mem_addr_t;

    typedef struct packed {
        logic [7:0][63:0] rho_p;
        logic [7:0][63:0] tr;
        logic [3:0][63:0] K;
        logic [3:0][63:0] rho;
    } mldsa_scratch_reg_t; //48 dwords

    typedef struct packed {
        logic [3:0][63:0] rsvd;
        logic [7:0][31:0] shared_key;
        logic [3:0][63:0] sigma; //cbd input randomness
        logic [7:0][31:0] seed_z;
        logic [3:0][63:0] tr; //hash of EK
        logic [3:0][63:0] rho;
    } mlkem_scratch_reg_t; //48 dwords

    typedef union packed {
        mlkem_scratch_reg_t mlkem_enc;
        mldsa_scratch_reg_t mldsa_enc;
        logic [SCRATCH_REG_NUM_DWORDS-1:0][31:0] raw;
    } abr_scratch_reg_u;

    //FSM Controller for streaming msg
    typedef enum logic [2:0] {
        MLDSA_MSG_IDLE,
        MLDSA_MSG_CTX_SIZE,
        MLDSA_MSG_CTX,
        MLDSA_MSG_RDY,
        MLDSA_MSG_FLUSH,
        MLDSA_MSG_DONE
    } mldsa_stream_msg_fsm_state_e;

    //FSM Controller for driving sampler 
    typedef enum logic [2:0] {
        ABR_CTRL_IDLE,
        ABR_CTRL_SHA3_START,
        ABR_CTRL_MSG_START,
        ABR_CTRL_MSG_LOAD,
        ABR_CTRL_MSG_WAIT,
        ABR_CTRL_FUNC_START,
        ABR_CTRL_DONE,
        ABR_CTRL_STALLED
    } abr_ctrl_fsm_state_e;

    typedef enum logic[4:0] {
        ABR_NTT_NONE,
        MLDSA_NTT,
        MLDSA_INTT,
        MLDSA_PWM,
        MLDSA_PWM_ACCUM,
        MLDSA_PWM_SMPL,
        MLDSA_PWM_ACCUM_SMPL,
        MLDSA_PWA,
        MLDSA_PWS,
        MLDSA_PWM_INTT,
        MLKEM_NTT,
        MLKEM_INTT,
        MLKEM_PWM,
        MLKEM_PWM_ACCUM,
        MLKEM_PWM_SMPL,
        MLKEM_PWM_ACCUM_SMPL,
        MLKEM_PWA,
        MLKEM_PWS,
        MLKEM_PWM_INTT
    } abr_ntt_mode_e;

    typedef enum logic[4:0] {
        ABR_AUX_NONE,
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
        MLDSA_DECOMP,
        MLDSA_LFSR,
        MLKEM_COMPRESS,
        MLKEM_DECOMPRESS
    } abr_aux_mode_e;

    typedef union packed {
        abr_sampler_mode_e   sampler_mode;
        abr_aux_mode_e       aux_mode;
        abr_ntt_mode_e       ntt_mode;
    } abr_opcode_mode_u;

    typedef struct packed {
        logic keccak_en;
        logic sampler_en;
        logic ntt_en;
        logic aux_en;
        abr_opcode_mode_u mode;
        logic masking_en;
        logic shuffling_en;
    } abr_opcode_t;

    typedef struct packed {
        abr_opcode_t                   opcode;
        logic [ABR_IMM_WIDTH-1 : 0]    imm;
        logic [ABR_OPR_WIDTH-1 : 0]    length;
        logic [ABR_OPR_WIDTH-1 : 0]    operand1;
        logic [ABR_OPR_WIDTH-1 : 0]    operand2;
        logic [ABR_OPR_WIDTH-1 : 0]    operand3;
    } abr_seq_instr_t;

    // MLDSA ISA
    localparam abr_opcode_t ABR_UOP_NOP              = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b0, aux_en: 1'b0, mode:ABR_SAMPLER_NONE,     masking_en:1'b0, shuffling_en:1'b0};
    localparam abr_opcode_t ABR_UOP_SHAKE256         = '{keccak_en: 1'b1, sampler_en:1'b1, ntt_en:1'b0, aux_en: 1'b0, mode:ABR_SHAKE256,         masking_en:1'b0, shuffling_en:1'b0};
    localparam abr_opcode_t ABR_UOP_SHAKE128         = '{keccak_en: 1'b1, sampler_en:1'b1, ntt_en:1'b0, aux_en: 1'b0, mode:ABR_SHAKE128,         masking_en:1'b0, shuffling_en:1'b0};
    localparam abr_opcode_t ABR_UOP_REJB             = '{keccak_en: 1'b1, sampler_en:1'b1, ntt_en:1'b0, aux_en: 1'b0, mode:ABR_REJ_BOUNDED,      masking_en:1'b0, shuffling_en:1'b0};
    localparam abr_opcode_t ABR_UOP_REJS_PWM         = '{keccak_en: 1'b1, sampler_en:1'b1, ntt_en:1'b1, aux_en: 1'b0, mode:MLDSA_PWM_SMPL,       masking_en:1'b0, shuffling_en:1'b0};
    localparam abr_opcode_t ABR_UOP_REJS_PWMA        = '{keccak_en: 1'b1, sampler_en:1'b1, ntt_en:1'b1, aux_en: 1'b0, mode:MLDSA_PWM_ACCUM_SMPL, masking_en:1'b0, shuffling_en:1'b0};
    localparam abr_opcode_t ABR_UOP_REJS_MASKED_PWM  = '{keccak_en: 1'b1, sampler_en:1'b1, ntt_en:1'b1, aux_en: 1'b0, mode:MLDSA_PWM_SMPL,       masking_en:1'b1, shuffling_en:1'b0};
    localparam abr_opcode_t ABR_UOP_REJS_MASKED_PWMA = '{keccak_en: 1'b1, sampler_en:1'b1, ntt_en:1'b1, aux_en: 1'b0, mode:MLDSA_PWM_ACCUM_SMPL, masking_en:1'b1, shuffling_en:1'b0};
    localparam abr_opcode_t ABR_UOP_SIB              = '{keccak_en: 1'b1, sampler_en:1'b1, ntt_en:1'b0, aux_en: 1'b0, mode:ABR_SAMPLE_IN_BALL,   masking_en:1'b0, shuffling_en:1'b0};
    localparam abr_opcode_t ABR_UOP_EXP_MASK         = '{keccak_en: 1'b1, sampler_en:1'b1, ntt_en:1'b0, aux_en: 1'b0, mode:ABR_EXP_MASK,         masking_en:1'b0, shuffling_en:1'b0};
    localparam abr_opcode_t ABR_UOP_NTT              = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b1, aux_en: 1'b0, mode:MLDSA_NTT,            masking_en:1'b0, shuffling_en:1'b1};
    localparam abr_opcode_t ABR_UOP_INTT             = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b1, aux_en: 1'b0, mode:MLDSA_INTT,           masking_en:1'b0, shuffling_en:1'b1};
    localparam abr_opcode_t ABR_UOP_PWM              = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b1, aux_en: 1'b0, mode:MLDSA_PWM,            masking_en:1'b0, shuffling_en:1'b1};
    localparam abr_opcode_t ABR_UOP_PWA              = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b1, aux_en: 1'b0, mode:MLDSA_PWA,            masking_en:1'b0, shuffling_en:1'b1};
    localparam abr_opcode_t ABR_UOP_PWS              = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b1, aux_en: 1'b0, mode:MLDSA_PWS,            masking_en:1'b0, shuffling_en:1'b1};
    localparam abr_opcode_t ABR_UOP_MASKED_NTT       = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b1, aux_en: 1'b0, mode:MLDSA_NTT,            masking_en:1'b1, shuffling_en:1'b1};
    localparam abr_opcode_t ABR_UOP_MASKED_INTT      = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b1, aux_en: 1'b0, mode:MLDSA_INTT,           masking_en:1'b1, shuffling_en:1'b1};
    localparam abr_opcode_t ABR_UOP_MASKED_PWM       = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b1, aux_en: 1'b0, mode:MLDSA_PWM,            masking_en:1'b1, shuffling_en:1'b1}; //TODO: if shuffling_en can be kept 1 always, we don't need sampler_mode input to ntt. Else, we need to distinguish between sampelr and non-sampler PWM with masking and no shuffling (since input delay balancing is diff for both these cases)
    localparam abr_opcode_t ABR_UOP_MASKED_PWA       = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b1, aux_en: 1'b0, mode:MLDSA_PWA,            masking_en:1'b1, shuffling_en:1'b1};
    localparam abr_opcode_t ABR_UOP_MASKED_PWS       = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b1, aux_en: 1'b0, mode:MLDSA_PWS,            masking_en:1'b1, shuffling_en:1'b1};
    // MLKEM ISA
    localparam abr_opcode_t ABR_UOP_SHA512                 = '{keccak_en: 1'b1, sampler_en:1'b1, ntt_en:1'b0, aux_en: 1'b0, mode:ABR_SHA512,           masking_en:1'b0, shuffling_en:1'b0};
    localparam abr_opcode_t ABR_UOP_SHA256                 = '{keccak_en: 1'b1, sampler_en:1'b1, ntt_en:1'b0, aux_en: 1'b0, mode:ABR_SHA256,           masking_en:1'b0, shuffling_en:1'b0};
    localparam abr_opcode_t ABR_UOP_CBD                    = '{keccak_en: 1'b1, sampler_en:1'b1, ntt_en:1'b0, aux_en: 1'b0, mode:ABR_CBD_SAMPLER,      masking_en:1'b0, shuffling_en:1'b0};
    localparam abr_opcode_t ABR_UOP_MLKEM_REJS_PWM         = '{keccak_en: 1'b1, sampler_en:1'b1, ntt_en:1'b1, aux_en: 1'b0, mode:MLKEM_PWM_SMPL,       masking_en:1'b0, shuffling_en:1'b0};
    localparam abr_opcode_t ABR_UOP_MLKEM_REJS_PWMA        = '{keccak_en: 1'b1, sampler_en:1'b1, ntt_en:1'b1, aux_en: 1'b0, mode:MLKEM_PWM_ACCUM_SMPL, masking_en:1'b0, shuffling_en:1'b0};
    localparam abr_opcode_t ABR_UOP_MLKEM_MASKED_REJS_PWM  = '{keccak_en: 1'b1, sampler_en:1'b1, ntt_en:1'b1, aux_en: 1'b0, mode:MLKEM_PWM_SMPL,       masking_en:1'b1, shuffling_en:1'b0};
    localparam abr_opcode_t ABR_UOP_MLKEM_MASKED_REJS_PWMA = '{keccak_en: 1'b1, sampler_en:1'b1, ntt_en:1'b1, aux_en: 1'b0, mode:MLKEM_PWM_ACCUM_SMPL, masking_en:1'b1, shuffling_en:1'b0};
    localparam abr_opcode_t ABR_UOP_MLKEM_NTT              = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b1, aux_en: 1'b0, mode:MLKEM_NTT,            masking_en:1'b0, shuffling_en:1'b1};
    localparam abr_opcode_t ABR_UOP_MLKEM_INTT             = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b1, aux_en: 1'b0, mode:MLKEM_INTT,           masking_en:1'b0, shuffling_en:1'b1};
    localparam abr_opcode_t ABR_UOP_MLKEM_MASKED_INTT      = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b1, aux_en: 1'b0, mode:MLKEM_INTT,           masking_en:1'b1, shuffling_en:1'b1};
    localparam abr_opcode_t ABR_UOP_MLKEM_PWA              = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b1, aux_en: 1'b0, mode:MLKEM_PWA,            masking_en:1'b0, shuffling_en:1'b1};
    localparam abr_opcode_t ABR_UOP_MLKEM_PWM              = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b1, aux_en: 1'b0, mode:MLKEM_PWM,            masking_en:1'b0, shuffling_en:1'b1};
    localparam abr_opcode_t ABR_UOP_MLKEM_PWMA             = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b1, aux_en: 1'b0, mode:MLKEM_PWM_ACCUM,      masking_en:1'b0, shuffling_en:1'b1};
    localparam abr_opcode_t ABR_UOP_MLKEM_MASKED_PWM       = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b1, aux_en: 1'b0, mode:MLKEM_PWM,            masking_en:1'b1, shuffling_en:1'b1};
    localparam abr_opcode_t ABR_UOP_MLKEM_MASKED_PWMA      = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b1, aux_en: 1'b0, mode:MLKEM_PWM_ACCUM,      masking_en:1'b1, shuffling_en:1'b1};
    localparam abr_opcode_t ABR_UOP_MLKEM_PWS              = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b1, aux_en: 1'b0, mode:MLKEM_PWS,            masking_en:1'b0, shuffling_en:1'b1};

    //Load Keccak with data but don't run it yet
    localparam abr_opcode_t ABR_UOP_LD_SHAKE256 = '{keccak_en: 1'b1, sampler_en:1'b0, ntt_en:1'b0, aux_en: 1'b0, mode:ABR_SHAKE256, masking_en:1'b0, shuffling_en:1'b0};
    localparam abr_opcode_t ABR_UOP_LD_SHAKE128 = '{keccak_en: 1'b1, sampler_en:1'b0, ntt_en:1'b0, aux_en: 1'b0, mode:ABR_SHAKE128, masking_en:1'b0, shuffling_en:1'b0};
    localparam abr_opcode_t ABR_UOP_LD_SHA512   = '{keccak_en: 1'b1, sampler_en:1'b0, ntt_en:1'b0, aux_en: 1'b0, mode:ABR_SHA512, masking_en:1'b0, shuffling_en:1'b0};
    localparam abr_opcode_t ABR_UOP_LD_SHA256   = '{keccak_en: 1'b1, sampler_en:1'b0, ntt_en:1'b0, aux_en: 1'b0, mode:ABR_SHA256, masking_en:1'b0, shuffling_en:1'b0};
    //Run Keccak but don't load it
    localparam abr_opcode_t ABR_UOP_RUN_SHAKE256 = '{keccak_en: 1'b0, sampler_en:1'b1, ntt_en:1'b0, aux_en: 1'b0, mode:ABR_SHAKE256, masking_en:1'b0, shuffling_en:1'b0};
    localparam abr_opcode_t ABR_UOP_RUN_SHAKE128 = '{keccak_en: 1'b0, sampler_en:1'b1, ntt_en:1'b0, aux_en: 1'b0, mode:ABR_SHAKE128, masking_en:1'b0, shuffling_en:1'b0};
    localparam abr_opcode_t ABR_UOP_RUN_SHA512   = '{keccak_en: 1'b0, sampler_en:1'b1, ntt_en:1'b0, aux_en: 1'b0, mode:ABR_SHA512, masking_en:1'b0, shuffling_en:1'b0};
    localparam abr_opcode_t ABR_UOP_RUN_SHA256   = '{keccak_en: 1'b0, sampler_en:1'b1, ntt_en:1'b0, aux_en: 1'b0, mode:ABR_SHA256, masking_en:1'b0, shuffling_en:1'b0};
    // Aux functions
    localparam abr_opcode_t ABR_UOP_DECOMPOSE  = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b0, aux_en: 1'b1, mode:MLDSA_DECOMP, masking_en:1'b0, shuffling_en:1'b0};
    localparam abr_opcode_t ABR_UOP_SKDECODE   = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b0, aux_en: 1'b1, mode:MLDSA_SKDECODE, masking_en:1'b0, shuffling_en:1'b0};
    localparam abr_opcode_t ABR_UOP_SKENCODE   = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b0, aux_en: 1'b1, mode:MLDSA_SKENCODE, masking_en:1'b0, shuffling_en:1'b0};
    localparam abr_opcode_t ABR_UOP_MAKEHINT   = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b0, aux_en: 1'b1, mode:MLDSA_MAKEHINT, masking_en:1'b0, shuffling_en:1'b0};
    localparam abr_opcode_t ABR_UOP_NORMCHK    = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b0, aux_en: 1'b1, mode:MLDSA_NORMCHK,  masking_en:1'b0, shuffling_en:1'b0};
    localparam abr_opcode_t ABR_UOP_SIGENCODE  = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b0, aux_en: 1'b1, mode:MLDSA_SIGENC,  masking_en:1'b0, shuffling_en:1'b0};
    localparam abr_opcode_t ABR_UOP_PKDECODE   = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b0, aux_en: 1'b1, mode:MLDSA_PKDECODE,  masking_en:1'b0, shuffling_en:1'b0};
    localparam abr_opcode_t ABR_UOP_SIGDEC_H   = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b0, aux_en: 1'b1, mode:MLDSA_SIGDEC_H,  masking_en:1'b0, shuffling_en:1'b0};
    localparam abr_opcode_t ABR_UOP_SIGDEC_Z   = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b0, aux_en: 1'b1, mode:MLDSA_SIGDEC_Z,  masking_en:1'b0, shuffling_en:1'b0};
    localparam abr_opcode_t ABR_UOP_HINTSUM    = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b0, aux_en: 1'b1, mode:MLDSA_HINTSUM,  masking_en:1'b0, shuffling_en:1'b0};
    localparam abr_opcode_t ABR_UOP_USEHINT    = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b0, aux_en: 1'b1, mode:MLDSA_USEHINT,  masking_en:1'b0, shuffling_en:1'b0};
    localparam abr_opcode_t ABR_UOP_PWR2RND    = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b0, aux_en: 1'b1, mode:MLDSA_PWR2RND,  masking_en:1'b0, shuffling_en:1'b0};
    localparam abr_opcode_t ABR_UOP_LFSR       = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b0, aux_en: 1'b1, mode:MLDSA_LFSR,     masking_en:1'b0, shuffling_en:1'b0};
    localparam abr_opcode_t ABR_UOP_COMPRESS   = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b0, aux_en: 1'b1, mode:MLKEM_COMPRESS, masking_en:1'b0, shuffling_en:1'b0};
    localparam abr_opcode_t ABR_UOP_DECOMPRESS = '{keccak_en: 1'b0, sampler_en:1'b0, ntt_en:1'b0, aux_en: 1'b1, mode:MLKEM_DECOMPRESS, masking_en:1'b0, shuffling_en:1'b0};

    //Immediate encodings
    localparam [ABR_IMM_WIDTH-1:0] MLDSA_NORMCHK_Z = 'h0000;
    localparam [ABR_IMM_WIDTH-1:0] MLDSA_NORMCHK_R0 = 'h0001;
    localparam [ABR_IMM_WIDTH-1:0] MLDSA_NORMCHK_CT0 = 'h0002;

    // MLDSA REGISTERS ID listing
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_NOP = 'd0;
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_NOP = 'd0;

    // DEST register IDs
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_DEST_K_RHO_REG_ID = 'd2;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_DEST_MU_REG_ID    = 'd3;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_DEST_RHO_P_REG_ID = 'd4;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_DEST_SIG_C_REG_ID = 'd5;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_DEST_TR_REG_ID    = 'd6;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_DEST_VERIFY_RES_REG_ID = 'd7;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_DEST_LFSR_SEED_REG_ID = 'd8;
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_DEST_RHO_SIGMA_REG_ID = 'd9;
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_DEST_TR_REG_ID    = 'd10;
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_DEST_K_R_REG_ID   = 'd11;
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_DEST_K_REG_ID   = 'd12;
    // DEST Mem overloaded into SK ram
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_DEST_DK_MEM_OFFSET = 'd0;
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_SRC_DK_MEM_OFFSET = MLKEM_DEST_DK_MEM_OFFSET/2;
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_DEST_EK_MEM_OFFSET = 'd384;
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_SRC_EK_MEM_OFFSET = MLKEM_DEST_EK_MEM_OFFSET/2;
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_DEST_C1_MEM_OFFSET = 'd768;
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_SRC_C1_MEM_OFFSET = MLKEM_DEST_C1_MEM_OFFSET/2;
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_DEST_C2_MEM_OFFSET = 'd1120;
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_SRC_C2_MEM_OFFSET = MLKEM_DEST_C2_MEM_OFFSET/2;
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_DEST_MSG_MEM_OFFSET  = 'd1160;
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_SRC_MSG_MEM_OFFSET  = MLKEM_DEST_MSG_MEM_OFFSET/2;

    //SRC register IDs
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_MSG_ID         = 'd15;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_SEED_ID        = 'd16;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_SIGN_RND_ID    = 'd17;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_K_ID           = 'd18;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_RHO_ID         = 'd19;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_RHO_P_ID       = 'd20;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_MU_ID          = 'd21;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_TR_ID          = 'd22;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_RHO_P_KAPPA_ID = 'd23;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_SIG_C_REG_ID   = 'd24;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_PK_REG_ID      = 'd25;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_ENTROPY_ID       = 'd26;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_CNT_ID           = 'd27;
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_SEED_D_ID      = 'd28;
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_RHO_ID         = 'd29;
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_SIGMA_ID       = 'd30;
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_EK_REG_ID      = 'd31;
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_TR_ID          = 'd32;
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_MSG_ID         = 'd33;
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_R_ID           = 'd34;
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_SEED_Z_ID      = 'd35;
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_CIPHERTEXT_ID  = 'd36;
    
    //SK offsets in dwords
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_SK_S1_OFFSET = 'd32;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_SK_T0_OFFSET = 'd360;

    // MLDSA MEMORY LOCATIONS
    //COEFF DEPTH is 256/4
    localparam MLDSA_COEFF_DEPTH = MLDSA_N/COEFF_PER_CLK;
    localparam MLKEM_COEFF_DEPTH = MLKEM_N/COEFF_PER_CLK;
    //MEMORY INST 0
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_INST0_BASE = 0 << (ABR_MEM_ADDR_WIDTH-3);
    //S1 / NTT(S1)
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_S1_0_BASE = ABR_INST0_BASE;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_S1_1_BASE = MLDSA_S1_0_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_S1_2_BASE = MLDSA_S1_1_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_S1_3_BASE = MLDSA_S1_2_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_S1_4_BASE = MLDSA_S1_3_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_S1_5_BASE = MLDSA_S1_4_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_S1_6_BASE = MLDSA_S1_5_BASE + MLDSA_COEFF_DEPTH;
    // z for VERIFY
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_Z_0_BASE = ABR_INST0_BASE;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_Z_1_BASE = MLDSA_Z_0_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_Z_2_BASE = MLDSA_Z_1_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_Z_3_BASE = MLDSA_Z_2_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_Z_4_BASE = MLDSA_Z_3_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_Z_5_BASE = MLDSA_Z_4_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_Z_6_BASE = MLDSA_Z_5_BASE + MLDSA_COEFF_DEPTH;
    // z NTT for VERIFY
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_Z_NTT_0_BASE = ABR_INST0_BASE;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_Z_NTT_1_BASE = MLDSA_Z_NTT_0_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_Z_NTT_2_BASE = MLDSA_Z_NTT_1_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_Z_NTT_3_BASE = MLDSA_Z_NTT_2_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_Z_NTT_4_BASE = MLDSA_Z_NTT_3_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_Z_NTT_5_BASE = MLDSA_Z_NTT_4_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_Z_NTT_6_BASE = MLDSA_Z_NTT_5_BASE + MLDSA_COEFF_DEPTH;
    //s2 / NTT(s2)
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_S2_0_BASE = MLDSA_S1_6_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_S2_1_BASE = MLDSA_S2_0_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_S2_2_BASE = MLDSA_S2_1_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_S2_3_BASE = MLDSA_S2_2_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_S2_4_BASE = MLDSA_S2_3_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_S2_5_BASE = MLDSA_S2_4_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_S2_6_BASE = MLDSA_S2_5_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_S2_7_BASE = MLDSA_S2_6_BASE + MLDSA_COEFF_DEPTH;
    //t0 / NTT(t0) t1 / NTT(t1)
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_T0_BASE = MLDSA_S2_7_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_T1_BASE = MLDSA_T0_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_T2_BASE = MLDSA_T1_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_T3_BASE = MLDSA_T2_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_T4_BASE = MLDSA_T3_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_T5_BASE = MLDSA_T4_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_T6_BASE = MLDSA_T5_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_T7_BASE = MLDSA_T6_BASE + MLDSA_COEFF_DEPTH;
    //c.s1
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_CS1_BASE = MLDSA_T7_BASE + MLDSA_COEFF_DEPTH;
    // z
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_Z_BASE = MLDSA_T7_BASE + MLDSA_COEFF_DEPTH;
    // CT for VERIFY
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_CT_BASE = MLDSA_T7_BASE + MLDSA_COEFF_DEPTH;
    //c.s2
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_CS2_BASE = MLDSA_CS1_BASE + MLDSA_COEFF_DEPTH;
    // R0
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_R0_BASE = MLDSA_CS1_BASE + MLDSA_COEFF_DEPTH;
    //TEMP storage for NTT ops
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_TEMP0_BASE = MLDSA_CS2_BASE + MLDSA_COEFF_DEPTH;
    //MLKEM KeyGen S/E/T memory locations
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_S0_BASE = ABR_INST0_BASE;
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_S1_BASE = MLKEM_S0_BASE + MLKEM_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_S2_BASE = MLKEM_S1_BASE + MLKEM_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_S3_BASE = MLKEM_S2_BASE + MLKEM_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_T0_BASE = MLKEM_S3_BASE + MLKEM_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_T1_BASE = MLKEM_T0_BASE + MLKEM_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_T2_BASE = MLKEM_T1_BASE + MLKEM_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_T3_BASE = MLKEM_T2_BASE + MLKEM_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_E0_BASE = MLKEM_T3_BASE + MLKEM_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_E1_BASE = MLKEM_E0_BASE + MLKEM_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_E2_BASE = MLKEM_E1_BASE + MLKEM_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_E3_BASE = MLKEM_E2_BASE + MLKEM_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_MU_BASE = MLKEM_E3_BASE + MLKEM_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_U0_BASE = MLKEM_MU_BASE + MLKEM_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_U1_BASE = MLKEM_U0_BASE + MLKEM_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_U2_BASE = MLKEM_U1_BASE + MLKEM_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_U3_BASE = MLKEM_U2_BASE + MLKEM_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_V_BASE = MLKEM_U3_BASE + MLKEM_COEFF_DEPTH;

    //MEMORY INST 1
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_INST1_BASE = 1 << (ABR_MEM_ADDR_WIDTH-3);
    // NTT(C)
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_C_NTT_BASE = ABR_INST1_BASE;
    // NTT(s1) for KEYGEN
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_S1_0_NTT_BASE = MLDSA_C_NTT_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_S1_1_NTT_BASE = MLDSA_S1_0_NTT_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_S1_2_NTT_BASE = MLDSA_S1_1_NTT_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_S1_3_NTT_BASE = MLDSA_S1_2_NTT_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_S1_4_NTT_BASE = MLDSA_S1_3_NTT_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_S1_5_NTT_BASE = MLDSA_S1_4_NTT_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_S1_6_NTT_BASE = MLDSA_S1_5_NTT_BASE + MLDSA_COEFF_DEPTH;
    // c.t0 for SIGNING
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_CT_0_BASE = MLDSA_C_NTT_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_CT_1_BASE = MLDSA_CT_0_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_CT_2_BASE = MLDSA_CT_1_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_CT_3_BASE = MLDSA_CT_2_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_CT_4_BASE = MLDSA_CT_3_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_CT_5_BASE = MLDSA_CT_4_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_CT_6_BASE = MLDSA_CT_5_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_CT_7_BASE = MLDSA_CT_6_BASE + MLDSA_COEFF_DEPTH;
    //hint_r
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_HINT_R_0_BASE = MLDSA_C_NTT_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_HINT_R_1_BASE = MLDSA_HINT_R_0_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_HINT_R_2_BASE = MLDSA_HINT_R_1_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_HINT_R_3_BASE = MLDSA_HINT_R_2_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_HINT_R_4_BASE = MLDSA_HINT_R_3_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_HINT_R_5_BASE = MLDSA_HINT_R_4_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_HINT_R_6_BASE = MLDSA_HINT_R_5_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_HINT_R_7_BASE = MLDSA_HINT_R_6_BASE + MLDSA_COEFF_DEPTH;
    //ML-KEM
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_Y0_BASE = ABR_INST1_BASE;
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_Y1_BASE = MLKEM_Y0_BASE + MLKEM_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_Y2_BASE = MLKEM_Y1_BASE + MLKEM_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_Y3_BASE = MLKEM_Y2_BASE + MLKEM_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_E_2_BASE = MLKEM_Y3_BASE + MLKEM_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_UP0_BASE = ABR_INST1_BASE;
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_UP1_BASE = MLKEM_UP0_BASE + MLKEM_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_UP2_BASE = MLKEM_UP1_BASE + MLKEM_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_UP3_BASE = MLKEM_UP2_BASE + MLKEM_COEFF_DEPTH;

    //MEMORY INST 2
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_INST2_BASE = 2 << (ABR_MEM_ADDR_WIDTH-3);
    //Y
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_Y_0_BASE = ABR_INST2_BASE;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_Y_1_BASE = MLDSA_Y_0_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_Y_2_BASE = MLDSA_Y_1_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_Y_3_BASE = MLDSA_Y_2_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_Y_4_BASE = MLDSA_Y_3_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_Y_5_BASE = MLDSA_Y_4_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_Y_6_BASE = MLDSA_Y_5_BASE + MLDSA_COEFF_DEPTH;
    //NTT(Y)
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_Y_0_NTT_BASE = MLDSA_Y_6_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_Y_1_NTT_BASE = MLDSA_Y_0_NTT_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_Y_2_NTT_BASE = MLDSA_Y_1_NTT_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_Y_3_NTT_BASE = MLDSA_Y_2_NTT_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_Y_4_NTT_BASE = MLDSA_Y_3_NTT_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_Y_5_NTT_BASE = MLDSA_Y_4_NTT_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_Y_6_NTT_BASE = MLDSA_Y_5_NTT_BASE + MLDSA_COEFF_DEPTH;
    //W0
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_W0_0_BASE = MLDSA_Y_6_NTT_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_W0_1_BASE = MLDSA_W0_0_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_W0_2_BASE = MLDSA_W0_1_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_W0_3_BASE = MLDSA_W0_2_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_W0_4_BASE = MLDSA_W0_3_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_W0_5_BASE = MLDSA_W0_4_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_W0_6_BASE = MLDSA_W0_5_BASE + MLDSA_COEFF_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_W0_7_BASE = MLDSA_W0_6_BASE + MLDSA_COEFF_DEPTH;
    //ML-KEM
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_TY_BASE = ABR_INST2_BASE;
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_SU_BASE = ABR_INST2_BASE;
    //TEMP for NTT
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_TEMP2_BASE = MLDSA_W0_7_BASE + MLDSA_COEFF_DEPTH;

    //MEMORY INST 3 - masked storage
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_INST3_BASE = 3 << (ABR_MEM_ADDR_WIDTH-3);

    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_AS0_BASE = ABR_INST3_BASE;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_AS0_INTT_BASE = MLDSA_AS0_BASE;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_AY0_BASE = ABR_INST3_BASE;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_AZ0_BASE = ABR_INST3_BASE;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_CS_NTT_BASE = ABR_INST3_BASE;
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_CT_NTT_BASE = ABR_INST3_BASE;
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_AS0_BASE = ABR_INST3_BASE;
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_AY0_BASE = ABR_INST3_BASE;
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_TY_MASKED_BASE = ABR_INST3_BASE;
    localparam [ABR_OPR_WIDTH-1 : 0] MLKEM_SU_MASKED_BASE = ABR_INST3_BASE;
    
    //SIB MEMORY
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_INST4_BASE = 4 << (ABR_MEM_ADDR_WIDTH-3);
    //C
    localparam [ABR_OPR_WIDTH-1 : 0] MLDSA_C_BASE = ABR_INST4_BASE;

    // MLDSA Subroutine listing
    //KG
    localparam [ABR_PROG_ADDR_W-1 : 0] ABR_RESET          = 'd0;
    localparam [ABR_PROG_ADDR_W-1 : 0] ABR_ZEROIZE        = ABR_RESET + 1;
    localparam [ABR_PROG_ADDR_W-1 : 0] MLDSA_KG_S         = ABR_ZEROIZE + 1;
    localparam [ABR_PROG_ADDR_W-1 : 0] MLDSA_KG_JUMP_SIGN = MLDSA_KG_S + 101;
    localparam [ABR_PROG_ADDR_W-1 : 0] MLDSA_KG_E         = MLDSA_KG_JUMP_SIGN + 1;
    //Signing
    localparam [ABR_PROG_ADDR_W-1 : 0] MLDSA_SIGN_S            = MLDSA_KG_E + 2;
    localparam [ABR_PROG_ADDR_W-1 : 0] MLDSA_SIGN_CHECK_MODE   = MLDSA_SIGN_S + 3;
    localparam [ABR_PROG_ADDR_W-1 : 0] MLDSA_SIGN_H_MU         = MLDSA_SIGN_CHECK_MODE + 1;
    localparam [ABR_PROG_ADDR_W-1 : 0] MLDSA_SIGN_H_RHO_P      = MLDSA_SIGN_H_MU + 2;
    localparam [ABR_PROG_ADDR_W-1 : 0] MLDSA_SIGN_INIT_S       = MLDSA_SIGN_H_RHO_P + 3;
    localparam [ABR_PROG_ADDR_W-1 : 0] MLDSA_SIGN_LFSR_S       = MLDSA_SIGN_INIT_S+24;
    localparam [ABR_PROG_ADDR_W-1 : 0] MLDSA_SIGN_MAKE_Y_S     = MLDSA_SIGN_LFSR_S + 3;
    localparam [ABR_PROG_ADDR_W-1 : 0] MLDSA_SIGN_MAKE_W_S     = MLDSA_SIGN_MAKE_Y_S+ 14;
    localparam [ABR_PROG_ADDR_W-1 : 0] MLDSA_SIGN_MAKE_W       = MLDSA_SIGN_MAKE_W_S+ 65;
    localparam [ABR_PROG_ADDR_W-1 : 0] MLDSA_SIGN_MAKE_C       = MLDSA_SIGN_MAKE_W+ 1;
    localparam [ABR_PROG_ADDR_W-1 : 0] MLDSA_SIGN_VALID_S      = MLDSA_SIGN_MAKE_C+ 2;
    localparam [ABR_PROG_ADDR_W-1 : 0] MLDSA_SIGN_CHL_E        = MLDSA_SIGN_VALID_S + 101;
    localparam [ABR_PROG_ADDR_W-1 : 0] MLDSA_SIGN_E            = MLDSA_SIGN_CHL_E + 1;
    //Verify
    localparam [ABR_PROG_ADDR_W-1 : 0] MLDSA_VERIFY_S          = MLDSA_SIGN_E + 2;
    localparam [ABR_PROG_ADDR_W-1 : 0] MLDSA_VERIFY_H_TR       = MLDSA_VERIFY_S + 9;
    localparam [ABR_PROG_ADDR_W-1 : 0] MLDSA_VERIFY_CHECK_MODE = MLDSA_VERIFY_H_TR + 1;
    localparam [ABR_PROG_ADDR_W-1 : 0] MLDSA_VERIFY_H_MU       = MLDSA_VERIFY_CHECK_MODE + 1;
    localparam [ABR_PROG_ADDR_W-1 : 0] MLDSA_VERIFY_MAKE_C     = MLDSA_VERIFY_H_MU + 2;
    localparam [ABR_PROG_ADDR_W-1 : 0] MLDSA_VERIFY_NTT_C      = MLDSA_VERIFY_MAKE_C + 1;
    localparam [ABR_PROG_ADDR_W-1 : 0] MLDSA_VERIFY_NTT_T1     = MLDSA_VERIFY_NTT_C + 1;
    localparam [ABR_PROG_ADDR_W-1 : 0] MLDSA_VERIFY_NTT_Z      = MLDSA_VERIFY_NTT_T1 + 8;
    localparam [ABR_PROG_ADDR_W-1 : 0] MLDSA_VERIFY_EXP_A      = MLDSA_VERIFY_NTT_Z + 7;
    localparam [ABR_PROG_ADDR_W-1 : 0] MLDSA_VERIFY_RES        = MLDSA_VERIFY_EXP_A + 80;
    localparam [ABR_PROG_ADDR_W-1 : 0] MLDSA_VERIFY_E          = MLDSA_VERIFY_RES + 4;

    localparam [ABR_PROG_ADDR_W-1 : 0] ABR_ERROR               = '1;

    localparam [ABR_PROG_ADDR_W-1 : 0] MLKEM_RESET = 'd0;
    localparam [ABR_PROG_ADDR_W-1 : 0] MLKEM_KG_S = MLDSA_VERIFY_E + 1;
    localparam [ABR_PROG_ADDR_W-1 : 0] MLKEM_KG_E = MLKEM_KG_S + 43;
    localparam [ABR_PROG_ADDR_W-1 : 0] MLKEM_DECAPS_S = MLKEM_KG_E + 1;
    localparam [ABR_PROG_ADDR_W-1 : 0] MLKEM_ENCAPS_S = MLKEM_DECAPS_S + 18;
    localparam [ABR_PROG_ADDR_W-1 : 0] MLKEM_ENCAPS_E = MLKEM_ENCAPS_S + 56;
    localparam [ABR_PROG_ADDR_W-1 : 0] MLKEM_DECAPS_CHK = MLKEM_ENCAPS_E + 1;
    localparam [ABR_PROG_ADDR_W-1 : 0] MLKEM_DECAPS_E = MLKEM_DECAPS_CHK + 2;



endpackage

`endif
