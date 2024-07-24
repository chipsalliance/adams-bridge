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

`ifndef ABR_SEQ_PKG
`define ABR_SEQ_PKG

package abr_seq_pkg;
    import abr_params_pkg::*;
    import sampler_pkg::*;

    localparam integer ABR_OPR_WIDTH       = 15;
    localparam ABR_PROG_ADDR_W             = 9;

    localparam SEED_NUM_DWORDS = 8;

    //FSM Controller for driving sampler 
    typedef enum logic [2:0] {
        ABR_CTRL_IDLE          = 3'b000,
        ABR_CTRL_SHA3_START    = 3'b001,
        ABR_CTRL_MSG_START     = 3'b010,
        ABR_CTRL_MSG_LOAD      = 3'b011,
        ABR_CTRL_SAMPLER_START = 3'b100,
        ABR_CTRL_NTT_START     = 3'b101,
        ABR_CTRL_DONE          = 3'b111
      } abr_ctrl_fsm_state_e;

    typedef enum logic[2:0] {
        ABR_NTT_NONE  = 3'b000,
        ABR_NTT       = 3'b001,
        ABR_INTT      = 3'b010,
        ABR_PWM       = 3'b100,
        ABR_PWM_ACCUM = 3'b101,
        ABR_PWA       = 3'b110
    } abr_ntt_mode_e;

    typedef struct packed {
        logic sampler_en;
        logic ntt_en;
        abr_sampler_mode_e sampler_mode;
        abr_ntt_mode_e     ntt_mode;
        logic sca_en;
    } abr_opcode_t;

    typedef struct packed {
        abr_opcode_t                   opcode;
        logic [15:0]                   iter;
        logic [ABR_OPR_WIDTH-1 : 0]    length;
        logic [ABR_OPR_WIDTH-1 : 0]    operand1;
        logic [ABR_OPR_WIDTH-1 : 0]    operand2;
        logic [ABR_OPR_WIDTH-1 : 0]    operand3;
    } abr_seq_instr_t;

    // DILITHIUM ISA
    localparam abr_opcode_t ABR_UOP_NOP       = '{sampler_en:1'b0, ntt_en:1'b0, sampler_mode:ABR_SAMPLER_NONE,   ntt_mode:ABR_NTT_NONE,  sca_en:1'b0};
    localparam abr_opcode_t ABR_UOP_SHAKE256  = '{sampler_en:1'b1, ntt_en:1'b0, sampler_mode:ABR_SHAKE256,       ntt_mode:ABR_NTT_NONE,  sca_en:1'b0};
    localparam abr_opcode_t ABR_UOP_SHAKE128  = '{sampler_en:1'b1, ntt_en:1'b0, sampler_mode:ABR_SHAKE128,       ntt_mode:ABR_NTT_NONE,  sca_en:1'b0};
    localparam abr_opcode_t ABR_UOP_REJB      = '{sampler_en:1'b1, ntt_en:1'b0, sampler_mode:ABR_REJ_BOUNDED,    ntt_mode:ABR_NTT_NONE,  sca_en:1'b0};
    localparam abr_opcode_t ABR_UOP_REJS_PWM  = '{sampler_en:1'b1, ntt_en:1'b1, sampler_mode:ABR_REJ_SAMPLER,    ntt_mode:ABR_PWM,       sca_en:1'b0};
    localparam abr_opcode_t ABR_UOP_REJS_PWMA = '{sampler_en:1'b1, ntt_en:1'b1, sampler_mode:ABR_REJ_SAMPLER,    ntt_mode:ABR_PWM_ACCUM, sca_en:1'b0};
    localparam abr_opcode_t ABR_UOP_SIB       = '{sampler_en:1'b1, ntt_en:1'b0, sampler_mode:ABR_SAMPLE_IN_BALL, ntt_mode:ABR_NTT_NONE,  sca_en:1'b0};
    localparam abr_opcode_t ABR_UOP_EXP_MASK  = '{sampler_en:1'b1, ntt_en:1'b0, sampler_mode:ABR_EXP_MASK,       ntt_mode:ABR_NTT_NONE,  sca_en:1'b0};
    localparam abr_opcode_t ABR_UOP_NTT       = '{sampler_en:1'b0, ntt_en:1'b1, sampler_mode:ABR_SAMPLER_NONE,   ntt_mode:ABR_NTT,       sca_en:1'b0};
    localparam abr_opcode_t ABR_UOP_INTT      = '{sampler_en:1'b0, ntt_en:1'b1, sampler_mode:ABR_SAMPLER_NONE,   ntt_mode:ABR_INTT,      sca_en:1'b0};
    localparam abr_opcode_t ABR_UOP_PWA       = '{sampler_en:1'b0, ntt_en:1'b1, sampler_mode:ABR_SAMPLER_NONE,   ntt_mode:ABR_PWA,       sca_en:1'b0};

    // DILITHIUM REGISTERS ID listing
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_NOP           = 'd0;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_CONST_ZERO_ID = 'd0;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_CONST_ONE_ID  = 'd1;

    localparam [ABR_OPR_WIDTH-1 : 0] ABR_DEST_K_ROH_REG_ID = 'd2;

    localparam [ABR_OPR_WIDTH-1 : 0] ABR_SEED_ID       = 'd16;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_K_ID          = 'd17;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_ROH_ID        = 'd18;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_ROH_P_ID      = 'd19;

    // DILITHIUM MEMORY LOCATIONS
    localparam ABR_S_DEPTH = DILITHIUM_N/COEFF_PER_CLK;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_S1_0_BASE     = 'd0;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_S1_1_BASE     = ABR_S1_0_BASE + ABR_S_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_S1_2_BASE     = ABR_S1_1_BASE + ABR_S_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_S1_3_BASE     = ABR_S1_2_BASE + ABR_S_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_S1_4_BASE     = ABR_S1_3_BASE + ABR_S_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_S1_5_BASE     = ABR_S1_4_BASE + ABR_S_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_S1_6_BASE     = ABR_S1_5_BASE + ABR_S_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_S2_0_BASE     = ABR_S1_6_BASE + ABR_S_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_S2_1_BASE     = ABR_S2_0_BASE + ABR_S_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_S2_2_BASE     = ABR_S2_1_BASE + ABR_S_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_S2_3_BASE     = ABR_S2_2_BASE + ABR_S_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_S2_4_BASE     = ABR_S2_3_BASE + ABR_S_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_S2_5_BASE     = ABR_S2_4_BASE + ABR_S_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_S2_6_BASE     = ABR_S2_5_BASE + ABR_S_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_S2_7_BASE     = ABR_S2_6_BASE + ABR_S_DEPTH;

    localparam [ABR_OPR_WIDTH-1 : 0] ABR_S1_0_NTT_BASE = ABR_S2_7_BASE + ABR_S_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_S1_1_NTT_BASE = ABR_S1_0_NTT_BASE + ABR_S_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_S1_2_NTT_BASE = ABR_S1_1_NTT_BASE + ABR_S_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_S1_3_NTT_BASE = ABR_S1_2_NTT_BASE + ABR_S_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_S1_4_NTT_BASE = ABR_S1_3_NTT_BASE + ABR_S_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_S1_5_NTT_BASE = ABR_S1_4_NTT_BASE + ABR_S_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_S1_6_NTT_BASE = ABR_S1_5_NTT_BASE + ABR_S_DEPTH;

    localparam [ABR_OPR_WIDTH-1 : 0] ABR_TEMP_BASE     = ABR_S1_6_NTT_BASE + ABR_S_DEPTH;

    localparam [ABR_OPR_WIDTH-1 : 0] ABR_AS0_BASE = 1 << (ABR_MEM_ADDR_WIDTH-1);
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_AS1_BASE = ABR_AS0_BASE + ABR_S_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_AS2_BASE = ABR_AS1_BASE + ABR_S_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_AS3_BASE = ABR_AS2_BASE + ABR_S_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_AS4_BASE = ABR_AS3_BASE + ABR_S_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_AS5_BASE = ABR_AS4_BASE + ABR_S_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_AS6_BASE = ABR_AS5_BASE + ABR_S_DEPTH;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_AS7_BASE = ABR_AS6_BASE + ABR_S_DEPTH;

    localparam [ABR_OPR_WIDTH-1 : 0] ABR_AS0_INTT_BASE = ABR_AS0_BASE;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_AS1_INTT_BASE = ABR_AS1_BASE;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_AS2_INTT_BASE = ABR_AS2_BASE;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_AS3_INTT_BASE = ABR_AS3_BASE;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_AS4_INTT_BASE = ABR_AS4_BASE;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_AS5_INTT_BASE = ABR_AS5_BASE;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_AS6_INTT_BASE = ABR_AS6_BASE;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_AS7_INTT_BASE = ABR_AS7_BASE;

    localparam [ABR_OPR_WIDTH-1 : 0] ABR_T0_BASE = ABR_AS0_BASE;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_T1_BASE = ABR_AS1_BASE;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_T2_BASE = ABR_AS2_BASE;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_T3_BASE = ABR_AS3_BASE;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_T4_BASE = ABR_AS4_BASE;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_T5_BASE = ABR_AS5_BASE;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_T6_BASE = ABR_AS6_BASE;
    localparam [ABR_OPR_WIDTH-1 : 0] ABR_T7_BASE = ABR_AS7_BASE;

    // DILITHIUM Subroutine listing
    localparam [ABR_PROG_ADDR_W-1 : 0] DILITHIUM_RESET   = 'd0;
    localparam [ABR_PROG_ADDR_W-1 : 0] DILITHIUM_KG_S    = DILITHIUM_RESET + 2; 
    localparam [ABR_PROG_ADDR_W-1 : 0] DILITHIUM_KG_E    = DILITHIUM_KG_S + 95;
    localparam [ABR_PROG_ADDR_W-1 : 0] DILITHIUM_ERROR   = '1;

endpackage

`endif
