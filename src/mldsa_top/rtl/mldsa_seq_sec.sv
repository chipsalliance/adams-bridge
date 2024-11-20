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

//Sequencer for MLDSA
//MLDSA functions
//  Signing initial steps
//  Signing validity checks
//  Signing signature generation

`include "mldsa_config_defines.svh"

module mldsa_seq_sec
  import mldsa_ctrl_pkg::*;
  (
  input logic clk,
  input logic rst_b,
  input logic zeroize,

  input  logic en_i,
  input  logic [MLDSA_PROG_ADDR_W-1 : 0] addr_i,
  output mldsa_seq_instr_t data_o
  );


`ifdef RV_FPGA_OPTIMIZE
    (*rom_style = "block" *) mldsa_seq_instr_t data_o_rom;
`else 
    mldsa_seq_instr_t data_o_rom;
`endif
    assign data_o = data_o_rom;


  //----------------------------------------------------------------
  // ROM content
  //----------------------------------------------------------------
 
  always_ff @(posedge clk) begin
        if (en_i) begin
            unique case(addr_i)
                //RESET
                MLDSA_RESET      : data_o_rom <= '{opcode:MLDSA_UOP_NOP, imm:'h0000, length:'d00, operand1:MLDSA_NOP, operand2:MLDSA_NOP, operand3:MLDSA_NOP};

                //Signing initial steps start
                MLDSA_SIGN_INIT_S   : data_o_rom <= '{opcode:MLDSA_UOP_SKDECODE, imm:'h0000, length:'d00, operand1:MLDSA_NOP, operand2:MLDSA_NOP, operand3:MLDSA_S1_0_BASE};
                //NTT(t0)
                MLDSA_SIGN_INIT_S+1 : data_o_rom <= '{opcode:MLDSA_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_T0_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_T0_BASE};
                MLDSA_SIGN_INIT_S+2 : data_o_rom <= '{opcode:MLDSA_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_T1_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_T1_BASE};
                MLDSA_SIGN_INIT_S+3 : data_o_rom <= '{opcode:MLDSA_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_T2_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_T2_BASE};
                MLDSA_SIGN_INIT_S+4 : data_o_rom <= '{opcode:MLDSA_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_T3_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_T3_BASE};
                MLDSA_SIGN_INIT_S+5 : data_o_rom <= '{opcode:MLDSA_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_T4_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_T4_BASE};
                MLDSA_SIGN_INIT_S+6 : data_o_rom <= '{opcode:MLDSA_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_T5_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_T5_BASE};
                MLDSA_SIGN_INIT_S+7 : data_o_rom <= '{opcode:MLDSA_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_T6_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_T6_BASE};
                MLDSA_SIGN_INIT_S+8 : data_o_rom <= '{opcode:MLDSA_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_T7_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_T7_BASE};
                //NTT(s1)
                MLDSA_SIGN_INIT_S+9 : data_o_rom <= '{opcode:MLDSA_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_S1_0_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_S1_0_BASE};
                MLDSA_SIGN_INIT_S+10 : data_o_rom <= '{opcode:MLDSA_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_S1_1_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_S1_1_BASE};
                MLDSA_SIGN_INIT_S+11: data_o_rom <= '{opcode:MLDSA_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_S1_2_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_S1_2_BASE};
                MLDSA_SIGN_INIT_S+12: data_o_rom <= '{opcode:MLDSA_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_S1_3_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_S1_3_BASE};
                MLDSA_SIGN_INIT_S+13: data_o_rom <= '{opcode:MLDSA_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_S1_4_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_S1_4_BASE};
                MLDSA_SIGN_INIT_S+14: data_o_rom <= '{opcode:MLDSA_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_S1_5_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_S1_5_BASE};
                MLDSA_SIGN_INIT_S+15: data_o_rom <= '{opcode:MLDSA_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_S1_6_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_S1_6_BASE};
                //NTT(s2)
                MLDSA_SIGN_INIT_S+16: data_o_rom <= '{opcode:MLDSA_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_S2_0_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_S2_0_BASE};
                MLDSA_SIGN_INIT_S+17: data_o_rom <= '{opcode:MLDSA_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_S2_1_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_S2_1_BASE};
                MLDSA_SIGN_INIT_S+18 : data_o_rom <= '{opcode:MLDSA_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_S2_2_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_S2_2_BASE};
                MLDSA_SIGN_INIT_S+19 : data_o_rom <= '{opcode:MLDSA_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_S2_3_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_S2_3_BASE};
                MLDSA_SIGN_INIT_S+20 : data_o_rom <= '{opcode:MLDSA_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_S2_4_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_S2_4_BASE};
                MLDSA_SIGN_INIT_S+21 : data_o_rom <= '{opcode:MLDSA_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_S2_5_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_S2_5_BASE};
                MLDSA_SIGN_INIT_S+22 : data_o_rom <= '{opcode:MLDSA_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_S2_6_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_S2_6_BASE};
                MLDSA_SIGN_INIT_S+23 : data_o_rom <= '{opcode:MLDSA_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_S2_7_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_S2_7_BASE};
                //Signing validity checks
                MLDSA_SIGN_CHECK_C_VLD : data_o_rom <= '{opcode:MLDSA_UOP_NOP, imm:'h0000, length:'d00, operand1:MLDSA_NOP, operand2:MLDSA_NOP, operand3:MLDSA_NOP};
                //NTT(C)
                MLDSA_SIGN_VALID_S     : data_o_rom <= '{opcode:MLDSA_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_C_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_C_NTT_BASE};

                //Compute Z and perform norm check
                MLDSA_SIGN_CHECK_Y_VLD : data_o_rom <= '{opcode:MLDSA_UOP_NOP, imm:'h0000, length:'d00, operand1:MLDSA_NOP, operand2:MLDSA_NOP, operand3:MLDSA_NOP};
                MLDSA_SIGN_VALID_S+2   : data_o_rom <= '{opcode:MLDSA_UOP_PWM, imm:'h0000, length:'d00, operand1:MLDSA_C_NTT_BASE, operand2:MLDSA_S1_0_BASE, operand3:MLDSA_CS1_BASE};
                MLDSA_SIGN_VALID_S+3   : data_o_rom <= '{opcode:MLDSA_UOP_INTT, imm:'h0000, length:'d00, operand1:MLDSA_CS1_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_CS1_BASE};
                MLDSA_SIGN_VALID_S+4   : data_o_rom <= '{opcode:MLDSA_UOP_PWA, imm:'h0000, length:'d00, operand1:MLDSA_Y_0_BASE, operand2:MLDSA_CS1_BASE, operand3:MLDSA_Z_BASE};
                MLDSA_SIGN_VALID_S+5   : data_o_rom <= '{opcode:MLDSA_UOP_NORMCHK, imm:MLDSA_NORMCHK_Z, length:'d00, operand1:MLDSA_Z_BASE, operand2:MLDSA_NOP, operand3:MLDSA_NOP};
                MLDSA_SIGN_VALID_S+6   : data_o_rom <= '{opcode:MLDSA_UOP_SIGENCODE, imm:'h0000, length:'d00, operand1:MLDSA_Z_BASE, operand2:MLDSA_NOP, operand3:15'h000};

                MLDSA_SIGN_VALID_S+7   : data_o_rom <= '{opcode:MLDSA_UOP_PWM, imm:'h0000, length:'d00, operand1:MLDSA_C_NTT_BASE, operand2:MLDSA_S1_1_BASE, operand3:MLDSA_CS1_BASE};
                MLDSA_SIGN_VALID_S+8   : data_o_rom <= '{opcode:MLDSA_UOP_INTT, imm:'h0000, length:'d00, operand1:MLDSA_CS1_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_CS1_BASE};
                MLDSA_SIGN_VALID_S+9   : data_o_rom <= '{opcode:MLDSA_UOP_PWA, imm:'h0000, length:'d00, operand1:MLDSA_Y_1_BASE, operand2:MLDSA_CS1_BASE, operand3:MLDSA_Z_BASE};
                MLDSA_SIGN_VALID_S+10  : data_o_rom <= '{opcode:MLDSA_UOP_NORMCHK, imm:MLDSA_NORMCHK_Z, length:'d00, operand1:MLDSA_Z_BASE, operand2:MLDSA_NOP, operand3:MLDSA_NOP};
                MLDSA_SIGN_VALID_S+11  : data_o_rom <= '{opcode:MLDSA_UOP_SIGENCODE, imm:'h0000, length:'d00, operand1:MLDSA_Z_BASE, operand2:MLDSA_NOP, operand3:15'h040};

                MLDSA_SIGN_VALID_S+12  : data_o_rom <= '{opcode:MLDSA_UOP_PWM, imm:'h0000, length:'d00, operand1:MLDSA_C_NTT_BASE, operand2:MLDSA_S1_2_BASE, operand3:MLDSA_CS1_BASE};
                MLDSA_SIGN_VALID_S+13  : data_o_rom <= '{opcode:MLDSA_UOP_INTT, imm:'h0000, length:'d00, operand1:MLDSA_CS1_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_CS1_BASE};
                MLDSA_SIGN_VALID_S+14  : data_o_rom <= '{opcode:MLDSA_UOP_PWA, imm:'h0000, length:'d00, operand1:MLDSA_Y_2_BASE, operand2:MLDSA_CS1_BASE, operand3:MLDSA_Z_BASE};
                MLDSA_SIGN_VALID_S+15  : data_o_rom <= '{opcode:MLDSA_UOP_NORMCHK, imm:MLDSA_NORMCHK_Z, length:'d00, operand1:MLDSA_Z_BASE, operand2:MLDSA_NOP, operand3:MLDSA_NOP};
                MLDSA_SIGN_VALID_S+16  : data_o_rom <= '{opcode:MLDSA_UOP_SIGENCODE, imm:'h0000, length:'d00, operand1:MLDSA_Z_BASE, operand2:MLDSA_NOP, operand3:15'h080};

                MLDSA_SIGN_VALID_S+17  : data_o_rom <= '{opcode:MLDSA_UOP_PWM, imm:'h0000, length:'d00, operand1:MLDSA_C_NTT_BASE, operand2:MLDSA_S1_3_BASE, operand3:MLDSA_CS1_BASE};
                MLDSA_SIGN_VALID_S+18  : data_o_rom <= '{opcode:MLDSA_UOP_INTT, imm:'h0000, length:'d00, operand1:MLDSA_CS1_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_CS1_BASE};
                MLDSA_SIGN_VALID_S+19  : data_o_rom <= '{opcode:MLDSA_UOP_PWA, imm:'h0000, length:'d00, operand1:MLDSA_Y_3_BASE, operand2:MLDSA_CS1_BASE, operand3:MLDSA_Z_BASE};
                MLDSA_SIGN_VALID_S+20  : data_o_rom <= '{opcode:MLDSA_UOP_NORMCHK, imm:MLDSA_NORMCHK_Z, length:'d00, operand1:MLDSA_Z_BASE, operand2:MLDSA_NOP, operand3:MLDSA_NOP};
                MLDSA_SIGN_VALID_S+21  : data_o_rom <= '{opcode:MLDSA_UOP_SIGENCODE, imm:'h0000, length:'d00, operand1:MLDSA_Z_BASE, operand2:MLDSA_NOP, operand3:15'h0C0};

                MLDSA_SIGN_VALID_S+22  : data_o_rom <= '{opcode:MLDSA_UOP_PWM, imm:'h0000, length:'d00, operand1:MLDSA_C_NTT_BASE, operand2:MLDSA_S1_4_BASE, operand3:MLDSA_CS1_BASE};
                MLDSA_SIGN_VALID_S+23  : data_o_rom <= '{opcode:MLDSA_UOP_INTT, imm:'h0000, length:'d00, operand1:MLDSA_CS1_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_CS1_BASE};
                MLDSA_SIGN_VALID_S+24  : data_o_rom <= '{opcode:MLDSA_UOP_PWA, imm:'h0000, length:'d00, operand1:MLDSA_Y_4_BASE, operand2:MLDSA_CS1_BASE, operand3:MLDSA_Z_BASE};
                MLDSA_SIGN_VALID_S+25  : data_o_rom <= '{opcode:MLDSA_UOP_NORMCHK, imm:MLDSA_NORMCHK_Z, length:'d00, operand1:MLDSA_Z_BASE, operand2:MLDSA_NOP, operand3:MLDSA_NOP};
                MLDSA_SIGN_VALID_S+26  : data_o_rom <= '{opcode:MLDSA_UOP_SIGENCODE, imm:'h0000, length:'d00, operand1:MLDSA_Z_BASE, operand2:MLDSA_NOP, operand3:15'h100};

                MLDSA_SIGN_VALID_S+27  : data_o_rom <= '{opcode:MLDSA_UOP_PWM, imm:'h0000, length:'d00, operand1:MLDSA_C_NTT_BASE, operand2:MLDSA_S1_5_BASE, operand3:MLDSA_CS1_BASE};
                MLDSA_SIGN_VALID_S+28  : data_o_rom <= '{opcode:MLDSA_UOP_INTT, imm:'h0000, length:'d00, operand1:MLDSA_CS1_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_CS1_BASE};
                MLDSA_SIGN_VALID_S+29  : data_o_rom <= '{opcode:MLDSA_UOP_PWA, imm:'h0000, length:'d00, operand1:MLDSA_Y_5_BASE, operand2:MLDSA_CS1_BASE, operand3:MLDSA_Z_BASE};
                MLDSA_SIGN_VALID_S+30  : data_o_rom <= '{opcode:MLDSA_UOP_NORMCHK, imm:MLDSA_NORMCHK_Z, length:'d00, operand1:MLDSA_Z_BASE, operand2:MLDSA_NOP, operand3:MLDSA_NOP};
                MLDSA_SIGN_VALID_S+31  : data_o_rom <= '{opcode:MLDSA_UOP_SIGENCODE, imm:'h0000, length:'d00, operand1:MLDSA_Z_BASE, operand2:MLDSA_NOP, operand3:15'h140};

                MLDSA_SIGN_VALID_S+32  : data_o_rom <= '{opcode:MLDSA_UOP_PWM, imm:'h0000, length:'d00, operand1:MLDSA_C_NTT_BASE, operand2:MLDSA_S1_6_BASE, operand3:MLDSA_CS1_BASE};
                MLDSA_SIGN_VALID_S+33  : data_o_rom <= '{opcode:MLDSA_UOP_INTT, imm:'h0000, length:'d00, operand1:MLDSA_CS1_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_CS1_BASE};
                MLDSA_SIGN_VALID_S+34  : data_o_rom <= '{opcode:MLDSA_UOP_PWA, imm:'h0000, length:'d00, operand1:MLDSA_Y_6_BASE, operand2:MLDSA_CS1_BASE, operand3:MLDSA_Z_BASE};
                MLDSA_SIGN_VALID_S+35  : data_o_rom <= '{opcode:MLDSA_UOP_NORMCHK, imm:MLDSA_NORMCHK_Z, length:'d00, operand1:MLDSA_Z_BASE, operand2:MLDSA_NOP, operand3:MLDSA_NOP};
                MLDSA_SIGN_VALID_S+36  : data_o_rom <= '{opcode:MLDSA_UOP_SIGENCODE, imm:'h0000, length:'d00, operand1:MLDSA_Z_BASE, operand2:MLDSA_NOP, operand3:15'h180};
                
                MLDSA_SIGN_CLEAR_Y    : data_o_rom <= '{opcode:MLDSA_UOP_NOP, imm:'h0000, length:'d00, operand1:MLDSA_NOP, operand2:MLDSA_NOP, operand3:MLDSA_NOP};

                MLDSA_SIGN_VALID_S+38 : data_o_rom <= '{opcode:MLDSA_UOP_PWM, imm:'h0000, length:'d00, operand1:MLDSA_C_NTT_BASE, operand2:MLDSA_T0_BASE, operand3:MLDSA_CT_0_BASE};
                MLDSA_SIGN_VALID_S+39 : data_o_rom <= '{opcode:MLDSA_UOP_PWM, imm:'h0000, length:'d00, operand1:MLDSA_C_NTT_BASE, operand2:MLDSA_T1_BASE, operand3:MLDSA_CT_1_BASE};
                MLDSA_SIGN_VALID_S+40 : data_o_rom <= '{opcode:MLDSA_UOP_PWM, imm:'h0000, length:'d00, operand1:MLDSA_C_NTT_BASE, operand2:MLDSA_T2_BASE, operand3:MLDSA_CT_2_BASE};
                MLDSA_SIGN_VALID_S+41 : data_o_rom <= '{opcode:MLDSA_UOP_PWM, imm:'h0000, length:'d00, operand1:MLDSA_C_NTT_BASE, operand2:MLDSA_T3_BASE, operand3:MLDSA_CT_3_BASE};
                MLDSA_SIGN_VALID_S+42 : data_o_rom <= '{opcode:MLDSA_UOP_PWM, imm:'h0000, length:'d00, operand1:MLDSA_C_NTT_BASE, operand2:MLDSA_T4_BASE, operand3:MLDSA_CT_4_BASE};
                MLDSA_SIGN_VALID_S+43 : data_o_rom <= '{opcode:MLDSA_UOP_PWM, imm:'h0000, length:'d00, operand1:MLDSA_C_NTT_BASE, operand2:MLDSA_T5_BASE, operand3:MLDSA_CT_5_BASE};
                MLDSA_SIGN_VALID_S+44 : data_o_rom <= '{opcode:MLDSA_UOP_PWM, imm:'h0000, length:'d00, operand1:MLDSA_C_NTT_BASE, operand2:MLDSA_T6_BASE, operand3:MLDSA_CT_6_BASE};
                MLDSA_SIGN_VALID_S+45 : data_o_rom <= '{opcode:MLDSA_UOP_PWM, imm:'h0000, length:'d00, operand1:MLDSA_C_NTT_BASE, operand2:MLDSA_T7_BASE, operand3:MLDSA_CT_7_BASE};
                MLDSA_SIGN_VALID_S+46 : data_o_rom <= '{opcode:MLDSA_UOP_INTT, imm:'h0000, length:'d00, operand1:MLDSA_CT_0_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_CT_0_BASE};
                MLDSA_SIGN_VALID_S+47 : data_o_rom <= '{opcode:MLDSA_UOP_INTT, imm:'h0000, length:'d00, operand1:MLDSA_CT_1_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_CT_1_BASE};
                MLDSA_SIGN_VALID_S+48 : data_o_rom <= '{opcode:MLDSA_UOP_INTT, imm:'h0000, length:'d00, operand1:MLDSA_CT_2_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_CT_2_BASE};
                MLDSA_SIGN_VALID_S+49 : data_o_rom <= '{opcode:MLDSA_UOP_INTT, imm:'h0000, length:'d00, operand1:MLDSA_CT_3_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_CT_3_BASE};
                MLDSA_SIGN_VALID_S+50 : data_o_rom <= '{opcode:MLDSA_UOP_INTT, imm:'h0000, length:'d00, operand1:MLDSA_CT_4_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_CT_4_BASE};
                MLDSA_SIGN_VALID_S+51 : data_o_rom <= '{opcode:MLDSA_UOP_INTT, imm:'h0000, length:'d00, operand1:MLDSA_CT_5_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_CT_5_BASE};
                MLDSA_SIGN_VALID_S+52 : data_o_rom <= '{opcode:MLDSA_UOP_INTT, imm:'h0000, length:'d00, operand1:MLDSA_CT_6_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_CT_6_BASE};
                MLDSA_SIGN_VALID_S+53 : data_o_rom <= '{opcode:MLDSA_UOP_INTT, imm:'h0000, length:'d00, operand1:MLDSA_CT_7_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_CT_7_BASE};

                MLDSA_SIGN_CHECK_W0_VLD : data_o_rom <= '{opcode:MLDSA_UOP_NOP, imm:'h0000, length:'d00, operand1:MLDSA_NOP, operand2:MLDSA_NOP, operand3:MLDSA_NOP};

                //Make R0, CT0 and Hint_r
                MLDSA_SIGN_VALID_S+55 : data_o_rom <= '{opcode:MLDSA_UOP_PWM, imm:'h0000, length:'d00, operand1:MLDSA_C_NTT_BASE, operand2:MLDSA_S2_0_BASE, operand3:MLDSA_CS2_BASE};
                MLDSA_SIGN_VALID_S+56 : data_o_rom <= '{opcode:MLDSA_UOP_INTT, imm:'h0000, length:'d00, operand1:MLDSA_CS2_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_CS2_BASE};
                MLDSA_SIGN_VALID_S+57 : data_o_rom <= '{opcode:MLDSA_UOP_PWS, imm:'h0000, length:'d00, operand1:MLDSA_CS2_BASE, operand2:MLDSA_W0_0_BASE, operand3:MLDSA_R0_BASE};
                MLDSA_SIGN_VALID_S+58 : data_o_rom <= '{opcode:MLDSA_UOP_NORMCHK, imm:MLDSA_NORMCHK_R0, length:'d00, operand1:MLDSA_R0_BASE, operand2:MLDSA_NOP, operand3:MLDSA_NOP};
                MLDSA_SIGN_VALID_S+59 : data_o_rom <= '{opcode:MLDSA_UOP_NORMCHK, imm:MLDSA_NORMCHK_CT0, length:'d00, operand1:MLDSA_CT_0_BASE, operand2:MLDSA_NOP, operand3:MLDSA_NOP};
                MLDSA_SIGN_VALID_S+60 : data_o_rom <= '{opcode:MLDSA_UOP_PWA, imm:'h0000, length:'d00, operand1:MLDSA_R0_BASE, operand2:MLDSA_CT_0_BASE, operand3:MLDSA_HINT_R_0_BASE};

                MLDSA_SIGN_VALID_S+61 : data_o_rom <= '{opcode:MLDSA_UOP_PWM, imm:'h0000, length:'d00, operand1:MLDSA_C_NTT_BASE, operand2:MLDSA_S2_1_BASE, operand3:MLDSA_CS2_BASE};
                MLDSA_SIGN_VALID_S+62 : data_o_rom <= '{opcode:MLDSA_UOP_INTT, imm:'h0000, length:'d00, operand1:MLDSA_CS2_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_CS2_BASE};
                MLDSA_SIGN_VALID_S+63 : data_o_rom <= '{opcode:MLDSA_UOP_PWS, imm:'h0000, length:'d00, operand1:MLDSA_CS2_BASE, operand2:MLDSA_W0_1_BASE, operand3:MLDSA_R0_BASE};
                MLDSA_SIGN_VALID_S+64 : data_o_rom <= '{opcode:MLDSA_UOP_NORMCHK, imm:MLDSA_NORMCHK_R0, length:'d00, operand1:MLDSA_R0_BASE, operand2:MLDSA_NOP, operand3:MLDSA_NOP};
                MLDSA_SIGN_VALID_S+65 : data_o_rom <= '{opcode:MLDSA_UOP_NORMCHK, imm:MLDSA_NORMCHK_CT0, length:'d00, operand1:MLDSA_CT_1_BASE, operand2:MLDSA_NOP, operand3:MLDSA_NOP};
                MLDSA_SIGN_VALID_S+66 : data_o_rom <= '{opcode:MLDSA_UOP_PWA, imm:'h0000, length:'d00, operand1:MLDSA_R0_BASE, operand2:MLDSA_CT_1_BASE, operand3:MLDSA_HINT_R_1_BASE};

                MLDSA_SIGN_VALID_S+67 : data_o_rom <= '{opcode:MLDSA_UOP_PWM, imm:'h0000, length:'d00, operand1:MLDSA_C_NTT_BASE, operand2:MLDSA_S2_2_BASE, operand3:MLDSA_CS2_BASE};
                MLDSA_SIGN_VALID_S+68 : data_o_rom <= '{opcode:MLDSA_UOP_INTT, imm:'h0000, length:'d00, operand1:MLDSA_CS2_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_CS2_BASE};
                MLDSA_SIGN_VALID_S+69 : data_o_rom <= '{opcode:MLDSA_UOP_PWS, imm:'h0000, length:'d00, operand1:MLDSA_CS2_BASE, operand2:MLDSA_W0_2_BASE, operand3:MLDSA_R0_BASE};
                MLDSA_SIGN_VALID_S+70 : data_o_rom <= '{opcode:MLDSA_UOP_NORMCHK, imm:MLDSA_NORMCHK_R0, length:'d00, operand1:MLDSA_R0_BASE, operand2:MLDSA_NOP, operand3:MLDSA_NOP};
                MLDSA_SIGN_VALID_S+71 : data_o_rom <= '{opcode:MLDSA_UOP_NORMCHK, imm:MLDSA_NORMCHK_CT0, length:'d00, operand1:MLDSA_CT_2_BASE, operand2:MLDSA_NOP, operand3:MLDSA_NOP};
                MLDSA_SIGN_VALID_S+72 : data_o_rom <= '{opcode:MLDSA_UOP_PWA, imm:'h0000, length:'d00, operand1:MLDSA_R0_BASE, operand2:MLDSA_CT_2_BASE, operand3:MLDSA_HINT_R_2_BASE};

                MLDSA_SIGN_VALID_S+73 : data_o_rom <= '{opcode:MLDSA_UOP_PWM, imm:'h0000, length:'d00, operand1:MLDSA_C_NTT_BASE, operand2:MLDSA_S2_3_BASE, operand3:MLDSA_CS2_BASE};
                MLDSA_SIGN_VALID_S+74 : data_o_rom <= '{opcode:MLDSA_UOP_INTT, imm:'h0000, length:'d00, operand1:MLDSA_CS2_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_CS2_BASE};
                MLDSA_SIGN_VALID_S+75 : data_o_rom <= '{opcode:MLDSA_UOP_PWS, imm:'h0000, length:'d00, operand1:MLDSA_CS2_BASE, operand2:MLDSA_W0_3_BASE, operand3:MLDSA_R0_BASE};
                MLDSA_SIGN_VALID_S+76 : data_o_rom <= '{opcode:MLDSA_UOP_NORMCHK, imm:MLDSA_NORMCHK_R0, length:'d00, operand1:MLDSA_R0_BASE, operand2:MLDSA_NOP, operand3:MLDSA_NOP};
                MLDSA_SIGN_VALID_S+77 : data_o_rom <= '{opcode:MLDSA_UOP_NORMCHK, imm:MLDSA_NORMCHK_CT0, length:'d00, operand1:MLDSA_CT_3_BASE, operand2:MLDSA_NOP, operand3:MLDSA_NOP};
                MLDSA_SIGN_VALID_S+78 : data_o_rom <= '{opcode:MLDSA_UOP_PWA, imm:'h0000, length:'d00, operand1:MLDSA_R0_BASE, operand2:MLDSA_CT_3_BASE, operand3:MLDSA_HINT_R_3_BASE};

                MLDSA_SIGN_VALID_S+79 : data_o_rom <= '{opcode:MLDSA_UOP_PWM, imm:'h0000, length:'d00, operand1:MLDSA_C_NTT_BASE, operand2:MLDSA_S2_4_BASE, operand3:MLDSA_CS2_BASE};
                MLDSA_SIGN_VALID_S+80 : data_o_rom <= '{opcode:MLDSA_UOP_INTT, imm:'h0000, length:'d00, operand1:MLDSA_CS2_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_CS2_BASE};
                MLDSA_SIGN_VALID_S+81 : data_o_rom <= '{opcode:MLDSA_UOP_PWS, imm:'h0000, length:'d00, operand1:MLDSA_CS2_BASE, operand2:MLDSA_W0_4_BASE, operand3:MLDSA_R0_BASE};
                MLDSA_SIGN_VALID_S+82 : data_o_rom <= '{opcode:MLDSA_UOP_NORMCHK, imm:MLDSA_NORMCHK_R0, length:'d00, operand1:MLDSA_R0_BASE, operand2:MLDSA_NOP, operand3:MLDSA_NOP};
                MLDSA_SIGN_VALID_S+83 : data_o_rom <= '{opcode:MLDSA_UOP_NORMCHK, imm:MLDSA_NORMCHK_CT0, length:'d00, operand1:MLDSA_CT_4_BASE, operand2:MLDSA_NOP, operand3:MLDSA_NOP};
                MLDSA_SIGN_VALID_S+84 : data_o_rom <= '{opcode:MLDSA_UOP_PWA, imm:'h0000, length:'d00, operand1:MLDSA_R0_BASE, operand2:MLDSA_CT_4_BASE, operand3:MLDSA_HINT_R_4_BASE};

                MLDSA_SIGN_VALID_S+85 : data_o_rom <= '{opcode:MLDSA_UOP_PWM, imm:'h0000, length:'d00, operand1:MLDSA_C_NTT_BASE, operand2:MLDSA_S2_5_BASE, operand3:MLDSA_CS2_BASE};
                MLDSA_SIGN_VALID_S+86 : data_o_rom <= '{opcode:MLDSA_UOP_INTT, imm:'h0000, length:'d00, operand1:MLDSA_CS2_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_CS2_BASE};
                MLDSA_SIGN_VALID_S+87 : data_o_rom <= '{opcode:MLDSA_UOP_PWS, imm:'h0000, length:'d00, operand1:MLDSA_CS2_BASE, operand2:MLDSA_W0_5_BASE, operand3:MLDSA_R0_BASE};
                MLDSA_SIGN_VALID_S+88 : data_o_rom <= '{opcode:MLDSA_UOP_NORMCHK, imm:MLDSA_NORMCHK_R0, length:'d00, operand1:MLDSA_R0_BASE, operand2:MLDSA_NOP, operand3:MLDSA_NOP};
                MLDSA_SIGN_VALID_S+89 : data_o_rom <= '{opcode:MLDSA_UOP_NORMCHK, imm:MLDSA_NORMCHK_CT0, length:'d00, operand1:MLDSA_CT_5_BASE, operand2:MLDSA_NOP, operand3:MLDSA_NOP};
                MLDSA_SIGN_VALID_S+90 : data_o_rom <= '{opcode:MLDSA_UOP_PWA, imm:'h0000, length:'d00, operand1:MLDSA_R0_BASE, operand2:MLDSA_CT_5_BASE, operand3:MLDSA_HINT_R_5_BASE};

                MLDSA_SIGN_VALID_S+91 : data_o_rom <= '{opcode:MLDSA_UOP_PWM, imm:'h0000, length:'d00, operand1:MLDSA_C_NTT_BASE, operand2:MLDSA_S2_6_BASE, operand3:MLDSA_CS2_BASE};
                MLDSA_SIGN_VALID_S+92 : data_o_rom <= '{opcode:MLDSA_UOP_INTT, imm:'h0000, length:'d00, operand1:MLDSA_CS2_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_CS2_BASE};
                MLDSA_SIGN_VALID_S+93 : data_o_rom <= '{opcode:MLDSA_UOP_PWS, imm:'h0000, length:'d00, operand1:MLDSA_CS2_BASE, operand2:MLDSA_W0_6_BASE, operand3:MLDSA_R0_BASE};
                MLDSA_SIGN_VALID_S+94 : data_o_rom <= '{opcode:MLDSA_UOP_NORMCHK, imm:MLDSA_NORMCHK_R0, length:'d00, operand1:MLDSA_R0_BASE, operand2:MLDSA_NOP, operand3:MLDSA_NOP};
                MLDSA_SIGN_VALID_S+95 : data_o_rom <= '{opcode:MLDSA_UOP_NORMCHK, imm:MLDSA_NORMCHK_CT0, length:'d00, operand1:MLDSA_CT_6_BASE, operand2:MLDSA_NOP, operand3:MLDSA_NOP};
                MLDSA_SIGN_VALID_S+96 : data_o_rom <= '{opcode:MLDSA_UOP_PWA, imm:'h0000, length:'d00, operand1:MLDSA_R0_BASE, operand2:MLDSA_CT_6_BASE, operand3:MLDSA_HINT_R_6_BASE};

                MLDSA_SIGN_VALID_S+97 : data_o_rom <= '{opcode:MLDSA_UOP_PWM, imm:'h0000, length:'d00, operand1:MLDSA_C_NTT_BASE, operand2:MLDSA_S2_7_BASE, operand3:MLDSA_CS2_BASE};
                MLDSA_SIGN_VALID_S+98 : data_o_rom <= '{opcode:MLDSA_UOP_INTT, imm:'h0000, length:'d00, operand1:MLDSA_CS2_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_CS2_BASE};
                MLDSA_SIGN_VALID_S+99 : data_o_rom <= '{opcode:MLDSA_UOP_PWS, imm:'h0000, length:'d00, operand1:MLDSA_CS2_BASE, operand2:MLDSA_W0_7_BASE, operand3:MLDSA_R0_BASE};
                MLDSA_SIGN_VALID_S+100 : data_o_rom <= '{opcode:MLDSA_UOP_NORMCHK, imm:MLDSA_NORMCHK_R0, length:'d00, operand1:MLDSA_R0_BASE, operand2:MLDSA_NOP, operand3:MLDSA_NOP};
                MLDSA_SIGN_VALID_S+101 : data_o_rom <= '{opcode:MLDSA_UOP_NORMCHK, imm:MLDSA_NORMCHK_CT0, length:'d00, operand1:MLDSA_CT_7_BASE, operand2:MLDSA_NOP, operand3:MLDSA_NOP};
                MLDSA_SIGN_VALID_S+102 : data_o_rom <= '{opcode:MLDSA_UOP_PWA, imm:'h0000, length:'d00, operand1:MLDSA_R0_BASE, operand2:MLDSA_CT_7_BASE, operand3:MLDSA_HINT_R_7_BASE};
            
                MLDSA_SIGN_CLEAR_W0   : data_o_rom <= '{opcode:MLDSA_UOP_NOP, imm:'h0000, length:'d00, operand1:MLDSA_NOP, operand2:MLDSA_NOP, operand3:MLDSA_NOP};

                MLDSA_SIGN_VALID_S+104 : data_o_rom <= '{opcode:MLDSA_UOP_MAKEHINT, imm:'h0000, length:'d00, operand1:MLDSA_HINT_R_0_BASE, operand2:MLDSA_NOP, operand3:MLDSA_NOP};

                MLDSA_SIGN_GEN_S   : data_o_rom <= '{opcode:MLDSA_UOP_NOP, imm:'h0000, length:'d00, operand1:MLDSA_NOP, operand2:MLDSA_NOP, operand3:MLDSA_NOP};
                MLDSA_SIGN_CLEAR_C : data_o_rom <= '{opcode:MLDSA_UOP_NOP, imm:'h0000, length:'d00, operand1:MLDSA_NOP, operand2:MLDSA_NOP, operand3:MLDSA_NOP};
                MLDSA_SIGN_GEN_E   : data_o_rom <= '{opcode: MLDSA_UOP_NOP, imm:'h0000, length:'d00, operand1:MLDSA_NOP, operand2:MLDSA_NOP, operand3:MLDSA_NOP};
                default :            data_o_rom <= '{opcode: MLDSA_UOP_NOP, imm:'h0000, length:'d00, operand1:MLDSA_NOP, operand2:MLDSA_NOP, operand3:MLDSA_NOP};
            endcase 
    end
    else begin
        data_o_rom <= '{opcode: MLDSA_UOP_NOP, imm:'h0000, length:'d00, operand1:MLDSA_NOP, operand2:MLDSA_NOP, operand3:MLDSA_NOP};
    end
end

endmodule