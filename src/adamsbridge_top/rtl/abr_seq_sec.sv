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

//Sequencer for Adams Bridge
//Adams Bridge functions
//  Signing initial steps
//  Signing validity checks
//  Signing signature generation

`include "config_defines.svh"

module abr_seq_sec
  import abr_ctrl_pkg::*;
  (
  input logic clk,
  input logic rst_b,
  input logic zeroize,

  input  logic en_i,
  input  logic [ABR_PROG_ADDR_W-1 : 0] addr_i,
  output abr_seq_instr_t data_o
  );


  //----------------------------------------------------------------
  // ROM content
  //----------------------------------------------------------------
 
  always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b) begin
        data_o <= '0;
    end 
    else if (zeroize) begin
        data_o <= '0;
    end 
    else begin
        if (en_i) begin
            unique case(addr_i)
                //RESET
                DILITHIUM_RESET      : data_o <= '{opcode:ABR_UOP_NOP, iter:'h0000, length:'d00, operand1:ABR_NOP, operand2:ABR_NOP, operand3:ABR_NOP};

                //Signing initial steps start
                DILITHIUM_SIGN_INIT_S   : data_o <= '{opcode:ABR_UOP_SKDECODE, iter:'h0000, length:'d00, operand1:ABR_NOP, operand2:ABR_NOP, operand3:ABR_S1_0_BASE};
                //NTT(s1)
                DILITHIUM_SIGN_INIT_S+1 : data_o <= '{opcode:ABR_UOP_NTT, iter:'h0000, length:'d00, operand1:ABR_S1_0_BASE, operand2:ABR_TEMP0_BASE, operand3:ABR_S1_0_BASE};
                DILITHIUM_SIGN_INIT_S+2 : data_o <= '{opcode:ABR_UOP_NTT, iter:'h0000, length:'d00, operand1:ABR_S1_1_BASE, operand2:ABR_TEMP0_BASE, operand3:ABR_S1_1_BASE};
                DILITHIUM_SIGN_INIT_S+3 : data_o <= '{opcode:ABR_UOP_NTT, iter:'h0000, length:'d00, operand1:ABR_S1_2_BASE, operand2:ABR_TEMP0_BASE, operand3:ABR_S1_2_BASE};
                DILITHIUM_SIGN_INIT_S+4 : data_o <= '{opcode:ABR_UOP_NTT, iter:'h0000, length:'d00, operand1:ABR_S1_3_BASE, operand2:ABR_TEMP0_BASE, operand3:ABR_S1_3_BASE};
                DILITHIUM_SIGN_INIT_S+5 : data_o <= '{opcode:ABR_UOP_NTT, iter:'h0000, length:'d00, operand1:ABR_S1_4_BASE, operand2:ABR_TEMP0_BASE, operand3:ABR_S1_4_BASE};
                DILITHIUM_SIGN_INIT_S+6 : data_o <= '{opcode:ABR_UOP_NTT, iter:'h0000, length:'d00, operand1:ABR_S1_5_BASE, operand2:ABR_TEMP0_BASE, operand3:ABR_S1_5_BASE};
                DILITHIUM_SIGN_INIT_S+7 : data_o <= '{opcode:ABR_UOP_NTT, iter:'h0000, length:'d00, operand1:ABR_S1_6_BASE, operand2:ABR_TEMP0_BASE, operand3:ABR_S1_6_BASE};
                //NTT(s2)
                DILITHIUM_SIGN_INIT_S+8 : data_o <= '{opcode:ABR_UOP_NTT, iter:'h0000, length:'d00, operand1:ABR_S2_0_BASE, operand2:ABR_TEMP0_BASE, operand3:ABR_S2_0_BASE};
                DILITHIUM_SIGN_INIT_S+9 : data_o <= '{opcode:ABR_UOP_NTT, iter:'h0000, length:'d00, operand1:ABR_S2_1_BASE, operand2:ABR_TEMP0_BASE, operand3:ABR_S2_1_BASE};
                DILITHIUM_SIGN_INIT_S+10 : data_o <= '{opcode:ABR_UOP_NTT, iter:'h0000, length:'d00, operand1:ABR_S2_2_BASE, operand2:ABR_TEMP0_BASE, operand3:ABR_S2_2_BASE};
                DILITHIUM_SIGN_INIT_S+11 : data_o <= '{opcode:ABR_UOP_NTT, iter:'h0000, length:'d00, operand1:ABR_S2_3_BASE, operand2:ABR_TEMP0_BASE, operand3:ABR_S2_3_BASE};
                DILITHIUM_SIGN_INIT_S+12 : data_o <= '{opcode:ABR_UOP_NTT, iter:'h0000, length:'d00, operand1:ABR_S2_4_BASE, operand2:ABR_TEMP0_BASE, operand3:ABR_S2_4_BASE};
                DILITHIUM_SIGN_INIT_S+13 : data_o <= '{opcode:ABR_UOP_NTT, iter:'h0000, length:'d00, operand1:ABR_S2_5_BASE, operand2:ABR_TEMP0_BASE, operand3:ABR_S2_5_BASE};
                DILITHIUM_SIGN_INIT_S+14 : data_o <= '{opcode:ABR_UOP_NTT, iter:'h0000, length:'d00, operand1:ABR_S2_6_BASE, operand2:ABR_TEMP0_BASE, operand3:ABR_S2_6_BASE};
                DILITHIUM_SIGN_INIT_S+15 : data_o <= '{opcode:ABR_UOP_NTT, iter:'h0000, length:'d00, operand1:ABR_S2_7_BASE, operand2:ABR_TEMP0_BASE, operand3:ABR_S2_7_BASE};
                //NTT(t0)
                DILITHIUM_SIGN_INIT_S+16 : data_o <= '{opcode:ABR_UOP_NTT, iter:'h0000, length:'d00, operand1:ABR_T0_BASE, operand2:ABR_TEMP0_BASE, operand3:ABR_T0_BASE};
                DILITHIUM_SIGN_INIT_S+17 : data_o <= '{opcode:ABR_UOP_NTT, iter:'h0000, length:'d00, operand1:ABR_T1_BASE, operand2:ABR_TEMP0_BASE, operand3:ABR_T1_BASE};
                DILITHIUM_SIGN_INIT_S+18 : data_o <= '{opcode:ABR_UOP_NTT, iter:'h0000, length:'d00, operand1:ABR_T2_BASE, operand2:ABR_TEMP0_BASE, operand3:ABR_T2_BASE};
                DILITHIUM_SIGN_INIT_S+19 : data_o <= '{opcode:ABR_UOP_NTT, iter:'h0000, length:'d00, operand1:ABR_T3_BASE, operand2:ABR_TEMP0_BASE, operand3:ABR_T3_BASE};
                DILITHIUM_SIGN_INIT_S+20 : data_o <= '{opcode:ABR_UOP_NTT, iter:'h0000, length:'d00, operand1:ABR_T4_BASE, operand2:ABR_TEMP0_BASE, operand3:ABR_T4_BASE};
                DILITHIUM_SIGN_INIT_S+21 : data_o <= '{opcode:ABR_UOP_NTT, iter:'h0000, length:'d00, operand1:ABR_T5_BASE, operand2:ABR_TEMP0_BASE, operand3:ABR_T5_BASE};
                DILITHIUM_SIGN_INIT_S+22 : data_o <= '{opcode:ABR_UOP_NTT, iter:'h0000, length:'d00, operand1:ABR_T6_BASE, operand2:ABR_TEMP0_BASE, operand3:ABR_T6_BASE};
                DILITHIUM_SIGN_INIT_S+23 : data_o <= '{opcode:ABR_UOP_NTT, iter:'h0000, length:'d00, operand1:ABR_T7_BASE, operand2:ABR_TEMP0_BASE, operand3:ABR_T7_BASE};
                //Signing validity checks
                DILITHIUM_SIGN_CHECK_C_VLD : data_o <= '{opcode:ABR_UOP_NOP, iter:'h0000, length:'d00, operand1:ABR_NOP, operand2:ABR_NOP, operand3:ABR_NOP};
                //NTT(C)
                DILITHIUM_SIGN_VALID_S    : data_o <= '{opcode:ABR_UOP_NTT, iter:'h0000, length:'d00, operand1:ABR_C_BASE, operand2:ABR_TEMP0_BASE, operand3:ABR_C_NTT_BASE};
                DILITHIUM_SIGN_VALID_S+1  : data_o <= '{opcode:ABR_UOP_NOP, iter:'h0000, length:'d00, operand1:ABR_NOP, operand2:ABR_NOP, operand3:ABR_NOP};
                //⟨⟨cs1⟩⟩←NTT−1(cˆ◦ sˆ1)
                DILITHIUM_SIGN_VALID_S+2  : data_o <= '{opcode:ABR_UOP_PWM, iter:'h0000, length:'d00, operand1:ABR_C_NTT_BASE, operand2:ABR_S1_0_BASE, operand3:ABR_CS1_0_BASE};
                DILITHIUM_SIGN_VALID_S+3  : data_o <= '{opcode:ABR_UOP_PWM, iter:'h0000, length:'d00, operand1:ABR_C_NTT_BASE, operand2:ABR_S1_1_BASE, operand3:ABR_CS1_1_BASE};
                DILITHIUM_SIGN_VALID_S+4  : data_o <= '{opcode:ABR_UOP_PWM, iter:'h0000, length:'d00, operand1:ABR_C_NTT_BASE, operand2:ABR_S1_2_BASE, operand3:ABR_CS1_2_BASE};
                DILITHIUM_SIGN_VALID_S+5  : data_o <= '{opcode:ABR_UOP_PWM, iter:'h0000, length:'d00, operand1:ABR_C_NTT_BASE, operand2:ABR_S1_3_BASE, operand3:ABR_CS1_3_BASE};
                DILITHIUM_SIGN_VALID_S+6  : data_o <= '{opcode:ABR_UOP_PWM, iter:'h0000, length:'d00, operand1:ABR_C_NTT_BASE, operand2:ABR_S1_4_BASE, operand3:ABR_CS1_4_BASE};
                DILITHIUM_SIGN_VALID_S+7  : data_o <= '{opcode:ABR_UOP_PWM, iter:'h0000, length:'d00, operand1:ABR_C_NTT_BASE, operand2:ABR_S1_5_BASE, operand3:ABR_CS1_5_BASE};
                DILITHIUM_SIGN_VALID_S+8  : data_o <= '{opcode:ABR_UOP_PWM, iter:'h0000, length:'d00, operand1:ABR_C_NTT_BASE, operand2:ABR_S1_6_BASE, operand3:ABR_CS1_6_BASE};
                DILITHIUM_SIGN_VALID_S+9  : data_o <= '{opcode:ABR_UOP_INTT, iter:'h0000, length:'d00, operand1:ABR_CS1_0_BASE, operand2:ABR_TEMP0_BASE, operand3:ABR_CS1_0_BASE};
                DILITHIUM_SIGN_VALID_S+10 : data_o <= '{opcode:ABR_UOP_INTT, iter:'h0000, length:'d00, operand1:ABR_CS1_1_BASE, operand2:ABR_TEMP0_BASE, operand3:ABR_CS1_1_BASE};
                DILITHIUM_SIGN_VALID_S+11 : data_o <= '{opcode:ABR_UOP_INTT, iter:'h0000, length:'d00, operand1:ABR_CS1_2_BASE, operand2:ABR_TEMP0_BASE, operand3:ABR_CS1_2_BASE};
                DILITHIUM_SIGN_VALID_S+12 : data_o <= '{opcode:ABR_UOP_INTT, iter:'h0000, length:'d00, operand1:ABR_CS1_3_BASE, operand2:ABR_TEMP0_BASE, operand3:ABR_CS1_3_BASE};
                DILITHIUM_SIGN_VALID_S+13 : data_o <= '{opcode:ABR_UOP_INTT, iter:'h0000, length:'d00, operand1:ABR_CS1_4_BASE, operand2:ABR_TEMP0_BASE, operand3:ABR_CS1_4_BASE};
                DILITHIUM_SIGN_VALID_S+14 : data_o <= '{opcode:ABR_UOP_INTT, iter:'h0000, length:'d00, operand1:ABR_CS1_5_BASE, operand2:ABR_TEMP0_BASE, operand3:ABR_CS1_5_BASE};
                DILITHIUM_SIGN_VALID_S+15 : data_o <= '{opcode:ABR_UOP_INTT, iter:'h0000, length:'d00, operand1:ABR_CS1_6_BASE, operand2:ABR_TEMP0_BASE, operand3:ABR_CS1_6_BASE};
                //z ←y +⟨⟨cs1⟩⟩ - Z overwrites CS1
                DILITHIUM_SIGN_CHECK_Y_VLD : data_o <= '{opcode:ABR_UOP_NOP, iter:'h0000, length:'d00, operand1:ABR_NOP, operand2:ABR_NOP, operand3:ABR_NOP};
                DILITHIUM_SIGN_VALID_S+17 : data_o <= '{opcode:ABR_UOP_PWA, iter:'h0000, length:'d00, operand1:ABR_Y_0_BASE, operand2:ABR_CS1_0_BASE, operand3:ABR_Z_0_BASE};
                DILITHIUM_SIGN_VALID_S+18 : data_o <= '{opcode:ABR_UOP_PWA, iter:'h0000, length:'d00, operand1:ABR_Y_1_BASE, operand2:ABR_CS1_1_BASE, operand3:ABR_Z_1_BASE};
                DILITHIUM_SIGN_VALID_S+19 : data_o <= '{opcode:ABR_UOP_PWA, iter:'h0000, length:'d00, operand1:ABR_Y_2_BASE, operand2:ABR_CS1_2_BASE, operand3:ABR_Z_2_BASE};
                DILITHIUM_SIGN_VALID_S+20 : data_o <= '{opcode:ABR_UOP_PWA, iter:'h0000, length:'d00, operand1:ABR_Y_3_BASE, operand2:ABR_CS1_3_BASE, operand3:ABR_Z_3_BASE};
                DILITHIUM_SIGN_VALID_S+21 : data_o <= '{opcode:ABR_UOP_PWA, iter:'h0000, length:'d00, operand1:ABR_Y_4_BASE, operand2:ABR_CS1_4_BASE, operand3:ABR_Z_4_BASE};
                DILITHIUM_SIGN_VALID_S+22 : data_o <= '{opcode:ABR_UOP_PWA, iter:'h0000, length:'d00, operand1:ABR_Y_5_BASE, operand2:ABR_CS1_5_BASE, operand3:ABR_Z_5_BASE};
                DILITHIUM_SIGN_VALID_S+23 : data_o <= '{opcode:ABR_UOP_PWA, iter:'h0000, length:'d00, operand1:ABR_Y_6_BASE, operand2:ABR_CS1_6_BASE, operand3:ABR_Z_6_BASE};
                DILITHIUM_SIGN_CLEAR_Y    : data_o <= '{opcode:ABR_UOP_NOP, iter:'h0000, length:'d00, operand1:ABR_NOP, operand2:ABR_NOP, operand3:ABR_NOP};
                //⟨⟨cs2⟩⟩←NTT−1(cˆ◦ sˆ2)
                DILITHIUM_SIGN_VALID_S+25 : data_o <= '{opcode:ABR_UOP_PWM, iter:'h0000, length:'d00, operand1:ABR_C_NTT_BASE, operand2:ABR_S2_0_BASE, operand3:ABR_CS2_0_BASE};
                DILITHIUM_SIGN_VALID_S+26 : data_o <= '{opcode:ABR_UOP_PWM, iter:'h0000, length:'d00, operand1:ABR_C_NTT_BASE, operand2:ABR_S2_1_BASE, operand3:ABR_CS2_1_BASE};
                DILITHIUM_SIGN_VALID_S+27 : data_o <= '{opcode:ABR_UOP_PWM, iter:'h0000, length:'d00, operand1:ABR_C_NTT_BASE, operand2:ABR_S2_2_BASE, operand3:ABR_CS2_2_BASE};
                DILITHIUM_SIGN_VALID_S+28 : data_o <= '{opcode:ABR_UOP_PWM, iter:'h0000, length:'d00, operand1:ABR_C_NTT_BASE, operand2:ABR_S2_3_BASE, operand3:ABR_CS2_3_BASE};
                DILITHIUM_SIGN_VALID_S+29 : data_o <= '{opcode:ABR_UOP_PWM, iter:'h0000, length:'d00, operand1:ABR_C_NTT_BASE, operand2:ABR_S2_4_BASE, operand3:ABR_CS2_4_BASE};
                DILITHIUM_SIGN_VALID_S+30 : data_o <= '{opcode:ABR_UOP_PWM, iter:'h0000, length:'d00, operand1:ABR_C_NTT_BASE, operand2:ABR_S2_5_BASE, operand3:ABR_CS2_5_BASE};
                DILITHIUM_SIGN_VALID_S+31 : data_o <= '{opcode:ABR_UOP_PWM, iter:'h0000, length:'d00, operand1:ABR_C_NTT_BASE, operand2:ABR_S2_6_BASE, operand3:ABR_CS2_6_BASE};
                DILITHIUM_SIGN_VALID_S+32 : data_o <= '{opcode:ABR_UOP_PWM, iter:'h0000, length:'d00, operand1:ABR_C_NTT_BASE, operand2:ABR_S2_7_BASE, operand3:ABR_CS2_7_BASE};
                DILITHIUM_SIGN_VALID_S+33 : data_o <= '{opcode:ABR_UOP_INTT, iter:'h0000, length:'d00, operand1:ABR_CS2_0_BASE, operand2:ABR_TEMP0_BASE, operand3:ABR_CS2_0_BASE};
                DILITHIUM_SIGN_VALID_S+34 : data_o <= '{opcode:ABR_UOP_INTT, iter:'h0000, length:'d00, operand1:ABR_CS2_1_BASE, operand2:ABR_TEMP0_BASE, operand3:ABR_CS2_1_BASE};
                DILITHIUM_SIGN_VALID_S+35 : data_o <= '{opcode:ABR_UOP_INTT, iter:'h0000, length:'d00, operand1:ABR_CS2_2_BASE, operand2:ABR_TEMP0_BASE, operand3:ABR_CS2_2_BASE};
                DILITHIUM_SIGN_VALID_S+36 : data_o <= '{opcode:ABR_UOP_INTT, iter:'h0000, length:'d00, operand1:ABR_CS2_3_BASE, operand2:ABR_TEMP0_BASE, operand3:ABR_CS2_3_BASE};
                DILITHIUM_SIGN_VALID_S+37 : data_o <= '{opcode:ABR_UOP_INTT, iter:'h0000, length:'d00, operand1:ABR_CS2_4_BASE, operand2:ABR_TEMP0_BASE, operand3:ABR_CS2_4_BASE};
                DILITHIUM_SIGN_VALID_S+38 : data_o <= '{opcode:ABR_UOP_INTT, iter:'h0000, length:'d00, operand1:ABR_CS2_5_BASE, operand2:ABR_TEMP0_BASE, operand3:ABR_CS2_5_BASE};
                DILITHIUM_SIGN_VALID_S+39 : data_o <= '{opcode:ABR_UOP_INTT, iter:'h0000, length:'d00, operand1:ABR_CS2_6_BASE, operand2:ABR_TEMP0_BASE, operand3:ABR_CS2_6_BASE};
                DILITHIUM_SIGN_VALID_S+40 : data_o <= '{opcode:ABR_UOP_INTT, iter:'h0000, length:'d00, operand1:ABR_CS2_7_BASE, operand2:ABR_TEMP0_BASE, operand3:ABR_CS2_7_BASE};
                //r0 ←(w0 −⟨⟨cs2⟩⟩)
                DILITHIUM_SIGN_CHECK_W0_VLD : data_o <= '{opcode:ABR_UOP_NOP, iter:'h0000, length:'d00, operand1:ABR_NOP, operand2:ABR_NOP, operand3:ABR_NOP};
                DILITHIUM_SIGN_VALID_S+42 : data_o <= '{opcode:ABR_UOP_PWS, iter:'h0000, length:'d00, operand1:ABR_CS2_0_BASE, operand2:ABR_W0_0_BASE, operand3:ABR_R0_0_BASE};
                DILITHIUM_SIGN_VALID_S+43 : data_o <= '{opcode:ABR_UOP_PWS, iter:'h0000, length:'d00, operand1:ABR_CS2_1_BASE, operand2:ABR_W0_1_BASE, operand3:ABR_R0_1_BASE};
                DILITHIUM_SIGN_VALID_S+44 : data_o <= '{opcode:ABR_UOP_PWS, iter:'h0000, length:'d00, operand1:ABR_CS2_2_BASE, operand2:ABR_W0_2_BASE, operand3:ABR_R0_2_BASE};
                DILITHIUM_SIGN_VALID_S+45 : data_o <= '{opcode:ABR_UOP_PWS, iter:'h0000, length:'d00, operand1:ABR_CS2_3_BASE, operand2:ABR_W0_3_BASE, operand3:ABR_R0_3_BASE};
                DILITHIUM_SIGN_VALID_S+46 : data_o <= '{opcode:ABR_UOP_PWS, iter:'h0000, length:'d00, operand1:ABR_CS2_4_BASE, operand2:ABR_W0_4_BASE, operand3:ABR_R0_4_BASE};
                DILITHIUM_SIGN_VALID_S+47 : data_o <= '{opcode:ABR_UOP_PWS, iter:'h0000, length:'d00, operand1:ABR_CS2_5_BASE, operand2:ABR_W0_5_BASE, operand3:ABR_R0_5_BASE};
                DILITHIUM_SIGN_VALID_S+48 : data_o <= '{opcode:ABR_UOP_PWS, iter:'h0000, length:'d00, operand1:ABR_CS2_6_BASE, operand2:ABR_W0_6_BASE, operand3:ABR_R0_6_BASE};
                DILITHIUM_SIGN_VALID_S+49 : data_o <= '{opcode:ABR_UOP_PWS, iter:'h0000, length:'d00, operand1:ABR_CS2_7_BASE, operand2:ABR_W0_7_BASE, operand3:ABR_R0_7_BASE};
                DILITHIUM_SIGN_CLEAR_W0   : data_o <= '{opcode:ABR_UOP_NOP, iter:'h0000, length:'d00, operand1:ABR_NOP, operand2:ABR_NOP, operand3:ABR_NOP};
                //⟨⟨ct0⟩⟩←NTT−1(cˆ◦ tˆ0) - Ct0 overwrites Cs2
                DILITHIUM_SIGN_VALID_S+51 : data_o <= '{opcode:ABR_UOP_PWM, iter:'h0000, length:'d00, operand1:ABR_C_NTT_BASE, operand2:ABR_T0_BASE, operand3:ABR_CT_0_BASE};
                DILITHIUM_SIGN_VALID_S+52 : data_o <= '{opcode:ABR_UOP_PWM, iter:'h0000, length:'d00, operand1:ABR_C_NTT_BASE, operand2:ABR_T1_BASE, operand3:ABR_CT_1_BASE};
                DILITHIUM_SIGN_VALID_S+53 : data_o <= '{opcode:ABR_UOP_PWM, iter:'h0000, length:'d00, operand1:ABR_C_NTT_BASE, operand2:ABR_T2_BASE, operand3:ABR_CT_2_BASE};
                DILITHIUM_SIGN_VALID_S+54 : data_o <= '{opcode:ABR_UOP_PWM, iter:'h0000, length:'d00, operand1:ABR_C_NTT_BASE, operand2:ABR_T3_BASE, operand3:ABR_CT_3_BASE};
                DILITHIUM_SIGN_VALID_S+55 : data_o <= '{opcode:ABR_UOP_PWM, iter:'h0000, length:'d00, operand1:ABR_C_NTT_BASE, operand2:ABR_T4_BASE, operand3:ABR_CT_4_BASE};
                DILITHIUM_SIGN_VALID_S+56 : data_o <= '{opcode:ABR_UOP_PWM, iter:'h0000, length:'d00, operand1:ABR_C_NTT_BASE, operand2:ABR_T5_BASE, operand3:ABR_CT_5_BASE};
                DILITHIUM_SIGN_VALID_S+57 : data_o <= '{opcode:ABR_UOP_PWM, iter:'h0000, length:'d00, operand1:ABR_C_NTT_BASE, operand2:ABR_T6_BASE, operand3:ABR_CT_6_BASE};
                DILITHIUM_SIGN_VALID_S+58 : data_o <= '{opcode:ABR_UOP_PWM, iter:'h0000, length:'d00, operand1:ABR_C_NTT_BASE, operand2:ABR_T7_BASE, operand3:ABR_CT_7_BASE};
                DILITHIUM_SIGN_VALID_S+59 : data_o <= '{opcode:ABR_UOP_INTT, iter:'h0000, length:'d00, operand1:ABR_CT_0_BASE, operand2:ABR_TEMP0_BASE, operand3:ABR_CT_0_BASE};
                DILITHIUM_SIGN_VALID_S+60 : data_o <= '{opcode:ABR_UOP_INTT, iter:'h0000, length:'d00, operand1:ABR_CT_1_BASE, operand2:ABR_TEMP0_BASE, operand3:ABR_CT_1_BASE};
                DILITHIUM_SIGN_VALID_S+61 : data_o <= '{opcode:ABR_UOP_INTT, iter:'h0000, length:'d00, operand1:ABR_CT_2_BASE, operand2:ABR_TEMP0_BASE, operand3:ABR_CT_2_BASE};
                DILITHIUM_SIGN_VALID_S+62 : data_o <= '{opcode:ABR_UOP_INTT, iter:'h0000, length:'d00, operand1:ABR_CT_3_BASE, operand2:ABR_TEMP0_BASE, operand3:ABR_CT_3_BASE};
                DILITHIUM_SIGN_VALID_S+63 : data_o <= '{opcode:ABR_UOP_INTT, iter:'h0000, length:'d00, operand1:ABR_CT_4_BASE, operand2:ABR_TEMP0_BASE, operand3:ABR_CT_4_BASE};
                DILITHIUM_SIGN_VALID_S+64 : data_o <= '{opcode:ABR_UOP_INTT, iter:'h0000, length:'d00, operand1:ABR_CT_5_BASE, operand2:ABR_TEMP0_BASE, operand3:ABR_CT_5_BASE};
                DILITHIUM_SIGN_VALID_S+65 : data_o <= '{opcode:ABR_UOP_INTT, iter:'h0000, length:'d00, operand1:ABR_CT_6_BASE, operand2:ABR_TEMP0_BASE, operand3:ABR_CT_6_BASE};
                DILITHIUM_SIGN_VALID_S+66 : data_o <= '{opcode:ABR_UOP_INTT, iter:'h0000, length:'d00, operand1:ABR_CT_7_BASE, operand2:ABR_TEMP0_BASE, operand3:ABR_CT_7_BASE};
                //h ←MakeHint(w1,r0+⟨⟨ct0⟩⟩)
                DILITHIUM_SIGN_VALID_S+67 : data_o <= '{opcode:ABR_UOP_PWA, iter:'h0000, length:'d00, operand1:ABR_R0_0_BASE, operand2:ABR_CT_0_BASE, operand3:ABR_HINT_R_0_BASE};
                DILITHIUM_SIGN_VALID_S+68 : data_o <= '{opcode:ABR_UOP_PWA, iter:'h0000, length:'d00, operand1:ABR_R0_1_BASE, operand2:ABR_CT_1_BASE, operand3:ABR_HINT_R_1_BASE};
                DILITHIUM_SIGN_VALID_S+69 : data_o <= '{opcode:ABR_UOP_PWA, iter:'h0000, length:'d00, operand1:ABR_R0_2_BASE, operand2:ABR_CT_2_BASE, operand3:ABR_HINT_R_2_BASE};
                DILITHIUM_SIGN_VALID_S+70 : data_o <= '{opcode:ABR_UOP_PWA, iter:'h0000, length:'d00, operand1:ABR_R0_3_BASE, operand2:ABR_CT_3_BASE, operand3:ABR_HINT_R_3_BASE};
                DILITHIUM_SIGN_VALID_S+71 : data_o <= '{opcode:ABR_UOP_PWA, iter:'h0000, length:'d00, operand1:ABR_R0_4_BASE, operand2:ABR_CT_4_BASE, operand3:ABR_HINT_R_4_BASE};
                DILITHIUM_SIGN_VALID_S+72 : data_o <= '{opcode:ABR_UOP_PWA, iter:'h0000, length:'d00, operand1:ABR_R0_5_BASE, operand2:ABR_CT_5_BASE, operand3:ABR_HINT_R_5_BASE};
                DILITHIUM_SIGN_VALID_S+73 : data_o <= '{opcode:ABR_UOP_PWA, iter:'h0000, length:'d00, operand1:ABR_R0_6_BASE, operand2:ABR_CT_6_BASE, operand3:ABR_HINT_R_6_BASE};
                DILITHIUM_SIGN_VALID_S+74 : data_o <= '{opcode:ABR_UOP_PWA, iter:'h0000, length:'d00, operand1:ABR_R0_7_BASE, operand2:ABR_CT_7_BASE, operand3:ABR_HINT_R_7_BASE};
                DILITHIUM_SIGN_VALID_S+75 : data_o <= '{opcode:ABR_UOP_MAKEHINT, iter:'h0000, length:'d00, operand1:ABR_HINT_R_0_BASE, operand2:ABR_NOP, operand3:ABR_NOP};
                //||z||∞ ≥ γ1 −β - z is in cs1
                DILITHIUM_SIGN_VALID_S+76 : data_o <= '{opcode:ABR_UOP_NORMCHK, iter:'h0000, length:'d00, operand1:ABR_Z_0_BASE, operand2:ABR_NOP, operand3:ABR_NOP};
                //||r0||∞ ≥ γ2 −β
                DILITHIUM_SIGN_VALID_S+77 : data_o <= '{opcode:ABR_UOP_NORMCHK, iter:'h0001, length:'d00, operand1:ABR_R0_0_BASE, operand2:ABR_NOP, operand3:ABR_NOP};
                //||⟨⟨ct0⟩⟩||∞ ≥ γ2 - ct0 is in cs2
                DILITHIUM_SIGN_VALID_S+78 : data_o <= '{opcode:ABR_UOP_NORMCHK, iter:'h0002, length:'d00, operand1:ABR_CT_0_BASE, operand2:ABR_NOP, operand3:ABR_NOP};
                //Signing signature generation
                DILITHIUM_SIGN_GEN_S   : data_o <= '{opcode:ABR_UOP_NOP, iter:'h0000, length:'d00, operand1:ABR_NOP, operand2:ABR_NOP, operand3:ABR_NOP};
                DILITHIUM_SIGN_CLEAR_C : data_o <= '{opcode:ABR_UOP_NOP, iter:'h0000, length:'d00, operand1:ABR_NOP, operand2:ABR_NOP, operand3:ABR_NOP};
                DILITHIUM_SIGN_GEN_S+2 : data_o <= '{opcode:ABR_UOP_SIGENCODE, iter:'h0000, length:'d00, operand1:ABR_Z_0_BASE, operand2:ABR_NOP, operand3:ABR_NOP};
                DILITHIUM_SIGN_GEN_E   : data_o <= '{opcode: ABR_UOP_NOP, iter:'h0000, length:'d00, operand1:ABR_NOP, operand2:ABR_NOP, operand3:ABR_NOP};
                default :              data_o <= '{opcode: ABR_UOP_NOP, iter:'h0000, length:'d00, operand1:ABR_NOP, operand2:ABR_NOP, operand3:ABR_NOP};
            endcase 
        end
    end
end

endmodule