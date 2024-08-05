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
//  Keygen
//  Signing - challenge generation
//  Verify

`include "config_defines.svh"

module abr_seq_prim
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
                DILITHIUM_RESET      : data_o <= '{opcode:ABR_UOP_NOP, iter:'h00, length:'d00, operand1:ABR_NOP, operand2:ABR_NOP, operand3:ABR_NOP};

                //KEYGEN
                //(p,p',K)=Keccak(seed)
                //                                //SHAKE256 operation                              //SRC                 //SRC2            //DEST
                DILITHIUM_KG_S       : data_o <= '{opcode:ABR_UOP_SHAKE256, iter:'h00, length:'d32, operand1:ABR_SEED_ID, operand2:ABR_NOP, operand3:ABR_DEST_K_ROH_REG_ID};
                //s1=expandS
                //                                //Rej Bounded op      //SRC iter              //SRC1                 //SRC2            //DEST
                DILITHIUM_KG_S+ 1    : data_o <= '{opcode:ABR_UOP_REJB, iter:'h00, length:'d66, operand1:ABR_ROH_P_ID, operand2:ABR_NOP, operand3:ABR_S1_0_BASE};
                DILITHIUM_KG_S+ 2    : data_o <= '{opcode:ABR_UOP_REJB, iter:'h01, length:'d66, operand1:ABR_ROH_P_ID, operand2:ABR_NOP, operand3:ABR_S1_1_BASE};
                DILITHIUM_KG_S+ 3    : data_o <= '{opcode:ABR_UOP_REJB, iter:'h02, length:'d66, operand1:ABR_ROH_P_ID, operand2:ABR_NOP, operand3:ABR_S1_2_BASE};
                DILITHIUM_KG_S+ 4    : data_o <= '{opcode:ABR_UOP_REJB, iter:'h03, length:'d66, operand1:ABR_ROH_P_ID, operand2:ABR_NOP, operand3:ABR_S1_3_BASE};
                DILITHIUM_KG_S+ 5    : data_o <= '{opcode:ABR_UOP_REJB, iter:'h04, length:'d66, operand1:ABR_ROH_P_ID, operand2:ABR_NOP, operand3:ABR_S1_4_BASE};
                DILITHIUM_KG_S+ 6    : data_o <= '{opcode:ABR_UOP_REJB, iter:'h05, length:'d66, operand1:ABR_ROH_P_ID, operand2:ABR_NOP, operand3:ABR_S1_5_BASE};
                DILITHIUM_KG_S+ 7    : data_o <= '{opcode:ABR_UOP_REJB, iter:'h06, length:'d66, operand1:ABR_ROH_P_ID, operand2:ABR_NOP, operand3:ABR_S1_6_BASE};
                //s1=expandS
                DILITHIUM_KG_S+ 8    : data_o <= '{opcode:ABR_UOP_REJB, iter:'h07, length:'d66, operand1:ABR_ROH_P_ID, operand2:ABR_NOP, operand3:ABR_S2_0_BASE};
                DILITHIUM_KG_S+ 9    : data_o <= '{opcode:ABR_UOP_REJB, iter:'h08, length:'d66, operand1:ABR_ROH_P_ID, operand2:ABR_NOP, operand3:ABR_S2_1_BASE};
                DILITHIUM_KG_S+ 10   : data_o <= '{opcode:ABR_UOP_REJB, iter:'h09, length:'d66, operand1:ABR_ROH_P_ID, operand2:ABR_NOP, operand3:ABR_S2_2_BASE};
                DILITHIUM_KG_S+ 11   : data_o <= '{opcode:ABR_UOP_REJB, iter:'h0A, length:'d66, operand1:ABR_ROH_P_ID, operand2:ABR_NOP, operand3:ABR_S2_3_BASE};
                DILITHIUM_KG_S+ 12   : data_o <= '{opcode:ABR_UOP_REJB, iter:'h0B, length:'d66, operand1:ABR_ROH_P_ID, operand2:ABR_NOP, operand3:ABR_S2_4_BASE};
                DILITHIUM_KG_S+ 13   : data_o <= '{opcode:ABR_UOP_REJB, iter:'h0C, length:'d66, operand1:ABR_ROH_P_ID, operand2:ABR_NOP, operand3:ABR_S2_5_BASE};
                DILITHIUM_KG_S+ 14   : data_o <= '{opcode:ABR_UOP_REJB, iter:'h0D, length:'d66, operand1:ABR_ROH_P_ID, operand2:ABR_NOP, operand3:ABR_S2_6_BASE};
                DILITHIUM_KG_S+ 15   : data_o <= '{opcode:ABR_UOP_REJB, iter:'h0E, length:'d66, operand1:ABR_ROH_P_ID, operand2:ABR_NOP, operand3:ABR_S2_7_BASE};
                //NTT(s1)
                DILITHIUM_KG_S+ 16   : data_o <= '{opcode:ABR_UOP_NTT,  iter:'h00, length:'d00, operand1:ABR_S1_0_BASE, operand2:ABR_TEMP3_BASE, operand3:ABR_S1_0_NTT_BASE};
                DILITHIUM_KG_S+ 17   : data_o <= '{opcode:ABR_UOP_NTT,  iter:'h00, length:'d00, operand1:ABR_S1_1_BASE, operand2:ABR_TEMP3_BASE, operand3:ABR_S1_1_NTT_BASE};
                DILITHIUM_KG_S+ 18   : data_o <= '{opcode:ABR_UOP_NTT,  iter:'h00, length:'d00, operand1:ABR_S1_2_BASE, operand2:ABR_TEMP3_BASE, operand3:ABR_S1_2_NTT_BASE};
                DILITHIUM_KG_S+ 19   : data_o <= '{opcode:ABR_UOP_NTT,  iter:'h00, length:'d00, operand1:ABR_S1_3_BASE, operand2:ABR_TEMP3_BASE, operand3:ABR_S1_3_NTT_BASE};
                DILITHIUM_KG_S+ 20   : data_o <= '{opcode:ABR_UOP_NTT,  iter:'h00, length:'d00, operand1:ABR_S1_4_BASE, operand2:ABR_TEMP3_BASE, operand3:ABR_S1_4_NTT_BASE};
                DILITHIUM_KG_S+ 21   : data_o <= '{opcode:ABR_UOP_NTT,  iter:'h00, length:'d00, operand1:ABR_S1_5_BASE, operand2:ABR_TEMP3_BASE, operand3:ABR_S1_5_NTT_BASE};
                DILITHIUM_KG_S+ 22   : data_o <= '{opcode:ABR_UOP_NTT,  iter:'h00, length:'d00, operand1:ABR_S1_6_BASE, operand2:ABR_TEMP3_BASE, operand3:ABR_S1_6_NTT_BASE};
                //ExpandA(ρ) AND Aˆ NTT(s1)
                DILITHIUM_KG_S+ 23   : data_o <= '{opcode:ABR_UOP_REJS_PWM,  iter:'h00, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_0_NTT_BASE, operand3:ABR_AS0_BASE};
                DILITHIUM_KG_S+ 24   : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h01, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_1_NTT_BASE, operand3:ABR_AS0_BASE};
                DILITHIUM_KG_S+ 25   : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h02, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_2_NTT_BASE, operand3:ABR_AS0_BASE};
                DILITHIUM_KG_S+ 26   : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h03, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_3_NTT_BASE, operand3:ABR_AS0_BASE};
                DILITHIUM_KG_S+ 27   : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h04, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_4_NTT_BASE, operand3:ABR_AS0_BASE};
                DILITHIUM_KG_S+ 28   : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h05, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_5_NTT_BASE, operand3:ABR_AS0_BASE};
                DILITHIUM_KG_S+ 29   : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h06, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_6_NTT_BASE, operand3:ABR_AS0_BASE};

                DILITHIUM_KG_S+ 30   : data_o <= '{opcode:ABR_UOP_REJS_PWM,  iter:'h10, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_0_NTT_BASE, operand3:ABR_AS1_BASE};
                DILITHIUM_KG_S+ 31   : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h11, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_1_NTT_BASE, operand3:ABR_AS1_BASE};
                DILITHIUM_KG_S+ 32   : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h12, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_2_NTT_BASE, operand3:ABR_AS1_BASE};
                DILITHIUM_KG_S+ 33   : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h13, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_3_NTT_BASE, operand3:ABR_AS1_BASE};
                DILITHIUM_KG_S+ 34   : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h14, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_4_NTT_BASE, operand3:ABR_AS1_BASE};
                DILITHIUM_KG_S+ 35   : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h15, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_5_NTT_BASE, operand3:ABR_AS1_BASE};
                DILITHIUM_KG_S+ 36   : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h16, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_6_NTT_BASE, operand3:ABR_AS1_BASE};

                DILITHIUM_KG_S+ 37   : data_o <= '{opcode:ABR_UOP_REJS_PWM,  iter:'h20, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_0_NTT_BASE, operand3:ABR_AS2_BASE};
                DILITHIUM_KG_S+ 38   : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h21, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_1_NTT_BASE, operand3:ABR_AS2_BASE};
                DILITHIUM_KG_S+ 39   : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h22, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_2_NTT_BASE, operand3:ABR_AS2_BASE};
                DILITHIUM_KG_S+ 40   : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h23, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_3_NTT_BASE, operand3:ABR_AS2_BASE};
                DILITHIUM_KG_S+ 41   : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h24, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_4_NTT_BASE, operand3:ABR_AS2_BASE};
                DILITHIUM_KG_S+ 42   : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h25, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_5_NTT_BASE, operand3:ABR_AS2_BASE};
                DILITHIUM_KG_S+ 43   : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h26, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_6_NTT_BASE, operand3:ABR_AS2_BASE};

                DILITHIUM_KG_S+ 44   : data_o <= '{opcode:ABR_UOP_REJS_PWM,  iter:'h30, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_0_NTT_BASE, operand3:ABR_AS3_BASE};
                DILITHIUM_KG_S+ 45   : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h31, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_1_NTT_BASE, operand3:ABR_AS3_BASE};
                DILITHIUM_KG_S+ 46   : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h32, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_2_NTT_BASE, operand3:ABR_AS3_BASE};
                DILITHIUM_KG_S+ 47   : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h33, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_3_NTT_BASE, operand3:ABR_AS3_BASE};
                DILITHIUM_KG_S+ 48   : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h34, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_4_NTT_BASE, operand3:ABR_AS3_BASE};
                DILITHIUM_KG_S+ 49   : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h35, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_5_NTT_BASE, operand3:ABR_AS3_BASE};
                DILITHIUM_KG_S+ 50   : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h36, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_6_NTT_BASE, operand3:ABR_AS3_BASE};

                DILITHIUM_KG_S+ 51   : data_o <= '{opcode:ABR_UOP_REJS_PWM,  iter:'h40, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_0_NTT_BASE, operand3:ABR_AS4_BASE};
                DILITHIUM_KG_S+ 52   : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h41, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_1_NTT_BASE, operand3:ABR_AS4_BASE};
                DILITHIUM_KG_S+ 53   : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h42, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_2_NTT_BASE, operand3:ABR_AS4_BASE};
                DILITHIUM_KG_S+ 54   : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h43, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_3_NTT_BASE, operand3:ABR_AS4_BASE};
                DILITHIUM_KG_S+ 55   : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h44, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_4_NTT_BASE, operand3:ABR_AS4_BASE};
                DILITHIUM_KG_S+ 56   : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h45, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_5_NTT_BASE, operand3:ABR_AS4_BASE};
                DILITHIUM_KG_S+ 57   : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h46, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_6_NTT_BASE, operand3:ABR_AS4_BASE};

                DILITHIUM_KG_S+ 58   : data_o <= '{opcode:ABR_UOP_REJS_PWM,  iter:'h50, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_0_NTT_BASE, operand3:ABR_AS5_BASE};
                DILITHIUM_KG_S+ 59   : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h51, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_1_NTT_BASE, operand3:ABR_AS5_BASE};
                DILITHIUM_KG_S+ 60   : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h52, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_2_NTT_BASE, operand3:ABR_AS5_BASE};
                DILITHIUM_KG_S+ 61   : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h53, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_3_NTT_BASE, operand3:ABR_AS5_BASE};
                DILITHIUM_KG_S+ 62   : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h54, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_4_NTT_BASE, operand3:ABR_AS5_BASE};
                DILITHIUM_KG_S+ 63   : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h55, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_5_NTT_BASE, operand3:ABR_AS5_BASE};
                DILITHIUM_KG_S+ 64   : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h56, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_6_NTT_BASE, operand3:ABR_AS5_BASE};

                DILITHIUM_KG_S+ 65   : data_o <= '{opcode:ABR_UOP_REJS_PWM,  iter:'h60, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_0_NTT_BASE, operand3:ABR_AS6_BASE};
                DILITHIUM_KG_S+ 66   : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h61, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_1_NTT_BASE, operand3:ABR_AS6_BASE};
                DILITHIUM_KG_S+ 67   : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h62, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_2_NTT_BASE, operand3:ABR_AS6_BASE};
                DILITHIUM_KG_S+ 68   : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h63, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_3_NTT_BASE, operand3:ABR_AS6_BASE};
                DILITHIUM_KG_S+ 69   : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h64, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_4_NTT_BASE, operand3:ABR_AS6_BASE};
                DILITHIUM_KG_S+ 70   : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h65, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_5_NTT_BASE, operand3:ABR_AS6_BASE};
                DILITHIUM_KG_S+ 71   : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h66, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_6_NTT_BASE, operand3:ABR_AS6_BASE};

                DILITHIUM_KG_S+ 72   : data_o <= '{opcode:ABR_UOP_REJS_PWM,  iter:'h70, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_0_NTT_BASE, operand3:ABR_AS7_BASE};
                DILITHIUM_KG_S+ 73   : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h71, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_1_NTT_BASE, operand3:ABR_AS7_BASE};
                DILITHIUM_KG_S+ 74   : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h72, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_2_NTT_BASE, operand3:ABR_AS7_BASE};
                DILITHIUM_KG_S+ 75   : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h73, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_3_NTT_BASE, operand3:ABR_AS7_BASE};
                DILITHIUM_KG_S+ 76   : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h74, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_4_NTT_BASE, operand3:ABR_AS7_BASE};
                DILITHIUM_KG_S+ 77   : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h75, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_5_NTT_BASE, operand3:ABR_AS7_BASE};
                DILITHIUM_KG_S+ 78   : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h76, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_S1_6_NTT_BASE, operand3:ABR_AS7_BASE};
                //NTT−1(Aˆ ◦NTT(s1))
                DILITHIUM_KG_S+ 79   : data_o <= '{opcode:ABR_UOP_INTT, iter:'d00, length:'d00, operand1:ABR_AS0_BASE, operand2:ABR_TEMP3_BASE, operand3:ABR_AS0_INTT_BASE};
                DILITHIUM_KG_S+ 80   : data_o <= '{opcode:ABR_UOP_INTT, iter:'d00, length:'d00, operand1:ABR_AS1_BASE, operand2:ABR_TEMP3_BASE, operand3:ABR_AS1_INTT_BASE};
                DILITHIUM_KG_S+ 81   : data_o <= '{opcode:ABR_UOP_INTT, iter:'d00, length:'d00, operand1:ABR_AS2_BASE, operand2:ABR_TEMP3_BASE, operand3:ABR_AS2_INTT_BASE};
                DILITHIUM_KG_S+ 82   : data_o <= '{opcode:ABR_UOP_INTT, iter:'d00, length:'d00, operand1:ABR_AS3_BASE, operand2:ABR_TEMP3_BASE, operand3:ABR_AS3_INTT_BASE};
                DILITHIUM_KG_S+ 83   : data_o <= '{opcode:ABR_UOP_INTT, iter:'d00, length:'d00, operand1:ABR_AS4_BASE, operand2:ABR_TEMP3_BASE, operand3:ABR_AS4_INTT_BASE};
                DILITHIUM_KG_S+ 84   : data_o <= '{opcode:ABR_UOP_INTT, iter:'d00, length:'d00, operand1:ABR_AS5_BASE, operand2:ABR_TEMP3_BASE, operand3:ABR_AS5_INTT_BASE};
                DILITHIUM_KG_S+ 85   : data_o <= '{opcode:ABR_UOP_INTT, iter:'d00, length:'d00, operand1:ABR_AS6_BASE, operand2:ABR_TEMP3_BASE, operand3:ABR_AS6_INTT_BASE};
                DILITHIUM_KG_S+ 86   : data_o <= '{opcode:ABR_UOP_INTT, iter:'d00, length:'d00, operand1:ABR_AS7_BASE, operand2:ABR_TEMP3_BASE, operand3:ABR_AS7_INTT_BASE};
                //t ←NTT−1(Aˆ ◦NTT(s1))+s2
                DILITHIUM_KG_S+ 87   : data_o <= '{opcode:ABR_UOP_PWA, iter:'d00, length:'d00, operand1:ABR_AS0_INTT_BASE, operand2:ABR_S2_0_BASE, operand3:ABR_T0_BASE};
                DILITHIUM_KG_S+ 88   : data_o <= '{opcode:ABR_UOP_PWA, iter:'d00, length:'d00, operand1:ABR_AS1_INTT_BASE, operand2:ABR_S2_1_BASE, operand3:ABR_T1_BASE};
                DILITHIUM_KG_S+ 89   : data_o <= '{opcode:ABR_UOP_PWA, iter:'d00, length:'d00, operand1:ABR_AS2_INTT_BASE, operand2:ABR_S2_2_BASE, operand3:ABR_T2_BASE};
                DILITHIUM_KG_S+ 90   : data_o <= '{opcode:ABR_UOP_PWA, iter:'d00, length:'d00, operand1:ABR_AS3_INTT_BASE, operand2:ABR_S2_3_BASE, operand3:ABR_T3_BASE};
                DILITHIUM_KG_S+ 91   : data_o <= '{opcode:ABR_UOP_PWA, iter:'d00, length:'d00, operand1:ABR_AS4_INTT_BASE, operand2:ABR_S2_4_BASE, operand3:ABR_T4_BASE};
                DILITHIUM_KG_S+ 92   : data_o <= '{opcode:ABR_UOP_PWA, iter:'d00, length:'d00, operand1:ABR_AS5_INTT_BASE, operand2:ABR_S2_5_BASE, operand3:ABR_T5_BASE};
                DILITHIUM_KG_S+ 93   : data_o <= '{opcode:ABR_UOP_PWA, iter:'d00, length:'d00, operand1:ABR_AS6_INTT_BASE, operand2:ABR_S2_6_BASE, operand3:ABR_T6_BASE};
                DILITHIUM_KG_S+ 94   : data_o <= '{opcode:ABR_UOP_PWA, iter:'d00, length:'d00, operand1:ABR_AS7_INTT_BASE, operand2:ABR_S2_7_BASE, operand3:ABR_T7_BASE};
                //(t1,t0)←Power2Round(t,d) AND pk ←pkEncode(ρ,t1)

                //tr ←H(BytesToBits(pk),512)

                //sk ←skEncode(ρ,K,tr,s1,s2,t0)

                //KG end
                DILITHIUM_KG_E       : data_o <= '{opcode:ABR_UOP_NOP, iter:'h00, length:'d00, operand1:ABR_NOP, operand2:ABR_NOP, operand3:ABR_NOP};

                //Signing start
                //μ ←H(tr||M,512)
                DILITHIUM_SIGN_S     : data_o <= '{opcode:ABR_UOP_LD_SHAKE256, iter:'h00, length:'d64, operand1:ABR_TR_ID, operand2:ABR_NOP, operand3:ABR_NOP};
                DILITHIUM_SIGN_S+ 1  : data_o <= '{opcode:ABR_UOP_SHAKE256, iter:'h00, length:'d64, operand1:ABR_MSG_ID, operand2:ABR_NOP, operand3:ABR_DEST_MU_REG_ID};
                //ρ′=Keccak(K||rnd|| μ)
                DILITHIUM_SIGN_S+ 2  : data_o <= '{opcode:ABR_UOP_LD_SHAKE256, iter:'h00, length:'d32, operand1:ABR_K_ID, operand2:ABR_NOP, operand3:ABR_NOP};
                DILITHIUM_SIGN_S+ 3  : data_o <= '{opcode:ABR_UOP_LD_SHAKE256, iter:'h00, length:'d32, operand1:ABR_SIGN_RND_ID, operand2:ABR_NOP, operand3:ABR_NOP};
                DILITHIUM_SIGN_S+ 4  : data_o <= '{opcode:ABR_UOP_SHAKE256, iter:'h00, length:'d64, operand1:ABR_MU_ID, operand2:ABR_NOP, operand3:ABR_DEST_ROH_P_REG_ID};
                //Check Y valid
                DILITHIUM_SIGN_CHECK_Y_CLR  : data_o <= '{opcode:ABR_UOP_NOP, iter:'h00, length:'d00, operand1:ABR_UOP_NOP, operand2:ABR_NOP, operand3:ABR_NOP};
                //y=ExpandMask(ρ’ ,κ)
                DILITHIUM_SIGN_MAKE_Y_S     : data_o <= '{opcode:ABR_UOP_EXP_MASK, iter:'h00, length:'d66, operand1:ABR_ROH_P_KAPPA_ID, operand2:ABR_NOP, operand3:ABR_Y_0_BASE};
                DILITHIUM_SIGN_MAKE_Y_S+ 1  : data_o <= '{opcode:ABR_UOP_EXP_MASK, iter:'h01, length:'d66, operand1:ABR_ROH_P_KAPPA_ID, operand2:ABR_NOP, operand3:ABR_Y_1_BASE};
                DILITHIUM_SIGN_MAKE_Y_S+ 2  : data_o <= '{opcode:ABR_UOP_EXP_MASK, iter:'h02, length:'d66, operand1:ABR_ROH_P_KAPPA_ID, operand2:ABR_NOP, operand3:ABR_Y_2_BASE};
                DILITHIUM_SIGN_MAKE_Y_S+ 3  : data_o <= '{opcode:ABR_UOP_EXP_MASK, iter:'h03, length:'d66, operand1:ABR_ROH_P_KAPPA_ID, operand2:ABR_NOP, operand3:ABR_Y_3_BASE};
                DILITHIUM_SIGN_MAKE_Y_S+ 4  : data_o <= '{opcode:ABR_UOP_EXP_MASK, iter:'h04, length:'d66, operand1:ABR_ROH_P_KAPPA_ID, operand2:ABR_NOP, operand3:ABR_Y_4_BASE};
                DILITHIUM_SIGN_MAKE_Y_S+ 5  : data_o <= '{opcode:ABR_UOP_EXP_MASK, iter:'h05, length:'d66, operand1:ABR_ROH_P_KAPPA_ID, operand2:ABR_NOP, operand3:ABR_Y_5_BASE};
                DILITHIUM_SIGN_MAKE_Y_S+ 6  : data_o <= '{opcode:ABR_UOP_EXP_MASK, iter:'h06, length:'d66, operand1:ABR_ROH_P_KAPPA_ID, operand2:ABR_NOP, operand3:ABR_Y_6_BASE};
                //NTT(Y)
                DILITHIUM_SIGN_MAKE_Y_S+ 7  : data_o <= '{opcode:ABR_UOP_NTT,  iter:'h00, length:'d00, operand1:ABR_Y_0_BASE, operand2:ABR_TEMP3_BASE, operand3:ABR_Y_0_NTT_BASE};
                DILITHIUM_SIGN_MAKE_Y_S+ 8  : data_o <= '{opcode:ABR_UOP_NTT,  iter:'h00, length:'d00, operand1:ABR_Y_1_BASE, operand2:ABR_TEMP3_BASE, operand3:ABR_Y_1_NTT_BASE};
                DILITHIUM_SIGN_MAKE_Y_S+ 9  : data_o <= '{opcode:ABR_UOP_NTT,  iter:'h00, length:'d00, operand1:ABR_Y_2_BASE, operand2:ABR_TEMP3_BASE, operand3:ABR_Y_2_NTT_BASE};
                DILITHIUM_SIGN_MAKE_Y_S+ 10 : data_o <= '{opcode:ABR_UOP_NTT,  iter:'h00, length:'d00, operand1:ABR_Y_3_BASE, operand2:ABR_TEMP3_BASE, operand3:ABR_Y_3_NTT_BASE};
                DILITHIUM_SIGN_MAKE_Y_S+ 11 : data_o <= '{opcode:ABR_UOP_NTT,  iter:'h00, length:'d00, operand1:ABR_Y_4_BASE, operand2:ABR_TEMP3_BASE, operand3:ABR_Y_4_NTT_BASE};
                DILITHIUM_SIGN_MAKE_Y_S+ 12 : data_o <= '{opcode:ABR_UOP_NTT,  iter:'h00, length:'d00, operand1:ABR_Y_5_BASE, operand2:ABR_TEMP3_BASE, operand3:ABR_Y_5_NTT_BASE};
                DILITHIUM_SIGN_MAKE_Y_S+ 13 : data_o <= '{opcode:ABR_UOP_NTT,  iter:'h00, length:'d00, operand1:ABR_Y_6_BASE, operand2:ABR_TEMP3_BASE, operand3:ABR_Y_6_NTT_BASE};
                //Set Y valid
                DILITHIUM_SIGN_SET_Y        : data_o <= '{opcode:ABR_UOP_NOP, iter:'h00, length:'d00, operand1:ABR_UOP_NOP, operand2:ABR_NOP, operand3:ABR_NOP};
                //Aˆ ←ExpandA(ρ) AND Aˆ ◦NTT(y)
                DILITHIUM_SIGN_MAKE_W_S     : data_o <= '{opcode:ABR_UOP_REJS_PWM,  iter:'h00, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_0_NTT_BASE, operand3:ABR_AY0_BASE};
                DILITHIUM_SIGN_MAKE_W_S+ 1  : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h01, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_1_NTT_BASE, operand3:ABR_AY0_BASE};
                DILITHIUM_SIGN_MAKE_W_S+ 2  : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h02, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_2_NTT_BASE, operand3:ABR_AY0_BASE};
                DILITHIUM_SIGN_MAKE_W_S+ 3  : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h03, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_3_NTT_BASE, operand3:ABR_AY0_BASE};
                DILITHIUM_SIGN_MAKE_W_S+ 4  : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h04, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_4_NTT_BASE, operand3:ABR_AY0_BASE};
                DILITHIUM_SIGN_MAKE_W_S+ 5  : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h05, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_5_NTT_BASE, operand3:ABR_AY0_BASE};
                DILITHIUM_SIGN_MAKE_W_S+ 6  : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h06, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_6_NTT_BASE, operand3:ABR_AY0_BASE};

                DILITHIUM_SIGN_MAKE_W_S+ 7  : data_o <= '{opcode:ABR_UOP_REJS_PWM,  iter:'h10, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_0_NTT_BASE, operand3:ABR_AY1_BASE};
                DILITHIUM_SIGN_MAKE_W_S+ 8  : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h11, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_1_NTT_BASE, operand3:ABR_AY1_BASE};
                DILITHIUM_SIGN_MAKE_W_S+ 9  : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h12, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_2_NTT_BASE, operand3:ABR_AY1_BASE};
                DILITHIUM_SIGN_MAKE_W_S+ 10 : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h13, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_3_NTT_BASE, operand3:ABR_AY1_BASE};
                DILITHIUM_SIGN_MAKE_W_S+ 11 : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h14, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_4_NTT_BASE, operand3:ABR_AY1_BASE};
                DILITHIUM_SIGN_MAKE_W_S+ 12 : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h15, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_5_NTT_BASE, operand3:ABR_AY1_BASE};
                DILITHIUM_SIGN_MAKE_W_S+ 13 : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h16, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_6_NTT_BASE, operand3:ABR_AY1_BASE};
                
                DILITHIUM_SIGN_MAKE_W_S+ 14 : data_o <= '{opcode:ABR_UOP_REJS_PWM,  iter:'h20, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_0_NTT_BASE, operand3:ABR_AY2_BASE};
                DILITHIUM_SIGN_MAKE_W_S+ 15 : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h21, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_1_NTT_BASE, operand3:ABR_AY2_BASE};
                DILITHIUM_SIGN_MAKE_W_S+ 16 : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h22, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_2_NTT_BASE, operand3:ABR_AY2_BASE};
                DILITHIUM_SIGN_MAKE_W_S+ 17 : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h23, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_3_NTT_BASE, operand3:ABR_AY2_BASE};
                DILITHIUM_SIGN_MAKE_W_S+ 18 : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h24, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_4_NTT_BASE, operand3:ABR_AY2_BASE};
                DILITHIUM_SIGN_MAKE_W_S+ 19 : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h25, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_5_NTT_BASE, operand3:ABR_AY2_BASE};
                DILITHIUM_SIGN_MAKE_W_S+ 20 : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h26, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_6_NTT_BASE, operand3:ABR_AY2_BASE};
                
                DILITHIUM_SIGN_MAKE_W_S+ 21 : data_o <= '{opcode:ABR_UOP_REJS_PWM,  iter:'h30, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_0_NTT_BASE, operand3:ABR_AY3_BASE};
                DILITHIUM_SIGN_MAKE_W_S+ 22 : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h31, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_1_NTT_BASE, operand3:ABR_AY3_BASE};
                DILITHIUM_SIGN_MAKE_W_S+ 23 : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h32, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_2_NTT_BASE, operand3:ABR_AY3_BASE};
                DILITHIUM_SIGN_MAKE_W_S+ 24 : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h33, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_3_NTT_BASE, operand3:ABR_AY3_BASE};
                DILITHIUM_SIGN_MAKE_W_S+ 25 : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h34, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_4_NTT_BASE, operand3:ABR_AY3_BASE};
                DILITHIUM_SIGN_MAKE_W_S+ 26 : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h35, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_5_NTT_BASE, operand3:ABR_AY3_BASE};
                DILITHIUM_SIGN_MAKE_W_S+ 27 : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h36, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_6_NTT_BASE, operand3:ABR_AY3_BASE};

                DILITHIUM_SIGN_MAKE_W_S+ 28 : data_o <= '{opcode:ABR_UOP_REJS_PWM,  iter:'h40, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_0_NTT_BASE, operand3:ABR_AY4_BASE};
                DILITHIUM_SIGN_MAKE_W_S+ 29 : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h41, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_1_NTT_BASE, operand3:ABR_AY4_BASE};
                DILITHIUM_SIGN_MAKE_W_S+ 30 : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h42, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_2_NTT_BASE, operand3:ABR_AY4_BASE};
                DILITHIUM_SIGN_MAKE_W_S+ 31 : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h43, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_3_NTT_BASE, operand3:ABR_AY4_BASE};
                DILITHIUM_SIGN_MAKE_W_S+ 32 : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h44, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_4_NTT_BASE, operand3:ABR_AY4_BASE};
                DILITHIUM_SIGN_MAKE_W_S+ 33 : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h45, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_5_NTT_BASE, operand3:ABR_AY4_BASE};
                DILITHIUM_SIGN_MAKE_W_S+ 34 : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h46, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_6_NTT_BASE, operand3:ABR_AY4_BASE};
    
                DILITHIUM_SIGN_MAKE_W_S+ 35 : data_o <= '{opcode:ABR_UOP_REJS_PWM,  iter:'h50, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_0_NTT_BASE, operand3:ABR_AY5_BASE};
                DILITHIUM_SIGN_MAKE_W_S+ 36 : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h51, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_1_NTT_BASE, operand3:ABR_AY5_BASE};
                DILITHIUM_SIGN_MAKE_W_S+ 37 : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h52, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_2_NTT_BASE, operand3:ABR_AY5_BASE};
                DILITHIUM_SIGN_MAKE_W_S+ 38 : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h53, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_3_NTT_BASE, operand3:ABR_AY5_BASE};
                DILITHIUM_SIGN_MAKE_W_S+ 39 : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h54, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_4_NTT_BASE, operand3:ABR_AY5_BASE};
                DILITHIUM_SIGN_MAKE_W_S+ 40 : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h55, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_5_NTT_BASE, operand3:ABR_AY5_BASE};
                DILITHIUM_SIGN_MAKE_W_S+ 41 : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h56, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_6_NTT_BASE, operand3:ABR_AY5_BASE};
                
                DILITHIUM_SIGN_MAKE_W_S+ 42 : data_o <= '{opcode:ABR_UOP_REJS_PWM,  iter:'h60, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_0_NTT_BASE, operand3:ABR_AY6_BASE};
                DILITHIUM_SIGN_MAKE_W_S+ 43 : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h61, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_1_NTT_BASE, operand3:ABR_AY6_BASE};
                DILITHIUM_SIGN_MAKE_W_S+ 44 : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h62, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_2_NTT_BASE, operand3:ABR_AY6_BASE};
                DILITHIUM_SIGN_MAKE_W_S+ 45 : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h63, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_3_NTT_BASE, operand3:ABR_AY6_BASE};
                DILITHIUM_SIGN_MAKE_W_S+ 46 : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h64, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_4_NTT_BASE, operand3:ABR_AY6_BASE};
                DILITHIUM_SIGN_MAKE_W_S+ 47 : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h65, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_5_NTT_BASE, operand3:ABR_AY6_BASE};
                DILITHIUM_SIGN_MAKE_W_S+ 48 : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h66, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_6_NTT_BASE, operand3:ABR_AY6_BASE};
                
                DILITHIUM_SIGN_MAKE_W_S+ 49 : data_o <= '{opcode:ABR_UOP_REJS_PWM,  iter:'h70, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_0_NTT_BASE, operand3:ABR_AY7_BASE};
                DILITHIUM_SIGN_MAKE_W_S+ 50 : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h71, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_1_NTT_BASE, operand3:ABR_AY7_BASE};
                DILITHIUM_SIGN_MAKE_W_S+ 51 : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h72, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_2_NTT_BASE, operand3:ABR_AY7_BASE};
                DILITHIUM_SIGN_MAKE_W_S+ 52 : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h73, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_3_NTT_BASE, operand3:ABR_AY7_BASE};
                DILITHIUM_SIGN_MAKE_W_S+ 53 : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h74, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_4_NTT_BASE, operand3:ABR_AY7_BASE};
                DILITHIUM_SIGN_MAKE_W_S+ 54 : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h75, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_5_NTT_BASE, operand3:ABR_AY7_BASE};
                DILITHIUM_SIGN_MAKE_W_S+ 55 : data_o <= '{opcode:ABR_UOP_REJS_PWMA, iter:'h76, length:'d34, operand1:ABR_ROH_ID, operand2:ABR_Y_6_NTT_BASE, operand3:ABR_AY7_BASE};
                //w ←NTT−1(Aˆ ◦NTT(y))
                DILITHIUM_SIGN_MAKE_W_S+ 56 : data_o <= '{opcode:ABR_UOP_INTT,  iter:'h00, length:'d00, operand1:ABR_AY0_BASE, operand2:ABR_TEMP3_BASE, operand3:ABR_AY0_BASE};
                DILITHIUM_SIGN_MAKE_W_S+ 57 : data_o <= '{opcode:ABR_UOP_INTT,  iter:'h00, length:'d00, operand1:ABR_AY1_BASE, operand2:ABR_TEMP3_BASE, operand3:ABR_AY1_BASE};
                DILITHIUM_SIGN_MAKE_W_S+ 58 : data_o <= '{opcode:ABR_UOP_INTT,  iter:'h00, length:'d00, operand1:ABR_AY2_BASE, operand2:ABR_TEMP3_BASE, operand3:ABR_AY2_BASE};
                DILITHIUM_SIGN_MAKE_W_S+ 59 : data_o <= '{opcode:ABR_UOP_INTT,  iter:'h00, length:'d00, operand1:ABR_AY3_BASE, operand2:ABR_TEMP3_BASE, operand3:ABR_AY3_BASE};
                DILITHIUM_SIGN_MAKE_W_S+ 60 : data_o <= '{opcode:ABR_UOP_INTT,  iter:'h00, length:'d00, operand1:ABR_AY4_BASE, operand2:ABR_TEMP3_BASE, operand3:ABR_AY4_BASE};
                DILITHIUM_SIGN_MAKE_W_S+ 61 : data_o <= '{opcode:ABR_UOP_INTT,  iter:'h00, length:'d00, operand1:ABR_AY5_BASE, operand2:ABR_TEMP3_BASE, operand3:ABR_AY5_BASE};
                DILITHIUM_SIGN_MAKE_W_S+ 62 : data_o <= '{opcode:ABR_UOP_INTT,  iter:'h00, length:'d00, operand1:ABR_AY6_BASE, operand2:ABR_TEMP3_BASE, operand3:ABR_AY6_BASE};
                DILITHIUM_SIGN_MAKE_W_S+ 63 : data_o <= '{opcode:ABR_UOP_INTT,  iter:'h00, length:'d00, operand1:ABR_AY7_BASE, operand2:ABR_TEMP3_BASE, operand3:ABR_AY7_BASE};
                //(w1,w0) ←Decompose(w) AND c˜←H(μ||w1Encode(w1),2λ)
                DILITHIUM_SIGN_MAKE_W_S+ 64 : data_o <= '{opcode:ABR_UOP_LD_SHAKE256, iter:'h00, length:'d64, operand1:ABR_MU_ID, operand2:ABR_NOP, operand3:ABR_NOP};
                //Check W0 valid
                DILITHIUM_SIGN_CHECK_W0_CLR : data_o <= '{opcode:ABR_UOP_NOP, iter:'h00, length:'d00, operand1:ABR_NOP, operand2:ABR_NOP, operand3:ABR_NOP};
                DILITHIUM_SIGN_MAKE_W       : data_o <= '{opcode:ABR_UOP_NOP, iter:'h00, length:'d00, operand1:ABR_NOP, operand2:ABR_NOP, operand3:ABR_NOP}; //decompose TODO
                DILITHIUM_SIGN_SET_W0       : data_o <= '{opcode:ABR_UOP_NOP, iter:'h00, length:'d00, operand1:ABR_NOP, operand2:ABR_NOP, operand3:ABR_NOP};
                // c ←SampleInBall(c˜1)
                //Check C valid
                DILITHIUM_SIGN_CHECK_C_CLR  : data_o <= '{opcode:ABR_UOP_NOP, iter:'h00, length:'d00, operand1:ABR_NOP, operand2:ABR_NOP, operand3:ABR_NOP};
                DILITHIUM_SIGN_MAKE_C       : data_o <= '{opcode:ABR_UOP_SIB, iter:'h00, length:'d00, operand1:ABR_NOP, operand2:ABR_NOP, operand3:ABR_NOP};
                DILITHIUM_SIGN_SET_C        : data_o <= '{opcode:ABR_UOP_NOP, iter:'h00, length:'d00, operand1:ABR_NOP, operand2:ABR_NOP, operand3:ABR_NOP};

                DILITHIUM_SIGN_E            : data_o <= '{opcode:ABR_UOP_NOP, iter:'h00, length:'d00, operand1:ABR_NOP, operand2:ABR_NOP, operand3:ABR_NOP};

                default :              data_o <= '{opcode: ABR_UOP_NOP, iter:'h00, length:'d00, operand1:ABR_NOP, operand2:ABR_NOP, operand3:ABR_NOP};
            endcase 
        end
    end
end

endmodule