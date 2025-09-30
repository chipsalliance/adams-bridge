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

//Sequencer for ABR
//ML-DSA functions
//  Keygen
//  Signing
//  Verify
//ML-KEM functions
//  Keygen

module abr_seq
  import abr_ctrl_pkg::*;
  (
  input logic clk,

  input  logic en_i,
  input  logic [ABR_PROG_ADDR_W-1 : 0] addr_i,
  output abr_seq_instr_t data_o
  );


`ifdef RV_FPGA_OPTIMIZE
    (*rom_style = "block" *) abr_seq_instr_t data_o_rom;
`else 
    abr_seq_instr_t data_o_rom;
`endif
    assign data_o = data_o_rom;

  //----------------------------------------------------------------
  // ROM content
  //----------------------------------------------------------------
 
  always_ff @(posedge clk) begin
        if (en_i) begin
            unique case(addr_i)
                //RESET
                ABR_RESET        : data_o_rom <= '{opcode:ABR_UOP_NOP, imm:'h0000, length:'d00, operand1:ABR_NOP, operand2:ABR_NOP, operand3:ABR_NOP};

                //ZEROIZE
                ABR_ZEROIZE      : data_o_rom <= '{opcode:ABR_UOP_NOP, imm:'h0000, length:'d00, operand1:ABR_NOP, operand2:ABR_NOP, operand3:ABR_NOP};

                //KEYGEN
                //rnd_seed=Keccak(entropy||counter)
                MLDSA_KG_S       : data_o_rom <= '{opcode:ABR_UOP_LD_SHAKE256, imm:'h0000, length:'d64, operand1:ABR_ENTROPY_ID, operand2:ABR_NOP, operand3:ABR_NOP};                
                MLDSA_KG_S+ 1    : data_o_rom <= '{opcode:ABR_UOP_SHAKE256,    imm:'h0000, length:'d08, operand1:ABR_CNT_ID,     operand2:ABR_NOP, operand3:ABR_DEST_LFSR_SEED_REG_ID};
                MLDSA_KG_S+ 2    : data_o_rom <= '{opcode:ABR_UOP_LFSR,        imm:'h0000, length:'d00, operand1:ABR_NOP,        operand2:ABR_NOP, operand3:ABR_NOP};
                //(p,p',K)=Keccak(seed)
                //                                //SHAKE256 operation                              //SRC                 //SRC2            //DEST
                MLDSA_KG_S+ 3    : data_o_rom <= '{opcode:ABR_UOP_SHAKE256, imm:'h0708, length:'d34, operand1:MLDSA_SEED_ID, operand2:ABR_NOP, operand3:MLDSA_DEST_K_RHO_REG_ID};
                //s1=expandS
                //                                //Rej Bounded op      //SRC imm              //SRC1                 //SRC2            //DEST
                MLDSA_KG_S+ 4    : data_o_rom <= '{opcode:ABR_UOP_REJB, imm:'h0000, length:'d66, operand1:MLDSA_RHO_P_ID, operand2:ABR_NOP, operand3:MLDSA_S1_0_BASE};
                MLDSA_KG_S+ 5    : data_o_rom <= '{opcode:ABR_UOP_REJB, imm:'h0001, length:'d66, operand1:MLDSA_RHO_P_ID, operand2:ABR_NOP, operand3:MLDSA_S1_1_BASE};
                MLDSA_KG_S+ 6    : data_o_rom <= '{opcode:ABR_UOP_REJB, imm:'h0002, length:'d66, operand1:MLDSA_RHO_P_ID, operand2:ABR_NOP, operand3:MLDSA_S1_2_BASE};
                MLDSA_KG_S+ 7    : data_o_rom <= '{opcode:ABR_UOP_REJB, imm:'h0003, length:'d66, operand1:MLDSA_RHO_P_ID, operand2:ABR_NOP, operand3:MLDSA_S1_3_BASE};
                MLDSA_KG_S+ 8    : data_o_rom <= '{opcode:ABR_UOP_REJB, imm:'h0004, length:'d66, operand1:MLDSA_RHO_P_ID, operand2:ABR_NOP, operand3:MLDSA_S1_4_BASE};
                MLDSA_KG_S+ 9    : data_o_rom <= '{opcode:ABR_UOP_REJB, imm:'h0005, length:'d66, operand1:MLDSA_RHO_P_ID, operand2:ABR_NOP, operand3:MLDSA_S1_5_BASE};
                MLDSA_KG_S+ 10   : data_o_rom <= '{opcode:ABR_UOP_REJB, imm:'h0006, length:'d66, operand1:MLDSA_RHO_P_ID, operand2:ABR_NOP, operand3:MLDSA_S1_6_BASE};
                //s1=expandS
                MLDSA_KG_S+ 11   : data_o_rom <= '{opcode:ABR_UOP_REJB, imm:'h0007, length:'d66, operand1:MLDSA_RHO_P_ID, operand2:ABR_NOP, operand3:MLDSA_S2_0_BASE};
                MLDSA_KG_S+ 12   : data_o_rom <= '{opcode:ABR_UOP_REJB, imm:'h0008, length:'d66, operand1:MLDSA_RHO_P_ID, operand2:ABR_NOP, operand3:MLDSA_S2_1_BASE};
                MLDSA_KG_S+ 13   : data_o_rom <= '{opcode:ABR_UOP_REJB, imm:'h0009, length:'d66, operand1:MLDSA_RHO_P_ID, operand2:ABR_NOP, operand3:MLDSA_S2_2_BASE};
                MLDSA_KG_S+ 14   : data_o_rom <= '{opcode:ABR_UOP_REJB, imm:'h000A, length:'d66, operand1:MLDSA_RHO_P_ID, operand2:ABR_NOP, operand3:MLDSA_S2_3_BASE};
                MLDSA_KG_S+ 15   : data_o_rom <= '{opcode:ABR_UOP_REJB, imm:'h000B, length:'d66, operand1:MLDSA_RHO_P_ID, operand2:ABR_NOP, operand3:MLDSA_S2_4_BASE};
                MLDSA_KG_S+ 16   : data_o_rom <= '{opcode:ABR_UOP_REJB, imm:'h000C, length:'d66, operand1:MLDSA_RHO_P_ID, operand2:ABR_NOP, operand3:MLDSA_S2_5_BASE};
                MLDSA_KG_S+ 17   : data_o_rom <= '{opcode:ABR_UOP_REJB, imm:'h000D, length:'d66, operand1:MLDSA_RHO_P_ID, operand2:ABR_NOP, operand3:MLDSA_S2_6_BASE};
                MLDSA_KG_S+ 18   : data_o_rom <= '{opcode:ABR_UOP_REJB, imm:'h000E, length:'d66, operand1:MLDSA_RHO_P_ID, operand2:ABR_NOP, operand3:MLDSA_S2_7_BASE};
                //NTT(s1)
                MLDSA_KG_S+ 19   : data_o_rom <= '{opcode:ABR_UOP_NTT,  imm:'h0000, length:'d00, operand1:MLDSA_S1_0_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_S1_0_NTT_BASE};
                MLDSA_KG_S+ 20   : data_o_rom <= '{opcode:ABR_UOP_NTT,  imm:'h0000, length:'d00, operand1:MLDSA_S1_1_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_S1_1_NTT_BASE};
                MLDSA_KG_S+ 21   : data_o_rom <= '{opcode:ABR_UOP_NTT,  imm:'h0000, length:'d00, operand1:MLDSA_S1_2_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_S1_2_NTT_BASE};
                MLDSA_KG_S+ 22   : data_o_rom <= '{opcode:ABR_UOP_NTT,  imm:'h0000, length:'d00, operand1:MLDSA_S1_3_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_S1_3_NTT_BASE};
                MLDSA_KG_S+ 23   : data_o_rom <= '{opcode:ABR_UOP_NTT,  imm:'h0000, length:'d00, operand1:MLDSA_S1_4_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_S1_4_NTT_BASE};
                MLDSA_KG_S+ 24   : data_o_rom <= '{opcode:ABR_UOP_NTT,  imm:'h0000, length:'d00, operand1:MLDSA_S1_5_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_S1_5_NTT_BASE};
                MLDSA_KG_S+ 25   : data_o_rom <= '{opcode:ABR_UOP_NTT,  imm:'h0000, length:'d00, operand1:MLDSA_S1_6_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_S1_6_NTT_BASE};
                //ExpandA(ρ) AND Aˆ NTT(s1)
                MLDSA_KG_S+ 26   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWM,  imm:'h0000, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_0_NTT_BASE, operand3:MLDSA_AS0_BASE};
                MLDSA_KG_S+ 27   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0001, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_1_NTT_BASE, operand3:MLDSA_AS0_BASE};
                MLDSA_KG_S+ 28   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0002, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_2_NTT_BASE, operand3:MLDSA_AS0_BASE};
                MLDSA_KG_S+ 29   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0003, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_3_NTT_BASE, operand3:MLDSA_AS0_BASE};
                MLDSA_KG_S+ 30   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0004, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_4_NTT_BASE, operand3:MLDSA_AS0_BASE};
                MLDSA_KG_S+ 31   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0005, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_5_NTT_BASE, operand3:MLDSA_AS0_BASE};
                MLDSA_KG_S+ 32   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0006, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_6_NTT_BASE, operand3:MLDSA_AS0_BASE};
                //NTT−1(Aˆ ◦NTT(s1))
                MLDSA_KG_S+ 33   : data_o_rom <= '{opcode:ABR_UOP_INTT, imm:'d01, length:'d00, operand1:MLDSA_AS0_BASE, operand2:MLDSA_TEMP2_BASE, operand3:MLDSA_AS0_INTT_BASE};
                //t ←NTT−1(Aˆ ◦NTT(s1))+s2
                MLDSA_KG_S+ 34   : data_o_rom <= '{opcode:ABR_UOP_PWA, imm:'d00, length:'d00, operand1:MLDSA_AS0_INTT_BASE, operand2:MLDSA_S2_0_BASE, operand3:MLDSA_T0_BASE};
                //ExpandA(ρ) AND Aˆ NTT(s1)
                MLDSA_KG_S+ 35   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWM,  imm:'h0100, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_0_NTT_BASE, operand3:MLDSA_AS0_BASE};
                MLDSA_KG_S+ 36   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0101, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_1_NTT_BASE, operand3:MLDSA_AS0_BASE};
                MLDSA_KG_S+ 37   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0102, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_2_NTT_BASE, operand3:MLDSA_AS0_BASE};
                MLDSA_KG_S+ 38   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0103, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_3_NTT_BASE, operand3:MLDSA_AS0_BASE};
                MLDSA_KG_S+ 39   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0104, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_4_NTT_BASE, operand3:MLDSA_AS0_BASE};
                MLDSA_KG_S+ 40   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0105, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_5_NTT_BASE, operand3:MLDSA_AS0_BASE};
                MLDSA_KG_S+ 41   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0106, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_6_NTT_BASE, operand3:MLDSA_AS0_BASE};
                //NTT−1(Aˆ ◦NTT(s1))
                MLDSA_KG_S+ 42   : data_o_rom <= '{opcode:ABR_UOP_INTT, imm:'d01, length:'d00, operand1:MLDSA_AS0_BASE, operand2:MLDSA_TEMP2_BASE, operand3:MLDSA_AS0_INTT_BASE};
                //t ←NTT−1(Aˆ ◦NTT(s1))+s2
                MLDSA_KG_S+ 43   : data_o_rom <= '{opcode:ABR_UOP_PWA, imm:'d00, length:'d00, operand1:MLDSA_AS0_INTT_BASE, operand2:MLDSA_S2_1_BASE, operand3:MLDSA_T1_BASE};
                //ExpandA(ρ) AND Aˆ NTT(s1)
                MLDSA_KG_S+ 44   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWM,  imm:'h0200, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_0_NTT_BASE, operand3:MLDSA_AS0_BASE};
                MLDSA_KG_S+ 45   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0201, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_1_NTT_BASE, operand3:MLDSA_AS0_BASE};
                MLDSA_KG_S+ 46   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0202, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_2_NTT_BASE, operand3:MLDSA_AS0_BASE};
                MLDSA_KG_S+ 47   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0203, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_3_NTT_BASE, operand3:MLDSA_AS0_BASE};
                MLDSA_KG_S+ 48   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0204, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_4_NTT_BASE, operand3:MLDSA_AS0_BASE};
                MLDSA_KG_S+ 49   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0205, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_5_NTT_BASE, operand3:MLDSA_AS0_BASE};
                MLDSA_KG_S+ 50   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0206, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_6_NTT_BASE, operand3:MLDSA_AS0_BASE};
                //NTT−1(Aˆ ◦NTT(s1))
                MLDSA_KG_S+ 51   : data_o_rom <= '{opcode:ABR_UOP_INTT, imm:'d01, length:'d00, operand1:MLDSA_AS0_BASE, operand2:MLDSA_TEMP2_BASE, operand3:MLDSA_AS0_INTT_BASE};
                //t ←NTT−1(Aˆ ◦NTT(s1))+s2
                MLDSA_KG_S+ 52   : data_o_rom <= '{opcode:ABR_UOP_PWA, imm:'d00, length:'d00, operand1:MLDSA_AS0_INTT_BASE, operand2:MLDSA_S2_2_BASE, operand3:MLDSA_T2_BASE};
                //ExpandA(ρ) AND Aˆ NTT(s1)
                MLDSA_KG_S+ 53   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWM,  imm:'h0300, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_0_NTT_BASE, operand3:MLDSA_AS0_BASE};
                MLDSA_KG_S+ 54   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0301, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_1_NTT_BASE, operand3:MLDSA_AS0_BASE};
                MLDSA_KG_S+ 55   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0302, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_2_NTT_BASE, operand3:MLDSA_AS0_BASE};
                MLDSA_KG_S+ 56   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0303, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_3_NTT_BASE, operand3:MLDSA_AS0_BASE};
                MLDSA_KG_S+ 57   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0304, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_4_NTT_BASE, operand3:MLDSA_AS0_BASE};
                MLDSA_KG_S+ 58   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0305, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_5_NTT_BASE, operand3:MLDSA_AS0_BASE};
                MLDSA_KG_S+ 59   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0306, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_6_NTT_BASE, operand3:MLDSA_AS0_BASE};
                //NTT−1(Aˆ ◦NTT(s1))
                MLDSA_KG_S+ 60   : data_o_rom <= '{opcode:ABR_UOP_INTT, imm:'d01, length:'d00, operand1:MLDSA_AS0_BASE, operand2:MLDSA_TEMP2_BASE, operand3:MLDSA_AS0_INTT_BASE};
                //t ←NTT−1(Aˆ ◦NTT(s1))+s2
                MLDSA_KG_S+ 61   : data_o_rom <= '{opcode:ABR_UOP_PWA, imm:'d00, length:'d00, operand1:MLDSA_AS0_INTT_BASE, operand2:MLDSA_S2_3_BASE, operand3:MLDSA_T3_BASE};
                //ExpandA(ρ) AND Aˆ NTT(s1)
                MLDSA_KG_S+ 62   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWM,  imm:'h0400, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_0_NTT_BASE, operand3:MLDSA_AS0_BASE};
                MLDSA_KG_S+ 63   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0401, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_1_NTT_BASE, operand3:MLDSA_AS0_BASE};
                MLDSA_KG_S+ 64   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0402, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_2_NTT_BASE, operand3:MLDSA_AS0_BASE};
                MLDSA_KG_S+ 65   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0403, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_3_NTT_BASE, operand3:MLDSA_AS0_BASE};
                MLDSA_KG_S+ 66   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0404, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_4_NTT_BASE, operand3:MLDSA_AS0_BASE};
                MLDSA_KG_S+ 67   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0405, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_5_NTT_BASE, operand3:MLDSA_AS0_BASE};
                MLDSA_KG_S+ 68   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0406, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_6_NTT_BASE, operand3:MLDSA_AS0_BASE};
                //NTT−1(Aˆ ◦NTT(s1))
                MLDSA_KG_S+ 69   : data_o_rom <= '{opcode:ABR_UOP_INTT, imm:'d01, length:'d00, operand1:MLDSA_AS0_BASE, operand2:MLDSA_TEMP2_BASE, operand3:MLDSA_AS0_INTT_BASE};
                //t ←NTT−1(Aˆ ◦NTT(s1))+s2
                MLDSA_KG_S+ 70   : data_o_rom <= '{opcode:ABR_UOP_PWA, imm:'d00, length:'d00, operand1:MLDSA_AS0_INTT_BASE, operand2:MLDSA_S2_4_BASE, operand3:MLDSA_T4_BASE};
                //ExpandA(ρ) AND Aˆ NTT(s1)
                MLDSA_KG_S+ 71   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWM,  imm:'h0500, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_0_NTT_BASE, operand3:MLDSA_AS0_BASE};
                MLDSA_KG_S+ 72   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0501, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_1_NTT_BASE, operand3:MLDSA_AS0_BASE};
                MLDSA_KG_S+ 73   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0502, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_2_NTT_BASE, operand3:MLDSA_AS0_BASE};
                MLDSA_KG_S+ 74   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0503, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_3_NTT_BASE, operand3:MLDSA_AS0_BASE};
                MLDSA_KG_S+ 75   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0504, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_4_NTT_BASE, operand3:MLDSA_AS0_BASE};
                MLDSA_KG_S+ 76   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0505, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_5_NTT_BASE, operand3:MLDSA_AS0_BASE};
                MLDSA_KG_S+ 77   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0506, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_6_NTT_BASE, operand3:MLDSA_AS0_BASE};
                //NTT−1(Aˆ ◦NTT(s1))
                MLDSA_KG_S+ 78   : data_o_rom <= '{opcode:ABR_UOP_INTT, imm:'d01, length:'d00, operand1:MLDSA_AS0_BASE, operand2:MLDSA_TEMP2_BASE, operand3:MLDSA_AS0_INTT_BASE};
                //t ←NTT−1(Aˆ ◦NTT(s1))+s2
                MLDSA_KG_S+ 79   : data_o_rom <= '{opcode:ABR_UOP_PWA, imm:'d00, length:'d00, operand1:MLDSA_AS0_INTT_BASE, operand2:MLDSA_S2_5_BASE, operand3:MLDSA_T5_BASE};
                //ExpandA(ρ) AND Aˆ NTT(s1)
                MLDSA_KG_S+ 80   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWM,  imm:'h0600, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_0_NTT_BASE, operand3:MLDSA_AS0_BASE};
                MLDSA_KG_S+ 81   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0601, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_1_NTT_BASE, operand3:MLDSA_AS0_BASE};
                MLDSA_KG_S+ 82   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0602, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_2_NTT_BASE, operand3:MLDSA_AS0_BASE};
                MLDSA_KG_S+ 83   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0603, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_3_NTT_BASE, operand3:MLDSA_AS0_BASE};
                MLDSA_KG_S+ 84   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0604, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_4_NTT_BASE, operand3:MLDSA_AS0_BASE};
                MLDSA_KG_S+ 85   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0605, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_5_NTT_BASE, operand3:MLDSA_AS0_BASE};
                MLDSA_KG_S+ 86   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0606, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_6_NTT_BASE, operand3:MLDSA_AS0_BASE};
                //NTT−1(Aˆ ◦NTT(s1))
                MLDSA_KG_S+ 87   : data_o_rom <= '{opcode:ABR_UOP_INTT, imm:'d01, length:'d00, operand1:MLDSA_AS0_BASE, operand2:MLDSA_TEMP2_BASE, operand3:MLDSA_AS0_INTT_BASE};
                //t ←NTT−1(Aˆ ◦NTT(s1))+s2
                MLDSA_KG_S+ 88   : data_o_rom <= '{opcode:ABR_UOP_PWA, imm:'d00, length:'d00, operand1:MLDSA_AS0_INTT_BASE, operand2:MLDSA_S2_6_BASE, operand3:MLDSA_T6_BASE};
                //ExpandA(ρ) AND Aˆ NTT(s1)
                MLDSA_KG_S+ 89   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWM,  imm:'h0700, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_0_NTT_BASE, operand3:MLDSA_AS0_BASE};
                MLDSA_KG_S+ 90   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0701, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_1_NTT_BASE, operand3:MLDSA_AS0_BASE};
                MLDSA_KG_S+ 91   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0702, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_2_NTT_BASE, operand3:MLDSA_AS0_BASE};
                MLDSA_KG_S+ 92   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0703, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_3_NTT_BASE, operand3:MLDSA_AS0_BASE};
                MLDSA_KG_S+ 93   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0704, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_4_NTT_BASE, operand3:MLDSA_AS0_BASE};
                MLDSA_KG_S+ 94   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0705, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_5_NTT_BASE, operand3:MLDSA_AS0_BASE};
                MLDSA_KG_S+ 95   : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0706, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_S1_6_NTT_BASE, operand3:MLDSA_AS0_BASE};
                //NTT−1(Aˆ ◦NTT(s1))
                MLDSA_KG_S+ 96   : data_o_rom <= '{opcode:ABR_UOP_INTT, imm:'d01, length:'d00, operand1:MLDSA_AS0_BASE, operand2:MLDSA_TEMP2_BASE, operand3:MLDSA_AS0_INTT_BASE};
                //t ←NTT−1(Aˆ ◦NTT(s1))+s2
                MLDSA_KG_S+ 97   : data_o_rom <= '{opcode:ABR_UOP_PWA, imm:'d00, length:'d00, operand1:MLDSA_AS0_INTT_BASE, operand2:MLDSA_S2_7_BASE, operand3:MLDSA_T7_BASE};
                //(t1,t0)←Power2Round(t,d) AND pk ←pkEncode(ρ,t1)
                MLDSA_KG_S+ 98   : data_o_rom <= '{opcode:ABR_UOP_PWR2RND, imm:'h0000, length:'d00, operand1:MLDSA_T0_BASE, operand2:ABR_NOP, operand3:MLDSA_SK_T0_OFFSET};
                //tr ←H(BytesToBits(pk),512)
                MLDSA_KG_S+ 99   : data_o_rom <= '{opcode:ABR_UOP_SHAKE256, imm:'h0000, length:PUBKEY_NUM_BYTES, operand1:MLDSA_PK_REG_ID, operand2:ABR_NOP, operand3:MLDSA_DEST_TR_REG_ID};
                //sk ←skEncode(ρ,K,tr,s1,s2,t0)
                MLDSA_KG_S+ 100  : data_o_rom <= '{opcode:ABR_UOP_SKENCODE, imm:'h0000, length:'d00, operand1:MLDSA_S1_0_BASE, operand2:ABR_NOP, operand3:ABR_NOP};
                MLDSA_KG_JUMP_SIGN : data_o_rom <= '{opcode:ABR_UOP_NOP, imm:'h0000, length:'d00, operand1:ABR_NOP, operand2:ABR_NOP, operand3:ABR_NOP};
                //KG end
                MLDSA_KG_E       : data_o_rom <= '{opcode:ABR_UOP_NOP, imm:'h0000, length:'d00, operand1:ABR_NOP, operand2:ABR_NOP, operand3:ABR_NOP};

                //rnd_seed=Keccak(entropy||counter)
                MLDSA_SIGN_S            : data_o_rom <= '{opcode:ABR_UOP_LD_SHAKE256, imm:'h0000, length:'d64, operand1:ABR_ENTROPY_ID, operand2:ABR_NOP, operand3:ABR_NOP};                
                MLDSA_SIGN_S+ 1         : data_o_rom <= '{opcode:ABR_UOP_SHAKE256,    imm:'h0000, length:'d08, operand1:ABR_CNT_ID,     operand2:ABR_NOP, operand3:ABR_DEST_LFSR_SEED_REG_ID};
                MLDSA_SIGN_S+ 2         : data_o_rom <= '{opcode:ABR_UOP_LFSR,        imm:'h0000, length:'d00, operand1:ABR_NOP,        operand2:ABR_NOP, operand3:ABR_NOP};
                MLDSA_SIGN_CHECK_MODE   : data_o_rom <= '{opcode:ABR_UOP_NOP, imm:'h0000, length:'d00, operand1:ABR_NOP, operand2:ABR_NOP, operand3:ABR_NOP};
                //μ ←H(tr||M,512)
                MLDSA_SIGN_H_MU         : data_o_rom <= '{opcode:ABR_UOP_LD_SHAKE256, imm:'h0000, length:'d64, operand1:MLDSA_TR_ID, operand2:ABR_NOP, operand3:ABR_NOP};
                MLDSA_SIGN_H_MU + 1     : data_o_rom <= '{opcode:ABR_UOP_SHAKE256, imm:'h0000, length:'d66, operand1:MLDSA_MSG_ID, operand2:ABR_NOP, operand3:MLDSA_DEST_MU_REG_ID};
                //ρ′=Keccak(K||rnd|| μ)
                MLDSA_SIGN_H_RHO_P      : data_o_rom <= '{opcode:ABR_UOP_LD_SHAKE256, imm:'h0000, length:'d32, operand1:MLDSA_K_ID, operand2:ABR_NOP, operand3:ABR_NOP};
                MLDSA_SIGN_H_RHO_P+ 1   : data_o_rom <= '{opcode:ABR_UOP_LD_SHAKE256, imm:'h0000, length:'d32, operand1:MLDSA_SIGN_RND_ID, operand2:ABR_NOP, operand3:ABR_NOP};
                MLDSA_SIGN_H_RHO_P+ 2   : data_o_rom <= '{opcode:ABR_UOP_SHAKE256, imm:'h0000, length:'d64, operand1:MLDSA_MU_ID, operand2:ABR_NOP, operand3:MLDSA_DEST_RHO_P_REG_ID};
       
                //Signing initial steps start
                MLDSA_SIGN_INIT_S   : data_o_rom <= '{opcode:ABR_UOP_SKDECODE, imm:'h0000, length:'d00, operand1:ABR_NOP, operand2:ABR_NOP, operand3:MLDSA_S1_0_BASE};
                //NTT(t0)
                MLDSA_SIGN_INIT_S+1 : data_o_rom <= '{opcode:ABR_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_T0_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_T0_BASE};
                MLDSA_SIGN_INIT_S+2 : data_o_rom <= '{opcode:ABR_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_T1_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_T1_BASE};
                MLDSA_SIGN_INIT_S+3 : data_o_rom <= '{opcode:ABR_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_T2_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_T2_BASE};
                MLDSA_SIGN_INIT_S+4 : data_o_rom <= '{opcode:ABR_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_T3_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_T3_BASE};
                MLDSA_SIGN_INIT_S+5 : data_o_rom <= '{opcode:ABR_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_T4_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_T4_BASE};
                MLDSA_SIGN_INIT_S+6 : data_o_rom <= '{opcode:ABR_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_T5_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_T5_BASE};
                MLDSA_SIGN_INIT_S+7 : data_o_rom <= '{opcode:ABR_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_T6_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_T6_BASE};
                MLDSA_SIGN_INIT_S+8 : data_o_rom <= '{opcode:ABR_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_T7_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_T7_BASE};
                //NTT(s1)
                MLDSA_SIGN_INIT_S+9 : data_o_rom <= '{opcode:ABR_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_S1_0_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_S1_0_BASE};
                MLDSA_SIGN_INIT_S+10 : data_o_rom <= '{opcode:ABR_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_S1_1_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_S1_1_BASE};
                MLDSA_SIGN_INIT_S+11: data_o_rom <= '{opcode:ABR_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_S1_2_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_S1_2_BASE};
                MLDSA_SIGN_INIT_S+12: data_o_rom <= '{opcode:ABR_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_S1_3_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_S1_3_BASE};
                MLDSA_SIGN_INIT_S+13: data_o_rom <= '{opcode:ABR_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_S1_4_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_S1_4_BASE};
                MLDSA_SIGN_INIT_S+14: data_o_rom <= '{opcode:ABR_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_S1_5_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_S1_5_BASE};
                MLDSA_SIGN_INIT_S+15: data_o_rom <= '{opcode:ABR_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_S1_6_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_S1_6_BASE};
                //NTT(s2)
                MLDSA_SIGN_INIT_S+16: data_o_rom <= '{opcode:ABR_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_S2_0_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_S2_0_BASE};
                MLDSA_SIGN_INIT_S+17: data_o_rom <= '{opcode:ABR_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_S2_1_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_S2_1_BASE};
                MLDSA_SIGN_INIT_S+18 : data_o_rom <= '{opcode:ABR_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_S2_2_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_S2_2_BASE};
                MLDSA_SIGN_INIT_S+19 : data_o_rom <= '{opcode:ABR_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_S2_3_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_S2_3_BASE};
                MLDSA_SIGN_INIT_S+20 : data_o_rom <= '{opcode:ABR_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_S2_4_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_S2_4_BASE};
                MLDSA_SIGN_INIT_S+21 : data_o_rom <= '{opcode:ABR_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_S2_5_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_S2_5_BASE};
                MLDSA_SIGN_INIT_S+22 : data_o_rom <= '{opcode:ABR_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_S2_6_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_S2_6_BASE};
                MLDSA_SIGN_INIT_S+23 : data_o_rom <= '{opcode:ABR_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_S2_7_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_S2_7_BASE};

                //lfsr_seed=Keccak(re_entropy||counter)
                MLDSA_SIGN_LFSR_S       : data_o_rom <= '{opcode:ABR_UOP_LD_SHAKE256, imm:'h0000, length:'d64, operand1:ABR_ENTROPY_ID, operand2:ABR_NOP, operand3:ABR_NOP};                
                MLDSA_SIGN_LFSR_S+ 1    : data_o_rom <= '{opcode:ABR_UOP_SHAKE256,    imm:'h0000, length:'d08, operand1:ABR_CNT_ID,     operand2:ABR_NOP, operand3:ABR_DEST_LFSR_SEED_REG_ID};
                MLDSA_SIGN_LFSR_S+ 2    : data_o_rom <= '{opcode:ABR_UOP_LFSR,        imm:'h0000, length:'d00, operand1:ABR_NOP,        operand2:ABR_NOP, operand3:ABR_NOP};
                //y=ExpandMask(ρ’ ,κ)
                MLDSA_SIGN_MAKE_Y_S     : data_o_rom <= '{opcode:ABR_UOP_EXP_MASK, imm:'h0000, length:'d66, operand1:MLDSA_RHO_P_KAPPA_ID, operand2:ABR_NOP, operand3:MLDSA_Y_0_BASE};
                MLDSA_SIGN_MAKE_Y_S+ 1  : data_o_rom <= '{opcode:ABR_UOP_EXP_MASK, imm:'h0001, length:'d66, operand1:MLDSA_RHO_P_KAPPA_ID, operand2:ABR_NOP, operand3:MLDSA_Y_1_BASE};
                MLDSA_SIGN_MAKE_Y_S+ 2  : data_o_rom <= '{opcode:ABR_UOP_EXP_MASK, imm:'h0002, length:'d66, operand1:MLDSA_RHO_P_KAPPA_ID, operand2:ABR_NOP, operand3:MLDSA_Y_2_BASE};
                MLDSA_SIGN_MAKE_Y_S+ 3  : data_o_rom <= '{opcode:ABR_UOP_EXP_MASK, imm:'h0003, length:'d66, operand1:MLDSA_RHO_P_KAPPA_ID, operand2:ABR_NOP, operand3:MLDSA_Y_3_BASE};
                MLDSA_SIGN_MAKE_Y_S+ 4  : data_o_rom <= '{opcode:ABR_UOP_EXP_MASK, imm:'h0004, length:'d66, operand1:MLDSA_RHO_P_KAPPA_ID, operand2:ABR_NOP, operand3:MLDSA_Y_4_BASE};
                MLDSA_SIGN_MAKE_Y_S+ 5  : data_o_rom <= '{opcode:ABR_UOP_EXP_MASK, imm:'h0005, length:'d66, operand1:MLDSA_RHO_P_KAPPA_ID, operand2:ABR_NOP, operand3:MLDSA_Y_5_BASE};
                MLDSA_SIGN_MAKE_Y_S+ 6  : data_o_rom <= '{opcode:ABR_UOP_EXP_MASK, imm:'h0006, length:'d66, operand1:MLDSA_RHO_P_KAPPA_ID, operand2:ABR_NOP, operand3:MLDSA_Y_6_BASE};
                //NTT(Y)
                MLDSA_SIGN_MAKE_Y_S+ 7  : data_o_rom <= '{opcode:ABR_UOP_NTT,  imm:'h0001, length:'d00, operand1:MLDSA_Y_0_BASE, operand2:MLDSA_TEMP2_BASE, operand3:MLDSA_Y_0_NTT_BASE};
                MLDSA_SIGN_MAKE_Y_S+ 8  : data_o_rom <= '{opcode:ABR_UOP_NTT,  imm:'h0001, length:'d00, operand1:MLDSA_Y_1_BASE, operand2:MLDSA_TEMP2_BASE, operand3:MLDSA_Y_1_NTT_BASE};
                MLDSA_SIGN_MAKE_Y_S+ 9  : data_o_rom <= '{opcode:ABR_UOP_NTT,  imm:'h0001, length:'d00, operand1:MLDSA_Y_2_BASE, operand2:MLDSA_TEMP2_BASE, operand3:MLDSA_Y_2_NTT_BASE};
                MLDSA_SIGN_MAKE_Y_S+ 10 : data_o_rom <= '{opcode:ABR_UOP_NTT,  imm:'h0001, length:'d00, operand1:MLDSA_Y_3_BASE, operand2:MLDSA_TEMP2_BASE, operand3:MLDSA_Y_3_NTT_BASE};
                MLDSA_SIGN_MAKE_Y_S+ 11 : data_o_rom <= '{opcode:ABR_UOP_NTT,  imm:'h0001, length:'d00, operand1:MLDSA_Y_4_BASE, operand2:MLDSA_TEMP2_BASE, operand3:MLDSA_Y_4_NTT_BASE};
                MLDSA_SIGN_MAKE_Y_S+ 12 : data_o_rom <= '{opcode:ABR_UOP_NTT,  imm:'h0001, length:'d00, operand1:MLDSA_Y_5_BASE, operand2:MLDSA_TEMP2_BASE, operand3:MLDSA_Y_5_NTT_BASE};
                MLDSA_SIGN_MAKE_Y_S+ 13 : data_o_rom <= '{opcode:ABR_UOP_NTT,  imm:'h0001, length:'d00, operand1:MLDSA_Y_6_BASE, operand2:MLDSA_TEMP2_BASE, operand3:MLDSA_Y_6_NTT_BASE};
                //Aˆ ←ExpandA(ρ) AND Aˆ ◦NTT(y)
                MLDSA_SIGN_MAKE_W_S     : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWM,  imm:'h0000, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_0_NTT_BASE, operand3:MLDSA_AY0_BASE};
                MLDSA_SIGN_MAKE_W_S+ 1  : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWMA, imm:'h0001, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_1_NTT_BASE, operand3:MLDSA_AY0_BASE};
                MLDSA_SIGN_MAKE_W_S+ 2  : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWMA, imm:'h0002, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_2_NTT_BASE, operand3:MLDSA_AY0_BASE};
                MLDSA_SIGN_MAKE_W_S+ 3  : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWMA, imm:'h0003, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_3_NTT_BASE, operand3:MLDSA_AY0_BASE};
                MLDSA_SIGN_MAKE_W_S+ 4  : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWMA, imm:'h0004, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_4_NTT_BASE, operand3:MLDSA_AY0_BASE};
                MLDSA_SIGN_MAKE_W_S+ 5  : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWMA, imm:'h0005, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_5_NTT_BASE, operand3:MLDSA_AY0_BASE};
                MLDSA_SIGN_MAKE_W_S+ 6  : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWMA, imm:'h0006, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_6_NTT_BASE, operand3:MLDSA_AY0_BASE};

                MLDSA_SIGN_MAKE_W_S+ 7  : data_o_rom <= '{opcode:ABR_UOP_MASKED_INTT,  imm:'h0001, length:'d00, operand1:MLDSA_AY0_BASE, operand2:MLDSA_TEMP2_BASE, operand3:MLDSA_W0_0_BASE};

                MLDSA_SIGN_MAKE_W_S+ 8  : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWM,  imm:'h0100, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_0_NTT_BASE, operand3:MLDSA_AY0_BASE};
                MLDSA_SIGN_MAKE_W_S+ 9  : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWMA, imm:'h0101, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_1_NTT_BASE, operand3:MLDSA_AY0_BASE};
                MLDSA_SIGN_MAKE_W_S+ 10 : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWMA, imm:'h0102, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_2_NTT_BASE, operand3:MLDSA_AY0_BASE};
                MLDSA_SIGN_MAKE_W_S+ 11 : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWMA, imm:'h0103, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_3_NTT_BASE, operand3:MLDSA_AY0_BASE};
                MLDSA_SIGN_MAKE_W_S+ 12 : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWMA, imm:'h0104, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_4_NTT_BASE, operand3:MLDSA_AY0_BASE};
                MLDSA_SIGN_MAKE_W_S+ 13 : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWMA, imm:'h0105, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_5_NTT_BASE, operand3:MLDSA_AY0_BASE};
                MLDSA_SIGN_MAKE_W_S+ 14 : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWMA, imm:'h0106, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_6_NTT_BASE, operand3:MLDSA_AY0_BASE};

                MLDSA_SIGN_MAKE_W_S+ 15 : data_o_rom <= '{opcode:ABR_UOP_MASKED_INTT,  imm:'h0001, length:'d00, operand1:MLDSA_AY0_BASE, operand2:MLDSA_TEMP2_BASE, operand3:MLDSA_W0_1_BASE};
                
                MLDSA_SIGN_MAKE_W_S+ 16 : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWM,  imm:'h0200, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_0_NTT_BASE, operand3:MLDSA_AY0_BASE};
                MLDSA_SIGN_MAKE_W_S+ 17 : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWMA, imm:'h0201, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_1_NTT_BASE, operand3:MLDSA_AY0_BASE};
                MLDSA_SIGN_MAKE_W_S+ 18 : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWMA, imm:'h0202, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_2_NTT_BASE, operand3:MLDSA_AY0_BASE};
                MLDSA_SIGN_MAKE_W_S+ 19 : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWMA, imm:'h0203, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_3_NTT_BASE, operand3:MLDSA_AY0_BASE};
                MLDSA_SIGN_MAKE_W_S+ 20 : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWMA, imm:'h0204, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_4_NTT_BASE, operand3:MLDSA_AY0_BASE};
                MLDSA_SIGN_MAKE_W_S+ 21 : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWMA, imm:'h0205, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_5_NTT_BASE, operand3:MLDSA_AY0_BASE};
                MLDSA_SIGN_MAKE_W_S+ 22 : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWMA, imm:'h0206, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_6_NTT_BASE, operand3:MLDSA_AY0_BASE};

                MLDSA_SIGN_MAKE_W_S+ 23 : data_o_rom <= '{opcode:ABR_UOP_MASKED_INTT,  imm:'h0001, length:'d00, operand1:MLDSA_AY0_BASE, operand2:MLDSA_TEMP2_BASE, operand3:MLDSA_W0_2_BASE};

                MLDSA_SIGN_MAKE_W_S+ 24 : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWM,  imm:'h0300, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_0_NTT_BASE, operand3:MLDSA_AY0_BASE};
                MLDSA_SIGN_MAKE_W_S+ 25 : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWMA, imm:'h0301, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_1_NTT_BASE, operand3:MLDSA_AY0_BASE};
                MLDSA_SIGN_MAKE_W_S+ 26 : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWMA, imm:'h0302, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_2_NTT_BASE, operand3:MLDSA_AY0_BASE};
                MLDSA_SIGN_MAKE_W_S+ 27 : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWMA, imm:'h0303, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_3_NTT_BASE, operand3:MLDSA_AY0_BASE};
                MLDSA_SIGN_MAKE_W_S+ 28 : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWMA, imm:'h0304, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_4_NTT_BASE, operand3:MLDSA_AY0_BASE};
                MLDSA_SIGN_MAKE_W_S+ 29 : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWMA, imm:'h0305, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_5_NTT_BASE, operand3:MLDSA_AY0_BASE};
                MLDSA_SIGN_MAKE_W_S+ 30 : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWMA, imm:'h0306, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_6_NTT_BASE, operand3:MLDSA_AY0_BASE};

                MLDSA_SIGN_MAKE_W_S+ 31 : data_o_rom <= '{opcode:ABR_UOP_MASKED_INTT,  imm:'h0001, length:'d00, operand1:MLDSA_AY0_BASE, operand2:MLDSA_TEMP2_BASE, operand3:MLDSA_W0_3_BASE};

                MLDSA_SIGN_MAKE_W_S+ 32 : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWM,  imm:'h0400, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_0_NTT_BASE, operand3:MLDSA_AY0_BASE};
                MLDSA_SIGN_MAKE_W_S+ 33 : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWMA, imm:'h0401, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_1_NTT_BASE, operand3:MLDSA_AY0_BASE};
                MLDSA_SIGN_MAKE_W_S+ 34 : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWMA, imm:'h0402, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_2_NTT_BASE, operand3:MLDSA_AY0_BASE};
                MLDSA_SIGN_MAKE_W_S+ 35 : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWMA, imm:'h0403, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_3_NTT_BASE, operand3:MLDSA_AY0_BASE};
                MLDSA_SIGN_MAKE_W_S+ 36 : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWMA, imm:'h0404, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_4_NTT_BASE, operand3:MLDSA_AY0_BASE};
                MLDSA_SIGN_MAKE_W_S+ 37 : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWMA, imm:'h0405, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_5_NTT_BASE, operand3:MLDSA_AY0_BASE};
                MLDSA_SIGN_MAKE_W_S+ 38 : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWMA, imm:'h0406, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_6_NTT_BASE, operand3:MLDSA_AY0_BASE};

                MLDSA_SIGN_MAKE_W_S+ 39 : data_o_rom <= '{opcode:ABR_UOP_MASKED_INTT,  imm:'h0001, length:'d00, operand1:MLDSA_AY0_BASE, operand2:MLDSA_TEMP2_BASE, operand3:MLDSA_W0_4_BASE};
    
                MLDSA_SIGN_MAKE_W_S+ 40 : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWM,  imm:'h0500, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_0_NTT_BASE, operand3:MLDSA_AY0_BASE};
                MLDSA_SIGN_MAKE_W_S+ 41 : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWMA, imm:'h0501, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_1_NTT_BASE, operand3:MLDSA_AY0_BASE};
                MLDSA_SIGN_MAKE_W_S+ 42 : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWMA, imm:'h0502, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_2_NTT_BASE, operand3:MLDSA_AY0_BASE};
                MLDSA_SIGN_MAKE_W_S+ 43 : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWMA, imm:'h0503, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_3_NTT_BASE, operand3:MLDSA_AY0_BASE};
                MLDSA_SIGN_MAKE_W_S+ 44 : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWMA, imm:'h0504, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_4_NTT_BASE, operand3:MLDSA_AY0_BASE};
                MLDSA_SIGN_MAKE_W_S+ 45 : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWMA, imm:'h0505, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_5_NTT_BASE, operand3:MLDSA_AY0_BASE};
                MLDSA_SIGN_MAKE_W_S+ 46 : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWMA, imm:'h0506, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_6_NTT_BASE, operand3:MLDSA_AY0_BASE};

                MLDSA_SIGN_MAKE_W_S+ 47 : data_o_rom <= '{opcode:ABR_UOP_MASKED_INTT,  imm:'h0001, length:'d00, operand1:MLDSA_AY0_BASE, operand2:MLDSA_TEMP2_BASE, operand3:MLDSA_W0_5_BASE};
                
                MLDSA_SIGN_MAKE_W_S+ 48 : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWM,  imm:'h0600, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_0_NTT_BASE, operand3:MLDSA_AY0_BASE};
                MLDSA_SIGN_MAKE_W_S+ 49 : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWMA, imm:'h0601, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_1_NTT_BASE, operand3:MLDSA_AY0_BASE};
                MLDSA_SIGN_MAKE_W_S+ 50 : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWMA, imm:'h0602, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_2_NTT_BASE, operand3:MLDSA_AY0_BASE};
                MLDSA_SIGN_MAKE_W_S+ 51 : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWMA, imm:'h0603, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_3_NTT_BASE, operand3:MLDSA_AY0_BASE};
                MLDSA_SIGN_MAKE_W_S+ 52 : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWMA, imm:'h0604, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_4_NTT_BASE, operand3:MLDSA_AY0_BASE};
                MLDSA_SIGN_MAKE_W_S+ 53 : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWMA, imm:'h0605, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_5_NTT_BASE, operand3:MLDSA_AY0_BASE};
                MLDSA_SIGN_MAKE_W_S+ 54 : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWMA, imm:'h0606, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_6_NTT_BASE, operand3:MLDSA_AY0_BASE};

                MLDSA_SIGN_MAKE_W_S+ 55 : data_o_rom <= '{opcode:ABR_UOP_MASKED_INTT,  imm:'h0001, length:'d00, operand1:MLDSA_AY0_BASE, operand2:MLDSA_TEMP2_BASE, operand3:MLDSA_W0_6_BASE};
                
                MLDSA_SIGN_MAKE_W_S+ 56 : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWM,  imm:'h0700, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_0_NTT_BASE, operand3:MLDSA_AY0_BASE};
                MLDSA_SIGN_MAKE_W_S+ 57 : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWMA, imm:'h0701, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_1_NTT_BASE, operand3:MLDSA_AY0_BASE};
                MLDSA_SIGN_MAKE_W_S+ 58 : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWMA, imm:'h0702, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_2_NTT_BASE, operand3:MLDSA_AY0_BASE};
                MLDSA_SIGN_MAKE_W_S+ 59 : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWMA, imm:'h0703, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_3_NTT_BASE, operand3:MLDSA_AY0_BASE};
                MLDSA_SIGN_MAKE_W_S+ 60 : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWMA, imm:'h0704, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_4_NTT_BASE, operand3:MLDSA_AY0_BASE};
                MLDSA_SIGN_MAKE_W_S+ 61 : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWMA, imm:'h0705, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_5_NTT_BASE, operand3:MLDSA_AY0_BASE};
                MLDSA_SIGN_MAKE_W_S+ 62 : data_o_rom <= '{opcode:ABR_UOP_REJS_MASKED_PWMA, imm:'h0706, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Y_6_NTT_BASE, operand3:MLDSA_AY0_BASE};

                MLDSA_SIGN_MAKE_W_S+ 63 : data_o_rom <= '{opcode:ABR_UOP_MASKED_INTT,  imm:'h0001, length:'d00, operand1:MLDSA_AY0_BASE, operand2:MLDSA_TEMP2_BASE, operand3:MLDSA_W0_7_BASE};

                //(w1,w0) ←Decompose(w) AND c˜←H(μ||w1Encode(w1),2λ)
                MLDSA_SIGN_MAKE_W_S+ 64 : data_o_rom <= '{opcode:ABR_UOP_LD_SHAKE256, imm:'h0000, length:'d64, operand1:MLDSA_MU_ID, operand2:ABR_NOP, operand3:ABR_NOP};
                MLDSA_SIGN_MAKE_W       : data_o_rom <= '{opcode:ABR_UOP_DECOMPOSE, imm:'h0000, length:'d00, operand1:MLDSA_W0_0_BASE, operand2:ABR_NOP, operand3:MLDSA_W0_0_BASE}; 

                MLDSA_SIGN_MAKE_C       : data_o_rom <= '{opcode:ABR_UOP_RUN_SHAKE256, imm:'h0000, length:'d00, operand1:ABR_NOP, operand2:ABR_NOP, operand3:MLDSA_DEST_SIG_C_REG_ID};
                MLDSA_SIGN_MAKE_C+ 1    : data_o_rom <= '{opcode:ABR_UOP_SIB, imm:'h0000, length:'d64, operand1:MLDSA_SIG_C_REG_ID, operand2:ABR_NOP, operand3:ABR_NOP};

                //NTT(C)
                MLDSA_SIGN_VALID_S     : data_o_rom <= '{opcode:ABR_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_C_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_C_NTT_BASE};

                //Compute Z and perform norm check
                MLDSA_SIGN_VALID_S+1   : data_o_rom <= '{opcode:ABR_UOP_MASKED_PWM, imm:'h0000, length:'d00, operand1:MLDSA_C_NTT_BASE, operand2:MLDSA_S1_0_BASE, operand3:MLDSA_CS_NTT_BASE};
                MLDSA_SIGN_VALID_S+2   : data_o_rom <= '{opcode:ABR_UOP_MASKED_INTT, imm:'h0000, length:'d00, operand1:MLDSA_CS_NTT_BASE, operand2:MLDSA_TEMP2_BASE, operand3:MLDSA_CS1_BASE};
                MLDSA_SIGN_VALID_S+3   : data_o_rom <= '{opcode:ABR_UOP_PWA, imm:'h0000, length:'d00, operand1:MLDSA_Y_0_BASE, operand2:MLDSA_CS1_BASE, operand3:MLDSA_Z_BASE};
                MLDSA_SIGN_VALID_S+4   : data_o_rom <= '{opcode:ABR_UOP_NORMCHK, imm:MLDSA_NORMCHK_Z, length:'d00, operand1:MLDSA_Z_BASE, operand2:ABR_NOP, operand3:ABR_NOP};
                MLDSA_SIGN_VALID_S+5   : data_o_rom <= '{opcode:ABR_UOP_SIGENCODE, imm:'h0000, length:'d00, operand1:MLDSA_Z_BASE, operand2:ABR_NOP, operand3:15'h000};

                MLDSA_SIGN_VALID_S+6   : data_o_rom <= '{opcode:ABR_UOP_MASKED_PWM, imm:'h0000, length:'d00, operand1:MLDSA_C_NTT_BASE, operand2:MLDSA_S1_1_BASE, operand3:MLDSA_CS_NTT_BASE};
                MLDSA_SIGN_VALID_S+7   : data_o_rom <= '{opcode:ABR_UOP_MASKED_INTT, imm:'h0000, length:'d00, operand1:MLDSA_CS_NTT_BASE, operand2:MLDSA_TEMP2_BASE, operand3:MLDSA_CS1_BASE};
                MLDSA_SIGN_VALID_S+8   : data_o_rom <= '{opcode:ABR_UOP_PWA, imm:'h0000, length:'d00, operand1:MLDSA_Y_1_BASE, operand2:MLDSA_CS1_BASE, operand3:MLDSA_Z_BASE};
                MLDSA_SIGN_VALID_S+9   : data_o_rom <= '{opcode:ABR_UOP_NORMCHK, imm:MLDSA_NORMCHK_Z, length:'d00, operand1:MLDSA_Z_BASE, operand2:ABR_NOP, operand3:ABR_NOP};
                MLDSA_SIGN_VALID_S+10  : data_o_rom <= '{opcode:ABR_UOP_SIGENCODE, imm:'h0000, length:'d00, operand1:MLDSA_Z_BASE, operand2:ABR_NOP, operand3:15'h040};

                MLDSA_SIGN_VALID_S+11  : data_o_rom <= '{opcode:ABR_UOP_MASKED_PWM, imm:'h0000, length:'d00, operand1:MLDSA_C_NTT_BASE, operand2:MLDSA_S1_2_BASE, operand3:MLDSA_CS_NTT_BASE};
                MLDSA_SIGN_VALID_S+12  : data_o_rom <= '{opcode:ABR_UOP_MASKED_INTT, imm:'h0000, length:'d00, operand1:MLDSA_CS_NTT_BASE, operand2:MLDSA_TEMP2_BASE, operand3:MLDSA_CS1_BASE};
                MLDSA_SIGN_VALID_S+13  : data_o_rom <= '{opcode:ABR_UOP_PWA, imm:'h0000, length:'d00, operand1:MLDSA_Y_2_BASE, operand2:MLDSA_CS1_BASE, operand3:MLDSA_Z_BASE};
                MLDSA_SIGN_VALID_S+14  : data_o_rom <= '{opcode:ABR_UOP_NORMCHK, imm:MLDSA_NORMCHK_Z, length:'d00, operand1:MLDSA_Z_BASE, operand2:ABR_NOP, operand3:ABR_NOP};
                MLDSA_SIGN_VALID_S+15  : data_o_rom <= '{opcode:ABR_UOP_SIGENCODE, imm:'h0000, length:'d00, operand1:MLDSA_Z_BASE, operand2:ABR_NOP, operand3:15'h080};

                MLDSA_SIGN_VALID_S+16  : data_o_rom <= '{opcode:ABR_UOP_MASKED_PWM, imm:'h0000, length:'d00, operand1:MLDSA_C_NTT_BASE, operand2:MLDSA_S1_3_BASE, operand3:MLDSA_CS_NTT_BASE};
                MLDSA_SIGN_VALID_S+17  : data_o_rom <= '{opcode:ABR_UOP_MASKED_INTT, imm:'h0000, length:'d00, operand1:MLDSA_CS_NTT_BASE, operand2:MLDSA_TEMP2_BASE, operand3:MLDSA_CS1_BASE};
                MLDSA_SIGN_VALID_S+18  : data_o_rom <= '{opcode:ABR_UOP_PWA, imm:'h0000, length:'d00, operand1:MLDSA_Y_3_BASE, operand2:MLDSA_CS1_BASE, operand3:MLDSA_Z_BASE};
                MLDSA_SIGN_VALID_S+19  : data_o_rom <= '{opcode:ABR_UOP_NORMCHK, imm:MLDSA_NORMCHK_Z, length:'d00, operand1:MLDSA_Z_BASE, operand2:ABR_NOP, operand3:ABR_NOP};
                MLDSA_SIGN_VALID_S+20  : data_o_rom <= '{opcode:ABR_UOP_SIGENCODE, imm:'h0000, length:'d00, operand1:MLDSA_Z_BASE, operand2:ABR_NOP, operand3:15'h0C0};

                MLDSA_SIGN_VALID_S+21  : data_o_rom <= '{opcode:ABR_UOP_MASKED_PWM, imm:'h0000, length:'d00, operand1:MLDSA_C_NTT_BASE, operand2:MLDSA_S1_4_BASE, operand3:MLDSA_CS_NTT_BASE};
                MLDSA_SIGN_VALID_S+22  : data_o_rom <= '{opcode:ABR_UOP_MASKED_INTT, imm:'h0000, length:'d00, operand1:MLDSA_CS_NTT_BASE, operand2:MLDSA_TEMP2_BASE, operand3:MLDSA_CS1_BASE};
                MLDSA_SIGN_VALID_S+23  : data_o_rom <= '{opcode:ABR_UOP_PWA, imm:'h0000, length:'d00, operand1:MLDSA_Y_4_BASE, operand2:MLDSA_CS1_BASE, operand3:MLDSA_Z_BASE};
                MLDSA_SIGN_VALID_S+24  : data_o_rom <= '{opcode:ABR_UOP_NORMCHK, imm:MLDSA_NORMCHK_Z, length:'d00, operand1:MLDSA_Z_BASE, operand2:ABR_NOP, operand3:ABR_NOP};
                MLDSA_SIGN_VALID_S+25  : data_o_rom <= '{opcode:ABR_UOP_SIGENCODE, imm:'h0000, length:'d00, operand1:MLDSA_Z_BASE, operand2:ABR_NOP, operand3:15'h100};

                MLDSA_SIGN_VALID_S+26  : data_o_rom <= '{opcode:ABR_UOP_MASKED_PWM, imm:'h0000, length:'d00, operand1:MLDSA_C_NTT_BASE, operand2:MLDSA_S1_5_BASE, operand3:MLDSA_CS_NTT_BASE};
                MLDSA_SIGN_VALID_S+27  : data_o_rom <= '{opcode:ABR_UOP_MASKED_INTT, imm:'h0000, length:'d00, operand1:MLDSA_CS_NTT_BASE, operand2:MLDSA_TEMP2_BASE, operand3:MLDSA_CS1_BASE};
                MLDSA_SIGN_VALID_S+28  : data_o_rom <= '{opcode:ABR_UOP_PWA, imm:'h0000, length:'d00, operand1:MLDSA_Y_5_BASE, operand2:MLDSA_CS1_BASE, operand3:MLDSA_Z_BASE};
                MLDSA_SIGN_VALID_S+29  : data_o_rom <= '{opcode:ABR_UOP_NORMCHK, imm:MLDSA_NORMCHK_Z, length:'d00, operand1:MLDSA_Z_BASE, operand2:ABR_NOP, operand3:ABR_NOP};
                MLDSA_SIGN_VALID_S+30  : data_o_rom <= '{opcode:ABR_UOP_SIGENCODE, imm:'h0000, length:'d00, operand1:MLDSA_Z_BASE, operand2:ABR_NOP, operand3:15'h140};

                MLDSA_SIGN_VALID_S+31  : data_o_rom <= '{opcode:ABR_UOP_MASKED_PWM, imm:'h0000, length:'d00, operand1:MLDSA_C_NTT_BASE, operand2:MLDSA_S1_6_BASE, operand3:MLDSA_CS_NTT_BASE};
                MLDSA_SIGN_VALID_S+32  : data_o_rom <= '{opcode:ABR_UOP_MASKED_INTT, imm:'h0000, length:'d00, operand1:MLDSA_CS_NTT_BASE, operand2:MLDSA_TEMP2_BASE, operand3:MLDSA_CS1_BASE};
                MLDSA_SIGN_VALID_S+33  : data_o_rom <= '{opcode:ABR_UOP_PWA, imm:'h0000, length:'d00, operand1:MLDSA_Y_6_BASE, operand2:MLDSA_CS1_BASE, operand3:MLDSA_Z_BASE};
                MLDSA_SIGN_VALID_S+34  : data_o_rom <= '{opcode:ABR_UOP_NORMCHK, imm:MLDSA_NORMCHK_Z, length:'d00, operand1:MLDSA_Z_BASE, operand2:ABR_NOP, operand3:ABR_NOP};
                MLDSA_SIGN_VALID_S+35  : data_o_rom <= '{opcode:ABR_UOP_SIGENCODE, imm:'h0000, length:'d00, operand1:MLDSA_Z_BASE, operand2:ABR_NOP, operand3:15'h180};

                MLDSA_SIGN_VALID_S+36 : data_o_rom <= '{opcode:ABR_UOP_MASKED_PWM, imm:'h0000, length:'d00, operand1:MLDSA_C_NTT_BASE, operand2:MLDSA_T0_BASE, operand3:MLDSA_CT_NTT_BASE};
                MLDSA_SIGN_VALID_S+37 : data_o_rom <= '{opcode:ABR_UOP_MASKED_INTT, imm:'h0000, length:'d00, operand1:MLDSA_CT_NTT_BASE, operand2:MLDSA_TEMP2_BASE, operand3:MLDSA_CT_0_BASE};
                MLDSA_SIGN_VALID_S+38 : data_o_rom <= '{opcode:ABR_UOP_MASKED_PWM, imm:'h0000, length:'d00, operand1:MLDSA_C_NTT_BASE, operand2:MLDSA_T1_BASE, operand3:MLDSA_CT_NTT_BASE};
                MLDSA_SIGN_VALID_S+39 : data_o_rom <= '{opcode:ABR_UOP_MASKED_INTT, imm:'h0000, length:'d00, operand1:MLDSA_CT_NTT_BASE, operand2:MLDSA_TEMP2_BASE, operand3:MLDSA_CT_1_BASE};
                MLDSA_SIGN_VALID_S+40 : data_o_rom <= '{opcode:ABR_UOP_MASKED_PWM, imm:'h0000, length:'d00, operand1:MLDSA_C_NTT_BASE, operand2:MLDSA_T2_BASE, operand3:MLDSA_CT_NTT_BASE};
                MLDSA_SIGN_VALID_S+41 : data_o_rom <= '{opcode:ABR_UOP_MASKED_INTT, imm:'h0000, length:'d00, operand1:MLDSA_CT_NTT_BASE, operand2:MLDSA_TEMP2_BASE, operand3:MLDSA_CT_2_BASE};
                MLDSA_SIGN_VALID_S+42 : data_o_rom <= '{opcode:ABR_UOP_MASKED_PWM, imm:'h0000, length:'d00, operand1:MLDSA_C_NTT_BASE, operand2:MLDSA_T3_BASE, operand3:MLDSA_CT_NTT_BASE};
                MLDSA_SIGN_VALID_S+43 : data_o_rom <= '{opcode:ABR_UOP_MASKED_INTT, imm:'h0000, length:'d00, operand1:MLDSA_CT_NTT_BASE, operand2:MLDSA_TEMP2_BASE, operand3:MLDSA_CT_3_BASE};
                MLDSA_SIGN_VALID_S+44 : data_o_rom <= '{opcode:ABR_UOP_MASKED_PWM, imm:'h0000, length:'d00, operand1:MLDSA_C_NTT_BASE, operand2:MLDSA_T4_BASE, operand3:MLDSA_CT_NTT_BASE};
                MLDSA_SIGN_VALID_S+45 : data_o_rom <= '{opcode:ABR_UOP_MASKED_INTT, imm:'h0000, length:'d00, operand1:MLDSA_CT_NTT_BASE, operand2:MLDSA_TEMP2_BASE, operand3:MLDSA_CT_4_BASE};
                MLDSA_SIGN_VALID_S+46 : data_o_rom <= '{opcode:ABR_UOP_MASKED_PWM, imm:'h0000, length:'d00, operand1:MLDSA_C_NTT_BASE, operand2:MLDSA_T5_BASE, operand3:MLDSA_CT_NTT_BASE};
                MLDSA_SIGN_VALID_S+47 : data_o_rom <= '{opcode:ABR_UOP_MASKED_INTT, imm:'h0000, length:'d00, operand1:MLDSA_CT_NTT_BASE, operand2:MLDSA_TEMP2_BASE, operand3:MLDSA_CT_5_BASE};
                MLDSA_SIGN_VALID_S+48 : data_o_rom <= '{opcode:ABR_UOP_MASKED_PWM, imm:'h0000, length:'d00, operand1:MLDSA_C_NTT_BASE, operand2:MLDSA_T6_BASE, operand3:MLDSA_CT_NTT_BASE};
                MLDSA_SIGN_VALID_S+49 : data_o_rom <= '{opcode:ABR_UOP_MASKED_INTT, imm:'h0000, length:'d00, operand1:MLDSA_CT_NTT_BASE, operand2:MLDSA_TEMP2_BASE, operand3:MLDSA_CT_6_BASE};
                MLDSA_SIGN_VALID_S+50 : data_o_rom <= '{opcode:ABR_UOP_MASKED_PWM, imm:'h0000, length:'d00, operand1:MLDSA_C_NTT_BASE, operand2:MLDSA_T7_BASE, operand3:MLDSA_CT_NTT_BASE};
                MLDSA_SIGN_VALID_S+51 : data_o_rom <= '{opcode:ABR_UOP_MASKED_INTT, imm:'h0000, length:'d00, operand1:MLDSA_CT_NTT_BASE, operand2:MLDSA_TEMP2_BASE, operand3:MLDSA_CT_7_BASE};

                //Make R0, CT0 and Hint_r
                MLDSA_SIGN_VALID_S+52 : data_o_rom <= '{opcode:ABR_UOP_MASKED_PWM, imm:'h0000, length:'d00, operand1:MLDSA_C_NTT_BASE, operand2:MLDSA_S2_0_BASE, operand3:MLDSA_CS_NTT_BASE};
                MLDSA_SIGN_VALID_S+53 : data_o_rom <= '{opcode:ABR_UOP_MASKED_INTT, imm:'h0000, length:'d00, operand1:MLDSA_CS_NTT_BASE, operand2:MLDSA_TEMP2_BASE, operand3:MLDSA_CS2_BASE};
                MLDSA_SIGN_VALID_S+54 : data_o_rom <= '{opcode:ABR_UOP_PWS, imm:'h0000, length:'d00, operand1:MLDSA_CS2_BASE, operand2:MLDSA_W0_0_BASE, operand3:MLDSA_R0_BASE};
                MLDSA_SIGN_VALID_S+55 : data_o_rom <= '{opcode:ABR_UOP_NORMCHK, imm:MLDSA_NORMCHK_R0, length:'d00, operand1:MLDSA_R0_BASE, operand2:ABR_NOP, operand3:ABR_NOP};
                MLDSA_SIGN_VALID_S+56 : data_o_rom <= '{opcode:ABR_UOP_NORMCHK, imm:MLDSA_NORMCHK_CT0, length:'d00, operand1:MLDSA_CT_0_BASE, operand2:ABR_NOP, operand3:ABR_NOP};
                MLDSA_SIGN_VALID_S+57 : data_o_rom <= '{opcode:ABR_UOP_PWA, imm:'h0000, length:'d00, operand1:MLDSA_R0_BASE, operand2:MLDSA_CT_0_BASE, operand3:MLDSA_HINT_R_0_BASE};

                MLDSA_SIGN_VALID_S+58 : data_o_rom <= '{opcode:ABR_UOP_MASKED_PWM, imm:'h0000, length:'d00, operand1:MLDSA_C_NTT_BASE, operand2:MLDSA_S2_1_BASE, operand3:MLDSA_CS_NTT_BASE};
                MLDSA_SIGN_VALID_S+59 : data_o_rom <= '{opcode:ABR_UOP_MASKED_INTT, imm:'h0000, length:'d00, operand1:MLDSA_CS_NTT_BASE, operand2:MLDSA_TEMP2_BASE, operand3:MLDSA_CS2_BASE};
                MLDSA_SIGN_VALID_S+60 : data_o_rom <= '{opcode:ABR_UOP_PWS, imm:'h0000, length:'d00, operand1:MLDSA_CS2_BASE, operand2:MLDSA_W0_1_BASE, operand3:MLDSA_R0_BASE};
                MLDSA_SIGN_VALID_S+61 : data_o_rom <= '{opcode:ABR_UOP_NORMCHK, imm:MLDSA_NORMCHK_R0, length:'d00, operand1:MLDSA_R0_BASE, operand2:ABR_NOP, operand3:ABR_NOP};
                MLDSA_SIGN_VALID_S+62 : data_o_rom <= '{opcode:ABR_UOP_NORMCHK, imm:MLDSA_NORMCHK_CT0, length:'d00, operand1:MLDSA_CT_1_BASE, operand2:ABR_NOP, operand3:ABR_NOP};
                MLDSA_SIGN_VALID_S+63 : data_o_rom <= '{opcode:ABR_UOP_PWA, imm:'h0000, length:'d00, operand1:MLDSA_R0_BASE, operand2:MLDSA_CT_1_BASE, operand3:MLDSA_HINT_R_1_BASE};

                MLDSA_SIGN_VALID_S+64 : data_o_rom <= '{opcode:ABR_UOP_MASKED_PWM, imm:'h0000, length:'d00, operand1:MLDSA_C_NTT_BASE, operand2:MLDSA_S2_2_BASE, operand3:MLDSA_CS_NTT_BASE};
                MLDSA_SIGN_VALID_S+65 : data_o_rom <= '{opcode:ABR_UOP_MASKED_INTT, imm:'h0000, length:'d00, operand1:MLDSA_CS_NTT_BASE, operand2:MLDSA_TEMP2_BASE, operand3:MLDSA_CS2_BASE};
                MLDSA_SIGN_VALID_S+66 : data_o_rom <= '{opcode:ABR_UOP_PWS, imm:'h0000, length:'d00, operand1:MLDSA_CS2_BASE, operand2:MLDSA_W0_2_BASE, operand3:MLDSA_R0_BASE};
                MLDSA_SIGN_VALID_S+67 : data_o_rom <= '{opcode:ABR_UOP_NORMCHK, imm:MLDSA_NORMCHK_R0, length:'d00, operand1:MLDSA_R0_BASE, operand2:ABR_NOP, operand3:ABR_NOP};
                MLDSA_SIGN_VALID_S+68 : data_o_rom <= '{opcode:ABR_UOP_NORMCHK, imm:MLDSA_NORMCHK_CT0, length:'d00, operand1:MLDSA_CT_2_BASE, operand2:ABR_NOP, operand3:ABR_NOP};
                MLDSA_SIGN_VALID_S+69 : data_o_rom <= '{opcode:ABR_UOP_PWA, imm:'h0000, length:'d00, operand1:MLDSA_R0_BASE, operand2:MLDSA_CT_2_BASE, operand3:MLDSA_HINT_R_2_BASE};

                MLDSA_SIGN_VALID_S+70 : data_o_rom <= '{opcode:ABR_UOP_MASKED_PWM, imm:'h0000, length:'d00, operand1:MLDSA_C_NTT_BASE, operand2:MLDSA_S2_3_BASE, operand3:MLDSA_CS_NTT_BASE};
                MLDSA_SIGN_VALID_S+71 : data_o_rom <= '{opcode:ABR_UOP_MASKED_INTT, imm:'h0000, length:'d00, operand1:MLDSA_CS_NTT_BASE, operand2:MLDSA_TEMP2_BASE, operand3:MLDSA_CS2_BASE};
                MLDSA_SIGN_VALID_S+72 : data_o_rom <= '{opcode:ABR_UOP_PWS, imm:'h0000, length:'d00, operand1:MLDSA_CS2_BASE, operand2:MLDSA_W0_3_BASE, operand3:MLDSA_R0_BASE};
                MLDSA_SIGN_VALID_S+73 : data_o_rom <= '{opcode:ABR_UOP_NORMCHK, imm:MLDSA_NORMCHK_R0, length:'d00, operand1:MLDSA_R0_BASE, operand2:ABR_NOP, operand3:ABR_NOP};
                MLDSA_SIGN_VALID_S+74 : data_o_rom <= '{opcode:ABR_UOP_NORMCHK, imm:MLDSA_NORMCHK_CT0, length:'d00, operand1:MLDSA_CT_3_BASE, operand2:ABR_NOP, operand3:ABR_NOP};
                MLDSA_SIGN_VALID_S+75 : data_o_rom <= '{opcode:ABR_UOP_PWA, imm:'h0000, length:'d00, operand1:MLDSA_R0_BASE, operand2:MLDSA_CT_3_BASE, operand3:MLDSA_HINT_R_3_BASE};

                MLDSA_SIGN_VALID_S+76 : data_o_rom <= '{opcode:ABR_UOP_MASKED_PWM, imm:'h0000, length:'d00, operand1:MLDSA_C_NTT_BASE, operand2:MLDSA_S2_4_BASE, operand3:MLDSA_CS_NTT_BASE};
                MLDSA_SIGN_VALID_S+77 : data_o_rom <= '{opcode:ABR_UOP_MASKED_INTT, imm:'h0000, length:'d00, operand1:MLDSA_CS_NTT_BASE, operand2:MLDSA_TEMP2_BASE, operand3:MLDSA_CS2_BASE};
                MLDSA_SIGN_VALID_S+78 : data_o_rom <= '{opcode:ABR_UOP_PWS, imm:'h0000, length:'d00, operand1:MLDSA_CS2_BASE, operand2:MLDSA_W0_4_BASE, operand3:MLDSA_R0_BASE};
                MLDSA_SIGN_VALID_S+79 : data_o_rom <= '{opcode:ABR_UOP_NORMCHK, imm:MLDSA_NORMCHK_R0, length:'d00, operand1:MLDSA_R0_BASE, operand2:ABR_NOP, operand3:ABR_NOP};
                MLDSA_SIGN_VALID_S+80 : data_o_rom <= '{opcode:ABR_UOP_NORMCHK, imm:MLDSA_NORMCHK_CT0, length:'d00, operand1:MLDSA_CT_4_BASE, operand2:ABR_NOP, operand3:ABR_NOP};
                MLDSA_SIGN_VALID_S+81 : data_o_rom <= '{opcode:ABR_UOP_PWA, imm:'h0000, length:'d00, operand1:MLDSA_R0_BASE, operand2:MLDSA_CT_4_BASE, operand3:MLDSA_HINT_R_4_BASE};

                MLDSA_SIGN_VALID_S+82 : data_o_rom <= '{opcode:ABR_UOP_MASKED_PWM, imm:'h0000, length:'d00, operand1:MLDSA_C_NTT_BASE, operand2:MLDSA_S2_5_BASE, operand3:MLDSA_CS_NTT_BASE};
                MLDSA_SIGN_VALID_S+83 : data_o_rom <= '{opcode:ABR_UOP_MASKED_INTT, imm:'h0000, length:'d00, operand1:MLDSA_CS_NTT_BASE, operand2:MLDSA_TEMP2_BASE, operand3:MLDSA_CS2_BASE};
                MLDSA_SIGN_VALID_S+84 : data_o_rom <= '{opcode:ABR_UOP_PWS, imm:'h0000, length:'d00, operand1:MLDSA_CS2_BASE, operand2:MLDSA_W0_5_BASE, operand3:MLDSA_R0_BASE};
                MLDSA_SIGN_VALID_S+85 : data_o_rom <= '{opcode:ABR_UOP_NORMCHK, imm:MLDSA_NORMCHK_R0, length:'d00, operand1:MLDSA_R0_BASE, operand2:ABR_NOP, operand3:ABR_NOP};
                MLDSA_SIGN_VALID_S+86 : data_o_rom <= '{opcode:ABR_UOP_NORMCHK, imm:MLDSA_NORMCHK_CT0, length:'d00, operand1:MLDSA_CT_5_BASE, operand2:ABR_NOP, operand3:ABR_NOP};
                MLDSA_SIGN_VALID_S+87 : data_o_rom <= '{opcode:ABR_UOP_PWA, imm:'h0000, length:'d00, operand1:MLDSA_R0_BASE, operand2:MLDSA_CT_5_BASE, operand3:MLDSA_HINT_R_5_BASE};

                MLDSA_SIGN_VALID_S+88 : data_o_rom <= '{opcode:ABR_UOP_MASKED_PWM, imm:'h0000, length:'d00, operand1:MLDSA_C_NTT_BASE, operand2:MLDSA_S2_6_BASE, operand3:MLDSA_CS_NTT_BASE};
                MLDSA_SIGN_VALID_S+89 : data_o_rom <= '{opcode:ABR_UOP_MASKED_INTT, imm:'h0000, length:'d00, operand1:MLDSA_CS_NTT_BASE, operand2:MLDSA_TEMP2_BASE, operand3:MLDSA_CS2_BASE};
                MLDSA_SIGN_VALID_S+90 : data_o_rom <= '{opcode:ABR_UOP_PWS, imm:'h0000, length:'d00, operand1:MLDSA_CS2_BASE, operand2:MLDSA_W0_6_BASE, operand3:MLDSA_R0_BASE};
                MLDSA_SIGN_VALID_S+91 : data_o_rom <= '{opcode:ABR_UOP_NORMCHK, imm:MLDSA_NORMCHK_R0, length:'d00, operand1:MLDSA_R0_BASE, operand2:ABR_NOP, operand3:ABR_NOP};
                MLDSA_SIGN_VALID_S+92 : data_o_rom <= '{opcode:ABR_UOP_NORMCHK, imm:MLDSA_NORMCHK_CT0, length:'d00, operand1:MLDSA_CT_6_BASE, operand2:ABR_NOP, operand3:ABR_NOP};
                MLDSA_SIGN_VALID_S+93 : data_o_rom <= '{opcode:ABR_UOP_PWA, imm:'h0000, length:'d00, operand1:MLDSA_R0_BASE, operand2:MLDSA_CT_6_BASE, operand3:MLDSA_HINT_R_6_BASE};

                MLDSA_SIGN_VALID_S+94 : data_o_rom <= '{opcode:ABR_UOP_MASKED_PWM, imm:'h0000, length:'d00, operand1:MLDSA_C_NTT_BASE, operand2:MLDSA_S2_7_BASE, operand3:MLDSA_CS_NTT_BASE};
                MLDSA_SIGN_VALID_S+95 : data_o_rom <= '{opcode:ABR_UOP_MASKED_INTT, imm:'h0000, length:'d00, operand1:MLDSA_CS_NTT_BASE, operand2:MLDSA_TEMP2_BASE, operand3:MLDSA_CS2_BASE};
                MLDSA_SIGN_VALID_S+96 : data_o_rom <= '{opcode:ABR_UOP_PWS, imm:'h0000, length:'d00, operand1:MLDSA_CS2_BASE, operand2:MLDSA_W0_7_BASE, operand3:MLDSA_R0_BASE};
                MLDSA_SIGN_VALID_S+97 : data_o_rom <= '{opcode:ABR_UOP_NORMCHK, imm:MLDSA_NORMCHK_R0, length:'d00, operand1:MLDSA_R0_BASE, operand2:ABR_NOP, operand3:ABR_NOP};
                MLDSA_SIGN_VALID_S+98 : data_o_rom <= '{opcode:ABR_UOP_NORMCHK, imm:MLDSA_NORMCHK_CT0, length:'d00, operand1:MLDSA_CT_7_BASE, operand2:ABR_NOP, operand3:ABR_NOP};
                MLDSA_SIGN_VALID_S+99 : data_o_rom <= '{opcode:ABR_UOP_PWA, imm:'h0000, length:'d00, operand1:MLDSA_R0_BASE, operand2:MLDSA_CT_7_BASE, operand3:MLDSA_HINT_R_7_BASE};
                
                MLDSA_SIGN_VALID_S+100: data_o_rom <= '{opcode:ABR_UOP_MAKEHINT, imm:'h0000, length:'d00, operand1:MLDSA_HINT_R_0_BASE, operand2:ABR_NOP, operand3:ABR_NOP};

                MLDSA_SIGN_CHL_E        : data_o_rom <= '{opcode:ABR_UOP_NOP, imm:'h0000, length:'d00, operand1:ABR_NOP, operand2:ABR_NOP, operand3:ABR_NOP};
                MLDSA_SIGN_E            : data_o_rom <= '{opcode:ABR_UOP_NOP, imm:'h0000, length:'d00, operand1:ABR_NOP, operand2:ABR_NOP, operand3:ABR_NOP};

                //Verify flow
                //(ρ,t1)←pkDecode(pk)
                MLDSA_VERIFY_S          : data_o_rom <= '{opcode:ABR_UOP_PKDECODE, imm:'h0000, length:'d00, operand1:ABR_NOP, operand2:ABR_NOP, operand3:MLDSA_T0_BASE};
                //(c˜,z,h)←sigDecode(σ) 
                MLDSA_VERIFY_S+ 1       : data_o_rom <= '{opcode:ABR_UOP_SIGDEC_Z, imm:'h0000, length:'d00, operand1:ABR_NOP, operand2:ABR_NOP, operand3:MLDSA_Z_0_BASE};
                //||z||∞ ≥ γ1 −β
                MLDSA_VERIFY_S+ 2       : data_o_rom <= '{opcode:ABR_UOP_NORMCHK, imm:MLDSA_NORMCHK_Z, length:'d00, operand1:MLDSA_Z_0_BASE, operand2:ABR_NOP, operand3:ABR_NOP};
                MLDSA_VERIFY_S+ 3       : data_o_rom <= '{opcode:ABR_UOP_NORMCHK, imm:MLDSA_NORMCHK_Z, length:'d00, operand1:MLDSA_Z_1_BASE, operand2:ABR_NOP, operand3:ABR_NOP};
                MLDSA_VERIFY_S+ 4       : data_o_rom <= '{opcode:ABR_UOP_NORMCHK, imm:MLDSA_NORMCHK_Z, length:'d00, operand1:MLDSA_Z_2_BASE, operand2:ABR_NOP, operand3:ABR_NOP};
                MLDSA_VERIFY_S+ 5       : data_o_rom <= '{opcode:ABR_UOP_NORMCHK, imm:MLDSA_NORMCHK_Z, length:'d00, operand1:MLDSA_Z_3_BASE, operand2:ABR_NOP, operand3:ABR_NOP};
                MLDSA_VERIFY_S+ 6       : data_o_rom <= '{opcode:ABR_UOP_NORMCHK, imm:MLDSA_NORMCHK_Z, length:'d00, operand1:MLDSA_Z_4_BASE, operand2:ABR_NOP, operand3:ABR_NOP};
                MLDSA_VERIFY_S+ 7       : data_o_rom <= '{opcode:ABR_UOP_NORMCHK, imm:MLDSA_NORMCHK_Z, length:'d00, operand1:MLDSA_Z_5_BASE, operand2:ABR_NOP, operand3:ABR_NOP};
                MLDSA_VERIFY_S+ 8       : data_o_rom <= '{opcode:ABR_UOP_NORMCHK, imm:MLDSA_NORMCHK_Z, length:'d00, operand1:MLDSA_Z_6_BASE, operand2:ABR_NOP, operand3:ABR_NOP};
                //tr ←H(pk,512)
                MLDSA_VERIFY_H_TR           : data_o_rom <= '{opcode:ABR_UOP_SHAKE256, imm:'h0000, length:PUBKEY_NUM_BYTES, operand1:MLDSA_PK_REG_ID, operand2:ABR_NOP, operand3:MLDSA_DEST_TR_REG_ID};
                MLDSA_VERIFY_CHECK_MODE     : data_o_rom <= '{opcode:ABR_UOP_NOP, imm:'h0000, length:'d00, operand1:ABR_NOP, operand2:ABR_NOP, operand3:ABR_NOP};
                //μ ←H(tr||M,512)
                MLDSA_VERIFY_H_MU           : data_o_rom <= '{opcode:ABR_UOP_LD_SHAKE256, imm:'h0000, length:'d64, operand1:MLDSA_TR_ID, operand2:ABR_NOP, operand3:ABR_NOP};
                MLDSA_VERIFY_H_MU+ 1        : data_o_rom <= '{opcode:ABR_UOP_SHAKE256, imm:'h0000, length:'d66, operand1:MLDSA_MSG_ID, operand2:ABR_NOP, operand3:MLDSA_DEST_MU_REG_ID};
                //c ←SampleInBall(c˜1)
                MLDSA_VERIFY_MAKE_C         : data_o_rom <= '{opcode:ABR_UOP_SIB, imm:'h0000, length:'d64, operand1:MLDSA_SIG_C_REG_ID, operand2:ABR_NOP, operand3:ABR_NOP};
                //cˆ ←NTT(c)
                MLDSA_VERIFY_NTT_C          : data_o_rom <= '{opcode:ABR_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_C_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_C_NTT_BASE};
                //t1 ←NTT(t1)
                MLDSA_VERIFY_NTT_T1          : data_o_rom <= '{opcode:ABR_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_T0_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_T0_BASE};
                MLDSA_VERIFY_NTT_T1+ 1       : data_o_rom <= '{opcode:ABR_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_T1_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_T1_BASE};
                MLDSA_VERIFY_NTT_T1+ 2       : data_o_rom <= '{opcode:ABR_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_T2_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_T2_BASE};
                MLDSA_VERIFY_NTT_T1+ 3       : data_o_rom <= '{opcode:ABR_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_T3_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_T3_BASE};
                MLDSA_VERIFY_NTT_T1+ 4       : data_o_rom <= '{opcode:ABR_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_T4_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_T4_BASE};
                MLDSA_VERIFY_NTT_T1+ 5       : data_o_rom <= '{opcode:ABR_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_T5_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_T5_BASE};
                MLDSA_VERIFY_NTT_T1+ 6       : data_o_rom <= '{opcode:ABR_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_T6_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_T6_BASE};
                MLDSA_VERIFY_NTT_T1+ 7       : data_o_rom <= '{opcode:ABR_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_T7_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_T7_BASE};

                //z ←NTT(z)
                MLDSA_VERIFY_NTT_Z          : data_o_rom <= '{opcode:ABR_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_Z_0_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_Z_NTT_0_BASE};
                MLDSA_VERIFY_NTT_Z+ 1       : data_o_rom <= '{opcode:ABR_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_Z_1_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_Z_NTT_1_BASE};
                MLDSA_VERIFY_NTT_Z+ 2       : data_o_rom <= '{opcode:ABR_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_Z_2_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_Z_NTT_2_BASE};
                MLDSA_VERIFY_NTT_Z+ 3       : data_o_rom <= '{opcode:ABR_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_Z_3_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_Z_NTT_3_BASE};
                MLDSA_VERIFY_NTT_Z+ 4       : data_o_rom <= '{opcode:ABR_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_Z_4_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_Z_NTT_4_BASE};
                MLDSA_VERIFY_NTT_Z+ 5       : data_o_rom <= '{opcode:ABR_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_Z_5_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_Z_NTT_5_BASE};
                MLDSA_VERIFY_NTT_Z+ 6       : data_o_rom <= '{opcode:ABR_UOP_NTT, imm:'h0000, length:'d00, operand1:MLDSA_Z_6_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_Z_NTT_6_BASE};
                //Aˆ ←ExpandA(ρ) AND Aˆ ◦NTT(z)
                MLDSA_VERIFY_EXP_A+ 0       : data_o_rom <= '{opcode:ABR_UOP_REJS_PWM,  imm:'h0000, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_0_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 1       : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0001, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_1_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 2       : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0002, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_2_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 3       : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0003, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_3_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 4       : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0004, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_4_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 5       : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0005, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_5_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 6       : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0006, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_6_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 7       : data_o_rom <= '{opcode:ABR_UOP_PWM, imm:'h0000, length:'d00, operand1:MLDSA_C_NTT_BASE, operand2:MLDSA_T0_BASE, operand3:MLDSA_CT_BASE};
                MLDSA_VERIFY_EXP_A+ 8       : data_o_rom <= '{opcode:ABR_UOP_PWS, imm:'h0000, length:'d00, operand1:MLDSA_CT_BASE, operand2:MLDSA_AZ0_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 9        : data_o_rom <= '{opcode:ABR_UOP_INTT, imm:'h0000, length:'d00, operand1:MLDSA_AZ0_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_W0_0_BASE};
                
                MLDSA_VERIFY_EXP_A+ 10      : data_o_rom <= '{opcode:ABR_UOP_REJS_PWM,  imm:'h0100, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_0_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 11      : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0101, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_1_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 12      : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0102, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_2_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 13      : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0103, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_3_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 14      : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0104, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_4_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 15      : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0105, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_5_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 16      : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0106, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_6_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 17      : data_o_rom <= '{opcode:ABR_UOP_PWM, imm:'h0000, length:'d00, operand1:MLDSA_C_NTT_BASE, operand2:MLDSA_T1_BASE, operand3:MLDSA_CT_BASE};
                MLDSA_VERIFY_EXP_A+ 18      : data_o_rom <= '{opcode:ABR_UOP_PWS, imm:'h0000, length:'d00, operand1:MLDSA_CT_BASE, operand2:MLDSA_AZ0_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 19      : data_o_rom <= '{opcode:ABR_UOP_INTT, imm:'h0000, length:'d00, operand1:MLDSA_AZ0_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_W0_1_BASE};
                
                MLDSA_VERIFY_EXP_A+ 20      : data_o_rom <= '{opcode:ABR_UOP_REJS_PWM,  imm:'h0200, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_0_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 21      : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0201, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_1_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 22      : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0202, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_2_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 23      : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0203, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_3_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 24      : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0204, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_4_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 25      : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0205, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_5_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 26      : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0206, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_6_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 27      : data_o_rom <= '{opcode:ABR_UOP_PWM, imm:'h0000, length:'d00, operand1:MLDSA_C_NTT_BASE, operand2:MLDSA_T2_BASE, operand3:MLDSA_CT_BASE};
                MLDSA_VERIFY_EXP_A+ 28      : data_o_rom <= '{opcode:ABR_UOP_PWS, imm:'h0000, length:'d00, operand1:MLDSA_CT_BASE, operand2:MLDSA_AZ0_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 29      : data_o_rom <= '{opcode:ABR_UOP_INTT, imm:'h0000, length:'d00, operand1:MLDSA_AZ0_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_W0_2_BASE};
                
                MLDSA_VERIFY_EXP_A+ 30      : data_o_rom <= '{opcode:ABR_UOP_REJS_PWM,  imm:'h0300, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_0_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 31      : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0301, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_1_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 32      : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0302, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_2_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 33      : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0303, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_3_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 34      : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0304, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_4_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 35      : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0305, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_5_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 36      : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0306, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_6_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 37      : data_o_rom <= '{opcode:ABR_UOP_PWM, imm:'h0000, length:'d00, operand1:MLDSA_C_NTT_BASE, operand2:MLDSA_T3_BASE, operand3:MLDSA_CT_BASE};
                MLDSA_VERIFY_EXP_A+ 38      : data_o_rom <= '{opcode:ABR_UOP_PWS, imm:'h0000, length:'d00, operand1:MLDSA_CT_BASE, operand2:MLDSA_AZ0_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 39      : data_o_rom <= '{opcode:ABR_UOP_INTT, imm:'h0000, length:'d00, operand1:MLDSA_AZ0_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_W0_3_BASE};
        
                MLDSA_VERIFY_EXP_A+ 40      : data_o_rom <= '{opcode:ABR_UOP_REJS_PWM,  imm:'h0400, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_0_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 41      : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0401, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_1_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 42      : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0402, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_2_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 43      : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0403, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_3_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 44      : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0404, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_4_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 45      : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0405, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_5_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 46      : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0406, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_6_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 47      : data_o_rom <= '{opcode:ABR_UOP_PWM, imm:'h0000, length:'d00, operand1:MLDSA_C_NTT_BASE, operand2:MLDSA_T4_BASE, operand3:MLDSA_CT_BASE};
                MLDSA_VERIFY_EXP_A+ 48      : data_o_rom <= '{opcode:ABR_UOP_PWS, imm:'h0000, length:'d00, operand1:MLDSA_CT_BASE, operand2:MLDSA_AZ0_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 49      : data_o_rom <= '{opcode:ABR_UOP_INTT, imm:'h0000, length:'d00, operand1:MLDSA_AZ0_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_W0_4_BASE};
        
                MLDSA_VERIFY_EXP_A+ 50      : data_o_rom <= '{opcode:ABR_UOP_REJS_PWM,  imm:'h0500, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_0_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 51      : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0501, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_1_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 52      : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0502, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_2_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 53      : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0503, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_3_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 54      : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0504, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_4_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 55      : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0505, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_5_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 56      : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0506, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_6_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 57      : data_o_rom <= '{opcode:ABR_UOP_PWM, imm:'h0000, length:'d00, operand1:MLDSA_C_NTT_BASE, operand2:MLDSA_T5_BASE, operand3:MLDSA_CT_BASE};
                MLDSA_VERIFY_EXP_A+ 58      : data_o_rom <= '{opcode:ABR_UOP_PWS, imm:'h0000, length:'d00, operand1:MLDSA_CT_BASE, operand2:MLDSA_AZ0_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 59      : data_o_rom <= '{opcode:ABR_UOP_INTT, imm:'h0000, length:'d00, operand1:MLDSA_AZ0_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_W0_5_BASE};
                
                MLDSA_VERIFY_EXP_A+ 60      : data_o_rom <= '{opcode:ABR_UOP_REJS_PWM,  imm:'h0600, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_0_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 61      : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0601, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_1_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 62      : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0602, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_2_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 63      : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0603, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_3_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 64      : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0604, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_4_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 65      : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0605, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_5_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 66      : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0606, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_6_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 67      : data_o_rom <= '{opcode:ABR_UOP_PWM, imm:'h0000, length:'d00, operand1:MLDSA_C_NTT_BASE, operand2:MLDSA_T6_BASE, operand3:MLDSA_CT_BASE};
                MLDSA_VERIFY_EXP_A+ 68      : data_o_rom <= '{opcode:ABR_UOP_PWS, imm:'h0000, length:'d00, operand1:MLDSA_CT_BASE, operand2:MLDSA_AZ0_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 69      : data_o_rom <= '{opcode:ABR_UOP_INTT, imm:'h0000, length:'d00, operand1:MLDSA_AZ0_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_W0_6_BASE};
            
                MLDSA_VERIFY_EXP_A+ 70      : data_o_rom <= '{opcode:ABR_UOP_REJS_PWM,  imm:'h0700, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_0_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 71      : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0701, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_1_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 72      : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0702, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_2_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 73      : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0703, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_3_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 74      : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0704, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_4_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 75      : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0705, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_5_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 76      : data_o_rom <= '{opcode:ABR_UOP_REJS_PWMA, imm:'h0706, length:'d34, operand1:MLDSA_RHO_ID, operand2:MLDSA_Z_NTT_6_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 77      : data_o_rom <= '{opcode:ABR_UOP_PWM, imm:'h0000, length:'d00, operand1:MLDSA_C_NTT_BASE, operand2:MLDSA_T7_BASE, operand3:MLDSA_CT_BASE};
                MLDSA_VERIFY_EXP_A+ 78      : data_o_rom <= '{opcode:ABR_UOP_PWS, imm:'h0000, length:'d00, operand1:MLDSA_CT_BASE, operand2:MLDSA_AZ0_BASE, operand3:MLDSA_AZ0_BASE};
                MLDSA_VERIFY_EXP_A+ 79      : data_o_rom <= '{opcode:ABR_UOP_INTT, imm:'h0000, length:'d00, operand1:MLDSA_AZ0_BASE, operand2:MLDSA_TEMP0_BASE, operand3:MLDSA_W0_7_BASE};
     
                MLDSA_VERIFY_RES+ 0         : data_o_rom <= '{opcode:ABR_UOP_SIGDEC_H, imm:'h0000, length:'d00, operand1:ABR_NOP, operand2:ABR_NOP, operand3:MLDSA_HINT_R_0_BASE};
                MLDSA_VERIFY_RES+ 1         : data_o_rom <= '{opcode:ABR_UOP_LD_SHAKE256, imm:'h0000, length:'d64, operand1:MLDSA_MU_ID, operand2:ABR_NOP, operand3:ABR_NOP};
                MLDSA_VERIFY_RES+ 2         : data_o_rom <= '{opcode:ABR_UOP_USEHINT, imm:'h0000, length:'d00, operand1:MLDSA_W0_0_BASE, operand2:MLDSA_HINT_R_0_BASE, operand3:ABR_NOP};
                MLDSA_VERIFY_RES+ 3         : data_o_rom <= '{opcode:ABR_UOP_RUN_SHAKE256, imm:'h0000, length:'d00, operand1:ABR_NOP, operand2:ABR_NOP, operand3:MLDSA_DEST_VERIFY_RES_REG_ID};
                MLDSA_VERIFY_E              : data_o_rom <= '{opcode:ABR_UOP_NOP, imm:'h0000, length:'d00, operand1:ABR_NOP, operand2:ABR_NOP, operand3:ABR_NOP};

                //MLKEM Keygen
                //rnd_seed=Keccak(entropy||counter)
                MLKEM_KG_S + 0 : data_o_rom <= '{opcode:ABR_UOP_LD_SHAKE256, imm:'h0000, length:'d64, operand1:ABR_ENTROPY_ID, operand2:ABR_NOP, operand3:ABR_NOP};                
                MLKEM_KG_S + 1 : data_o_rom <= '{opcode:ABR_UOP_SHAKE256, imm:'h0000, length:'d08, operand1:ABR_CNT_ID, operand2:ABR_NOP, operand3:ABR_DEST_LFSR_SEED_REG_ID};
                MLKEM_KG_S + 2 : data_o_rom <= '{opcode:ABR_UOP_LFSR, imm:'h0000, length:'d00, operand1:ABR_NOP, operand2:ABR_NOP, operand3:ABR_NOP};
                MLKEM_KG_S + 3 : data_o_rom <= '{opcode:ABR_UOP_SHA512, imm:'h0004, length:'d33, operand1:MLKEM_SEED_D_ID, operand2:ABR_NOP, operand3:MLKEM_DEST_RHO_SIGMA_REG_ID};
                MLKEM_KG_S + 4 : data_o_rom <= '{opcode:ABR_UOP_CBD, imm:'h0000, length:'d33, operand1:MLKEM_SIGMA_ID, operand2:ABR_NOP, operand3:MLKEM_S0_BASE};
                MLKEM_KG_S + 5 : data_o_rom <= '{opcode:ABR_UOP_CBD, imm:'h0001, length:'d33, operand1:MLKEM_SIGMA_ID, operand2:ABR_NOP, operand3:MLKEM_S1_BASE};
                MLKEM_KG_S + 6 : data_o_rom <= '{opcode:ABR_UOP_CBD, imm:'h0002, length:'d33, operand1:MLKEM_SIGMA_ID, operand2:ABR_NOP, operand3:MLKEM_S2_BASE};
                MLKEM_KG_S + 7 : data_o_rom <= '{opcode:ABR_UOP_CBD, imm:'h0003, length:'d33, operand1:MLKEM_SIGMA_ID, operand2:ABR_NOP, operand3:MLKEM_S3_BASE};
                MLKEM_KG_S + 8 : data_o_rom <= '{opcode:ABR_UOP_CBD, imm:'h0004, length:'d33, operand1:MLKEM_SIGMA_ID, operand2:ABR_NOP, operand3:MLKEM_E0_BASE};
                MLKEM_KG_S + 9 : data_o_rom <= '{opcode:ABR_UOP_CBD, imm:'h0005, length:'d33, operand1:MLKEM_SIGMA_ID, operand2:ABR_NOP, operand3:MLKEM_E1_BASE};
                MLKEM_KG_S + 10: data_o_rom <= '{opcode:ABR_UOP_CBD, imm:'h0006, length:'d33, operand1:MLKEM_SIGMA_ID, operand2:ABR_NOP, operand3:MLKEM_E2_BASE};
                MLKEM_KG_S + 11: data_o_rom <= '{opcode:ABR_UOP_CBD, imm:'h0007, length:'d33, operand1:MLKEM_SIGMA_ID, operand2:ABR_NOP, operand3:MLKEM_E3_BASE};
                MLKEM_KG_S + 12: data_o_rom <= '{opcode:ABR_UOP_MLKEM_NTT, imm:'h0000, length:'d00, operand1:MLKEM_S0_BASE, operand2:ABR_NOP, operand3:MLKEM_S0_BASE};
                MLKEM_KG_S + 13: data_o_rom <= '{opcode:ABR_UOP_MLKEM_NTT, imm:'h0000, length:'d00, operand1:MLKEM_S1_BASE, operand2:ABR_NOP, operand3:MLKEM_S1_BASE};
                MLKEM_KG_S + 14: data_o_rom <= '{opcode:ABR_UOP_MLKEM_NTT, imm:'h0000, length:'d00, operand1:MLKEM_S2_BASE, operand2:ABR_NOP, operand3:MLKEM_S2_BASE};
                MLKEM_KG_S + 15: data_o_rom <= '{opcode:ABR_UOP_MLKEM_NTT, imm:'h0000, length:'d00, operand1:MLKEM_S3_BASE, operand2:ABR_NOP, operand3:MLKEM_S3_BASE};
                MLKEM_KG_S + 16: data_o_rom <= '{opcode:ABR_UOP_MLKEM_NTT, imm:'h0000, length:'d00, operand1:MLKEM_E0_BASE, operand2:ABR_NOP, operand3:MLKEM_E0_BASE};
                MLKEM_KG_S + 17: data_o_rom <= '{opcode:ABR_UOP_MLKEM_NTT, imm:'h0000, length:'d00, operand1:MLKEM_E1_BASE, operand2:ABR_NOP, operand3:MLKEM_E1_BASE};
                MLKEM_KG_S + 18: data_o_rom <= '{opcode:ABR_UOP_MLKEM_NTT, imm:'h0000, length:'d00, operand1:MLKEM_E2_BASE, operand2:ABR_NOP, operand3:MLKEM_E2_BASE};
                MLKEM_KG_S + 19: data_o_rom <= '{opcode:ABR_UOP_MLKEM_NTT, imm:'h0000, length:'d00, operand1:MLKEM_E3_BASE, operand2:ABR_NOP, operand3:MLKEM_E3_BASE};
                MLKEM_KG_S + 20: data_o_rom <= '{opcode:ABR_UOP_MLKEM_REJS_PWM , imm:'h0000, length:'d34, operand1:MLKEM_RHO_ID, operand2:MLKEM_S0_BASE, operand3:MLKEM_AS0_BASE};
                MLKEM_KG_S + 21: data_o_rom <= '{opcode:ABR_UOP_MLKEM_REJS_PWMA, imm:'h0001, length:'d34, operand1:MLKEM_RHO_ID, operand2:MLKEM_S1_BASE, operand3:MLKEM_AS0_BASE};
                MLKEM_KG_S + 22: data_o_rom <= '{opcode:ABR_UOP_MLKEM_REJS_PWMA, imm:'h0002, length:'d34, operand1:MLKEM_RHO_ID, operand2:MLKEM_S2_BASE, operand3:MLKEM_AS0_BASE};
                MLKEM_KG_S + 23: data_o_rom <= '{opcode:ABR_UOP_MLKEM_REJS_PWMA, imm:'h0003, length:'d34, operand1:MLKEM_RHO_ID, operand2:MLKEM_S3_BASE, operand3:MLKEM_AS0_BASE};
                MLKEM_KG_S + 24: data_o_rom <= '{opcode:ABR_UOP_MLKEM_PWA,       imm:'h0000, length:'d00, operand1:MLKEM_AS0_BASE, operand2:MLKEM_E0_BASE, operand3:MLKEM_T0_BASE};
                MLKEM_KG_S + 25: data_o_rom <= '{opcode:ABR_UOP_MLKEM_REJS_PWM , imm:'h0100, length:'d34, operand1:MLKEM_RHO_ID, operand2:MLKEM_S0_BASE, operand3:MLKEM_AS0_BASE};
                MLKEM_KG_S + 26: data_o_rom <= '{opcode:ABR_UOP_MLKEM_REJS_PWMA, imm:'h0101, length:'d34, operand1:MLKEM_RHO_ID, operand2:MLKEM_S1_BASE, operand3:MLKEM_AS0_BASE};
                MLKEM_KG_S + 27: data_o_rom <= '{opcode:ABR_UOP_MLKEM_REJS_PWMA, imm:'h0102, length:'d34, operand1:MLKEM_RHO_ID, operand2:MLKEM_S2_BASE, operand3:MLKEM_AS0_BASE};
                MLKEM_KG_S + 28: data_o_rom <= '{opcode:ABR_UOP_MLKEM_REJS_PWMA, imm:'h0103, length:'d34, operand1:MLKEM_RHO_ID, operand2:MLKEM_S3_BASE, operand3:MLKEM_AS0_BASE};
                MLKEM_KG_S + 29: data_o_rom <= '{opcode:ABR_UOP_MLKEM_PWA,       imm:'h0000, length:'d00, operand1:MLKEM_AS0_BASE, operand2:MLKEM_E1_BASE, operand3:MLKEM_T1_BASE};
                MLKEM_KG_S + 30: data_o_rom <= '{opcode:ABR_UOP_MLKEM_REJS_PWM , imm:'h0200, length:'d34, operand1:MLKEM_RHO_ID, operand2:MLKEM_S0_BASE, operand3:MLKEM_AS0_BASE};
                MLKEM_KG_S + 31: data_o_rom <= '{opcode:ABR_UOP_MLKEM_REJS_PWMA, imm:'h0201, length:'d34, operand1:MLKEM_RHO_ID, operand2:MLKEM_S1_BASE, operand3:MLKEM_AS0_BASE};
                MLKEM_KG_S + 32: data_o_rom <= '{opcode:ABR_UOP_MLKEM_REJS_PWMA, imm:'h0202, length:'d34, operand1:MLKEM_RHO_ID, operand2:MLKEM_S2_BASE, operand3:MLKEM_AS0_BASE};
                MLKEM_KG_S + 33: data_o_rom <= '{opcode:ABR_UOP_MLKEM_REJS_PWMA, imm:'h0203, length:'d34, operand1:MLKEM_RHO_ID, operand2:MLKEM_S3_BASE, operand3:MLKEM_AS0_BASE};
                MLKEM_KG_S + 34: data_o_rom <= '{opcode:ABR_UOP_MLKEM_PWA,       imm:'h0000, length:'d00, operand1:MLKEM_AS0_BASE, operand2:MLKEM_E2_BASE, operand3:MLKEM_T2_BASE};
                MLKEM_KG_S + 35: data_o_rom <= '{opcode:ABR_UOP_MLKEM_REJS_PWM , imm:'h0300, length:'d34, operand1:MLKEM_RHO_ID, operand2:MLKEM_S0_BASE, operand3:MLKEM_AS0_BASE};
                MLKEM_KG_S + 36: data_o_rom <= '{opcode:ABR_UOP_MLKEM_REJS_PWMA, imm:'h0301, length:'d34, operand1:MLKEM_RHO_ID, operand2:MLKEM_S1_BASE, operand3:MLKEM_AS0_BASE};
                MLKEM_KG_S + 37: data_o_rom <= '{opcode:ABR_UOP_MLKEM_REJS_PWMA, imm:'h0302, length:'d34, operand1:MLKEM_RHO_ID, operand2:MLKEM_S2_BASE, operand3:MLKEM_AS0_BASE};
                MLKEM_KG_S + 38: data_o_rom <= '{opcode:ABR_UOP_MLKEM_REJS_PWMA, imm:'h0303, length:'d34, operand1:MLKEM_RHO_ID, operand2:MLKEM_S3_BASE, operand3:MLKEM_AS0_BASE};
                MLKEM_KG_S + 39: data_o_rom <= '{opcode:ABR_UOP_MLKEM_PWA,       imm:'h0000, length:'d00, operand1:MLKEM_AS0_BASE, operand2:MLKEM_E3_BASE, operand3:MLKEM_T3_BASE};
                MLKEM_KG_S + 40: data_o_rom <= '{opcode:ABR_UOP_COMPRESS, imm:'h0403, length:'d00, operand1:MLKEM_T0_BASE, operand2:ABR_NOP, operand3:MLKEM_DEST_EK_MEM_OFFSET};
                MLKEM_KG_S + 41: data_o_rom <= '{opcode:ABR_UOP_COMPRESS, imm:'h0403, length:'d00, operand1:MLKEM_S0_BASE, operand2:ABR_NOP, operand3:MLKEM_DEST_DK_MEM_OFFSET};
                MLKEM_KG_S + 42: data_o_rom <= '{opcode:ABR_UOP_SHA256, imm:'h0000, length:EK_NUM_BYTES, operand1:MLKEM_EK_REG_ID, operand2:ABR_NOP, operand3:MLKEM_DEST_TR_REG_ID};
                MLKEM_KG_E : data_o_rom <= '{opcode:ABR_UOP_NOP, imm:'h0000, length:'d00, operand1:ABR_NOP, operand2:ABR_NOP, operand3:ABR_NOP};
                //MLKEM Decaps
                //rnd_seed=Keccak(entropy||counter)
                MLKEM_DECAPS_S + 0 : data_o_rom <= '{opcode:ABR_UOP_LD_SHAKE256, imm:'h0000, length:'d64, operand1:ABR_ENTROPY_ID, operand2:ABR_NOP, operand3:ABR_NOP};                
                MLKEM_DECAPS_S + 1 : data_o_rom <= '{opcode:ABR_UOP_SHAKE256, imm:'h0000, length:'d08, operand1:ABR_CNT_ID, operand2:ABR_NOP, operand3:ABR_DEST_LFSR_SEED_REG_ID};
                MLKEM_DECAPS_S + 2 : data_o_rom <= '{opcode:ABR_UOP_LFSR, imm:'h0000, length:'d00, operand1:ABR_NOP, operand2:ABR_NOP, operand3:ABR_NOP};
                MLKEM_DECAPS_S + 3 : data_o_rom <= '{opcode:ABR_UOP_SHA256, imm:'h0000, length:EK_NUM_BYTES, operand1:MLKEM_EK_REG_ID, operand2:ABR_NOP, operand3:MLKEM_DEST_TR_REG_ID};
                MLKEM_DECAPS_S + 4 : data_o_rom <= '{opcode:ABR_UOP_DECOMPRESS, imm:'h0403, length:'d00, operand1:MLKEM_SRC_DK_MEM_OFFSET, operand2:ABR_NOP, operand3:MLKEM_S0_BASE};
                MLKEM_DECAPS_S + 5 : data_o_rom <= '{opcode:ABR_UOP_DECOMPRESS, imm:'h0402, length:'d00, operand1:MLKEM_SRC_C1_MEM_OFFSET, operand2:ABR_NOP, operand3:MLKEM_U0_BASE};
                MLKEM_DECAPS_S + 6 : data_o_rom <= '{opcode:ABR_UOP_DECOMPRESS, imm:'h0101, length:'d00, operand1:MLKEM_SRC_C2_MEM_OFFSET, operand2:ABR_NOP, operand3:MLKEM_V_BASE};
                MLKEM_DECAPS_S + 7 : data_o_rom <= '{opcode:ABR_UOP_MLKEM_NTT, imm:'h0000, length:'d00, operand1:MLKEM_U0_BASE, operand2:ABR_NOP, operand3:MLKEM_UP0_BASE};
                MLKEM_DECAPS_S + 8 : data_o_rom <= '{opcode:ABR_UOP_MLKEM_NTT, imm:'h0000, length:'d00, operand1:MLKEM_U1_BASE, operand2:ABR_NOP, operand3:MLKEM_UP1_BASE};
                MLKEM_DECAPS_S + 9 : data_o_rom <= '{opcode:ABR_UOP_MLKEM_NTT, imm:'h0000, length:'d00, operand1:MLKEM_U2_BASE, operand2:ABR_NOP, operand3:MLKEM_UP2_BASE};
                MLKEM_DECAPS_S + 10 : data_o_rom <= '{opcode:ABR_UOP_MLKEM_NTT, imm:'h0000, length:'d00, operand1:MLKEM_U3_BASE, operand2:ABR_NOP, operand3:MLKEM_UP3_BASE};
                MLKEM_DECAPS_S + 11: data_o_rom <= '{opcode:ABR_UOP_MLKEM_MASKED_PWM, imm:'h0000, length:'d00, operand1:MLKEM_S0_BASE, operand2:MLKEM_UP0_BASE, operand3:MLKEM_SU_MASKED_BASE};
                MLKEM_DECAPS_S + 12: data_o_rom <= '{opcode:ABR_UOP_MLKEM_MASKED_PWMA, imm:'h0000, length:'d00, operand1:MLKEM_S1_BASE, operand2:MLKEM_UP1_BASE, operand3:MLKEM_SU_MASKED_BASE};
                MLKEM_DECAPS_S + 13: data_o_rom <= '{opcode:ABR_UOP_MLKEM_MASKED_PWMA, imm:'h0000, length:'d00, operand1:MLKEM_S2_BASE, operand2:MLKEM_UP2_BASE, operand3:MLKEM_SU_MASKED_BASE};
                MLKEM_DECAPS_S + 14: data_o_rom <= '{opcode:ABR_UOP_MLKEM_MASKED_PWMA, imm:'h0000, length:'d00, operand1:MLKEM_S3_BASE, operand2:MLKEM_UP3_BASE, operand3:MLKEM_SU_MASKED_BASE};
                MLKEM_DECAPS_S + 15: data_o_rom <= '{opcode:ABR_UOP_MLKEM_MASKED_INTT, imm:'h0000, length:'d00, operand1:MLKEM_SU_MASKED_BASE, operand2:ABR_NOP, operand3:MLKEM_SU_BASE};
                MLKEM_DECAPS_S + 16: data_o_rom <= '{opcode:ABR_UOP_MLKEM_PWS, imm:'h0000, length:'d00, operand1:MLKEM_SU_BASE, operand2:MLKEM_V_BASE, operand3:MLKEM_V_BASE};
                MLKEM_DECAPS_S + 17: data_o_rom <= '{opcode:ABR_UOP_COMPRESS, imm:'h0100, length:'d00, operand1:MLKEM_V_BASE, operand2:ABR_NOP, operand3:MLKEM_DEST_MSG_MEM_OFFSET};
                //MLKEM Encaps
                //rnd_seed=Keccak(entropy||counter)
                MLKEM_ENCAPS_S + 0 : data_o_rom <= '{opcode:ABR_UOP_LD_SHAKE256, imm:'h0000, length:'d64, operand1:ABR_ENTROPY_ID, operand2:ABR_NOP, operand3:ABR_NOP};                
                MLKEM_ENCAPS_S + 1 : data_o_rom <= '{opcode:ABR_UOP_SHAKE256, imm:'h0000, length:'d08, operand1:ABR_CNT_ID, operand2:ABR_NOP, operand3:ABR_DEST_LFSR_SEED_REG_ID};
                MLKEM_ENCAPS_S + 2 : data_o_rom <= '{opcode:ABR_UOP_LFSR, imm:'h0000, length:'d00, operand1:ABR_NOP, operand2:ABR_NOP, operand3:ABR_NOP};
                MLKEM_ENCAPS_S + 3 : data_o_rom <= '{opcode:ABR_UOP_DECOMPRESS, imm:'h0403, length:'d00, operand1:MLKEM_SRC_EK_MEM_OFFSET, operand2:ABR_NOP, operand3:MLKEM_T0_BASE};
                MLKEM_ENCAPS_S + 4 : data_o_rom <= '{opcode:ABR_UOP_COMPRESS, imm:'h0413, length:'d00, operand1:MLKEM_T0_BASE, operand2:ABR_NOP, operand3:MLKEM_DEST_EK_MEM_OFFSET};
                MLKEM_ENCAPS_S + 5 : data_o_rom <= '{opcode:ABR_UOP_SHA256, imm:'h0000, length:EK_NUM_BYTES, operand1:MLKEM_EK_REG_ID, operand2:ABR_NOP, operand3:MLKEM_DEST_TR_REG_ID};
                MLKEM_ENCAPS_S + 6 : data_o_rom <= '{opcode:ABR_UOP_LD_SHA512, imm:'h0000, length:'d32, operand1:MLKEM_MSG_ID, operand2:ABR_NOP, operand3:ABR_NOP};
                MLKEM_ENCAPS_S + 7 : data_o_rom <= '{opcode:ABR_UOP_SHA512, imm:'h0000, length:'d32, operand1:MLKEM_TR_ID, operand2:ABR_NOP, operand3:MLKEM_DEST_K_R_REG_ID};
                MLKEM_ENCAPS_S + 8 : data_o_rom <= '{opcode:ABR_UOP_CBD, imm:'h0000, length:'d33, operand1:MLKEM_R_ID, operand2:ABR_NOP, operand3:MLKEM_Y0_BASE};
                MLKEM_ENCAPS_S + 9 : data_o_rom <= '{opcode:ABR_UOP_CBD, imm:'h0001, length:'d33, operand1:MLKEM_R_ID, operand2:ABR_NOP, operand3:MLKEM_Y1_BASE};
                MLKEM_ENCAPS_S + 10: data_o_rom <= '{opcode:ABR_UOP_CBD, imm:'h0002, length:'d33, operand1:MLKEM_R_ID, operand2:ABR_NOP, operand3:MLKEM_Y2_BASE};
                MLKEM_ENCAPS_S + 11: data_o_rom <= '{opcode:ABR_UOP_CBD, imm:'h0003, length:'d33, operand1:MLKEM_R_ID, operand2:ABR_NOP, operand3:MLKEM_Y3_BASE};
                MLKEM_ENCAPS_S + 12: data_o_rom <= '{opcode:ABR_UOP_CBD, imm:'h0004, length:'d33, operand1:MLKEM_R_ID, operand2:ABR_NOP, operand3:MLKEM_E0_BASE};
                MLKEM_ENCAPS_S + 13: data_o_rom <= '{opcode:ABR_UOP_CBD, imm:'h0005, length:'d33, operand1:MLKEM_R_ID, operand2:ABR_NOP, operand3:MLKEM_E1_BASE};
                MLKEM_ENCAPS_S + 14: data_o_rom <= '{opcode:ABR_UOP_CBD, imm:'h0006, length:'d33, operand1:MLKEM_R_ID, operand2:ABR_NOP, operand3:MLKEM_E2_BASE};
                MLKEM_ENCAPS_S + 15: data_o_rom <= '{opcode:ABR_UOP_CBD, imm:'h0007, length:'d33, operand1:MLKEM_R_ID, operand2:ABR_NOP, operand3:MLKEM_E3_BASE};
                MLKEM_ENCAPS_S + 16: data_o_rom <= '{opcode:ABR_UOP_CBD, imm:'h0008, length:'d33, operand1:MLKEM_R_ID, operand2:ABR_NOP, operand3:MLKEM_E_2_BASE};
                MLKEM_ENCAPS_S + 17: data_o_rom <= '{opcode:ABR_UOP_MLKEM_NTT, imm:'h0000, length:'d00, operand1:MLKEM_Y0_BASE, operand2:ABR_NOP, operand3:MLKEM_Y0_BASE};
                MLKEM_ENCAPS_S + 18: data_o_rom <= '{opcode:ABR_UOP_MLKEM_NTT, imm:'h0000, length:'d00, operand1:MLKEM_Y1_BASE, operand2:ABR_NOP, operand3:MLKEM_Y1_BASE};
                MLKEM_ENCAPS_S + 19: data_o_rom <= '{opcode:ABR_UOP_MLKEM_NTT, imm:'h0000, length:'d00, operand1:MLKEM_Y2_BASE, operand2:ABR_NOP, operand3:MLKEM_Y2_BASE};
                MLKEM_ENCAPS_S + 20: data_o_rom <= '{opcode:ABR_UOP_MLKEM_NTT, imm:'h0000, length:'d00, operand1:MLKEM_Y3_BASE, operand2:ABR_NOP, operand3:MLKEM_Y3_BASE};
                MLKEM_ENCAPS_S + 21: data_o_rom <= '{opcode:ABR_UOP_MLKEM_MASKED_REJS_PWM, imm:'h0000, length:'d34, operand1:MLKEM_RHO_ID, operand2:MLKEM_Y0_BASE, operand3:MLKEM_AY0_BASE};
                MLKEM_ENCAPS_S + 22: data_o_rom <= '{opcode:ABR_UOP_MLKEM_MASKED_REJS_PWMA, imm:'h0100, length:'d34, operand1:MLKEM_RHO_ID, operand2:MLKEM_Y1_BASE, operand3:MLKEM_AY0_BASE};
                MLKEM_ENCAPS_S + 23: data_o_rom <= '{opcode:ABR_UOP_MLKEM_MASKED_REJS_PWMA, imm:'h0200, length:'d34, operand1:MLKEM_RHO_ID, operand2:MLKEM_Y2_BASE, operand3:MLKEM_AY0_BASE};
                MLKEM_ENCAPS_S + 24: data_o_rom <= '{opcode:ABR_UOP_MLKEM_MASKED_REJS_PWMA, imm:'h0300, length:'d34, operand1:MLKEM_RHO_ID, operand2:MLKEM_Y3_BASE, operand3:MLKEM_AY0_BASE};
                MLKEM_ENCAPS_S + 25: data_o_rom <= '{opcode:ABR_UOP_MLKEM_MASKED_INTT, imm:'h0000, length:'d00, operand1:MLKEM_AY0_BASE, operand2:ABR_NOP, operand3:MLKEM_AY0_BASE};
                MLKEM_ENCAPS_S + 26: data_o_rom <= '{opcode:ABR_UOP_MLKEM_PWA, imm:'h0000, length:'d00, operand1:MLKEM_AY0_BASE, operand2:MLKEM_E0_BASE, operand3:MLKEM_U0_BASE};
                MLKEM_ENCAPS_S + 27: data_o_rom <= '{opcode:ABR_UOP_MLKEM_MASKED_REJS_PWM, imm:'h0001, length:'d34, operand1:MLKEM_RHO_ID, operand2:MLKEM_Y0_BASE, operand3:MLKEM_AY0_BASE};
                MLKEM_ENCAPS_S + 28: data_o_rom <= '{opcode:ABR_UOP_MLKEM_MASKED_REJS_PWMA, imm:'h0101, length:'d34, operand1:MLKEM_RHO_ID, operand2:MLKEM_Y1_BASE, operand3:MLKEM_AY0_BASE};
                MLKEM_ENCAPS_S + 29: data_o_rom <= '{opcode:ABR_UOP_MLKEM_MASKED_REJS_PWMA, imm:'h0201, length:'d34, operand1:MLKEM_RHO_ID, operand2:MLKEM_Y2_BASE, operand3:MLKEM_AY0_BASE};
                MLKEM_ENCAPS_S + 30: data_o_rom <= '{opcode:ABR_UOP_MLKEM_MASKED_REJS_PWMA, imm:'h0301, length:'d34, operand1:MLKEM_RHO_ID, operand2:MLKEM_Y3_BASE, operand3:MLKEM_AY0_BASE};
                MLKEM_ENCAPS_S + 31: data_o_rom <= '{opcode:ABR_UOP_MLKEM_MASKED_INTT, imm:'h0000, length:'d00, operand1:MLKEM_AY0_BASE, operand2:ABR_NOP, operand3:MLKEM_AY0_BASE};
                MLKEM_ENCAPS_S + 32: data_o_rom <= '{opcode:ABR_UOP_MLKEM_PWA, imm:'h0000, length:'d00, operand1:MLKEM_AY0_BASE, operand2:MLKEM_E1_BASE, operand3:MLKEM_U1_BASE};
                MLKEM_ENCAPS_S + 33: data_o_rom <= '{opcode:ABR_UOP_MLKEM_MASKED_REJS_PWM, imm:'h0002, length:'d34, operand1:MLKEM_RHO_ID, operand2:MLKEM_Y0_BASE, operand3:MLKEM_AY0_BASE};
                MLKEM_ENCAPS_S + 34: data_o_rom <= '{opcode:ABR_UOP_MLKEM_MASKED_REJS_PWMA, imm:'h0102, length:'d34, operand1:MLKEM_RHO_ID, operand2:MLKEM_Y1_BASE, operand3:MLKEM_AY0_BASE};
                MLKEM_ENCAPS_S + 35: data_o_rom <= '{opcode:ABR_UOP_MLKEM_MASKED_REJS_PWMA, imm:'h0202, length:'d34, operand1:MLKEM_RHO_ID, operand2:MLKEM_Y2_BASE, operand3:MLKEM_AY0_BASE};
                MLKEM_ENCAPS_S + 36: data_o_rom <= '{opcode:ABR_UOP_MLKEM_MASKED_REJS_PWMA, imm:'h0302, length:'d34, operand1:MLKEM_RHO_ID, operand2:MLKEM_Y3_BASE, operand3:MLKEM_AY0_BASE};
                MLKEM_ENCAPS_S + 37: data_o_rom <= '{opcode:ABR_UOP_MLKEM_MASKED_INTT, imm:'h0000, length:'d00, operand1:MLKEM_AY0_BASE, operand2:ABR_NOP, operand3:MLKEM_AY0_BASE};
                MLKEM_ENCAPS_S + 38: data_o_rom <= '{opcode:ABR_UOP_MLKEM_PWA, imm:'h0000, length:'d00, operand1:MLKEM_AY0_BASE, operand2:MLKEM_E2_BASE, operand3:MLKEM_U2_BASE};
                MLKEM_ENCAPS_S + 39: data_o_rom <= '{opcode:ABR_UOP_MLKEM_MASKED_REJS_PWM, imm:'h0003, length:'d34, operand1:MLKEM_RHO_ID, operand2:MLKEM_Y0_BASE, operand3:MLKEM_AY0_BASE};
                MLKEM_ENCAPS_S + 40: data_o_rom <= '{opcode:ABR_UOP_MLKEM_MASKED_REJS_PWMA, imm:'h0103, length:'d34, operand1:MLKEM_RHO_ID, operand2:MLKEM_Y1_BASE, operand3:MLKEM_AY0_BASE};
                MLKEM_ENCAPS_S + 41: data_o_rom <= '{opcode:ABR_UOP_MLKEM_MASKED_REJS_PWMA, imm:'h0203, length:'d34, operand1:MLKEM_RHO_ID, operand2:MLKEM_Y2_BASE, operand3:MLKEM_AY0_BASE};
                MLKEM_ENCAPS_S + 42: data_o_rom <= '{opcode:ABR_UOP_MLKEM_MASKED_REJS_PWMA, imm:'h0303, length:'d34, operand1:MLKEM_RHO_ID, operand2:MLKEM_Y3_BASE, operand3:MLKEM_AY0_BASE};
                MLKEM_ENCAPS_S + 43: data_o_rom <= '{opcode:ABR_UOP_MLKEM_MASKED_INTT, imm:'h0000, length:'d00, operand1:MLKEM_AY0_BASE, operand2:ABR_NOP, operand3:MLKEM_AY0_BASE};
                MLKEM_ENCAPS_S + 44: data_o_rom <= '{opcode:ABR_UOP_MLKEM_PWA, imm:'h0000, length:'d00, operand1:MLKEM_AY0_BASE, operand2:MLKEM_E3_BASE, operand3:MLKEM_U3_BASE};
                MLKEM_ENCAPS_S + 45: data_o_rom <= '{opcode:ABR_UOP_MLKEM_MASKED_PWM, imm:'h0000, length:'d00, operand1:MLKEM_T0_BASE, operand2:MLKEM_Y0_BASE, operand3:MLKEM_TY_MASKED_BASE};
                MLKEM_ENCAPS_S + 46: data_o_rom <= '{opcode:ABR_UOP_MLKEM_MASKED_PWMA, imm:'h0000, length:'d00, operand1:MLKEM_T1_BASE, operand2:MLKEM_Y1_BASE, operand3:MLKEM_TY_MASKED_BASE};
                MLKEM_ENCAPS_S + 47: data_o_rom <= '{opcode:ABR_UOP_MLKEM_MASKED_PWMA, imm:'h0000, length:'d00, operand1:MLKEM_T2_BASE, operand2:MLKEM_Y2_BASE, operand3:MLKEM_TY_MASKED_BASE};
                MLKEM_ENCAPS_S + 48: data_o_rom <= '{opcode:ABR_UOP_MLKEM_MASKED_PWMA, imm:'h0000, length:'d00, operand1:MLKEM_T3_BASE, operand2:MLKEM_Y3_BASE, operand3:MLKEM_TY_MASKED_BASE};
                MLKEM_ENCAPS_S + 49: data_o_rom <= '{opcode:ABR_UOP_MLKEM_MASKED_INTT, imm:'h0000, length:'d00, operand1:MLKEM_TY_MASKED_BASE, operand2:ABR_NOP, operand3:MLKEM_V_BASE};
                MLKEM_ENCAPS_S + 50: data_o_rom <= '{opcode:ABR_UOP_DECOMPRESS, imm:'h0100, length:'d00, operand1:MLKEM_SRC_MSG_MEM_OFFSET, operand2:ABR_NOP, operand3:MLKEM_MU_BASE};
                MLKEM_ENCAPS_S + 51: data_o_rom <= '{opcode:ABR_UOP_MLKEM_PWA, imm:'h0000, length:'d00, operand1:MLKEM_MU_BASE, operand2:MLKEM_E_2_BASE, operand3:MLKEM_E_2_BASE};
                MLKEM_ENCAPS_S + 52: data_o_rom <= '{opcode:ABR_UOP_MLKEM_PWA, imm:'h0000, length:'d00, operand1:MLKEM_V_BASE, operand2:MLKEM_E_2_BASE, operand3:MLKEM_V_BASE};
                MLKEM_ENCAPS_S + 53: data_o_rom <= '{opcode:ABR_UOP_COMPRESS, imm:'h0422, length:'d00, operand1:MLKEM_U0_BASE, operand2:ABR_NOP, operand3:MLKEM_DEST_C1_MEM_OFFSET};
                MLKEM_ENCAPS_S + 54: data_o_rom <= '{opcode:ABR_UOP_COMPRESS, imm:'h0121, length:'d00, operand1:MLKEM_V_BASE, operand2:ABR_NOP, operand3:MLKEM_DEST_C2_MEM_OFFSET};
                MLKEM_ENCAPS_E + 0 : data_o_rom <= '{opcode:ABR_UOP_NOP, imm:'h0000, length:'d00, operand1:ABR_NOP, operand2:ABR_NOP, operand3:ABR_NOP};
                MLKEM_DECAPS_CHK + 0: data_o_rom <= '{opcode:ABR_UOP_LD_SHAKE256,  imm:'h0000, length:'d32, operand1:MLKEM_SEED_Z_ID, operand2:ABR_NOP, operand3:ABR_NOP};
                MLKEM_DECAPS_CHK + 1: data_o_rom <= '{opcode:ABR_UOP_SHAKE256,  imm:'h0000, length:CT_NUM_BYTES, operand1:MLKEM_CIPHERTEXT_ID, operand2:ABR_NOP, operand3:MLKEM_DEST_K_REG_ID};
                MLKEM_DECAPS_E + 0 : data_o_rom <= '{opcode:ABR_UOP_NOP, imm:'h0000, length:'d00, operand1:ABR_NOP, operand2:ABR_NOP, operand3:ABR_NOP};

                default :              data_o_rom <= '{opcode: ABR_UOP_NOP, imm:'h0000, length:'d00, operand1:ABR_NOP, operand2:ABR_NOP, operand3:ABR_NOP};
            endcase 
    end
    else begin
        data_o_rom <= '{opcode: ABR_UOP_NOP, imm:'h0000, length:'d00, operand1:ABR_NOP, operand2:ABR_NOP, operand3:ABR_NOP};
    end
end

endmodule
