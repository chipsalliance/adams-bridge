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

//Sequencer for MLKEM
//MLKEM functions
//  Keygen
//  Encaps
//  Decaps

module mlkem_seq
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
 
//FIXME todo, remove MLDSA references

  always_ff @(posedge clk) begin
        if (en_i) begin
            unique case(addr_i)
                //RESET
                MLKEM_RESET    : data_o_rom <= '{opcode:ABR_UOP_NOP, imm:'h0000, length:'d00, operand1:ABR_NOP, operand2:ABR_NOP, operand3:ABR_NOP};
                //MLKEM Keygen
                MLKEM_KG_S + 0 : data_o_rom <= '{opcode:ABR_UOP_SHA512, imm:'h0004, length:'d33, operand1:MLKEM_SEED_D_ID, operand2:ABR_NOP, operand3:MLKEM_DEST_RHO_SIGMA_REG_ID};
                MLKEM_KG_S + 1 : data_o_rom <= '{opcode:ABR_UOP_CBD, imm:'h0000, length:'d33, operand1:MLKEM_SIGMA_ID, operand2:ABR_NOP, operand3:MLKEM_S0_BASE};
                MLKEM_KG_S + 2 : data_o_rom <= '{opcode:ABR_UOP_CBD, imm:'h0001, length:'d33, operand1:MLKEM_SIGMA_ID, operand2:ABR_NOP, operand3:MLKEM_S1_BASE};
                MLKEM_KG_S + 3 : data_o_rom <= '{opcode:ABR_UOP_CBD, imm:'h0002, length:'d33, operand1:MLKEM_SIGMA_ID, operand2:ABR_NOP, operand3:MLKEM_S2_BASE};
                MLKEM_KG_S + 4 : data_o_rom <= '{opcode:ABR_UOP_CBD, imm:'h0003, length:'d33, operand1:MLKEM_SIGMA_ID, operand2:ABR_NOP, operand3:MLKEM_S3_BASE};
                MLKEM_KG_S + 5 : data_o_rom <= '{opcode:ABR_UOP_CBD, imm:'h0004, length:'d33, operand1:MLKEM_SIGMA_ID, operand2:ABR_NOP, operand3:MLKEM_E0_BASE};
                MLKEM_KG_S + 6 : data_o_rom <= '{opcode:ABR_UOP_CBD, imm:'h0005, length:'d33, operand1:MLKEM_SIGMA_ID, operand2:ABR_NOP, operand3:MLKEM_E1_BASE};
                MLKEM_KG_S + 7 : data_o_rom <= '{opcode:ABR_UOP_CBD, imm:'h0006, length:'d33, operand1:MLKEM_SIGMA_ID, operand2:ABR_NOP, operand3:MLKEM_E2_BASE};
                MLKEM_KG_S + 8 : data_o_rom <= '{opcode:ABR_UOP_CBD, imm:'h0007, length:'d33, operand1:MLKEM_SIGMA_ID, operand2:ABR_NOP, operand3:MLKEM_E3_BASE};
                MLKEM_KG_S + 9 : data_o_rom <= '{opcode:ABR_UOP_NTT, imm:'h0000, length:'d00, operand1:MLKEM_S0_BASE, operand2:ABR_NOP, operand3:MLKEM_S0_BASE};
                MLKEM_KG_S + 10: data_o_rom <= '{opcode:ABR_UOP_NTT, imm:'h0000, length:'d00, operand1:MLKEM_S1_BASE, operand2:ABR_NOP, operand3:MLKEM_S1_BASE};
                MLKEM_KG_S + 11: data_o_rom <= '{opcode:ABR_UOP_NTT, imm:'h0000, length:'d00, operand1:MLKEM_S2_BASE, operand2:ABR_NOP, operand3:MLKEM_S2_BASE};
                MLKEM_KG_S + 12: data_o_rom <= '{opcode:ABR_UOP_NTT, imm:'h0000, length:'d00, operand1:MLKEM_S3_BASE, operand2:ABR_NOP, operand3:MLKEM_S3_BASE};
                MLKEM_KG_S + 13: data_o_rom <= '{opcode:ABR_UOP_NTT, imm:'h0000, length:'d00, operand1:MLKEM_E0_BASE, operand2:ABR_NOP, operand3:MLKEM_E0_BASE};
                MLKEM_KG_S + 14: data_o_rom <= '{opcode:ABR_UOP_NTT, imm:'h0000, length:'d00, operand1:MLKEM_E1_BASE, operand2:ABR_NOP, operand3:MLKEM_E1_BASE};
                MLKEM_KG_S + 15: data_o_rom <= '{opcode:ABR_UOP_NTT, imm:'h0000, length:'d00, operand1:MLKEM_E2_BASE, operand2:ABR_NOP, operand3:MLKEM_E2_BASE};
                MLKEM_KG_S + 16: data_o_rom <= '{opcode:ABR_UOP_NTT, imm:'h0000, length:'d00, operand1:MLKEM_E3_BASE, operand2:ABR_NOP, operand3:MLKEM_E3_BASE};
                MLKEM_KG_S + 17: data_o_rom <= '{opcode:ABR_UOP_MLKEM_REJS_PWM , imm:'h0000, length:'d34, operand1:MLKEM_RHO_ID, operand2:MLKEM_S0_BASE, operand3:MLKEM_AS0_BASE};
                MLKEM_KG_S + 18: data_o_rom <= '{opcode:ABR_UOP_MLKEM_REJS_PWMA, imm:'h0001, length:'d34, operand1:MLKEM_RHO_ID, operand2:MLKEM_S1_BASE, operand3:MLKEM_AS0_BASE};
                MLKEM_KG_S + 19: data_o_rom <= '{opcode:ABR_UOP_MLKEM_REJS_PWMA, imm:'h0002, length:'d34, operand1:MLKEM_RHO_ID, operand2:MLKEM_S2_BASE, operand3:MLKEM_AS0_BASE};
                MLKEM_KG_S + 20: data_o_rom <= '{opcode:ABR_UOP_MLKEM_REJS_PWMA, imm:'h0003, length:'d34, operand1:MLKEM_RHO_ID, operand2:MLKEM_S3_BASE, operand3:MLKEM_AS0_BASE};
                MLKEM_KG_S + 21: data_o_rom <= '{opcode:ABR_UOP_PWA            , imm:'h0000, length:'d00, operand1:MLKEM_AS0_BASE, operand2:MLKEM_E0_BASE, operand3:MLKEM_T0_BASE};
                MLKEM_KG_S + 22: data_o_rom <= '{opcode:ABR_UOP_MLKEM_REJS_PWM , imm:'h0100, length:'d00, operand1:MLKEM_RHO_ID, operand2:MLKEM_S0_BASE, operand3:MLKEM_AS0_BASE};
                MLKEM_KG_S + 23: data_o_rom <= '{opcode:ABR_UOP_MLKEM_REJS_PWMA, imm:'h0101, length:'d00, operand1:MLKEM_RHO_ID, operand2:MLKEM_S1_BASE, operand3:MLKEM_AS0_BASE};
                MLKEM_KG_S + 24: data_o_rom <= '{opcode:ABR_UOP_MLKEM_REJS_PWMA, imm:'h0102, length:'d00, operand1:MLKEM_RHO_ID, operand2:MLKEM_S2_BASE, operand3:MLKEM_AS0_BASE};
                MLKEM_KG_S + 25: data_o_rom <= '{opcode:ABR_UOP_MLKEM_REJS_PWMA, imm:'h0103, length:'d00, operand1:MLKEM_RHO_ID, operand2:MLKEM_S3_BASE, operand3:MLKEM_AS0_BASE};
                MLKEM_KG_S + 26: data_o_rom <= '{opcode:ABR_UOP_PWA,             imm:'h0000, length:'d00, operand1:MLKEM_AS0_BASE, operand2:MLKEM_E1_BASE, operand3:MLKEM_T1_BASE};
                MLKEM_KG_S + 27: data_o_rom <= '{opcode:ABR_UOP_MLKEM_REJS_PWM , imm:'h0200, length:'d00, operand1:MLKEM_RHO_ID, operand2:MLKEM_S0_BASE, operand3:MLKEM_AS0_BASE};
                MLKEM_KG_S + 28: data_o_rom <= '{opcode:ABR_UOP_MLKEM_REJS_PWMA, imm:'h0201, length:'d00, operand1:MLKEM_RHO_ID, operand2:MLKEM_S1_BASE, operand3:MLKEM_AS0_BASE};
                MLKEM_KG_S + 29: data_o_rom <= '{opcode:ABR_UOP_MLKEM_REJS_PWMA, imm:'h0202, length:'d00, operand1:MLKEM_RHO_ID, operand2:MLKEM_S2_BASE, operand3:MLKEM_AS0_BASE};
                MLKEM_KG_S + 30: data_o_rom <= '{opcode:ABR_UOP_MLKEM_REJS_PWMA, imm:'h0203, length:'d00, operand1:MLKEM_RHO_ID, operand2:MLKEM_S3_BASE, operand3:MLKEM_AS0_BASE};
                MLKEM_KG_S + 31: data_o_rom <= '{opcode:ABR_UOP_PWA,             imm:'h0000, length:'d00, operand1:MLKEM_AS0_BASE, operand2:MLKEM_E2_BASE, operand3:MLKEM_T2_BASE};
                MLKEM_KG_S + 32: data_o_rom <= '{opcode:ABR_UOP_MLKEM_REJS_PWM , imm:'h0300, length:'d00, operand1:MLKEM_RHO_ID, operand2:MLKEM_S0_BASE, operand3:MLKEM_AS0_BASE};
                MLKEM_KG_S + 33: data_o_rom <= '{opcode:ABR_UOP_MLKEM_REJS_PWMA, imm:'h0301, length:'d00, operand1:MLKEM_RHO_ID, operand2:MLKEM_S1_BASE, operand3:MLKEM_AS0_BASE};
                MLKEM_KG_S + 34: data_o_rom <= '{opcode:ABR_UOP_MLKEM_REJS_PWMA, imm:'h0302, length:'d00, operand1:MLKEM_RHO_ID, operand2:MLKEM_S2_BASE, operand3:MLKEM_AS0_BASE};
                MLKEM_KG_S + 35: data_o_rom <= '{opcode:ABR_UOP_MLKEM_REJS_PWMA, imm:'h0303, length:'d00, operand1:MLKEM_RHO_ID, operand2:MLKEM_S3_BASE, operand3:MLKEM_AS0_BASE};
                MLKEM_KG_S + 36: data_o_rom <= '{opcode:ABR_UOP_PWA,             imm:'h0000, length:'d00, operand1:MLKEM_AS0_BASE, operand2:MLKEM_E3_BASE, operand3:MLKEM_T3_BASE};
                MLKEM_KG_S + 37: data_o_rom <= '{opcode:ABR_UOP_BYTE_ENC, imm:'h0000, length:'d00, operand1:MLKEM_T0_BASE, operand2:ABR_NOP, operand3:MLKEM_DEST_EK_MEM_ID};
                MLKEM_KG_S + 38: data_o_rom <= '{opcode:ABR_UOP_BYTE_ENC, imm:'h0000, length:'d00, operand1:MLKEM_S0_BASE, operand2:ABR_NOP, operand3:MLKEM_DEST_DK_MEM_ID};
                MLKEM_KG_S + 39: data_o_rom <= '{opcode:ABR_UOP_SHA256, imm:'h0000, length:EK_NUM_BYTES, operand1:MLKEM_EK_REG_ID, operand2:ABR_NOP, operand3:MLKEM_DEST_TR_REG_ID};


                
                default : data_o_rom <= '{opcode: ABR_UOP_NOP, imm:'h0000, length:'d00, operand1:ABR_NOP, operand2:ABR_NOP, operand3:ABR_NOP};
            endcase 
    end
    else begin
        data_o_rom <= '{opcode: ABR_UOP_NOP, imm:'h0000, length:'d00, operand1:ABR_NOP, operand2:ABR_NOP, operand3:ABR_NOP};
    end
end

endmodule