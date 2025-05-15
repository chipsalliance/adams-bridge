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

module mldsa_seq_sec
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
                MLDSA_RESET : data_o_rom <= '{opcode:MLDSA_UOP_NOP, imm:'h0000, length:'d00, operand1:MLDSA_NOP, operand2:MLDSA_NOP, operand3:MLDSA_NOP};

                default : data_o_rom <= '{opcode: MLDSA_UOP_NOP, imm:'h0000, length:'d00, operand1:MLDSA_NOP, operand2:MLDSA_NOP, operand3:MLDSA_NOP};
            endcase 
    end
    else begin
        data_o_rom <= '{opcode: MLDSA_UOP_NOP, imm:'h0000, length:'d00, operand1:MLDSA_NOP, operand2:MLDSA_NOP, operand3:MLDSA_NOP};
    end
end

endmodule