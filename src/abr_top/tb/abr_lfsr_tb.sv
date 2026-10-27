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

module abr_lfsr_tb;
  timeunit 1ns;
  timeprecision 1ps;
  import abr_ctrl_pkg::*;

  bit clk = 0;
  bit rst_b = 0;
  bit seed_en = 0;
  bit lfsr_en = 0;
  logic [63:0] seed;
  logic [63:0] state;
  logic [ABR_PROG_ADDR_W-1:0] addr;
  abr_seq_instr_t instr;
  int state_checks = 0;
  int rom_checks = 0;
  int samples = 0;
  string fault = "";

  always #5 clk = !clk;

  abr_prim_lfsr #(
    .LfsrType("FIB_XNOR"),
    .LfsrDw(ABR_LFSR_W),
    .StateOutDw(ABR_LFSR_W)
  ) dut (
    .clk_i(clk), .rst_b(rst_b),
    .seed_en_i(seed_en), .seed_i(seed),
    .lfsr_en_i(lfsr_en), .entropy_i(8'b0), .state_o(state)
  );

  abr_seq seq (.clk(clk), .en_i(1'b1), .addr_i(addr), .data_o(instr));

  // Independent 64-bit recurrence: taps 64, 63, 61, 60, not the DUT's LUT/helper.
  function automatic logic [63:0] next_state(input logic [63:0] current);
    if (&current) return 64'h1;
    return {current[62:0], ~(current[63] ^ current[62] ^ current[60] ^ current[59])};
  endfunction

  task automatic check_state(input logic [63:0] expected);
    logic [63:0] observed;
    observed = state;
    samples++;
    // These controls corrupt one channel at the checker boundary, not its verdict.
    if (samples == 8) begin
      case (fault)
        "actual": observed[0] = ~observed[0];
        "expected": expected[0] = ~expected[0];
        "unknown": observed[0] = 1'bx;
        default: ;
      endcase
    end
    if (!(fault == "missing" && samples == 8)) begin
      if ($isunknown(observed) || observed !== expected)
        $fatal(1, "LFSR mismatch sample %0d: expected %h observed %h", samples, expected, observed);
      state_checks++;
    end
  endtask

  task automatic check_prologue(input logic [ABR_PROG_ADDR_W-1:0] start_addr);
    abr_seq_instr_t expected;
    for (int step = 0; step < 5; step++) begin
      expected = '{opcode:ABR_UOP_LFSR, imm:'0, length:'0,
                   operand1:ABR_NOP, operand2:ABR_NOP, operand3:ABR_NOP};
      if (step < 4) begin
        if (step % 2 == 0) begin
          expected.opcode = ABR_UOP_LD_SHAKE256;
          expected.length = 64;
          expected.operand1 = ABR_ENTROPY_ID;
        end else begin
          expected.opcode = ABR_UOP_SHAKE256;
          expected.length = 8;
          expected.operand1 = ABR_CNT_ID;
          case (step)
            1: expected.operand3 = ABR_DEST_ENTROPY_REG_ID;
            3: expected.operand3 = ABR_DEST_LFSR_SEED_REG_ID;
            default: $fatal(1, "Invalid prologue step");
          endcase
        end
      end
      @(negedge clk);
      addr = start_addr + ABR_PROG_ADDR_W'(step);
      @(posedge clk);
      #1;
      if (instr !== expected)
        $fatal(1, "Prologue mismatch at address %0d: expected %h observed %h", addr, expected, instr);
      rom_checks++;
    end
  endtask

  initial begin : run
    logic [63:0] expected;
    logic [63:0] seeds [5] = '{64'h0, 64'h1, 64'hffff_ffff_ffff_ffff,
                              64'h3468_d1a3_468d_1a34, 64'h8000_0000_0000_0000};
    if ($value$plusargs("LFSR_FAULT=%s", fault) &&
        !(fault inside {"actual", "expected", "missing", "unknown"}))
      $fatal(1, "Unsupported LFSR_FAULT=%s", fault);
    if (ABR_LFSR_W != 64 || NTT_LFSR_W != 64 ||
        KECCAK_DOM_LFSR_DW != 64 || KECCAK_MSG_LFSR_W != 64 ||
        NTT_NUM_LFSR != 4 || KECCAK_DOM_NUM_LFSR != 13 ||
        NTT_RAND_W < 102 || KECCAK_DOM_LFSR_W < 801 ||
        SHAKE256_RATE_W != 1088 || ENTROPY_LSB != 0 || ENTROPY_W != 512 ||
        NTT_SEED_LSB != 512 || NTT_SEED_W != 256 ||
        NTT_SEED_LSB + NTT_SEED_W > SHAKE256_RATE_W ||
        DOM_SEED_LSB != 0 || MSG_SEED_LSB != 832 ||
        MSG_SEED_LSB + KECCAK_MSG_LFSR_W > SHAKE256_RATE_W ||
        $bits(abr_lfsr_seed_t) != 1152)
      $fatal(1, "Invalid 64-bit bank or rate-only seed layout");
    repeat (2) @(negedge clk);
    if (state !== 64'h1) $fatal(1, "Invalid reset state");
    rst_b = 1;

    check_prologue(MLDSA_KG_S);
    check_prologue(MLDSA_SIGN_S);
    check_prologue(MLDSA_SIGN_LFSR_S);
    check_prologue(MLKEM_KG_S);
    check_prologue(MLKEM_DECAPS_S);
    check_prologue(MLKEM_ENCAPS_S);

    foreach (seeds[i]) begin
      @(negedge clk);
      seed = seeds[i];
      seed_en = 1;
      lfsr_en = 0; // Seed load must take priority even with stepping disabled.
      @(posedge clk);
      #1;
      expected = seeds[i];
      check_state(expected);
      @(negedge clk);
      seed_en = 0;
      @(posedge clk);
      #1;
      check_state(expected);
      @(negedge clk);
      lfsr_en = 1;
      repeat (256) begin
        @(posedge clk);
        #1;
        expected = next_state(expected);
        check_state(expected);
      end
    end
    if (state_checks != 1290 || rom_checks != 30)
      $fatal(1, "Incomplete checks: state=%0d/1290 ROM=%0d/30", state_checks, rom_checks);
    $display("LFSR64 completed: state_checks=%0d rom_checks=%0d", state_checks, rom_checks);
    $display("* TESTCASE PASSED");
    $finish;
  end

  initial begin
    #100000;
    $fatal(1, "LFSR64 test timeout");
  end
endmodule
