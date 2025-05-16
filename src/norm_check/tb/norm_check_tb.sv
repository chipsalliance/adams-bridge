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
// norm_check_tb.sv
// --------
// 
//
//
//======================================================================

`default_nettype none

module norm_check_tb
  import abr_params_pkg::*;
    import norm_check_defines_pkg::*;
#(
    parameter NUM_WR = 4,
    parameter NUM_RD = 4,
    parameter BUFFER_DATA_W = 8
)
();

parameter CLK_HALF_PERIOD = 5;
parameter CLK_PERIOD      = 2 * CLK_HALF_PERIOD;

parameter MLDSA_Q = 8380417;
parameter MLDSA_ETA = 2;
parameter MLDSA_TAU = 60;
parameter MLDSA_GAMMA1 = 2**19;
parameter MLDSA_GAMMA2 = (MLDSA_Q -1)/32;
parameter MLDSA_BETA = MLDSA_TAU * MLDSA_ETA;

parameter Z_BOUND = MLDSA_GAMMA1 - MLDSA_BETA;
parameter R0_BOUND = MLDSA_GAMMA2 - MLDSA_BETA;
parameter CT0_BOUND = MLDSA_GAMMA2;

//----------------------------------------------------------------
// Register and Wire declarations.
//----------------------------------------------------------------
reg           clk_tb;
reg           reset_n_tb;
reg           zeroize_tb;
reg           en_tb;
reg           shuffling_enable_tb;
reg           [5:0] randomness_tb;
reg [MLDSA_MEM_ADDR_WIDTH-1:0] src_base_tb;
wire invalid_tb;
wire norm_check_done_tb;
chk_norm_mode_t mode_tb;

parameter NUM_OF_COEFF = 256 * 7; // Adjust as per your design
parameter NUM_OF_MEM_WORDS = NUM_OF_COEFF / 4;
reg [3:0][REG_SIZE-1:0] input_mem [0:NUM_OF_MEM_WORDS-1];

mem_if_t mem_rd_req_tb;
reg [3:0][REG_SIZE-1:0] mem_rd_data_tb;

int mem_word_index;

generate
    genvar k;
    for (k = 0; k < 4; k = k +1) begin : mem_blocks
        normcheck_dual_port_memory #(
            .ADDR_WIDTH(MLDSA_MEM_ADDR_WIDTH),
            .DATA_WIDTH(REG_SIZE),
            .DEPTH(NUM_OF_MEM_WORDS)
        )
        input_memory (
            .clk(clk_tb),
            .addr_a(mem_rd_req_tb.addr),
            .data_in_a(24'h0),
            .we_a(1'b0),
            .data_out_a(mem_rd_data_tb[k]),
            .addr_b('0), // Unused
            .data_in_b(24'h0),
            .we_b(1'b0),
            .data_out_b()
        );
    end
endgenerate

norm_check_top dut(
    .clk(clk_tb),
    .reset_n(reset_n_tb),
    .zeroize(zeroize_tb),
    .norm_check_enable(en_tb),
    .shuffling_enable(shuffling_enable_tb),
    .randomness(randomness_tb),
    .mode(mode_tb),
    .mem_base_addr(src_base_tb),
    .mem_rd_req(mem_rd_req_tb),
    .mem_rd_data(mem_rd_data_tb),
    .invalid(invalid_tb),
    .norm_check_ready(),
    .norm_check_done(norm_check_done_tb)
);

//----------------------------------------------------------------
// clk_gen
//----------------------------------------------------------------
always
begin : clk_gen
  #CLK_HALF_PERIOD;
  clk_tb = !clk_tb;
end // clk_gen

task init_sim;
    begin
        $display("Start of init\n");
        clk_tb = 0;
        reset_n_tb = 0;
        zeroize_tb = 0;
        en_tb = 0;
        src_base_tb = 'h0;
        shuffling_enable_tb = '0;
    end
endtask

//----------------------------------------------------------------
// reset_dut()
//----------------------------------------------------------------
task reset_dut;
    begin
      $display("*** Toggle reset.");
      reset_n_tb = 0;

      #(2 * CLK_PERIOD);
      reset_n_tb = 1;
      #(2 * CLK_PERIOD);

      $display("End of reset");
    end
endtask // reset_dut

task overwrite_memory_content(input reg [MLDSA_MEM_ADDR_WIDTH-1:0] src_base_addr);
    int i;
    for (i = 0; i < 64; i = i + 1) begin
        mem_blocks[0].input_memory.mem[i+src_base_addr] = input_mem[i][0];
        mem_blocks[1].input_memory.mem[i+src_base_addr] = input_mem[i][1];
        mem_blocks[2].input_memory.mem[i+src_base_addr] = input_mem[i][2];
        mem_blocks[3].input_memory.mem[i+src_base_addr] = input_mem[i][3];
    end
endtask

task z_bound_norm_check_test;
  // Z_BOUND Test
  $display("Z bound mode\n");
  mode_tb = z_bound;
  src_base_tb = 'h0;

  mem_word_index = 0;
  for (int i = 0; i < 64; i++) begin
    input_mem[mem_word_index][0] = REG_SIZE'($urandom_range(0,Z_BOUND-1));
    input_mem[mem_word_index][1] = REG_SIZE'($urandom_range(MLDSA_Q-Z_BOUND, MLDSA_Q-1));
    input_mem[mem_word_index][2] = REG_SIZE'($urandom_range(0,Z_BOUND));
    input_mem[mem_word_index][3] = REG_SIZE'($urandom_range(0,Z_BOUND));
    mem_word_index = mem_word_index + 1;
  end
  overwrite_memory_content(src_base_tb);
  @(negedge clk_tb);
  en_tb = 1'b1;
  @(posedge clk_tb);
  @(negedge clk_tb);
  en_tb = 1'b0;

  repeat (2) @(posedge clk_tb);

  wait (norm_check_done_tb);
  if (invalid_tb) $error("Expected z check to be valid, received invalid\n");
  else $display("Norm check for z is successful\n");
endtask

task r0_bound_norm_check_test;
  //R0_BOUND Test
  $display("r0 bound mode\n");
  mode_tb = r0_bound;
  src_base_tb = 'h40;

  mem_word_index = 0;
  for (int i = 0; i < 64; i++) begin
    input_mem[mem_word_index][0] = REG_SIZE'($urandom_range(MLDSA_Q-R0_BOUND, MLDSA_Q-1));
    input_mem[mem_word_index][1] = REG_SIZE'($urandom_range(MLDSA_Q-R0_BOUND, MLDSA_Q-1));
    input_mem[mem_word_index][2] = REG_SIZE'($urandom_range(MLDSA_Q-R0_BOUND, MLDSA_Q-1));
    input_mem[mem_word_index][3] = REG_SIZE'($urandom_range(MLDSA_Q-R0_BOUND, MLDSA_Q-1));
    mem_word_index = mem_word_index + 1;
  end
  overwrite_memory_content(src_base_tb);
  @(negedge clk_tb);
  en_tb = 1'b1;
  @(posedge clk_tb);
  @(negedge clk_tb);
  en_tb = 1'b0;
  repeat (2) @(posedge clk_tb);

  wait (norm_check_done_tb);
  if (invalid_tb) $error("Expected r0 check to be valid, received invalid\n");
  else $display("Norm check for r0 is successful\n");

endtask

task ct0_bound_norm_check_test;
  // CT0_BOUND Test
  $display("ct0 bound mode\n");
  mode_tb = ct0_bound;
  src_base_tb = 'h80;

  mem_word_index = '0;
  for (int i = 0; i < 64; i++) begin
    input_mem[mem_word_index][0] = REG_SIZE'($urandom_range(0,CT0_BOUND-1));
    input_mem[mem_word_index][1] = REG_SIZE'($urandom_range(0,CT0_BOUND-1));
    input_mem[mem_word_index][2] = REG_SIZE'($urandom_range(0,CT0_BOUND-1));
    input_mem[mem_word_index][3] = REG_SIZE'($urandom_range(0,CT0_BOUND-1));
    mem_word_index = mem_word_index + 1;
  end
  overwrite_memory_content(src_base_tb);
  @(negedge clk_tb);
  en_tb = 1'b1;
  @(posedge clk_tb);
  @(negedge clk_tb);
  en_tb = 1'b0;
  repeat (2) @(posedge clk_tb);

  wait (norm_check_done_tb);
  if (invalid_tb) $error("Expected r0 check to be valid, received invalid\n");
  else $display("Norm check for r0 is successful\n");

endtask

task rejected_ct0_bound_norm_check_test;
  // Rejected Test
  $display("Rejected test for ct0 bound mode\n");
  mode_tb = ct0_bound;
  src_base_tb = 'hC0;

  mem_word_index = 0;
  for (int poly = 0; poly < 8; poly++) begin
      $display("Starting poly %0d", poly);
      for (int i = 0; i < 32; i++) begin
          input_mem[mem_word_index][0] = REG_SIZE'($urandom_range(0,CT0_BOUND-1));
          input_mem[mem_word_index][1] = REG_SIZE'($urandom_range(0,CT0_BOUND-1));
          input_mem[mem_word_index][2] = REG_SIZE'($urandom_range(0,CT0_BOUND-1));
          input_mem[mem_word_index][3] = REG_SIZE'($urandom_range(CT0_BOUND,MLDSA_Q-1));
          mem_word_index = mem_word_index + 1;
      end
  end
  overwrite_memory_content(src_base_tb);
  @(negedge clk_tb);
  en_tb = 1'b1;
  @(posedge clk_tb);
  @(negedge clk_tb);
  en_tb = 1'b0;
  repeat (2) @(posedge clk_tb);

  @(posedge clk_tb);
  wait (norm_check_done_tb);
  if (invalid_tb) $display("Norm check for ct0 is rejected as expected\n");
  else $error("Expected ct0 check to be invalid, received valid\n");

endtask

task rejected_z_bound_norm_check_test;
  // Z_BOUND Test
  $display("Z bound mode\n");
  mode_tb = z_bound;
  src_base_tb = 'h0;

  mem_word_index = 0;
  for (int i = 0; i < 64; i++) begin
    input_mem[mem_word_index][0] = REG_SIZE'($urandom_range(0,Z_BOUND-1));
    input_mem[mem_word_index][1] = REG_SIZE'($urandom_range(MLDSA_Q-Z_BOUND, MLDSA_Q-1));
    input_mem[mem_word_index][2] = REG_SIZE'($urandom_range(0,Z_BOUND));
    if (i==63) begin
      input_mem[mem_word_index][3] = REG_SIZE'($urandom_range(Z_BOUND,MLDSA_Q-Z_BOUND));
    end 
    else begin
      input_mem[mem_word_index][3] = REG_SIZE'($urandom_range(0,Z_BOUND));
    end
    mem_word_index = mem_word_index + 1;
  end
  overwrite_memory_content(src_base_tb);
  @(negedge clk_tb);
  en_tb = 1'b1;
  @(posedge clk_tb);
  @(negedge clk_tb);
  en_tb = 1'b0;

  repeat (2) @(posedge clk_tb);

  wait (norm_check_done_tb);
  if (invalid_tb) $display("Norm check for z is rejected as expected\n");
  else $error("Expected z check to be invalid, received valid\n");
endtask

task rejected_r0_bound_norm_check_test;
  //R0_BOUND Test
  $display("r0 bound mode\n");
  mode_tb = r0_bound;
  src_base_tb = 'h40;

  mem_word_index = 0;
  for (int i = 0; i < 64; i++) begin
    if (i==0)
      input_mem[mem_word_index][0] = REG_SIZE'($urandom_range(0, MLDSA_Q-R0_BOUND-1));
    else
      input_mem[mem_word_index][0] = REG_SIZE'($urandom_range(MLDSA_Q-R0_BOUND, MLDSA_Q-1));
    input_mem[mem_word_index][1] = REG_SIZE'($urandom_range(MLDSA_Q-R0_BOUND, MLDSA_Q-1));
    input_mem[mem_word_index][2] = REG_SIZE'($urandom_range(MLDSA_Q-R0_BOUND, MLDSA_Q-1));
    input_mem[mem_word_index][3] = REG_SIZE'($urandom_range(MLDSA_Q-R0_BOUND, MLDSA_Q-1));
    mem_word_index = mem_word_index + 1;
  end
  overwrite_memory_content(src_base_tb);
  @(negedge clk_tb);
  en_tb = 1'b1;
  @(posedge clk_tb);
  @(negedge clk_tb);
  en_tb = 1'b0;
  repeat (2) @(posedge clk_tb);

  wait (norm_check_done_tb);
  if (invalid_tb) $display("Norm check for r0 is rejected as expected\n");
  else $error("Expected r0 check to be invalid, received valid\n");

endtask

task randomized_rejected_r0_bound_norm_check_test;
  //R0_BOUND Test
  int inner_index;
  mode_tb = r0_bound;
  src_base_tb = $urandom_range(0, 127);
  repeat (3) @(posedge clk_tb);

  mem_word_index = 0;
  for (int i = 0; i < 64; i++) begin
    input_mem[mem_word_index][0] = REG_SIZE'($urandom_range(MLDSA_Q-R0_BOUND, MLDSA_Q-1));
    input_mem[mem_word_index][1] = REG_SIZE'($urandom_range(MLDSA_Q-R0_BOUND, MLDSA_Q-1));
    input_mem[mem_word_index][2] = REG_SIZE'($urandom_range(MLDSA_Q-R0_BOUND, MLDSA_Q-1));
    input_mem[mem_word_index][3] = REG_SIZE'($urandom_range(MLDSA_Q-R0_BOUND, MLDSA_Q-1));
    mem_word_index = mem_word_index + 1;
  end
  mem_word_index = $urandom_range(0, 63);
  inner_index = $urandom_range(0, 3);
  input_mem[mem_word_index][inner_index] = REG_SIZE'($urandom_range(R0_BOUND, MLDSA_Q-R0_BOUND-1));

  overwrite_memory_content(src_base_tb);
  @(negedge clk_tb);
  en_tb = 1'b1;
  @(posedge clk_tb);
  @(negedge clk_tb);
  en_tb = 1'b0;
  repeat (2) @(posedge clk_tb);

  wait (norm_check_done_tb);
  if (!invalid_tb) begin
    $display("The incorrect range (%x) is inserted in %d and %d\n",input_mem[mem_word_index][inner_index], mem_word_index, inner_index );
    $error("Expected r0 check to be invalid, received valid at %t\n", $time);
  end

endtask

task randomized_ct0_bound_norm_check_test;
  // CT0_BOUND Test
  mode_tb = ct0_bound;
  src_base_tb = $urandom_range(0, 127);
  repeat (3) @(posedge clk_tb);

  mem_word_index = '0;
  for (int i = 0; i < 64; i++) begin
    input_mem[mem_word_index][0] = REG_SIZE'($urandom_range(0,CT0_BOUND-1));
    input_mem[mem_word_index][1] = REG_SIZE'($urandom_range(0,CT0_BOUND-1));
    input_mem[mem_word_index][2] = REG_SIZE'($urandom_range(0,CT0_BOUND-1));
    input_mem[mem_word_index][3] = REG_SIZE'($urandom_range(0,CT0_BOUND-1));
    mem_word_index = mem_word_index + 1;
  end
  overwrite_memory_content(src_base_tb);
  @(negedge clk_tb);
  en_tb = 1'b1;
  @(posedge clk_tb);
  @(negedge clk_tb);
  en_tb = 1'b0;
  repeat (2) @(posedge clk_tb);

  wait (norm_check_done_tb);
  if (invalid_tb) $error("Expected r0 check to be valid, received invalid\n");

endtask

task norm_check_test;
    $display("Starting check norm ctrl test\n");
    z_bound_norm_check_test();
    repeat (2) @(posedge clk_tb);
    r0_bound_norm_check_test();
    repeat (2) @(posedge clk_tb);
    ct0_bound_norm_check_test();
    repeat (2) @(posedge clk_tb);
    rejected_ct0_bound_norm_check_test();
    repeat (2) @(posedge clk_tb);
    rejected_z_bound_norm_check_test();
    repeat (2) @(posedge clk_tb);
    rejected_r0_bound_norm_check_test();
    repeat (10000) randomized_rejected_r0_bound_norm_check_test();
    repeat (10000) randomized_ct0_bound_norm_check_test();
    $display("Ctrl test done\n");
endtask

initial begin
  fork
    begin
      init_sim();
      reset_dut();
      shuffling_enable_tb = '0;
      norm_check_test();
      shuffling_enable_tb = '1;
      norm_check_test();
    end
    begin
      while(1) begin
        @(posedge clk_tb);
        randomness_tb =  $urandom_range(0,64);
      end
    end
  join_any
    $finish;
end

endmodule

// Memory module definition (normcheck_dual_port_memory)
module normcheck_dual_port_memory
#(
    parameter ADDR_WIDTH = 15,
    parameter DATA_WIDTH = 32,
    parameter DEPTH = 256
)
(
    input wire clk,
    
    // Port A
    input wire [ADDR_WIDTH-1:0] addr_a,
    input wire [DATA_WIDTH-1:0] data_in_a,
    input wire we_a,  // Write enable for port A
    output reg [DATA_WIDTH-1:0] data_out_a,

    // Port B (Unused in this testbench)
    input wire [ADDR_WIDTH-1:0] addr_b,
    input wire [DATA_WIDTH-1:0] data_in_b,
    input wire we_b,  // Write enable for port B
    output reg [DATA_WIDTH-1:0] data_out_b
);

    // Memory array
    reg [DATA_WIDTH-1:0] mem [0:DEPTH-1];

    // Port A logic
    always @(posedge clk) begin
        if (we_a) begin
            mem[addr_a] <= data_in_a;
        end
        data_out_a <= mem[addr_a];
    end

    // Port B logic (Unused)
    always @(posedge clk) begin
        if (we_b) begin
            mem[addr_b] <= data_in_b;
        end
        data_out_b <= mem[addr_b];
    end

endmodule