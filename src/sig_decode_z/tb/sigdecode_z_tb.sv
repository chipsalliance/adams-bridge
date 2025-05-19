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
// sigdecode_z_tb.sv
// ---------------
// Testbench for sigdecode_z_top module
//======================================================================

`default_nettype none

module sigdecode_z_tb
    import abr_params_pkg::*;
    import sigdecode_z_defines_pkg::*;
#(
    parameter REG_SIZE = 24,
    parameter MEM_ADDR_WIDTH = MLDSA_MEM_ADDR_WIDTH,
    parameter GAMMA1 = 19
)
();
localparam NUM_OF_COEFF = 256* MLDSA_L;
parameter CLK_HALF_PERIOD = 5;
parameter CLK_PERIOD = 2 * CLK_HALF_PERIOD;

//----------------------------------------------------------------
// Register and Wire declarations.
//----------------------------------------------------------------
reg clk_tb;
reg reset_n_tb;
reg zeroize_tb;
reg sigdecode_z_enable_tb;
reg [MEM_ADDR_WIDTH-1:0] src_base_addr_tb;
reg [MEM_ADDR_WIDTH-1:0] dest_base_addr_tb;
wire  [3:0][REG_SIZE-1:0] mem_a_wr_data_tb;
wire  [3:0][REG_SIZE-1:0] mem_b_wr_data_tb;
wire sigdecode_z_done_tb;
mem_if_t mem_a_wr_req_tb;
mem_if_t mem_b_wr_req_tb;
wire [3:0][19:0] sigmem_a_rd_data_tb;
wire [3:0][19:0] sigmem_b_rd_data_tb;
sig_mem_if_t sigmem_a_rd_req_tb;
sig_mem_if_t sigmem_b_rd_req_tb;


reg [19:0] input_mem [0:NUM_OF_COEFF-1];
reg [23:0] expected_output_mem [0:NUM_OF_COEFF-1];
reg [23:0] actual_output_mem [0:NUM_OF_COEFF-1];



sigdecode_z_top #(
    .MEM_ADDR_WIDTH(MEM_ADDR_WIDTH),
    .REG_SIZE(REG_SIZE),
    .GAMMA1(GAMMA1)
) dut (
    .clk(clk_tb),
    .reset_n(reset_n_tb),
    .zeroize(zeroize_tb),
    .dest_base_addr(dest_base_addr_tb),
    .mem_a_wr_req(mem_a_wr_req_tb),
    .mem_b_wr_req(mem_b_wr_req_tb),
    .mem_a_wr_data(mem_a_wr_data_tb),
    .mem_b_wr_data(mem_b_wr_data_tb),
    .sigmem_src_base_addr(src_base_addr_tb),
    .sigmem_a_rd_req(sigmem_a_rd_req_tb),
    .sigmem_b_rd_req(sigmem_b_rd_req_tb),
    .sigmem_a_rd_data(sigmem_a_rd_data_tb),
    .sigmem_b_rd_data(sigmem_b_rd_data_tb),
    .sigdecode_z_enable(sigdecode_z_enable_tb),
    .sigdecode_z_done(sigdecode_z_done_tb)
);

wire [REG_SIZE-1:0] dummy_mem_out0, dummy_mem_out1;

genvar k;
generate
    for (k = 0; k < 4; k = k +1) begin : mem_blocks
        sig_dual_port_memory #(
            .ADDR_WIDTH(MEM_ADDR_WIDTH),
            .DATA_WIDTH(REG_SIZE),
            .DEPTH(NUM_OF_COEFF)
        )
        output_memory (
            .clk(clk_tb),
            .addr_a(mem_a_wr_req_tb.addr),
            .data_in_a(mem_a_wr_data_tb[k]),
            .we_a((mem_a_wr_req_tb.rd_wr_en == RW_WRITE)),
            .data_out_a(dummy_mem_out0),
            .addr_b(mem_b_wr_req_tb.addr),
            .data_in_b(mem_b_wr_data_tb[k]),
            .we_b((mem_b_wr_req_tb.rd_wr_en == RW_WRITE)),
            .data_out_b(dummy_mem_out1)
        );
        sig_dual_port_memory #(
            .ADDR_WIDTH(MEM_ADDR_WIDTH),
            .DATA_WIDTH(GAMMA1+1),
            .DEPTH(NUM_OF_COEFF)
        )
        input_memory (
            .clk(clk_tb),
            .addr_a(sigmem_a_rd_req_tb.addr),
            .data_in_a(20'h0),
            .we_a(1'b0),
            .data_out_a(sigmem_a_rd_data_tb[k]),
            .addr_b(sigmem_b_rd_req_tb.addr),
            .data_in_b(20'h0),
            .we_b(1'b0),
            .data_out_b(sigmem_b_rd_data_tb[k])
        );
    end : mem_blocks
endgenerate

//----------------------------------------------------------------
// clk_gen
//
// Always running clock generator process.
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
        sigdecode_z_enable_tb = 0;
        src_base_addr_tb = 0;
        dest_base_addr_tb = 0;
    end
endtask

//----------------------------------------------------------------
// reset_dut()
//
// Toggle reset to put the DUT into a well known state.
//----------------------------------------------------------------
task reset_dut;
    begin
      $display("*** Toggle reset.");
      reset_n_tb = 0;
      #(3 * CLK_PERIOD);
      reset_n_tb = 1;
      $display("End of reset");
    end
endtask // reset_dut


task overwrite_memory_content(reg [MEM_ADDR_WIDTH-1:0] src_base_addr);
    int i, j;

    // Overwrite input memory with the values from input_mem
    for (i = 0; i < (NUM_OF_COEFF/4); i = i + 1) begin
        mem_blocks[0].input_memory.mem[i+src_base_addr] = input_mem[4*i + 0];
        mem_blocks[1].input_memory.mem[i+src_base_addr] = input_mem[4*i + 1];
        mem_blocks[2].input_memory.mem[i+src_base_addr] = input_mem[4*i + 2];
        mem_blocks[3].input_memory.mem[i+src_base_addr] = input_mem[4*i + 3];
    end
endtask

task read_memory_content(input reg [MEM_ADDR_WIDTH-1:0] dest_base_addr);
    int i, j;
    // Read output memory into the actual_output_mem array
    for (i = 0; i < (NUM_OF_COEFF/4); i = i + 1) begin
        actual_output_mem[4*i + 0] = mem_blocks[0].output_memory.mem[i+dest_base_addr];
        actual_output_mem[4*i + 1] = mem_blocks[1].output_memory.mem[i+dest_base_addr];
        actual_output_mem[4*i + 2] = mem_blocks[2].output_memory.mem[i+dest_base_addr];
        actual_output_mem[4*i + 3] = mem_blocks[3].output_memory.mem[i+dest_base_addr];
    end
endtask

task read_test_vectors(input reg [MEM_ADDR_WIDTH-1:0] src_base_addr);
    string input_file = "input_z.hex";
    string output_file = "output_decoded_z.hex";
    integer file, ret;
    int i;
    string line;

    // Read input file
    file = $fopen(input_file, "r");
    if (file == 0) $error("Cannot open %s for reading\n", input_file);
    i = 0;
    while (!$feof(file)) begin
        if($fgets(line,file)) begin
            ret = $sscanf(line, "%h", input_mem[i]);
            i = i + 1;
        end
    end
    $fclose(file);
    overwrite_memory_content(src_base_addr);

    // Read expected output file
    file = $fopen(output_file, "r");
    if (file == 0) $error("Cannot open %s for reading\n", output_file);
    i = 0;
    while (!$feof(file)) begin
        if($fgets(line,file)) begin
            ret = $sscanf(line, "%h", expected_output_mem[i]);
            i = i + 1;
        end
    end
    $fclose(file);
    
endtask

task sigdecode_z_test(input reg [MEM_ADDR_WIDTH-1:0] dest_base_addr, input reg [MEM_ADDR_WIDTH-1:0] src_base_addr);
    int i, j;
    $display("Starting sigdecode_z test\n");
    read_test_vectors(src_base_addr);
    @(posedge clk_tb);
    sigdecode_z_enable_tb = 1;
    src_base_addr_tb = src_base_addr;
    dest_base_addr_tb = dest_base_addr;
    @(posedge clk_tb);
    sigdecode_z_enable_tb = 0;
    src_base_addr_tb = 0;
    dest_base_addr_tb = 0;

    $display("Waiting for sigdecode_z to complete\n");
    wait (sigdecode_z_done_tb);
    read_memory_content(dest_base_addr);

    $display("Checking output data\n");
    for (i = 0; i < NUM_OF_COEFF; i = i + 1) begin
        if (actual_output_mem[i] !== expected_output_mem[i]) begin
            $display("Error: Output mismatch at index %0d. Expected: %h, Got: %h", i, expected_output_mem[i], actual_output_mem[i]);
        end
    end
    $display("Test completed\n");
endtask

initial begin
    $system($sformatf("python3 polyz_unpack.py"));
    init_sim();
    reset_dut();
    $display("Reading test vectors from hex files\n");
    sigdecode_z_test('h0,'h0);
    sigdecode_z_test('h40, 'h20);
    $finish;
end

endmodule


module sig_dual_port_memory
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

    // Port B
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

    // Port B logic
    always @(posedge clk) begin
        if (we_b) begin
            mem[addr_b] <= data_in_b;
        end
        data_out_b <= mem[addr_b];
    end

endmodule
    
