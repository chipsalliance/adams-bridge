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
// decompose_tb.sv
// --------
// 
//
//
//======================================================================

`default_nettype none
`include "caliptra_reg_defines.svh"

module decompose_tb
    import decompose_defines_pkg::*;
#(
    parameter NUM_WR = 4, //TODO: sample_buffer needs more writes than reads?
    parameter NUM_RD = 4,
    parameter BUFFER_DATA_W = 8,
    parameter REG_SIZE = 24,
    parameter MEM_ADDR_WIDTH = 15
) 
();

parameter CLK_HALF_PERIOD = 5;
parameter CLK_PERIOD      = 2 * CLK_HALF_PERIOD;

//----------------------------------------------------------------
// Register and Wire declarations.
//----------------------------------------------------------------
reg           clk_tb;
reg           reset_n_tb;
reg           cptra_pwrgood_tb;
reg           zeroize_tb;
reg           en_tb;
reg [4*REG_SIZE-1:0] coeff_tb, mem_wr_data_o;
reg [MEM_ADDR_WIDTH-1:0] src_base_tb, dest_base_tb;
reg r0_rdy_tb;
logic [255:0][REG_SIZE-1:0] coeff_array, coeff_high, coeff_low;
logic [3:0][3:0] coeff_high_tb;
logic kdone_tb;
decompose dut(
    .clk(clk_tb),
    .reset_n(reset_n_tb),
    .zeroize(zeroize_tb),
    .decompose_enable(en_tb),
    .src_base_addr(src_base_tb),
    .dest_base_addr(dest_base_tb),
    .mem_rd_req(),
    .mem_wr_req(),
    .mem_rd_data(coeff_tb),
    .mem_wr_data(mem_wr_data_o),
    .z_mem_wr_req(),
    .z_neq_z(),
    .w1_o(),
    .buffer_en(),
    .keccak_en(),
    .decompose_done(),
    .w1_encode_done(),
    .keccak_done(kdone_tb)
);

// w1_encode dut(
//     .clk(clk_tb),
//     .reset_n(reset_n_tb),
//     .zeroize(zeroize_tb),
//     .w1_encode_enable(en_tb),
//     .r1_i(coeff_high_tb),
//     .w1_o(),
//     .buffer_en(),
//     .keccak_en(),
//     .w1_encode_done(),
//     .keccak_done(kdone_tb)
// );

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
        cptra_pwrgood_tb = 0;
        // hint_4bit_tb = 0;
        // index_tb = 0;
        zeroize_tb = 0;
        en_tb = 0;
        coeff_tb = 0;
        src_base_tb = 'h0;
        dest_base_tb = 'h0;
        r0_rdy_tb = 'b0;
        coeff_high_tb = 'h0;
        kdone_tb = 'b0;
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
    //   cptra_pwrgood_tb = '0;
      reset_n_tb = 0;
    
    //   #(2 * CLK_PERIOD);
    //   cptra_pwrgood_tb = 1;
    
      #(2 * CLK_PERIOD);
      reset_n_tb = 1;
    
      $display("End of reset");
    end
endtask // reset_dut


task r1_lut_test;
    $display("Starting r1 lut test\n");
    @(posedge clk_tb);
    en_tb = 1;
    @(posedge clk_tb);
    // en_tb = 0; //comment back in for r1_lut_test
    // @(posedge clk_tb);
    for (int poly = 0; poly < 8; poly++) begin
        $display("Starting Poly %0d", poly);
            for (int i = 0; i < 64; i++) begin
                coeff_tb = REG_SIZE'($random);
                @(posedge clk_tb);
            end
    end
    @(posedge clk_tb);
    $display("Test done\n");
endtask

task ctrl_test;
    $display("Starting decompose ctrl test\n");
    @(posedge clk_tb);
    en_tb = 1'b1;
    @(posedge clk_tb);
    en_tb = 1'b0;
    src_base_tb = 'h0;
    dest_base_tb = 'h40;
    r0_rdy_tb = 1'b1;
endtask

task read_test_vectors();
    string fname = "test_vector.hex";
    integer file;
    string line;
    integer i, ret;

    i = 0;
    file = $fopen(fname, "r");
    if (file == 0) $error("Cannot open %s for reading\n", fname);
    
    while (!$feof(file)) begin
        if($fgets(line,file)) begin
            ret = $sscanf(line, "%h %h %h", coeff_array[i], coeff_high[i], coeff_low[i]);
            i = i+1;
        end
    end
    $fclose(file);
endtask

task dcmp_test;
    $display("Reading hex file\n");
    read_test_vectors();

    $display("Starting dcmp test\n");
    @(posedge clk_tb);
    en_tb = 1;
    @(posedge clk_tb);
    en_tb = 1'b0;
    src_base_tb = 'h0;
    dest_base_tb = 'h40;
    fork
        
    begin
        for (int poly = 0; poly < 1; poly++) begin
            $display("Starting Poly %0d", poly);
            for (int i = 0; i < 256; i=i+4) begin
                coeff_tb <= {coeff_array[i+3], coeff_array[i+2], coeff_array[i+1], coeff_array[i]}; //{{1'b0,(REG_SIZE-1)'($random)}, {1'b0,(REG_SIZE-1)'($random)}, {1'b0,(REG_SIZE-1)'($random)}, {1'b0,(REG_SIZE-1)'($random)}};
                @(posedge clk_tb);
            end
        end
        @(posedge clk_tb);
    end
    begin
        @(posedge clk_tb); //wait for mod_ready to go high
        while(dut.mod_ready != 'hf) @(posedge clk_tb);
        for(int i = 0; i < 256; i = i+4) begin
            if (dut.r1_reg[i%4] != coeff_high[i])
                $error("r1 does not match. Expected = %h, observed = %h\n", coeff_high[i], dut.r1_reg[i%4]);
            if (mem_wr_data_o != {coeff_low[i+3], coeff_low[i+2], coeff_low[i+1], coeff_low[i]})
                $error("r0 does not match. Expected = %h %h %h %h, observed = %h %h %h %h\n", coeff_low[i+3], coeff_low[i+2], coeff_low[i+1], coeff_low[i], dut.r0[3], dut.r0[2], dut.r0[1], dut.r0[0]);
            @(posedge clk_tb);
        end
    end
    join
    
    //Wait for decompose done (i.e., w1 encode done)
    //Then wait for a fixed time to emulate keccak done and assert it
    while(dut.decompose_done != 1) @(posedge clk_tb);
    repeat(100) @(posedge clk_tb);
    kdone_tb = 'b1; //emulate keccak done
    @(posedge clk_tb);
    kdone_tb = 'b0;
    $display("Test done\n");
endtask 

task encode_test;

    $display("Reading hex file\n");
    read_test_vectors();
    
    $display("Starting w1 encode test\n");
    @(posedge clk_tb);
    en_tb <= 1;
    for (int poly = 0; poly < 8; poly++) begin
        $display("Starting Poly %0d", poly);
        for (int i = 0; i < 256; i = i+4) begin
            coeff_high_tb <= {$random, $random, $random, $random}; //{coeff_high[i+3], coeff_high[i+2], coeff_high[i+1], coeff_high[i]};
            @(posedge clk_tb);
        end
        // @(posedge clk_tb);
        if (poly == 7) en_tb <= 1'b0;
    end
    

    kdone_tb <= 'b1;
    @(posedge clk_tb);
    kdone_tb <= 'b0;
    $display("Test done\n");
endtask


initial begin
    init_sim();
    reset_dut();
    // sample_buffer_test();
    // r1_lut_test();
    // ctrl_test();
    dcmp_test();
    // encode_test();
    repeat(1000) @(posedge clk_tb);
    $finish;
end
endmodule