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
// makehint_tb.sv
// --------
// 
//
//
//======================================================================

`default_nettype none

module makehint_tb
    import makehint_defines_pkg::*;
    import mldsa_params_pkg::*;
#(
    parameter NUM_WR = 4,
    parameter NUM_RD = 4,
    parameter BUFFER_DATA_W = 8,
    parameter REG_SIZE = 24
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
reg [(4*24)-1:0] coeff_tb;
reg [NUM_WR-1:0] z_tb;
reg [NUM_WR-1:0] hint_4bit_tb;
reg [NUM_WR-1:0][BUFFER_DATA_W] index_tb;
reg [(64*8)-1:0][4*REG_SIZE-1:0] coeff_array; //8 polys with 64 addr each
reg [(64*8)-1:0][3:0] z_array;



makehint #(
    .BUFFER_DATA_W(BUFFER_DATA_W)
) dut (
    .clk(clk_tb),
    .reset_n(reset_n_tb),
    .zeroize(zeroize_tb),
    .makehint_enable(en_tb),
    .r(coeff_tb),
    .z(z_tb),
    .mem_base_addr(MLDSA_MEM_ADDR_WIDTH'(0)),
    .dest_base_addr(MLDSA_MEM_ADDR_WIDTH'(0)),
    .invalid_h(),
    .mem_rd_req(),
    .z_rd_req(),
    .makehint_done(),
    .reg_wren(),
    .reg_wrdata(),
    .reg_wr_addr()

);

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
        z_tb = 0;
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


task read_test_vectors();
    string fname;
    integer file;
    string line;
    integer i, ret, j;

    for (j = 0; j < 2; j++) begin
        i = 0;
        if (j == 0) begin
            $display("reading coeffs\n");
            fname = "r.hex";
        end
        else if (j == 1) begin
            $display("reading z vector\n");
            fname = "z.hex";
        end

        file = $fopen(fname, "r");
        if (file == 0) $error("Cannot open %s for reading\n", fname);

        while (!$feof(file)) begin
            if ($fgets(line, file)) begin
                if (j == 0)
                    ret = $sscanf(line, "%h", coeff_array[i]);
                else if (j == 1)
                    ret = $sscanf(line, "%b", z_array[i]);
                i = i + 1;
            end
        end

        $fclose(file);
    end


endtask

task sample_buffer_test;
    $display("Starting buffer test\n");
    @(posedge clk_tb);
    for (int i = 0; i < 64; i++) begin
        hint_4bit_tb = i;
        index_tb = {BUFFER_DATA_W'(i*4+7), BUFFER_DATA_W'(i*4+6), BUFFER_DATA_W'(i*4+5), BUFFER_DATA_W'(i*4+4), BUFFER_DATA_W'(i*4+3), BUFFER_DATA_W'(i*4+2), BUFFER_DATA_W'(i*4+1), BUFFER_DATA_W'(i*4)};
        @(posedge clk_tb);
    end
    @(posedge clk_tb);
endtask

task makehint_test;
    $display("Starting makehint test\n");
    en_tb = 1;
    @(posedge clk_tb);
    en_tb = 0;
    @(posedge clk_tb);
    for (int poly = 0; poly < 8; poly++) begin
        $display("Starting Poly %0d", poly);
            for (int i = 0; i < 64; i++) begin
                coeff_tb = coeff_array[(64*poly)+i];
                z_tb = z_array[(64*poly)+i];
                @(posedge clk_tb);
            end
        $display("Wait 2 cycles to let poly finish\n"); //To emulate 1 cycle transition between polynomials
        @(posedge clk_tb);
        @(posedge clk_tb); 
    end
    @(posedge clk_tb);
    $display("Wait for done signal from makehint\n");
    while(!dut.makehint_done)
        @(posedge clk_tb);
    $display("Hint sum = %d, invalid_h = %0d", dut.hintsum, dut.invalid_h);
    $display("Test done\n");
endtask

initial begin
    init_sim();
    reset_dut();
    read_test_vectors();
    makehint_test();
    repeat(1000) @(posedge clk_tb);
    $finish;
end
endmodule