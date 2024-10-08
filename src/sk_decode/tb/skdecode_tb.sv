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
// skdecode_tb.sv
// ---------------
//======================================================================

`default_nettype none

module skdecode_tb
    import mldsa_params_pkg::*;
#(
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
reg [7:0][2:0] s1s2_data_i;
reg [3:0][12:0] t0_data_i;
reg [MLDSA_MEM_ADDR_WIDTH-1:0] dest_base_tb;
reg [31:0] ahb_data_tb, keymem_a_data_tb, keymem_b_data_tb;
reg [167:0][3:0][7:0] s1_array, s1_array_rev;
reg [191:0][3:0][7:0] s2_array_tb;
reg [831:0][3:0][7:0] t0_array_tb;
reg [2:0] stall_count; 
reg [9:0] byte_index;
reg [6:0] buf_count;
reg [(256*8)-1:0][REG_SIZE-1:0] t0_out_array, s2_out_array;
reg [(256*7)-1:0][REG_SIZE-1:0] s1_out_array;

skdecode_top dut (
    .clk(clk_tb),
    .reset_n(reset_n_tb),
    .zeroize(zeroize_tb),
    .skdecode_enable(en_tb),
    .keymem_src_base_addr(MLDSA_MEM_ADDR_WIDTH'(0)),
    .dest_base_addr(dest_base_tb),
    .keymem_a_rd_data(keymem_a_data_tb),
    .keymem_b_rd_data(keymem_b_data_tb),
    .keymem_a_rd_req(),
    .keymem_b_rd_req(),
    .mem_a_wr_req(),
    .mem_b_wr_req(),
    .mem_a_wr_data(),
    .mem_b_wr_data(),
    .skdecode_error(),
    .skdecode_done(),
    .s1_done(),
    .s2_done(),
    .t0_done()
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
        s1s2_data_i = 'h0;
        t0_data_i = 'h0;
        dest_base_tb = 'h0;
        ahb_data_tb = 'h0;
        keymem_a_data_tb = 'h0;
        keymem_b_data_tb = 'h0;
        stall_count = 'h0;
        byte_index = 'h0;
        buf_count = 'h0;
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
    string fname = "s1_bytes.hex";
    string s2_name = "s2_bytes.hex";
    string t0_name = "t0_bytes.hex";
    string t0_outname = "t0_out.hex";
    string s1_outname = "s1_out.hex";
    string s2_outname = "s2_out.hex";

    integer file, file2, file3;
    string line;
    integer i, ret;

    i = 0;
    file = $fopen(fname, "r");
    file2 = $fopen(s2_name, "r");
    file3 = $fopen(t0_name, "r");
    if (file == 0) $error("Cannot open %s for reading\n", fname);
    if (file2 == 0) $error("Cannot open %s for reading\n", s2_name);
    if (file3 == 0) $error("Cannot open %s for reading\n", t0_name);
    
    while (!$feof(file)) begin
        if($fgets(line,file)) begin
            ret = $sscanf(line, "%02x%02x%02x%02x", s1_array[i][0],s1_array[i][1],s1_array[i][2],s1_array[i][3]);
            ret = $sscanf(line, "%h", s1_array_rev[167-i]);
            i = i+1;
        end
    end
    $fclose(file);

    i = 0;
    while (!$feof(file2)) begin
        if($fgets(line,file2)) begin
            ret = $sscanf(line, "%02x%02x%02x%02x", s2_array_tb[i][0],s2_array_tb[i][1],s2_array_tb[i][2],s2_array_tb[i][3]);
            i = i+1;
        end
    end
    $fclose(file2);

    i = 0;
    while (!$feof(file3)) begin
        if($fgets(line,file3)) begin
            ret = $sscanf(line, "%02x%02x%02x%02x", t0_array_tb[i][0],t0_array_tb[i][1],t0_array_tb[i][2],t0_array_tb[i][3]);
            i = i+1;
        end
    end
    $fclose(file3);

    file = $fopen(s1_outname, "r");
    if (file == 0) $error("Cannot open %s for reading\n", s1_outname);
    i = 0;
    while (!$feof(file)) begin
        if($fgets(line,file)) begin
            ret = $sscanf(line, "%h", s1_out_array[i]);
            i = i+1;
        end
    end
    $fclose(file);

    file = $fopen(s2_outname, "r");
    if (file == 0) $error("Cannot open %s for reading\n", s2_outname);
    i = 0;
    while (!$feof(file)) begin
        if($fgets(line,file)) begin
            ret = $sscanf(line, "%h", s2_out_array[i]);
            i = i+1;
        end
    end
    $fclose(file);

    file = $fopen(t0_outname, "r");
    if (file == 0) $error("Cannot open %s for reading\n", t0_outname);
    i = 0;
    while (!$feof(file)) begin
        if($fgets(line,file)) begin
            ret = $sscanf(line, "%h", t0_out_array[i]);
            i = i+1;
        end
    end
    $fclose(file);
endtask

task skdecode_ref_test(input logic [167:0][31:0] s_array_tb);
    
    int i;
    string sval;
    int check_count;

    $display("Starting ref test\n");
    @(posedge clk_tb);
    en_tb = 1;
    @(posedge clk_tb);
    en_tb = 1'b0;
    dest_base_tb = 15'h0;

    
    $display("Wait a cycle to emulate mem read\n");
    @(posedge clk_tb);
    
        $display("Starting s1 poly\n");
        fork
            begin
                for (i = 0; i < 224; i++) begin
                    if (stall_count < 'h3) begin
                    // if ((!dut.s1s2_buf_full) && (byte_index < 'd167)) begin
                        keymem_a_data_tb <= s_array_tb[byte_index];
                        stall_count++;
                        byte_index++;
                    end
                    else begin
                        stall_count = 'h0;
                        // keymem_a_data_tb <= 'h0;
                    end
                    @(posedge clk_tb);
                end
            end
            begin
                $display("Waiting for s1s2 valid\n");
                while (!dut.s1s2_valid[0]) @(posedge clk_tb);
                $display("Received s1s2 valid\n");
                for (int k = 0; k < 224; k++) begin
                for (int j = 0; j < 8; j++) begin
                    if (dut.s1s2_data[j] != s1_out_array[(8*k)+j])
                        $display("Error: s1 data mismatch. Exp: %6h, Obs: %6h", s1_out_array[(8*k)+j], dut.s1s2_data[j]);
                    else check_count++;
                end
                @(posedge clk_tb);
                end
            end
        join
if (check_count == 1792) $display("s1 unpack passed, check count = %d", check_count);
else $display("s1 unpack failed, check count = %d", check_count);
        byte_index = 'h0;
        $display("Waiting for s1 done, value = %0d\n", dut.s1_done);
        @(posedge clk_tb iff (dut.s1_done == 1'b1));
        // $display("Waiting for s1 done, value = %0d\n", dut.s1_done);

        @(posedge clk_tb); //Wait a cycle to emulate delay in fsm for last mem write

        //------------------------------------------------------------------------

    // begin
        byte_index = 'h0;
        stall_count = 'h0;
        check_count = 'h0;
        $display("Starting s2 poly\n");
        fork 
            begin
                for (i = 0; i < 256; i++) begin
                    if (stall_count < 'h3) begin
                    // if ((!dut.s1s2_buf_full) && (byte_index < 'd191)) begin
                        keymem_a_data_tb <= s2_array_tb[byte_index]; //s1_array[i];
                        stall_count++;
                        byte_index++;
                    end
                    else begin
                        stall_count = 'h0;
                        // keymem_a_data_tb <= 'h0; //TODO remove and validate
                    end
                    @(posedge clk_tb);
                end
            end
            begin
                $display("Waiting for s1s2 valid\n");
                while (!dut.s1s2_valid[0]) @(posedge clk_tb);
                $display("Received s1s2 valid\n");
                for (int k = 0; k < 256; k++) begin
                for (int j = 0; j < 8; j++) begin
                    if (dut.s1s2_data[j] != s2_out_array[(8*k)+j])
                        $display("Error: s2 data mismatch. Exp: %6h, Obs: %6h", s2_out_array[(8*k)+j], dut.s1s2_data[j]);
                    else check_count++;
                end
                @(posedge clk_tb);
                end

            end
        join

        if (check_count == 2048) $display("s2 unpack passed, check count = %d", check_count);
        else $display("s2 unpack failed, check count = %d", check_count);
    

    // end

    // while (dut.s2_done == 1'b0) begin
        $display("Waiting for s2 done, value = %0d\n", dut.s2_done);
        // @(posedge clk_tb);
    // end
        @(posedge clk_tb iff (dut.s2_done == 1'b1));
        // $display("Waiting for s2 done, value = %0d\n", dut.s2_done);

        @(posedge clk_tb); //Wait a cycle to emulate delay in fsm for last mem write

        //------------------------------------------------------------------------

    // begin
        byte_index = 'h0;
        stall_count = 'h0;
        check_count = 0;
        $display("Starting t0 poly\n");
        fork
            begin
                for (i = 0; i < 512; i++) begin
                    // if ((buf_count <= 104) && (byte_index < 'd831)) begin
                    if ((!dut.t0_buf_full) & (byte_index < 'd831)) begin
                    // if (buf_count < 'd60) begin
                        keymem_a_data_tb <= t0_array_tb[byte_index];
                        keymem_b_data_tb <= t0_array_tb[byte_index+1];
                        stall_count++;
                        byte_index = byte_index+2;
                        if (i == 0)
                            buf_count <= buf_count + 'd64;
                        else
                            buf_count <= buf_count - 'd52 + 'd64;
                    end
                    // else begin
                    //     stall_count = 'h0;
                    //     // keymem_a_data_tb <= 'h0; //TODO remove and validate
                    //     // keymem_b_data_tb <= 'h0;
                    //     buf_count <= buf_count - 'd52;
                    // end
                    @(posedge clk_tb);
                end
            end
            begin
                $display("Waiting for t0 valid\n");
                while (!dut.t0_valid[0]) @(posedge clk_tb);
                $display("Received t0 valid\n");
                for (int k = 0; k < 512; k++) begin
                for (int j = 0; j < 4; j++) begin
                    if (dut.t0_data[j] != t0_out_array[(4*k)+j])
                        $display("Error: t0 data mismatch. Exp: %6h, Obs: %6h", t0_out_array[(4*k)+j], dut.t0_data[j]);
                    else check_count++;
                end
                @(posedge clk_tb);
                end
            end
        join
    if (check_count == 2048) $display("T0 unpack passed, check count = %d", check_count);
    else $display("T0 unpack failed, check count = %d", check_count);
    // end

    // while (dut.s2_done == 1'b0) begin
        $display("Waiting for t0 done, value = %0d\n", dut.t0_done);
        // @(posedge clk_tb);
    // end
        @(posedge clk_tb iff (dut.t0_done == 1'b1));
        // $display("Waiting for t0 done, value = %0d\n", dut.t0_done);

    while (!dut.skdecode_done) @(posedge clk_tb);
    $display("Test done\n");

endtask

task skdecode_test;
    $display("Starting skdecode test\n");
    @(posedge clk_tb);
    en_tb = 1;
    @(posedge clk_tb);
    en_tb = 1'b0;
    dest_base_tb = 'h0;

    $display("Starting s1 poly\n");
    for (int poly = 0; poly < 7; poly++) begin
        $display("Starting poly %0d", poly);
        for (int i = 0; i < 256; i=i+8) begin
            // for (int j = 0; j < 8; j++) begin
                // s1s2_data_i[j] <= $urandom_range(1,4); //{$urandom_range(0,4), $urandom_range(0,4), $urandom_range(0,4), $urandom_range(0,4), $urandom_range(0,4), $urandom_range(0,4), $urandom_range(0,4), $urandom_range(0,4)};
                // ahb_data_tb <= $urandom();
                keymem_a_data_tb <= {$urandom_range(1,4), $urandom_range(1,4),
                                     $urandom_range(1,4), $urandom_range(1,4),
                                     $urandom_range(1,4), $urandom_range(1,4),
                                     $urandom_range(1,4), $urandom_range(1,4)};
            // end
            @(posedge clk_tb);
        end
    end

    // $display("Polys done, waiting\n");
    // while(!dut.s1_done | !dut.skdecode_error) @(posedge clk_tb);
    // if (dut.skdecode_error)
    //     $error("s1 invalid\n");
    // else
    //     $display("s1 done\n");
    $display("Starting s2 poly\n");
    for (int poly = 0; poly < 8; poly++) begin
        $display("Starting poly %0d", poly);
        for (int i = 0; i < 256; i=i+8) begin
            // for (int j = 0; j < 8; j++) begin
                // s1s2_data_i[j] <= $urandom_range(1,4); //{$urandom_range(0,4), $urandom_range(0,4), $urandom_range(0,4), $urandom_range(0,4), $urandom_range(0,4), $urandom_range(0,4), $urandom_range(0,4), $urandom_range(0,4)};
            // end
            keymem_a_data_tb <= $urandom_range(1,4);
            @(posedge clk_tb);
        end
    end

    // while(!dut.s2_done | !dut.skdecode_error) @(posedge clk_tb);
    // if (dut.skdecode_error)
    //     $error("s2 invalid\n");
    // else
        // $display("s2 done\n");
    repeat(2) @(posedge clk_tb);
    $display("Starting t0 poly\n");
    for (int poly = 0; poly < 8; poly++) begin
        $display("Starting poly %0d", poly);
        for (int i = 0; i < 256; i=i+8) begin
            // for (int j = 0; j < 8; j++) begin
                // t0_data_i[j] <= $random; //{$random, $random, $random, $random, $random, $random, $random, $random};

            // end
            keymem_a_data_tb <= $urandom();
            keymem_b_data_tb <= $urandom();
            @(posedge clk_tb);
        end
    end

    @(posedge clk_tb);
    en_tb = 1;
    @(posedge clk_tb);
    en_tb = 1'b0;
    dest_base_tb = 'h0;

    $display("Starting illegal s1 poly\n");
    for (int poly = 0; poly < 7; poly++) begin
        $display("Starting poly %0d", poly);
        for (int i = 0; i < 256; i=i+8) begin
            // for (int j = 0; j < 8; j++) begin
                // s1s2_data_i[j] <= $random; //{$random, $random, $random, $random, $random, $random, $random, $random};
            // end
            keymem_a_data_tb <= $urandom();
            @(posedge clk_tb);
        end
    end

    // while(!dut.t0_done) @(posedge clk_tb);
    // $display("t0 done\n");
    while (!dut.skdecode_done) @(posedge clk_tb);
    $display("Test done\n");
endtask

initial begin
    init_sim();
    reset_dut();
    // skdecode_test();
    $display("Reading test vectors from hex\n");
    read_test_vectors();
    skdecode_ref_test(s1_array);
    repeat(100) @(posedge clk_tb);
    // skdecode_ref_test(s1_array_rev);
    // repeat(1000) @(posedge clk_tb);
    $finish;
end

endmodule