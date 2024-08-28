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
// sigdecode_h_tb.sv
// --------
// 
//
//
//======================================================================

`default_nettype none

module sigdecode_h_tb
    import mldsa_params_pkg::*;
#(
    parameter NUM_WR = 4,
    parameter NUM_RD = 4,
    parameter BUFFER_DATA_W = 8,
    parameter REG_SIZE = 24,
    parameter MLDSA_OMEGA = 75,
    parameter MLDSA_K = 8
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
reg [MLDSA_OMEGA+MLDSA_K-1:0][7:0] y_tb;
reg [MLDSA_K-1:0][7:0] hintsum;
reg [MLDSA_OMEGA-1:0][7:0] y_bytes, padding;


sigdecode_h #(
    .REG_SIZE(REG_SIZE)
) dut (
    .clk(clk_tb),
    .reset_n(reset_n_tb),
    .zeroize(zeroize_tb),
    .encoded_h_i(y_tb),
    .sigdecode_h_enable(en_tb),
    .dest_base_addr(MLDSA_MEM_ADDR_WIDTH'(0)),
    .mem_wr_req(),
    .mem_wr_data(),
    .sigdecode_h_done(),
    .sigdecode_h_error()
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
        y_tb = 'h0;
        hintsum = 0;
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

task init_y_array;
    hintsum = {8'd40, 8'd35, 8'd30, 8'd25, 8'd20, 8'd15, 8'd10, 8'd5};
    y_bytes = {8'd100, 8'd74, 8'd51, 8'd43, 8'd16, 
                8'd9, 8'd7, 8'd5, 8'd3, 8'd1, 
                8'd121, 8'd100, 8'd33, 8'd17, 8'd0, 
                8'd77, 8'd66, 8'd55, 8'd44, 8'd33,
                8'd65, 8'd54, 8'd43, 8'd32, 8'd21,
                8'd4, 8'd3, 8'd2, 8'd1, 8'd0,
                8'd9, 8'd8, 8'd7, 8'd6, 8'd5,
                8'd255, 8'd191, 8'd127, 8'd63, 8'd31};
    padding = {35{8'h00}};
    // hintsum = {8'd5, 8'd4, 8'd4, 8'd3, 8'd2, 8'd2, 8'd1, 8'd0};
    // y_bytes = {8'd99, 8'd88, 8'd77, 8'd66, 8'd55};
    // padding = {75{8'h00}};
endtask

task sigdecode_h_test_check;
    reg [7:0] hintsum_curr, hintsum_prev, hintsum_y, rem_hintsum;
    reg [7:0] ptr;
    $display("Starting sigdecode h test");
    en_tb = 'b1;
    @(posedge clk_tb);
    en_tb = 'b0;
    y_tb = {hintsum, y_bytes}; //((MLDSA_OMEGA+MLDSA_K)*8)'(0);
    @(posedge clk_tb);

    //Check output
    hintsum_prev = 0;
    ptr = 0;
    for (int poly = 0; poly < 8; poly++) begin
        $display("Poly %0d", poly);
        hintsum_y = y_tb[75+poly];
        hintsum_curr = hintsum_y - hintsum_prev;

        if (hintsum_y < hintsum_prev) begin
            $error("Invalid signature, exiting");
            break;
        end

        while(!dut.sdh_ctrl_inst.poly_done_rd) @(posedge clk_tb);
        @(posedge clk_tb); //Wait a clk for bitmap to be updated
        
        rem_hintsum = hintsum_curr;
        // $display("hintsum = %0d, y = %0d, prev = %0d, rem = %0d", hintsum_curr, hintsum_y, hintsum_prev, rem_hintsum);
        if (hintsum_curr > 0) begin
            while (rem_hintsum > 0) begin
                // $display("ptr = %0d, index = %0d", ptr, y_tb[ptr]);
                if (~dut.bitmap[y_tb[ptr]]) begin
                        $error("Expected 1 in bitmap index %0d", y_tb[ptr]);
                end
                ptr++;
                rem_hintsum--;
            end
        end
        else begin
            if (dut.bitmap > 256'h0)
                $error("Curr poly hintsum = %0d, expecting all 0s in bitmap", hintsum_curr);
        end

        hintsum_prev = hintsum_y;
        @(posedge clk_tb);
    end
endtask

initial begin
    init_sim();
    reset_dut();
    init_y_array();
    sigdecode_h_test_check();
    repeat(1000) @(posedge clk_tb);
    $finish;
end

endmodule