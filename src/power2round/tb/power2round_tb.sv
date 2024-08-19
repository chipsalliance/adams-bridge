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
// power2round_tb.sv
// --------
// 
//
//
//======================================================================

`default_nettype none

module power2round_tb
    import ntt_defines_pkg::*;
    import skdecode_defines_pkg::*;
    import abr_params_pkg::*;
#(
        parameter REG_SIZE = 24,
        parameter DILITHIUM_Q = 23'd8380417,
        parameter DILITHIUM_N = 256,
        parameter DILITHIUM_K = 8,
        parameter OMEGA = 75,
        parameter BUFFER_DATA_W = 8,
        parameter MEM_ADDR_WIDTH = 15,
        parameter AHB_DATA_WIDTH = 32
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
logic done_tb;

reg [511:0][95:0] input_array;

logic [(4*24)-1:0] mem_rd_data_a_tb, mem_rd_data_b_tb;
logic mem_rd_data_valid_tb;
mem_if_t mem_a_rd_req_tb;
mem_if_t mem_b_rd_req_tb;

power2round_top #(
    //.BUFFER_DATA_W(BUFFER_DATA_W)
) dut (
    .clk(clk_tb),
    .reset_n(reset_n_tb),
    .zeroize(zeroize_tb),
    .enable(en_tb),
    .src_base_addr(15'h0),
    .skmem_dest_base_addr(15'h0),
    .mem_a_rd_req(mem_a_rd_req_tb),
    .mem_b_rd_req(mem_b_rd_req_tb),
    .mem_rd_data_a(mem_rd_data_a_tb),
    .mem_rd_data_b(mem_rd_data_b_tb),
    .mem_rd_data_valid(mem_rd_data_valid_tb),
    .skmem_a_wr_req(),
    .skmem_b_wr_req(),
    .skmem_wr_data_a(),
    .skmem_wr_data_b(),
    .pk_t1_wren(),
    .pk_t1_wrdata(),
    .pk_t1_wr_addr(),
    .done(done_tb)
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
        zeroize_tb = 0;
        en_tb = 0;
        mem_rd_data_a_tb = 'h0;
        mem_rd_data_b_tb = 'h0;
        mem_rd_data_valid_tb = 0;
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
    
      #(2 * CLK_PERIOD);
      reset_n_tb = 1;
    
      $display("End of reset");
    end
endtask // reset_dut

task read_test_vectors;
    input_array <= 'h0;

    input_array[0] <= {24'h2C361F, 24'h241EF9, 24'h56A63F, 24'h75EAF5};
    input_array[1] <= {24'h27BE0B, 24'h15A72,  24'h587101, 24'h7D5146};
    input_array[2] <= {24'h27BE0B, 24'h15A72,  24'h587101, 24'h7D5146};
    input_array[3] <= {24'h2C361F, 24'h241EF9, 24'h56A63F, 24'h75EAF5};

    input_array[4] <= {24'h2C361F, 24'h241EF9, 24'h56A63F, 24'h75EAF5};
    input_array[5] <= {24'h27BE0B, 24'h15A72,  24'h587101, 24'h7D5146};
    input_array[6] <= {24'h27BE0B, 24'h15A72,  24'h587101, 24'h7D5146};
    input_array[7] <= {24'h2C361F, 24'h241EF9, 24'h56A63F, 24'h75EAF5};

    input_array[508] <= {24'h2C361F, 24'h241EF9, 24'h56A63F, 24'h75EAF5};
    input_array[509] <= {24'h27BE0B, 24'h15A72,  24'h587101, 24'h7D5146};
    input_array[510] <= {24'h27BE0B, 24'h15A72,  24'h587101, 24'h7D5146};
    input_array[511] <= {24'h2C361F, 24'h241EF9, 24'h56A63F, 24'h75EAF5};
endtask

task power2round_test();
    reg [31  : 0] time_limit;
    begin
        time_limit = 0;
        $display("Starting power2round test\n");
        //$system($sformatf("python3 power2round.py"));
        @(posedge clk_tb);
        en_tb <= 1;
        @(posedge clk_tb);
        en_tb <= 0;
        @(posedge clk_tb);
        while (~done_tb & (time_limit < 1000)) begin
            mem_rd_data_a_tb <= (mem_a_rd_req_tb.rd_wr_en == RW_READ)? input_array[mem_a_rd_req_tb.addr] : 'h0;
            mem_rd_data_b_tb <= (mem_b_rd_req_tb.rd_wr_en == RW_READ)? input_array[mem_b_rd_req_tb.addr] : 'h0;
            mem_rd_data_valid_tb <= (mem_a_rd_req_tb.rd_wr_en == RW_READ);
            time_limit =  time_limit + 1;
            @(posedge clk_tb);
        end
        
        $display("Test done\n");
        repeat(100) @(posedge clk_tb);
    end
endtask

initial begin
    init_sim();
    reset_dut();
    read_test_vectors();
    power2round_test();
    $finish;
end
endmodule