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
// ntt_mult_reduction_tb.sv
// --------
//
//
//======================================================================

module ntt_mult_reduction_tb 
    #(
    parameter   PRIME     = 23'd8380417,
    parameter   REG_SIZE  = 23
    )
();


parameter CLK_HALF_PERIOD = 5;
parameter CLK_PERIOD      = 2 * CLK_HALF_PERIOD;

reg [31 : 0]  cycle_ctr;
reg [31 : 0]  error_ctr;
reg [31 : 0]  tc_ctr;

reg           clk_tb;
reg           reset_n_tb;
reg           zeroize_tb;
reg [(2*REG_SIZE)-1:0]  opa_i_tb;
reg [REG_SIZE-1:0]      res_o_tb;
reg           bf_ready_tb;

logic [REG_SIZE-1:0] a;
logic [REG_SIZE-1:0] b;
logic [REG_SIZE-1:0] expected;

ntt_mult_reduction #(
    .REG_SIZE(REG_SIZE),
    .PRIME(PRIME) 
)
dut (
    .clk(clk_tb),
    .reset_n(reset_n_tb),
    .zeroize(zeroize_tb),
    .opa_i(opa_i_tb),
    .res_o(res_o_tb),
    .ready_o(ready_o_tb)
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

//----------------------------------------------------------------
// sys_monitor()
//
// An always running process that creates a cycle counter and
// conditionally displays information about the DUT.
//----------------------------------------------------------------
always
begin : sys_monitor
  #(CLK_PERIOD);
  cycle_ctr = cycle_ctr + 1;
end

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
    end
endtask // reset_dut


//----------------------------------------------------------------
// init_sim()
//
// Initialize all counters and testbed functionality as well
// as setting the DUT inputs to defined values.
//----------------------------------------------------------------
task init_sim;
    begin
        $display("Start of init\n");
        cycle_ctr = 32'h00000000;
        error_ctr = 32'h00000000;
        tc_ctr    = 32'h00000000;

        clk_tb        = 0;
        reset_n_tb    = 0;
    end
endtask

//----------------------------------------------------------------
// ntt_mult_test()
//
// Toggle reset to put the DUT into a well known state.
//----------------------------------------------------------------
task ntt_mult_test(input [REG_SIZE-1 : 0] op_a, 
                   input [REG_SIZE-1 : 0] op_b);
    begin
      
      $display("*** ntt_mult_test.");
      #(CLK_PERIOD);

      opa_i_tb = a * b;
      #(CLK_PERIOD);

      expected = opa_i_tb % PRIME;
      #(5 * CLK_PERIOD);
    
      if (res_o_tb == expected)
        $display("*** successful");
      else begin
        $display("*** failed");
        $display("TC%01d: Expected: 0x%06x", tc_ctr, expected);
        $display("TC%01d: Got:      0x%06x", tc_ctr, res_o_tb);
        error_ctr = error_ctr + 1;
      end

      tc_ctr = tc_ctr + 1;
      #(2 * CLK_PERIOD);
    end
endtask // ntt_mult_test


initial begin
    init_sim();
    reset_dut();

    @(posedge clk_tb);

    $display("Starting ntt test\n");
    
    a = 30;
    b = 40;
    ntt_mult_test(a, b);

    a = 3054463;
    b = 809589;
    ntt_mult_test(a, b);

    a = 3082050;
    b = 5637242;
    ntt_mult_test(a, b);

    repeat(10) @(posedge clk_tb);
    $finish;
end

endmodule