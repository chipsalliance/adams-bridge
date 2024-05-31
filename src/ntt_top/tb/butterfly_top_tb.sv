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
// butterfly_top_tb.sv
// --------
// 
//
//
//======================================================================

`default_nettype none
`include "caliptra_reg_defines.svh"

module butterfly_top_tb 
    import kv_defines_pkg::*;
    import ntt_defines_pkg::*;
#(
    parameter   TEST_VECTOR_NUM = 10,
    parameter   PRIME     = 23'd8380417,
    parameter   REG_SIZE  = 23
)
();

parameter CLK_HALF_PERIOD = 5;
parameter CLK_PERIOD      = 2 * CLK_HALF_PERIOD;

//----------------------------------------------------------------
// Register and Wire declarations.
//----------------------------------------------------------------
reg [31 : 0]  cycle_ctr;
reg [31 : 0]  error_ctr;
reg [31 : 0]  tc_ctr;

reg           clk_tb;
reg           reset_n_tb;
reg           cptra_pwrgood_tb;

reg [REG_SIZE-1:0] A, B, U, V, w;
reg [REG_SIZE-1:0] U_out, V_out;
reg [REG_SIZE-1:0] GS_V, pwm_res;
reg [REG_SIZE-1:0] GS_U;
reg [REG_SIZE-1:0] res;
mode_t mode_tb;
reg enable, sub;
reg ready;
reg zeroize_tb;

reg [REG_SIZE-1:0] u00, u01, v00, v01, w00, w01, w10, w11;
reg [REG_SIZE-1:0] U20_out, U21_out, V20_out, V21_out;

string operation;
reg [23:0] zeta [255:0];
reg [23:0] zeta_inv [255:0];
reg [23:0] in_val [255*4:0];
reg [23:0] out_val [255*4:0];
reg [23:0] out_observed [255*4:0];
reg [23:0] intt_out_observed [255*4:0];

bf_uvwi_t uvw_tb;
bf_uvo_t uv_o_tb;

//----------------------------------------------------------------
// Device Under Test.
//----------------------------------------------------------------

butterfly2x2 #(
  .REG_SIZE(23),
  .RADIX(23),
  .DILITHIUM_Q(PRIME)
)
dut (
  .clk(clk_tb),
  .reset_n(reset_n_tb),
  .zeroize(zeroize_tb),
  .mode(mode_tb),
  .enable(enable),
  .uvw_i(uvw_tb),
  .uv_o(uv_o_tb),
  .ready_o(ready)
);

// butterfly #(
//     .REG_SIZE(23),
//     .RADIX(23),
//     .DILITHIUM_Q(PRIME)
// )
// dut (
//     .clk(clk_tb),
//     .reset_n(reset_n_tb),
//     .zeroize(zeroize_tb),
//     .mode(mode_tb),
//     .enable(enable),
//     .opu_i(U),
//     .opv_i(V),
//     .opw_i(w),
//     .u_o(U_out),
//     .v_o(V_out),
//     // .intt_u_o(GS_U),
//     // .intt_v_o(GS_V),
//     .pwm_res_o(pwm_res),
//     .ready_o(ready)
// );

// ecc_add_sub_mod_alter #(
//     .REG_SIZE(23)
// )
// dut (
//     .clk(clk_tb),
//     .reset_n(reset_n_tb),
//     .zeroize(),
//     .add_en_i(enable),
//     .sub_i(sub),
//     .opa_i(A),
//     .opb_i(B),
//     .prime_i(PRIME),
//     .res_o(res), //result ready in 2 cycles after enable is asserted
//     .ready_o()

// );

// mult_mod_alter #(
//     .RADIX(23),
//     .REG_SIZE(23),
//     .PRIME(PRIME)
// )
// dut (
//     .clk(clk_tb),
//     .reset_n(reset_n_tb),
//     .zeroize(1'b0),
//     .enable(enable),
//     .opa_i(A),
//     .opb_i(B),
//     .res_o(res),
//     .ready_o()
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
//   cptra_pwrgood_tb = '0;
  reset_n_tb = 0;

//   #(2 * CLK_PERIOD);
//   cptra_pwrgood_tb = 1;

  #(2 * CLK_PERIOD);
  reset_n_tb = 1;

  $display("End of reset");
end
endtask // reset_dut

//----------------------------------------------------------------
// display_test_results()
//
// Display the accumulated test results.
//----------------------------------------------------------------
task display_test_results;
    begin
      if (error_ctr == 0)
        begin
          $display("*** All %02d test cases completed successfully", tc_ctr);
          $display("* TESTCASE PASSED");
        end
      else
        begin
          $display("*** %02d tests completed - %02d test cases did not complete successfully.",
                   tc_ctr, error_ctr);
          $display("* TESTCASE FAILED");
        end
    end
  endtask // display_test_results

//----------------------------------------------------------------
// init_sim()
//
// Initialize all counters and testbed functionality as well
// as setting the DUT inputs to defined values.
//----------------------------------------------------------------
  task init_sim;
    int i;
    begin
        $display("Start of init");
      cycle_ctr = 32'h00000000;
      error_ctr = 32'h00000000;
      tc_ctr    = 32'h00000000;

      clk_tb        = 0;
      reset_n_tb    = 0;
      cptra_pwrgood_tb = 0;

      A = 'h0;
      B = 'h0;
      U = 'h0;
      V = 'h0;
      w = 'h0;
      mode_tb = ct;
      enable = 1'b0;
      zeroize_tb = 1'b0;
      sub = 1'b0;
      // u00 = 'h0; v00 = 'h0; u01 = 'h0; v01 = 'h0;
      // w00 = 'h0; w01 = 'h0; w10 = 'h0; w11 = 'h0;
      uvw_tb.u00_i = 'h0;
      uvw_tb.v00_i = 'h0;
      uvw_tb.u01_i = 'h0;
      uvw_tb.v01_i = 'h0;
      uvw_tb.w00_i = 'h0;
      uvw_tb.w01_i = 'h0;
      uvw_tb.w10_i = 'h0;
      uvw_tb.w11_i = 'h0;
      operation = "init";
      for (i = 0; i < 256; i++) begin
        zeta[i] = 0;
        zeta_inv[i] = 0;
      end
      for (i = 0; i < 256*4; i++) begin
        in_val[i] = 'h0;
        out_val[i] = 'h0;
        out_observed[i] = 'h0;
        intt_out_observed[i] = 'h0;
      end
      $display("End of init");
    end
  endtask

  task butterfly_test();
    begin
    U <= 8380416;
    V <= 10000;
    w <= 1;
    mode_tb <= ct;
    enable <= 1'b1;
    zeroize_tb <= 1'b0;
    operation = "NTT";
    // #(CLK_PERIOD);
    // enable <= 1'b0;
    #(4*CLK_PERIOD);
    // while(dut.ready_o == 1'b0)
    //     #(CLK_PERIOD);
    $display("U = %d, V = %d, w = %d, ntt u = %d, ntt v = %d, pwm_res", U, V, w, U_out, V_out, pwm_res);

    // #(CLK_PERIOD);
    // #(CLK_HALF_PERIOD);
    U <= 11;
    V <= 22;
    w <= 1;
    // mode_tb <= ct;
    // enable <= 1'b1;
    // zeroize_tb <= 1'b0;
    // operation = "NTT";
    // #(CLK_PERIOD);
    // enable <= 1'b0;
    #(4*CLK_PERIOD);
    // while(dut.ready_o == 1'b0)
    //     #(CLK_PERIOD);
    $display("U = %d, V = %d, w = %d, ntt u = %d, ntt v = %d, pwm_res", U, V, w, U_out, V_out, pwm_res);

    // #(CLK_PERIOD);
    // #(CLK_HALF_PERIOD);
    U <= 55;
    V <= 66;
    w <= 5;
    // mode_tb <= ct;
    // enable <= 1'b1;
    // zeroize_tb <= 1'b0;
    // operation = "NTT";
    // #(CLK_PERIOD);
    // enable <= 1'b0;
    #(4*CLK_PERIOD);
    while(dut.ready_o == 1'b0)
        #(CLK_PERIOD);
    $display("U = %d, V = %d, w = %d, ntt u = %d, ntt v = %d, pwm_res", U, V, w, U_out, V_out, pwm_res);



    U <= U_out;
    V <= V_out;
    w <= 5; //'h7fe000;
    mode_tb <= gs;
    enable <= 1'b1;
    operation = "INTT";
    // #(CLK_PERIOD);
    // enable <= 1'b0;
    #(4*CLK_PERIOD);
    // while(dut.ready_o == 1'b0)
    //     #(CLK_PERIOD);
    $display("U = %d, V = %d, w = %d, ntt u = %d, ntt v = %d, pwm_res", U, V, w, U_out, V_out, pwm_res);
    end
  endtask

  task butterfly_2coeff_test();
    begin
      U <= 8380416;
      V <= 10000;
      w <= 1;
      mode_tb <= ct;
      enable <= 1'b1;
      zeroize_tb <= 1'b0;
      operation = "NTT";
      // #(CLK_PERIOD);
      // enable <= 1'b0;
      #(4*CLK_PERIOD);
      // while(dut.ready_o == 1'b0)
      //     #(CLK_PERIOD);
      $display("U = %d, V = %d, w = %d, ntt u = %d, ntt v = %d, pwm_res", U, V, w, U_out, V_out, pwm_res);
      #(CLK_PERIOD);

      U <= U_out;
      V <= V_out;
      w <= 1; //'h7fe000;
      mode_tb <= gs;
      enable <= 1'b1;
      operation = "INTT";
      // #(CLK_PERIOD);
      // enable <= 1'b0;
      #(4*CLK_PERIOD);
      // while(dut.ready_o == 1'b0)
      //     #(CLK_PERIOD);
      $display("U = %d, V = %d, w = %d, ntt u = %d, ntt v = %d, pwm_res", U, V, w, U_out, V_out, pwm_res);

    end
  endtask

  task zeroize_dut();
    begin
      zeroize_tb <= 1'b1;
      #(CLK_PERIOD);
      zeroize_tb <= 1'b0;
      #(5*CLK_PERIOD);
    end
  endtask

  task pwm_test();
    begin
      mode_tb <= pwm;
      enable <= 1'b1;
      operation = "PWM";
      U <= 1234;
      V <= 8380417;
      w <= 8380416;
      // #(CLK_PERIOD);
      // enable <= 1'b0;
      // while(dut.ready_o == 1'b0)
      //     #(CLK_PERIOD);
      $display("U = %d, V = %d, w = %d, ntt u = %d, ntt v = %d, pwm_res", U, V, w, U_out, V_out, pwm_res);

    end
  endtask

  task intt_butterfly2x2_div2_test();
    int a;
    int test_cnt;

    fork
      begin
        enable <= 1'b1;
        @(posedge clk_tb);
        enable <= 1'b0;
      end
      begin
        for (int j = 0; j < 64; j++) begin
          int k1 = 3; //fix harcoding later TODO
          int k2 = 2;
          int k3 = 1;

          // u00 <= out_observed[j*4];
          uvw_tb.u00_i <= out_observed[j*4];
          uvw_tb.u01_i <= out_observed[(j*4)+1];
          uvw_tb.v00_i <= out_observed[(j*4)+2];
          uvw_tb.v01_i <= out_observed[(j*4)+3];

          uvw_tb.w00_i <= zeta_inv[k1];
          uvw_tb.w01_i <= zeta_inv[k2];
          uvw_tb.w10_i <= zeta_inv[k3];
          uvw_tb.w11_i <= zeta_inv[k3];

          mode_tb <= gs;
          // enable <= 1'b1;
          zeroize_tb <= 1'b0;
          operation = $sformatf("INTT %0d, %0d, %0d, %0d", j*4, (j*4)+1, (j*4)+2, (j*4)+3);
          $display("operation = %s", operation);
          @(posedge clk_tb);
          // enable <= 1'b0; //HERE
        end
      end

      begin
        for (int j = 0; j < 64+11; j++) begin
          if (dut.ready_o && (test_cnt < 256)) begin
            $display("Capturing result %h, j = %d, test_cnt = %d", uv_o_tb.u20_o, j, test_cnt);
            test_cnt++;
            a = j-11; //by the time ready is 1, j advances to 11
            intt_out_observed[a*4]     = uv_o_tb.u20_o; //U20_out;
            intt_out_observed[(a*4)+1] = uv_o_tb.u21_o; //U21_out;
            intt_out_observed[(a*4)+2] = uv_o_tb.v20_o; //V20_out;
            intt_out_observed[(a*4)+3] = uv_o_tb.v21_o; //V21_out;
            $display("out observed is now %h at location %d", intt_out_observed[a*4], a*4);
          end
          @(posedge clk_tb);
        end
      end
    join

      if (intt_out_observed == in_val)
        $display("INTT operation success\n");
      else begin
        $display("Test failed at INTT operation\n");
        $display("INTT: U20_out = %h, out_observed[0] = %h, out_val[0] = %h", uv_o_tb.u20_o, intt_out_observed[0], out_val[0]);
      end
      enable <= 1'b0;
      @(posedge clk_tb);
  endtask

  task butterfly2x2_test();
    begin
      int a;
      int test_cnt;
      // u00 <= 'h0; v00 <= 'd128; u01 <= 'd64; v01 <= 'd192;
      // w00 <= 'h495E02; /*w01 <= 'h495e02;*/ w10 <= 'h397567; w11 <= 'h396569;
      fork
      begin
        enable <= 1'b1;
        @(posedge clk_tb);
        enable <= 1'b0;
      end
      begin
        // for (int l = 256; l > 0; l-2) begin
        //   int m = 1 << (l-2);
        int l = 6;
        int i;
          $display("Stage %d and %d\n", 8-l, (8-l)+1);
          for (i = 0; i < 256; i = i + 64) begin
            for (int j = 0; j < 64; j++) begin //i = 0, m = 64 for 1st stage
              int k1 = (256+i) >> l;
              int k2 = (256+i) >> l-1;
              int k3 = k2 + 1;
            
              $display("In for loop, j = %d at time %t, ready = %d\n", j, $time, dut.ready_o);
            
              // u00 <= in_val[j*4];
              uvw_tb.u00_i <= in_val[j*4] ;
              uvw_tb.u01_i <= in_val[(j*4) + 1]; 
              uvw_tb.v00_i <= in_val[(j*4) + 2]; 
              uvw_tb.v01_i <= in_val[(j*4)+3];

              uvw_tb.w00_i <= zeta[k1]; 
              uvw_tb.w01_i <= zeta[k1]; 
              uvw_tb.w10_i <= zeta[k2]; 
              uvw_tb.w11_i <= zeta[k3];
              // $display("w00 = %h", w00);
              mode_tb <= ct;
              // enable <= 1'b1;
              zeroize_tb <= 1'b0;
              operation = $sformatf("NTT %0d, %0d, %0d, %0d", j*4, (j*4)+1, (j*4)+2, (j*4)+3);
              $display("operation = %s", operation);
            
              @(posedge clk_tb);
            end //j
          end //i
        // end //l
      end
      begin
        for (int j = 0; j < 64+11; j++) begin
          if (dut.ready_o && (test_cnt < 256)) begin
            $display("Capturing result %h, j = %d, test_cnt = %d", uv_o_tb.u20_o, j, test_cnt);
            test_cnt++;
            a = j-11; //by the time ready is 1, j advances to 11
            out_observed[a*4]     = uv_o_tb.u20_o; //U20_out;
            out_observed[(a*4)+1] = uv_o_tb.u21_o; //U21_out;
            out_observed[(a*4)+2] = uv_o_tb.v20_o; //V20_out;
            out_observed[(a*4)+3] = uv_o_tb.v21_o; //V21_out;
            $display("out observed is now %h at location %d", out_observed[a*4], a*4);
          end
          #(CLK_PERIOD);
        end
      end
    join

      if (out_observed == out_val) begin
        $display("NTT operation success\n");
      end
      else begin
        $display("Test failed at NTT operation\n");
        $display("NTT: U20_out = %h, out_observed[0] = %h, out_val[0] = %h", U20_out, out_observed[0], out_val[0]);
      end
      enable <= 1'b0;
      // if ((U20_out == out_val[0]) & (U21_out == out_val[1]) & (V20_out == out_val[2]) & (V21_out == out_val[3]))
      //   $display("Test case passed for fwd NTT!\n");
      // else begin
      //   $error("Test case failed\n");
      //   $finish;
      // end
      // $display("u20 = %d, u21 = %d, v20 = %d, v21 = %d", U20_out, U21_out, V20_out, V21_out);

      // $display("Expected: u20 = 3139780, u21 = 4687447, v20 = 4217002, v21 = 4716605\n");

      #(CLK_PERIOD);
      // enable <= 1'b1;
      // u00 <= U20_out; v00 <= V20_out; u01 <= U21_out; v01 <= V21_out;
      // w00 <= 'h7fe000; w01 <= 'h3681ff; w10 <= 'h466a9a; w11 <= 'h467a98;
      // mode_tb <= ct;
      // // enable <= 1'b1;
      // zeroize_tb <= 1'b0;
      // operation = "NTT 2";
      // // #(CLK_PERIOD);
      // // enable <= 1'b0;
      // while(dut.ready_o == 1'b0)
      //     #(CLK_PERIOD);
      // enable <= 1'b0;
      // $display("u20 = %h, u21 = %h, v20 = %h, v21 = %h", U20_out, U21_out, V20_out, V21_out);

    end
  endtask

  // task read_ntt_hex(input string fname);
  //   integer fin;
  //   integer rv;
  //   integer line_cnt;
  //   reg [23:0] val[255:0];
  //   fin = $fopen(fname, "r");
  //   if (fin == 0)
  //     $error("Cannot open file %s for reading", fname);
  //   while (!$feof(fin)) begin
  //     rv = $fscanf(fin, "%h\n", val);
  //     if(rv != 1) begin
  //       $error("Failed to read matching string");
  //       $fclose(fin);
  //       $finish;
  //     end
  //   end
  //   $display("zeta 0 = %h", val[0]);
  //   $fclose(fin);
  // endtask

  task read_ntt_hex();
    begin
    end
  endtask

//----------------------------------------------------------------
// ecc_test()
//
//----------------------------------------------------------------
  initial begin
    init_sim();
    reset_dut();
    $readmemh("zeta.txt", zeta);
    $readmemh("zeta_inv.hex", zeta_inv);
    $display("Zeta values are %h, %h, %h, ...", zeta[0], zeta[1], zeta[2]);
    $display("Zeta inv values are %h, %h, %h, ...", zeta_inv[0], zeta_inv[1], zeta_inv[2]);
    $readmemh("ntt_stage2.hex", in_val);
    $display("in_val = %h, %h, %h, ...", in_val[0], in_val[1], in_val[2]);
    $readmemh("ntt_stage2_out.hex", out_val);
    $display("out_val = %h, %h, %h, ...", out_val[0], out_val[1], out_val[2]);
    #(CLK_PERIOD);
    #(CLK_HALF_PERIOD);
    
    // butterfly_test();
    // zeroize_dut();
    // enable <= 1'b0;
    // butterfly_2coeff_test();
    // zeroize_dut();
    // enable <= 1'b0;
    butterfly2x2_test();
    intt_butterfly2x2_div2_test();
    // zeroize_dut();
    // enable <= 1'b0;
    // pwm_test();
    // read_ntt_hex("ntt_test_vector.hex");
    
    #(10*CLK_PERIOD);

    $finish;
  end

endmodule