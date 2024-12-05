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
// ntt_top_masking_tb.sv
// --------
//======================================================================

`default_nettype none

module ntt_top_masking_tb 

    import ntt_defines_pkg::*;
    import mldsa_params_pkg::*;
    
#(
    parameter   TEST_VECTOR_NUM = 10,
    parameter   PRIME     = 23'd8380417,
    parameter   REG_SIZE  = 23,
    parameter   MEM_DEPTH = 32768, //32 KB
    parameter   MEM_ADDR_WIDTH = $clog2(MEM_DEPTH)
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
reg           zeroize_tb;
reg           enable_tb;
reg           bf_ready_tb;

mode_t mode_tb;

reg [23:0] zeta [255:0];
reg [23:0] zeta_inv [255:0];

string operation;

logic sub;
logic [45:0] actual_u, actual_v, actual_w;
logic [1:0][45:0] u;
logic [1:0][45:0] v;
logic [1:0][45:0] w;
logic [45:0] rnd0, rnd1, rnd2, rnd3;
logic wren_tb, rden_tb;
logic [1:0] wrptr_tb, rdptr_tb;
logic [5:0] random_tb;
bf_uvwi_t uvw_i_tb;
masked_bf_uvwi_t masked_uvw_i_tb;
pwo_uvwi_t pw_uvw_i_tb;
hybrid_bf_uvwi_t hybrid_uvw_i_tb;
bf_uvo_t uv_o_tb;
logic [REG_SIZE-1:0] u10, u11, v10, v11;
//----------------------------------------------------------------
// Device Under Test.
//----------------------------------------------------------------

// ntt_masked_BFU_add_sub dut (
//     .clk(clk_tb),
//     .reset_n(reset_n_tb),
//     .zeroize(zeroize_tb),
//     .sub(sub),
//     .u(u),
//     .v(v),
//     .rnd0(rnd0),
//     .rnd1(rnd1),
//     .rnd2(rnd2),
//     .rnd3(rnd3),
//     .res()
// );

// ntt_masked_BFU_mult dut (
//     .clk(clk_tb),
//     .reset_n(reset_n_tb),
//     .zeroize(zeroize_tb),
//     .u(u),
//     .v(v),
//     .rnd0(rnd0),
//     .rnd1(rnd1),
//     .rnd2(rnd2),
//     .rnd3(rnd3),
//     .rnd4(rnd0+rnd1),
//     .res()
// );

// ntt_masked_pwm dut (
//     .clk(clk_tb),
//     .reset_n(reset_n_tb),
//     .zeroize(zeroize_tb),
//     .u(u),
//     .v(v),
//     .w(w),
//     .accumulate(1'b1),
//     .rnd({rnd0+rnd1, rnd3, rnd2, rnd1, rnd0}),
//     .res()
// );

// ntt_masked_butterfly1x2 dut (
//     .clk(clk_tb),
//     .reset_n(reset_n_tb),
//     .zeroize(zeroize_tb),
//     .uvw_i(masked_uvw_i_tb),
//     .rnd_i({rnd0+rnd1, rnd3, rnd2, rnd1, rnd0}),
//     .uv_o()
// );

// ntt_masked_gs_butterfly dut (
//     .clk(clk_tb),
//     .reset_n(reset_n_tb),
//     .zeroize(zeroize_tb),
//     .opu_i(u),
//     .opv_i(v),
//     .opw_i(w),
//     .rnd_i({rnd0+rnd1, rnd3, rnd2, rnd1, rnd0}),
//     .u_o(),
//     .v_o()
// );

ntt_hybrid_butterfly_2x2 dut (
    .clk(clk_tb),
    .reset_n(reset_n_tb),
    .zeroize(zeroize_tb),
    .mode(mode_tb),
    .enable(enable_tb),
    .masking_en(1'b1),
    .uvw_i(uvw_i_tb),
    .pw_uvw_i(pw_uvw_i_tb),
    .hybrid_pw_uvw_i(),
    .rnd_i({rnd0+rnd1, rnd3, rnd2, rnd1, rnd0}),
    .accumulate(1'b0),
    .uv_o(),
    .pwo_uv_o(),
    .ready_o()
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
  rnd0 = $random();
  rnd1 = $random();
  rnd2 = $random();
  rnd3 = $random();
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
// init_sim()
//
// Initialize all counters and testbed functionality as well
// as setting the DUT inputs to defined values.
//----------------------------------------------------------------
task init_sim;
    int i;
    begin
        $display("Start of init\n");
        cycle_ctr = 32'h00000000;
        error_ctr = 32'h00000000;
        tc_ctr    = 32'h00000000;

        clk_tb        = 0;
        reset_n_tb    = 0;
        cptra_pwrgood_tb = 0;

        zeroize_tb = 'b0;
        enable_tb = 'b0;
        wren_tb = 'b0; rden_tb = 'b0;
        wrptr_tb = 'h0; rdptr_tb = 'h0;

        mode_tb = ct;

        //NTT ctrl
        bf_ready_tb = 1'b0;
        random_tb <= 'h0;

        //Masking
        for (int i = 0; i < 46; i++) begin
            u[i] = 2'h0;
            v[i] = 2'h0;
        end
        actual_u = 'h0;
        actual_v = 'h0;
        actual_w = 'h0;
        sub = 'h0;

        rnd0 = 'h0;
        rnd1 = 'h0;
        rnd2 = 'h0;
        rnd3 = 'h0;

        uvw_i_tb.u00_i = 'h0;
        uvw_i_tb.u01_i = 'h0;
        uvw_i_tb.v00_i = 'h0;
        uvw_i_tb.v01_i = 'h0;
        uvw_i_tb.w00_i = 'h0;
        uvw_i_tb.w01_i = 'h0;
        uvw_i_tb.w10_i = 'h0;
        uvw_i_tb.w11_i = 'h0;

        pw_uvw_i_tb.u0_i = 'h0;
        pw_uvw_i_tb.v0_i = 'h0;
        pw_uvw_i_tb.w0_i = 'h0;

        pw_uvw_i_tb.u1_i = 'h0;
        pw_uvw_i_tb.v1_i = 'h0;
        pw_uvw_i_tb.w1_i = 'h0;

        pw_uvw_i_tb.u2_i = 'h0;
        pw_uvw_i_tb.v2_i = 'h0;
        pw_uvw_i_tb.w2_i = 'h0;

        pw_uvw_i_tb.u3_i = 'h0;
        pw_uvw_i_tb.v3_i = 'h0;
        pw_uvw_i_tb.w3_i = 'h0;

        hybrid_uvw_i_tb.u0_i = 'h0;
        hybrid_uvw_i_tb.u1_i = 'h0;
        hybrid_uvw_i_tb.u2_i = 'h0;
        hybrid_uvw_i_tb.u3_i = 'h0;

        hybrid_uvw_i_tb.v0_i = 'h0;
        hybrid_uvw_i_tb.v1_i = 'h0;
        hybrid_uvw_i_tb.v2_i = 'h0;
        hybrid_uvw_i_tb.v3_i = 'h0;

        hybrid_uvw_i_tb.w0_i = 'h0;
        hybrid_uvw_i_tb.w1_i = 'h0;
        hybrid_uvw_i_tb.w2_i = 'h0;
        hybrid_uvw_i_tb.w3_i = 'h0;

        hybrid_uvw_i_tb.twiddle_w0_i = 'h0;
        hybrid_uvw_i_tb.twiddle_w1_i = 'h0;
        hybrid_uvw_i_tb.twiddle_w2_i = 'h0;
        hybrid_uvw_i_tb.twiddle_w3_i = 'h0;

        masked_uvw_i_tb = {'h0, 'h0, 'h0, 'h0, 'h0, 'h0};

        u10 = 'h0;
        u11 = 'h0;
        v10 = 'h0;
        v11 = 'h0;

        $display("End of init\n");
    end
endtask

/*
task masked_BFU_adder_test();
    logic [45:0] u_array, v_array;
    logic [45:0] rand0, rand1;
    sub = 1;
    for (int i = 0; i < 1000; i++) begin
        @(posedge clk_tb);
        fork
            begin
                actual_u = $random()%PRIME;
                actual_v = $random()%PRIME;
                u_array = actual_u;
                v_array = actual_v;
                rand0 = $random();
                rand1 = $random();

                u[0] = actual_u-rand0;
                u[1] = rand0;
                v[0] = actual_v-rand1;
                v[1] = rand1;
                // $display("u0 = %h, u1 = %h, v0 = %h, v1 = %h", u[0], u[1], v[0], v[1]);
            end
            begin
                repeat(54) @(posedge clk_tb);
                if (!sub) begin
                    if ((dut.add_res_reduced[1] + dut.add_res_reduced[0]) != ((u_array + v_array)%PRIME)) begin
                        $error("Addition Mismatch: exp_output = %h   output shares = %h %h actual output = %h", (u_array + v_array)%PRIME, dut.add_res_reduced[0], dut.add_res_reduced[1], dut.add_res_reduced[0] + dut.add_res_reduced[1]);
                    end
                end
                else begin
                    if ((dut.add_res_reduced[1] + dut.add_res_reduced[0]) != ((u_array - v_array + PRIME)%PRIME)) begin
                        $error("Subtraction Mismatch: exp_output = %h   output shares = %h %h actual output = %h", (u_array + PRIME + (~v_array+'h1))%PRIME, dut.add_res_reduced[0], dut.add_res_reduced[1], dut.add_res_reduced[0] + dut.add_res_reduced[1]);
                    end
                end
            end
        join
    end
endtask


task masked_BFU_mult_test();
    logic [45:0] u_array, v_array;
    logic [45:0] rand0, rand1;

    for (int i = 0; i < 10; i++) begin
        @(posedge clk_tb);
        fork
            begin
                actual_u = $random()%PRIME;
                actual_v = $random()%PRIME;
                u_array = actual_u;
                v_array = actual_v;
                rand0 = $random();
                rand1 = $random();

                // $display("actual u = %h, actual v = %h", actual_u, actual_v);

                u[0] = actual_u-rand0;
                u[1] = rand0;
                v[0] = actual_v-rand1;
                v[1] = rand1;
                // $display("u0 = %h, u1 = %h, v0 = %h, v1 = %h", u[0], u[1], v[0], v[1]);
            end
            begin
                repeat(210) @(posedge clk_tb);
                if ((dut.final_res[1] + dut.final_res[0]) != ((u_array * v_array)%PRIME)) begin
                    $error("Multiplication Mismatch: exp_output = %h   output shares = %h %h actual output = %h", (u_array * v_array)%PRIME, dut.final_res[0], dut.final_res[1], dut.final_res[0] + dut.final_res[1]);
                end
            end
        join
    end
endtask
*/


// task masked_gs_butterfly_test();
//     logic [45:0] rand0, rand1, rand2;
//     logic [45:0] actual_u_normalized;
//     for (int i = 0; i < 10; i++) begin
//         @(posedge clk_tb);
//         fork
//             begin
//                 actual_u = $random()%PRIME;
//                 actual_v = $random()%PRIME;
//                 actual_w = 'h2;
//                 if (actual_u < actual_v)
//                     actual_u_normalized = actual_u + PRIME;
//                 else
//                     actual_u_normalized = actual_u;
//                 // u_array = actual_u;
//                 // v_array = actual_v;
//                 rand0 = $random();
//                 rand1 = $random();
//                 rand2 = $random();

//                 // $display("actual u = %h, actual v = %h", actual_u, actual_v);

//                 u[0] = actual_u-rand0;
//                 u[1] = rand0;
//                 v[0] = actual_v-rand1;
//                 v[1] = rand1;
//                 w[0] = actual_w-rand2;
//                 w[1] = rand2;
//                 // $display("u0 = %h, u1 = %h, v0 = %h, v1 = %h", u[0], u[1], v[0], v[1]);
//             end
//             begin
//                 repeat(264) @(posedge clk_tb);
//                 if ((dut.u_o_0 + dut.u_o_1) != ((actual_u_normalized + actual_v)%PRIME)) begin
//                     $error("U = u+v Mismatch: exp_output = %h   output shares = %h %h actual output = %h", (actual_u_normalized + actual_v)%PRIME, dut.u_o_0, dut.u_o_1, dut.u_o_0 + dut.u_o_1);
//                 end
//                 if ((dut.v_o_0 + dut.v_o_1) != (((actual_u_normalized - actual_v)*actual_w)%PRIME)) begin
//                     $error("V = (u-v)w Mismatch: exp_output = %h   output shares = %h %h actual output = %h", ((actual_u_normalized - actual_v)*actual_w)%PRIME, dut.v_o_0, dut.v_o_1, dut.v_o_0 + dut.v_o_1);
//                 end
//             end
//         join
//     end
// endtask

/*
task masked_pwm_test();
    logic [45:0] rand0, rand1, rand2;
    for (int i = 0; i < 10; i++) begin
        @(posedge clk_tb);
        fork
            begin
                actual_u = $random()%PRIME;
                actual_v = $random()%PRIME;
                actual_w = 'h2;

                // u_array = actual_u;
                // v_array = actual_v;
                rand0 = $random();
                rand1 = $random();
                rand2 = $random();

                // $display("actual u = %h, actual v = %h", actual_u, actual_v);

                u[0] = actual_u-rand0;
                u[1] = rand0;
                v[0] = actual_v-rand1;
                v[1] = rand1;
                w[0] = actual_w-rand2;
                w[1] = rand2;
                // $display("u0 = %h, u1 = %h, v0 = %h, v1 = %h", u[0], u[1], v[0], v[1]);
            end
            begin
                repeat(264) @(posedge clk_tb);
                if ((dut.res[0] + dut.res[1]) != ((((actual_u * actual_v)%PRIME)+actual_w) % PRIME)) begin
                    $error("U = u*v+w Mismatch: exp_output = %h   output shares = %h %h actual output = %h", ((((actual_u * actual_v)%PRIME)+actual_w) % PRIME), dut.res[0], dut.res[1], dut.res[0] + dut.res[1]);
                end
            end
        join
    end
endtask
*/

task div2(logic [REG_SIZE-1:0] in, output logic [REG_SIZE-1:0] out);
    if (in[0]) begin
        out = (in >> 1) + ((PRIME+1)/2);
    end
    else begin
        out = (in >> 1);
    end
endtask
/*
task masked_bfu_1x2_test();
    logic [45:0] rand0, rand1, rand2;
    logic [REG_SIZE:0] temp;
    for (int i = 0; i < 10; i++) begin
        @(posedge clk_tb);
        fork
            begin
                actual_u = $random()%PRIME;
                actual_v = $random()%PRIME;
                actual_w = 'h2;

                // u_array = actual_u;
                // v_array = actual_v;
                rand0 = $random()%PRIME;
                rand1 = $random()%PRIME;
                rand2 = $random()%PRIME;

                $display("actual u = %h, actual v = %h", actual_u, actual_v);

                u[0] = actual_u-rand0;
                u[1] = rand0;
                v[0] = actual_v-rand1;
                v[1] = rand1;
                w[0] = actual_w-rand2;
                w[1] = rand2;

                masked_uvw_i_tb.u00_i = u;
                masked_uvw_i_tb.u01_i = u;
                masked_uvw_i_tb.v00_i = v;
                masked_uvw_i_tb.v01_i = v;
                masked_uvw_i_tb.w00_i = w;
                masked_uvw_i_tb.w01_i = w;
                // $display("u0 = %h, u1 = %h, v0 = %h, v1 = %h", u[0], u[1], v[0], v[1]);
            end
            begin
                repeat(267) @(posedge clk_tb);
                $display("actual u = %h, actual v = %h", actual_u, actual_v);
                u10 = (actual_u+actual_v)%PRIME;
                if (actual_u < actual_v)
                    temp = actual_u + PRIME;
                else
                    temp = actual_u;
                v10 = (((temp-actual_v)%PRIME)*actual_w)%PRIME;
                $display("u10 = %h", u10);
                $display("v10 = %h", v10);
                $display("----------");
                div2(u10, uv_o_tb.u20_o);
                div2(v10, uv_o_tb.u21_o);
                div2(u10, uv_o_tb.v20_o); //since same inputs
                div2(v10, uv_o_tb.v21_o);

                if (dut.uv_o != uv_o_tb)
                    $error("Data mismatch. Expected = {%h, %h, %h, %h}, Observed = {%h, %h, %h, %h}", uv_o_tb.u20_o, uv_o_tb.u21_o, uv_o_tb.v20_o, uv_o_tb.v21_o, dut.uv_o.u20_o, dut.uv_o.u21_o, dut.uv_o.v20_o, dut.uv_o.v21_o);
                else
                    $display("Success: Matched results");
            end
        join
    end
endtask
*/

task masked_hybrid_bf_2x2_test();
    logic [45:0] rand0, rand1, rand2;
    for (int j = 0; j < 6; j++) begin
    mode_tb = j;
    for (int i = 0; i < 10; i++) begin
        @(posedge clk_tb);
        enable_tb = 1'b1;
        fork
            begin
                actual_u = $random()%PRIME;
                actual_v = $random()%PRIME;
                actual_w = 'h2;

                // u_array = actual_u;
                // v_array = actual_v;
                rand0 = $random();
                rand1 = $random();
                rand2 = $random();

                // $display("actual u = %h, actual v = %h", actual_u, actual_v);

                u[0] = actual_u-rand0;
                u[1] = rand0;
                v[0] = actual_v-rand1;
                v[1] = rand1;
                w[0] = actual_w-rand2;
                w[1] = rand2;

                uvw_i_tb.u00_i = actual_u;
                uvw_i_tb.u01_i = actual_u;
                uvw_i_tb.v00_i = actual_v;
                uvw_i_tb.v01_i = actual_v;
                uvw_i_tb.w00_i = actual_w;
                uvw_i_tb.w01_i = actual_w;
                uvw_i_tb.w10_i = actual_w;
                uvw_i_tb.w11_i = actual_w;

                pw_uvw_i_tb.u0_i = actual_u;
                pw_uvw_i_tb.v0_i = actual_v;
                pw_uvw_i_tb.w0_i = actual_w;

                pw_uvw_i_tb.u1_i = actual_u;
                pw_uvw_i_tb.v1_i = actual_v;
                pw_uvw_i_tb.w1_i = actual_w;

                pw_uvw_i_tb.u2_i = actual_u;
                pw_uvw_i_tb.v2_i = actual_v;
                pw_uvw_i_tb.w2_i = actual_w;

                pw_uvw_i_tb.u3_i = actual_u;
                pw_uvw_i_tb.v3_i = actual_v;
                pw_uvw_i_tb.w3_i = actual_w;
                //$display("u0 = %h, u1 = %h, v0 = %h, v1 = %h", u[0], u[1], v[0], v[1]);
            end
            // begin //TODO
            //     repeat(470) @(posedge clk_tb); //467 clks
            //     if ((dut.res[0] + dut.res[1]) != ((((actual_u * actual_v)%PRIME)+actual_w) % PRIME)) begin
            //         $error("U = u*v+w Mismatch: exp_output = %h   output shares = %h %h actual output = %h", ((((actual_u * actual_v)%PRIME)+actual_w) % PRIME), dut.res[0], dut.res[1], dut.res[0] + dut.res[1]);
            //     end
            // end
        join
    end
    enable_tb = 1'b0;
    @(posedge clk_tb);
    end
endtask


initial begin
    init_sim();
    reset_dut();

    @(posedge clk_tb);
    $display("Starting masked ntt test\n");
    
    // masked_BFU_adder_test();
    // masked_BFU_mult_test();
    // masked_gs_butterfly_test();
    // masked_pwm_test();
    masked_bfu_1x2_test();
    // masked_hybrid_bf_2x2_test();

    repeat(1000) @(posedge clk_tb);
    $finish;
end

endmodule