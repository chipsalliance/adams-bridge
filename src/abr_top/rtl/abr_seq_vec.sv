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

//Vector-row annotation table for the ABR sequencer.
//
//This is a side table addressed in lockstep with abr_seq. It carries no
//instruction of its own; it only says, for the rows that belong to a (k, l)
//indexed vector or matrix loop, which index the row implements and whether the
//row's domain separator has to be recomputed. Every address that is not listed
//returns ABR_VEC_NONE, so a category-5 build behaves exactly as before: all of
//its rows are in range and no separator is overridden.
//
//Keeping this separate from abr_seq means the instruction ROM itself is left
//untouched, which makes "category 5 is unchanged" something that can be read
//off the diff rather than argued about.

module abr_seq_vec
  import abr_ctrl_pkg::*;
  (
  input logic clk,

  input  logic en_i,
  input  logic [ABR_PROG_ADDR_W-1 : 0] addr_i,
  output abr_vec_ctrl_t data_o
  );

`ifdef RV_FPGA_OPTIMIZE
    (*rom_style = "block" *) abr_vec_ctrl_t data_o_rom;
`else
    abr_vec_ctrl_t data_o_rom;
`endif
    assign data_o = data_o_rom;

  always_ff @(posedge clk) begin
        if (en_i) begin
            unique case(addr_i)
                //ML-DSA keygen: ExpandS s1 rows (l of them)
                MLDSA_KG_S+ 6  : data_o_rom <= abr_vec_s1(4'd0);
                MLDSA_KG_S+ 7  : data_o_rom <= abr_vec_s1(4'd1);
                MLDSA_KG_S+ 8  : data_o_rom <= abr_vec_s1(4'd2);
                MLDSA_KG_S+ 9  : data_o_rom <= abr_vec_s1(4'd3);
                MLDSA_KG_S+ 10 : data_o_rom <= abr_vec_s1(4'd4);
                MLDSA_KG_S+ 11 : data_o_rom <= abr_vec_s1(4'd5);
                MLDSA_KG_S+ 12 : data_o_rom <= abr_vec_s1(4'd6);
                //ML-DSA keygen: ExpandS s2 rows (k of them, separators follow s1)
                MLDSA_KG_S+ 13 : data_o_rom <= abr_vec_s2(4'd0);
                MLDSA_KG_S+ 14 : data_o_rom <= abr_vec_s2(4'd1);
                MLDSA_KG_S+ 15 : data_o_rom <= abr_vec_s2(4'd2);
                MLDSA_KG_S+ 16 : data_o_rom <= abr_vec_s2(4'd3);
                MLDSA_KG_S+ 17 : data_o_rom <= abr_vec_s2(4'd4);
                MLDSA_KG_S+ 18 : data_o_rom <= abr_vec_s2(4'd5);
                MLDSA_KG_S+ 19 : data_o_rom <= abr_vec_s2(4'd6);
                MLDSA_KG_S+ 20 : data_o_rom <= abr_vec_s2(4'd7);
                //ML-DSA keygen: NTT(s1) rows
                MLDSA_KG_S+ 21 : data_o_rom <= abr_vec_l(4'd0);
                MLDSA_KG_S+ 22 : data_o_rom <= abr_vec_l(4'd1);
                MLDSA_KG_S+ 23 : data_o_rom <= abr_vec_l(4'd2);
                MLDSA_KG_S+ 24 : data_o_rom <= abr_vec_l(4'd3);
                MLDSA_KG_S+ 25 : data_o_rom <= abr_vec_l(4'd4);
                MLDSA_KG_S+ 26 : data_o_rom <= abr_vec_l(4'd5);
                MLDSA_KG_S+ 27 : data_o_rom <= abr_vec_l(4'd6);
                //ML-DSA keygen: per matrix row i, ExpandA(i,j) then INTT and t_i = .. + s2_i
                MLDSA_KG_S+ 28 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 29 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 30 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 31 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 32 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 33 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 34 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 35 : data_o_rom <= abr_vec_k(4'd0);
                MLDSA_KG_S+ 36 : data_o_rom <= abr_vec_k(4'd0);
                MLDSA_KG_S+ 37 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 38 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 39 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 40 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 41 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 42 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 43 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 44 : data_o_rom <= abr_vec_k(4'd1);
                MLDSA_KG_S+ 45 : data_o_rom <= abr_vec_k(4'd1);
                MLDSA_KG_S+ 46 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 47 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 48 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 49 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 50 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 51 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 52 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 53 : data_o_rom <= abr_vec_k(4'd2);
                MLDSA_KG_S+ 54 : data_o_rom <= abr_vec_k(4'd2);
                MLDSA_KG_S+ 55 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 56 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 57 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 58 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 59 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 60 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 61 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 62 : data_o_rom <= abr_vec_k(4'd3);
                MLDSA_KG_S+ 63 : data_o_rom <= abr_vec_k(4'd3);
                MLDSA_KG_S+ 64 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 65 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 66 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 67 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 68 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 69 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 70 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 71 : data_o_rom <= abr_vec_k(4'd4);
                MLDSA_KG_S+ 72 : data_o_rom <= abr_vec_k(4'd4);
                MLDSA_KG_S+ 73 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 74 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 75 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 76 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 77 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 78 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 79 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 80 : data_o_rom <= abr_vec_k(4'd5);
                MLDSA_KG_S+ 81 : data_o_rom <= abr_vec_k(4'd5);
                MLDSA_KG_S+ 82 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 83 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 84 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 85 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 86 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 87 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 88 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 89 : data_o_rom <= abr_vec_k(4'd6);
                MLDSA_KG_S+ 90 : data_o_rom <= abr_vec_k(4'd6);
                MLDSA_KG_S+ 91 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 92 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 93 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 94 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 95 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 96 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 97 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_KG_S+ 98 : data_o_rom <= abr_vec_k(4'd7);
                MLDSA_KG_S+ 99 : data_o_rom <= abr_vec_k(4'd7);

                //ML-DSA sign: NTT(t) rows
                MLDSA_SIGN_INIT_S+1  : data_o_rom <= abr_vec_k(4'd0);
                MLDSA_SIGN_INIT_S+2  : data_o_rom <= abr_vec_k(4'd1);
                MLDSA_SIGN_INIT_S+3  : data_o_rom <= abr_vec_k(4'd2);
                MLDSA_SIGN_INIT_S+4  : data_o_rom <= abr_vec_k(4'd3);
                MLDSA_SIGN_INIT_S+5  : data_o_rom <= abr_vec_k(4'd4);
                MLDSA_SIGN_INIT_S+6  : data_o_rom <= abr_vec_k(4'd5);
                MLDSA_SIGN_INIT_S+7  : data_o_rom <= abr_vec_k(4'd6);
                MLDSA_SIGN_INIT_S+8  : data_o_rom <= abr_vec_k(4'd7);
                //ML-DSA sign: NTT(s1) rows
                MLDSA_SIGN_INIT_S+9  : data_o_rom <= abr_vec_l(4'd0);
                MLDSA_SIGN_INIT_S+10 : data_o_rom <= abr_vec_l(4'd1);
                MLDSA_SIGN_INIT_S+11 : data_o_rom <= abr_vec_l(4'd2);
                MLDSA_SIGN_INIT_S+12 : data_o_rom <= abr_vec_l(4'd3);
                MLDSA_SIGN_INIT_S+13 : data_o_rom <= abr_vec_l(4'd4);
                MLDSA_SIGN_INIT_S+14 : data_o_rom <= abr_vec_l(4'd5);
                MLDSA_SIGN_INIT_S+15 : data_o_rom <= abr_vec_l(4'd6);
                //ML-DSA sign: NTT(s2) rows
                MLDSA_SIGN_INIT_S+16 : data_o_rom <= abr_vec_k(4'd0);
                MLDSA_SIGN_INIT_S+17 : data_o_rom <= abr_vec_k(4'd1);
                MLDSA_SIGN_INIT_S+18 : data_o_rom <= abr_vec_k(4'd2);
                MLDSA_SIGN_INIT_S+19 : data_o_rom <= abr_vec_k(4'd3);
                MLDSA_SIGN_INIT_S+20 : data_o_rom <= abr_vec_k(4'd4);
                MLDSA_SIGN_INIT_S+21 : data_o_rom <= abr_vec_k(4'd5);
                MLDSA_SIGN_INIT_S+22 : data_o_rom <= abr_vec_k(4'd6);
                MLDSA_SIGN_INIT_S+23 : data_o_rom <= abr_vec_k(4'd7);
                //ML-DSA sign: ExpandMask(rho', kappa) rows, then NTT(y)
                MLDSA_SIGN_MAKE_Y_S+0  : data_o_rom <= abr_vec_l(4'd0);
                MLDSA_SIGN_MAKE_Y_S+1  : data_o_rom <= abr_vec_l(4'd1);
                MLDSA_SIGN_MAKE_Y_S+2  : data_o_rom <= abr_vec_l(4'd2);
                MLDSA_SIGN_MAKE_Y_S+3  : data_o_rom <= abr_vec_l(4'd3);
                MLDSA_SIGN_MAKE_Y_S+4  : data_o_rom <= abr_vec_l(4'd4);
                MLDSA_SIGN_MAKE_Y_S+5  : data_o_rom <= abr_vec_l(4'd5);
                MLDSA_SIGN_MAKE_Y_S+6  : data_o_rom <= abr_vec_l(4'd6);
                MLDSA_SIGN_MAKE_Y_S+7  : data_o_rom <= abr_vec_l(4'd0);
                MLDSA_SIGN_MAKE_Y_S+8  : data_o_rom <= abr_vec_l(4'd1);
                MLDSA_SIGN_MAKE_Y_S+9  : data_o_rom <= abr_vec_l(4'd2);
                MLDSA_SIGN_MAKE_Y_S+10 : data_o_rom <= abr_vec_l(4'd3);
                MLDSA_SIGN_MAKE_Y_S+11 : data_o_rom <= abr_vec_l(4'd4);
                MLDSA_SIGN_MAKE_Y_S+12 : data_o_rom <= abr_vec_l(4'd5);
                MLDSA_SIGN_MAKE_Y_S+13 : data_o_rom <= abr_vec_l(4'd6);
                //ML-DSA sign: per matrix row i, ExpandA(i,j) then INTT into w0_i
                MLDSA_SIGN_MAKE_W_S+0  : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+1  : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+2  : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+3  : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+4  : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+5  : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+6  : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+7  : data_o_rom <= abr_vec_k(4'd0);
                MLDSA_SIGN_MAKE_W_S+8  : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+9  : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+10 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+11 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+12 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+13 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+14 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+15 : data_o_rom <= abr_vec_k(4'd1);
                MLDSA_SIGN_MAKE_W_S+16 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+17 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+18 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+19 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+20 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+21 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+22 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+23 : data_o_rom <= abr_vec_k(4'd2);
                MLDSA_SIGN_MAKE_W_S+24 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+25 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+26 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+27 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+28 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+29 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+30 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+31 : data_o_rom <= abr_vec_k(4'd3);
                MLDSA_SIGN_MAKE_W_S+32 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+33 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+34 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+35 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+36 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+37 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+38 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+39 : data_o_rom <= abr_vec_k(4'd4);
                MLDSA_SIGN_MAKE_W_S+40 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+41 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+42 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+43 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+44 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+45 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+46 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+47 : data_o_rom <= abr_vec_k(4'd5);
                MLDSA_SIGN_MAKE_W_S+48 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+49 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+50 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+51 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+52 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+53 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+54 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+55 : data_o_rom <= abr_vec_k(4'd6);
                MLDSA_SIGN_MAKE_W_S+56 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+57 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+58 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+59 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+60 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+61 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+62 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_SIGN_MAKE_W_S+63 : data_o_rom <= abr_vec_k(4'd7);
                //ML-DSA verify: per-row z norm checks
                //ML-DSA sign, challenge loop. These rows were never exercised at
                //category 5 (l=7, k=8 leaves every row in range), so they are tagged
                //here for the first time. z = y + c*s1 is l-indexed, 5 rows per row of z.
                MLDSA_SIGN_VALID_S+1   : data_o_rom <= abr_vec_l(4'd0);
                MLDSA_SIGN_VALID_S+2   : data_o_rom <= abr_vec_l(4'd0);
                MLDSA_SIGN_VALID_S+3   : data_o_rom <= abr_vec_l(4'd0);
                MLDSA_SIGN_VALID_S+4   : data_o_rom <= abr_vec_l(4'd0);
                MLDSA_SIGN_VALID_S+5   : data_o_rom <= abr_vec_l(4'd0);

                MLDSA_SIGN_VALID_S+6   : data_o_rom <= abr_vec_l(4'd1);
                MLDSA_SIGN_VALID_S+7   : data_o_rom <= abr_vec_l(4'd1);
                MLDSA_SIGN_VALID_S+8   : data_o_rom <= abr_vec_l(4'd1);
                MLDSA_SIGN_VALID_S+9   : data_o_rom <= abr_vec_l(4'd1);
                MLDSA_SIGN_VALID_S+10  : data_o_rom <= abr_vec_l(4'd1);

                MLDSA_SIGN_VALID_S+11  : data_o_rom <= abr_vec_l(4'd2);
                MLDSA_SIGN_VALID_S+12  : data_o_rom <= abr_vec_l(4'd2);
                MLDSA_SIGN_VALID_S+13  : data_o_rom <= abr_vec_l(4'd2);
                MLDSA_SIGN_VALID_S+14  : data_o_rom <= abr_vec_l(4'd2);
                MLDSA_SIGN_VALID_S+15  : data_o_rom <= abr_vec_l(4'd2);

                MLDSA_SIGN_VALID_S+16  : data_o_rom <= abr_vec_l(4'd3);
                MLDSA_SIGN_VALID_S+17  : data_o_rom <= abr_vec_l(4'd3);
                MLDSA_SIGN_VALID_S+18  : data_o_rom <= abr_vec_l(4'd3);
                MLDSA_SIGN_VALID_S+19  : data_o_rom <= abr_vec_l(4'd3);
                MLDSA_SIGN_VALID_S+20  : data_o_rom <= abr_vec_l(4'd3);

                MLDSA_SIGN_VALID_S+21  : data_o_rom <= abr_vec_l(4'd4);
                MLDSA_SIGN_VALID_S+22  : data_o_rom <= abr_vec_l(4'd4);
                MLDSA_SIGN_VALID_S+23  : data_o_rom <= abr_vec_l(4'd4);
                MLDSA_SIGN_VALID_S+24  : data_o_rom <= abr_vec_l(4'd4);
                MLDSA_SIGN_VALID_S+25  : data_o_rom <= abr_vec_l(4'd4);

                MLDSA_SIGN_VALID_S+26  : data_o_rom <= abr_vec_l(4'd5);
                MLDSA_SIGN_VALID_S+27  : data_o_rom <= abr_vec_l(4'd5);
                MLDSA_SIGN_VALID_S+28  : data_o_rom <= abr_vec_l(4'd5);
                MLDSA_SIGN_VALID_S+29  : data_o_rom <= abr_vec_l(4'd5);
                MLDSA_SIGN_VALID_S+30  : data_o_rom <= abr_vec_l(4'd5);

                MLDSA_SIGN_VALID_S+31  : data_o_rom <= abr_vec_l(4'd6);
                MLDSA_SIGN_VALID_S+32  : data_o_rom <= abr_vec_l(4'd6);
                MLDSA_SIGN_VALID_S+33  : data_o_rom <= abr_vec_l(4'd6);
                MLDSA_SIGN_VALID_S+34  : data_o_rom <= abr_vec_l(4'd6);
                MLDSA_SIGN_VALID_S+35  : data_o_rom <= abr_vec_l(4'd6);

                //c*t0 is k-indexed, 2 rows per row of t0.
                MLDSA_SIGN_VALID_S+36  : data_o_rom <= abr_vec_k(4'd0);
                MLDSA_SIGN_VALID_S+37  : data_o_rom <= abr_vec_k(4'd0);

                MLDSA_SIGN_VALID_S+38  : data_o_rom <= abr_vec_k(4'd1);
                MLDSA_SIGN_VALID_S+39  : data_o_rom <= abr_vec_k(4'd1);

                MLDSA_SIGN_VALID_S+40  : data_o_rom <= abr_vec_k(4'd2);
                MLDSA_SIGN_VALID_S+41  : data_o_rom <= abr_vec_k(4'd2);

                MLDSA_SIGN_VALID_S+42  : data_o_rom <= abr_vec_k(4'd3);
                MLDSA_SIGN_VALID_S+43  : data_o_rom <= abr_vec_k(4'd3);

                MLDSA_SIGN_VALID_S+44  : data_o_rom <= abr_vec_k(4'd4);
                MLDSA_SIGN_VALID_S+45  : data_o_rom <= abr_vec_k(4'd4);

                MLDSA_SIGN_VALID_S+46  : data_o_rom <= abr_vec_k(4'd5);
                MLDSA_SIGN_VALID_S+47  : data_o_rom <= abr_vec_k(4'd5);

                MLDSA_SIGN_VALID_S+48  : data_o_rom <= abr_vec_k(4'd6);
                MLDSA_SIGN_VALID_S+49  : data_o_rom <= abr_vec_k(4'd6);

                MLDSA_SIGN_VALID_S+50  : data_o_rom <= abr_vec_k(4'd7);
                MLDSA_SIGN_VALID_S+51  : data_o_rom <= abr_vec_k(4'd7);

                //r0 / ct0 / hint is k-indexed, 6 rows per row of w0.
                MLDSA_SIGN_VALID_S+52  : data_o_rom <= abr_vec_k(4'd0);
                MLDSA_SIGN_VALID_S+53  : data_o_rom <= abr_vec_k(4'd0);
                MLDSA_SIGN_VALID_S+54  : data_o_rom <= abr_vec_k(4'd0);
                MLDSA_SIGN_VALID_S+55  : data_o_rom <= abr_vec_k(4'd0);
                MLDSA_SIGN_VALID_S+56  : data_o_rom <= abr_vec_k(4'd0);
                MLDSA_SIGN_VALID_S+57  : data_o_rom <= abr_vec_k(4'd0);

                MLDSA_SIGN_VALID_S+58  : data_o_rom <= abr_vec_k(4'd1);
                MLDSA_SIGN_VALID_S+59  : data_o_rom <= abr_vec_k(4'd1);
                MLDSA_SIGN_VALID_S+60  : data_o_rom <= abr_vec_k(4'd1);
                MLDSA_SIGN_VALID_S+61  : data_o_rom <= abr_vec_k(4'd1);
                MLDSA_SIGN_VALID_S+62  : data_o_rom <= abr_vec_k(4'd1);
                MLDSA_SIGN_VALID_S+63  : data_o_rom <= abr_vec_k(4'd1);

                MLDSA_SIGN_VALID_S+64  : data_o_rom <= abr_vec_k(4'd2);
                MLDSA_SIGN_VALID_S+65  : data_o_rom <= abr_vec_k(4'd2);
                MLDSA_SIGN_VALID_S+66  : data_o_rom <= abr_vec_k(4'd2);
                MLDSA_SIGN_VALID_S+67  : data_o_rom <= abr_vec_k(4'd2);
                MLDSA_SIGN_VALID_S+68  : data_o_rom <= abr_vec_k(4'd2);
                MLDSA_SIGN_VALID_S+69  : data_o_rom <= abr_vec_k(4'd2);

                MLDSA_SIGN_VALID_S+70  : data_o_rom <= abr_vec_k(4'd3);
                MLDSA_SIGN_VALID_S+71  : data_o_rom <= abr_vec_k(4'd3);
                MLDSA_SIGN_VALID_S+72  : data_o_rom <= abr_vec_k(4'd3);
                MLDSA_SIGN_VALID_S+73  : data_o_rom <= abr_vec_k(4'd3);
                MLDSA_SIGN_VALID_S+74  : data_o_rom <= abr_vec_k(4'd3);
                MLDSA_SIGN_VALID_S+75  : data_o_rom <= abr_vec_k(4'd3);

                MLDSA_SIGN_VALID_S+76  : data_o_rom <= abr_vec_k(4'd4);
                MLDSA_SIGN_VALID_S+77  : data_o_rom <= abr_vec_k(4'd4);
                MLDSA_SIGN_VALID_S+78  : data_o_rom <= abr_vec_k(4'd4);
                MLDSA_SIGN_VALID_S+79  : data_o_rom <= abr_vec_k(4'd4);
                MLDSA_SIGN_VALID_S+80  : data_o_rom <= abr_vec_k(4'd4);
                MLDSA_SIGN_VALID_S+81  : data_o_rom <= abr_vec_k(4'd4);

                MLDSA_SIGN_VALID_S+82  : data_o_rom <= abr_vec_k(4'd5);
                MLDSA_SIGN_VALID_S+83  : data_o_rom <= abr_vec_k(4'd5);
                MLDSA_SIGN_VALID_S+84  : data_o_rom <= abr_vec_k(4'd5);
                MLDSA_SIGN_VALID_S+85  : data_o_rom <= abr_vec_k(4'd5);
                MLDSA_SIGN_VALID_S+86  : data_o_rom <= abr_vec_k(4'd5);
                MLDSA_SIGN_VALID_S+87  : data_o_rom <= abr_vec_k(4'd5);

                MLDSA_SIGN_VALID_S+88  : data_o_rom <= abr_vec_k(4'd6);
                MLDSA_SIGN_VALID_S+89  : data_o_rom <= abr_vec_k(4'd6);
                MLDSA_SIGN_VALID_S+90  : data_o_rom <= abr_vec_k(4'd6);
                MLDSA_SIGN_VALID_S+91  : data_o_rom <= abr_vec_k(4'd6);
                MLDSA_SIGN_VALID_S+92  : data_o_rom <= abr_vec_k(4'd6);
                MLDSA_SIGN_VALID_S+93  : data_o_rom <= abr_vec_k(4'd6);

                MLDSA_SIGN_VALID_S+94  : data_o_rom <= abr_vec_k(4'd7);
                MLDSA_SIGN_VALID_S+95  : data_o_rom <= abr_vec_k(4'd7);
                MLDSA_SIGN_VALID_S+96  : data_o_rom <= abr_vec_k(4'd7);
                MLDSA_SIGN_VALID_S+97  : data_o_rom <= abr_vec_k(4'd7);
                MLDSA_SIGN_VALID_S+98  : data_o_rom <= abr_vec_k(4'd7);
                MLDSA_SIGN_VALID_S+99  : data_o_rom <= abr_vec_k(4'd7);


                MLDSA_VERIFY_S+2      : data_o_rom <= abr_vec_l(4'd0);
                MLDSA_VERIFY_S+3      : data_o_rom <= abr_vec_l(4'd1);
                MLDSA_VERIFY_S+4      : data_o_rom <= abr_vec_l(4'd2);
                MLDSA_VERIFY_S+5      : data_o_rom <= abr_vec_l(4'd3);
                MLDSA_VERIFY_S+6      : data_o_rom <= abr_vec_l(4'd4);
                MLDSA_VERIFY_S+7      : data_o_rom <= abr_vec_l(4'd5);
                MLDSA_VERIFY_S+8      : data_o_rom <= abr_vec_l(4'd6);
                //ML-DSA verify: NTT(t1) rows
                MLDSA_VERIFY_NTT_T1+0  : data_o_rom <= abr_vec_k(4'd0);
                MLDSA_VERIFY_NTT_T1+1  : data_o_rom <= abr_vec_k(4'd1);
                MLDSA_VERIFY_NTT_T1+2  : data_o_rom <= abr_vec_k(4'd2);
                MLDSA_VERIFY_NTT_T1+3  : data_o_rom <= abr_vec_k(4'd3);
                MLDSA_VERIFY_NTT_T1+4  : data_o_rom <= abr_vec_k(4'd4);
                MLDSA_VERIFY_NTT_T1+5  : data_o_rom <= abr_vec_k(4'd5);
                MLDSA_VERIFY_NTT_T1+6  : data_o_rom <= abr_vec_k(4'd6);
                MLDSA_VERIFY_NTT_T1+7  : data_o_rom <= abr_vec_k(4'd7);
                //ML-DSA verify: NTT(z) rows
                MLDSA_VERIFY_NTT_Z+0   : data_o_rom <= abr_vec_l(4'd0);
                MLDSA_VERIFY_NTT_Z+1   : data_o_rom <= abr_vec_l(4'd1);
                MLDSA_VERIFY_NTT_Z+2   : data_o_rom <= abr_vec_l(4'd2);
                MLDSA_VERIFY_NTT_Z+3   : data_o_rom <= abr_vec_l(4'd3);
                MLDSA_VERIFY_NTT_Z+4   : data_o_rom <= abr_vec_l(4'd4);
                MLDSA_VERIFY_NTT_Z+5   : data_o_rom <= abr_vec_l(4'd5);
                MLDSA_VERIFY_NTT_Z+6   : data_o_rom <= abr_vec_l(4'd6);
                //ML-DSA verify: per matrix row i, ExpandA(i,j), c*t1_i, subtract, INTT
                MLDSA_VERIFY_EXP_A+0  : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+1  : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+2  : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+3  : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+4  : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+5  : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+6  : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+7  : data_o_rom <= abr_vec_k(4'd0);
                MLDSA_VERIFY_EXP_A+8  : data_o_rom <= abr_vec_k(4'd0);
                MLDSA_VERIFY_EXP_A+9  : data_o_rom <= abr_vec_k(4'd0);
                MLDSA_VERIFY_EXP_A+10 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+11 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+12 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+13 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+14 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+15 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+16 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+17 : data_o_rom <= abr_vec_k(4'd1);
                MLDSA_VERIFY_EXP_A+18 : data_o_rom <= abr_vec_k(4'd1);
                MLDSA_VERIFY_EXP_A+19 : data_o_rom <= abr_vec_k(4'd1);
                MLDSA_VERIFY_EXP_A+20 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+21 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+22 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+23 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+24 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+25 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+26 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+27 : data_o_rom <= abr_vec_k(4'd2);
                MLDSA_VERIFY_EXP_A+28 : data_o_rom <= abr_vec_k(4'd2);
                MLDSA_VERIFY_EXP_A+29 : data_o_rom <= abr_vec_k(4'd2);
                MLDSA_VERIFY_EXP_A+30 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+31 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+32 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+33 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+34 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+35 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+36 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+37 : data_o_rom <= abr_vec_k(4'd3);
                MLDSA_VERIFY_EXP_A+38 : data_o_rom <= abr_vec_k(4'd3);
                MLDSA_VERIFY_EXP_A+39 : data_o_rom <= abr_vec_k(4'd3);
                MLDSA_VERIFY_EXP_A+40 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+41 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+42 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+43 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+44 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+45 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+46 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+47 : data_o_rom <= abr_vec_k(4'd4);
                MLDSA_VERIFY_EXP_A+48 : data_o_rom <= abr_vec_k(4'd4);
                MLDSA_VERIFY_EXP_A+49 : data_o_rom <= abr_vec_k(4'd4);
                MLDSA_VERIFY_EXP_A+50 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+51 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+52 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+53 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+54 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+55 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+56 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+57 : data_o_rom <= abr_vec_k(4'd5);
                MLDSA_VERIFY_EXP_A+58 : data_o_rom <= abr_vec_k(4'd5);
                MLDSA_VERIFY_EXP_A+59 : data_o_rom <= abr_vec_k(4'd5);
                MLDSA_VERIFY_EXP_A+60 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+61 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+62 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+63 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+64 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+65 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+66 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+67 : data_o_rom <= abr_vec_k(4'd6);
                MLDSA_VERIFY_EXP_A+68 : data_o_rom <= abr_vec_k(4'd6);
                MLDSA_VERIFY_EXP_A+69 : data_o_rom <= abr_vec_k(4'd6);
                MLDSA_VERIFY_EXP_A+70 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+71 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+72 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+73 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+74 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+75 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+76 : data_o_rom <= ABR_VEC_MAT_A;
                MLDSA_VERIFY_EXP_A+77 : data_o_rom <= abr_vec_k(4'd7);
                MLDSA_VERIFY_EXP_A+78 : data_o_rom <= abr_vec_k(4'd7);
                MLDSA_VERIFY_EXP_A+79 : data_o_rom <= abr_vec_k(4'd7);
                //ML-KEM keygen: CBD s/e, NTT, A*s + e
                MLKEM_KG_S+6       : data_o_rom <= abr_vec_s1(4'd0);
                MLKEM_KG_S+7       : data_o_rom <= abr_vec_s1(4'd1);
                MLKEM_KG_S+8       : data_o_rom <= abr_vec_s1(4'd2);
                MLKEM_KG_S+9       : data_o_rom <= abr_vec_s1(4'd3);
                MLKEM_KG_S+10     : data_o_rom <= abr_vec_e(4'd0);
                MLKEM_KG_S+11     : data_o_rom <= abr_vec_e(4'd1);
                MLKEM_KG_S+12     : data_o_rom <= abr_vec_e(4'd2);
                MLKEM_KG_S+13     : data_o_rom <= abr_vec_e(4'd3);
                MLKEM_KG_S+14     : data_o_rom <= abr_vec_k(4'd0);
                MLKEM_KG_S+15     : data_o_rom <= abr_vec_k(4'd1);
                MLKEM_KG_S+16     : data_o_rom <= abr_vec_k(4'd2);
                MLKEM_KG_S+17     : data_o_rom <= abr_vec_k(4'd3);
                MLKEM_KG_S+18     : data_o_rom <= abr_vec_k(4'd0);
                MLKEM_KG_S+19     : data_o_rom <= abr_vec_k(4'd1);
                MLKEM_KG_S+20     : data_o_rom <= abr_vec_k(4'd2);
                MLKEM_KG_S+21     : data_o_rom <= abr_vec_k(4'd3);
                MLKEM_KG_S+22     : data_o_rom <= ABR_VEC_MAT_A;
                MLKEM_KG_S+23     : data_o_rom <= ABR_VEC_MAT_A;
                MLKEM_KG_S+24     : data_o_rom <= ABR_VEC_MAT_A;
                MLKEM_KG_S+25     : data_o_rom <= ABR_VEC_MAT_A;
                MLKEM_KG_S+26     : data_o_rom <= abr_vec_k(4'd0);
                MLKEM_KG_S+27     : data_o_rom <= ABR_VEC_MAT_A;
                MLKEM_KG_S+28     : data_o_rom <= ABR_VEC_MAT_A;
                MLKEM_KG_S+29     : data_o_rom <= ABR_VEC_MAT_A;
                MLKEM_KG_S+30     : data_o_rom <= ABR_VEC_MAT_A;
                MLKEM_KG_S+31     : data_o_rom <= abr_vec_k(4'd1);
                MLKEM_KG_S+32     : data_o_rom <= ABR_VEC_MAT_A;
                MLKEM_KG_S+33     : data_o_rom <= ABR_VEC_MAT_A;
                MLKEM_KG_S+34     : data_o_rom <= ABR_VEC_MAT_A;
                MLKEM_KG_S+35     : data_o_rom <= ABR_VEC_MAT_A;
                MLKEM_KG_S+36     : data_o_rom <= abr_vec_k(4'd2);
                MLKEM_KG_S+37     : data_o_rom <= ABR_VEC_MAT_A;
                MLKEM_KG_S+38     : data_o_rom <= ABR_VEC_MAT_A;
                MLKEM_KG_S+39     : data_o_rom <= ABR_VEC_MAT_A;
                MLKEM_KG_S+40     : data_o_rom <= ABR_VEC_MAT_A;
                MLKEM_KG_S+41     : data_o_rom <= abr_vec_k(4'd3);
                //ML-KEM encaps: CBD y/e1/e2, NTT(y), A^T*y + e1, t^T*y
                MLKEM_ENCAPS_S+10  : data_o_rom <= abr_vec_s1(4'd0);
                MLKEM_ENCAPS_S+11  : data_o_rom <= abr_vec_s1(4'd1);
                MLKEM_ENCAPS_S+12  : data_o_rom <= abr_vec_s1(4'd2);
                MLKEM_ENCAPS_S+13  : data_o_rom <= abr_vec_s1(4'd3);
                MLKEM_ENCAPS_S+14  : data_o_rom <= abr_vec_e(4'd0);
                MLKEM_ENCAPS_S+15  : data_o_rom <= abr_vec_e(4'd1);
                MLKEM_ENCAPS_S+16  : data_o_rom <= abr_vec_e(4'd2);
                MLKEM_ENCAPS_S+17  : data_o_rom <= abr_vec_e(4'd3);
                MLKEM_ENCAPS_S+18  : data_o_rom <= abr_vec_e2();
                MLKEM_ENCAPS_S+19  : data_o_rom <= abr_vec_k(4'd0);
                MLKEM_ENCAPS_S+20  : data_o_rom <= abr_vec_k(4'd1);
                MLKEM_ENCAPS_S+21  : data_o_rom <= abr_vec_k(4'd2);
                MLKEM_ENCAPS_S+22  : data_o_rom <= abr_vec_k(4'd3);
                MLKEM_ENCAPS_S+23  : data_o_rom <= ABR_VEC_MAT_A;
                MLKEM_ENCAPS_S+24  : data_o_rom <= ABR_VEC_MAT_A;
                MLKEM_ENCAPS_S+25  : data_o_rom <= ABR_VEC_MAT_A;
                MLKEM_ENCAPS_S+26  : data_o_rom <= ABR_VEC_MAT_A;
                MLKEM_ENCAPS_S+27  : data_o_rom <= abr_vec_k(4'd0);
                MLKEM_ENCAPS_S+28  : data_o_rom <= abr_vec_k(4'd0);
                MLKEM_ENCAPS_S+29  : data_o_rom <= ABR_VEC_MAT_A;
                MLKEM_ENCAPS_S+30  : data_o_rom <= ABR_VEC_MAT_A;
                MLKEM_ENCAPS_S+31  : data_o_rom <= ABR_VEC_MAT_A;
                MLKEM_ENCAPS_S+32  : data_o_rom <= ABR_VEC_MAT_A;
                MLKEM_ENCAPS_S+33  : data_o_rom <= abr_vec_k(4'd1);
                MLKEM_ENCAPS_S+34  : data_o_rom <= abr_vec_k(4'd1);
                MLKEM_ENCAPS_S+35  : data_o_rom <= ABR_VEC_MAT_A;
                MLKEM_ENCAPS_S+36  : data_o_rom <= ABR_VEC_MAT_A;
                MLKEM_ENCAPS_S+37  : data_o_rom <= ABR_VEC_MAT_A;
                MLKEM_ENCAPS_S+38  : data_o_rom <= ABR_VEC_MAT_A;
                MLKEM_ENCAPS_S+39  : data_o_rom <= abr_vec_k(4'd2);
                MLKEM_ENCAPS_S+40  : data_o_rom <= abr_vec_k(4'd2);
                MLKEM_ENCAPS_S+41  : data_o_rom <= ABR_VEC_MAT_A;
                MLKEM_ENCAPS_S+42  : data_o_rom <= ABR_VEC_MAT_A;
                MLKEM_ENCAPS_S+43  : data_o_rom <= ABR_VEC_MAT_A;
                MLKEM_ENCAPS_S+44  : data_o_rom <= ABR_VEC_MAT_A;
                MLKEM_ENCAPS_S+45  : data_o_rom <= abr_vec_k(4'd3);
                MLKEM_ENCAPS_S+46  : data_o_rom <= abr_vec_k(4'd3);
                MLKEM_ENCAPS_S+47  : data_o_rom <= abr_vec_k(4'd0);
                MLKEM_ENCAPS_S+48  : data_o_rom <= abr_vec_k(4'd1);
                MLKEM_ENCAPS_S+49  : data_o_rom <= abr_vec_k(4'd2);
                MLKEM_ENCAPS_S+50  : data_o_rom <= abr_vec_k(4'd3);
                //ML-KEM decaps: NTT(u), s^T*u
                MLKEM_DECAPS_S+9   : data_o_rom <= abr_vec_k(4'd0);
                MLKEM_DECAPS_S+10  : data_o_rom <= abr_vec_k(4'd1);
                MLKEM_DECAPS_S+11  : data_o_rom <= abr_vec_k(4'd2);
                MLKEM_DECAPS_S+12  : data_o_rom <= abr_vec_k(4'd3);
                MLKEM_DECAPS_S+13  : data_o_rom <= abr_vec_k(4'd0);
                MLKEM_DECAPS_S+14  : data_o_rom <= abr_vec_k(4'd1);
                MLKEM_DECAPS_S+15  : data_o_rom <= abr_vec_k(4'd2);
                MLKEM_DECAPS_S+16  : data_o_rom <= abr_vec_k(4'd3);
                default : data_o_rom <= ABR_VEC_NONE;
            endcase
        end
  end

endmodule
