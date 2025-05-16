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
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either sibress or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//Sample In Ball Shuffler takes in two indexes (i and j) and a sign bit
//Indexes are used to address a 256 coefficient memory
//The value found in Index j is moved to Index i
//For sign value of 1, the value Q-1 is written to Index j, else 1 is written to Index j

module sample_in_ball_shuffler
  import abr_params_pkg::*;
  #(
     parameter SIB_SAMPLE_W = 8
  )
  (
    input logic                          clk,
    input logic                          rst_b,
    input logic                          zeroize,
    //input data
    input  logic                         valid_i,
    output logic                         hold_o,
    input  logic [SIB_SAMPLE_W-1:0]      indexi_i,
    input  logic [SIB_SAMPLE_W-1:0]      indexj_i,
    input  logic                         sign_i,

    //memory if 
    output logic [1:0]                         cs_o,
    output logic [1:0]                         we_o,
    output logic [1:0][7:2]                    addr_o,
    output logic [1:0][3:0][MLDSA_Q_WIDTH-2:0] wrdata_o,
    input  logic [1:0][3:0][MLDSA_Q_WIDTH-2:0] rddata_i

  );

  logic read_valid;
  logic addr_match;
  logic [MLDSA_Q_WIDTH-2:0] nxt_i, nxt_j;
  logic [3:0][MLDSA_Q_WIDTH-2:0] wrdata_pre;

  //hold the first phase
  always_comb hold_o = valid_i & ~read_valid;

  //Read phase
  //Read from entry pointed to by indexi_i and indexj_i
  always_comb addr_o[0] = indexj_i[7:2];
  always_comb addr_o[1] = indexi_i[7:2];

  always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b)begin
      read_valid <= 0;
    end else if (zeroize) begin
      read_valid <= 0;
    end else if (valid_i & ~read_valid) begin
      read_valid <= 1;
    end else begin
      read_valid <= 0;
    end
  end

  always_comb addr_match = indexi_i[7:2] == indexj_i[7:2];

  //Assign the nxt j value (contents of i, modified by sign bit)
  always_comb nxt_j = sign_i ? MLDSA_Q-1 : 1;

  //Write nxt_j into indexj_i location
  always_comb begin
    unique case (indexj_i[1:0])
      2'b00: wrdata_o[0] = {rddata_i[0][3],rddata_i[0][2],rddata_i[0][1],nxt_j       };
      2'b01: wrdata_o[0] = {rddata_i[0][3],rddata_i[0][2],nxt_j         ,rddata_i[0][0]};
      2'b10: wrdata_o[0] = {rddata_i[0][3],nxt_j         ,rddata_i[0][1],rddata_i[0][0]};
      2'b11: wrdata_o[0] = {nxt_j         ,rddata_i[0][2],rddata_i[0][1],rddata_i[0][0]};
      default: wrdata_o[0] = 'x;
    endcase
  end

  //Assign the nxt i value (contents of j)
  always_comb nxt_i = rddata_i[0][indexj_i[1:0]];

  //Write nxt_i into indexi_i location
  always_comb begin
    unique case ({indexi_i[1:0]})
      2'b00: wrdata_pre = {rddata_i[1][3],rddata_i[1][2],rddata_i[1][1],nxt_i       };
      2'b01: wrdata_pre = {rddata_i[1][3],rddata_i[1][2],nxt_i         ,rddata_i[1][0]};
      2'b10: wrdata_pre = {rddata_i[1][3],nxt_i         ,rddata_i[1][1],rddata_i[1][0]};
      2'b11: wrdata_pre = {nxt_i         ,rddata_i[1][2],rddata_i[1][1],rddata_i[1][0]};
      default: wrdata_pre = 'x;
    endcase
  end

  //If addr match, write nxt_j on same write port
  always_comb begin
    unique casez ({addr_match, indexj_i[1:0]})
      3'b0_??: wrdata_o[1] = wrdata_pre;
      3'b1_00: wrdata_o[1] = {wrdata_pre[3],wrdata_pre[2],wrdata_pre[1],nxt_j       };
      3'b1_01: wrdata_o[1] = {wrdata_pre[3],wrdata_pre[2],nxt_j        ,wrdata_pre[0]};
      3'b1_10: wrdata_o[1] = {wrdata_pre[3],nxt_j        ,wrdata_pre[1],wrdata_pre[0]};
      3'b1_11: wrdata_o[1] = {nxt_j        ,wrdata_pre[2],wrdata_pre[1],wrdata_pre[0]};
      default: wrdata_o[1] = 'x;
    endcase
  end

  always_comb cs_o = {2{valid_i}};
  always_comb we_o[0] = read_valid & ~addr_match;
  always_comb we_o[1] = read_valid;

endmodule
