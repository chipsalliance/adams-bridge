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

// -------------------------------------------------
// Copyright(c) LUBIS EDA GmbH, All rights reserved
// Contact: contact@lubis-eda.com
// -------------------------------------------------


module fv_makehint_scoreboard
    import mldsa_params_pkg::*;
#(
    parameter REG_SIZE      = 24,
    parameter MLDSA_Q       = 23'd8380417,
    parameter MLDSA_N       = 256,
    parameter MLDSA_K       = 8,
    parameter OMEGA         = 75,
    parameter BUFFER_DATA_W = 8
    //#$localparams
    //$#//
) (
    //#$ports
    input                                  pi_clk,
    input                                  pi_reset_n,
    input                                  pi_zeroize,
    input                                  pi_makehint_enable,
    input [(4*REG_SIZE)-1:0]               pi_r,
    input [3:0]                            pi_z,
    input [MLDSA_MEM_ADDR_WIDTH-1:0]       pi_mem_base_addr,
    input [MLDSA_MEM_ADDR_WIDTH-1:0]       pi_dest_base_addr,
    input logic                            po_invalid_h,
    input mem_if_t                         po_mem_rd_req,
    input mem_if_t                         po_z_rd_req,
    input logic                            po_makehint_done,
    input logic                            po_reg_wren,
    input logic [3:0][7:0]                 po_reg_wrdata,
    input logic [MLDSA_MEM_ADDR_WIDTH-1:0] po_reg_wr_addr,

    input logic [3:0]                                           fifo_valid_i,
    input logic [3:0][7:0]                                      fifo_data_i,

    input logic                                                 fifo_valid_o,
    input logic [3:0][BUFFER_DATA_W-1:0]                        fifo_data_o,
    input logic                                                 pi_flush_buffer
    //$#//
);

logic         fv_scoreboard_push;
logic         fv_soft_reset;
logic [63:0]  fv_scoreboard_data_in_reg;
logic [ 3:0]  fv_valid_counter_nxt;
logic [ 3:0]  fv_valid_counter;
logic [ 3:0]  fv_valid_counter_1;
logic [ 3:0]  valid_cnt;
logic [63:0]  data_in;
logic         sampled_in_loc;

lubis_scoreboard_unroll_ext_m #(
.IN_TYPE        (logic[31:0]),
.DEPTH          (1),
.EXP_TYPE       (logic[31:0]),
.OUT_TYPE       (logic[31:0]),
.BYPASS         (1          ),
.ENABLE_INVARIANCE(0),
.ENABLE_CMD_UNROLL(0)
)fv_makehint_fifo_scoreboard(
.clk            (pi_clk),
.rst            (~pi_reset_n || pi_zeroize || pi_flush_buffer),
.soft_rst       ('0),
.full           ('0),
.empty          ('0),
.data_in        (data_in[31:0]),
.data_out       (fifo_data_o),
.expected_data  (data_in[31:0]),
.incr_val       (1),
.push           (fv_scoreboard_push ),
.pop            (fifo_valid_o),
.num_elements   (),
.must_read      (),
.sampled_out    (),
.sym_data       (),
.sampled_in     (sampled_in_loc)
);


lubis_incr_decr_counter_m #(
    .COUNTER_WIDTH      (4),
    .NUM_INC_SRCS       (1 ),
    .NUM_DEC_SRCS       (1 ),
    .MAX_VALUE          (4 ),
    .MIN_VALUE          (    ),
    .INCR_VAL_WIDTH (4),
    .DECR_VAL_WIDTH (4)/*
    .ASSERT_CLAMP_MAX   (0            ),
    .ASSERT_CLAMP_MIN   (0            ),
    .ASSERT_NO_UNDERFLOW(1            ),
    .ASSERT_NO_OVERFLOW (1            )*/
) lubis_incr_decr_counter_verif
(
    .clk     (pi_clk                            ),
    .rst     (~pi_reset_n || pi_zeroize         ),
    .soft_rst(pi_flush_buffer                   ),
    .incr_en ((|fifo_valid_i)                     ),
    .decr_en (fv_valid_counter >= 4               ),
    .incr_val($countones(fifo_valid_i)            ),
    .decr_val(4                                   ),
    .count   (fv_valid_counter                    ),
    .count_next(fv_valid_counter_nxt              )
);

always_comb begin
  data_in = fv_scoreboard_data_in_reg;
  fv_scoreboard_push = (fv_valid_counter_nxt >= 4) ? 1'b1 : 1'b0;
  
  valid_cnt = 0;
  for(int i = 0; i < 4; i++) begin
    if(fifo_valid_i[i]) begin
      data_in[((fv_valid_counter_1 + valid_cnt)*8 + 7)-:8] = fifo_data_i[i];
      valid_cnt += 1;
    end
  end
end


always_ff@ (posedge pi_clk, negedge pi_reset_n) begin
  if(~pi_reset_n || pi_zeroize || pi_flush_buffer) begin
    fv_scoreboard_data_in_reg <= '0;
    fv_valid_counter_1 <= '0;
  end
  else begin
    if (fv_scoreboard_push)
      fv_scoreboard_data_in_reg <= data_in >> 32;
    else
      fv_scoreboard_data_in_reg <= data_in;

    if (fv_valid_counter_nxt >= 4)
      fv_valid_counter_1 <= fv_valid_counter_nxt - 4;
    else
      fv_valid_counter_1 <= fv_valid_counter_nxt;
  end
end

endmodule