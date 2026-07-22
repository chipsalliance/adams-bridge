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


module fv_skdecode_top_scoreboard 
    import mldsa_params_pkg::*;
    import skdecode_defines_pkg::*;
#(
    // Parameters
    parameter MLDSA_ETA = 2,
    parameter MLDSA_D = 13,
    parameter ETA_SIZE = 3,
    parameter REG_SIZE = 24,
    parameter AHB_DATA_WIDTH = 32
)(
    ////////////////////////////
    // Input / Output signals //
    ////////////////////////////
    input logic pi_clk,
    input logic pi_reset_n,
    input logic pi_zeroize,

    input wire pi_skdecode_enable,
    input wire [MLDSA_MEM_ADDR_WIDTH-1:0] pi_keymem_src_base_addr,
    input wire [MLDSA_MEM_ADDR_WIDTH-1:0] pi_dest_base_addr,
    input wire [AHB_DATA_WIDTH-1:0] pi_keymem_a_rd_data,
    input wire [AHB_DATA_WIDTH-1:0] pi_keymem_b_rd_data,

    input mem_if_t po_keymem_a_rd_req,
    input mem_if_t po_keymem_b_rd_req,
    input mem_if_t po_mem_a_wr_req,
    input mem_if_t po_mem_b_wr_req,
    input logic [3:0][REG_SIZE-1:0] po_mem_a_wr_data,
    input logic [3:0][REG_SIZE-1:0] po_mem_b_wr_data,
    input logic po_skdecode_error,
    input logic po_skdecode_done,
    input logic po_s1_done,
    input logic po_s2_done,
    input logic po_t0_done,

    //////////////////////////////
    // Internal Buffer signals  //
    //////////////////////////////
    input [3:0] s1s2_fifo_valid_i,
    input [3:0][7:0] s1s2_fifo_data_i,
    input logic s1s2_fifo_valid_o,
    input logic s1s2_buffer_full_o,
    input [2:0][7:0] s1s2_fifo_data_o,

    input [15:0] t0_fifo_valid_i,
    input [15:0][3:0] t0_fifo_data_i,
    input logic t0_fifo_valid_o,
    input logic t0_buffer_full_o,
    input [12:0][3:0] t0_fifo_data_o


);

//////////////////////////////////// s1s2_buffer ////////////////////////////////////
logic         fv_s1s2_scoreboard_push;
logic         fv_s1s2_soft_reset;
logic [55:0]  fv_s1s2_scoreboard_data_in_reg;
logic [ 3:0]  fv_s1s2_valid_counter_nxt;
logic [ 3:0]  fv_s1s2_valid_counter;
logic [ 3:0]  fv_s1s2_valid_counter_1;
logic [ 3:0]  s1s2_valid_cnt;
logic [55:0]  s1s2_data_in;
logic         s1s2_sampled_in_loc;


lubis_scoreboard_unroll_ext_m #(
.IN_TYPE        (logic[23:0]),
.DEPTH          (2),
.EXP_TYPE       (logic[23:0]),
.OUT_TYPE       (logic[23:0]),
.ENABLE_INVARIANCE(0),
.ENABLE_CMD_UNROLL(0)
)fv_skdecode_top_fifo_s1s2_scoreboard(
.clk            (pi_clk),
.rst            (~pi_reset_n || pi_zeroize),
.soft_rst       ('0),
.full           ('0),
.empty          ('0),
.data_in        (s1s2_data_in[23:0]),
.data_out       (s1s2_fifo_data_o),
.expected_data  (s1s2_data_in[23:0]),
.incr_val       (1),
.push           (fv_s1s2_scoreboard_push ),
.pop            (s1s2_fifo_valid_o),
.num_elements   (),
.must_read      (),
.sampled_out    (),
.sym_data       (),
.sampled_in     (s1s2_sampled_in_loc)
);


lubis_incr_decr_counter_m #(
    .COUNTER_WIDTH      (4),
    .NUM_INC_SRCS       (1 ),
    .NUM_DEC_SRCS       (1 ),
    .MAX_VALUE          (6 ),
    .MIN_VALUE          (    ),
    .INCR_VAL_WIDTH (4),
    .DECR_VAL_WIDTH (4)/*
    .ASSERT_CLAMP_MAX   (0            ),
    .ASSERT_CLAMP_MIN   (0            ),
    .ASSERT_NO_UNDERFLOW(1            ),
    .ASSERT_NO_OVERFLOW (1            )*/
) lubis_incr_decr_counter_s1s2_verif
(
    .clk     (pi_clk                            ),
    .rst     (~pi_reset_n || pi_zeroize         ),
    .soft_rst(1'b0                   ),
    .incr_en ((|s1s2_fifo_valid_i)   && !s1s2_buffer_full_o),  
    .decr_en (fv_s1s2_valid_counter >= 3               ),
    .incr_val($countones(s1s2_fifo_valid_i)            ),
    .decr_val(3                                   ),
    .count   (fv_s1s2_valid_counter                    ),
    .count_next(fv_s1s2_valid_counter_nxt              )
);

always_comb begin
  s1s2_data_in = fv_s1s2_scoreboard_data_in_reg;
  fv_s1s2_scoreboard_push = (fv_s1s2_valid_counter_nxt >= 3) ? 1'b1 : 1'b0;
  
  s1s2_valid_cnt = 0;
  for(int i = 0; i < 4; i++) begin
    if(s1s2_fifo_valid_i[i]) begin
      s1s2_data_in[((fv_s1s2_valid_counter_1 + s1s2_valid_cnt)*8 + 7)-:8] = s1s2_fifo_data_i[i];
      s1s2_valid_cnt += 1;
    end
  end
end


always_ff @(posedge pi_clk or negedge pi_reset_n) begin
  if (~pi_reset_n || pi_zeroize) begin
    fv_s1s2_scoreboard_data_in_reg <= '0;
    fv_s1s2_valid_counter_1 <= '0;
  end
  else begin
    if (fv_s1s2_scoreboard_push) begin
      fv_s1s2_scoreboard_data_in_reg <= s1s2_data_in >> 24;
    end
    else begin
      fv_s1s2_scoreboard_data_in_reg <= s1s2_data_in;
    end

    if (fv_s1s2_valid_counter_nxt >= 3)
      fv_s1s2_valid_counter_1 <= fv_s1s2_valid_counter_nxt - 3;
    else
      fv_s1s2_valid_counter_1 <= fv_s1s2_valid_counter_nxt;


    
  end
end


//////////////////////////////////// t0_buffer ////////////////////////////////////
logic         fv_t0_scoreboard_push;
logic         fv_t0_soft_reset;
logic [115:0]  fv_t0_scoreboard_data_in_reg;
logic [ 5:0]  fv_t0_valid_counter_nxt;
logic [ 5:0]  fv_t0_valid_counter;
logic [ 5:0]  fv_t0_valid_counter_1;
logic [ 5:0]  t0_valid_cnt;
logic [115:0]  t0_data_in;
logic         t0_sampled_in_loc;


lubis_scoreboard_unroll_ext_m #(
.IN_TYPE        (logic[51:0]),
.DEPTH          (3),
.EXP_TYPE       (logic[51:0]),
.OUT_TYPE       (logic[51:0]),
.ENABLE_INVARIANCE(0),
.ENABLE_CMD_UNROLL(0)
)fv_skdecode_top_fifo_t0_scoreboard(
.clk            (pi_clk),
.rst            (~pi_reset_n || pi_zeroize),
.soft_rst       ('0),
.full           ('0),
.empty          ('0),
.data_in        (t0_data_in[51:0]),
.data_out       (t0_fifo_data_o),
.expected_data  (t0_data_in[51:0]),
.incr_val       (1),
.push           (fv_t0_scoreboard_push ),
.pop            (t0_fifo_valid_o),
.num_elements   (),
.must_read      (),
.sampled_out    (),
.sym_data       (),
.sampled_in     (t0_sampled_in_loc)
);


lubis_incr_decr_counter_m #(
    .COUNTER_WIDTH      (6),
    .NUM_INC_SRCS       (1 ),
    .NUM_DEC_SRCS       (1 ),
    .MAX_VALUE          (28 ),
    .MIN_VALUE          (    ),
    .INCR_VAL_WIDTH (6),
    .DECR_VAL_WIDTH (6)/*
    .ASSERT_CLAMP_MAX   (0            ),
    .ASSERT_CLAMP_MIN   (0            ),
    .ASSERT_NO_UNDERFLOW(1            ),
    .ASSERT_NO_OVERFLOW (1            )*/
) lubis_incr_decr_counter_t0_verif
(
    .clk     (pi_clk                            ),
    .rst     (~pi_reset_n || pi_zeroize         ),
    .soft_rst(1'b0                   ),
    .incr_en ((|t0_fifo_valid_i)   && !t0_buffer_full_o),  
    .decr_en (fv_t0_valid_counter >= 13               ),
    .incr_val($countones(t0_fifo_valid_i)            ),
    .decr_val(13                                   ),
    .count   (fv_t0_valid_counter                    ),
    .count_next(fv_t0_valid_counter_nxt              )
);

always_comb begin
  t0_data_in = fv_t0_scoreboard_data_in_reg;
  fv_t0_scoreboard_push = (fv_t0_valid_counter_nxt >= 13) ? 1'b1 : 1'b0;
  
  t0_valid_cnt = 0;
  for(int i = 0; i < 16; i++) begin
    if(t0_fifo_valid_i[i]) begin
      t0_data_in[((fv_t0_valid_counter_1 + t0_valid_cnt)*4 + 3)-:4] = t0_fifo_data_i[i];
      t0_valid_cnt += 1;
    end
  end
end


always_ff @(posedge pi_clk or negedge pi_reset_n) begin
  if (~pi_reset_n || pi_zeroize) begin
    fv_t0_scoreboard_data_in_reg <= '0;
    fv_t0_valid_counter_1 <= '0;
  end
  else begin
    if (fv_t0_scoreboard_push) begin
      fv_t0_scoreboard_data_in_reg <= t0_data_in >> 52;
    end
    else begin
      fv_t0_scoreboard_data_in_reg <= t0_data_in;
    end

    if (fv_t0_valid_counter_nxt >= 13)
      fv_t0_valid_counter_1 <= fv_t0_valid_counter_nxt - 13;
    else
      fv_t0_valid_counter_1 <= fv_t0_valid_counter_nxt;


    
  end
end


endmodule