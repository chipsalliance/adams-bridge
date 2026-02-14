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

module fv_ntt_ctrl_gs_mode_additional_properties
  import ntt_defines_pkg::*;
#(
    parameter MEM_ADDR_WIDTH = 15
)
(
  input logic rst_n,
  input logic clk,
  input logic zeroize,
  input logic butterfly_ready,
  input logic buf0_valid,
  input logic shuffle_en,
  input logic buf_wren,
  input logic buf_rden,
  input logic [6:0] twiddle_addr,
  input logic [MEM_ADDR_WIDTH-1:0] mem_rd_addr,
  input logic [MEM_ADDR_WIDTH-1:0] mem_wr_addr,
  input logic mem_rd_en,
  input logic mem_wr_en,
  input logic buf_rd_rst_count,
  input logic buf_wr_rst_count,
  input logic busy,
  input ntt_read_state_t read_fsm_state_ps,
  input ntt_write_state_t write_fsm_state_ps,
  input logic buf_wren_intt_reg,
  input logic unsigned [1:0] buf_count,
  input logic rst_rounds,
  input logic mem_rd_en_reg,
  input logic [MEM_ADDR_WIDTH-1:0] mem_rd_base_addr,
  input logic [6:0] twiddle_addr_reg,
  input logic [6:0] twiddle_addr_reg_d3,
  input logic [MASKED_INTT_WRBUF_LATENCY-3:0][3:0] chunk_count_reg,
  input logic [MASKED_INTT_WRBUF_LATENCY-1:0][1:0] buf_wrptr_reg,
  input logic [2:0] rounds_count
);


default clocking default_clk @(posedge clk); endclocking


logic [7:0][6:0] twiddle_offsets;
assign twiddle_offsets = '{
  0: 7'd0,
  1: 7'd64,
  2: 7'd80,
  3: 7'd84,
  4: 7'd0,
  5: 7'd0,
  6: 7'd0,
  7: 7'd0
};


logic [7:0][6:0] twiddle_rand_offsets;
assign twiddle_rand_offsets = '{
  0: 4 * chunk_count_reg[UNMASKED_BF_LATENCY] + buf_wrptr_reg[INTT_WRBUF_LATENCY - 1],
  1: (chunk_count_reg[UNMASKED_BF_LATENCY] & 4'h3) * 4 + buf_wrptr_reg[INTT_WRBUF_LATENCY - 1],
  2: buf_wrptr_reg[INTT_WRBUF_LATENCY - 1],
  3: 7'd0,
  4: 7'd0,
  5: 7'd0,
  6: 7'd0,
  7: 7'd0
};


logic [6:0] twiddle_addr_int;
assign twiddle_addr_int = shuffle_en
  ? (twiddle_rand_offsets[rounds_count] + twiddle_offsets[rounds_count])
  : (twiddle_addr_reg + twiddle_offsets[rounds_count]);


property assert_buf_wren_p;
  buf_wren == (shuffle_en
    ? buf_wren_intt_reg
    : ((write_fsm_state_ps == WR_BUF && butterfly_ready) || (write_fsm_state_ps == WR_MEM) || (write_fsm_state_ps == WR_WAIT && !shuffle_en && buf_count <= 3)));
endproperty
assert_buf_wren_a: assert property (disable iff (!rst_n || zeroize) assert_buf_wren_p);


property assert_buf_wren_intt_reg_p;
  ##1 buf_wren_intt_reg == $past((write_fsm_state_ps == WR_BUF && butterfly_ready) || (write_fsm_state_ps == WR_MEM) || (write_fsm_state_ps == WR_WAIT && !shuffle_en && buf_count <= 3));
endproperty
assert_buf_wren_intt_reg_a: assert property (disable iff (!rst_n || zeroize) assert_buf_wren_intt_reg_p);


property assert_buf_rden_p;
  buf_rden == ((write_fsm_state_ps == WR_BUF && buf0_valid) || (write_fsm_state_ps == WR_MEM) || (write_fsm_state_ps == WR_WAIT));
endproperty
assert_buf_rden_a: assert property (disable iff (!rst_n || zeroize) assert_buf_rden_p);


property assert_twiddle_addr_p;
  twiddle_addr == (shuffle_en
    ? twiddle_addr_reg_d3
    : twiddle_addr_int);
endproperty
assert_twiddle_addr_a: assert property (disable iff (!rst_n || zeroize) assert_twiddle_addr_p);


property assert_mem_rd_en_p;
  mem_rd_en == (shuffle_en
    ? mem_rd_en_reg
    : (read_fsm_state_ps == RD_EXEC && mem_rd_addr <= mem_rd_base_addr + 63));
endproperty
assert_mem_rd_en_a: assert property (disable iff (!rst_n || zeroize) assert_mem_rd_en_p);


property assert_mem_wr_en_p;
  mem_wr_en == ((write_fsm_state_ps == WR_BUF && buf0_valid) || (write_fsm_state_ps == WR_MEM) || (write_fsm_state_ps == WR_WAIT));
endproperty
assert_mem_wr_en_a: assert property (disable iff (!rst_n || zeroize) assert_mem_wr_en_p);


property assert_buf_wr_rst_count_p;
  buf_wr_rst_count == ((read_fsm_state_ps == RD_IDLE) || (read_fsm_state_ps == EXEC_WAIT) || (write_fsm_state_ps == WR_STAGE));
endproperty
assert_buf_wr_rst_count_a: assert property (disable iff (!rst_n || zeroize) assert_buf_wr_rst_count_p);


property assert_buf_rd_rst_count_p;
  buf_rd_rst_count == ((read_fsm_state_ps == RD_IDLE) || (write_fsm_state_ps == WR_STAGE));
endproperty
assert_buf_rd_rst_count_a: assert property (disable iff (!rst_n || zeroize) assert_buf_rd_rst_count_p);


property assert_busy_p;
  busy == ((read_fsm_state_ps != RD_IDLE) && (write_fsm_state_ps != WR_IDLE));
endproperty
assert_busy_a: assert property (disable iff (!rst_n || zeroize) assert_busy_p);


property assert_rst_rounds_p;
  rst_rounds == ((read_fsm_state_ps == RD_IDLE) && (write_fsm_state_ps == WR_IDLE));
endproperty
assert_rst_rounds_a: assert property (disable iff (!rst_n || zeroize) assert_rst_rounds_p);


// Whenever mem_rd_en && mem_wr_en -> mem_rd_addr != mem_wr_addr
property assert_different_rd_wr_addrs_p;
  mem_rd_en && mem_wr_en
|->
  mem_rd_addr != mem_wr_addr;
endproperty
assert_different_rd_wr_addrs_a: assert property (disable iff (!rst_n || zeroize) assert_different_rd_wr_addrs_p);


endmodule


bind ntt_ctrl fv_ntt_ctrl_gs_mode_additional_properties gs_mlkem_additional_inst(
  .rst_n(reset_n),
  .clk(clk),
  .zeroize(zeroize),
  .butterfly_ready(butterfly_ready),
  .buf0_valid(buf0_valid),
  .shuffle_en(shuffle_en),
  .buf_wren(buf_wren),
  .buf_rden(buf_rden),
  .twiddle_addr(twiddle_addr),
  .mem_rd_addr(mem_rd_addr),
  .mem_wr_addr(mem_wr_addr),
  .mem_rd_en(mem_rd_en),
  .mem_wr_en(mem_wr_en),
  .buf_rd_rst_count(buf_rd_rst_count),
  .buf_wr_rst_count(buf_wr_rst_count),
  .busy(busy),
  .read_fsm_state_ps(read_fsm_state_ps),
  .write_fsm_state_ps(write_fsm_state_ps),
  .buf_wren_intt_reg(buf_wren_intt_reg),
  .buf_count(buf_count),
  .rst_rounds(rst_rounds),
  .mem_rd_en_reg(mem_rd_en_reg),
  .mem_rd_base_addr(mem_rd_base_addr),
  .twiddle_addr_reg(twiddle_addr_reg),
  .twiddle_addr_reg_d3(twiddle_addr_reg_d3),
  .chunk_count_reg(chunk_count_reg),
  .buf_wrptr_reg(buf_wrptr_reg),
  .rounds_count(rounds_count)
);
