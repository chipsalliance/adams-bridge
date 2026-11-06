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

// +---------------------------------------------------+
// | Copyright (c) LUBIS EDA GmbH, all rights reserved |
// | Contact: contact@lubis-eda.com                    |
// +---------------------------------------------------+


import fv_ntt_ctrl_ct_mlkem_pkg::*;
import abr_params_pkg::*;
import ntt_defines_pkg::*;
import fv_ntt_ctrl_ct_mlkem_pkg::*;
import fv_ntt_ctrl_ct_mlkem_functions::*;


module fv_ntt_ctrl_ct_mlkem_m(
  input logic rst_n,
  input logic clk,

  // Ports
  input st_Base_Address base_address_port,

  input st_Request_and_Address mem_read_req_port,

  input st_Request_and_Address mem_write_req_port,

  input logic unsigned [1:0] buf_wrptr_out,

  input logic unsigned [1:0] buf_rdptr_f_out,

  input logic bf_enable_out,

  input logic buf_rden_out,

  input logic pw_rden_out,

  input logic pw_rden_dest_mem,

  input logic pw_wren_out,

  input logic unsigned [2:0] rounds_count_out,

  input logic ntt_done_out,

  input logic done_out,

  input logic unsigned [2:0] opcode_port,

  input logic unsigned [6:0] twiddle_addr_reg_out,

  input logic shuffle_en_in,

  input logic unsigned [3:0] chunk_count_in,

  input logic unsigned [3:0] chunk_rand_offset_in,

  input logic unsigned [2:0] rounds_count_in,

  input logic buf0_valid_in,

  input logic ntt_enable_in,

  input logic mlkem_in,

  input logic unsigned [5:0] random_in,

  input logic butterfly_ready_in,

  input logic unsigned [3:0] chunk_count_reg_port,

  input logic unsigned [1:0] buf_rdptr_reg_port,

  input logic latch_index_rand_offset_port,

  // Registers
  input logic unsigned [1:0] buf_count,
  input logic unsigned [13:0] buf_rdptr_reg_1,
  input logic unsigned [3:0] chunk_count,
  input logic unsigned [27:0] chunk_count_reg_1,
  input logic unsigned [3:0] chunk_count_write,
  input logic unsigned [3:0] chunk_rand_offset_write,
  input logic unsigned [1:0] index_rand_offset,
  input logic unsigned [14:0] mem_rd_next_addr,
  input logic unsigned [6:0] rd_valid_count,
  input st_Request_and_Address read_req,
  input e_CtReadStatesType read_state,
  input logic unsigned [2:0] rounds_count_write,
  input logic shuffle_en,
  input logic unsigned [6:0] twiddle_addr_reg,
  input logic unsigned [6:0] wr_valid_count,
  input st_Request_and_Address write_req,
  input e_CtWriteStatesType write_state,

  // States
  input logic read_idle,
  input logic read_stage,
  input logic read_buf,
  input logic read_exec,
  input logic read_exec_wait,
  input logic write_idle,
  input logic write_stage,
  input logic write_mem
);


default clocking default_clk @(posedge clk); endclocking


st_Request_and_Address mem_read_req_port_0_i;
assign mem_read_req_port_0_i = '{
  request: 0,
  address: 14'd0
};

st_Request_and_Address mem_read_req_port_1_i;
assign mem_read_req_port_1_i = '{
  request: 0,
  address: (shuffle_en_in ? (((rounds_count_in == 3'd0) ? base_address_port.source : ((rounds_count_in[0] == 0) ? base_address_port.destination : base_address_port.interim)) + ({ 10'd0, chunk_rand_offset_in} )) : ((rounds_count_in == 3'd0) ? base_address_port.source : ((rounds_count_in[0] == 0) ? base_address_port.destination : base_address_port.interim)))
};

logic unsigned [6:0] twiddle_rand_offset_0_i;
assign twiddle_rand_offset_0_i = twiddle_rand_offset(rounds_count_in, (shuffle_en_in ? (index_rand_offset + buf_count) : buf_count), chunk_count_in);

logic unsigned [6:0] twiddle_end_addr_0_i;
assign twiddle_end_addr_0_i = twiddle_end_addr(rounds_count_in);

st_Request_and_Address mem_read_req_port_2_i;
assign mem_read_req_port_2_i = '{
  request: 1,
  address: (shuffle_en_in ? ((read_req.address == (14'd63 + ((rounds_count_in == 3'd0) ? base_address_port.source : ((rounds_count_in[0] == 0) ? base_address_port.destination : base_address_port.interim)))) ? ((rounds_count_in == 3'd0) ? base_address_port.source : ((rounds_count_in[0] == 0) ? base_address_port.destination : base_address_port.interim)) : (((64'd16 + ({ 50'd0, read_req.address} )) > (64'd63 + ({ 50'd0, ((rounds_count_in == 3'd0) ? base_address_port.source : ((rounds_count_in[0] == 0) ? base_address_port.destination : base_address_port.interim))} ))) ? { (({ 49'd0, 15'((15'd16 + ({ 1'd0, read_req.address} )))} ) - 64'd63) }[13:0] : (14'd16 + read_req.address))) : (((64'd16 + ({ 50'd0, read_req.address} )) > (64'd63 + ({ 50'd0, ((rounds_count_in == 3'd0) ? base_address_port.source : ((rounds_count_in[0] == 0) ? base_address_port.destination : base_address_port.interim))} ))) ? { (({ 49'd0, 15'((15'd16 + ({ 1'd0, read_req.address} )))} ) - 64'd63) }[13:0] : (14'd16 + read_req.address)))
};

st_Request_and_Address mem_read_req_port_3_i;
assign mem_read_req_port_3_i = '{
  request: (shuffle_en_in ? ((read_req.address <= (14'd63 + ((rounds_count_in == 3'd0) ? base_address_port.source : ((rounds_count_in[0] == 0) ? base_address_port.destination : base_address_port.interim)))) && !((buf_count == 2'd3) && (rd_valid_count == 7'd60))) : (read_req.address <= (14'd63 + ((rounds_count_in == 3'd0) ? base_address_port.source : ((rounds_count_in[0] == 0) ? base_address_port.destination : base_address_port.interim))))),
  address: (shuffle_en_in ? ((read_req.address == (14'd63 + ((rounds_count_in == 3'd0) ? base_address_port.source : ((rounds_count_in[0] == 0) ? base_address_port.destination : base_address_port.interim)))) ? ((rounds_count_in == 3'd0) ? base_address_port.source : ((rounds_count_in[0] == 0) ? base_address_port.destination : base_address_port.interim)) : ((({ 49'd0, mem_rd_next_addr} ) > (64'd63 + ({ 50'd0, ((rounds_count_in == 3'd0) ? base_address_port.source : ((rounds_count_in[0] == 0) ? base_address_port.destination : base_address_port.interim))} ))) ? { (({ 49'd0, 15'((15'd16 + ({ 1'd0, read_req.address} )))} ) - 64'd63) }[13:0] : (14'd16 + read_req.address))) : ((({ 49'd0, mem_rd_next_addr} ) > (64'd63 + ({ 50'd0, ((rounds_count_in == 3'd0) ? base_address_port.source : ((rounds_count_in[0] == 0) ? base_address_port.destination : base_address_port.interim))} ))) ? { (({ 49'd0, 15'((15'd16 + ({ 1'd0, read_req.address} )))} ) - 64'd63) }[13:0] : (14'd16 + read_req.address)))
};

st_Request_and_Address mem_read_req_port_4_i;
assign mem_read_req_port_4_i = '{
  request: 0,
  address: (shuffle_en_in ? ((read_req.address == (14'd63 + ((rounds_count_in == 3'd0) ? base_address_port.source : ((rounds_count_in[0] == 0) ? base_address_port.destination : base_address_port.interim)))) ? ((rounds_count_in == 3'd0) ? base_address_port.source : ((rounds_count_in[0] == 0) ? base_address_port.destination : base_address_port.interim)) : ((({ 49'd0, mem_rd_next_addr} ) > (64'd63 + ({ 50'd0, ((rounds_count_in == 3'd0) ? base_address_port.source : ((rounds_count_in[0] == 0) ? base_address_port.destination : base_address_port.interim))} ))) ? { (({ 49'd0, 15'((15'd16 + ({ 1'd0, read_req.address} )))} ) - 64'd63) }[13:0] : (14'd16 + read_req.address))) : ((({ 49'd0, mem_rd_next_addr} ) > (64'd63 + ({ 50'd0, ((rounds_count_in == 3'd0) ? base_address_port.source : ((rounds_count_in[0] == 0) ? base_address_port.destination : base_address_port.interim))} ))) ? { (({ 49'd0, 15'((15'd16 + ({ 1'd0, read_req.address} )))} ) - 64'd63) }[13:0] : (14'd16 + read_req.address)))
};

st_Request_and_Address mem_read_req_port_5_i;
assign mem_read_req_port_5_i = '{
  request: 0,
  address: read_req.address
};

st_Request_and_Address mem_write_req_port_0_i;
assign mem_write_req_port_0_i = '{
  request: 0,
  address: (shuffle_en ? (base_address_port.interim + (14'd4 * ({ 10'd0, chunk_rand_offset_write} ))) : base_address_port.interim)
};

st_Request_and_Address mem_write_req_port_1_i;
assign mem_write_req_port_1_i = '{
  request: 0,
  address: (shuffle_en ? (((rounds_count_write[0] == 0) ? base_address_port.interim : base_address_port.destination) + (14'd4 * ({ 10'd0, chunk_rand_offset_write} ))) : ((rounds_count_write[0] == 0) ? base_address_port.interim : base_address_port.destination))
};

st_Request_and_Address mem_write_req_port_2_i;
assign mem_write_req_port_2_i = '{
  request: butterfly_ready_in,
  address: (butterfly_ready_in ? ((({ 49'd0, (shuffle_en ? (((15'd4 * ({ 11'd0, chunk_count_reg_port} )) + ({ 13'd0, buf_rdptr_reg_port} )) + ({ 1'd0, ((rounds_count_write[0] == 0) ? base_address_port.interim : base_address_port.destination)} )) : (15'd1 + ({ 1'd0, write_req.address} )))} ) > (64'd63 + ({ 50'd0, ((rounds_count_write[0] == 0) ? base_address_port.interim : base_address_port.destination)} ))) ? { (({ 49'd0, (shuffle_en ? (((15'd4 * ({ 11'd0, chunk_count_reg_port} )) + ({ 13'd0, buf_rdptr_reg_port} )) + ({ 1'd0, ((rounds_count_write[0] == 0) ? base_address_port.interim : base_address_port.destination)} )) : (15'd1 + ({ 1'd0, write_req.address} )))} ) - 64'd63) }[13:0] : (shuffle_en ? (((14'd4 * ({ 10'd0, chunk_count_reg_port} )) + ({ 12'd0, buf_rdptr_reg_port} )) + ((rounds_count_write[0] == 0) ? base_address_port.interim : base_address_port.destination)) : (14'd1 + write_req.address))) : write_req.address)
};


sequence reset_sequence;
  rst_n && $past(!rst_n);
endsequence


property read_reset_p;
  reset_sequence |->
  read_idle &&
  bf_enable_out == 0 &&
  buf_count == 2'd0 &&
  buf_rden_out == 0 &&
  buf_rdptr_f_out == 2'd0 &&
  buf_rdptr_reg_1 == 14'd0 &&
  chunk_count_reg_1 == 28'd0 &&
  index_rand_offset == 2'd0 &&
  mem_read_req_port == mem_read_req_port_0_i &&
  opcode_port == 3'd0 &&
  pw_rden_dest_mem == 0 &&
  pw_rden_out == 0 &&
  pw_wren_out == 0 &&
  rd_valid_count == 7'd0 &&
  twiddle_addr_reg_out == 7'd0;
endproperty
read_reset_a: assert property (read_reset_p);


property write_reset_p;
  reset_sequence |->
  write_idle &&
  chunk_count_write == 4'd0 &&
  chunk_rand_offset_write == 4'd0 &&
  done_out == 0 &&
  mem_write_req_port == mem_read_req_port_0_i &&
  rounds_count_out == 3'd0 &&
  wr_valid_count == 7'd0;
endproperty
write_reset_a: assert property (write_reset_p);


property read_read_buf_to_read_buf_p;
  read_buf &&
  !buf0_valid_in
|->
  ##1
  read_buf &&
  bf_enable_out == $past(buf0_valid_in, 1) &&
  buf_count == (($past(buf0_valid_in, 1) || ((({ 30'd0, $past(buf_count, 1)} ) > 0) && (({ 30'd0, $past(buf_count, 1)} ) < 3))) ? (2'sd1 + signed'($past(buf_count, 1))) : 2'd0) &&
  buf_rden_out == $past(buf0_valid_in, 1) &&
  buf_rdptr_f_out == ($past(shuffle_en_in, 1) ? ($past(index_rand_offset, 1) + $past(buf_count, 1)) : $past(buf_count, 1)) &&
  buf_rdptr_reg_1 == (((($past(butterfly_ready_in, 1) || ($past(buf0_valid_in, 1) && ($past(read_state, 1) == CtReadBuf))) || ($past(read_state, 1) == CtReadExec)) || ($past(read_state, 1) == CtReadExecwait)) ? ({ ($past(shuffle_en_in, 1) ? ($past(index_rand_offset, 1) + $past(buf_count, 1)) : $past(buf_count, 1)), { $past(buf_rdptr_reg_1, 1) }[13:2]} ) : 14'd0) &&
  chunk_count_reg_1 == (((($past(butterfly_ready_in, 1) || ($past(buf0_valid_in, 1) && ($past(read_state, 1) == CtReadBuf))) || ($past(read_state, 1) == CtReadExec)) || ($past(read_state, 1) == CtReadExecwait)) ? ({ $past(chunk_count_in, 1), { $past(chunk_count_reg_1, 1) }[27:4]} ) : $past(chunk_count_reg_1, 1)) &&
  index_rand_offset == ($past(latch_index_rand_offset_port, 1) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  mem_read_req_port == $past(mem_read_req_port_2_i, 1) &&
  opcode_port == 3'd0 &&
  pw_rden_dest_mem == 0 &&
  pw_rden_out == 0 &&
  pw_wren_out == 0 &&
  rd_valid_count == (((($past(read_state, 1) == CtReadIdle) || ($past(read_state, 1) == CtReadStage)) || ($past(buf0_valid_in, 1) && ($past(rd_valid_count, 1) >= 7'd64))) ? 7'd0 : ($past(buf0_valid_in, 1) ? (7'd4 + $past(rd_valid_count, 1)) : $past(rd_valid_count, 1))) &&
  twiddle_addr_reg_out == $past(twiddle_addr_reg, 1);
endproperty
read_read_buf_to_read_buf_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) read_read_buf_to_read_buf_p);


property read_read_buf_to_read_exec_p;
  read_buf &&
  buf0_valid_in
|->
  ##1
  read_exec &&
  bf_enable_out == $past(buf0_valid_in, 1) &&
  buf_count == (($past(buf0_valid_in, 1) || ((({ 30'd0, $past(buf_count, 1)} ) > 0) && (({ 30'd0, $past(buf_count, 1)} ) < 3))) ? (2'sd1 + signed'($past(buf_count, 1))) : 2'd0) &&
  buf_rden_out == $past(buf0_valid_in, 1) &&
  buf_rdptr_f_out == ($past(shuffle_en_in, 1) ? ($past(index_rand_offset, 1) + $past(buf_count, 1)) : $past(buf_count, 1)) &&
  buf_rdptr_reg_1 == (((($past(butterfly_ready_in, 1) || ($past(buf0_valid_in, 1) && ($past(read_state, 1) == CtReadBuf))) || ($past(read_state, 1) == CtReadExec)) || ($past(read_state, 1) == CtReadExecwait)) ? ({ ($past(shuffle_en_in, 1) ? ($past(index_rand_offset, 1) + $past(buf_count, 1)) : $past(buf_count, 1)), { $past(buf_rdptr_reg_1, 1) }[13:2]} ) : 14'd0) &&
  chunk_count_reg_1 == (((($past(butterfly_ready_in, 1) || ($past(buf0_valid_in, 1) && ($past(read_state, 1) == CtReadBuf))) || ($past(read_state, 1) == CtReadExec)) || ($past(read_state, 1) == CtReadExecwait)) ? ({ $past(chunk_count_in, 1), { $past(chunk_count_reg_1, 1) }[27:4]} ) : $past(chunk_count_reg_1, 1)) &&
  index_rand_offset == ($past(latch_index_rand_offset_port, 1) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  mem_read_req_port == $past(mem_read_req_port_2_i, 1) &&
  opcode_port == 3'd0 &&
  pw_rden_dest_mem == 0 &&
  pw_rden_out == 0 &&
  pw_wren_out == 0 &&
  rd_valid_count == (((($past(read_state, 1) == CtReadIdle) || ($past(read_state, 1) == CtReadStage)) || ($past(buf0_valid_in, 1) && ($past(rd_valid_count, 1) >= 7'd64))) ? 7'd0 : ($past(buf0_valid_in, 1) ? (7'd4 + $past(rd_valid_count, 1)) : $past(rd_valid_count, 1))) &&
  twiddle_addr_reg_out == ($past(shuffle_en_in, 1) ? $past(twiddle_rand_offset_0_i, 1) : (($past(twiddle_addr_reg, 1) == $past(twiddle_end_addr_0_i, 1)) ? 7'd0 : (7'd1 + $past(twiddle_addr_reg, 1))));
endproperty
read_read_buf_to_read_exec_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) read_read_buf_to_read_exec_p);


property read_read_exec_to_read_buf_p;
  read_exec &&
  (rd_valid_count < 7'd64) &&
  (buf_count == 2'd0) &&
  !buf0_valid_in
|->
  ##1
  read_buf &&
  bf_enable_out == 1 &&
  buf_count == (($past(buf0_valid_in, 1) || ((({ 30'd0, $past(buf_count, 1)} ) > 0) && (({ 30'd0, $past(buf_count, 1)} ) < 3))) ? (2'sd1 + signed'($past(buf_count, 1))) : 2'd0) &&
  buf_rden_out == 1 &&
  buf_rdptr_f_out == ($past(shuffle_en_in, 1) ? ($past(index_rand_offset, 1) + $past(buf_count, 1)) : $past(buf_count, 1)) &&
  buf_rdptr_reg_1 == (((($past(butterfly_ready_in, 1) || ($past(buf0_valid_in, 1) && ($past(read_state, 1) == CtReadBuf))) || ($past(read_state, 1) == CtReadExec)) || ($past(read_state, 1) == CtReadExecwait)) ? ({ ($past(shuffle_en_in, 1) ? ($past(index_rand_offset, 1) + $past(buf_count, 1)) : $past(buf_count, 1)), { $past(buf_rdptr_reg_1, 1) }[13:2]} ) : 14'd0) &&
  chunk_count_reg_1 == (((($past(butterfly_ready_in, 1) || ($past(buf0_valid_in, 1) && ($past(read_state, 1) == CtReadBuf))) || ($past(read_state, 1) == CtReadExec)) || ($past(read_state, 1) == CtReadExecwait)) ? ({ $past(chunk_count_in, 1), { $past(chunk_count_reg_1, 1) }[27:4]} ) : $past(chunk_count_reg_1, 1)) &&
  index_rand_offset == ($past(latch_index_rand_offset_port, 1) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  mem_read_req_port == $past(mem_read_req_port_3_i, 1) &&
  opcode_port == 3'd0 &&
  pw_rden_dest_mem == 0 &&
  pw_rden_out == 0 &&
  pw_wren_out == 0 &&
  rd_valid_count == (((($past(read_state, 1) == CtReadIdle) || ($past(read_state, 1) == CtReadStage)) || ($past(buf0_valid_in, 1) && ($past(rd_valid_count, 1) >= 7'd64))) ? 7'd0 : ($past(buf0_valid_in, 1) ? (7'd4 + $past(rd_valid_count, 1)) : $past(rd_valid_count, 1))) &&
  twiddle_addr_reg_out == ($past(shuffle_en_in, 1) ? $past(twiddle_rand_offset_0_i, 1) : (($past(twiddle_addr_reg, 1) == $past(twiddle_end_addr_0_i, 1)) ? 7'd0 : (7'd1 + $past(twiddle_addr_reg, 1))));
endproperty
read_read_exec_to_read_buf_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) read_read_exec_to_read_buf_p);


property read_read_exec_to_read_exec_p;
  read_exec &&
  (!((rd_valid_count < 7'd64) && (buf_count == 2'd0)) || buf0_valid_in) &&
  !((buf_count == 2'd3) && (rd_valid_count == 7'd60))
|->
  ##1
  read_exec &&
  bf_enable_out == 1 &&
  buf_count == (($past(buf0_valid_in, 1) || ((({ 30'd0, $past(buf_count, 1)} ) > 0) && (({ 30'd0, $past(buf_count, 1)} ) < 3))) ? (2'sd1 + signed'($past(buf_count, 1))) : 2'd0) &&
  buf_rden_out == 1 &&
  buf_rdptr_f_out == ($past(shuffle_en_in, 1) ? ($past(index_rand_offset, 1) + $past(buf_count, 1)) : $past(buf_count, 1)) &&
  buf_rdptr_reg_1 == (((($past(butterfly_ready_in, 1) || ($past(buf0_valid_in, 1) && ($past(read_state, 1) == CtReadBuf))) || ($past(read_state, 1) == CtReadExec)) || ($past(read_state, 1) == CtReadExecwait)) ? ({ ($past(shuffle_en_in, 1) ? ($past(index_rand_offset, 1) + $past(buf_count, 1)) : $past(buf_count, 1)), { $past(buf_rdptr_reg_1, 1) }[13:2]} ) : 14'd0) &&
  chunk_count_reg_1 == (((($past(butterfly_ready_in, 1) || ($past(buf0_valid_in, 1) && ($past(read_state, 1) == CtReadBuf))) || ($past(read_state, 1) == CtReadExec)) || ($past(read_state, 1) == CtReadExecwait)) ? ({ $past(chunk_count_in, 1), { $past(chunk_count_reg_1, 1) }[27:4]} ) : $past(chunk_count_reg_1, 1)) &&
  index_rand_offset == ($past(latch_index_rand_offset_port, 1) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  mem_read_req_port == $past(mem_read_req_port_3_i, 1) &&
  opcode_port == 3'd0 &&
  pw_rden_dest_mem == 0 &&
  pw_rden_out == 0 &&
  pw_wren_out == 0 &&
  rd_valid_count == (((($past(read_state, 1) == CtReadIdle) || ($past(read_state, 1) == CtReadStage)) || ($past(buf0_valid_in, 1) && ($past(rd_valid_count, 1) >= 7'd64))) ? 7'd0 : ($past(buf0_valid_in, 1) ? (7'd4 + $past(rd_valid_count, 1)) : $past(rd_valid_count, 1))) &&
  twiddle_addr_reg_out == ($past(shuffle_en_in, 1) ? $past(twiddle_rand_offset_0_i, 1) : (($past(twiddle_addr_reg, 1) == $past(twiddle_end_addr_0_i, 1)) ? 7'd0 : (7'd1 + $past(twiddle_addr_reg, 1))));
endproperty
read_read_exec_to_read_exec_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) read_read_exec_to_read_exec_p);


property read_read_exec_to_read_exec_wait_p;
  read_exec &&
  (buf_count == 2'd3) &&
  (rd_valid_count == 7'd60)
|->
  ##1
  read_exec_wait &&
  bf_enable_out == 1 &&
  buf_count == (($past(buf0_valid_in, 1) || ((({ 30'd0, $past(buf_count, 1)} ) > 0) && (({ 30'd0, $past(buf_count, 1)} ) < 3))) ? (2'sd1 + signed'($past(buf_count, 1))) : 2'd0) &&
  buf_rden_out == 1 &&
  buf_rdptr_f_out == ($past(shuffle_en_in, 1) ? ($past(index_rand_offset, 1) + $past(buf_count, 1)) : $past(buf_count, 1)) &&
  buf_rdptr_reg_1 == (((($past(butterfly_ready_in, 1) || ($past(buf0_valid_in, 1) && ($past(read_state, 1) == CtReadBuf))) || ($past(read_state, 1) == CtReadExec)) || ($past(read_state, 1) == CtReadExecwait)) ? ({ ($past(shuffle_en_in, 1) ? ($past(index_rand_offset, 1) + $past(buf_count, 1)) : $past(buf_count, 1)), { $past(buf_rdptr_reg_1, 1) }[13:2]} ) : 14'd0) &&
  chunk_count_reg_1 == (((($past(butterfly_ready_in, 1) || ($past(buf0_valid_in, 1) && ($past(read_state, 1) == CtReadBuf))) || ($past(read_state, 1) == CtReadExec)) || ($past(read_state, 1) == CtReadExecwait)) ? ({ $past(chunk_count_in, 1), { $past(chunk_count_reg_1, 1) }[27:4]} ) : $past(chunk_count_reg_1, 1)) &&
  index_rand_offset == ($past(latch_index_rand_offset_port, 1) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  mem_read_req_port == $past(mem_read_req_port_4_i, 1) &&
  opcode_port == 3'd0 &&
  pw_rden_dest_mem == 0 &&
  pw_rden_out == 0 &&
  pw_wren_out == 0 &&
  rd_valid_count == (((($past(read_state, 1) == CtReadIdle) || ($past(read_state, 1) == CtReadStage)) || ($past(buf0_valid_in, 1) && ($past(rd_valid_count, 1) >= 7'd64))) ? 7'd0 : ($past(buf0_valid_in, 1) ? (7'd4 + $past(rd_valid_count, 1)) : $past(rd_valid_count, 1))) &&
  twiddle_addr_reg_out == ($past(shuffle_en_in, 1) ? $past(twiddle_rand_offset_0_i, 1) : (($past(twiddle_addr_reg, 1) == $past(twiddle_end_addr_0_i, 1)) ? 7'd0 : (7'd1 + $past(twiddle_addr_reg, 1))));
endproperty
read_read_exec_to_read_exec_wait_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) read_read_exec_to_read_exec_wait_p);


property read_read_exec_wait_to_read_exec_wait_p;
  read_exec_wait &&
  !((rd_valid_count == 7'd64) && (buf_count == 2'd3))
|->
  ##1
  read_exec_wait &&
  bf_enable_out == 1 &&
  buf_count == (($past(buf0_valid_in, 1) || ((({ 30'd0, $past(buf_count, 1)} ) > 0) && (({ 30'd0, $past(buf_count, 1)} ) < 3))) ? (2'sd1 + signed'($past(buf_count, 1))) : 2'd0) &&
  buf_rden_out == 1 &&
  buf_rdptr_f_out == ($past(shuffle_en_in, 1) ? ($past(index_rand_offset, 1) + $past(buf_count, 1)) : $past(buf_count, 1)) &&
  buf_rdptr_reg_1 == (((($past(butterfly_ready_in, 1) || ($past(buf0_valid_in, 1) && ($past(read_state, 1) == CtReadBuf))) || ($past(read_state, 1) == CtReadExec)) || ($past(read_state, 1) == CtReadExecwait)) ? ({ ($past(shuffle_en_in, 1) ? ($past(index_rand_offset, 1) + $past(buf_count, 1)) : $past(buf_count, 1)), { $past(buf_rdptr_reg_1, 1) }[13:2]} ) : 14'd0) &&
  chunk_count_reg_1 == (((($past(butterfly_ready_in, 1) || ($past(buf0_valid_in, 1) && ($past(read_state, 1) == CtReadBuf))) || ($past(read_state, 1) == CtReadExec)) || ($past(read_state, 1) == CtReadExecwait)) ? ({ $past(chunk_count_in, 1), { $past(chunk_count_reg_1, 1) }[27:4]} ) : $past(chunk_count_reg_1, 1)) &&
  index_rand_offset == ($past(latch_index_rand_offset_port, 1) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  mem_read_req_port == $past(mem_read_req_port_5_i, 1) &&
  opcode_port == 3'd0 &&
  pw_rden_dest_mem == 0 &&
  pw_rden_out == 0 &&
  pw_wren_out == 0 &&
  rd_valid_count == (((($past(read_state, 1) == CtReadIdle) || ($past(read_state, 1) == CtReadStage)) || ($past(buf0_valid_in, 1) && ($past(rd_valid_count, 1) >= 7'd64))) ? 7'd0 : ($past(buf0_valid_in, 1) ? (7'd4 + $past(rd_valid_count, 1)) : $past(rd_valid_count, 1))) &&
  twiddle_addr_reg_out == ($past(shuffle_en_in, 1) ? $past(twiddle_rand_offset_0_i, 1) : (($past(twiddle_addr_reg, 1) == $past(twiddle_end_addr_0_i, 1)) ? 7'd0 : (7'd1 + $past(twiddle_addr_reg, 1))));
endproperty
read_read_exec_wait_to_read_exec_wait_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) read_read_exec_wait_to_read_exec_wait_p);


property read_read_exec_wait_to_read_stage_p;
  read_exec_wait &&
  (rd_valid_count == 7'd64) &&
  (buf_count == 2'd3)
|->
  ##1
  read_stage &&
  bf_enable_out == 1 &&
  buf_count == (($past(buf0_valid_in, 1) || ((({ 30'd0, $past(buf_count, 1)} ) > 0) && (({ 30'd0, $past(buf_count, 1)} ) < 3))) ? (2'sd1 + signed'($past(buf_count, 1))) : 2'd0) &&
  buf_rden_out == 1 &&
  buf_rdptr_f_out == ($past(shuffle_en_in, 1) ? ($past(index_rand_offset, 1) + $past(buf_count, 1)) : $past(buf_count, 1)) &&
  buf_rdptr_reg_1 == (((($past(butterfly_ready_in, 1) || ($past(buf0_valid_in, 1) && ($past(read_state, 1) == CtReadBuf))) || ($past(read_state, 1) == CtReadExec)) || ($past(read_state, 1) == CtReadExecwait)) ? ({ ($past(shuffle_en_in, 1) ? ($past(index_rand_offset, 1) + $past(buf_count, 1)) : $past(buf_count, 1)), { $past(buf_rdptr_reg_1, 1) }[13:2]} ) : 14'd0) &&
  chunk_count_reg_1 == (((($past(butterfly_ready_in, 1) || ($past(buf0_valid_in, 1) && ($past(read_state, 1) == CtReadBuf))) || ($past(read_state, 1) == CtReadExec)) || ($past(read_state, 1) == CtReadExecwait)) ? ({ $past(chunk_count_in, 1), { $past(chunk_count_reg_1, 1) }[27:4]} ) : $past(chunk_count_reg_1, 1)) &&
  index_rand_offset == ($past(latch_index_rand_offset_port, 1) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  mem_read_req_port == $past(mem_read_req_port_5_i, 1) &&
  opcode_port == 3'd0 &&
  pw_rden_dest_mem == 0 &&
  pw_rden_out == 0 &&
  pw_wren_out == 0 &&
  rd_valid_count == (((($past(read_state, 1) == CtReadIdle) || ($past(read_state, 1) == CtReadStage)) || ($past(buf0_valid_in, 1) && ($past(rd_valid_count, 1) >= 7'd64))) ? 7'd0 : ($past(buf0_valid_in, 1) ? (7'd4 + $past(rd_valid_count, 1)) : $past(rd_valid_count, 1))) &&
  twiddle_addr_reg_out == ($past(shuffle_en_in, 1) ? $past(twiddle_rand_offset_0_i, 1) : (($past(twiddle_addr_reg, 1) == $past(twiddle_end_addr_0_i, 1)) ? 7'd0 : (7'd1 + $past(twiddle_addr_reg, 1))));
endproperty
read_read_exec_wait_to_read_stage_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) read_read_exec_wait_to_read_stage_p);


property read_read_idle_to_read_idle_p;
  read_idle &&
  !ntt_enable_in
|->
  ##1
  read_idle &&
  bf_enable_out == 0 &&
  buf_count == ($past(buf0_valid_in, 1) ? 2'd1 : 2'd0) &&
  buf_rden_out == 0 &&
  buf_rdptr_f_out == ($past(shuffle_en_in, 1) ? ($past(index_rand_offset, 1) + $past(buf_count, 1)) : $past(buf_count, 1)) &&
  buf_rdptr_reg_1 == (((($past(butterfly_ready_in, 1) || ($past(buf0_valid_in, 1) && ($past(read_state, 1) == CtReadBuf))) || ($past(read_state, 1) == CtReadExec)) || ($past(read_state, 1) == CtReadExecwait)) ? ({ ($past(shuffle_en_in, 1) ? ($past(index_rand_offset, 1) + $past(buf_count, 1)) : $past(buf_count, 1)), { $past(buf_rdptr_reg_1, 1) }[13:2]} ) : 14'd0) &&
  chunk_count_reg_1 == (((($past(butterfly_ready_in, 1) || ($past(buf0_valid_in, 1) && ($past(read_state, 1) == CtReadBuf))) || ($past(read_state, 1) == CtReadExec)) || ($past(read_state, 1) == CtReadExecwait)) ? ({ $past(chunk_count, 1), { $past(chunk_count_reg_1, 1) }[27:4]} ) : $past(chunk_count_reg_1, 1)) &&
  index_rand_offset == ($past(latch_index_rand_offset_port, 1) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  mem_read_req_port == $past(mem_read_req_port_1_i, 1) &&
  opcode_port == 3'd0 &&
  pw_rden_dest_mem == 0 &&
  pw_rden_out == 0 &&
  pw_wren_out == 0 &&
  rd_valid_count == (((($past(read_state, 1) == CtReadIdle) || ($past(read_state, 1) == CtReadStage)) || ($past(buf0_valid_in, 1) && ($past(rd_valid_count, 1) >= 7'd64))) ? 7'd0 : ($past(buf0_valid_in, 1) ? (7'd4 + $past(rd_valid_count, 1)) : $past(rd_valid_count, 1))) &&
  twiddle_addr_reg_out == 7'd0;
endproperty
read_read_idle_to_read_idle_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) read_read_idle_to_read_idle_p);


property read_read_idle_to_read_stage_p;
  read_idle &&
  ntt_enable_in
|->
  ##1
  read_stage &&
  bf_enable_out == 0 &&
  buf_count == ($past(buf0_valid_in, 1) ? 2'd1 : 2'd0) &&
  buf_rden_out == 0 &&
  buf_rdptr_f_out == ($past(shuffle_en_in, 1) ? ($past(index_rand_offset, 1) + $past(buf_count, 1)) : $past(buf_count, 1)) &&
  buf_rdptr_reg_1 == (((($past(butterfly_ready_in, 1) || ($past(buf0_valid_in, 1) && ($past(read_state, 1) == CtReadBuf))) || ($past(read_state, 1) == CtReadExec)) || ($past(read_state, 1) == CtReadExecwait)) ? ({ ($past(shuffle_en_in, 1) ? ($past(index_rand_offset, 1) + $past(buf_count, 1)) : $past(buf_count, 1)), { $past(buf_rdptr_reg_1, 1) }[13:2]} ) : 14'd0) &&
  chunk_count_reg_1 == (((($past(butterfly_ready_in, 1) || ($past(buf0_valid_in, 1) && ($past(read_state, 1) == CtReadBuf))) || ($past(read_state, 1) == CtReadExec)) || ($past(read_state, 1) == CtReadExecwait)) ? ({ $past(chunk_count, 1), { $past(chunk_count_reg_1, 1) }[27:4]} ) : $past(chunk_count_reg_1, 1)) &&
  index_rand_offset == ($past(latch_index_rand_offset_port, 1) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  mem_read_req_port == $past(mem_read_req_port_1_i, 1) &&
  opcode_port == 3'd0 &&
  pw_rden_dest_mem == 0 &&
  pw_rden_out == 0 &&
  pw_wren_out == 0 &&
  rd_valid_count == (((($past(read_state, 1) == CtReadIdle) || ($past(read_state, 1) == CtReadStage)) || ($past(buf0_valid_in, 1) && ($past(rd_valid_count, 1) >= 7'd64))) ? 7'd0 : ($past(buf0_valid_in, 1) ? (7'd4 + $past(rd_valid_count, 1)) : $past(rd_valid_count, 1))) &&
  twiddle_addr_reg_out == 7'd0;
endproperty
read_read_idle_to_read_stage_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) read_read_idle_to_read_stage_p);


property read_read_stage_to_read_buf_p;
  read_stage &&
  (rounds_count_in != 3'd4) &&
  (write_state == CtWriteStage)
|->
  ##1
  read_buf &&
  bf_enable_out == 0 &&
  buf_count == (($past(buf0_valid_in, 1) || ((({ 30'd0, $past(buf_count, 1)} ) > 0) && (({ 30'd0, $past(buf_count, 1)} ) < 3))) ? (2'sd1 + signed'($past(buf_count, 1))) : 2'd0) &&
  buf_rden_out == 0 &&
  buf_rdptr_f_out == ($past(shuffle_en_in, 1) ? ($past(index_rand_offset, 1) + $past(buf_count, 1)) : $past(buf_count, 1)) &&
  buf_rdptr_reg_1 == (((($past(butterfly_ready_in, 1) || ($past(buf0_valid_in, 1) && ($past(read_state, 1) == CtReadBuf))) || ($past(read_state, 1) == CtReadExec)) || ($past(read_state, 1) == CtReadExecwait)) ? ({ ($past(shuffle_en_in, 1) ? ($past(index_rand_offset, 1) + $past(buf_count, 1)) : $past(buf_count, 1)), { $past(buf_rdptr_reg_1, 1) }[13:2]} ) : 14'd0) &&
  chunk_count_reg_1 == (((($past(butterfly_ready_in, 1) || ($past(buf0_valid_in, 1) && ($past(read_state, 1) == CtReadBuf))) || ($past(read_state, 1) == CtReadExec)) || ($past(read_state, 1) == CtReadExecwait)) ? ({ $past(chunk_count_in, 1), { $past(chunk_count_reg_1, 1) }[27:4]} ) : $past(chunk_count_reg_1, 1)) &&
  index_rand_offset == ($past(latch_index_rand_offset_port, 1) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  mem_read_req_port == $past(mem_read_req_port_1_i, 1) &&
  opcode_port == 3'd0 &&
  pw_rden_dest_mem == 0 &&
  pw_rden_out == 0 &&
  pw_wren_out == 0 &&
  rd_valid_count == (((($past(read_state, 1) == CtReadIdle) || ($past(read_state, 1) == CtReadStage)) || ($past(buf0_valid_in, 1) && ($past(rd_valid_count, 1) >= 7'd64))) ? 7'd0 : ($past(buf0_valid_in, 1) ? (7'd4 + $past(rd_valid_count, 1)) : $past(rd_valid_count, 1))) &&
  twiddle_addr_reg_out == ($past(butterfly_ready_in, 1) ? $past(twiddle_addr_reg, 1) : 7'd0);
endproperty
read_read_stage_to_read_buf_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) read_read_stage_to_read_buf_p);


property read_read_stage_to_read_idle_p;
  read_stage &&
  (rounds_count_in == 3'd4)
|->
  ##1
  read_idle &&
  bf_enable_out == 0 &&
  buf_count == (($past(buf0_valid_in, 1) || ((({ 30'd0, $past(buf_count, 1)} ) > 0) && (({ 30'd0, $past(buf_count, 1)} ) < 3))) ? (2'sd1 + signed'($past(buf_count, 1))) : 2'd0) &&
  buf_rden_out == 0 &&
  buf_rdptr_f_out == ($past(shuffle_en_in, 1) ? ($past(index_rand_offset, 1) + $past(buf_count, 1)) : $past(buf_count, 1)) &&
  buf_rdptr_reg_1 == (((($past(butterfly_ready_in, 1) || ($past(buf0_valid_in, 1) && ($past(read_state, 1) == CtReadBuf))) || ($past(read_state, 1) == CtReadExec)) || ($past(read_state, 1) == CtReadExecwait)) ? ({ ($past(shuffle_en_in, 1) ? ($past(index_rand_offset, 1) + $past(buf_count, 1)) : $past(buf_count, 1)), { $past(buf_rdptr_reg_1, 1) }[13:2]} ) : 14'd0) &&
  chunk_count_reg_1 == (((($past(butterfly_ready_in, 1) || ($past(buf0_valid_in, 1) && ($past(read_state, 1) == CtReadBuf))) || ($past(read_state, 1) == CtReadExec)) || ($past(read_state, 1) == CtReadExecwait)) ? ({ $past(chunk_count_in, 1), { $past(chunk_count_reg_1, 1) }[27:4]} ) : $past(chunk_count_reg_1, 1)) &&
  index_rand_offset == ($past(latch_index_rand_offset_port, 1) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  mem_read_req_port == $past(mem_read_req_port_1_i, 1) &&
  opcode_port == 3'd0 &&
  pw_rden_dest_mem == 0 &&
  pw_rden_out == 0 &&
  pw_wren_out == 0 &&
  rd_valid_count == (((($past(read_state, 1) == CtReadIdle) || ($past(read_state, 1) == CtReadStage)) || ($past(buf0_valid_in, 1) && ($past(rd_valid_count, 1) >= 7'd64))) ? 7'd0 : ($past(buf0_valid_in, 1) ? (7'd4 + $past(rd_valid_count, 1)) : $past(rd_valid_count, 1))) &&
  twiddle_addr_reg_out == ($past(butterfly_ready_in, 1) ? $past(twiddle_addr_reg, 1) : 7'd0);
endproperty
read_read_stage_to_read_idle_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) read_read_stage_to_read_idle_p);


property read_read_stage_to_read_stage_p;
  read_stage &&
  (rounds_count_in != 3'd4) &&
  (write_state != CtWriteStage)
|->
  ##1
  read_stage &&
  bf_enable_out == 0 &&
  buf_count == (($past(buf0_valid_in, 1) || ((({ 30'd0, $past(buf_count, 1)} ) > 0) && (({ 30'd0, $past(buf_count, 1)} ) < 3))) ? (2'sd1 + signed'($past(buf_count, 1))) : 2'd0) &&
  buf_rden_out == 0 &&
  buf_rdptr_f_out == ($past(shuffle_en_in, 1) ? ($past(index_rand_offset, 1) + $past(buf_count, 1)) : $past(buf_count, 1)) &&
  buf_rdptr_reg_1 == (((($past(butterfly_ready_in, 1) || ($past(buf0_valid_in, 1) && ($past(read_state, 1) == CtReadBuf))) || ($past(read_state, 1) == CtReadExec)) || ($past(read_state, 1) == CtReadExecwait)) ? ({ ($past(shuffle_en_in, 1) ? ($past(index_rand_offset, 1) + $past(buf_count, 1)) : $past(buf_count, 1)), { $past(buf_rdptr_reg_1, 1) }[13:2]} ) : 14'd0) &&
  chunk_count_reg_1 == (((($past(butterfly_ready_in, 1) || ($past(buf0_valid_in, 1) && ($past(read_state, 1) == CtReadBuf))) || ($past(read_state, 1) == CtReadExec)) || ($past(read_state, 1) == CtReadExecwait)) ? ({ $past(chunk_count_in, 1), { $past(chunk_count_reg_1, 1) }[27:4]} ) : $past(chunk_count_reg_1, 1)) &&
  index_rand_offset == ($past(latch_index_rand_offset_port, 1) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  mem_read_req_port == $past(mem_read_req_port_1_i, 1) &&
  opcode_port == 3'd0 &&
  pw_rden_dest_mem == 0 &&
  pw_rden_out == 0 &&
  pw_wren_out == 0 &&
  rd_valid_count == (((($past(read_state, 1) == CtReadIdle) || ($past(read_state, 1) == CtReadStage)) || ($past(buf0_valid_in, 1) && ($past(rd_valid_count, 1) >= 7'd64))) ? 7'd0 : ($past(buf0_valid_in, 1) ? (7'd4 + $past(rd_valid_count, 1)) : $past(rd_valid_count, 1))) &&
  twiddle_addr_reg_out == ($past(butterfly_ready_in, 1) ? $past(twiddle_addr_reg, 1) : 7'd0);
endproperty
read_read_stage_to_read_stage_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) read_read_stage_to_read_stage_p);


property write_write_idle_to_write_idle_p;
  write_idle &&
  !ntt_enable_in
|->
  ##1
  write_idle &&
  chunk_count_write == (($past(buf_count, 1) == 2'd3) ? (4'd1 + $past(chunk_count_write, 1)) : $past(chunk_count_write, 1)) &&
  $stable(chunk_rand_offset_write) &&
  done_out == 0 &&
  mem_write_req_port == $past(mem_write_req_port_0_i, 1) &&
  rounds_count_out == 3'd0 &&
  wr_valid_count == (($past(write_state, 1) == CtWriteMem) ? ($past(butterfly_ready_in, 1) ? (7'd1 + $past(wr_valid_count, 1)) : $past(wr_valid_count, 1)) : 7'd0);
endproperty
write_write_idle_to_write_idle_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) write_write_idle_to_write_idle_p);


property write_write_idle_to_write_stage_p;
  write_idle &&
  ntt_enable_in
|->
  ##1
  write_stage &&
  chunk_count_write == { $past(random_in, 1) }[5:2] &&
  chunk_rand_offset_write == { $past(random_in, 1) }[5:2] &&
  done_out == 0 &&
  mem_write_req_port == $past(mem_write_req_port_0_i, 1) &&
  rounds_count_out == 3'd0 &&
  wr_valid_count == (($past(write_state, 1) == CtWriteMem) ? ($past(butterfly_ready_in, 1) ? (7'd1 + $past(wr_valid_count, 1)) : $past(wr_valid_count, 1)) : 7'd0);
endproperty
write_write_idle_to_write_stage_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) write_write_idle_to_write_stage_p);


property write_write_mem_to_write_mem_p;
  write_mem &&
  (wr_valid_count != 7'd63)
|->
  ##1 ($stable(rounds_count_out)) and
  ##1
  write_mem &&
  chunk_count_write == (($past(buf_count, 1) == 2'd3) ? (4'd1 + $past(chunk_count_write, 1)) : $past(chunk_count_write, 1)) &&
  $stable(chunk_rand_offset_write) &&
  done_out == ($past(rounds_count_write, 1) == 3'd4) &&
  mem_write_req_port == $past(mem_write_req_port_2_i, 1) &&
  wr_valid_count == (($past(write_state, 1) == CtWriteMem) ? ($past(butterfly_ready_in, 1) ? (7'd1 + $past(wr_valid_count, 1)) : $past(wr_valid_count, 1)) : 7'd0);
endproperty
write_write_mem_to_write_mem_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) write_write_mem_to_write_mem_p);


property write_write_mem_to_write_stage_p;
  write_mem &&
  (wr_valid_count == 7'd63)
|->
  ##1
  write_stage &&
  chunk_count_write == { $past(random_in, 1) }[5:2] &&
  chunk_rand_offset_write == { $past(random_in, 1) }[5:2] &&
  done_out == (((({ 29'd0, $past(rounds_count_write, 1)} ) < 4) ? (3'd1 + $past(rounds_count_write, 1)) : 3'd0) == 3'd4) &&
  mem_write_req_port == $past(mem_write_req_port_2_i, 1) &&
  rounds_count_out == ((({ 29'd0, $past(rounds_count_write, 1)} ) < 4) ? (3'd1 + $past(rounds_count_write, 1)) : 3'd0) &&
  wr_valid_count == (($past(write_state, 1) == CtWriteMem) ? ($past(butterfly_ready_in, 1) ? (7'd1 + $past(wr_valid_count, 1)) : $past(wr_valid_count, 1)) : 7'd0);
endproperty
write_write_mem_to_write_stage_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) write_write_mem_to_write_stage_p);


property write_write_stage_to_write_idle_p;
  write_stage &&
  (rounds_count_write == 3'd4)
|->
  ##1
  write_idle &&
  chunk_count_write == (($past(buf_count, 1) == 2'd3) ? (4'd1 + $past(chunk_count_write, 1)) : $past(chunk_count_write, 1)) &&
  $stable(chunk_rand_offset_write) &&
  done_out == 0 &&
  mem_write_req_port == $past(mem_write_req_port_1_i, 1) &&
  rounds_count_out == 3'd0 &&
  wr_valid_count == (($past(write_state, 1) == CtWriteMem) ? ($past(butterfly_ready_in, 1) ? (7'd1 + $past(wr_valid_count, 1)) : $past(wr_valid_count, 1)) : 7'd0);
endproperty
write_write_stage_to_write_idle_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) write_write_stage_to_write_idle_p);


property write_write_stage_to_write_mem_p;
  write_stage &&
  (rounds_count_write != 3'd4)
|->
  ##1 ($stable(rounds_count_out)) and
  ##1
  write_mem &&
  chunk_count_write == (($past(buf_count, 1) == 2'd3) ? (4'd1 + $past(chunk_count_write, 1)) : $past(chunk_count_write, 1)) &&
  $stable(chunk_rand_offset_write) &&
  done_out == ($past(rounds_count_write, 1) == 3'd4) &&
  mem_write_req_port == $past(mem_write_req_port_1_i, 1) &&
  wr_valid_count == (($past(write_state, 1) == CtWriteMem) ? ($past(butterfly_ready_in, 1) ? (7'd1 + $past(wr_valid_count, 1)) : $past(wr_valid_count, 1)) : 7'd0);
endproperty
write_write_stage_to_write_mem_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) write_write_stage_to_write_mem_p);


// Manually added `ntt_enable_in` in the assumption part
// instead of adding eventually(ntt_enable_in) as constraint.
property read_read_idle_eventually_left_p;
  read_idle &&
  ntt_enable_in
|->
  s_eventually(!read_idle);
endproperty
read_read_idle_eventually_left_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) read_read_idle_eventually_left_p);


property read_read_stage_eventually_left_p;
  read_stage
|->
  s_eventually(!read_stage);
endproperty
read_read_stage_eventually_left_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) read_read_stage_eventually_left_p);


property read_read_buf_eventually_left_p;
  read_buf
|->
  s_eventually(!read_buf);
endproperty
read_read_buf_eventually_left_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) read_read_buf_eventually_left_p);


property read_read_exec_eventually_left_p;
  read_exec
|->
  s_eventually(!read_exec);
endproperty
read_read_exec_eventually_left_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) read_read_exec_eventually_left_p);


property read_read_exec_wait_eventually_left_p;
  read_exec_wait
|->
  s_eventually(!read_exec_wait);
endproperty
read_read_exec_wait_eventually_left_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) read_read_exec_wait_eventually_left_p);


// Manually added `ntt_enable_in` in the assumption part
// instead of adding eventually(ntt_enable_in) as constraint.
property write_write_idle_eventually_left_p;
  write_idle &&
  ntt_enable_in
|->
  s_eventually(!write_idle);
endproperty
write_write_idle_eventually_left_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) write_write_idle_eventually_left_p);


property write_write_stage_eventually_left_p;
  write_stage
|->
  s_eventually(!write_stage);
endproperty
write_write_stage_eventually_left_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) write_write_stage_eventually_left_p);


property write_write_mem_eventually_left_p;
  write_mem
|->
  s_eventually(!write_mem);
endproperty
write_write_mem_eventually_left_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) write_write_mem_eventually_left_p);


parameter CONSISTENCY = 1;
if (CONSISTENCY) begin
  // Check that no more than 1 state condition is met at the same time
  read_consistency_onehot0_state: assert property($onehot0({ read_buf, read_exec, read_exec_wait, read_idle, read_stage }));
end


if (CONSISTENCY) begin
  // Check that no more than 1 state condition is met at the same time
  write_consistency_onehot0_state: assert property($onehot0({ write_idle, write_mem, write_stage }));
end


endmodule
