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
// | Created on 05.08.2025 at 16:36                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import ntt_ctrl_ct_mlkem_pkg::*;
import abr_params_pkg::*;
import ntt_defines_pkg::*;
import ntt_ctrl_ct_mlkem_pkg::*;
import ntt_ctrl_ct_mlkem_functions::*;


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

  input logic buf_wren_out,

  input logic buf_rden_out,

  input logic pw_rden_out,

  input logic pw_wren_out,

  input logic unsigned [2:0] rounds_count_out,

  input logic ntt_done_out,

  input logic unsigned [2:0] opcode_port,

  input logic masking_en_ctrl_out,

  input logic unsigned [6:0] twiddle_addr_reg_out,

  input logic ntt_passthrough_out,

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

  input logic unsigned [3:0] mlkem_chunk_count_reg_port,

  input logic unsigned [1:0] buf_rdptr_reg_port,

  input logic unsigned [1:0] mlkem_buf_rdptr_reg_port,

  input logic latch_index_rand_offset_port,

  // Registers
  input logic unsigned [1:0] buf_count,
  input logic unsigned [21:0] buf_rdptr_reg_1,
  input logic unsigned [3:0] chunk_count,
  input logic unsigned [43:0] chunk_count_reg_1,
  input logic unsigned [3:0] chunk_count_write,
  input logic unsigned [3:0] chunk_rand_offset_write,
  input logic unsigned [1:0] index_rand_offset,
  input logic unsigned [15:0] mem_rd_next_addr,
  input logic ntt_done,
  input logic ntt_done_read,
  input logic unsigned [6:0] rd_valid_count,
  input st_Request_and_Address read_req,
  input e_CtReadStatesType read_state,
  input logic unsigned [2:0] rounds_count_write,
  input logic shuffle_en,
  input logic unsigned [6:0] twiddle_addr_reg,
  input logic wr_stage_set,
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
  input logic write_mem,
  input logic undriven_state
);


default clocking default_clk @(posedge clk); endclocking


st_Request_and_Address mem_read_req_port_0_i;
assign mem_read_req_port_0_i = '{
  request: 0,
  address: 15'd0
};

st_Request_and_Address mem_read_req_port_1_i;
assign mem_read_req_port_1_i = '{
  request: 0,
  address: (shuffle_en_in ? 15'((((rounds_count_in == 3'd0) ? base_address_port.source : ((rounds_count_in[0] == 0) ? base_address_port.destination : base_address_port.interim)) + chunk_rand_offset_in)) : 15'(((rounds_count_in == 3'd0) ? base_address_port.source : ((rounds_count_in[0] == 0) ? base_address_port.destination : base_address_port.interim))))
};

logic unsigned [6:0] twiddle_rand_offset_0_i;
assign twiddle_rand_offset_0_i = twiddle_rand_offset(rounds_count_in, (shuffle_en_in ? (index_rand_offset + buf_count) : buf_count), chunk_count_in);

logic unsigned [6:0] twiddle_end_addr_0_i;
assign twiddle_end_addr_0_i = twiddle_end_addr(rounds_count_in);

st_Request_and_Address mem_read_req_port_2_i;
assign mem_read_req_port_2_i = '{
  request: 1,
  address: (shuffle_en_in ? ((read_req.address == (15'd63 + ((rounds_count_in == 3'd0) ? ({ 1'd0, base_address_port.source} ) : ((rounds_count_in[0] == 0) ? ({ 1'd0, base_address_port.destination} ) : ({ 1'd0, base_address_port.interim} ))))) ? 16'(((rounds_count_in == 3'd0) ? base_address_port.source : ((rounds_count_in[0] == 0) ? base_address_port.destination : base_address_port.interim))) : (((16 + ({ 17'd0, read_req.address} )) > (63 + ((rounds_count_in == 3'd0) ? ({ 18'd0, base_address_port.source} ) : ((rounds_count_in[0] == 0) ? ({ 18'd0, base_address_port.destination} ) : ({ 18'd0, base_address_port.interim} ))))) ? (16'((16 + ({ 17'd0, read_req.address} ))) - 15'd63) : 16'({ 16'((16 + ({ 17'd0, read_req.address} ))) }[14:0]))) : (((16 + ({ 17'd0, read_req.address} )) > (63 + ((rounds_count_in == 3'd0) ? ({ 18'd0, base_address_port.source} ) : ((rounds_count_in[0] == 0) ? ({ 18'd0, base_address_port.destination} ) : ({ 18'd0, base_address_port.interim} ))))) ? (16'((16 + ({ 17'd0, read_req.address} ))) - 15'd63) : 16'({ 16'((16 + ({ 17'd0, read_req.address} ))) }[14:0])))
};

st_Request_and_Address read_req_0_i;
assign read_req_0_i = '{
  request: ((({ 17'd0, read_req.address} ) <= (63 + ((rounds_count_in == 3'd0) ? ({ 18'd0, base_address_port.source} ) : ((rounds_count_in[0] == 0) ? ({ 18'd0, base_address_port.destination} ) : ({ 18'd0, base_address_port.interim} ))))) && !((buf_count == 2'd3) && (rd_valid_count == 7'd60))),
  address: (shuffle_en_in ? ((({ 17'd0, read_req.address} ) == (63 + ((rounds_count_in == 3'd0) ? ({ 18'd0, base_address_port.source} ) : ((rounds_count_in[0] == 0) ? ({ 18'd0, base_address_port.destination} ) : ({ 18'd0, base_address_port.interim} ))))) ? 16'(((rounds_count_in == 3'd0) ? base_address_port.source : ((rounds_count_in[0] == 0) ? base_address_port.destination : base_address_port.interim))) : ((({ 16'd0, mem_rd_next_addr} ) > (63 + ((rounds_count_in == 3'd0) ? ({ 18'd0, base_address_port.source} ) : ((rounds_count_in[0] == 0) ? ({ 18'd0, base_address_port.destination} ) : ({ 18'd0, base_address_port.interim} ))))) ? (16'((16 + ({ 17'd0, read_req.address} ))) - 15'd63) : 16'({ 16'((16 + ({ 17'd0, read_req.address} ))) }[14:0]))) : ((({ 16'd0, mem_rd_next_addr} ) > (63 + ((rounds_count_in == 3'd0) ? ({ 18'd0, base_address_port.source} ) : ((rounds_count_in[0] == 0) ? ({ 18'd0, base_address_port.destination} ) : ({ 18'd0, base_address_port.interim} ))))) ? (16'((16 + ({ 17'd0, read_req.address} ))) - 15'd63) : 16'({ 16'((16 + ({ 17'd0, read_req.address} ))) }[14:0])))
};

st_Request_and_Address mem_read_req_port_3_i;
assign mem_read_req_port_3_i = '{
  request: 0,
  address: read_req.address
};

st_Request_and_Address mem_write_req_port_0_i;
assign mem_write_req_port_0_i = '{
  request: 0,
  address: (shuffle_en ? 15'((({ 50'd0, base_address_port.interim} ) + (64'd4 * ({ 60'd0, chunk_rand_offset_write} )))) : 15'(base_address_port.interim))
};

st_Request_and_Address mem_write_req_port_1_i;
assign mem_write_req_port_1_i = '{
  request: 0,
  address: (shuffle_en ? 15'((((rounds_count_write[0] == 0) ? ({ 50'd0, base_address_port.interim} ) : ({ 50'd0, base_address_port.destination} )) + (64'd4 * ({ 60'd0, chunk_rand_offset_write} )))) : 15'(((rounds_count_write[0] == 0) ? base_address_port.interim : base_address_port.destination)))
};

st_Request_and_Address mem_write_req_port_2_i;
assign mem_write_req_port_2_i = '{
  request: butterfly_ready_in,
  address: (butterfly_ready_in ? 15'((((shuffle_en ? (mlkem_in ? 16'((((64'd4 * mlkem_chunk_count_reg_port) + mlkem_buf_rdptr_reg_port) + ((rounds_count_write[0] == 0) ? ({ 50'd0, base_address_port.interim} ) : ({ 50'd0, base_address_port.destination} )))) : 16'((((64'd4 * chunk_count_reg_port) + buf_rdptr_reg_port) + ((rounds_count_write[0] == 0) ? ({ 50'd0, base_address_port.interim} ) : ({ 50'd0, base_address_port.destination} ))))) : 16'((1 + ({ 17'd0, write_req.address} )))) > (64'd63 + ((rounds_count_write[0] == 0) ? ({ 50'd0, base_address_port.interim} ) : ({ 50'd0, base_address_port.destination} )))) ? ((shuffle_en ? (mlkem_in ? 16'((((64'd4 * mlkem_chunk_count_reg_port) + mlkem_buf_rdptr_reg_port) + ((rounds_count_write[0] == 0) ? ({ 50'd0, base_address_port.interim} ) : ({ 50'd0, base_address_port.destination} )))) : 16'((((64'd4 * chunk_count_reg_port) + buf_rdptr_reg_port) + ((rounds_count_write[0] == 0) ? ({ 50'd0, base_address_port.interim} ) : ({ 50'd0, base_address_port.destination} ))))) : 16'((1 + ({ 17'd0, write_req.address} )))) - 15'd63) : 16'((shuffle_en ? (mlkem_in ? { 16'((((64'd4 * mlkem_chunk_count_reg_port) + mlkem_buf_rdptr_reg_port) + ((rounds_count_write[0] == 0) ? ({ 50'd0, base_address_port.interim} ) : ({ 50'd0, base_address_port.destination} )))) }[14:0] : { 16'((((64'd4 * chunk_count_reg_port) + buf_rdptr_reg_port) + ((rounds_count_write[0] == 0) ? ({ 50'd0, base_address_port.interim} ) : ({ 50'd0, base_address_port.destination} )))) }[14:0]) : { 16'((1 + ({ 17'd0, write_req.address} ))) }[14:0])))) : write_req.address)
};


sequence reset_sequence;
  !rst_n ##1 rst_n;
endsequence


property read_reset_p;
  $past(!ntt_ctrl.reset_n || ntt_ctrl.zeroize) |->
  read_idle &&
  bf_enable_out == 0 &&
  buf_count == 2'd0 &&
  buf_rden_out == 0 &&
  buf_rdptr_f_out == 2'd0 &&
  buf_rdptr_reg_1 == 22'd0 &&
  buf_wren_out == 0 &&
  chunk_count_reg_1 == 44'd0 &&
  index_rand_offset == 2'd0 &&
  masking_en_ctrl_out == 0 &&
  mem_read_req_port == mem_read_req_port_0_i &&
  ntt_passthrough_out == 0 &&
  opcode_port == 3'd0 &&
  pw_rden_out == 0 &&
  pw_wren_out == 0 &&
  rd_valid_count == 7'd0 &&
  twiddle_addr_reg_out == 7'd0;
endproperty
read_reset_a: assert property (read_reset_p);


property write_reset_p;
  $past(!ntt_ctrl.reset_n || ntt_ctrl.zeroize) |->
  write_idle &&
  chunk_count_write == 4'd0 &&
  chunk_rand_offset_write == 4'd0 &&
  mem_write_req_port == mem_read_req_port_0_i &&
  rounds_count_out == 3'd0 &&
  wr_valid_count == 7'd0;
endproperty
write_reset_a: assert property (write_reset_p);


property _undriven_reset_p;
  $past(!ntt_ctrl.reset_n || ntt_ctrl.zeroize) |->
  undriven_state;
endproperty
_undriven_reset_a: assert property (_undriven_reset_p);



property read_read_buf_to_read_buf_p;
  read_buf &&
  !buf0_valid_in
|->
  ##1
  read_buf &&
  bf_enable_out == $past(buf0_valid_in, 1) &&
  buf_count == (($past(buf0_valid_in, 1) || (($past(buf_count, 1) > 2'd0) && ($past(buf_count, 1) < 2'd3))) ? (2'd1 + $past(buf_count, 1)) : 2'd0) &&
  buf_rden_out == $past(buf0_valid_in, 1) &&
  buf_rdptr_f_out == ($past(shuffle_en_in, 1) ? ($past(index_rand_offset, 1) + $past(buf_count, 1)) : $past(buf_count, 1)) &&
  buf_rdptr_reg_1 == 22'((((($past(butterfly_ready_in, 1) || ($past(buf0_valid_in, 1) && ($past(read_state, 1) == CtReadBuf))) || ($past(read_state, 1) == CtReadExec)) || ($past(read_state, 1) == CtReadExecwait)) ? (24'(({ 2'h0, { $past(buf_rdptr_reg_1, 1) }[21:2]} )) | ({ { 24'(({ $past(shuffle_en_in, 1) } ? ({ $past(index_rand_offset, 1) } + { $past(buf_count, 1) }) : { $past(buf_count, 1) })) }[3:0], 20'd0} )) : 24'd0)) &&
  buf_wren_out == 1 &&
  chunk_count_reg_1 == (((($past(butterfly_ready_in, 1) || ($past(buf0_valid_in, 1) && ($past(read_state, 1) == CtReadBuf))) || ($past(read_state, 1) == CtReadExec)) || ($past(read_state, 1) == CtReadExecwait)) ? ({ { 44'({ $past(chunk_count_in, 1) }) }[3:0], { $past(chunk_count_reg_1, 1) }[43:4]} ) : $past(chunk_count_reg_1, 1)) &&
  index_rand_offset == ($past(latch_index_rand_offset_port, 1) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  masking_en_ctrl_out == 0 &&
  mem_read_req_port == $past(mem_read_req_port_2_i, 1) &&
  ntt_passthrough_out == ($past(mlkem_in, 1) && ($past(rounds_count_in, 1) == 3'd3)) &&
  opcode_port == 3'd0 &&
  pw_rden_out == 0 &&
  pw_wren_out == 0 &&
  rd_valid_count == (((($past(read_state, 1) == CtReadIdle) || ($past(read_state, 1) == CtReadStage)) || ($past(buf0_valid_in, 1) && ($past(rd_valid_count, 1) > 7'd64))) ? 7'd0 : $past(rd_valid_count, 1)) &&
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
  buf_count == (2'd1 + $past(buf_count, 1)) &&
  buf_rden_out == $past(buf0_valid_in, 1) &&
  buf_rdptr_f_out == ($past(shuffle_en_in, 1) ? ($past(index_rand_offset, 1) + $past(buf_count, 1)) : $past(buf_count, 1)) &&
  buf_rdptr_reg_1 == 22'((((($past(butterfly_ready_in, 1) || ($past(buf0_valid_in, 1) && ($past(read_state, 1) == CtReadBuf))) || ($past(read_state, 1) == CtReadExec)) || ($past(read_state, 1) == CtReadExecwait)) ? (24'(({ 2'h0, { $past(buf_rdptr_reg_1, 1) }[21:2]} )) | ({ { 24'(({ $past(shuffle_en_in, 1) } ? ({ $past(index_rand_offset, 1) } + { $past(buf_count, 1) }) : { $past(buf_count, 1) })) }[3:0], 20'd0} )) : 24'd0)) &&
  buf_wren_out == 1 &&
  chunk_count_reg_1 == (((($past(butterfly_ready_in, 1) || ($past(buf0_valid_in, 1) && ($past(read_state, 1) == CtReadBuf))) || ($past(read_state, 1) == CtReadExec)) || ($past(read_state, 1) == CtReadExecwait)) ? ({ { 44'({ $past(chunk_count_in, 1) }) }[3:0], { $past(chunk_count_reg_1, 1) }[43:4]} ) : $past(chunk_count_reg_1, 1)) &&
  index_rand_offset == ($past(latch_index_rand_offset_port, 1) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  masking_en_ctrl_out == 0 &&
  mem_read_req_port == $past(mem_read_req_port_2_i, 1) &&
  ntt_passthrough_out == ($past(mlkem_in, 1) && ($past(rounds_count_in, 1) == 3'd3)) &&
  opcode_port == 3'd0 &&
  pw_rden_out == 0 &&
  pw_wren_out == 0 &&
  rd_valid_count == (((($past(read_state, 1) == CtReadIdle) || ($past(read_state, 1) == CtReadStage)) || ($past(buf0_valid_in, 1) && ($past(rd_valid_count, 1) > 7'd64))) ? 7'd0 : (7'd4 + $past(rd_valid_count, 1))) &&
  twiddle_addr_reg_out == 7'(($past(shuffle_en_in, 1) ? ({ 57'd0, $past(twiddle_rand_offset_0_i, 1)} ) : (($past(twiddle_addr_reg, 1) == $past(twiddle_end_addr_0_i, 1)) ? 64'd0 : 7'((64'd1 + ({ 57'd0, $past(twiddle_addr_reg, 1)} ))))));
endproperty
read_read_buf_to_read_exec_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) read_read_buf_to_read_exec_p);


property read_read_exec_to_read_buf_p;
  read_exec &&
  (rd_valid_count < 7'h40) &&
  (buf_count == 2'd0) &&
  !buf0_valid_in
|->
  ##1 ($stable(mem_read_req_port)) and
  ##1 ($stable(twiddle_addr_reg_out)) and
  ##1
  read_buf &&
  bf_enable_out == 1 &&
  buf_count == 2'd0 &&
  buf_rden_out == 1 &&
  buf_rdptr_f_out == ($past(shuffle_en_in, 1) ? ($past(index_rand_offset, 1) + $past(buf_count, 1)) : $past(buf_count, 1)) &&
  buf_rdptr_reg_1 == 22'((((($past(butterfly_ready_in, 1) || ($past(buf0_valid_in, 1) && ($past(read_state, 1) == CtReadBuf))) || ($past(read_state, 1) == CtReadExec)) || ($past(read_state, 1) == CtReadExecwait)) ? (24'(({ 2'h0, { $past(buf_rdptr_reg_1, 1) }[21:2]} )) | ({ { 24'(({ $past(shuffle_en_in, 1) } ? ({ $past(index_rand_offset, 1) } + { $past(buf_count, 1) }) : { $past(buf_count, 1) })) }[3:0], 20'd0} )) : 24'd0)) &&
  buf_wren_out == 1 &&
  chunk_count_reg_1 == (((($past(butterfly_ready_in, 1) || ($past(buf0_valid_in, 1) && ($past(read_state, 1) == CtReadBuf))) || ($past(read_state, 1) == CtReadExec)) || ($past(read_state, 1) == CtReadExecwait)) ? ({ { 44'({ $past(chunk_count_in, 1) }) }[3:0], { $past(chunk_count_reg_1, 1) }[43:4]} ) : $past(chunk_count_reg_1, 1)) &&
  index_rand_offset == ($past(latch_index_rand_offset_port, 1) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  masking_en_ctrl_out == 0 &&
  ntt_passthrough_out == ($past(mlkem_in, 1) && ($past(rounds_count_in, 1) == 3'd3)) &&
  opcode_port == 3'd0 &&
  pw_rden_out == 0 &&
  pw_wren_out == 0 &&
  rd_valid_count == (((($past(read_state, 1) == CtReadIdle) || ($past(read_state, 1) == CtReadStage)) || ($past(buf0_valid_in, 1) && ($past(rd_valid_count, 1) > 7'd64))) ? 7'd0 : $past(rd_valid_count, 1));
endproperty
read_read_exec_to_read_buf_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) read_read_exec_to_read_buf_p);


property read_read_exec_to_read_exec_p;
  read_exec &&
  (!((rd_valid_count < 7'h40) && (buf_count == 2'd0)) || buf0_valid_in) &&
  !((buf_count == 2'h3) && (rd_valid_count == 7'h3C))
|->
  ##1
  read_exec &&
  bf_enable_out == 1 &&
  buf_count == (($past(buf0_valid_in, 1) || (($past(buf_count, 1) > 2'd0) && ($past(buf_count, 1) < 2'd3))) ? (2'd1 + $past(buf_count, 1)) : 2'd0) &&
  buf_rden_out == 1 &&
  buf_rdptr_f_out == ($past(shuffle_en_in, 1) ? ($past(index_rand_offset, 1) + $past(buf_count, 1)) : $past(buf_count, 1)) &&
  buf_rdptr_reg_1 == 22'((((($past(butterfly_ready_in, 1) || ($past(buf0_valid_in, 1) && ($past(read_state, 1) == CtReadBuf))) || ($past(read_state, 1) == CtReadExec)) || ($past(read_state, 1) == CtReadExecwait)) ? (24'(({ 2'h0, { $past(buf_rdptr_reg_1, 1) }[21:2]} )) | ({ { 24'(({ $past(shuffle_en_in, 1) } ? ({ $past(index_rand_offset, 1) } + { $past(buf_count, 1) }) : { $past(buf_count, 1) })) }[3:0], 20'd0} )) : 24'd0)) &&
  buf_wren_out == 1 &&
  chunk_count_reg_1 == (((($past(butterfly_ready_in, 1) || ($past(buf0_valid_in, 1) && ($past(read_state, 1) == CtReadBuf))) || ($past(read_state, 1) == CtReadExec)) || ($past(read_state, 1) == CtReadExecwait)) ? ({ { 44'({ $past(chunk_count_in, 1) }) }[3:0], { $past(chunk_count_reg_1, 1) }[43:4]} ) : $past(chunk_count_reg_1, 1)) &&
  index_rand_offset == ($past(latch_index_rand_offset_port, 1) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  masking_en_ctrl_out == 0 &&
  mem_read_req_port == $past(read_req_0_i, 1) &&
  ntt_passthrough_out == ($past(mlkem_in, 1) && ($past(rounds_count_in, 1) == 3'd3)) &&
  opcode_port == 3'd0 &&
  pw_rden_out == 0 &&
  pw_wren_out == 0 &&
  rd_valid_count == (((($past(read_state, 1) == CtReadIdle) || ($past(read_state, 1) == CtReadStage)) || ($past(buf0_valid_in, 1) && ($past(rd_valid_count, 1) > 7'd64))) ? 7'd0 : ($past(buf0_valid_in, 1) ? (7'd4 + $past(rd_valid_count, 1)) : $past(rd_valid_count, 1))) &&
  twiddle_addr_reg_out == 7'(($past(shuffle_en_in, 1) ? ({ 57'd0, $past(twiddle_rand_offset_0_i, 1)} ) : (($past(twiddle_addr_reg, 1) == $past(twiddle_end_addr_0_i, 1)) ? 64'd0 : 7'((64'd1 + ({ 57'd0, $past(twiddle_addr_reg, 1)} ))))));
endproperty
read_read_exec_to_read_exec_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) read_read_exec_to_read_exec_p);


property read_read_exec_to_read_exec_wait_p;
  read_exec &&
  (buf_count == 2'h3) &&
  (rd_valid_count == 7'h3C)
|->
  ##1
  read_exec_wait &&
  bf_enable_out == 1 &&
  buf_count == (($past(buf0_valid_in, 1) || (($past(buf_count, 1) > 2'd0) && ($past(buf_count, 1) < 2'd3))) ? (2'd1 + $past(buf_count, 1)) : 2'd0) &&
  buf_rden_out == 1 &&
  buf_rdptr_f_out == ($past(shuffle_en_in, 1) ? ($past(index_rand_offset, 1) + $past(buf_count, 1)) : $past(buf_count, 1)) &&
  buf_rdptr_reg_1 == 22'((((($past(butterfly_ready_in, 1) || ($past(buf0_valid_in, 1) && ($past(read_state, 1) == CtReadBuf))) || ($past(read_state, 1) == CtReadExec)) || ($past(read_state, 1) == CtReadExecwait)) ? (24'(({ 2'h0, { $past(buf_rdptr_reg_1, 1) }[21:2]} )) | ({ { 24'(({ $past(shuffle_en_in, 1) } ? ({ $past(index_rand_offset, 1) } + { $past(buf_count, 1) }) : { $past(buf_count, 1) })) }[3:0], 20'd0} )) : 24'd0)) &&
  buf_wren_out == 1 &&
  chunk_count_reg_1 == (((($past(butterfly_ready_in, 1) || ($past(buf0_valid_in, 1) && ($past(read_state, 1) == CtReadBuf))) || ($past(read_state, 1) == CtReadExec)) || ($past(read_state, 1) == CtReadExecwait)) ? ({ { 44'({ $past(chunk_count_in, 1) }) }[3:0], { $past(chunk_count_reg_1, 1) }[43:4]} ) : $past(chunk_count_reg_1, 1)) &&
  index_rand_offset == ($past(latch_index_rand_offset_port, 1) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  masking_en_ctrl_out == 0 &&
  mem_read_req_port == $past(read_req_0_i, 1) &&
  ntt_passthrough_out == ($past(mlkem_in, 1) && ($past(rounds_count_in, 1) == 3'd3)) &&
  opcode_port == 3'd0 &&
  pw_rden_out == 0 &&
  pw_wren_out == 0 &&
  rd_valid_count == (((($past(read_state, 1) == CtReadIdle) || ($past(read_state, 1) == CtReadStage)) || ($past(buf0_valid_in, 1) && ($past(rd_valid_count, 1) > 7'd64))) ? 7'd0 : ($past(buf0_valid_in, 1) ? (7'd4 + $past(rd_valid_count, 1)) : $past(rd_valid_count, 1))) &&
  twiddle_addr_reg_out == 7'(($past(shuffle_en_in, 1) ? ({ 57'd0, $past(twiddle_rand_offset_0_i, 1)} ) : (($past(twiddle_addr_reg, 1) == $past(twiddle_end_addr_0_i, 1)) ? 64'd0 : 7'((64'd1 + ({ 57'd0, $past(twiddle_addr_reg, 1)} ))))));
endproperty
read_read_exec_to_read_exec_wait_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) read_read_exec_to_read_exec_wait_p);


property read_read_exec_wait_to_read_exec_wait_p;
  read_exec_wait &&
  !((rd_valid_count == 7'h40) && (buf_count == 2'd3))
|->
  ##1
  read_exec_wait &&
  bf_enable_out == 1 &&
  buf_count == (($past(buf0_valid_in, 1) || (($past(buf_count, 1) > 2'd0) && ($past(buf_count, 1) < 2'd3))) ? (2'd1 + $past(buf_count, 1)) : 2'd0) &&
  buf_rden_out == 1 &&
  buf_rdptr_f_out == ($past(shuffle_en_in, 1) ? ($past(index_rand_offset, 1) + $past(buf_count, 1)) : $past(buf_count, 1)) &&
  buf_rdptr_reg_1 == 22'((((($past(butterfly_ready_in, 1) || ($past(buf0_valid_in, 1) && ($past(read_state, 1) == CtReadBuf))) || ($past(read_state, 1) == CtReadExec)) || ($past(read_state, 1) == CtReadExecwait)) ? (24'(({ 2'h0, { $past(buf_rdptr_reg_1, 1) }[21:2]} )) | ({ { 24'(({ $past(shuffle_en_in, 1) } ? ({ $past(index_rand_offset, 1) } + { $past(buf_count, 1) }) : { $past(buf_count, 1) })) }[3:0], 20'd0} )) : 24'd0)) &&
  buf_wren_out == ($past(buf_count, 1) < 2'd3) &&
  chunk_count_reg_1 == (((($past(butterfly_ready_in, 1) || ($past(buf0_valid_in, 1) && ($past(read_state, 1) == CtReadBuf))) || ($past(read_state, 1) == CtReadExec)) || ($past(read_state, 1) == CtReadExecwait)) ? ({ { 44'({ $past(chunk_count_in, 1) }) }[3:0], { $past(chunk_count_reg_1, 1) }[43:4]} ) : $past(chunk_count_reg_1, 1)) &&
  index_rand_offset == ($past(latch_index_rand_offset_port, 1) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  masking_en_ctrl_out == 0 &&
  mem_read_req_port == $past(mem_read_req_port_3_i, 1) &&
  ntt_passthrough_out == ($past(mlkem_in, 1) && ($past(rounds_count_in, 1) == 3'd3)) &&
  opcode_port == 3'd0 &&
  pw_rden_out == 0 &&
  pw_wren_out == 0 &&
  rd_valid_count == (((($past(read_state, 1) == CtReadIdle) || ($past(read_state, 1) == CtReadStage)) || ($past(buf0_valid_in, 1) && ($past(rd_valid_count, 1) > 7'd64))) ? 7'd0 : ($past(buf0_valid_in, 1) ? (7'd4 + $past(rd_valid_count, 1)) : $past(rd_valid_count, 1))) &&
  twiddle_addr_reg_out == 7'(($past(shuffle_en_in, 1) ? ({ 57'd0, $past(twiddle_rand_offset_0_i, 1)} ) : (($past(twiddle_addr_reg, 1) == $past(twiddle_end_addr_0_i, 1)) ? 64'd0 : 7'((64'd1 + ({ 57'd0, $past(twiddle_addr_reg, 1)} ))))));
endproperty
read_read_exec_wait_to_read_exec_wait_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) read_read_exec_wait_to_read_exec_wait_p);


property read_read_exec_wait_to_read_stage_p;
  read_exec_wait &&
  (rd_valid_count == 7'h40) &&
  (buf_count == 2'd3)
|->
  ##1
  read_stage &&
  bf_enable_out == 1 &&
  buf_count == (($past(buf0_valid_in, 1) || (($past(buf_count, 1) > 2'd0) && ($past(buf_count, 1) < 2'd3))) ? (2'd1 + $past(buf_count, 1)) : 2'd0) &&
  buf_rden_out == 1 &&
  buf_rdptr_f_out == ($past(shuffle_en_in, 1) ? ($past(index_rand_offset, 1) + $past(buf_count, 1)) : $past(buf_count, 1)) &&
  buf_rdptr_reg_1 == 22'((((($past(butterfly_ready_in, 1) || ($past(buf0_valid_in, 1) && ($past(read_state, 1) == CtReadBuf))) || ($past(read_state, 1) == CtReadExec)) || ($past(read_state, 1) == CtReadExecwait)) ? (24'(({ 2'h0, { $past(buf_rdptr_reg_1, 1) }[21:2]} )) | ({ { 24'(({ $past(shuffle_en_in, 1) } ? ({ $past(index_rand_offset, 1) } + { $past(buf_count, 1) }) : { $past(buf_count, 1) })) }[3:0], 20'd0} )) : 24'd0)) &&
  buf_wren_out == ($past(buf_count, 1) < 2'd3) &&
  chunk_count_reg_1 == (((($past(butterfly_ready_in, 1) || ($past(buf0_valid_in, 1) && ($past(read_state, 1) == CtReadBuf))) || ($past(read_state, 1) == CtReadExec)) || ($past(read_state, 1) == CtReadExecwait)) ? ({ { 44'({ $past(chunk_count_in, 1) }) }[3:0], { $past(chunk_count_reg_1, 1) }[43:4]} ) : $past(chunk_count_reg_1, 1)) &&
  index_rand_offset == ($past(latch_index_rand_offset_port, 1) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  masking_en_ctrl_out == 0 &&
  mem_read_req_port == $past(mem_read_req_port_3_i, 1) &&
  ntt_passthrough_out == ($past(mlkem_in, 1) && ($past(rounds_count_in, 1) == 3'd3)) &&
  opcode_port == 3'd0 &&
  pw_rden_out == 0 &&
  pw_wren_out == 0 &&
  rd_valid_count == (((($past(read_state, 1) == CtReadIdle) || ($past(read_state, 1) == CtReadStage)) || ($past(buf0_valid_in, 1) && ($past(rd_valid_count, 1) > 7'd64))) ? 7'd0 : ($past(buf0_valid_in, 1) ? (7'd4 + $past(rd_valid_count, 1)) : $past(rd_valid_count, 1))) &&
  twiddle_addr_reg_out == 7'(($past(shuffle_en_in, 1) ? ({ 57'd0, $past(twiddle_rand_offset_0_i, 1)} ) : (($past(twiddle_addr_reg, 1) == $past(twiddle_end_addr_0_i, 1)) ? 64'd0 : 7'((64'd1 + ({ 57'd0, $past(twiddle_addr_reg, 1)} ))))));
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
  buf_rdptr_reg_1 == 22'((((($past(butterfly_ready_in, 1) || ($past(buf0_valid_in, 1) && ($past(read_state, 1) == CtReadBuf))) || ($past(read_state, 1) == CtReadExec)) || ($past(read_state, 1) == CtReadExecwait)) ? (24'(({ 2'h0, { $past(buf_rdptr_reg_1, 1) }[21:2]} )) | ({ { 24'(({ $past(shuffle_en_in, 1) } ? ({ $past(index_rand_offset, 1) } + { $past(buf_count, 1) }) : { $past(buf_count, 1) })) }[3:0], 20'd0} )) : 24'd0)) &&
  buf_wren_out == 0 &&
  chunk_count_reg_1 == (((($past(butterfly_ready_in, 1) || ($past(buf0_valid_in, 1) && ($past(read_state, 1) == CtReadBuf))) || ($past(read_state, 1) == CtReadExec)) || ($past(read_state, 1) == CtReadExecwait)) ? ({ { 44'({ $past(chunk_count, 1) }) }[3:0], { $past(chunk_count_reg_1, 1) }[43:4]} ) : $past(chunk_count_reg_1, 1)) &&
  index_rand_offset == ($past(latch_index_rand_offset_port, 1) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  masking_en_ctrl_out == 0 &&
  mem_read_req_port == $past(mem_read_req_port_1_i, 1) &&
  ntt_passthrough_out == ($past(mlkem_in, 1) && ($past(rounds_count_in, 1) == 3'd3)) &&
  opcode_port == 3'd0 &&
  pw_rden_out == 0 &&
  pw_wren_out == 0 &&
  rd_valid_count == (((($past(read_state, 1) == CtReadIdle) || ($past(read_state, 1) == CtReadStage)) || ($past(buf0_valid_in, 1) && ($past(rd_valid_count, 1) > 7'd64))) ? 7'd0 : ($past(buf0_valid_in, 1) ? (7'd4 + $past(rd_valid_count, 1)) : $past(rd_valid_count, 1))) &&
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
  buf_rdptr_reg_1 == 22'((((($past(butterfly_ready_in, 1) || ($past(buf0_valid_in, 1) && ($past(read_state, 1) == CtReadBuf))) || ($past(read_state, 1) == CtReadExec)) || ($past(read_state, 1) == CtReadExecwait)) ? (24'(({ 2'h0, { $past(buf_rdptr_reg_1, 1) }[21:2]} )) | ({ { 24'(({ $past(shuffle_en_in, 1) } ? ({ $past(index_rand_offset, 1) } + { $past(buf_count, 1) }) : { $past(buf_count, 1) })) }[3:0], 20'd0} )) : 24'd0)) &&
  buf_wren_out == 0 &&
  chunk_count_reg_1 == (((($past(butterfly_ready_in, 1) || ($past(buf0_valid_in, 1) && ($past(read_state, 1) == CtReadBuf))) || ($past(read_state, 1) == CtReadExec)) || ($past(read_state, 1) == CtReadExecwait)) ? ({ { 44'({ $past(chunk_count, 1) }) }[3:0], { $past(chunk_count_reg_1, 1) }[43:4]} ) : $past(chunk_count_reg_1, 1)) &&
  index_rand_offset == ($past(latch_index_rand_offset_port, 1) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  masking_en_ctrl_out == 0 &&
  mem_read_req_port == $past(mem_read_req_port_1_i, 1) &&
  ntt_passthrough_out == ($past(mlkem_in, 1) && ($past(rounds_count_in, 1) == 3'd3)) &&
  opcode_port == 3'd0 &&
  pw_rden_out == 0 &&
  pw_wren_out == 0 &&
  rd_valid_count == (((($past(read_state, 1) == CtReadIdle) || ($past(read_state, 1) == CtReadStage)) || ($past(buf0_valid_in, 1) && ($past(rd_valid_count, 1) > 7'd64))) ? 7'd0 : ($past(buf0_valid_in, 1) ? (7'd4 + $past(rd_valid_count, 1)) : $past(rd_valid_count, 1))) &&
  twiddle_addr_reg_out == 7'd0;
endproperty
read_read_idle_to_read_stage_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) read_read_idle_to_read_stage_p);


property read_read_stage_to_read_buf_p;
  read_stage &&
  wr_stage_set &&
  !ntt_done_read
|->
  ##1
  read_buf &&
  bf_enable_out == 0 &&
  buf_count == (($past(buf0_valid_in, 1) || (($past(buf_count, 1) > 2'd0) && ($past(buf_count, 1) < 2'd3))) ? (2'd1 + $past(buf_count, 1)) : 2'd0) &&
  buf_rden_out == 0 &&
  buf_rdptr_f_out == ($past(shuffle_en_in, 1) ? ($past(index_rand_offset, 1) + $past(buf_count, 1)) : $past(buf_count, 1)) &&
  buf_rdptr_reg_1 == 22'((((($past(butterfly_ready_in, 1) || ($past(buf0_valid_in, 1) && ($past(read_state, 1) == CtReadBuf))) || ($past(read_state, 1) == CtReadExec)) || ($past(read_state, 1) == CtReadExecwait)) ? (24'(({ 2'h0, { $past(buf_rdptr_reg_1, 1) }[21:2]} )) | ({ { 24'(({ $past(shuffle_en_in, 1) } ? ({ $past(index_rand_offset, 1) } + { $past(buf_count, 1) }) : { $past(buf_count, 1) })) }[3:0], 20'd0} )) : 24'd0)) &&
  buf_wren_out == 0 &&
  chunk_count_reg_1 == (((($past(butterfly_ready_in, 1) || ($past(buf0_valid_in, 1) && ($past(read_state, 1) == CtReadBuf))) || ($past(read_state, 1) == CtReadExec)) || ($past(read_state, 1) == CtReadExecwait)) ? ({ { 44'({ $past(chunk_count_in, 1) }) }[3:0], { $past(chunk_count_reg_1, 1) }[43:4]} ) : $past(chunk_count_reg_1, 1)) &&
  index_rand_offset == ($past(latch_index_rand_offset_port, 1) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  masking_en_ctrl_out == 0 &&
  mem_read_req_port == $past(mem_read_req_port_1_i, 1) &&
  ntt_passthrough_out == ($past(mlkem_in, 1) && ($past(rounds_count_in, 1) == 3'd3)) &&
  opcode_port == 3'd0 &&
  pw_rden_out == 0 &&
  pw_wren_out == 0 &&
  rd_valid_count == (((($past(read_state, 1) == CtReadIdle) || ($past(read_state, 1) == CtReadStage)) || ($past(buf0_valid_in, 1) && ($past(rd_valid_count, 1) > 7'd64))) ? 7'd0 : ($past(buf0_valid_in, 1) ? (7'd4 + $past(rd_valid_count, 1)) : $past(rd_valid_count, 1))) &&
  twiddle_addr_reg_out == ($past(butterfly_ready_in, 1) ? $past(twiddle_addr_reg, 1) : 7'd0);
endproperty
read_read_stage_to_read_buf_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) read_read_stage_to_read_buf_p);


property read_read_stage_to_read_idle_p;
  read_stage &&
  ntt_done_read
|->
  ##1
  read_idle &&
  bf_enable_out == 0 &&
  buf_count == (($past(buf0_valid_in, 1) || (($past(buf_count, 1) > 2'd0) && ($past(buf_count, 1) < 2'd3))) ? (2'd1 + $past(buf_count, 1)) : 2'd0) &&
  buf_rden_out == 0 &&
  buf_rdptr_f_out == ($past(shuffle_en_in, 1) ? ($past(index_rand_offset, 1) + $past(buf_count, 1)) : $past(buf_count, 1)) &&
  buf_rdptr_reg_1 == 22'((((($past(butterfly_ready_in, 1) || ($past(buf0_valid_in, 1) && ($past(read_state, 1) == CtReadBuf))) || ($past(read_state, 1) == CtReadExec)) || ($past(read_state, 1) == CtReadExecwait)) ? (24'(({ 2'h0, { $past(buf_rdptr_reg_1, 1) }[21:2]} )) | ({ { 24'(({ $past(shuffle_en_in, 1) } ? ({ $past(index_rand_offset, 1) } + { $past(buf_count, 1) }) : { $past(buf_count, 1) })) }[3:0], 20'd0} )) : 24'd0)) &&
  buf_wren_out == 0 &&
  chunk_count_reg_1 == (((($past(butterfly_ready_in, 1) || ($past(buf0_valid_in, 1) && ($past(read_state, 1) == CtReadBuf))) || ($past(read_state, 1) == CtReadExec)) || ($past(read_state, 1) == CtReadExecwait)) ? ({ { 44'({ $past(chunk_count_in, 1) }) }[3:0], { $past(chunk_count_reg_1, 1) }[43:4]} ) : $past(chunk_count_reg_1, 1)) &&
  index_rand_offset == ($past(latch_index_rand_offset_port, 1) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  masking_en_ctrl_out == 0 &&
  mem_read_req_port == $past(mem_read_req_port_1_i, 1) &&
  ntt_passthrough_out == ($past(mlkem_in, 1) && ($past(rounds_count_in, 1) == 3'd3)) &&
  opcode_port == 3'd0 &&
  pw_rden_out == 0 &&
  pw_wren_out == 0 &&
  rd_valid_count == (((($past(read_state, 1) == CtReadIdle) || ($past(read_state, 1) == CtReadStage)) || ($past(buf0_valid_in, 1) && ($past(rd_valid_count, 1) > 7'd64))) ? 7'd0 : ($past(buf0_valid_in, 1) ? (7'd4 + $past(rd_valid_count, 1)) : $past(rd_valid_count, 1))) &&
  twiddle_addr_reg_out == ($past(butterfly_ready_in, 1) ? $past(twiddle_addr_reg, 1) : 7'd0);
endproperty
read_read_stage_to_read_idle_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) read_read_stage_to_read_idle_p);


property read_read_stage_to_read_stage_p;
  read_stage &&
  !wr_stage_set &&
  !ntt_done_read
|->
  ##1
  read_stage &&
  bf_enable_out == 0 &&
  buf_count == (($past(buf0_valid_in, 1) || (($past(buf_count, 1) > 2'd0) && ($past(buf_count, 1) < 2'd3))) ? (2'd1 + $past(buf_count, 1)) : 2'd0) &&
  buf_rden_out == 0 &&
  buf_rdptr_f_out == ($past(shuffle_en_in, 1) ? ($past(index_rand_offset, 1) + $past(buf_count, 1)) : $past(buf_count, 1)) &&
  buf_rdptr_reg_1 == 22'((((($past(butterfly_ready_in, 1) || ($past(buf0_valid_in, 1) && ($past(read_state, 1) == CtReadBuf))) || ($past(read_state, 1) == CtReadExec)) || ($past(read_state, 1) == CtReadExecwait)) ? (24'(({ 2'h0, { $past(buf_rdptr_reg_1, 1) }[21:2]} )) | ({ { 24'(({ $past(shuffle_en_in, 1) } ? ({ $past(index_rand_offset, 1) } + { $past(buf_count, 1) }) : { $past(buf_count, 1) })) }[3:0], 20'd0} )) : 24'd0)) &&
  buf_wren_out == 0 &&
  chunk_count_reg_1 == (((($past(butterfly_ready_in, 1) || ($past(buf0_valid_in, 1) && ($past(read_state, 1) == CtReadBuf))) || ($past(read_state, 1) == CtReadExec)) || ($past(read_state, 1) == CtReadExecwait)) ? ({ { 44'({ $past(chunk_count_in, 1) }) }[3:0], { $past(chunk_count_reg_1, 1) }[43:4]} ) : $past(chunk_count_reg_1, 1)) &&
  index_rand_offset == ($past(latch_index_rand_offset_port, 1) ? { $past(random_in, 1) }[1:0] : $past(index_rand_offset, 1)) &&
  masking_en_ctrl_out == 0 &&
  mem_read_req_port == $past(mem_read_req_port_1_i, 1) &&
  ntt_passthrough_out == ($past(mlkem_in, 1) && (rounds_count_in == 3'd3)) &&
  opcode_port == 3'd0 &&
  pw_rden_out == 0 &&
  pw_wren_out == 0 &&
  rd_valid_count == (((($past(read_state, 1) == CtReadIdle) || ($past(read_state, 1) == CtReadStage)) || ($past(buf0_valid_in, 1) && ($past(rd_valid_count, 1) > 7'd64))) ? 7'd0 : ($past(buf0_valid_in, 1) ? (7'd4 + $past(rd_valid_count, 1)) : $past(rd_valid_count, 1))) &&
  twiddle_addr_reg_out == ($past(butterfly_ready_in, 1) ? $past(twiddle_addr_reg, 1) : 7'd0);
endproperty
read_read_stage_to_read_stage_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) read_read_stage_to_read_stage_p);


property write_write_idle_to_write_idle_p;
  write_idle &&
  !ntt_enable_in
|->
  ##1
  write_idle &&
  chunk_count_write == (($past(buf_count, 1) == 2'd3) ? 4'((64'd1 + ({ 60'h0, $past(chunk_count_write, 1)} ))) : ({ 60'h0, $past(chunk_count_write, 1)} )) &&
  $stable(chunk_rand_offset_write) &&
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
  mem_write_req_port == $past(mem_write_req_port_0_i, 1) &&
  rounds_count_out == 3'd0 &&
  wr_valid_count == (($past(write_state, 1) == CtWriteMem) ? ($past(butterfly_ready_in, 1) ? (7'd1 + $past(wr_valid_count, 1)) : $past(wr_valid_count, 1)) : 7'd0);
endproperty
write_write_idle_to_write_stage_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) write_write_idle_to_write_stage_p);


property write_write_mem_to_write_mem_p;
  write_mem &&
  (wr_valid_count != 7'h3F)
|->
  ##1 ($stable(rounds_count_out)) and
  ##1
  write_mem &&
  chunk_count_write == (($past(buf_count, 1) == 2'd3) ? 4'((64'd1 + ({ 60'h0, $past(chunk_count_write, 1)} ))) : ({ 60'h0, $past(chunk_count_write, 1)} )) &&
  $stable(chunk_rand_offset_write) &&
  mem_write_req_port == $past(mem_write_req_port_2_i, 1) &&
  wr_valid_count == (($past(write_state, 1) == CtWriteMem) ? ($past(butterfly_ready_in, 1) ? (7'd1 + $past(wr_valid_count, 1)) : $past(wr_valid_count, 1)) : 7'd0);
endproperty
write_write_mem_to_write_mem_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) write_write_mem_to_write_mem_p);


property write_write_mem_to_write_stage_p;
  write_mem &&
  (wr_valid_count == 7'h3F)
|->
  ##1
  write_stage &&
  chunk_count_write == { $past(random_in, 1) }[5:2] &&
  chunk_rand_offset_write == { $past(random_in, 1) }[5:2] &&
  mem_write_req_port == $past(mem_write_req_port_2_i, 1) &&
  rounds_count_out == (($past(rounds_count_write, 1) < 3'd4) ? (3'd1 + $past(rounds_count_write, 1)) : 3'd0) &&
  wr_valid_count == (($past(write_state, 1) == CtWriteMem) ? ($past(butterfly_ready_in, 1) ? (7'd1 + $past(wr_valid_count, 1)) : $past(wr_valid_count, 1)) : 7'd0);
endproperty
write_write_mem_to_write_stage_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) write_write_mem_to_write_stage_p);


property write_write_stage_to_write_idle_p;
  write_stage &&
  ntt_done
|->
  ##1
  write_idle &&
  chunk_count_write == (($past(buf_count, 1) == 2'd3) ? 4'((64'd1 + ({ 60'h0, $past(chunk_count_write, 1)} ))) : ({ 60'h0, $past(chunk_count_write, 1)} )) &&
  $stable(chunk_rand_offset_write) &&
  mem_write_req_port == $past(mem_write_req_port_1_i, 1) &&
  rounds_count_out == 3'd0 &&
  wr_valid_count == (($past(write_state, 1) == CtWriteMem) ? ($past(butterfly_ready_in, 1) ? (7'd1 + $past(wr_valid_count, 1)) : $past(wr_valid_count, 1)) : 7'd0);
endproperty
write_write_stage_to_write_idle_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) write_write_stage_to_write_idle_p);


property write_write_stage_to_write_mem_p;
  write_stage &&
  !ntt_done
|->
  ##1 ($stable(rounds_count_out)) and
  ##1
  write_mem &&
  chunk_count_write == (($past(buf_count, 1) == 2'd3) ? 4'((64'd1 + ({ 60'h0, $past(chunk_count_write, 1)} ))) : ({ 60'h0, $past(chunk_count_write, 1)} )) &&
  $stable(chunk_rand_offset_write) &&
  mem_write_req_port == $past(mem_write_req_port_1_i, 1) &&
  wr_valid_count == (($past(write_state, 1) == CtWriteMem) ? ($past(butterfly_ready_in, 1) ? (7'd1 + $past(wr_valid_count, 1)) : $past(wr_valid_count, 1)) : 7'd0);
endproperty
write_write_stage_to_write_mem_a: assert property (disable iff(!rst_n || ntt_ctrl.zeroize) write_write_stage_to_write_mem_p);

property read_read_idle_eventually_left_p;
  read_idle
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


property write_write_idle_eventually_left_p;
  write_idle
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
