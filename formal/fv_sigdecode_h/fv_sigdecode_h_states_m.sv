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
// | Created on 10.03.2025 at 09:40                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


module fv_sigdecode_h_states_m
  import fv_sigdecode_h_states_pkg::*;
  import abr_params_pkg::*;
  import fv_sigdecode_h_functions::*;
  import sigdecode_h_defines_pkg::*;
(
  input logic rst,
  input logic clk,

  // Ports
  input logic start_port,

  input logic start_write_fsm,

  input logic unsigned [13:0] dest_address_port,

  input a_unsigned_8_83 read_data_port,

  input st_Request write_request_port,

  input logic unsigned [95:0] write_data_port,

  input logic done_port,

  input logic error_port,

  // Registers
  input logic OR_remaining_encoded_h_i,
  input logic unsigned [255:0] bitmap,
  input logic unsigned [7:0] bitmap_ptr,
  input logic unsigned [3:0] curr_poly_map,
  input logic unsigned [13:0] dest_address,
  input logic error,
  input logic first_hint,
  input a_unsigned_8_4 hint,
  input logic hint_ok,
  input logic hint_rd_en_f,
  input logic unsigned [7:0] hintsum,
  input logic unsigned [7:0] hintsum_curr_poly,
  input logic hintsum_max_error_i,
  input logic unsigned [7:0] hintsum_prev_poly,
  input logic unsigned [13:0] mem_wr_addr,
  input logic unsigned [3:0] poly_count,
  input logic unsigned [7:0] prev_hint,
  input logic unsigned [6:0] rd_ptr,
  input a_unsigned_8_83 read_data,
  input e_ReadStatesType read_state,
  input logic unsigned [7:0] rem_hintsum,
  input e_WriteStatesType write_state,

  // States
  input logic rIDLE,
  input logic rINIT,
  input logic rHINTSUM,
  input logic rEXEC,
  input logic wIDLE,
  input logic wINIT,
  input logic wMEM
);


default clocking default_clk @(posedge clk); endclocking

eight_polys: cover property (disable iff(rst) sigdecode_h.poly_count == 8);
// poly_eight_incr: cover property (disable iff(rst) sigdecode_h.poly_count == 8 && sigdecode_h.sdh_ctrl_inst.incr_poly); // unreachable

logic fv_err_reg;

always_ff @(posedge clk, posedge rst) begin
  if(rst) begin
    fv_err_reg <= '0;
  end
  else begin
    if(error_port) begin
      fv_err_reg <= '1;
    end
  end
end

a_unsigned_8_4 hint_0_i;
assign hint_0_i = '{
  0: 8'd0,
  1: 8'd0,
  2: 8'd0,
  3: 8'd0
};

a_unsigned_8_83 read_data_0_i;
assign read_data_0_i = '{
  0: 8'd0,
  1: 8'd0,
  2: 8'd0,
  3: 8'd0,
  4: 8'd0,
  5: 8'd0,
  6: 8'd0,
  7: 8'd0,
  8: 8'd0,
  9: 8'd0,
  10: 8'd0,
  11: 8'd0,
  12: 8'd0,
  13: 8'd0,
  14: 8'd0,
  15: 8'd0,
  16: 8'd0,
  17: 8'd0,
  18: 8'd0,
  19: 8'd0,
  20: 8'd0,
  21: 8'd0,
  22: 8'd0,
  23: 8'd0,
  24: 8'd0,
  25: 8'd0,
  26: 8'd0,
  27: 8'd0,
  28: 8'd0,
  29: 8'd0,
  30: 8'd0,
  31: 8'd0,
  32: 8'd0,
  33: 8'd0,
  34: 8'd0,
  35: 8'd0,
  36: 8'd0,
  37: 8'd0,
  38: 8'd0,
  39: 8'd0,
  40: 8'd0,
  41: 8'd0,
  42: 8'd0,
  43: 8'd0,
  44: 8'd0,
  45: 8'd0,
  46: 8'd0,
  47: 8'd0,
  48: 8'd0,
  49: 8'd0,
  50: 8'd0,
  51: 8'd0,
  52: 8'd0,
  53: 8'd0,
  54: 8'd0,
  55: 8'd0,
  56: 8'd0,
  57: 8'd0,
  58: 8'd0,
  59: 8'd0,
  60: 8'd0,
  61: 8'd0,
  62: 8'd0,
  63: 8'd0,
  64: 8'd0,
  65: 8'd0,
  66: 8'd0,
  67: 8'd0,
  68: 8'd0,
  69: 8'd0,
  70: 8'd0,
  71: 8'd0,
  72: 8'd0,
  73: 8'd0,
  74: 8'd0,
  75: 8'd0,
  76: 8'd0,
  77: 8'd0,
  78: 8'd0,
  79: 8'd0,
  80: 8'd0,
  81: 8'd0,
  82: 8'd0
};

st_Request write_request_0_i;
assign write_request_0_i = '{
  address: 14'd0,
  idle: 0,
  read: 0,
  write: 0
};

logic upd_hint_ok_0_i;
assign upd_hint_ok_0_i = upd_hint_ok(curr_poly_map, hint, 8'd0, first_hint);

logic unsigned [255:0] upd_bitmap_0_i;
assign upd_bitmap_0_i = upd_bitmap(curr_poly_map, hint, bitmap);

logic upd_hint_ok_1_i;
assign upd_hint_ok_1_i = upd_hint_ok(curr_poly_map, hint, prev_hint, first_hint);

logic unsigned [7:0] upd_rem_hintsum_0_i;
assign upd_rem_hintsum_0_i = upd_rem_hintsum(rem_hintsum);

a_unsigned_8_4 hint_1_i;
assign hint_1_i = '{
  0: read_data[7'((rd_ptr + 64'd0))],
  1: read_data[7'((rd_ptr + 64'd1))],
  2: read_data[7'((rd_ptr + 64'd2))],
  3: read_data[7'((rd_ptr + 64'd3))]
};

logic upd_remaining_encoded_h_i_0_i;
assign upd_remaining_encoded_h_i_0_i = upd_remaining_encoded_h_i(read_data_port);

logic upd_hintsum_max_error_i_0_i;
assign upd_hintsum_max_error_i_0_i = upd_hintsum_max_error_i(read_data_port);

st_Request write_request_1_i;
assign write_request_1_i = '{
  address: 14'd0,
  idle: 1,
  read: 0,
  write: 0
};

logic unsigned [95:0] upd_write_data_0_i;
assign upd_write_data_0_i = upd_write_data(bitmap, bitmap_ptr);

st_Request write_request_2_i;
assign write_request_2_i = '{
  address: mem_wr_addr,
  idle: 1,
  read: 0,
  write: 0
};

st_Request write_request_3_i;
assign write_request_3_i = '{
  address: mem_wr_addr,
  idle: 0,
  read: 0,
  write: 1
};


sequence reset_sequence;
  rst ##1 !rst;
endsequence


property read_reset_p;
  reset_sequence |->
  rIDLE &&
  bitmap == 256'd0 &&
  curr_poly_map == 4'd0 &&
  first_hint == 0 &&
  hint == hint_0_i &&
  hint_ok == 1 &&
  hint_rd_en_f == 0 &&
  hintsum == 8'd0 &&
  hintsum_curr_poly == 8'd0 &&
  hintsum_prev_poly == 8'd0 &&
  prev_hint == 8'd0 &&
  rd_ptr == 7'd0 &&
  rem_hintsum == 8'd0;
endproperty
read_reset_a: assert property (read_reset_p);


property write_reset_p;
  reset_sequence |->
  wIDLE &&
  OR_remaining_encoded_h_i == upd_remaining_encoded_h_i_0_i &&
  bitmap_ptr == 8'd0 &&
  done_port == 1 &&
  error_port == 0 &&
  hintsum_max_error_i == upd_hintsum_max_error_i_0_i &&
  mem_wr_addr == 14'd0 &&
  poly_count == 4'd0 &&
  write_data_port == 96'd0 &&
  write_request_port == write_request_1_i;
endproperty
write_reset_a: assert property (write_reset_p);


property read_rEXEC_to_rEXEC_p;
  rEXEC &&
  !error &&
  (rem_hintsum != 8'd0)
|->
  ##1
  rEXEC &&
  bitmap == $past(upd_bitmap_0_i, 1) &&
  curr_poly_map == 4'((($past(rem_hintsum, 1) >= 8'd4) ? 8'd15 : (($past(rem_hintsum, 1) == 8'd3) ? 8'd7 : (($past(rem_hintsum, 1) == 8'd2) ? 8'd3 : 4'($past(rem_hintsum, 1)))))) &&
  first_hint == ((!$past(error, 1) && ($past(rem_hintsum, 1) > 8'd0)) && !$past(hint_rd_en_f, 1)) &&
  hint == $past(hint_1_i, 1) &&
  hint_ok == $past(upd_hint_ok_1_i, 1) &&
  hint_rd_en_f == (!$past(error, 1) && ($past(rem_hintsum, 1) != 8'd0)) &&
  hintsum == (($past(poly_count, 1) == 4'd8) ? 8'd0 : $past(read_data[(7'd75 + 7'(poly_count))], 1)) &&
  hintsum_curr_poly == ((($past(poly_count, 1) == 4'd8) ? 8'd0 : $past(read_data[(7'd75 + 7'(poly_count))], 1)) - $past(hintsum, 1)) &&
  hintsum_prev_poly == $past(hintsum, 1) &&
  prev_hint == $past(hint[64'd3], 1) &&
  rd_ptr == (($past(rem_hintsum, 1) >= 8'd4) ? 7'((64'd4 + ({ 57'h0, $past(rd_ptr, 1)} ))) : 7'((({ 1'h0, $past(rd_ptr, 1)} ) + $past(rem_hintsum, 1)))) &&
  rem_hintsum == $past(upd_rem_hintsum_0_i, 1);
endproperty
read_rEXEC_to_rEXEC_a: assert property (disable iff(rst || fv_err_reg) read_rEXEC_to_rEXEC_p);


property read_rEXEC_to_rIDLE_p;
  rEXEC &&
  (error || ((rem_hintsum == 8'd0) && (poly_count == 4'd7)))
|->
  ##1
  rIDLE &&
  bitmap == ((($past(write_state, 1) == WriteMem) && ($past(error, 1) || ({ $past(mem_wr_addr, 1) }[5:0] == 63))) ? 256'd0 : $past(upd_bitmap_0_i, 1)) &&
  curr_poly_map == 4'((($past(rem_hintsum, 1) >= 8'd4) ? 8'd15 : (($past(rem_hintsum, 1) == 8'd3) ? 8'd7 : (($past(rem_hintsum, 1) == 8'd2) ? 8'd3 : 4'($past(rem_hintsum, 1)))))) &&
  first_hint == ((!$past(error, 1) && ($past(rem_hintsum, 1) > 8'd0)) && !$past(hint_rd_en_f, 1)) &&
  hint == hint_0_i &&
  hint_ok == $past(upd_hint_ok_1_i, 1) &&
  hint_rd_en_f == (!$past(error, 1) && ($past(rem_hintsum, 1) != 8'd0)) &&
  $stable(hintsum) &&
  $stable(hintsum_curr_poly) &&
  $stable(hintsum_prev_poly) &&
  prev_hint == $past(hint[64'd3], 1) &&
  rd_ptr == (($past(rem_hintsum, 1) >= 8'd4) ? 7'((64'd4 + ({ 57'h0, $past(rd_ptr, 1)} ))) : 7'((({ 1'h0, $past(rd_ptr, 1)} ) + $past(rem_hintsum, 1)))) &&
  rem_hintsum == $past(upd_rem_hintsum_0_i, 1);
endproperty
read_rEXEC_to_rIDLE_a: assert property (disable iff(rst) read_rEXEC_to_rIDLE_p);


property read_rEXEC_to_rINIT_p;
  rEXEC &&
  !error &&
  (rem_hintsum == 8'd0) &&
  (poly_count != 4'd7)
|->
  ##1
  rINIT &&
  bitmap == $past(upd_bitmap_0_i, 1) &&
  curr_poly_map == 4'($past(rem_hintsum, 1)) &&
  first_hint == ((!$past(error, 1) && ($past(rem_hintsum, 1) > 8'd0)) && !$past(hint_rd_en_f, 1)) &&
  hint == hint_0_i &&
  hint_ok == $past(upd_hint_ok_1_i, 1) &&
  hint_rd_en_f == (!$past(error, 1) && ($past(rem_hintsum, 1) != 8'd0)) &&
  $stable(hintsum) &&
  hintsum_curr_poly == ($past(hintsum, 1) - $past(hintsum_prev_poly, 1)) &&
  $stable(hintsum_prev_poly) &&
  prev_hint == $past(hint[64'd3], 1) &&
  $stable(rd_ptr) &&
  rem_hintsum == $past(upd_rem_hintsum_0_i, 1);
endproperty
read_rEXEC_to_rINIT_a: assert property (disable iff(rst || fv_err_reg) read_rEXEC_to_rINIT_p);


property read_rHINTSUM_to_rEXEC_p;
  rHINTSUM
|->
  ##1
  rEXEC &&
  $stable(bitmap) &&
  curr_poly_map == 4'd0 &&
  $stable(first_hint) &&
  $stable(hint) &&
  $stable(hint_ok) &&
  $stable(hint_rd_en_f) &&
  hintsum == (($past(poly_count, 1) == 4'd8) ? 8'd0 : $past(read_data[(7'd75 + 7'(poly_count))], 1)) &&
  hintsum_curr_poly == ((($past(poly_count, 1) == 4'd8) ? 8'd0 : $past(read_data[(7'd75 + 7'(poly_count))], 1)) - $past(hintsum, 1)) &&
  hintsum_prev_poly == $past(hintsum, 1) &&
  $stable(prev_hint) &&
  $stable(rd_ptr) &&
  rem_hintsum == $past(hintsum_curr_poly, 1);
endproperty
read_rHINTSUM_to_rEXEC_a: assert property (disable iff(rst || fv_err_reg) read_rHINTSUM_to_rEXEC_p);


property read_rIDLE_to_rIDLE_p;
  rIDLE &&
  !start_port
|->
  ##1
  rIDLE &&
  bitmap == ((($past(write_state, 1) == WriteMem) && ($past(error, 1) || ({ $past(mem_wr_addr, 1) }[5:0] == 63))) ? 256'd0 : $past(bitmap, 1)) &&
  $stable(curr_poly_map) &&
  $stable(first_hint) &&
  $stable(hint) &&
  hint_ok == 1 &&
  $stable(hint_rd_en_f) &&
  hintsum == ((($past(poly_count, 1) == 4'd8) || ($past(write_state, 1) == WriteIdle)) ? 8'd0 : $past(read_data[(7'd75 + 7'(poly_count))], 1)) &&
  hintsum_curr_poly == (((($past(poly_count, 1) == 4'd8) || ($past(write_state, 1) == WriteIdle)) ? 8'd0 : $past(read_data[(7'd75 + 7'(poly_count))], 1)) - $past(hintsum, 1)) &&
  hintsum_prev_poly == $past(hintsum, 1) &&
  prev_hint == 8'd0 &&
  $stable(rd_ptr) &&
  $stable(rem_hintsum);
endproperty
read_rIDLE_to_rIDLE_a: assert property (disable iff(rst || fv_err_reg) read_rIDLE_to_rIDLE_p);


property read_rIDLE_to_rINIT_p;
  rIDLE &&
  start_port
|->
  ##1
  rINIT &&
  $stable(bitmap) &&
  $stable(curr_poly_map) &&
  $stable(first_hint) &&
  $stable(hint) &&
  hint_ok == 1 &&
  $stable(hint_rd_en_f) &&
  hintsum == 8'd0 &&
  $stable(hintsum_curr_poly) &&
  $stable(hintsum_prev_poly) &&
  prev_hint == 8'd0 &&
  $stable(rd_ptr) &&
  $stable(rem_hintsum);
endproperty
read_rIDLE_to_rINIT_a: assert property (disable iff(rst || fv_err_reg) read_rIDLE_to_rINIT_p);


property read_rINIT_to_rHINTSUM_p;
  rINIT &&
  !error &&
  (write_state == WriteInit)
|->
  ##1
  rHINTSUM &&
  $stable(bitmap) &&
  $stable(curr_poly_map) &&
  $stable(first_hint) &&
  $stable(hint) &&
  hint_ok == 1 &&
  $stable(hint_rd_en_f) &&
  hintsum == (($past(poly_count, 1) == 4'd8) ? 8'd0 : $past(read_data[(7'd75 + 7'(poly_count))], 1)) &&
  hintsum_curr_poly == ((($past(poly_count, 1) == 4'd8) ? 8'd0 : $past(read_data[(7'd75 + 7'(poly_count))], 1)) - $past(hintsum, 1)) &&
  hintsum_prev_poly == $past(hintsum, 1) &&
  prev_hint == 8'd0 &&
  $stable(rd_ptr) &&
  $stable(rem_hintsum);
endproperty
read_rINIT_to_rHINTSUM_a: assert property (disable iff(rst || fv_err_reg) read_rINIT_to_rHINTSUM_p);


property read_rINIT_to_rIDLE_p;
  rINIT &&
  error
|->
  ##1
  rIDLE &&
  bitmap == ((($past(write_state, 1) == WriteMem) && ($past(error, 1) || ({ $past(mem_wr_addr, 1) }[5:0] == 63))) ? 256'd0 : $past(bitmap, 1)) &&
  $stable(curr_poly_map) &&
  $stable(first_hint) &&
  $stable(hint) &&
  hint_ok == 1 &&
  $stable(hint_rd_en_f) &&
  $stable(hintsum) &&
  $stable(hintsum_curr_poly) &&
  $stable(hintsum_prev_poly) &&
  prev_hint == 8'd0 &&
  $stable(rd_ptr) &&
  $stable(rem_hintsum);
endproperty
read_rINIT_to_rIDLE_a: assert property (disable iff(rst) read_rINIT_to_rIDLE_p);


property read_rINIT_to_rINIT_p;
  rINIT &&
  !error &&
  (write_state != WriteInit)
|->
  ##1
  rINIT &&
  bitmap == ((($past(write_state, 1) == WriteMem) && ($past(error, 1) || ({ $past(mem_wr_addr, 1) }[5:0] == 63))) ? 256'd0 : $past(bitmap, 1)) &&
  $stable(curr_poly_map) &&
  $stable(first_hint) &&
  $stable(hint) &&
  hint_ok == $past(upd_hint_ok_0_i, 1) &&
  $stable(hint_rd_en_f) &&
  $stable(hintsum) &&
  $stable(hintsum_curr_poly) &&
  $stable(hintsum_prev_poly) &&
  prev_hint == 8'd0 &&
  $stable(rd_ptr) &&
  $stable(rem_hintsum);
endproperty
read_rINIT_to_rINIT_a: assert property (disable iff(rst || fv_err_reg) read_rINIT_to_rINIT_p);


property write_wIDLE_to_wIDLE_p;
  wIDLE &&
  !start_write_fsm
|->
  ##1 ($stable(error_port)) and
  ##1
  wIDLE &&
  OR_remaining_encoded_h_i == upd_remaining_encoded_h_i_0_i &&
  $stable(bitmap_ptr) &&
  done_port == (read_state == ReadIdle) &&
  hintsum_max_error_i == upd_hintsum_max_error_i_0_i &&
  mem_wr_addr == $past(dest_address_port, 1) &&
  $stable(poly_count) &&
  write_data_port == $past(upd_write_data_0_i, 1) &&
  write_request_port == $past(write_request_2_i, 1);
endproperty
write_wIDLE_to_wIDLE_a: assert property (disable iff(rst || fv_err_reg) write_wIDLE_to_wIDLE_p);


property write_wIDLE_to_wINIT_p;
  wIDLE &&
  start_write_fsm
|->
  ##1
  wINIT &&
  OR_remaining_encoded_h_i == $past(upd_remaining_encoded_h_i_0_i, 1) &&
  $stable(bitmap_ptr) &&
  done_port == 0 &&
  error_port == 0 &&
  hintsum_max_error_i == $past(upd_hintsum_max_error_i_0_i, 1) &&
  mem_wr_addr == $past(dest_address_port, 1) &&
  $stable(poly_count) &&
  write_data_port == $past(upd_write_data_0_i, 1) &&
  write_request_port == $past(write_request_2_i, 1);
endproperty
write_wIDLE_to_wINIT_a: assert property (disable iff(rst || fv_err_reg) write_wIDLE_to_wINIT_p);


property write_wINIT_to_wIDLE_p;
  wINIT &&
  error
|->
  ##1
  wIDLE &&
  OR_remaining_encoded_h_i == $past(upd_remaining_encoded_h_i_0_i, 1) &&
  $stable(bitmap_ptr) &&
  done_port == (read_state == ReadIdle) &&
  error_port == ((($past(upd_remaining_encoded_h_i_0_i, 1) || !$past(hint_ok, 1)) || $past(upd_hintsum_max_error_i_0_i, 1)) || ($past(hintsum, 1) < $past(hintsum_prev_poly, 1))) &&
  hintsum_max_error_i == $past(upd_hintsum_max_error_i_0_i, 1) &&
  $stable(mem_wr_addr) &&
  $stable(poly_count) &&
  write_data_port == $past(upd_write_data_0_i, 1) &&
  write_request_port == $past(write_request_2_i, 1);
endproperty
write_wINIT_to_wIDLE_a: assert property (disable iff(rst) write_wINIT_to_wIDLE_p);


property write_wINIT_to_wINIT_p;
  wINIT &&
  !error &&
  !hint_rd_en_f &&
  !((rem_hintsum == 8'd0) && (read_state == ReadExec))
|->
  ##1
  wINIT &&
  $stable(OR_remaining_encoded_h_i) &&
  $stable(bitmap_ptr) &&
  done_port == 0 &&
  error_port == ((($past(OR_remaining_encoded_h_i, 1) || !$past(hint_ok, 1)) || $past(hintsum_max_error_i, 1)) || ($past(hintsum, 1) < $past(hintsum_prev_poly, 1))) &&
  $stable(hintsum_max_error_i) &&
  $stable(mem_wr_addr) &&
  $stable(poly_count) &&
  write_data_port == $past(upd_write_data_0_i, 1) &&
  write_request_port == $past(write_request_2_i, 1);
endproperty
write_wINIT_to_wINIT_a: assert property (disable iff(rst || fv_err_reg) write_wINIT_to_wINIT_p);


property write_wINIT_to_wMEM_p;
  wINIT &&
  !error &&
  (hint_rd_en_f || ((rem_hintsum == 8'd0) && (read_state == ReadExec)))
|->
  ##1
  wMEM &&
  $stable(OR_remaining_encoded_h_i) &&
  $stable(bitmap_ptr) &&
  done_port == 0 &&
  error_port == ((($past(OR_remaining_encoded_h_i, 1) || !$past(hint_ok, 1)) || $past(hintsum_max_error_i, 1)) || ($past(hintsum, 1) < $past(hintsum_prev_poly, 1))) &&
  $stable(hintsum_max_error_i) &&
  $stable(mem_wr_addr) &&
  $stable(poly_count) &&
  write_data_port == $past(upd_write_data_0_i, 1) &&
  write_request_port == $past(write_request_2_i, 1);
endproperty
write_wINIT_to_wMEM_a: assert property (disable iff(rst || fv_err_reg) write_wINIT_to_wMEM_p);


property write_wMEM_to_wIDLE_p;
  wMEM &&
  (error || ((mem_wr_addr[5:0] == 63) && (poly_count == 4'd7)))
|->
  ##1
  wIDLE &&
  OR_remaining_encoded_h_i == $past(upd_remaining_encoded_h_i_0_i, 1) &&
  bitmap_ptr == 8'((({ $past(mem_wr_addr, 1) }[5:0] == 63) ? 64'd0 : (64'd4 + ({ 56'd0, $past(bitmap_ptr, 1)} )))) &&
  done_port == (read_state == ReadIdle) &&
  error_port == ((($past(upd_remaining_encoded_h_i_0_i, 1) || !$past(hint_ok, 1)) || $past(upd_hintsum_max_error_i_0_i, 1)) || ($past(hintsum, 1) < $past(hintsum_prev_poly, 1))) &&
  hintsum_max_error_i == $past(upd_hintsum_max_error_i_0_i, 1) &&
  mem_wr_addr == 14'((($past(mem_wr_addr, 1) == (14'd511 + $past(dest_address, 1))) ? 64'd0 : (64'd1 + ({ 50'd0, $past(mem_wr_addr, 1)} )))) &&
  poly_count == ((({ $past(mem_wr_addr, 1) }[5:0] == 63) && ($past(poly_count, 1) == 4'd8)) ? 4'd0 : (({ $past(mem_wr_addr, 1) }[5:0] == 63) ? (4'd1 + $past(poly_count, 1)) : $past(poly_count, 1))) &&
  write_data_port == $past(upd_write_data_0_i, 1) &&
  write_request_port == $past(write_request_3_i, 1);
endproperty
write_wMEM_to_wIDLE_a: assert property (disable iff(rst) write_wMEM_to_wIDLE_p);


property write_wMEM_to_wINIT_p;
  wMEM &&
  !error &&
  (mem_wr_addr[5:0] == 63) &&
  (poly_count != 4'd7)
|->
  ##1
  wINIT &&
  $stable(OR_remaining_encoded_h_i) &&
  bitmap_ptr == 8'd0 &&
  done_port == 0 &&
  error_port == ((($past(OR_remaining_encoded_h_i, 1) || !$past(hint_ok, 1)) || $past(hintsum_max_error_i, 1)) || ($past(hintsum, 1) < $past(hintsum_prev_poly, 1))) &&
  $stable(hintsum_max_error_i) &&
  mem_wr_addr == 14'((($past(mem_wr_addr, 1) == (14'd511 + $past(dest_address, 1))) ? 64'd0 : (64'd1 + ({ 50'd0, $past(mem_wr_addr, 1)} )))) &&
  poly_count == 4'((($past(poly_count, 1) == 4'd8) ? 64'd0 : (64'd1 + ({ 60'd0, $past(poly_count, 1)} )))) &&
  write_data_port == $past(upd_write_data_0_i, 1) &&
  write_request_port == $past(write_request_3_i, 1);
endproperty
write_wMEM_to_wINIT_a: assert property (disable iff(rst || fv_err_reg) write_wMEM_to_wINIT_p);


property write_wMEM_to_wMEM_p;
  wMEM &&
  !error &&
  (mem_wr_addr[5:0] != 63)
|->
  ##1
  wMEM &&
  $stable(OR_remaining_encoded_h_i) &&
  bitmap_ptr == (8'd4 + $past(bitmap_ptr, 1)) &&
  done_port == 0 &&
  error_port == ((($past(OR_remaining_encoded_h_i, 1) || !$past(hint_ok, 1)) || $past(hintsum_max_error_i, 1)) || ($past(hintsum, 1) < $past(hintsum_prev_poly, 1))) &&
  $stable(hintsum_max_error_i) &&
  mem_wr_addr == 14'((($past(mem_wr_addr, 1) == (14'd511 + $past(dest_address, 1))) ? 64'd0 : (64'd1 + ({ 50'd0, $past(mem_wr_addr, 1)} )))) &&
  $stable(poly_count) &&
  write_data_port == $past(upd_write_data_0_i, 1) &&
  write_request_port == $past(write_request_3_i, 1);
endproperty
write_wMEM_to_wMEM_a: assert property (disable iff(rst || fv_err_reg) write_wMEM_to_wMEM_p);


property read_rIDLE_eventually_left_p;
  rIDLE &&
  start_port
|->
  s_eventually(!rIDLE);
endproperty
read_rIDLE_eventually_left_a: assert property (disable iff(rst) read_rIDLE_eventually_left_p);


property read_rINIT_eventually_left_p;
  rINIT
|->
  s_eventually(!rINIT);
endproperty
read_rINIT_eventually_left_a: assert property (disable iff(rst) read_rINIT_eventually_left_p);


property read_rHINTSUM_eventually_left_p;
  rHINTSUM
|->
  s_eventually(!rHINTSUM);
endproperty
read_rHINTSUM_eventually_left_a: assert property (disable iff(rst) read_rHINTSUM_eventually_left_p);


property read_rEXEC_eventually_left_p;
  rEXEC
|->
  s_eventually(!rEXEC);
endproperty
read_rEXEC_eventually_left_a: assert property (disable iff(rst) read_rEXEC_eventually_left_p);


property write_wIDLE_eventually_left_p;
  wIDLE &&
  start_port
|->
  s_eventually(!wIDLE);
endproperty
write_wIDLE_eventually_left_a: assert property (disable iff(rst) write_wIDLE_eventually_left_p);


property write_wINIT_eventually_left_p;
  wINIT
|->
  s_eventually(!wINIT);
endproperty
write_wINIT_eventually_left_a: assert property (disable iff(rst) write_wINIT_eventually_left_p);


property write_wMEM_eventually_left_p;
  wMEM
|->
  s_eventually(!wMEM);
endproperty
write_wMEM_eventually_left_a: assert property (disable iff(rst) write_wMEM_eventually_left_p);


parameter CONSISTENCY = 1;
if (CONSISTENCY) begin
  // Check that no more than 1 state condition is met at the same time
  read_consistency_onehot0_state: assert property($onehot0({ rEXEC, rHINTSUM, rIDLE, rINIT }));
end


if (CONSISTENCY) begin
  // Check that no more than 1 state condition is met at the same time
  write_consistency_onehot0_state: assert property($onehot0({ wIDLE, wINIT, wMEM }));
end


endmodule
