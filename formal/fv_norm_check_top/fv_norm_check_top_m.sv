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
// | Created on 18.02.2025 at 14:01                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import fv_norm_check_top_pkg::*;
import fv_norm_check_top_functions::*;


module fv_norm_check_top_m(
  input logic rst,
  input logic clk,

  // Ports
  input logic mem_base_addr_port_vld,
  input logic mem_base_addr_port_rdy,
  input logic unsigned [13:0] mem_base_addr_port,

  input logic unsigned [1:0] norm_check_mode_port,

  input logic shuffling_enable_port,

  input logic unsigned [4:0] randomness_port,

  input logic unsigned [0:0] randomness_lsb_port,

  input a_unsigned_24_4 mem_rd_data_port,

  input logic norm_check_done_port,

  input logic invalid_port,

  input st_mem_if_it mem_rd_req_port,

  // Registers
  input logic unsigned [4:0] incr_addr,
  input logic invalid,
  input logic unsigned [13:0] mem_base_addr,
  input logic unsigned [13:0] mem_rd_addr,
  input a_unsigned_24_4 mem_rd_data,
  input st_mem_if_it mem_rd_req,
  input logic unsigned [6:0] neutral_cnt,
  input logic unsigned [1:0] norm_check_mode,
  input logic unsigned [0:0] randomness_lsb,
  input logic shuffling_enable,

  // States
  input logic IDLE,
  input logic READ_MEM,
  input logic WAIT,
  input logic DONE
);


default clocking default_clk @(posedge clk); endclocking


a_unsigned_24_4 mem_rd_data_0_i;
assign mem_rd_data_0_i = '{
  0: 24'd0,
  1: 24'd0,
  2: 24'd0,
  3: 24'd0
};

st_mem_if_it mem_rd_req_0_i;
assign mem_rd_req_0_i = '{
  address: 14'd0,
  rd_wr_en: 2'd0
};

logic return_invalid_0_i;
assign return_invalid_0_i = return_invalid(norm_check_mode_port, (mem_rd_data_port[64'd0]));

logic return_invalid_1_i;
assign return_invalid_1_i = return_invalid(norm_check_mode_port, (mem_rd_data_port[64'd1]));

logic return_invalid_2_i;
assign return_invalid_2_i = return_invalid(norm_check_mode_port, (mem_rd_data_port[64'd2]));

logic return_invalid_3_i;
assign return_invalid_3_i = return_invalid(norm_check_mode_port, (mem_rd_data_port[64'd3]));

logic unsigned [13:0] return_idle_mem_rd_req_0_i;
assign return_idle_mem_rd_req_0_i = return_idle_mem_rd_req(randomness_port, randomness_lsb_port);

st_mem_if_it mem_rd_req_1_i;
assign mem_rd_req_1_i = '{
  address: (return_idle_mem_rd_req_0_i + mem_base_addr_port),
  rd_wr_en: 2'd0
};

logic unsigned [13:0] return_idle_mem_rd_req_1_i;
assign return_idle_mem_rd_req_1_i = return_idle_mem_rd_req(5'd0, 1'd0);

st_mem_if_it mem_rd_req_2_i;
assign mem_rd_req_2_i = '{
  address: (return_idle_mem_rd_req_1_i + mem_base_addr_port),
  rd_wr_en: 2'd0
};

logic unsigned [13:0] return_read_mem_mem_rd_req_0_i;
assign return_read_mem_mem_rd_req_0_i = return_read_mem_mem_rd_req(mem_rd_addr, randomness_lsb);

logic return_invalid_4_i;
assign return_invalid_4_i = return_invalid(norm_check_mode, 22'(mem_rd_data[64'd0]));

logic return_invalid_5_i;
assign return_invalid_5_i = return_invalid(norm_check_mode, 22'(mem_rd_data[64'd1]));

logic return_invalid_6_i;
assign return_invalid_6_i = return_invalid(norm_check_mode, 22'(mem_rd_data[64'd2]));

logic return_invalid_7_i;
assign return_invalid_7_i = return_invalid(norm_check_mode, 22'(mem_rd_data[64'd3]));

st_mem_if_it mem_rd_req_3_i;
assign mem_rd_req_3_i = '{
  address: (return_read_mem_mem_rd_req_0_i + mem_base_addr),
  rd_wr_en: 2'd1
};

logic unsigned [13:0] return_wait_mem_mem_rd_req_0_i;
assign return_wait_mem_mem_rd_req_0_i = return_wait_mem_mem_rd_req(mem_rd_addr, incr_addr, randomness_lsb_port);

st_mem_if_it mem_rd_req_4_i;
assign mem_rd_req_4_i = '{
  address: (return_wait_mem_mem_rd_req_0_i + mem_base_addr),
  rd_wr_en: 2'd1
};

logic unsigned [13:0] return_wait_mem_mem_rd_req_1_i;
assign return_wait_mem_mem_rd_req_1_i = return_wait_mem_mem_rd_req(mem_rd_addr, incr_addr, randomness_lsb);

st_mem_if_it mem_rd_req_5_i;
assign mem_rd_req_5_i = '{
  address: (return_wait_mem_mem_rd_req_1_i + mem_base_addr),
  rd_wr_en: 2'd1
};

st_mem_if_it mem_rd_req_6_i;
assign mem_rd_req_6_i = '{
  address: mem_rd_req.address,
  rd_wr_en: 2'd0
};


sequence reset_sequence;
  rst ##1 !rst;
endsequence


property run_reset_p;
  reset_sequence |->
  IDLE &&
  invalid_port == 0 &&
  norm_check_done_port == 0 &&
  mem_base_addr_port_rdy == 0 &&
  mem_rd_req_port.rd_wr_en == 0 &&
  mem_rd_req_port.address == '0 &&
  mem_base_addr == '0 &&
  randomness_lsb == '0 &&
  incr_addr == 0;
endproperty
run_reset_a: assert property (run_reset_p);


////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////IDLE TRANSTION PROPERTIES //////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////
property run_IDLE_to_READ_MEM_p;
  IDLE &&
  mem_base_addr_port_vld &&
  shuffling_enable_port
|->
  ##1
  READ_MEM &&
  mem_rd_req_port.address == $past(mem_rd_req_1_i.address, 1) &&
  mem_rd_req_port.rd_wr_en == 1 &&
  norm_check_done_port == 0 &&
  mem_base_addr == $past(mem_base_addr_port) &&
  mem_base_addr_port_rdy == $past(norm_check_done_port) && 
  neutral_cnt == 0 &&
  randomness_lsb == $past(randomness_lsb_port)&&
  incr_addr == $past(randomness_port);
endproperty
run_IDLE_to_READ_MEM_a: assert property (disable iff(rst) run_IDLE_to_READ_MEM_p);

property run_IDLE_to_READ_MEM_1_p;
  IDLE &&
  mem_base_addr_port_vld &&
  !shuffling_enable_port
|->
  ##1
  READ_MEM &&
  mem_rd_req_port.address == $past(mem_rd_req_2_i.address, 1) &&
  mem_rd_req_port.rd_wr_en == 1 &&
  norm_check_done_port == 0  &&
  mem_base_addr == $past(mem_base_addr_port) &&
  mem_base_addr_port_rdy == $past(norm_check_done_port) &&
  neutral_cnt == 0 &&
  randomness_lsb == '0 &&
  incr_addr == 0;
endproperty
run_IDLE_to_READ_MEM_1_a: assert property (disable iff(rst) run_IDLE_to_READ_MEM_1_p);


property run_IDLE_wait_p;
  IDLE &&
  !mem_base_addr_port_vld
|->
  ##1
  IDLE &&
  norm_check_done_port == 0 &&
  incr_addr == $past(5'(incr_addr + 1)) &&
  randomness_lsb == ($past(shuffling_enable_port) ? $past(randomness_lsb_port):'0)&& 
  $stable(mem_base_addr) &&
  $stable(mem_rd_req.rd_wr_en) &&
  mem_base_addr_port_rdy == $past(norm_check_done_port) &&
  neutral_cnt == $past(7'(neutral_cnt + 1));
endproperty
run_IDLE_wait_a: assert property (disable iff(rst ) run_IDLE_wait_p);


//run_IDLE_wait_1_a: assert property (disable iff(rst ) run_IDLE_wait_1_p);
////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////







////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////READ MEM TRANSTION PROPERTIES ///////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////
property run_READ_MEM_to_DONE_p;//This is unreachable
  READ_MEM &&
  ((7'd1 + neutral_cnt) >= 7'd64)
|->
  ##1
  DONE ;
endproperty
run_READ_MEM_to_DONE_a: assert property (disable iff(rst) run_READ_MEM_to_DONE_p);

property run_READ_MEM_to_WAIT_p;
  READ_MEM &&
  ((7'd1 + neutral_cnt) < 7'd64)
|->
  ##1
  WAIT &&
  mem_rd_req_port.address == $past(mem_rd_req_3_i.address, 1) &&
  mem_rd_req_port.rd_wr_en == mem_rd_req_3_i.rd_wr_en   &&
  norm_check_done_port == 0 &&
  incr_addr == $past(5'(incr_addr + 1)) &&
  randomness_lsb == ($past(shuffling_enable_port) ? $past(randomness_lsb_port):'0)&&
  $stable(mem_base_addr) &&
  mem_base_addr_port_rdy == $past(norm_check_done_port) &&
  neutral_cnt == $past(neutral_cnt + 1);
endproperty
run_READ_MEM_to_WAIT_a: assert property (disable iff(rst) run_READ_MEM_to_WAIT_p);


property run_WAIT_to_READMEM_p;
  WAIT &&
  ((7'd1 + neutral_cnt) < 7'd64)
|->
  ##1
  READ_MEM &&
  mem_rd_req_port.address == $past(mem_rd_req_5_i.address, 1) &&
  mem_rd_req_port.rd_wr_en == mem_rd_req_5_i.rd_wr_en   &&
  norm_check_done_port == 0 &&
  $stable(incr_addr) &&
  $stable(randomness_lsb) &&
  $stable(mem_base_addr) &&
  mem_base_addr_port_rdy == $past(norm_check_done_port) &&
  neutral_cnt == $past(7'(neutral_cnt + 1));
endproperty
run_WAIT_to_READMEM_a: assert property (disable iff(rst) run_WAIT_to_READMEM_p);

////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////






////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////WAIT TRANSTION PROPERTIES ///////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////
property run_WAIT_to_DONE_p;
  WAIT &&
  ((7'd1 + neutral_cnt) >= 7'd64)
|->
  ##1
  DONE &&
  mem_rd_req_port.rd_wr_en == 0 &&
  norm_check_done_port == 0 &&
  $stable(incr_addr) &&
  $stable(randomness_lsb) &&
  $stable(mem_base_addr) &&
  mem_base_addr_port_rdy == $past(norm_check_done_port) &&
  neutral_cnt == $past(7'(neutral_cnt + 1));
endproperty
run_WAIT_to_DONE_a: assert property (disable iff(rst) run_WAIT_to_DONE_p);
////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////DONE TRANSTION PROPERTIES //////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////
property run_DONE_to_IDLE_p;
  DONE
|->
  ##1
  IDLE &&
  norm_check_done_port == 1 &&
  mem_rd_req_port.rd_wr_en == 0 &&
  neutral_cnt == $past(7'(neutral_cnt + 1)) &&
  incr_addr == $past(5'(incr_addr + 1)) &&
  randomness_lsb == ($past(shuffling_enable_port) ? $past(randomness_lsb_port):'0) &&
  $stable(mem_base_addr) &&
  mem_base_addr_port_rdy == $past(norm_check_done_port);
endproperty
run_DONE_to_IDLE_a: assert property (disable iff(rst) run_DONE_to_IDLE_p);
////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////IVALID CHECKS //////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////
// After the check is done, the invalid port should be set to zero one cycle later
property run_IDLE_disable_invalid_p;
  ##0 IDLE
  ##0 norm_check_done_port
|->
  ##1 invalid_port == 0;
endproperty
run_IDLE_disable_invalid_a: assert property (disable iff(rst) run_IDLE_disable_invalid_p);
// If there state is IDLE and there is no done, the invalid_port should stay the same as the last cycle. 
property run_IDLE_STABLE_INVALID_p;
  ##0 IDLE
  ##0 !norm_check_done_port
|->
  ##1 invalid_port == '0; // $past(invalid_port,1); //
endproperty
run_IDLE_STABLE_INVALID_a: assert property (disable iff(rst ) run_IDLE_STABLE_INVALID_p);
//Check computation for the invalid while the state is READ_MEM or wait
property run_INVALID_COMPUTATION_p;
  ##0 READ_MEM || WAIT || DONE
|->
  ##1 invalid_port == $past(invalid_port,1)       ||
                      $past(return_invalid_0_i,1) ||
                      $past(return_invalid_1_i,1) ||
                      $past(return_invalid_2_i,1) ||
                      $past(return_invalid_3_i,1);
endproperty
run_INVALID_COMPUTATION_a: assert property (disable iff(rst) run_INVALID_COMPUTATION_p);


////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////WHITE BOX CHECKS ///////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////

property run_IDLE_eventually_left_p;
  ##0 IDLE
  ##0 mem_base_addr_port_vld
|->
  s_eventually(!IDLE);
endproperty
run_IDLE_eventually_left_a: assert property (disable iff(rst) run_IDLE_eventually_left_p);


property run_READ_MEM_eventually_left_p;
  READ_MEM
|->
  s_eventually(!READ_MEM);
endproperty
run_READ_MEM_eventually_left_a: assert property (disable iff(rst) run_READ_MEM_eventually_left_p);


property run_WAIT_eventually_left_p;
  WAIT
|->
  s_eventually(!WAIT);
endproperty
run_WAIT_eventually_left_a: assert property (disable iff(rst) run_WAIT_eventually_left_p);


property run_DONE_eventually_left_p;
  DONE
|->
  s_eventually(!DONE);
endproperty
run_DONE_eventually_left_a: assert property (disable iff(rst) run_DONE_eventually_left_p);


parameter CONSISTENCY = 1;
if (CONSISTENCY) begin
  // Check that no more than 1 state condition is met at the same time
  run_consistency_onehot0_state: assert property($onehot0({ DONE, IDLE, READ_MEM, WAIT }));
end
////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////

endmodule
