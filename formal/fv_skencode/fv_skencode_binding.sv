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
// | Created on 05.04.2025 at 12:39                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import fv_skencode_functions::*;


module fv_skencode_ref_wrapper_m;


default clocking default_clk @(posedge (skencode.clk)); endclocking


fv_skencode_m fv_skencode(
  .rst_n(skencode.reset_n && !skencode.zeroize),
  .clk(skencode.clk),

  // Ports
  .mem_rd_data_curr({skencode.mem_b_rd_data, skencode.mem_a_rd_data}),

  .mem_rd_data_prev($past({skencode.mem_b_rd_data, skencode.mem_a_rd_data}, 1)),

  .mem_rd_data_prev_3($past({skencode.mem_b_rd_data, skencode.mem_a_rd_data}, 3)),

  .mem_rd_data_prev_4($past({skencode.mem_b_rd_data, skencode.mem_a_rd_data}, 4)),

  .mem_rd_data_prev_5($past({skencode.mem_b_rd_data, skencode.mem_a_rd_data}, 5)),

  .start_port_vld(skencode.skencode_enable),
  .start_port_rdy(1'b1),
  .start_port({skencode.src_base_addr, skencode.dest_base_addr}),

  .top_bits(skencode.keymem_a_wr_data),

  .buffer_new(skencode.consumer_selector),

  .keymem_a_wr_data(skencode.keymem_a_wr_data),

  .keymem_a_wr_req_vld(1'b1),
  .keymem_a_wr_req(skencode.keymem_a_wr_req),

  .mem_a_rd_req_vld(1'b1),
  .mem_a_rd_req(skencode.mem_a_rd_req),

  .mem_b_rd_req_vld(1'b1),
  .mem_b_rd_req(skencode.mem_b_rd_req),

  .num_api_operands_new(),

  .num_mem_operands_new(),

  .skencode_done_vld(skencode.skencode_done),
  .skencode_done(skencode.skencode_done),

  // Registers
  .base_address({skencode.locked_src_addr, skencode.locked_dest_addr}),
  .consumer_selector(skencode.consumer_selector),
  .num_api_operands(skencode.num_api_operands),
  .num_mem_operands(skencode.num_mem_operands),
  .producer_selector(skencode.producer_selector),

  // States
  .CONSUME___WRITE(skencode.main_state == skencode.CONSUME && skencode.write_state == skencode.WRITE),
  .CONSUME_LAST___STALL(skencode.main_state == skencode.CONSUME_LAST && skencode.write_state == skencode.STALL),
  .DONE___GET_LAST(skencode.main_state == skencode.DONE && skencode.write_state == skencode.GET_LAST),
  .IDLE((skencode.main_state == skencode.IDLE && skencode.write_state == skencode.IDLE) || (skencode.main_state == skencode.IDLE && skencode.write_state == skencode.DONE && skencode.skencode_done ==1)),
  .READ_and_ENC(skencode.main_state == skencode.READ_and_ENC && skencode.write_state == skencode.IDLE),
  .READ_ENC_and_CONSUME___IDLE(skencode.main_state == skencode.READ_ENC_and_CONSUME && skencode.write_state == skencode.IDLE),
  .READ_ENC_and_CONSUME___looped((skencode.main_state == skencode.READ_ENC_and_CONSUME || skencode.main_state == skencode.ENC_and_CONSUME) && skencode.num_api_operands > 0),
  .READ_ENC_and_CONSUME___WAIT_BUFFER(skencode.main_state == skencode.READ_ENC_and_CONSUME && skencode.write_state == skencode.WAIT_BUFFER && skencode.num_api_operands==0)
);


endmodule


bind skencode fv_skencode_ref_wrapper_m fv_skencode_ref_wrapper();
