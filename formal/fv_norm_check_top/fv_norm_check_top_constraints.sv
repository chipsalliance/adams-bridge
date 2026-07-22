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


import fv_norm_check_top_pkg::*;


module fv_norm_check_top_constraints(
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

  input st_mem_if_it mem_rd_req_port

 
);

    default clocking default_clk @(posedge clk); endclocking

    stable_base_addr                           : assume property (##1 $stable(mem_base_addr_port));
    stable_norm_check_mode_port                : assume property (##1 $stable(norm_check_mode_port));
    stable_norm_check_shuffle_en               : assume property (##1 $stable(shuffling_enable_port));

    logic ongoing_computation;
    always_ff @(posedge clk) begin
        if(rst) begin
            ongoing_computation <= 1'b0;
        end else if(!ongoing_computation || norm_check_done_port) begin
            ongoing_computation <= mem_base_addr_port_vld;
        end
    end

    // Set enable only when it is not busy
    assume_only_enable_when_idle : assume property (
        mem_base_addr_port_vld
    |->
        !ongoing_computation || norm_check_done_port
    );
endmodule
bind norm_check_top fv_norm_check_top_constraints fv_norm_check_top_constraints(
  .rst(!norm_check_top.reset_n || norm_check_top.zeroize),
  .clk(norm_check_top.clk),

  // Ports
  .mem_base_addr_port_vld(norm_check_top.norm_check_enable),
  .mem_base_addr_port_rdy(norm_check_top.norm_check_ready),
  .mem_base_addr_port(norm_check_top.mem_base_addr),

  .mem_rd_data_port({norm_check_top.mem_rd_data[95:72],norm_check_top.mem_rd_data[71:48],norm_check_top.mem_rd_data[47:24],norm_check_top.mem_rd_data[23:0]}),

  .norm_check_mode_port(norm_check_top.mode),

  .randomness_lsb_port(norm_check_top.randomness[0]),

  .randomness_port(norm_check_top.randomness[5:1]),

  .shuffling_enable_port(norm_check_top.shuffling_enable),

  .invalid_port(norm_check_top.invalid),

  .norm_check_done_port(norm_check_top.norm_check_done)
);
