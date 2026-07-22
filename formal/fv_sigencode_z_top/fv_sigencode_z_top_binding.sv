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
// | Created on 21.11.2024 at 13:12                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+



module fv_sigencode_z_top_ref_wrapper_m
  import abr_params_pkg::*;
  import fv_sigencode_z_top_pkg::*;
  import fv_sigencode_z_top_functions::*;
  import sigencode_z_defines_pkg::*;
#(
    parameter MEM_ADDR_WIDTH = MLDSA_MEM_ADDR_WIDTH,
    parameter REG_SIZE       = 24,
    parameter GAMMA1         = 19
) (
    //#$ports
    input                       pi_clk,
    input                       pi_reset_n,
    input                       pi_zeroize,
    input [MEM_ADDR_WIDTH-1:0]  pi_src_base_addr,
    input mem_if_t              po_mem_a_rd_req,
    input mem_if_t              po_mem_b_rd_req,
    input [3:0][REG_SIZE-1:0]   pi_mem_a_rd_data,
    input [3:0][REG_SIZE-1:0]   pi_mem_b_rd_data,
    input [MEM_ADDR_WIDTH-1:0]  pi_sigmem_dest_base_addr,
    input sig_mem_if_t          po_sigmem_a_wr_req,
    input sig_mem_if_t          po_sigmem_b_wr_req,
    input logic [3:0][GAMMA1:0] po_sigmem_a_wr_data,
    input logic [3:0][GAMMA1:0] po_sigmem_b_wr_data,
    input                       pi_sigencode_z_enable,
    input logic                 po_sigencode_z_done
    //$#//
);

st_BaseAddress start_port;
assign start_port = '{sigencode_z_top.src_base_addr, sigencode_z_top.sigmem_dest_base_addr};

st_Request read_request_port;
assign read_request_port = '{
    addresses: '{sigencode_z_top.mem_a_rd_req.addr, sigencode_z_top.mem_b_rd_req.addr},
    idle:  (sigencode_z_top.mem_a_rd_req.rd_wr_en == RW_IDLE)  && (sigencode_z_top.mem_b_rd_req.rd_wr_en == RW_IDLE),
    read:  (sigencode_z_top.mem_a_rd_req.rd_wr_en == RW_READ)  && (sigencode_z_top.mem_b_rd_req.rd_wr_en == RW_READ),
    write: (sigencode_z_top.mem_a_rd_req.rd_wr_en == RW_WRITE) && (sigencode_z_top.mem_b_rd_req.rd_wr_en == RW_WRITE)
};

st_Request write_request_port;
assign write_request_port = '{
    addresses: '{sigencode_z_top.sigmem_a_wr_req.addr, sigencode_z_top.sigmem_b_wr_req.addr},
    idle:  (sigencode_z_top.sigmem_a_wr_req.rd_wr_en == RW_IDLE)  && (sigencode_z_top.sigmem_b_wr_req.rd_wr_en == RW_IDLE),
    read:  (sigencode_z_top.sigmem_a_wr_req.rd_wr_en == RW_READ)  && (sigencode_z_top.sigmem_b_wr_req.rd_wr_en == RW_READ),
    write: (sigencode_z_top.sigmem_a_wr_req.rd_wr_en == RW_WRITE) && (sigencode_z_top.sigmem_b_wr_req.rd_wr_en == RW_WRITE)
};

st_BaseAddress base_address;
assign base_address = '{source: sigencode_z_top.locked_src_addr, destination: sigencode_z_top.locked_dest_addr};


fv_sigencode_z_top_m fv_sigencode_z_top(
  .rst(!sigencode_z_top.reset_n || sigencode_z_top.zeroize),
  .clk(sigencode_z_top.clk),

  // Ports
  .read_data_port({sigencode_z_top.mem_a_rd_data, sigencode_z_top.mem_b_rd_data}),

  .start_port_vld(sigencode_z_top.sigencode_z_enable),
  .start_port_rdy(1'b1),
  .start_port(start_port),

  .done_port(sigencode_z_top.sigencode_z_done),

  .read_request_port(read_request_port),

  .write_data_port({sigencode_z_top.sigmem_a_wr_data, sigencode_z_top.sigmem_b_wr_data}),

  .write_request_port(write_request_port),

  // Registers
  .base_address(base_address),
  .operands(sigencode_z_top.num_mem_operands[6:0]),

  // States
  .DONE(sigencode_z_top.state == sigencode_z_top.DONE),
  .EXEC_WRITE(sigencode_z_top.state == sigencode_z_top.EXEC_and_WRITE),
  .IDLE(sigencode_z_top.state == sigencode_z_top.IDLE),
  .READ_EXEC(sigencode_z_top.state == sigencode_z_top.READ_and_EXEC),
  .READ_EXEC_WRITE(sigencode_z_top.state == sigencode_z_top.READ_EXEC_and_WRITE),
  .WRITE(sigencode_z_top.state == sigencode_z_top.WRITE)
);
endmodule

bind sigencode_z_top fv_sigencode_z_top_ref_wrapper_m #(
    .MEM_ADDR_WIDTH(MEM_ADDR_WIDTH),
    .REG_SIZE(REG_SIZE),
    .GAMMA1(GAMMA1)
 ) fv_sigencode_z_top_ref_wrapper (    
    //#$bind
    .pi_clk (clk),
    .pi_reset_n (reset_n),
    .pi_zeroize (zeroize),
    .pi_src_base_addr (src_base_addr),
    .po_mem_a_rd_req (mem_a_rd_req),
    .po_mem_b_rd_req (mem_b_rd_req),
    .pi_mem_a_rd_data (mem_a_rd_data),
    .pi_mem_b_rd_data (mem_b_rd_data),
    .pi_sigmem_dest_base_addr (sigmem_dest_base_addr),
    .po_sigmem_a_wr_req (sigmem_a_wr_req),
    .po_sigmem_b_wr_req (sigmem_b_wr_req),
    .po_sigmem_a_wr_data (sigmem_a_wr_data),
    .po_sigmem_b_wr_data (sigmem_b_wr_data),
    .pi_sigencode_z_enable (sigencode_z_enable),
    .po_sigencode_z_done (sigencode_z_done)
    //$#//
);