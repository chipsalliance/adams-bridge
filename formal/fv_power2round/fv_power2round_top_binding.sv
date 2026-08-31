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
// | Created on 03.05.2025 at 11:33                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


module fv_power2round_top_ref_wrapper_m
  import fv_power2round_top_pkg::*;
  import abr_params_pkg::*;
  import power2round_defines_pkg::*;
  import fv_power2round_top_functions::*;
#(
    parameter REG_SIZE       = 24,
    parameter MLDSA_Q        = 23'd8380417,
    parameter MLDSA_N        = 256,
    parameter MLDSA_K        = 8,
    parameter MLDSA_D        = 13,
    parameter AHB_DATA_WIDTH = 32
) (
      //#$ports
    input                            pi_clk,
    input                            pi_reset_n,
    input                            pi_zeroize,
    input                            pi_enable,
    input [ABR_MEM_ADDR_WIDTH-1:0] pi_src_base_addr,
    input [ABR_MEM_ADDR_WIDTH-1:0] pi_skmem_dest_base_addr,
    input mem_if_t                   po_mem_a_rd_req,
    input mem_if_t                   po_mem_b_rd_req,
    input [(4*REG_SIZE)-1:0]         pi_mem_rd_data_a,
    input [(4*REG_SIZE)-1:0]         pi_mem_rd_data_b,
    input mem_if_t                   po_skmem_a_wr_req,
    input mem_if_t                   po_skmem_b_wr_req,
    input logic [AHB_DATA_WIDTH-1:0] po_skmem_wr_data_a,
    input logic [AHB_DATA_WIDTH-1:0] po_skmem_wr_data_b,
    input logic                      po_pk_t1_wren,
    input logic [7:0][9:0]           po_pk_t1_wrdata,
    input logic [7:0]                po_pk_t1_wr_addr,
    input logic                      po_done
    //$#//
);


a_unsigned_24_8 rd_data_port;
assign rd_data_port = '{power2round_top.mem_data_reg[7], power2round_top.mem_data_reg[6], power2round_top.mem_data_reg[5], power2round_top.mem_data_reg[4], power2round_top.mem_data_reg[3], power2round_top.mem_data_reg[2], power2round_top.mem_data_reg[1], power2round_top.mem_data_reg[0]};

st_PkRequest pk_wr_req_out;
assign pk_wr_req_out = '{address: power2round_top.pk_t1_wr_addr, enable: power2round_top.pk_t1_wren};

st_Request rd_req_out;
assign rd_req_out = '{addresses: '{power2round_top.mem_a_rd_req.addr, power2round_top.mem_b_rd_req.addr}, idle: (power2round_top.mem_a_rd_req.rd_wr_en == RW_IDLE) && (power2round_top.mem_b_rd_req.rd_wr_en == RW_IDLE), read: (power2round_top.mem_a_rd_req.rd_wr_en == RW_READ) && (power2round_top.mem_b_rd_req.rd_wr_en == RW_READ), write: (power2round_top.mem_a_rd_req.rd_wr_en == RW_WRITE) && (power2round_top.mem_b_rd_req.rd_wr_en == RW_WRITE)};

a_unsigned_32_2 wr_data_port;
assign wr_data_port = '{power2round_top.skmem_wr_data_b , power2round_top.skmem_wr_data_a};

st_Request wr_req_out;
assign wr_req_out = '{addresses: '{power2round_top.skmem_a_wr_req.addr, power2round_top.skmem_b_wr_req.addr}, idle: (power2round_top.skmem_a_wr_req.rd_wr_en == RW_IDLE) && (power2round_top.skmem_b_wr_req.rd_wr_en == RW_IDLE), read: (power2round_top.skmem_a_wr_req.rd_wr_en == RW_READ) && (power2round_top.skmem_b_wr_req.rd_wr_en == RW_READ), write: (power2round_top.skmem_a_wr_req.rd_wr_en == RW_WRITE) && (power2round_top.skmem_b_wr_req.rd_wr_en == RW_WRITE)};

st_BaseAddress base_address;
assign base_address = '{source: power2round_top.power2round_ctrl_inst.src_base_addr, destination: power2round_top.power2round_ctrl_inst.skmem_dest_base_addr};


fv_power2round_top_m fv_power2round_top(
  .rst(!power2round_top.reset_n || power2round_top.zeroize),
  .clk(power2round_top.clk),

  // Ports
  .current_buffer(power2round_top.sk_buffer_inst.num_valid),

  .current_rd_cnt(power2round_top.power2round_ctrl_inst.mem_rd_addr - power2round_top.src_base_addr),

  .current_wr_cnt(power2round_top.power2round_ctrl_inst.skmem_wr_addr - power2round_top.skmem_dest_base_addr),

  .enable_port(power2round_top.enable),

  .rd_data_port(rd_data_port),

  .start_port_vld(power2round_top.enable),
  .start_port_rdy(1'b1),
  .start_port({power2round_top.src_base_addr, power2round_top.skmem_dest_base_addr}),

  .buffer_new(power2round_top.sk_buffer_inst.num_valid),

  .done_port(power2round_top.done),

  .pk_wr_data_port(power2round_top.pk_t1_wrdata),

  .pk_wr_req_out_vld(1'b1),
  .pk_wr_req_out(pk_wr_req_out),

  .rd_cnt_new(power2round_top.power2round_ctrl_inst.mem_rd_addr - power2round_top.src_base_addr),

  .rd_req_out_vld(1'b1),
  .rd_req_out(rd_req_out),

  .wr_cnt_new(power2round_top.power2round_ctrl_inst.skmem_wr_addr - power2round_top.skmem_dest_base_addr),

  .wr_data_port(wr_data_port),

  .wr_req_out_vld(1'b1),
  .wr_req_out(wr_req_out),

  // Registers
  .base_address(base_address),
  .buffer(power2round_top.sk_buffer_inst.num_valid),
  .buffer_data(power2round_top.sk_buffer_inst.buffer_d),
  .enable(power2round_top.enable),
  .r0_packed(power2round_top.r0_packed),
  .r0_packed_reg(power2round_top.r0_packed_reg),
  .r1(power2round_top.r1),
  .r1_reg(power2round_top.r1_reg),
  .rd_cnt(power2round_top.power2round_ctrl_inst.mem_rd_addr - power2round_top.src_base_addr),
  .wr_cnt(power2round_top.power2round_ctrl_inst.skmem_wr_addr - power2round_top.skmem_dest_base_addr),

  // States
  .DONE(power2round_top.power2round_ctrl_inst.read_fsm_state_ps==T_RD_IDLE && power2round_top.power2round_ctrl_inst.sk_write_fsm_state_ps==SK_WR_IDLE && power2round_top.power2round_ctrl_inst.pk_write_fsm_state_ps==PK_WR_IDLE && power2round_top.done),
  .IDLE(power2round_top.power2round_ctrl_inst.read_fsm_state_ps==T_RD_IDLE && power2round_top.power2round_ctrl_inst.sk_write_fsm_state_ps==SK_WR_IDLE && power2round_top.power2round_ctrl_inst.pk_write_fsm_state_ps==PK_WR_IDLE && !power2round_top.done),
  .LAST_READ(power2round_top.power2round_ctrl_inst.read_fsm_state_ps==T_RD_DONE && power2round_top.power2round_ctrl_inst.sk_write_fsm_state_ps==SK_WR_MEM && power2round_top.power2round_ctrl_inst.skmem_wr_addr - power2round_top.skmem_dest_base_addr == 820 && power2round_top.power2round_ctrl_inst.pk_write_fsm_state_ps==PK_WR_API),
  .LOOP(power2round_top.power2round_ctrl_inst.mem_rd_addr - power2round_top.src_base_addr >= 6 && power2round_top.power2round_ctrl_inst.sk_write_fsm_state_ps==SK_WR_MEM && power2round_top.power2round_ctrl_inst.skmem_wr_addr - power2round_top.skmem_dest_base_addr < 820 && power2round_top.power2round_ctrl_inst.pk_write_fsm_state_ps==PK_WR_API),
  .ONLY_WRITE1(power2round_top.power2round_ctrl_inst.read_fsm_state_ps==T_RD_IDLE && power2round_top.power2round_ctrl_inst.sk_write_fsm_state_ps==SK_WR_MEM && power2round_top.power2round_ctrl_inst.skmem_wr_addr - power2round_top.skmem_dest_base_addr == 822 && power2round_top.power2round_ctrl_inst.pk_write_fsm_state_ps==PK_WR_API),
  .ONLY_WRITE2(power2round_top.power2round_ctrl_inst.read_fsm_state_ps==T_RD_IDLE && power2round_top.power2round_ctrl_inst.sk_write_fsm_state_ps==SK_WR_MEM && power2round_top.power2round_ctrl_inst.skmem_wr_addr - power2round_top.skmem_dest_base_addr == 824 && power2round_top.power2round_ctrl_inst.pk_write_fsm_state_ps==PK_WR_API),
  .ONLY_WRITE3(power2round_top.power2round_ctrl_inst.read_fsm_state_ps==T_RD_IDLE && power2round_top.power2round_ctrl_inst.sk_write_fsm_state_ps==SK_WR_MEM && power2round_top.power2round_ctrl_inst.skmem_wr_addr - power2round_top.skmem_dest_base_addr == 826 && power2round_top.power2round_ctrl_inst.pk_write_fsm_state_ps==PK_WR_API),
  .ONLY_WRITE4(power2round_top.power2round_ctrl_inst.read_fsm_state_ps==T_RD_IDLE && power2round_top.power2round_ctrl_inst.sk_write_fsm_state_ps==SK_WR_MEM && power2round_top.power2round_ctrl_inst.skmem_wr_addr - power2round_top.skmem_dest_base_addr == 828 && power2round_top.power2round_ctrl_inst.pk_write_fsm_state_ps==PK_WR_DONE),
  .ONLY_WRITE5(power2round_top.power2round_ctrl_inst.read_fsm_state_ps==T_RD_IDLE && power2round_top.power2round_ctrl_inst.sk_write_fsm_state_ps==SK_WR_MEM && power2round_top.power2round_ctrl_inst.skmem_wr_addr - power2round_top.skmem_dest_base_addr == 830 && power2round_top.power2round_ctrl_inst.pk_write_fsm_state_ps==PK_WR_IDLE),
  .ONLY_WRITE6(power2round_top.power2round_ctrl_inst.read_fsm_state_ps==T_RD_IDLE && power2round_top.power2round_ctrl_inst.sk_write_fsm_state_ps==SK_WR_DONE && power2round_top.power2round_ctrl_inst.skmem_wr_addr - power2round_top.skmem_dest_base_addr == 830 && power2round_top.power2round_ctrl_inst.pk_write_fsm_state_ps==PK_WR_IDLE),
  .REQ_1ST_DATA(power2round_top.power2round_ctrl_inst.read_fsm_state_ps==T_RD_MEM && power2round_top.power2round_ctrl_inst.mem_rd_addr - power2round_top.src_base_addr == 0 && power2round_top.power2round_ctrl_inst.sk_write_fsm_state_ps==SK_WR_IDLE && power2round_top.power2round_ctrl_inst.pk_write_fsm_state_ps==PK_WR_IDLE),
  .REQ_2ND_DATA(power2round_top.power2round_ctrl_inst.read_fsm_state_ps==T_RD_MEM && power2round_top.power2round_ctrl_inst.mem_rd_addr - power2round_top.src_base_addr == 2 && power2round_top.power2round_ctrl_inst.sk_write_fsm_state_ps==SK_WR_WAIT && power2round_top.power2round_ctrl_inst.pk_write_fsm_state_ps==PK_WR_API),
  .REQ_3RD_DATA(power2round_top.power2round_ctrl_inst.read_fsm_state_ps==T_RD_MEM && power2round_top.power2round_ctrl_inst.mem_rd_addr - power2round_top.src_base_addr == 4 && power2round_top.power2round_ctrl_inst.sk_write_fsm_state_ps==SK_WR_MEM && power2round_top.power2round_ctrl_inst.pk_write_fsm_state_ps==PK_WR_API)
);


endmodule


bind power2round_top fv_power2round_top_ref_wrapper_m #(
    .REG_SIZE(REG_SIZE),
    .MLDSA_Q(MLDSA_Q),
    .MLDSA_N(MLDSA_N),
    .MLDSA_K(MLDSA_K),
    .MLDSA_D(MLDSA_D),
    .AHB_DATA_WIDTH(AHB_DATA_WIDTH)
 ) fv_power2round_top_ref_wrapper (
  //#$bind
  .pi_clk (clk),
  .pi_reset_n (reset_n),
  .pi_zeroize (zeroize),
  .pi_enable (enable),
  .pi_src_base_addr (src_base_addr),
  .pi_skmem_dest_base_addr (skmem_dest_base_addr),
  .po_mem_a_rd_req (mem_a_rd_req),
  .po_mem_b_rd_req (mem_b_rd_req),
  .pi_mem_rd_data_a (mem_rd_data_a),
  .pi_mem_rd_data_b (mem_rd_data_b),
  .po_skmem_a_wr_req (skmem_a_wr_req),
  .po_skmem_b_wr_req (skmem_b_wr_req),
  .po_skmem_wr_data_a (skmem_wr_data_a),
  .po_skmem_wr_data_b (skmem_wr_data_b),
  .po_pk_t1_wren (pk_t1_wren),
  .po_pk_t1_wrdata (pk_t1_wrdata),
  .po_pk_t1_wr_addr (pk_t1_wr_addr),
  .po_done (done)
);
