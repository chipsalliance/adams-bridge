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

//Initial top level module
`include "config_defines.svh"

module adamsbridge_top
  import abr_prim_alert_pkg::*;
  import adamsbridge_reg_pkg::*;
  import abr_params_pkg::*;
  import abr_seq_pkg::*;
  import sampler_pkg::*;
  import sha3_pkg::*;
  import ntt_defines_pkg::*;
  #(
  //top level params
    parameter AHB_ADDR_WIDTH = 32,
    parameter AHB_DATA_WIDTH = 32,
    parameter CLIENT_DATA_WIDTH = 32
  )
  (
  input logic clk,
  input logic rst_b,

  //ahb input
  input logic  [AHB_ADDR_WIDTH-1:0] haddr_i,
  input logic  [AHB_DATA_WIDTH-1:0] hwdata_i,
  input logic                       hsel_i,
  input logic                       hwrite_i,
  input logic                       hready_i,
  input logic  [1:0]                htrans_i,
  input logic  [2:0]                hsize_i,

  //ahb output
  output logic                      hresp_o,
  output logic                      hreadyout_o,
  output logic [AHB_DATA_WIDTH-1:0] hrdata_o


  );

  localparam DATA_WIDTH = 32;

//Signal Declarations
  logic zeroize_reg;
  logic [1:0] cmd_reg;

  abr_sampler_mode_e         sampler_mode;
  logic                      sha3_start;
  logic                      msg_start;
  logic                      msg_valid;
  logic                      msg_rdy;
  logic [MsgStrbW-1:0]       msg_strobe;
  logic [MsgWidth-1:0]       msg_data[Sha3Share];
  logic                      sampler_start;
  logic [ABR_MEM_ADDR_WIDTH-1:0] dest_base_addr;

  logic                        sampler_busy;
  logic                        sampler_state_dv;
  logic [sha3_pkg::StateW-1:0] sampler_state_data[Sha3Share];

  logic sampler_mem_dv;
  logic [ABR_MEM_DATA_WIDTH-1:0] sampler_mem_data;
  logic [ABR_MEM_ADDR_WIDTH-1:0] sampler_mem_addr;

  logic                                        sampler_ntt_dv;
  logic [COEFF_PER_CLK-1:0][DILITHIUM_Q_W-1:0] sampler_ntt_data;

  abr_ntt_mode_e ntt_mode;
  mode_t mode;
  logic accumulate;
  logic ntt_enable;
  ntt_mem_addr_t ntt_mem_base_addr;
  pwo_mem_addr_t pwo_mem_base_addr;
  mem_if_t mem_wr_req;
  mem_if_t mem_rd_req;
  logic [ABR_MEM_DATA_WIDTH-1:0] mem_wr_data;
  logic [ABR_MEM_DATA_WIDTH-1:0] mem_rd_data;
  mem_if_t pwm_a_rd_req;
  mem_if_t pwm_b_rd_req;
  logic [ABR_MEM_DATA_WIDTH-1:0] pwm_a_rd_data;
  logic [ABR_MEM_DATA_WIDTH-1:0] pwm_b_rd_data;
  logic ntt_done;
  logic ntt_busy;

  //gasket to assemble reg requests
  logic abr_reg_dv;
  logic [CLIENT_DATA_WIDTH-1:0] abr_reg_rdata;
  logic [AHB_ADDR_WIDTH-1:0]    abr_reg_addr;
  logic [AHB_DATA_WIDTH-1:0]    abr_reg_wdata;
  logic                         abr_reg_write;

  logic abr_reg_err, abr_reg_read_err, abr_reg_write_err;

  adamsbridge_reg__in_t abr_reg_hwif_in;
  adamsbridge_reg__out_t abr_reg_hwif_out;

  abr_ahb_slv_sif #(
    .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
    .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
    .CLIENT_DATA_WIDTH(CLIENT_DATA_WIDTH)
)
  abr_ahb_slv_inst (
    //AMBA AHB Lite INF
    .hclk(clk),
    .hreset_n(rst_b),
    .haddr_i(haddr_i),
    .hwdata_i(hwdata_i),
    .hsel_i(hsel_i),
    .hwrite_i(hwrite_i),
    .hready_i(hready_i),
    .htrans_i(htrans_i),
    .hsize_i(hsize_i),

    .hresp_o(hresp_o),
    .hreadyout_o(hreadyout_o),
    .hrdata_o(hrdata_o),

    //COMPONENT INF
    .dv(abr_reg_dv),
    .hld('0),
    .err(abr_reg_err),
    .write(abr_reg_write),
    .wdata(abr_reg_wdata),
    .addr(abr_reg_addr[AHB_ADDR_WIDTH-1:0]),

    .rdata(abr_reg_rdata)
);

always_comb abr_reg_err = abr_reg_read_err | abr_reg_write_err;

adamsbridge_reg adamsbridge_reg_inst (
  .clk(clk),
  .rst(rst_b),

  .s_cpuif_req(abr_reg_dv),
  .s_cpuif_req_is_wr(abr_reg_write),
  .s_cpuif_addr(abr_reg_addr[ADAMSBRIDGE_REG_ADDR_WIDTH-1:0]),
  .s_cpuif_wr_data(abr_reg_wdata),
  .s_cpuif_wr_biten('1),
  .s_cpuif_req_stall_wr(),
  .s_cpuif_req_stall_rd(),
  .s_cpuif_rd_ack(),
  .s_cpuif_rd_err(abr_reg_read_err),
  .s_cpuif_rd_data(abr_reg_rdata),
  .s_cpuif_wr_ack(),
  .s_cpuif_wr_err(abr_reg_write_err),

  .hwif_in(abr_reg_hwif_in),
  .hwif_out(abr_reg_hwif_out)
);

abr_ctrl abr_control_inst
(
  .clk(clk),
  .rst_b(rst_b),
  .zeroize(zeroize_reg),

  //control interface
  .abr_reg_hwif_in_o(abr_reg_hwif_in),
  .abr_reg_hwif_out_i(abr_reg_hwif_out),

  //sampler interface
  .sampler_mode_o(sampler_mode),
  .sha3_start_o(sha3_start), //start the sha3 engine
  .msg_start_o(msg_start), //start a new message
  .msg_valid_o(msg_valid), //msg interface valid
  .msg_rdy_i(msg_rdy),  //msg interface rdy (~hold)
  .msg_strobe_o(msg_strobe), //msg byte enables
  .msg_data_o(msg_data),

  .sampler_start_o(sampler_start),
  .dest_base_addr_o(dest_base_addr),

  .sampler_state_dv_i(sampler_state_dv),
  .sampler_state_data_i(sampler_state_data),
  .sampler_busy_i(sampler_busy),

  //ntt interface
  .ntt_enable_o(ntt_enable),
  .ntt_mode_o(ntt_mode),
  .ntt_mem_base_addr_o(ntt_mem_base_addr),
  .pwo_mem_base_addr_o(pwo_mem_base_addr),
  .ntt_busy_i(ntt_busy)
);

sampler_top sampler_top_inst
(
  .clk(clk),
  .rst_b(rst_b),
  .zeroize(zeroize_reg),

  .sampler_mode_i(sampler_mode),
  .sha3_start_i(sha3_start), //start the sha3 engine
  .msg_start_i(msg_start), //start a new message
  .msg_valid_i(msg_valid), //msg interface valid
  .msg_rdy_o(msg_rdy),  //msg interface rdy (~hold)
  .msg_strobe_i(msg_strobe), //msg byte enables
  .msg_data_i(msg_data), //msg data

  .sampler_start_i(sampler_start),
  .dest_base_addr_i(dest_base_addr),

  .sampler_busy_o(sampler_busy),

  .sampler_ntt_dv_o(sampler_ntt_dv),
  .sampler_ntt_data_o(sampler_ntt_data),

  .sampler_mem_dv_o(sampler_mem_dv),
  .sampler_mem_data_o(sampler_mem_data),
  .sampler_mem_addr_o(sampler_mem_addr),

  .sampler_state_dv_o(sampler_state_dv),
  .sampler_state_data_o(sampler_state_data)
);

logic sampler_valid;

//NTT
//gasket here, create common interfaces?
always_comb begin
  mode = '0;
  accumulate = '0;
  sampler_valid = 0;

  unique case (ntt_mode) inside
    ABR_NTT_NONE: begin
    end
    ABR_NTT: begin
      mode = ct;
    end
    ABR_INTT: begin
      mode = gs;
    end
    ABR_PWM: begin
      mode = pwm;
      sampler_valid = sampler_ntt_dv;
    end
    ABR_PWM_ACCUM: begin
      mode = pwm;
      accumulate = 1;
      sampler_valid = sampler_ntt_dv;
    end
    ABR_PWA: begin
      mode = pwa;
      sampler_valid = 1;
    end
    default: begin
    end
  endcase 
end

ntt_top #(
  .REG_SIZE(REG_SIZE),
  .DILITHIUM_Q(DILITHIUM_Q),
  .DILITHIUM_N(DILITHIUM_N),
  .MEM_ADDR_WIDTH(ABR_MEM_ADDR_WIDTH)
)
ntt_top_inst0 (
  .clk(clk),
  .reset_n(rst_b),
  .zeroize(zeroize_reg),

  .mode(mode),
  .ntt_enable(ntt_enable),
  .ntt_mem_base_addr(ntt_mem_base_addr),
  .pwo_mem_base_addr(pwo_mem_base_addr),
  .accumulate(accumulate),
  .sampler_valid(sampler_valid),
  //NTT mem IF
  .mem_wr_req(mem_wr_req),
  .mem_rd_req(mem_rd_req),
  .mem_wr_data(mem_wr_data),
  .mem_rd_data(mem_rd_data),
  //PWM mem IF
  .pwm_a_rd_req(pwm_a_rd_req),
  .pwm_b_rd_req(pwm_b_rd_req),
  .pwm_a_rd_data(pwm_a_rd_data),
  .pwm_b_rd_data(sampler_ntt_dv ? sampler_ntt_data : pwm_b_rd_data),
  .ntt_busy(ntt_busy),
  .ntt_done(ntt_done)
);

//MUX memory accesses
logic [1:0] abr_mem0_cs;
logic [1:0] abr_mem0_we;
logic [1:0][ABR_MEM_ADDR_WIDTH-2:0] abr_mem0_addr;
logic [1:0][ABR_MEM_DATA_WIDTH-1:0] abr_mem0_wdata;
logic [1:0][ABR_MEM_DATA_WIDTH-1:0] abr_mem0_rdata;

logic [1:0] abr_mem1_cs;
logic [1:0] abr_mem1_we;
logic [1:0][ABR_MEM_ADDR_WIDTH-2:0] abr_mem1_addr;
logic [1:0][ABR_MEM_DATA_WIDTH-1:0] abr_mem1_wdata;
logic [1:0][ABR_MEM_DATA_WIDTH-1:0] abr_mem1_rdata;

//FIXME common memory ports to make muxing easier
//this is really ugly - settle memory architecture and do this better
logic sampler_mem0_cs, sampler_mem1_cs;
logic [1:0] ntt_mem0_cs, ntt_mem1_cs;
logic [1:0] pwo_mem0_cs, pwo_mem1_cs;
logic [1:0] ntt_mem0_cs_f, ntt_mem1_cs_f;
logic [1:0] pwo_mem0_cs_f, pwo_mem1_cs_f;
 
always_ff @(posedge clk or negedge rst_b) begin : read_mux_flops
  if (!rst_b) begin
    ntt_mem0_cs_f <= 0;
    ntt_mem1_cs_f <= 0;
    pwo_mem0_cs_f <= 0;
    pwo_mem1_cs_f <= 0;
  end
  else begin
    ntt_mem0_cs_f <= ntt_mem0_cs;
    ntt_mem1_cs_f <= ntt_mem1_cs;
    pwo_mem0_cs_f <= pwo_mem0_cs;
    pwo_mem1_cs_f <= pwo_mem1_cs;
  end
end  

always_comb sampler_mem0_cs = (sampler_mem_dv & ~sampler_mem_addr[ABR_MEM_ADDR_WIDTH-1]);
always_comb sampler_mem1_cs = (sampler_mem_dv &  sampler_mem_addr[ABR_MEM_ADDR_WIDTH-1]);

always_comb ntt_mem0_cs[0] = ((mem_wr_req.rd_wr_en != RW_IDLE) & ~mem_wr_req.addr[ABR_MEM_ADDR_WIDTH-1]);
always_comb ntt_mem0_cs[1] = ((mem_rd_req.rd_wr_en != RW_IDLE) & ~mem_rd_req.addr[ABR_MEM_ADDR_WIDTH-1]);
always_comb ntt_mem1_cs[0] = ((mem_wr_req.rd_wr_en != RW_IDLE) &  mem_wr_req.addr[ABR_MEM_ADDR_WIDTH-1]);
always_comb ntt_mem1_cs[1] = ((mem_rd_req.rd_wr_en != RW_IDLE) &  mem_rd_req.addr[ABR_MEM_ADDR_WIDTH-1]);

always_comb pwo_mem0_cs[0] = ((pwm_a_rd_req.rd_wr_en != RW_IDLE) & ~pwm_a_rd_req.addr[ABR_MEM_ADDR_WIDTH-1]);
always_comb pwo_mem0_cs[1] = ((pwm_b_rd_req.rd_wr_en != RW_IDLE) & ~pwm_b_rd_req.addr[ABR_MEM_ADDR_WIDTH-1]);
always_comb pwo_mem1_cs[0] = ((pwm_a_rd_req.rd_wr_en != RW_IDLE) &  pwm_a_rd_req.addr[ABR_MEM_ADDR_WIDTH-1]);
always_comb pwo_mem1_cs[1] = ((pwm_b_rd_req.rd_wr_en != RW_IDLE) &  pwm_b_rd_req.addr[ABR_MEM_ADDR_WIDTH-1]);


always_comb mem_rd_data = ({ABR_MEM_DATA_WIDTH{ntt_mem0_cs_f[1]}} & abr_mem0_rdata[1]) | 
                          ({ABR_MEM_DATA_WIDTH{ntt_mem1_cs_f[1]}} & abr_mem1_rdata[1]);
always_comb pwm_a_rd_data = ({ABR_MEM_DATA_WIDTH{pwo_mem0_cs_f[0]}} & abr_mem0_rdata[1]) | 
                            ({ABR_MEM_DATA_WIDTH{pwo_mem1_cs_f[0]}} & abr_mem1_rdata[1]);
always_comb pwm_b_rd_data = ({ABR_MEM_DATA_WIDTH{pwo_mem0_cs_f[1]}} & abr_mem0_rdata[1]) | 
                            ({ABR_MEM_DATA_WIDTH{pwo_mem1_cs_f[1]}} & abr_mem1_rdata[1]);

//memory 0 port 0
always_comb begin
  abr_mem0_cs[0] = sampler_mem0_cs | ntt_mem0_cs[0] | pwo_mem0_cs[0];
  abr_mem0_we[0] = sampler_mem0_cs | 
                   ((mem_wr_req.rd_wr_en == RW_WRITE) & ntt_mem0_cs[0]);
  abr_mem0_addr[0] = ({ABR_MEM_ADDR_WIDTH-1{sampler_mem0_cs}} & sampler_mem_addr[ABR_MEM_ADDR_WIDTH-2:0]) | 
                     ({ABR_MEM_ADDR_WIDTH-1{ntt_mem0_cs[0]}} & mem_wr_req.addr[ABR_MEM_ADDR_WIDTH-2:0]) |
                     ({ABR_MEM_ADDR_WIDTH-1{pwo_mem0_cs[0]}} & pwm_a_rd_req.addr[ABR_MEM_ADDR_WIDTH-2:0]);
  abr_mem0_wdata[0] = ({ABR_MEM_DATA_WIDTH{sampler_mem0_cs}} & sampler_mem_data) |
                      ({ABR_MEM_DATA_WIDTH{ntt_mem0_cs[0]}} & mem_wr_data);
end

//memory 0 port 1
always_comb begin
  abr_mem0_cs[1] = ntt_mem0_cs[1] | pwo_mem0_cs[1];
  abr_mem0_we[1] = 0;
  abr_mem0_addr[1] = ({ABR_MEM_ADDR_WIDTH-1{ntt_mem0_cs[1]}} & mem_rd_req.addr[ABR_MEM_ADDR_WIDTH-2:0]) |
                     ({ABR_MEM_ADDR_WIDTH-1{pwo_mem0_cs[1]}} & pwm_b_rd_req.addr[ABR_MEM_ADDR_WIDTH-2:0]);
  abr_mem0_wdata[1] = 0;
end

abr_sram
#(
  .DEPTH(ABR_MEM_INST_DEPTH),
  .DATA_WIDTH(ABR_MEM_DATA_WIDTH),
  .NUM_PORTS(2)
) abr_sram_inst0
(
  .clk_i(clk),
  .cs_i(abr_mem0_cs),
  .we_i(abr_mem0_we),
  .addr_i(abr_mem0_addr),
  .wdata_i(abr_mem0_wdata),
  .rdata_o(abr_mem0_rdata)
);

//memory 1 port 0
always_comb begin
  abr_mem1_cs[0] = sampler_mem1_cs | ntt_mem1_cs[0] | pwo_mem1_cs[0];
  abr_mem1_we[0] = sampler_mem1_cs | 
                   ((mem_wr_req.rd_wr_en == RW_WRITE) & ntt_mem1_cs[0]);
  abr_mem1_addr[0] = ({ABR_MEM_ADDR_WIDTH-1{sampler_mem1_cs}} & sampler_mem_addr[ABR_MEM_ADDR_WIDTH-2:0]) | 
                     ({ABR_MEM_ADDR_WIDTH-1{ntt_mem1_cs[0]}} & mem_wr_req.addr[ABR_MEM_ADDR_WIDTH-2:0]) |
                     ({ABR_MEM_ADDR_WIDTH-1{pwo_mem1_cs[0]}} & pwm_a_rd_req.addr[ABR_MEM_ADDR_WIDTH-2:0]);
  abr_mem1_wdata[0] = ({ABR_MEM_DATA_WIDTH{sampler_mem1_cs}} & sampler_mem_data) |
                      ({ABR_MEM_DATA_WIDTH{ntt_mem1_cs[0]}} & mem_wr_data);
end

//memory 1 port 1
always_comb begin
  abr_mem1_cs[1] = ntt_mem1_cs[1] | pwo_mem1_cs[1];
  abr_mem1_we[1] = 0;
  abr_mem1_addr[1] = ({ABR_MEM_ADDR_WIDTH-1{ntt_mem1_cs[1]}} & mem_rd_req.addr[ABR_MEM_ADDR_WIDTH-2:0]) |
                     ({ABR_MEM_ADDR_WIDTH-1{pwo_mem1_cs[1]}} & pwm_b_rd_req.addr[ABR_MEM_ADDR_WIDTH-2:0]);
  abr_mem1_wdata[1] = 0;
end

abr_sram
#(
  .DEPTH(ABR_MEM_INST_DEPTH),
  .DATA_WIDTH(ABR_MEM_DATA_WIDTH),
  .NUM_PORTS(2)
) abr_sram_inst1
(
  .clk_i(clk),
  .cs_i(abr_mem1_cs),
  .we_i(abr_mem1_we),
  .addr_i(abr_mem1_addr),
  .wdata_i(abr_mem1_wdata),
  .rdata_o(abr_mem1_rdata)
);

`ABR_ASSERT_MUTEX(ERR_MEM0_0_ACCESS_MUTEX, {sampler_mem0_cs,ntt_mem0_cs[0],pwo_mem0_cs[0]}, clk, !rst_b)
`ABR_ASSERT_MUTEX(ERR_MEM0_1_ACCESS_MUTEX, {ntt_mem0_cs[1],pwo_mem0_cs[1]}, clk, !rst_b)  
`ABR_ASSERT_MUTEX(ERR_MEM1_0_ACCESS_MUTEX, {sampler_mem1_cs,ntt_mem1_cs[0],pwo_mem1_cs[0]}, clk, !rst_b)
`ABR_ASSERT_MUTEX(ERR_MEM1_1_ACCESS_MUTEX, {ntt_mem1_cs[1],pwo_mem1_cs[1]}, clk, !rst_b)

`ABR_ASSERT_KNOWN(ERR_MEM0_0_WDATA_X, {abr_mem0_wdata[0]}, clk, !rst_b, (abr_mem0_cs[0] &  abr_mem0_we[0]))
`ABR_ASSERT_KNOWN(ERR_MEM0_1_WDATA_X, {abr_mem0_wdata[1]}, clk, !rst_b, (abr_mem0_cs[1] &  abr_mem0_we[1]))
`ABR_ASSERT_KNOWN(ERR_MEM1_0_WDATA_X, {abr_mem1_wdata[0]}, clk, !rst_b, (abr_mem1_cs[0] &  abr_mem1_we[0]))
`ABR_ASSERT_KNOWN(ERR_MEM1_1_WDATA_X, {abr_mem1_wdata[1]}, clk, !rst_b, (abr_mem1_cs[1] &  abr_mem1_we[1]))

endmodule