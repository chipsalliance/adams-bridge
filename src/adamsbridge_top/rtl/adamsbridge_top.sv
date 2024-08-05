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
  import abr_ctrl_pkg::*;
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

  logic [1:0]                                  sampler_ntt_dv;
  logic [1:0]                                  sampler_valid;
  logic [COEFF_PER_CLK-1:0][DILITHIUM_Q_W-1:0] sampler_ntt_data;

  abr_ntt_mode_e [1:0] ntt_mode;
  mode_t [1:0] mode;
  logic [1:0] accumulate;
  logic [1:0] ntt_enable;
  ntt_mem_addr_t [1:0] ntt_mem_base_addr;
  pwo_mem_addr_t [1:0] pwo_mem_base_addr;
  mem_if_t [1:0] mem_wr_req;
  mem_if_t [1:0] mem_rd_req;
  logic [1:0][ABR_MEM_DATA_WIDTH-1:0] mem_wr_data;
  logic [1:0][ABR_MEM_DATA_WIDTH-1:0] mem_rd_data;
  mem_if_t [1:0] pwm_a_rd_req;
  mem_if_t [1:0] pwm_b_rd_req;
  logic [1:0][ABR_MEM_DATA_WIDTH-1:0] pwm_a_rd_data;
  logic [1:0][ABR_MEM_DATA_WIDTH-1:0] pwm_b_rd_data;
  logic [1:0] ntt_done;
  logic [1:0] ntt_busy;

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

  .sampler_ntt_dv_o(sampler_ntt_dv[0]),
  .sampler_ntt_data_o(sampler_ntt_data),

  .sampler_mem_dv_o(sampler_mem_dv),
  .sampler_mem_data_o(sampler_mem_data),
  .sampler_mem_addr_o(sampler_mem_addr),

  .sampler_state_dv_o(sampler_state_dv),
  .sampler_state_data_o(sampler_state_data)
);

assign sampler_ntt_dv[1] = 0; //no sampler interface to secondary ntt

generate
  for (genvar g_inst = 0; g_inst < 2; g_inst++) begin
    //NTT
    //gasket here, create common interfaces?
    always_comb begin
      mode[g_inst] = '0;
      accumulate[g_inst] = '0;
      sampler_valid[g_inst] = 0;

      unique case (ntt_mode[g_inst]) inside
        ABR_NTT_NONE: begin
        end
        ABR_NTT: begin
          mode[g_inst] = ct;
        end
        ABR_INTT: begin
          mode[g_inst] = gs;
        end
        ABR_PWM_SMPL: begin
          mode[g_inst] = pwm;
          sampler_valid[g_inst] = sampler_ntt_dv[g_inst];
        end
        ABR_PWM_ACCUM_SMPL: begin
          mode[g_inst] = pwm;
          accumulate[g_inst] = 1;
          sampler_valid[g_inst] = sampler_ntt_dv[g_inst];
        end
        ABR_PWM: begin
          mode[g_inst] = pwm;
          sampler_valid[g_inst] = 1;
        end
        ABR_PWM_ACCUM: begin
          mode[g_inst] = pwm;
          accumulate[g_inst] = 1;
          sampler_valid[g_inst] = 1;
        end
        ABR_PWA: begin
          mode[g_inst] = pwa;
          sampler_valid[g_inst] = 1;
        end
        ABR_PWS: begin
          mode[g_inst] = pws;
          sampler_valid[g_inst] = 1;
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

    .mode(mode[g_inst]),
    .ntt_enable(ntt_enable[g_inst]),
    .ntt_mem_base_addr(ntt_mem_base_addr[g_inst]),
    .pwo_mem_base_addr(pwo_mem_base_addr[g_inst]),
    .accumulate(accumulate[g_inst]),
    .sampler_valid(sampler_valid[g_inst]),
    //NTT mem IF
    .mem_wr_req(mem_wr_req[g_inst]),
    .mem_rd_req(mem_rd_req[g_inst]),
    .mem_wr_data(mem_wr_data[g_inst]),
    .mem_rd_data(mem_rd_data[g_inst]),
    //PWM mem IF
    .pwm_a_rd_req(pwm_a_rd_req[g_inst]),
    .pwm_b_rd_req(pwm_b_rd_req[g_inst]),
    .pwm_a_rd_data(pwm_a_rd_data[g_inst]),
    .pwm_b_rd_data(sampler_ntt_dv[g_inst] ? sampler_ntt_data : pwm_b_rd_data[g_inst]),
    .ntt_busy(ntt_busy[g_inst]),
    .ntt_done(ntt_done[g_inst])
  );
  end
endgenerate

//MUX memory accesses
logic [3:0] abr_mem_re;
logic [3:0][ABR_MEM_ADDR_WIDTH-3:0] abr_mem_raddr;
logic [3:0][ABR_MEM_DATA_WIDTH-1:0] abr_mem_rdata;
logic [3:0] abr_mem_we;
logic [3:0][ABR_MEM_ADDR_WIDTH-3:0] abr_mem_waddr;
logic [3:0][ABR_MEM_DATA_WIDTH-1:0] abr_mem_wdata;


//FIXME common memory ports to make muxing easier
//this is better - common interfaces will help clean this up further

logic [3:0] sampler_mem_we;
logic [1:0][3:0] ntt_mem_we;

logic [1:0][3:0] ntt_mem_re;
logic [1:0][3:0] pwo_a_mem_re;
logic [1:0][3:0] pwo_b_mem_re;
logic [1:0][3:0] ntt_mem_re_f;
logic [1:0][3:0] pwo_a_mem_re_f;
logic [1:0][3:0] pwo_b_mem_re_f;

//Write Muxes
always_comb begin
  for (int i = 0; i < 4; i++) begin
    sampler_mem_we[i] = sampler_mem_dv & (sampler_mem_addr[ABR_MEM_ADDR_WIDTH-1:ABR_MEM_ADDR_WIDTH-2] == i[1:0]);
    ntt_mem_we[0][i] = (mem_wr_req[0].rd_wr_en == RW_WRITE) & (mem_wr_req[0].addr[ABR_MEM_ADDR_WIDTH-1:ABR_MEM_ADDR_WIDTH-2] == i[1:0]);
    ntt_mem_we[1][i] = (mem_wr_req[1].rd_wr_en == RW_WRITE) & (mem_wr_req[1].addr[ABR_MEM_ADDR_WIDTH-1:ABR_MEM_ADDR_WIDTH-2] == i[1:0]);

    abr_mem_we[i] = sampler_mem_we[i] | ntt_mem_we[0][i] | ntt_mem_we[1][i];
    abr_mem_waddr[i] = ({ABR_MEM_ADDR_WIDTH-2{sampler_mem_we[i]}} & sampler_mem_addr[ABR_MEM_ADDR_WIDTH-3:0]) |
                       ({ABR_MEM_ADDR_WIDTH-2{ntt_mem_we[0][i]}}  & mem_wr_req[0].addr[ABR_MEM_ADDR_WIDTH-3:0]) |
                       ({ABR_MEM_ADDR_WIDTH-2{ntt_mem_we[1][i]}}  & mem_wr_req[1].addr[ABR_MEM_ADDR_WIDTH-3:0]);
    abr_mem_wdata[i] = ({ABR_MEM_DATA_WIDTH{sampler_mem_we[i]}}   & sampler_mem_data) |
                       ({ABR_MEM_DATA_WIDTH{ntt_mem_we[0][i]}}    & mem_wr_data[0]) |
                       ({ABR_MEM_DATA_WIDTH{ntt_mem_we[1][i]}}    & mem_wr_data[1]);
  end
end

//Read Muxes
always_comb begin
  for (int i = 0; i < 4; i++) begin
    ntt_mem_re[0][i]   = (mem_rd_req[0].rd_wr_en == RW_READ) & (mem_rd_req[0].addr[ABR_MEM_ADDR_WIDTH-1:ABR_MEM_ADDR_WIDTH-2] == i[1:0]);
    pwo_a_mem_re[0][i] = (pwm_a_rd_req[0].rd_wr_en == RW_READ) & (pwm_a_rd_req[0].addr[ABR_MEM_ADDR_WIDTH-1:ABR_MEM_ADDR_WIDTH-2] == i[1:0]);
    pwo_b_mem_re[0][i] = ~sampler_ntt_dv & (pwm_b_rd_req[0].rd_wr_en == RW_READ) & (pwm_b_rd_req[0].addr[ABR_MEM_ADDR_WIDTH-1:ABR_MEM_ADDR_WIDTH-2] == i[1:0]);

    ntt_mem_re[1][i]   = (mem_rd_req[1].rd_wr_en == RW_READ) & (mem_rd_req[1].addr[ABR_MEM_ADDR_WIDTH-1:ABR_MEM_ADDR_WIDTH-2] == i[1:0]);
    pwo_a_mem_re[1][i] = (pwm_a_rd_req[1].rd_wr_en == RW_READ) & (pwm_a_rd_req[1].addr[ABR_MEM_ADDR_WIDTH-1:ABR_MEM_ADDR_WIDTH-2] == i[1:0]);
    pwo_b_mem_re[1][i] = (pwm_b_rd_req[1].rd_wr_en == RW_READ) & (pwm_b_rd_req[1].addr[ABR_MEM_ADDR_WIDTH-1:ABR_MEM_ADDR_WIDTH-2] == i[1:0]);

    abr_mem_re[i] = ntt_mem_re[0][i] | pwo_a_mem_re[0][i] | pwo_b_mem_re[0][i] |
                    ntt_mem_re[1][i] | pwo_a_mem_re[1][i] | pwo_b_mem_re[1][i];
    abr_mem_raddr[i] = ({ABR_MEM_ADDR_WIDTH-2{ntt_mem_re[0][i]}}   & mem_rd_req[0].addr[ABR_MEM_ADDR_WIDTH-3:0])   |
                       ({ABR_MEM_ADDR_WIDTH-2{pwo_a_mem_re[0][i]}} & pwm_a_rd_req[0].addr[ABR_MEM_ADDR_WIDTH-3:0]) |
                       ({ABR_MEM_ADDR_WIDTH-2{pwo_b_mem_re[0][i]}} & pwm_b_rd_req[0].addr[ABR_MEM_ADDR_WIDTH-3:0]) |
                       ({ABR_MEM_ADDR_WIDTH-2{ntt_mem_re[1][i]}}   & mem_rd_req[1].addr[ABR_MEM_ADDR_WIDTH-3:0])   |
                       ({ABR_MEM_ADDR_WIDTH-2{pwo_a_mem_re[1][i]}} & pwm_a_rd_req[1].addr[ABR_MEM_ADDR_WIDTH-3:0]) |
                       ({ABR_MEM_ADDR_WIDTH-2{pwo_b_mem_re[1][i]}} & pwm_b_rd_req[1].addr[ABR_MEM_ADDR_WIDTH-3:0]);
  end
end

//Align read enables
always_ff @(posedge clk or negedge rst_b) begin : read_mux_flops
  if (!rst_b) begin
    ntt_mem_re_f <= 0;
    pwo_a_mem_re_f <= 0;
    pwo_b_mem_re_f <= 0;
  end
  else begin
    ntt_mem_re_f <= ntt_mem_re;
    pwo_a_mem_re_f<= pwo_a_mem_re;
    pwo_b_mem_re_f <= pwo_b_mem_re;
  end
end  

//Read data muxes
always_comb begin
  mem_rd_data = 0;
  pwm_a_rd_data = 0;
  pwm_b_rd_data = 0;

  for (int i = 0; i < 2; i++) begin
    for (int j = 0; j < 4; j++) begin
      mem_rd_data[i] |= ({ABR_MEM_DATA_WIDTH{ntt_mem_re_f[i][j]}} & abr_mem_rdata[j]);
      pwm_a_rd_data[i] |= ({ABR_MEM_DATA_WIDTH{pwo_a_mem_re_f[i][j]}} & abr_mem_rdata[j]);
      pwm_b_rd_data[i] |= ({ABR_MEM_DATA_WIDTH{pwo_b_mem_re_f[i][j]}} & abr_mem_rdata[j]);
    end
  end
end

abr_1r1w_ram
#(
  .DEPTH(ABR_MEM_INST0_DEPTH),
  .DATA_WIDTH(ABR_MEM_DATA_WIDTH)
) abr_sram_inst0
(
  .clk_i(clk),
  .we_i(abr_mem_we[0]),
  .waddr_i(abr_mem_waddr[0][ABR_MEM_INST0_ADDR_W-1:0]),
  .wdata_i(abr_mem_wdata[0]),
  .re_i(abr_mem_re[0]),
  .raddr_i(abr_mem_raddr[0][ABR_MEM_INST0_ADDR_W-1:0]),
  .rdata_o(abr_mem_rdata[0])
);

abr_1r1w_ram
#(
  .DEPTH(ABR_MEM_INST1_DEPTH),
  .DATA_WIDTH(ABR_MEM_DATA_WIDTH)
) abr_sram_inst1
(
  .clk_i(clk),
  .we_i(abr_mem_we[1]),
  .waddr_i(abr_mem_waddr[1][ABR_MEM_INST1_ADDR_W-1:0]),
  .wdata_i(abr_mem_wdata[1]),
  .re_i(abr_mem_re[1]),
  .raddr_i(abr_mem_raddr[1][ABR_MEM_INST1_ADDR_W-1:0]),
  .rdata_o(abr_mem_rdata[1])
);

abr_1r1w_ram
#(
  .DEPTH(ABR_MEM_INST2_DEPTH),
  .DATA_WIDTH(ABR_MEM_DATA_WIDTH)
) abr_sram_inst2
(
  .clk_i(clk),
  .we_i(abr_mem_we[2]),
  .waddr_i(abr_mem_waddr[2][ABR_MEM_INST2_ADDR_W-1:0]),
  .wdata_i(abr_mem_wdata[2]),
  .re_i(abr_mem_re[2]),
  .raddr_i(abr_mem_raddr[2][ABR_MEM_INST2_ADDR_W-1:0]),
  .rdata_o(abr_mem_rdata[2])
);

abr_1r1w_ram
#(
  .DEPTH(ABR_MEM_INST3_DEPTH),
  .DATA_WIDTH(ABR_MEM_DATA_WIDTH)
) abr_sram_inst3
(
  .clk_i(clk),
  .we_i(abr_mem_we[3]),
  .waddr_i(abr_mem_waddr[3][ABR_MEM_INST3_ADDR_W-1:0]),
  .wdata_i(abr_mem_wdata[3]),
  .re_i(abr_mem_re[3]),
  .raddr_i(abr_mem_raddr[3][ABR_MEM_INST3_ADDR_W-1:0]),
  .rdata_o(abr_mem_rdata[3])
);




`ABR_ASSERT_MUTEX(ERR_MEM_0_RD_ACCESS_MUTEX, {ntt_mem_re[0][0],pwo_a_mem_re[0][0],pwo_b_mem_re[0][0],ntt_mem_re[1][0],pwo_a_mem_re[1][0],pwo_b_mem_re[1][0]}, clk, !rst_b)
`ABR_ASSERT_MUTEX(ERR_MEM_1_RD_ACCESS_MUTEX, {ntt_mem_re[0][1],pwo_a_mem_re[0][1],pwo_b_mem_re[0][1],ntt_mem_re[1][1],pwo_a_mem_re[1][1],pwo_b_mem_re[1][1]}, clk, !rst_b)
`ABR_ASSERT_MUTEX(ERR_MEM_2_RD_ACCESS_MUTEX, {ntt_mem_re[0][2],pwo_a_mem_re[0][2],pwo_b_mem_re[0][2],ntt_mem_re[1][2],pwo_a_mem_re[1][2],pwo_b_mem_re[1][2]}, clk, !rst_b)
`ABR_ASSERT_MUTEX(ERR_MEM_3_RD_ACCESS_MUTEX, {ntt_mem_re[0][3],pwo_a_mem_re[0][3],pwo_b_mem_re[0][3],ntt_mem_re[1][3],pwo_a_mem_re[1][3],pwo_b_mem_re[1][3]}, clk, !rst_b)

`ABR_ASSERT_MUTEX(ERR_MEM_0_WR_ACCESS_MUTEX, {sampler_mem_we[0],ntt_mem_we[0][0],ntt_mem_we[1][0]}, clk, !rst_b)
`ABR_ASSERT_MUTEX(ERR_MEM_1_WR_ACCESS_MUTEX, {sampler_mem_we[1],ntt_mem_we[0][1],ntt_mem_we[1][1]}, clk, !rst_b)
`ABR_ASSERT_MUTEX(ERR_MEM_2_WR_ACCESS_MUTEX, {sampler_mem_we[2],ntt_mem_we[0][2],ntt_mem_we[1][2]}, clk, !rst_b)
`ABR_ASSERT_MUTEX(ERR_MEM_3_WR_ACCESS_MUTEX, {sampler_mem_we[3],ntt_mem_we[0][3],ntt_mem_we[1][3]}, clk, !rst_b)

//`ABR_ASSERT_KNOWN(ERR_MEM_0_WDATA_X, {abr_mem_wdata[0]}, clk, !rst_b, abr_mem_we[0])
//`ABR_ASSERT_KNOWN(ERR_MEM_1_WDATA_X, {abr_mem_wdata[1]}, clk, !rst_b, abr_mem_we[1])
//`ABR_ASSERT_KNOWN(ERR_MEM_2_WDATA_X, {abr_mem_wdata[2]}, clk, !rst_b, abr_mem_we[2])
//`ABR_ASSERT_KNOWN(ERR_MEM_3_WDATA_X, {abr_mem_wdata[3]}, clk, !rst_b, abr_mem_we[3])

//`ABR_ASSERT_KNOWN(ERR_MEM_0_RDATA_X, {mem_rd_data}, clk, !rst_b)
//`ABR_ASSERT_KNOWN(ERR_MEM_1_RDATA_X, {pwm_a_rd_data}, clk, !rst_b)
//`ABR_ASSERT_KNOWN(ERR_MEM_2_RDATA_X, {pwm_b_rd_data}, clk, !rst_b)

endmodule
