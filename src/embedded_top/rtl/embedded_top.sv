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

module embedded_top
  import sha3_pkg::*;
  import abr_prim_alert_pkg::*;
  import adamsbridge_reg_pkg::*;
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

//Signal Declarations
  logic zeroize;

  logic                    msg_start;
  logic                    msg_valid;
  logic [MsgStrbW-1:0]     msg_strobe;
  logic [MsgWidth-1:0]     msg_data[Sha3Share];
  logic                    sha3_msg_rdy;
  logic                    sha3_start;
  logic                    sha3_process;
  logic                    sha3_run;

  abr_prim_mubi_pkg::mubi4_t    sha3_done;
  abr_prim_mubi_pkg::mubi4_t    sha3_absorbed;

  logic sha3_squeezing;

  logic sha3_block_processed;

  sha3_pkg::sha3_st_e sha3_fsm;
  sha3_pkg::err_t sha3_err;

  sha3_pkg::sha3_mode_e mode;
  sha3_pkg::keccak_strength_e strength;

  logic sha3_state_vld;
  logic [sha3_pkg::StateW-1:0] sha3_state[Sha3Share];

  logic sha3_state_error;
  logic sha3_count_error;
  logic sha3_rst_storage_err;

  //rej sampler
  logic                                            sha3_rejs_dv;
  logic                                            rejs_sha3_hold;
  logic [REJS_PISO_INPUT_RATE-1:0]                 sha3_rejs_data;

  logic                                            rejs_piso_dv;
  logic                                            rejs_piso_hold;
  logic [REJS_NUM_SAMPLERS-1:0][REJS_SAMPLE_W-1:0] rejs_piso_data;

  logic                                            rejs_dv_o;
  logic [REJS_VLD_SAMPLES-1:0][DILITHIUM_Q_W-1:0]  rejs_data_o;

  //rej bounded
  logic                                               sha3_rejb_dv;
  logic                                               rejb_sha3_hold;
  logic [REJB_PISO_INPUT_RATE-1:0]                    sha3_rejb_data;

  logic                                               rejb_piso_dv;
  logic                                               rejb_piso_hold;
  logic [REJB_NUM_SAMPLERS-1:0][REJB_SAMPLE_W-1:0]    rejb_piso_data;

  logic                                               rejb_dv_o;
  logic [REJB_VLD_SAMPLES-1:0][DILITHIUM_Q_W-1:0]     rejb_data_o;

  //exp mask
  logic                                             sha3_exp_dv;
  logic                                             exp_sha3_hold;
  logic [EXP_PISO_INPUT_RATE-1:0]                   sha3_exp_data;

  logic                                             exp_piso_dv;
  logic                                             exp_piso_hold;
  logic [EXP_NUM_SAMPLERS-1:0][EXP_SAMPLE_W-1:0]    exp_piso_data;

  logic                                             exp_dv_o;
  logic [EXP_VLD_SAMPLES-1:0][EXP_VLD_SAMPLE_W-1:0] exp_data_o;

  //sample in ball
  logic                                          sha3_sib_dv;
  logic                                          sib_sha3_hold;
  logic [SIB_PISO_INPUT_RATE-1:0]                sha3_sib_data;

  logic                                          sib_piso_dv;
  logic                                          sib_piso_hold;
  logic [SIB_NUM_SAMPLERS-1:0][SIB_SAMPLE_W-1:0] sib_piso_data;

  logic                                          sib_done;

  logic [1:0]                                    sib_mem_we;
  logic [1:0][7:2]                               sib_mem_addr;
  logic [1:0][3:0][DILITHIUM_Q_W-2:0]            sib_mem_wrdata;
  logic [1:0][3:0][DILITHIUM_Q_W-2:0]            sib_mem_rddata;

  logic zeroize_reg;

  //gasket to assemble reg requests
  logic abr_reg_dv;
  logic [CLIENT_DATA_WIDTH-1:0] abr_reg_rdata;
  logic [AHB_ADDR_WIDTH-1:0]    abr_reg_addr;
  logic [AHB_DATA_WIDTH-1:0]    abr_reg_wdata;
  logic                         abr_reg_write;

  logic abr_reg_err, abr_reg_read_err, abr_reg_write_err;

  adamsbridge_reg__in_t abr_reg_hwif_in;
  adamsbridge_reg__out_t abr_reg_hwif_out;

  ahb_slv_sif #(
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

//HWIF to reg block
always_comb abr_reg_hwif_in.reset_b = rst_b;
always_comb abr_reg_hwif_in.hard_reset_b = rst_b;
always_comb abr_reg_hwif_in.adamsbridge_ready = '1;
always_comb abr_reg_hwif_in.ADAMSBRIDGE_CTRL.CTRL.hwclr = zeroize_reg;

always_comb abr_reg_hwif_in.ADAMSBRIDGE_NAME[0].NAME.next = '0;
always_comb abr_reg_hwif_in.ADAMSBRIDGE_NAME[1].NAME.next = '0;
always_comb abr_reg_hwif_in.ADAMSBRIDGE_VERSION[0].VERSION.next = '0;
always_comb abr_reg_hwif_in.ADAMSBRIDGE_VERSION[1].VERSION.next = '0;

always_comb abr_reg_hwif_in.ADAMSBRIDGE_STATUS.READY.next = '1;
always_comb abr_reg_hwif_in.ADAMSBRIDGE_STATUS.VALID.next = '0;

always_comb abr_reg_hwif_in.intr_block_rf.error_internal_intr_r.error_internal_sts.hwset = '0;
always_comb abr_reg_hwif_in.intr_block_rf.notif_internal_intr_r.notif_cmd_done_sts.hwset = '0;

always_comb zeroize_reg = abr_reg_hwif_out.ADAMSBRIDGE_CTRL.ZEROIZE.value;

always_comb begin // adamsbridge reg writing
  for (int dword=0; dword < 1216; dword++)begin
      abr_reg_hwif_in.ADAMSBRIDGE_PRIVKEY_IN[dword].PRIVKEY_IN.we = '0;
      abr_reg_hwif_in.ADAMSBRIDGE_PRIVKEY_IN[dword].PRIVKEY_IN.next = '0;
      abr_reg_hwif_in.ADAMSBRIDGE_PRIVKEY_IN[dword].PRIVKEY_IN.hwclr = zeroize_reg;
  end 

  for (int dword=0; dword < 1216; dword++)begin
      abr_reg_hwif_in.ADAMSBRIDGE_PRIVKEY_OUT[dword].PRIVKEY_OUT.we = '0;
      abr_reg_hwif_in.ADAMSBRIDGE_PRIVKEY_OUT[dword].PRIVKEY_OUT.next = '0;
      abr_reg_hwif_in.ADAMSBRIDGE_PRIVKEY_OUT[dword].PRIVKEY_OUT.hwclr = zeroize_reg;
  end

  for (int dword=0; dword < 648; dword++)begin
      abr_reg_hwif_in.ADAMSBRIDGE_PUBKEY[dword].PUBKEY.we = '0;
      abr_reg_hwif_in.ADAMSBRIDGE_PUBKEY[dword].PUBKEY.next = '0;
      abr_reg_hwif_in.ADAMSBRIDGE_PUBKEY[dword].PUBKEY.hwclr = zeroize_reg;
  end

  for (int dword=0; dword < 8; dword++)begin
      abr_reg_hwif_in.ADAMSBRIDGE_SEED[dword].SEED.we = '0;
      abr_reg_hwif_in.ADAMSBRIDGE_SEED[dword].SEED.next = '0;
      abr_reg_hwif_in.ADAMSBRIDGE_SEED[dword].SEED.hwclr = zeroize_reg;
  end

  for (int dword=0; dword < 16; dword++)begin
      abr_reg_hwif_in.ADAMSBRIDGE_MSG[dword].MSG.we = '0;
      abr_reg_hwif_in.ADAMSBRIDGE_MSG[dword].MSG.next = '0;
      abr_reg_hwif_in.ADAMSBRIDGE_MSG[dword].MSG.hwclr = zeroize_reg;
  end

  for (int dword=0; dword < 1149; dword++)begin
      abr_reg_hwif_in.ADAMSBRIDGE_SIGNATURE[dword].SIGNATURE.we = '0;
      abr_reg_hwif_in.ADAMSBRIDGE_SIGNATURE[dword].SIGNATURE.next = '0;
      abr_reg_hwif_in.ADAMSBRIDGE_SIGNATURE[dword].SIGNATURE.hwclr = zeroize_reg;
  end

  for (int dword=0; dword < 8; dword++)begin
      abr_reg_hwif_in.ADAMSBRIDGE_SIGN_RND[dword].SIGN_RND.hwclr = zeroize_reg;
  end

  for (int dword=0; dword < 16; dword++)begin 
      abr_reg_hwif_in.ADAMSBRIDGE_VERIFY_RES[dword].VERIFY_RES.we = '0;       
      abr_reg_hwif_in.ADAMSBRIDGE_VERIFY_RES[dword].VERIFY_RES.next = '0;
      abr_reg_hwif_in.ADAMSBRIDGE_VERIFY_RES[dword].VERIFY_RES.hwclr = zeroize_reg;
  end

  for (int dword=0; dword < 16; dword++)begin
      abr_reg_hwif_in.ADAMSBRIDGE_IV[dword].IV.hwclr = zeroize_reg;
  end
end

//SHA3 instance
//TIE OFFS FIXME TODO
  always_comb msg_start = '0;
  always_comb msg_valid = '0;
  always_comb msg_strobe = '0;
  always_comb msg_data[0] = '0;
  always_comb sha3_start = '0;
  always_comb sha3_process = '0;
  always_comb sha3_run = '0;
  always_comb sha3_done = abr_prim_mubi_pkg::MuBi4False;
  always_comb mode = sha3_pkg::Shake;
  always_comb strength = sha3_pkg::L256;
  always_comb zeroize = '0;

  sha3 #(
    .RoundsPerClock(RoundsPerClock),
    .EnMasking (Sha3EnMasking)
  ) sha3_inst (
    .clk_i (clk),
    .rst_b (rst_b),

    // MSG_FIFO interface
    .msg_start_i (msg_start),
    .msg_valid_i (msg_valid),
    .msg_data_i  (msg_data),
    .msg_strb_i  (msg_strobe),
    .msg_ready_o (sha3_msg_rdy),

    // Entropy interface - not using
    .rand_valid_i    (1'b0),
    .rand_early_i    (1'b0),
    .rand_data_i     ('0),
    .rand_aux_i      ('0),
    .rand_consumed_o (),

    // N, S: Used in cSHAKE mode
    .ns_data_i       ('0), // ns_prefix),

    // Configurations
    .mode_i     (mode), 
    .strength_i (strength), 

    // Controls (CMD register)
    .start_i    (sha3_start       ),
    .process_i  (sha3_process     ),
    .run_i      (sha3_run         ), // For squeeze
    .done_i     (sha3_done        ),

    .absorbed_o (sha3_absorbed),
    .squeezing_o (sha3_squeezing),

    .block_processed_o (sha3_block_processed),

    .sha3_fsm_o (sha3_fsm),

    .state_valid_o (sha3_state_vld),
    .state_o       (sha3_state),

    .error_o (sha3_err),
    .sparse_fsm_error_o (sha3_state_error),
    .count_error_o  (sha3_count_error),
    .keccak_storage_rst_error_o (sha3_rst_storage_err)
  );

  //control logic to steer sha3 output to appropriate sampler
  always_comb sha3_rejs_dv = sha3_state_vld & 1'b1; //TODO controller or singular PISO
  always_comb sha3_rejb_dv = sha3_state_vld & 1'b1; //TODO controller or singular PISO
  always_comb sha3_exp_dv = sha3_state_vld & 1'b1; //TODO controller or singular PISO
  always_comb sha3_sib_dv = sha3_state_vld & 1'b1; //TODO controller or singular PISO

  always_comb sha3_rejs_data = sha3_state[0][REJS_PISO_INPUT_RATE-1:0];
  always_comb sha3_rejb_data = sha3_state[0][REJB_PISO_INPUT_RATE-1:0];
  always_comb sha3_exp_data = sha3_state[0][EXP_PISO_INPUT_RATE-1:0];
  always_comb sha3_sib_data = sha3_state[0][SIB_PISO_INPUT_RATE-1:0];

//rej sampler
  abr_piso #(
    .PISO_BUFFER_W(REJS_PISO_BUFFER_W),
    .PISO_INPUT_RATE(REJS_PISO_INPUT_RATE),
    .PISO_OUTPUT_RATE(REJS_PISO_OUTPUT_RATE)
  ) rej_sampler_piso_inst (
    .clk(clk),
    .rst_b(rst_b),
    .zeroize(zeroize),
    .valid_i(sha3_rejs_dv),
    .hold_o(rejs_sha3_hold),
    .data_i(sha3_rejs_data),
    .valid_o(rejs_piso_dv),
    .hold_i(rejs_piso_hold),
    .data_o(rejs_piso_data)
  );

  rej_sampler_ctrl#(
    .REJ_NUM_SAMPLERS(REJS_NUM_SAMPLERS),
    .REJ_SAMPLE_W(REJS_SAMPLE_W),
    .REJ_VLD_SAMPLES(REJS_VLD_SAMPLES),
    .REJ_VALUE(DILITHIUM_Q)
  ) rej_sampler_inst (
    .clk(clk),
    .rst_b(rst_b),
    .zeroize(zeroize), 
    //input data
    .data_valid_i(rejs_piso_dv),
    .data_hold_o(rejs_piso_hold),
    .data_i(rejs_piso_data),

    //output data
    .data_valid_o(rejs_dv_o),
    .data_o(rejs_data_o)
  );

//rej bounded
  abr_piso #(
    .PISO_BUFFER_W(REJB_PISO_BUFFER_W),
    .PISO_INPUT_RATE(REJB_PISO_INPUT_RATE),
    .PISO_OUTPUT_RATE(REJB_PISO_OUTPUT_RATE)
  ) rej_bounded_piso_inst (
    .clk(clk),
    .rst_b(rst_b),
    .zeroize(zeroize),
    .valid_i(sha3_rejb_dv),
    .hold_o(rejb_sha3_hold),
    .data_i(sha3_rejb_data),
    .valid_o(rejb_piso_dv),
    .hold_i(rejb_piso_hold),
    .data_o(rejb_piso_data)
 );

  rej_bounded_ctrl #(
    .REJ_NUM_SAMPLERS(REJB_NUM_SAMPLERS),
    .REJ_SAMPLE_W(REJB_SAMPLE_W),
    .REJ_VLD_SAMPLES(REJB_VLD_SAMPLES),
    .REJ_VALUE(REJB_VALUE)
  ) rej_bounded_inst (
    .clk(clk),
    .rst_b(rst_b),
    .zeroize(zeroize), 
    //input data
    .data_valid_i(rejb_piso_dv),
    .data_hold_o(rejb_piso_hold),
    .data_i(rejb_piso_data),

    //output data
    .data_valid_o(rejb_dv_o),
    .data_o(rejb_data_o)
  );

//exp mask
  abr_piso #(
    .PISO_BUFFER_W(EXP_PISO_BUFFER_W),
    .PISO_INPUT_RATE(EXP_PISO_INPUT_RATE),
    .PISO_OUTPUT_RATE(EXP_PISO_OUTPUT_RATE)
  ) exp_mask_piso_inst (
    .clk(clk),
    .rst_b(rst_b),
    .zeroize(zeroize),
    .valid_i(sha3_exp_dv),
    .hold_o(exp_sha3_hold),
    .data_i(sha3_exp_data),
    .valid_o(exp_piso_dv),
    .hold_i(exp_piso_hold),
    .data_o(exp_piso_data)
 );


  exp_mask_ctrl #(
    .EXP_NUM_SAMPLERS(EXP_NUM_SAMPLERS),
    .EXP_SAMPLE_W(EXP_SAMPLE_W),
    .EXP_VLD_SAMPLES(EXP_VLD_SAMPLES),
    .EXP_VLD_SAMPLE_W(EXP_VLD_SAMPLE_W)
  ) exp_mask_inst (
    .clk(clk),
    .rst_b(rst_b),
    .zeroize(zeroize), 
    //input data
    .data_valid_i(exp_piso_dv),
    .data_hold_o(exp_piso_hold),
    .data_i(exp_piso_data),

    //output data
    .data_valid_o(exp_dv_o),
    .data_o(exp_data_o)
  );

//sample in ball
  sib_mem
  #(
    .DATA_WIDTH((DILITHIUM_Q_W-1)*4),
    .DEPTH     (DILITHIUM_N/4  ),
    .NUM_PORTS (2              )
  )
  sib_mem_inst
  (
    .clk_i(clk),
    .zeroize(zeroize),
    .cs_i('1),
    .we_i(sib_mem_we),
    .addr_i(sib_mem_addr),
    .wdata_i(sib_mem_wrdata),

    .rdata_o(sib_mem_rddata)
  );

  abr_piso #(
    .PISO_BUFFER_W(SIB_PISO_BUFFER_W),
    .PISO_INPUT_RATE(SIB_PISO_INPUT_RATE),
    .PISO_OUTPUT_RATE(SIB_PISO_OUTPUT_RATE)
  ) sib_piso_inst (
    .clk(clk),
    .rst_b(rst_b),
    .zeroize(zeroize),
    .valid_i(sha3_sib_dv),
    .hold_o(sib_sha3_hold),
    .data_i(sha3_sib_data),
    .valid_o(sib_piso_dv),
    .hold_i(sib_piso_hold),
    .data_o(sib_piso_data)
  );

  sample_in_ball_ctrl #(
    .SIB_NUM_SAMPLERS(SIB_NUM_SAMPLERS),
    .SIB_SAMPLE_W(SIB_SAMPLE_W),
    .SIB_TAU(SIB_TAU)
  ) sib_inst (
    .clk(clk),
    .rst_b(rst_b),
    .zeroize(zeroize), 
    //input data
    .data_valid_i(sib_piso_dv),
    .data_hold_o(sib_piso_hold),
    .data_i(sib_piso_data),
    .sib_done_o(sib_done),

    //memory_if
    .we_o(sib_mem_we),
    .addr_o(sib_mem_addr),
    .wrdata_o(sib_mem_wrdata),
    .rddata_i(sib_mem_rddata)
  );

endmodule