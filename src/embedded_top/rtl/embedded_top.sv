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
  #(
  //top level params
  )
  (
  input logic clk,
  input logic rst_b

  //input

  //output

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