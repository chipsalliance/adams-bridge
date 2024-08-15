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

`include "config_defines.svh"

module sampler_top
  import sampler_pkg::*;
  import sha3_pkg::*;
  import abr_params_pkg::*;
  import abr_prim_alert_pkg::*;
  #(
  //top level params
  )
  (
  input logic clk,
  input logic rst_b,
  input logic zeroize,

  //input
  input abr_sampler_mode_e sampler_mode_i,

  input logic                    sha3_start_i,

  input logic                    msg_start_i,
  input logic                    msg_valid_i,
  output logic                   msg_rdy_o,
  input logic [MsgStrbW-1:0]     msg_strobe_i,
  input logic [MsgWidth-1:0]     msg_data_i[Sha3Share],

  input logic                    sampler_start_i,

  input logic [ABR_MEM_ADDR_WIDTH-1:0] dest_base_addr_i,

  //NTT read from sib_mem
  input mem_if_t                        sib_mem_rd_req_i,
  output logic [ABR_MEM_DATA_WIDTH-1:0] sib_mem_rd_data_o,

  //output
  output logic                     sampler_busy_o,

  output logic                                        sampler_ntt_dv_o,
  output logic [COEFF_PER_CLK-1:0][DILITHIUM_Q_W-1:0] sampler_ntt_data_o,

  output logic                                        sampler_mem_dv_o,
  output logic [COEFF_PER_CLK-1:0][DILITHIUM_Q_W-1:0] sampler_mem_data_o,
  output logic [ABR_MEM_ADDR_WIDTH-1:0]               sampler_mem_addr_o,

  output logic                                        sampler_state_dv_o,
  output logic [sha3_pkg::StateW-1:0]                 sampler_state_data_o [Sha3Share]

  );

//Signal Declarations
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

  logic sha3_state_dv;
  logic sha3_state_hold;
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

  logic                                            rejs_dv;
  logic [REJS_VLD_SAMPLES-1:0][DILITHIUM_Q_W-1:0]  rejs_data;
  logic [REJS_VLD_SAMPLES-1:0][DILITHIUM_Q_W-1:0]  rejs_data_q;

  //rej bounded
  logic                                               sha3_rejb_dv;
  logic                                               rejb_sha3_hold;
  logic [REJB_PISO_INPUT_RATE-1:0]                    sha3_rejb_data;

  logic                                               rejb_piso_dv;
  logic                                               rejb_piso_hold;
  logic [REJB_NUM_SAMPLERS-1:0][REJB_SAMPLE_W-1:0]    rejb_piso_data;

  logic                                               rejb_dv;
  logic [REJB_VLD_SAMPLES-1:0][DILITHIUM_Q_W-1:0]     rejb_data;

  //exp mask
  logic                                             sha3_exp_dv;
  logic                                             exp_sha3_hold;
  logic [EXP_PISO_INPUT_RATE-1:0]                   sha3_exp_data;

  logic                                             exp_piso_dv;
  logic                                             exp_piso_hold;
  logic [EXP_NUM_SAMPLERS-1:0][EXP_SAMPLE_W-1:0]    exp_piso_data;

  logic                                             exp_dv;
  logic [EXP_VLD_SAMPLES-1:0][EXP_VLD_SAMPLE_W-1:0] exp_data;

  //sample in ball
  logic                                          sha3_sib_dv;
  logic                                          sib_sha3_hold;
  logic [SIB_PISO_INPUT_RATE-1:0]                sha3_sib_data;

  logic                                          sib_piso_dv;
  logic                                          sib_piso_hold;
  logic [SIB_NUM_SAMPLERS-1:0][SIB_SAMPLE_W-1:0] sib_piso_data;

  logic                                          sib_done;

  logic [1:0]                                    sib_mem_cs, sib_mem_cs_mux;
  logic [1:0]                                    sib_mem_we;
  logic [1:0][7:2]                               sib_mem_addr, sib_mem_addr_mux;
  logic [1:0][3:0][DILITHIUM_Q_W-2:0]            sib_mem_wrdata;
  logic [1:0][3:0][DILITHIUM_Q_W-2:0]            sib_mem_rddata;

  logic [ABR_MEM_ADDR_WIDTH-1:0] dest_addr;
  logic [$clog2(ABR_COEFF_CNT/4):0] coeff_cnt;
  logic vld_cycle;
  logic sampler_done;

  logic zeroize_sha3, zeroize_rejb, zeroize_rejs, zeroize_sib, zeroize_exp_mask;
  logic zeroize_sib_mem;

  //Sampler mode muxes
  always_comb begin
    mode = sha3_pkg::Shake;
    strength = sha3_pkg::L256;
    vld_cycle = 0;
    sampler_done = 0;
    sampler_mem_dv_o = 0;
    sampler_mem_data_o = 0;
    sampler_mem_addr_o = 0;
    sampler_state_dv_o = 0;
    sampler_state_data_o[0] = 0;
    zeroize_rejb = 0;
    zeroize_rejs = 0;
    zeroize_exp_mask = 0;
    zeroize_sib = 0;
    zeroize_sib_mem = 0;
    zeroize_sha3 = 0;

    unique case (sampler_mode_i) inside
      ABR_SHAKE256: begin
        mode = sha3_pkg::Shake;
        strength = sha3_pkg::L256;
        sampler_state_dv_o = sha3_state_dv;
        sampler_state_data_o[0] = sha3_state[0];
        sampler_done = sha3_state_dv;
        zeroize_sha3 = sha3_state_dv;
      end
      ABR_SHAKE128: begin
        mode = sha3_pkg::Shake;
        strength = sha3_pkg::L128;
        sampler_state_dv_o = sha3_state_dv;
        sampler_state_data_o [0]= sha3_state[0];
        sampler_done = sha3_state_dv;
        zeroize_sha3 = sha3_state_dv;
      end
      ABR_REJ_SAMPLER: begin
        mode = sha3_pkg::Shake;
        strength = sha3_pkg::L128;
        vld_cycle = rejs_dv;
        sampler_done = (coeff_cnt == (ABR_COEFF_CNT/4));
        zeroize_rejs = sampler_done;
        zeroize_sha3 = sampler_done;
      end
      ABR_EXP_MASK: begin
        mode = sha3_pkg::Shake;
        strength = sha3_pkg::L256;
        vld_cycle = exp_dv;
        sampler_mem_dv_o = exp_dv;
        sampler_mem_data_o = exp_data;
        sampler_mem_addr_o = dest_addr;
        sampler_done = (coeff_cnt == (ABR_COEFF_CNT/4));
        zeroize_exp_mask = sampler_done;
        zeroize_sha3 = sampler_done;
      end
      ABR_REJ_BOUNDED: begin
        mode = sha3_pkg::Shake;
        strength = sha3_pkg::L256;
        vld_cycle = rejb_dv;
        sampler_mem_dv_o = rejb_dv;
        sampler_mem_data_o = rejb_data;
        sampler_mem_addr_o = dest_addr;
        sampler_done = (coeff_cnt == (ABR_COEFF_CNT/4));
        zeroize_rejb = sampler_done;
        zeroize_sha3 = sampler_done;
      end
      ABR_SAMPLE_IN_BALL: begin
        mode = sha3_pkg::Shake;
        strength = sha3_pkg::L256;
        zeroize_sib_mem = sampler_start_i;
        sampler_done = sib_done;
        zeroize_sib = sampler_done;
        zeroize_sha3 = sampler_done;
      end
      default: begin

      end
    endcase
  end

//FSM Controller
//declare fsm state variables
typedef enum logic [2:0] {
  ABR_SAMPLER_IDLE   = 3'b000,
  ABR_SAMPLER_PROC   = 3'b001,
  ABR_SAMPLER_WAIT   = 3'b010,
  ABR_SAMPLER_RUN    = 3'b011,
  ABR_SAMPLER_DONE   = 3'b100
} abr_sampler_fsm_state_e;

abr_sampler_fsm_state_e sampler_fsm_ps, sampler_fsm_ns;

//Count coefficients
//Load and increment dest address
always_ff @(posedge clk or negedge rst_b) begin
  if (!rst_b) begin
    coeff_cnt <= 0;
    dest_addr <= 0;
  end
  else if (zeroize) begin
    coeff_cnt <= 0;
    dest_addr <= 0;
  end
  else begin
    coeff_cnt <= sampler_start_i ? 'd0 :
                 vld_cycle ? coeff_cnt + 'd1 : coeff_cnt;
    dest_addr <= sampler_start_i ? dest_base_addr_i :
                 vld_cycle ? dest_addr + 'd1 : dest_addr;
  end
end

always_comb sampler_busy_o = sampler_start_i | (sampler_fsm_ps != ABR_SAMPLER_IDLE);

//State logic
always_comb begin : sampler_fsm_out_comb
    sampler_fsm_ns = sampler_fsm_ps;
    sha3_process = 0;
    sha3_run = 0;
    sha3_done = abr_prim_mubi_pkg::MuBi4False;
    
    unique case (sampler_fsm_ps)
      ABR_SAMPLER_IDLE: begin
        //wait for start
        if (sampler_start_i)
          sampler_fsm_ns = ABR_SAMPLER_PROC;
      end
      ABR_SAMPLER_PROC: begin
        sampler_fsm_ns = ABR_SAMPLER_WAIT;
        //drive process signal
        sha3_process = 1;
      end
      ABR_SAMPLER_WAIT: begin
        if (sampler_done) begin
          sampler_fsm_ns = ABR_SAMPLER_DONE;
        end else if (sha3_state_dv & ~sha3_state_hold) begin
          sampler_fsm_ns = ABR_SAMPLER_RUN;
        end
      end
      ABR_SAMPLER_RUN: begin
        if (sampler_done) begin
          sampler_fsm_ns = ABR_SAMPLER_DONE;
        end else begin 
          sampler_fsm_ns = ABR_SAMPLER_WAIT;
          //drive run signal
          sha3_run = 1;
        end
      end
      ABR_SAMPLER_DONE: begin
        //drive done
        sha3_done = abr_prim_mubi_pkg::MuBi4True;
        //Go to IDLE when sha3 resets
        if (~sha3_squeezing) sampler_fsm_ns = ABR_SAMPLER_IDLE;
        //zeroize samplers
      end
      default: begin
      end
    endcase
end

//State flop
always_ff @(posedge clk or negedge rst_b) begin : sampler_fsm_flops
  if (!rst_b) begin
      sampler_fsm_ps <= ABR_SAMPLER_IDLE;
  end
  else if (zeroize) begin
      sampler_fsm_ps <= ABR_SAMPLER_IDLE;
  end
  else begin
      sampler_fsm_ps <= sampler_fsm_ns;
  end
end  

//rej sampler output gets sent to NTT
always_comb sampler_ntt_dv_o = rejs_dv;
always_comb sampler_ntt_data_o = rejs_data;

//SHA3 instance
  sha3 #(
    .RoundsPerClock(RoundsPerClock),
    .EnMasking (Sha3EnMasking)
  ) sha3_inst (
    .clk_i (clk),
    .rst_b (rst_b),
    .zeroize (zeroize_sha3),

    // MSG_FIFO interface
    .msg_start_i (msg_start_i),
    .msg_valid_i (msg_valid_i),
    .msg_data_i  (msg_data_i),
    .msg_strb_i  (msg_strobe_i),
    .msg_ready_o (msg_rdy_o),

    // Entropy interface - not using
    .rand_valid_i    (1'b0),
    .rand_early_i    (1'b0),
    .rand_data_i     ('0),
    .rand_aux_i      ('0),
    .rand_consumed_o (),

    // N, S: Used in cSHAKE mode
    .ns_data_i       ('0),

    // Configurations
    .mode_i     (mode), 
    .strength_i (strength), 

    // Controls (CMD register)
    .start_i    (sha3_start_i),
    .process_i  (sha3_process),
    .run_i      (sha3_run), // For squeeze
    .done_i     (sha3_done),

    .absorbed_o (sha3_absorbed),
    .squeezing_o (sha3_squeezing),

    .block_processed_o (sha3_block_processed),

    .sha3_fsm_o (sha3_fsm),

    .state_valid_o      (sha3_state_dv),
    .state_valid_hold_i (sha3_state_hold),
    .state_o       (sha3_state),

    .error_o (sha3_err),
    .sparse_fsm_error_o (sha3_state_error),
    .count_error_o  (sha3_count_error),
    .keccak_storage_rst_error_o (sha3_rst_storage_err)
  );

  //FIXME just one PISO
  //control logic to steer sha3 output to appropriate sampler
  always_comb sha3_rejs_dv = sha3_state_dv & (sampler_mode_i == ABR_REJ_SAMPLER); 
  always_comb sha3_rejb_dv = sha3_state_dv & (sampler_mode_i == ABR_REJ_BOUNDED);
  always_comb sha3_exp_dv = sha3_state_dv & (sampler_mode_i == ABR_EXP_MASK);
  always_comb sha3_sib_dv = sha3_state_dv & (sampler_mode_i == ABR_SAMPLE_IN_BALL);

  always_comb sha3_state_hold = ((sampler_mode_i == ABR_REJ_SAMPLER)    & rejs_sha3_hold) |
                                ((sampler_mode_i == ABR_REJ_BOUNDED)    & rejb_sha3_hold) |
                                ((sampler_mode_i == ABR_EXP_MASK)       & exp_sha3_hold)  |
                                ((sampler_mode_i == ABR_SAMPLE_IN_BALL) & sib_sha3_hold);

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
    .zeroize(zeroize_rejs),
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
    .zeroize(zeroize_rejs), 
    //input data
    .data_valid_i(rejs_piso_dv),
    .data_hold_o(rejs_piso_hold),
    .data_i(rejs_piso_data),

    //output data
    .data_valid_o(rejs_dv),
    .data_o(rejs_data_q)
  );
  
  //FIXME HACK
always_ff  @(posedge clk or negedge rst_b) begin : delay_rejs_data
  if (!rst_b) begin
    rejs_data <= 0;
  end
  else if (zeroize) begin
    rejs_data <= 0;
  end
  else begin
    rejs_data <= rejs_data_q;
  end
end  

//rej bounded
  abr_piso #(
    .PISO_BUFFER_W(REJB_PISO_BUFFER_W),
    .PISO_INPUT_RATE(REJB_PISO_INPUT_RATE),
    .PISO_OUTPUT_RATE(REJB_PISO_OUTPUT_RATE)
  ) rej_bounded_piso_inst (
    .clk(clk),
    .rst_b(rst_b),
    .zeroize(zeroize_rejb),
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
    .zeroize(zeroize_rejb), 
    //input data
    .data_valid_i(rejb_piso_dv),
    .data_hold_o(rejb_piso_hold),
    .data_i(rejb_piso_data),

    //output data
    .data_valid_o(rejb_dv),
    .data_o(rejb_data)
  );

//exp mask
  abr_piso #(
    .PISO_BUFFER_W(EXP_PISO_BUFFER_W),
    .PISO_INPUT_RATE(EXP_PISO_INPUT_RATE),
    .PISO_OUTPUT_RATE(EXP_PISO_OUTPUT_RATE)
  ) exp_mask_piso_inst (
    .clk(clk),
    .rst_b(rst_b),
    .zeroize(zeroize_exp_mask),
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
    .zeroize(zeroize_exp_mask), 
    //input data
    .data_valid_i(exp_piso_dv),
    .data_hold_o(exp_piso_hold),
    .data_i(exp_piso_data),

    //output data
    .data_valid_o(exp_dv),
    .data_o(exp_data)
  );

//sample in ball
  //Mux read from NTT in here
  always_comb sib_mem_addr_mux[0] = (sib_mem_rd_req_i.rd_wr_en == RW_READ) ? sib_mem_rd_req_i.addr[5:0] : sib_mem_addr[0];
  always_comb sib_mem_addr_mux[1] = sib_mem_addr[1];
  always_comb sib_mem_cs_mux[0] = (sib_mem_rd_req_i.rd_wr_en == RW_READ) | sib_mem_cs[0];
  always_comb sib_mem_cs_mux[1] = sib_mem_cs[1];

  //ugly expansion of 23->24 bits FIXME
  assign sib_mem_rd_data_o = {1'b0,sib_mem_rddata[0][3],1'b0,sib_mem_rddata[0][2],1'b0,sib_mem_rddata[0][1],1'b0,sib_mem_rddata[0][0]};

  sib_mem
  #(
    .DATA_WIDTH((DILITHIUM_Q_W-1)*4),
    .DEPTH     (DILITHIUM_N/4),
    .NUM_PORTS (2)
  )
  sib_mem_inst
  (
    .clk_i(clk),
    .zeroize(zeroize_sib_mem),
    .cs_i(sib_mem_cs_mux),
    .we_i(sib_mem_we),
    .addr_i(sib_mem_addr_mux),
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
    .zeroize(zeroize_sib),
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
    .zeroize(zeroize_sib), 
    //input data
    .data_valid_i(sib_piso_dv),
    .data_hold_o(sib_piso_hold),
    .data_i(sib_piso_data),
    .sib_done_o(sib_done),

    //memory_if
    .cs_o(sib_mem_cs),
    .we_o(sib_mem_we),
    .addr_o(sib_mem_addr),
    .wrdata_o(sib_mem_wrdata),
    .rddata_i(sib_mem_rddata)
  );


  `ABR_ASSERT_MUTEX(ERR_SAMPLER_O_MUTEX, {sampler_ntt_dv_o,sampler_mem_dv_o,sampler_state_dv_o}, clk, !rst_b)

  `ABR_ASSERT_NEVER(ERR_SIBMEM_ACCESS, (sib_mem_rd_req_i.rd_wr_en == RW_READ) && |sib_mem_cs, clk, !rst_b)

  `ABR_ASSERT_KNOWN(ERR_SAMPLER_FSM_X, sampler_fsm_ps, clk, !rst_b)
  `ABR_ASSERT_KNOWN(ERR_SAMPLER_MODE_X, sampler_mode_i, clk, !rst_b)
  `ABR_ASSERT_KNOWN(ERR_SAMPLER_NTT_DATA_X, sampler_ntt_data_o, clk, !rst_b, sampler_ntt_dv_o)
  `ABR_ASSERT_KNOWN(ERR_SAMPLER_MEM_DATA_X, sampler_mem_data_o, clk, !rst_b, sampler_mem_dv_o)
  `ABR_ASSERT_KNOWN(ERR_SAMPLER_STATE_DATA_X, sampler_state_data_o[0], clk, !rst_b, sampler_state_dv_o)

endmodule