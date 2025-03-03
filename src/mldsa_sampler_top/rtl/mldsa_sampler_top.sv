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

`include "mldsa_config_defines.svh"

module mldsa_sampler_top
  import mldsa_sampler_pkg::*;
  import abr_sha3_pkg::*;
  import mldsa_params_pkg::*;
  import abr_prim_alert_pkg::*;
  #(
  //top level params
  )
  (
  input logic clk,
  input logic rst_b,
  input logic zeroize,

  //input
  input mldsa_sampler_mode_e sampler_mode_i,

  input logic                    sha3_start_i,

  input logic                    msg_start_i,
  input logic                    msg_valid_i,
  output logic                   msg_rdy_o,
  input logic [MsgStrbW-1:0]     msg_strobe_i,
  input logic [MsgWidth-1:0]     msg_data_i[Sha3Share],

  input logic                    sampler_start_i,

  input logic [MLDSA_MEM_ADDR_WIDTH-1:0] dest_base_addr_i,

  //NTT read from sib_mem
  input mem_if_t                        sib_mem_rd_req_i,
  output logic [MLDSA_MEM_DATA_WIDTH-1:0] sib_mem_rd_data_o,

  //output
  output logic                     sampler_busy_o,

  output logic                                        sampler_ntt_dv_o,
  output logic [COEFF_PER_CLK-1:0][MLDSA_Q_WIDTH-1:0] sampler_ntt_data_o,

  output logic                                        sampler_mem_dv_o,
  output logic [COEFF_PER_CLK-1:0][MLDSA_Q_WIDTH-1:0] sampler_mem_data_o,
  output logic [MLDSA_MEM_ADDR_WIDTH-1:0]             sampler_mem_addr_o,

  output logic                                        sampler_state_dv_o,
  output logic [abr_sha3_pkg::StateW-1:0]             sampler_state_data_o [Sha3Share]

  );

//Signal Declarations
  logic                    sha3_process;
  logic                    sha3_run;

  abr_prim_mubi_pkg::mubi4_t    sha3_done;
  abr_prim_mubi_pkg::mubi4_t    sha3_absorbed;

  logic sha3_squeezing;

  logic sha3_block_processed;

  abr_sha3_pkg::sha3_st_e sha3_fsm;
  abr_sha3_pkg::err_t sha3_err;

  abr_sha3_pkg::sha3_mode_e mode;
  abr_sha3_pkg::keccak_strength_e strength;

  logic sha3_state_dv;
  logic sha3_state_hold;
  logic [abr_sha3_pkg::StateW-1:0] sha3_state[Sha3Share];

  logic sha3_state_error;
  logic sha3_count_error;
  logic sha3_rst_storage_err;

  //rej sampler
  logic                                            rejs_piso_dv;
  logic                                            rejs_piso_hold;
  logic [REJS_NUM_SAMPLERS-1:0][REJS_SAMPLE_W-1:0] rejs_piso_data;

  logic                                            rejs_dv;
  logic [REJS_VLD_SAMPLES-1:0][MLDSA_Q_WIDTH-1:0]  rejs_data;
  logic [REJS_VLD_SAMPLES-1:0][MLDSA_Q_WIDTH-1:0]  rejs_data_q;

  //rej bounded
  logic                                               rejb_piso_dv;
  logic                                               rejb_piso_hold;
  logic [REJB_NUM_SAMPLERS-1:0][REJB_SAMPLE_W-1:0]    rejb_piso_data;

  logic                                               rejb_dv;
  logic [REJB_VLD_SAMPLES-1:0][MLDSA_Q_WIDTH-1:0]     rejb_data;

  //exp mask
  logic                                             exp_piso_dv;
  logic                                             exp_piso_hold;
  logic [EXP_NUM_SAMPLERS-1:0][EXP_SAMPLE_W-1:0]    exp_piso_data;

  logic                                             exp_dv;
  logic [EXP_VLD_SAMPLES-1:0][EXP_VLD_SAMPLE_W-1:0] exp_data;

  //sample in ball
  logic                                          sib_piso_dv;
  logic                                          sib_piso_hold;
  logic [SIB_NUM_SAMPLERS-1:0][SIB_SAMPLE_W-1:0] sib_piso_data;

  logic                                          sib_done;

  logic [1:0]                                    sib_mem_cs, sib_mem_cs_mux;
  logic [1:0]                                    sib_mem_we;
  logic [1:0][7:2]                               sib_mem_addr, sib_mem_addr_mux;
  logic [1:0][3:0][MLDSA_Q_WIDTH-2:0]            sib_mem_wrdata;
  logic [1:0][3:0][MLDSA_Q_WIDTH-2:0]            sib_mem_rddata;

  logic [MLDSA_MEM_ADDR_WIDTH-1:0] dest_addr;
  logic [$clog2(MLDSA_COEFF_CNT/4):0] coeff_cnt;
  logic vld_cycle;
  logic sampler_done;

  logic zeroize_sha3, zeroize_rejb, zeroize_rejs, zeroize_sib, zeroize_exp_mask;
  logic zeroize_sib_mem;
  logic zeroize_piso;

  logic [1:0] piso_mode;
  logic piso_dv, piso_hold;
  logic [REJS_PISO_OUTPUT_RATE-1:0] piso_data;

  //Sampler mode muxes
  always_comb begin
    mode = abr_sha3_pkg::Shake;
    strength = abr_sha3_pkg::L256;
    vld_cycle = 0;
    sampler_done = 0;
    sampler_mem_dv_o = 0;
    sampler_mem_data_o = 0;
    sampler_mem_addr_o = 0;
    sampler_state_dv_o = 0;
    sampler_state_data_o[0] = 0;
    zeroize_rejb = zeroize;
    zeroize_rejs = zeroize;
    zeroize_exp_mask = zeroize;
    zeroize_sib = zeroize;
    zeroize_sib_mem = zeroize;
    zeroize_sha3 = zeroize;
    zeroize_piso = zeroize;
    piso_mode = 0;

    unique case (sampler_mode_i) inside
      MLDSA_SHAKE256: begin
        mode = abr_sha3_pkg::Shake;
        strength = abr_sha3_pkg::L256;
        sampler_state_dv_o = sha3_state_dv;
        sampler_state_data_o[0] = sha3_state[0];
        sampler_done = sha3_state_dv;
        zeroize_sha3 |= sha3_state_dv;
      end
      MLDSA_SHAKE128: begin
        mode = abr_sha3_pkg::Shake;
        strength = abr_sha3_pkg::L128;
        sampler_state_dv_o = sha3_state_dv;
        sampler_state_data_o [0]= sha3_state[0];
        sampler_done = sha3_state_dv;
        zeroize_sha3 |= sha3_state_dv;
      end
      MLDSA_REJ_SAMPLER: begin
        mode = abr_sha3_pkg::Shake;
        strength = abr_sha3_pkg::L128;
        vld_cycle = rejs_dv;
        sampler_done = (coeff_cnt == (MLDSA_COEFF_CNT/4));
        zeroize_rejs |= sampler_done;
        zeroize_sha3 |= sampler_done;
        zeroize_piso |= sampler_done;
        piso_mode = 0;
      end
      MLDSA_EXP_MASK: begin
        mode = abr_sha3_pkg::Shake;
        strength = abr_sha3_pkg::L256;
        vld_cycle = exp_dv;
        sampler_mem_dv_o = exp_dv;
        sampler_mem_data_o = exp_data;
        sampler_mem_addr_o = dest_addr;
        sampler_done = (coeff_cnt == (MLDSA_COEFF_CNT/4));
        zeroize_exp_mask |= sampler_done;
        zeroize_sha3 |= sampler_done;
        zeroize_piso |= sampler_done;
        piso_mode = 2;
      end
      MLDSA_REJ_BOUNDED: begin
        mode = abr_sha3_pkg::Shake;
        strength = abr_sha3_pkg::L256;
        vld_cycle = rejb_dv;
        sampler_mem_dv_o = rejb_dv;
        sampler_mem_data_o = rejb_data;
        sampler_mem_addr_o = dest_addr;
        sampler_done = (coeff_cnt == (MLDSA_COEFF_CNT/4));
        zeroize_rejb |= sampler_done;
        zeroize_sha3 |= sampler_done;
        zeroize_piso |= sampler_done;
        piso_mode = 1;
      end
      MLDSA_SAMPLE_IN_BALL: begin
        mode = abr_sha3_pkg::Shake;
        strength = abr_sha3_pkg::L256;
        zeroize_sib_mem = sampler_start_i;
        sampler_done = sib_done;
        zeroize_sib |= sampler_done;
        zeroize_sha3 |= sampler_done;
        zeroize_piso |= sampler_done;
        piso_mode = 3;
      end
      default: begin

      end
    endcase
  end

//FSM Controller
//declare fsm state variables
typedef enum logic [2:0] {
  MLDSA_SAMPLER_IDLE   = 3'b000,
  MLDSA_SAMPLER_PROC   = 3'b001,
  MLDSA_SAMPLER_WAIT   = 3'b010,
  MLDSA_SAMPLER_RUN    = 3'b011,
  MLDSA_SAMPLER_DONE   = 3'b100
} mldsa_sampler_fsm_state_e;

mldsa_sampler_fsm_state_e sampler_fsm_ps, sampler_fsm_ns;

//Count coefficients
//Load and increment dest address
always_ff @(posedge clk or negedge rst_b) begin
  if (!rst_b) begin
    coeff_cnt <= 0;
    dest_addr <= 0;
  end
  else if (zeroize | sampler_done) begin
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

always_comb sampler_busy_o = sampler_start_i | (sampler_fsm_ps != MLDSA_SAMPLER_IDLE);

//State logic
always_comb begin : sampler_fsm_out_comb
    sampler_fsm_ns = sampler_fsm_ps;
    sha3_process = 0;
    sha3_run = 0;
    sha3_done = abr_prim_mubi_pkg::MuBi4False;

    unique case (sampler_fsm_ps)
      MLDSA_SAMPLER_IDLE: begin
        //wait for start
        if (sampler_start_i)
          sampler_fsm_ns = MLDSA_SAMPLER_PROC;
      end
      MLDSA_SAMPLER_PROC: begin
        sampler_fsm_ns = MLDSA_SAMPLER_WAIT;
        //drive process signal
        sha3_process = 1;
      end
      MLDSA_SAMPLER_WAIT: begin
        if (sampler_done) begin
          sampler_fsm_ns = MLDSA_SAMPLER_DONE;
        end else if (sha3_state_dv & ~sha3_state_hold) begin
          sampler_fsm_ns = MLDSA_SAMPLER_RUN;
        end
      end
      MLDSA_SAMPLER_RUN: begin
        if (sampler_done) begin
          sampler_fsm_ns = MLDSA_SAMPLER_DONE;
        end else begin 
          sampler_fsm_ns = MLDSA_SAMPLER_WAIT;
          //drive run signal
          sha3_run = 1;
        end
      end
      MLDSA_SAMPLER_DONE: begin
        //drive done
        if (sha3_fsm == abr_sha3_pkg::StSqueeze) begin
          sha3_done = abr_prim_mubi_pkg::MuBi4True;
        end
        //Go to IDLE when sha3 resets
        if (~sha3_squeezing) begin 
          sampler_fsm_ns = MLDSA_SAMPLER_IDLE;
        end
      end
      default: begin
      end
    endcase
end

//State flop
always_ff @(posedge clk or negedge rst_b) begin : sampler_fsm_flops
  if (!rst_b) begin
      sampler_fsm_ps <= MLDSA_SAMPLER_IDLE;
  end
  else if (zeroize) begin
      sampler_fsm_ps <= MLDSA_SAMPLER_IDLE;
  end
  else begin
      sampler_fsm_ps <= sampler_fsm_ns;
  end
end  

//rej sampler output gets sent to NTT
always_comb sampler_ntt_dv_o = rejs_dv;
always_comb sampler_ntt_data_o = rejs_data;

//SHA3 instance
  abr_sha3 #(
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

//one piso
  abr_piso_4 #(
    .PISO_BUFFER_W(REJS_PISO_BUFFER_W),
    .PISO_INPUT_RATE0(REJS_PISO_INPUT_RATE),
    .PISO_INPUT_RATE1(REJB_PISO_INPUT_RATE),
    .PISO_INPUT_RATE2(EXP_PISO_INPUT_RATE),
    .PISO_INPUT_RATE3(SIB_PISO_INPUT_RATE),
    .PISO_OUTPUT_RATE0(REJS_PISO_OUTPUT_RATE),
    .PISO_OUTPUT_RATE1(REJB_PISO_OUTPUT_RATE),
    .PISO_OUTPUT_RATE2(EXP_PISO_OUTPUT_RATE),
    .PISO_OUTPUT_RATE3(SIB_PISO_OUTPUT_RATE),
    .PISO_ACT_INPUT_RATE(REJS_PISO_INPUT_RATE),
    .PISO_ACT_OUTPUT_RATE(REJS_PISO_OUTPUT_RATE)
  ) abr_piso_inst (
    .clk(clk),
    .rst_b(rst_b),
    .zeroize(zeroize_piso),
    .mode(piso_mode),
    .valid_i(sha3_state_dv & sampler_mode_i inside {MLDSA_REJ_SAMPLER,MLDSA_REJ_BOUNDED,MLDSA_EXP_MASK,MLDSA_SAMPLE_IN_BALL}),
    .hold_o(sha3_state_hold),
    .data_i(sha3_state[0][REJS_PISO_INPUT_RATE-1:0]),
    .valid_o(piso_dv),
    .hold_i(piso_hold),
    .data_o(piso_data)
  );

  always_comb rejs_piso_dv = piso_dv & (sampler_mode_i == MLDSA_REJ_SAMPLER); 
  always_comb rejb_piso_dv = piso_dv & (sampler_mode_i == MLDSA_REJ_BOUNDED);
  always_comb exp_piso_dv = piso_dv & (sampler_mode_i == MLDSA_EXP_MASK);
  always_comb sib_piso_dv = piso_dv & (sampler_mode_i == MLDSA_SAMPLE_IN_BALL);

  always_comb piso_hold = ((sampler_mode_i == MLDSA_REJ_SAMPLER)    & rejs_piso_hold) |
                          ((sampler_mode_i == MLDSA_REJ_BOUNDED)    & rejb_piso_hold) |
                          ((sampler_mode_i == MLDSA_EXP_MASK)       & exp_piso_hold)  |
                          ((sampler_mode_i == MLDSA_SAMPLE_IN_BALL) & sib_piso_hold);

  always_comb rejs_piso_data = piso_data[REJS_PISO_OUTPUT_RATE-1:0];
  always_comb rejb_piso_data = piso_data[REJB_PISO_OUTPUT_RATE-1:0];
  always_comb exp_piso_data = piso_data[EXP_PISO_OUTPUT_RATE-1:0];
  always_comb sib_piso_data = piso_data[SIB_PISO_OUTPUT_RATE-1:0];

  rej_sampler_ctrl#(
    .REJ_NUM_SAMPLERS(REJS_NUM_SAMPLERS),
    .REJ_SAMPLE_W(REJS_SAMPLE_W),
    .REJ_VLD_SAMPLES(REJS_VLD_SAMPLES),
    .REJ_VALUE(MLDSA_Q)
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
  
//optimization - align sampler data in ntt
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
    .DATA_WIDTH((MLDSA_Q_WIDTH-1)*4),
    .DEPTH     (MLDSA_N/4),
    .NUM_PORTS (2)
  )
  sib_mem_inst
  (
    .clk_i(clk),
    .rst_b(rst_b),
    .zeroize(zeroize_sib_mem),
    .cs_i(sib_mem_cs_mux),
    .we_i(sib_mem_we),
    .addr_i(sib_mem_addr_mux),
    .wdata_i(sib_mem_wrdata),

    .rdata_o(sib_mem_rddata)
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