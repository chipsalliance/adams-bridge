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

module abr_sampler_top
  import abr_sampler_pkg::*;
  import abr_sha3_pkg::*;
  import abr_params_pkg::*;
  import abr_prim_alert_pkg::*;
  #(
    parameter SRAM_LATENCY = 1,
    parameter int ABR_NUM_NTT = 1,
    // Masking of the SHA3/Keccak core. Threaded from the top-level
    // SHA3_MASKING_EN parameter (no longer a package parameter).
    parameter bit Sha3EnMasking = 1,
    localparam int Sha3Share = (Sha3EnMasking) ? 2 : 1
  )
  (
  input logic clk,
  input logic rst_b,
  input logic zeroize,

  //input
  input abr_sampler_mode_e sampler_mode_i,
  //eta=4 select for ML-DSA-65 rejection bounded sampling. Public.
  input logic              mldsa_eta4_i,
  input logic              gamma1_17_i,
  //Active ML-KEM parameter set uses eta1 = 3 (ML-KEM-512 only). Public.
  input logic              eta3_i,
  //Number of non-zero challenge coefficients (FIPS 204 tau). Public.
  input logic [7:0]        mldsa_tau_i,

  input logic                    sha3_start_i,
  input logic                    sha3_masked_i,

  input logic                    msg_start_i,
  input logic                    msg_valid_i,
  output logic                   msg_rdy_o,
  input logic [MsgStrbW-1:0]     msg_strobe_i,
  input logic [MsgWidth-1:0]     msg_data_i[Sha3Share],

  input logic                    sampler_start_i,

  input logic [ABR_MEM_ADDR_WIDTH-1:0] dest_base_addr_i,

  //NTT read from sib_mem
  input mem_if_t                                      sib_mem_rd_req_i,
  output logic [COEFF_PER_CLK-1:0][MLDSA_Q_WIDTH-1:0] sib_mem_rd_data_o,

  //output
  output logic                     sampler_busy_o,

  output logic                                        sampler_ntt_dv_o,
  output logic [COEFF_PER_CLK-1:0][MLDSA_Q_WIDTH-1:0] sampler_ntt_data_o,

  output logic                                        sampler_mem_dv_o,
  output logic [ABR_MEM_DATA_WIDTH-1:0]               sampler_mem_data_o [ABR_NUM_NTT],
  output logic [ABR_MEM_ADDR_WIDTH-1:0]               sampler_mem_addr_o,

  // Splitter control
  input  logic                                        split_en_i,
  input  logic [ABR_MEM_DATA_WIDTH-1:0]               rand_i,

  // Dedicated masked-Keccak randomness (DOM multipliers)
  input  logic                                        keccak_rand_valid_i,
  input  logic                                        keccak_rand_early_i,
  input  logic [abr_sha3_pkg::StateW/2-1:0]           keccak_rand_data_i,
  input  logic                                        keccak_rand_aux_i,

  output logic                                        sampler_state_dv_o,
  output logic [abr_sha3_pkg::StateW-1:0]             sampler_state_data_o

  );

  `include "abr_prim_assert.sv"

  //Signal Declarations
  logic                    sha3_process;
  logic                    sha3_run;

  logic sha3_squeezing;

  logic sha3_block_processed;

  abr_sha3_pkg::sha3_st_e sha3_fsm;
  abr_sha3_pkg::err_t sha3_err;

  abr_sha3_pkg::sha3_mode_e mode;
  abr_sha3_pkg::keccak_strength_e strength;

  logic sha3_state_dv;
  logic sha3_state_hold;
  logic [abr_sha3_pkg::StateW-1:0] sha3_state_o[Sha3Share];
  logic [abr_sha3_pkg::StateW-1:0] sha3_state;

  logic sha3_state_error;
  logic sha3_count_error;
  logic sha3_rst_storage_err;

  //mldsa rej sampler
  logic                                                        mldsa_rejs_piso_dv;
  logic                                                        mldsa_rejs_piso_hold;

  logic                                            mldsa_rejs_dv;
  logic [REJS_VLD_SAMPLES-1:0][MLDSA_Q_WIDTH-1:0]  mldsa_rejs_data_q;

  //mlkem rej sampler
  logic                                                        mlkem_rejs_piso_dv;
  logic                                                        mlkem_rejs_piso_hold;

  logic                                            mlkem_rejs_dv;
  logic [REJS_VLD_SAMPLES-1:0][MLKEM_Q_WIDTH-1:0]  mlkem_rejs_data_q;

  //common rejs piso data
  logic [MLDSA_REJS_NUM_SAMPLERS-1:0][MLDSA_REJS_SAMPLE_W-1:0] rejs_piso_data;

  //rej bounded
  logic                                               rejb_piso_dv;
  logic                                               rejb_piso_hold;
  logic [REJB_NUM_SAMPLERS_MAX-1:0][REJB_SAMPLE_W-1:0] rejb_piso_data;

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
  logic [1:0][3:0][1:0]                          sib_mem_wrdata;
  logic [1:0][3:0][1:0]                          sib_mem_rddata;

  //cbd
  logic                                               cbd_piso_dv;
  logic                                               cbd_piso_hold;
  logic [CBD_NUM_SAMPLERS-1:0][CBD_SAMPLE_W_MAX-1:0]  cbd_piso_data;

  logic                                               cbd_dv;
  logic [CBD_VLD_SAMPLES-1:0][MLKEM_Q_WIDTH-1:0]      cbd_data;

  logic [ABR_MEM_ADDR_WIDTH-1:0] dest_addr;
  logic [$clog2(ABR_COEFF_CNT/4):0] coeff_cnt;
  logic vld_cycle;
  logic sampler_done;
  logic rejb_pad_hold;

  logic zeroize_sha3, zeroize_rejb, zeroize_mldsa_rejs, zeroize_sib, zeroize_exp_mask;
  logic zeroize_cbd, zeroize_mlkem_rejs;
  logic zeroize_sib_mem;
  logic zeroize_piso;

  abr_piso_mode_e piso_mode;
  logic sha3_piso_dv;
  logic piso_dv, piso_hold;
  logic [REJS_PISO_OUTPUT_RATE-1:0] piso_data;

  abr_sampler_fsm_state_e sampler_fsm_ps, sampler_fsm_ns;

  logic [COEFF_PER_CLK-1:0][MLDSA_Q_WIDTH-1:0] sampler_ntt_data[SRAM_LATENCY:0];

  // Pre-split signals (before splitter)
  logic                                        sampler_mem_dv_pre;
  logic [COEFF_PER_CLK-1:0][MLDSA_Q_WIDTH-1:0] sampler_mem_data_pre;
  logic [ABR_MEM_ADDR_WIDTH-1:0]               sampler_mem_addr_pre;

  logic splitter_en;
  logic splitter_ready;

  //Sampler mode muxes
  always_comb begin
    mode = abr_sha3_pkg::Shake;
    strength = abr_sha3_pkg::L256;
    vld_cycle = 0;
    sampler_done = 0;
    sampler_mem_dv_pre = 0;
    sampler_mem_data_pre = 0;
    sampler_mem_addr_pre = 0;
    sampler_state_dv_o = 0;
    sampler_state_data_o = 0;
    zeroize_rejb = zeroize;
    zeroize_mldsa_rejs = zeroize;
    zeroize_mlkem_rejs = zeroize;
    zeroize_exp_mask = zeroize;
    zeroize_sib = zeroize;
    zeroize_sib_mem = zeroize;
    zeroize_sha3 = zeroize;
    zeroize_cbd = zeroize;
    zeroize_piso = zeroize;
    piso_mode = ABR_REJS_MODE;

    unique case (sampler_mode_i) inside
      ABR_SHAKE256: begin
        mode = abr_sha3_pkg::Shake;
        strength = abr_sha3_pkg::L256;
        sampler_state_dv_o = sha3_state_dv;
        sampler_state_data_o = sha3_state;
        sampler_done = sha3_state_dv;
        zeroize_sha3 |= sha3_state_dv;
      end
      ABR_SHAKE128: begin
        mode = abr_sha3_pkg::Shake;
        strength = abr_sha3_pkg::L128;
        sampler_state_dv_o = sha3_state_dv;
        sampler_state_data_o = sha3_state;
        sampler_done = sha3_state_dv;
        zeroize_sha3 |= sha3_state_dv;
      end
      ABR_SHA512: begin
        mode = abr_sha3_pkg::Sha3;
        strength = abr_sha3_pkg::L512;
        sampler_state_dv_o = sha3_state_dv;
        sampler_state_data_o = sha3_state;
        sampler_done = sha3_state_dv;
        zeroize_sha3 |= sha3_state_dv;
      end
      ABR_SHA256: begin
        mode = abr_sha3_pkg::Sha3;
        strength = abr_sha3_pkg::L256;
        sampler_state_dv_o = sha3_state_dv;
        sampler_state_data_o = sha3_state;
        sampler_done = sha3_state_dv;
        zeroize_sha3 |= sha3_state_dv;
      end
      MLKEM_REJ_SAMPLER: begin
        mode = abr_sha3_pkg::Shake;
        strength = abr_sha3_pkg::L128;
        vld_cycle = mlkem_rejs_dv;
        sampler_done = (coeff_cnt == (ABR_COEFF_CNT/4));
        zeroize_mlkem_rejs |= sampler_done;
        zeroize_sha3 |= sampler_done;
        zeroize_piso |= sampler_done;
        piso_mode = ABR_REJS_MODE;
      end
      MLDSA_REJ_SAMPLER: begin
        mode = abr_sha3_pkg::Shake;
        strength = abr_sha3_pkg::L128;
        vld_cycle = mldsa_rejs_dv;
        sampler_done = (coeff_cnt == (ABR_COEFF_CNT/4));
        zeroize_mldsa_rejs |= sampler_done;
        zeroize_sha3 |= sampler_done;
        zeroize_piso |= sampler_done;
        piso_mode = ABR_REJS_MODE;
      end
      ABR_EXP_MASK: begin
        mode = abr_sha3_pkg::Shake;
        strength = abr_sha3_pkg::L256;
        vld_cycle = exp_dv;
        sampler_mem_dv_pre = exp_dv;
        sampler_mem_data_pre = exp_data;
        sampler_mem_addr_pre = dest_addr;
        sampler_done = (coeff_cnt == (ABR_COEFF_CNT/4));
        zeroize_exp_mask |= sampler_done;
        zeroize_sha3 |= sampler_done;
        zeroize_piso |= sampler_done;
        piso_mode = gamma1_17_i ? ABR_EXP17_MODE : ABR_EXP_MODE;
      end
      ABR_REJ_BOUNDED: begin
        mode = abr_sha3_pkg::Shake;
        strength = abr_sha3_pkg::L256;
        vld_cycle = rejb_dv;
        sampler_mem_dv_pre = rejb_dv;
        sampler_mem_data_pre = rejb_data;
        sampler_mem_addr_pre = dest_addr;
        sampler_done = (coeff_cnt == (ABR_COEFF_CNT/4));
        zeroize_rejb |= sampler_done;
        zeroize_sha3 |= sampler_done;
        zeroize_piso |= sampler_done;
        piso_mode = (ABR_NEED_ETA4 & mldsa_eta4_i) ? ABR_REJB4_MODE : ABR_REJB_MODE;
      end
      ABR_SAMPLE_IN_BALL: begin
        mode = abr_sha3_pkg::Shake;
        strength = abr_sha3_pkg::L256;
        zeroize_sib_mem = sampler_start_i;
        sampler_done = sib_done;
        zeroize_sib |= sampler_done;
        zeroize_sha3 |= sampler_done;
        zeroize_piso |= sampler_done;
        piso_mode = ABR_SIB_MODE;
      end
      ABR_CBD_SAMPLER: begin
        mode = abr_sha3_pkg::Shake;
        strength = abr_sha3_pkg::L256;
        vld_cycle = cbd_dv;
        sampler_mem_dv_pre = cbd_dv;
        for (int coeff = 0; coeff < COEFF_PER_CLK; coeff++) begin
          sampler_mem_data_pre[coeff][MLKEM_Q_WIDTH-1:0] = cbd_data[coeff];
        end
        sampler_mem_addr_pre = dest_addr;
        sampler_done = (coeff_cnt == (ABR_COEFF_CNT/4));
        zeroize_cbd |= sampler_done;
        zeroize_sha3 |= sampler_done;
        zeroize_piso |= sampler_done;
        piso_mode = eta3_i ? ABR_CBD3_MODE : ABR_CBD_MODE;
      end
      ABR_SAMPLER_NONE: begin
        //do nothing
      end
      default: begin
        //do nothing
      end
    endcase
  end

//FSM Controller

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
    coeff_cnt <= sampler_start_i ? 0 :
                 vld_cycle ? coeff_cnt + 1 : coeff_cnt;
    dest_addr <= sampler_start_i ? dest_base_addr_i :
                 vld_cycle ? dest_addr + 1 : dest_addr;
  end
end

always_comb splitter_en = sampler_mem_dv_pre & split_en_i;

always_comb sampler_busy_o = sampler_start_i | (sampler_fsm_ps != ABR_SAMPLER_IDLE) |
                             (splitter_en | splitter_ready);

//State logic
always_comb begin : sampler_fsm_out_comb
    sampler_fsm_ns = sampler_fsm_ps;
    sha3_process = 0;
    sha3_run = 0;

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
          sampler_fsm_ns = rejb_pad_hold ? ABR_SAMPLER_PAD : ABR_SAMPLER_DONE;
        end else if (sha3_state_dv & ~sha3_state_hold) begin
          sampler_fsm_ns = ABR_SAMPLER_RUN;
        end
      end
      ABR_SAMPLER_RUN: begin
        if (sampler_done) begin
          sampler_fsm_ns = rejb_pad_hold ? ABR_SAMPLER_PAD : ABR_SAMPLER_DONE;
        end else begin 
          sampler_fsm_ns = ABR_SAMPLER_WAIT;
          //drive run signal
          sha3_run = 1;
        end
      end
      ABR_SAMPLER_PAD: begin
        //Sampling is finished; stay busy until the constant observable length
        //has elapsed so the activation cannot be timed against the secret.
        if (~rejb_pad_hold) begin
          sampler_fsm_ns = ABR_SAMPLER_DONE;
        end
      end
      ABR_SAMPLER_DONE: begin
        //Go to IDLE when sha3 resets
        if (~sha3_squeezing) begin 
          sampler_fsm_ns = ABR_SAMPLER_IDLE;
        end
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

    // Entropy interface - masked Keccak DOM randomness
    .rand_valid_i    (keccak_rand_valid_i),
    .rand_early_i    (keccak_rand_early_i),
    .rand_data_i     (keccak_rand_data_i),
    .rand_aux_i      (keccak_rand_aux_i),
    .rand_update_o   (),
    .rand_consumed_o (),

    // Configurations
    .mode_i     (mode), 
    .strength_i (strength), 

    // Controls (CMD register)
    .start_i    (sha3_start_i),
    .masked_i   (sha3_masked_i),
    .process_i  (sha3_process),
    .run_i      (sha3_run), // For squeeze

    .absorbed_o (),
    .squeezing_o (sha3_squeezing),

    .block_processed_o (sha3_block_processed),

    .sha3_fsm_o (sha3_fsm),

    .state_valid_o      (sha3_state_dv),
    .state_valid_hold_i (sha3_state_hold),
    .state_o            (sha3_state_o),

    .error_o            (sha3_err),
    .sparse_fsm_error_o (sha3_state_error),
    .count_error_o      (sha3_count_error),
    .keccak_storage_rst_error_o (sha3_rst_storage_err)
  );

  always_comb sha3_piso_dv = sha3_state_dv & (sampler_mode_i inside {MLKEM_REJ_SAMPLER, MLDSA_REJ_SAMPLER, ABR_EXP_MASK,
                                                                     ABR_REJ_BOUNDED, ABR_SAMPLE_IN_BALL, ABR_CBD_SAMPLER});

generate
  if (Sha3EnMasking) begin : gen_sha3_masking_recombine
  //simple recombine
  abr_prim_xor2 #(
    .Width (abr_sha3_pkg::StateW)
  ) u_abr_prim_xor_sha3_state (
    .in0_i (sha3_state_o[0]),
    .in1_i (sha3_state_o[1]),
    .out_o (sha3_state)
  );
  end else begin
      assign sha3_state = sha3_state_o[0];
  end
endgenerate
  

  //Multi-rate piso.
  //The eta = 4 RejBounded rate is an eighth mode, so it is only elaborated when
  //ML-DSA-65 is compiled in. Keeping the seven-mode instance for every other
  //configuration preserves the "comment the defines out and category 5 is
  //structurally untouched" property - with NUM_MODES = 7 the code 3'b111 is out
  //of range and clamps, exactly as it did before this change.
  generate
    if (ABR_NEED_ETA4) begin : g_piso_eta4
      abr_piso_multi #(
        .NUM_MODES(8),
        .PISO_BUFFER_W(REJS_PISO_BUFFER_W),
        .PISO_ACT_INPUT_RATE(REJS_PISO_INPUT_RATE),
        .PISO_ACT_OUTPUT_RATE(REJS_PISO_OUTPUT_RATE),
        .INPUT_RATES('{REJS_PISO_INPUT_RATE, REJB_PISO_INPUT_RATE, EXP_PISO_INPUT_RATE, SIB_PISO_INPUT_RATE, CBD_PISO_INPUT_RATE, EXP_PISO_INPUT_RATE, CBD_PISO_INPUT_RATE, REJB_PISO_INPUT_RATE}),
        .OUTPUT_RATES('{REJS_PISO_OUTPUT_RATE, REJB_PISO_OUTPUT_RATE, EXP_PISO_OUTPUT_RATE, SIB_PISO_OUTPUT_RATE, CBD_PISO_OUTPUT_RATE, EXP_PISO_OUTPUT_RATE_17, CBD_PISO_OUTPUT_RATE_3, REJB_PISO_OUTPUT_RATE_ETA4})
      ) abr_piso_inst (
        .clk(clk),
        .rst_b(rst_b),
        .zeroize(zeroize_piso),
        .mode(piso_mode),
        .valid_i(sha3_piso_dv),
        .hold_o(sha3_state_hold),
        .data_i(sha3_state[REJS_PISO_INPUT_RATE-1:0]),
        .valid_o(piso_dv),
        .hold_i(piso_hold),
        .data_o(piso_data)
      );
    end else begin : g_piso
      abr_piso_multi #(
        .NUM_MODES(7),
        .PISO_BUFFER_W(REJS_PISO_BUFFER_W),
        .PISO_ACT_INPUT_RATE(REJS_PISO_INPUT_RATE),
        .PISO_ACT_OUTPUT_RATE(REJS_PISO_OUTPUT_RATE),
        .INPUT_RATES('{REJS_PISO_INPUT_RATE, REJB_PISO_INPUT_RATE, EXP_PISO_INPUT_RATE, SIB_PISO_INPUT_RATE, CBD_PISO_INPUT_RATE, EXP_PISO_INPUT_RATE, CBD_PISO_INPUT_RATE}),
        .OUTPUT_RATES('{REJS_PISO_OUTPUT_RATE, REJB_PISO_OUTPUT_RATE, EXP_PISO_OUTPUT_RATE, SIB_PISO_OUTPUT_RATE, CBD_PISO_OUTPUT_RATE, EXP_PISO_OUTPUT_RATE_17, CBD_PISO_OUTPUT_RATE_3})
      ) abr_piso_inst (
        .clk(clk),
        .rst_b(rst_b),
        .zeroize(zeroize_piso),
        .mode(piso_mode),
        .valid_i(sha3_piso_dv),
        .hold_o(sha3_state_hold),
        .data_i(sha3_state[REJS_PISO_INPUT_RATE-1:0]),
        .valid_o(piso_dv),
        .hold_i(piso_hold),
        .data_o(piso_data)
      );
    end
  endgenerate

  logic sha3_state_dv_q;
  logic sha3_state_dv_rise;
  logic rejb_hold_done;         // sticky: cleared on start, set after first hold
  logic [$clog2(REJB_MASKED_KECCAK_HOLD_MAX+2)-1:0] rejb_hold_cnt;
  logic [$clog2(REJB_MASKED_KECCAK_HOLD_MAX+2)-1:0] rejb_hold_val;
  logic rejb_hold_active;

  always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b)                         sha3_state_dv_q <= 1'b0;
    else if (zeroize | sampler_start_i) sha3_state_dv_q <= 1'b0;
    else                                sha3_state_dv_q <= sha3_state_dv;
  end
  always_comb sha3_state_dv_rise = sha3_state_dv & ~sha3_state_dv_q;

  generate
    if (!Sha3EnMasking || (REJB_MASKED_KECCAK_HOLD_MAX == 0)) begin : g_no_rejb_hold
      always_comb rejb_hold_cnt    = '0;
      always_comb rejb_hold_val    = '0;
      always_comb rejb_hold_active = 1'b0;
      always_comb rejb_hold_done   = 1'b1;
    end else begin : g_rejb_hold
      // The eta = 4 bank drains a PISO word more slowly, so it needs a longer
      // head start before the second Keccak state is guaranteed to be in flight.
      always_comb rejb_hold_val = (ABR_NEED_ETA4 & mldsa_eta4_i)
                   ? $bits(rejb_hold_val)'(REJB_MASKED_KECCAK_HOLD_ETA4)
                   : $bits(rejb_hold_val)'(REJB_MASKED_KECCAK_HOLD_MASKED);
      // Load counter only on the FIRST sha3_state_dv rise per rejb activation.
      always_ff @(posedge clk or negedge rst_b) begin
        if (!rst_b) begin
          rejb_hold_cnt  <= '0;
          rejb_hold_done <= 1'b0;
        end else if (zeroize | sampler_start_i) begin
          rejb_hold_cnt  <= '0;
          rejb_hold_done <= 1'b0;
        end else if ((sampler_mode_i == ABR_REJ_BOUNDED)
                     && sha3_state_dv_rise
                     && !rejb_hold_done) begin
          rejb_hold_cnt  <= rejb_hold_val;
          rejb_hold_done <= 1'b1;
        end else if (rejb_hold_cnt != 0) begin
          rejb_hold_cnt  <= rejb_hold_cnt - 1'b1;
        end
      end
      always_comb rejb_hold_active = (rejb_hold_cnt != 0);
    end
  endgenerate

  //--------------------------------------------------------------------------
  //Constant observable length for eta = 4 RejBounded activations.
  //
  //HOLD makes the drain demand limited, which removes every seed dependence the
  //loop has *provided* the two resident Keccak states supply the 256 accepted
  //coefficients. At eta = 2 that holds with probability 1 - 5.3e-194 and needs
  //no further argument. At eta = 4 the acceptance rate is 9/16, so it holds only
  //with probability 1 - 7.0e-6, and the rare polynomial that needs a third
  //squeeze finishes roughly a masked permutation late. That residual is a direct
  //timing dependence on s1/s2, so it is closed here by holding the activation in
  //ABR_SAMPLER_PAD until a compile time constant number of cycles has elapsed.
  //
  //Deepening the PISO is not an alternative: the third Keccak state is not ready
  //before ~329 sampler cycles whatever the buffer depth, while the drain has
  //ended by 260. Only time closes this.
  //--------------------------------------------------------------------------
  generate
    if (ABR_NEED_ETA4) begin : g_rejb_pad
      logic [$clog2(REJB_ETA4_FIXED_LEN+1)-1:0] rejb_pad_cnt;
      always_ff @(posedge clk or negedge rst_b) begin
        if (!rst_b) begin
          rejb_pad_cnt <= '0;
        end else if (zeroize | sampler_start_i) begin
          rejb_pad_cnt <= '0;
        end else if (rejb_pad_cnt != $bits(rejb_pad_cnt)'(REJB_ETA4_FIXED_LEN)) begin
          rejb_pad_cnt <= rejb_pad_cnt + 1'b1;
        end
      end
      always_comb rejb_pad_hold = mldsa_eta4_i &
                                  (sampler_mode_i == ABR_REJ_BOUNDED) &
                                  (rejb_pad_cnt != $bits(rejb_pad_cnt)'(REJB_ETA4_FIXED_LEN));

      //An eta = 4 RejBounded activation must not be able to reach ABR_SAMPLER_DONE
      //- and therefore must not be able to drop sampler_busy_o - before the pad
      //has expired. This is the direct statement of the constant observable
      //length, as opposed to ERR_REJB_ETA4_PAD_UNDERSIZED which only says the
      //natural completion lands inside the pad window.
      `ABR_ASSERT_NEVER(ERR_REJB_ETA4_EARLY_DONE,
          mldsa_eta4_i && (sampler_mode_i == ABR_REJ_BOUNDED) &&
          (sampler_fsm_ps == ABR_SAMPLER_DONE) &&
          (rejb_pad_cnt != $bits(rejb_pad_cnt)'(REJB_ETA4_FIXED_LEN)), clk, !rst_b)

      //The sequencer gates a new start on ~sampler_busy_i, so a start pulse can
      //never land in the pad. If it ever did it would reset the pad counter
      //without launching an operation and stretch the pad indefinitely.
      `ABR_ASSERT_NEVER(ERR_REJB_START_DURING_PAD,
          sampler_start_i && (sampler_fsm_ps == ABR_SAMPLER_PAD), clk, !rst_b)
    end else begin : g_no_rejb_pad
      always_comb rejb_pad_hold = 1'b0;
    end
  endgenerate

  always_comb mldsa_rejs_piso_dv = piso_dv & (sampler_mode_i == MLDSA_REJ_SAMPLER); 
  always_comb mlkem_rejs_piso_dv = piso_dv & (sampler_mode_i == MLKEM_REJ_SAMPLER); 
  // Constant-time pause: hide piso_dv from rej_bounded for HOLD cycles
  // after the FIRST Keccak state completes (sha3_state_dv rising edge).
  always_comb rejb_piso_dv = piso_dv & (sampler_mode_i == ABR_REJ_BOUNDED) & ~rejb_hold_active;
  always_comb exp_piso_dv = piso_dv & (sampler_mode_i == ABR_EXP_MASK);
  always_comb sib_piso_dv = piso_dv & (sampler_mode_i == ABR_SAMPLE_IN_BALL);
  always_comb cbd_piso_dv = piso_dv & (sampler_mode_i == ABR_CBD_SAMPLER);

  always_comb piso_hold = ((sampler_mode_i == MLDSA_REJ_SAMPLER)    & mldsa_rejs_piso_hold) |
                          ((sampler_mode_i == MLKEM_REJ_SAMPLER)    & mlkem_rejs_piso_hold) |
                          ((sampler_mode_i == ABR_REJ_BOUNDED)    & (rejb_piso_hold | rejb_hold_active)) |
                          ((sampler_mode_i == ABR_EXP_MASK)       & exp_piso_hold)  |
                          ((sampler_mode_i == ABR_SAMPLE_IN_BALL) & sib_piso_hold)  |
                          ((sampler_mode_i == ABR_CBD_SAMPLER)    & cbd_piso_hold);

  always_comb rejs_piso_data = piso_data[REJS_PISO_OUTPUT_RATE-1:0];
  //At eta = 4 the PISO delivers REJB_NUM_SAMPLERS_ETA4 half bytes per cycle;
  //at eta = 2 only the low REJB_NUM_SAMPLERS lanes are driven and the rest are
  //held at zero so the unused eta = 4 samplers cannot see stale PISO bits.
  always_comb begin
    rejb_piso_data = '0;
    if (ABR_NEED_ETA4 & mldsa_eta4_i)
      rejb_piso_data = piso_data[REJB_PISO_OUTPUT_RATE_MAX-1:0];
    else
      rejb_piso_data[REJB_NUM_SAMPLERS-1:0] = piso_data[REJB_PISO_OUTPUT_RATE-1:0];
  end
  //ML-DSA-44 delivers 18-bit samples; zero-extend into the 20-bit lanes so the
  //downstream exp_mask instances keep a single width.
  always_comb begin
    if (ABR_NEED_GAMMA1_17 & gamma1_17_i) begin
      for (int i = 0; i < EXP_NUM_SAMPLERS; i++)
        exp_piso_data[i] = EXP_SAMPLE_W'(piso_data[(i*EXP_SAMPLE_W_17) +: EXP_SAMPLE_W_17]);
    end
    else begin
      for (int i = 0; i < EXP_NUM_SAMPLERS; i++)
        exp_piso_data[i] = piso_data[(i*EXP_SAMPLE_W) +: EXP_SAMPLE_W];
    end
  end
  always_comb sib_piso_data = piso_data[SIB_PISO_OUTPUT_RATE-1:0];
  //Unpack CBD samples into fixed width lanes. At eta1 = 3 the samples are 6 bits
  //wide; at eta = 2 they are 4 bits and are zero extended into the same lanes,
  //which is arithmetically inert because the sampler only reads 2*eta bits.
  always_comb begin
    for (int unsigned i = 0; i < CBD_NUM_SAMPLERS; i++) begin
      if (ABR_NEED_CBD3 & eta3_i)
        cbd_piso_data[i] = piso_data[i*CBD_SAMPLE_W_3 +: CBD_SAMPLE_W_3];
      else
        cbd_piso_data[i] = CBD_SAMPLE_W_MAX'(piso_data[i*CBD_SAMPLE_W +: CBD_SAMPLE_W]);
    end
  end

  rej_sampler_ctrl#(
    .REJ_NUM_SAMPLERS(MLDSA_REJS_NUM_SAMPLERS),
    .REJ_SAMPLE_W(MLDSA_REJS_SAMPLE_W),
    .REJ_VLD_SAMPLES(REJS_VLD_SAMPLES),
    .REJ_VLD_SAMPLES_W(MLDSA_Q_WIDTH),
    .REJ_VALUE(MLDSA_Q)
  ) mldsa_rej_sampler_inst (
    .clk(clk),
    .rst_b(rst_b),
    .zeroize(zeroize_mldsa_rejs), 
    //input data
    .data_valid_i(mldsa_rejs_piso_dv),
    .data_hold_o(mldsa_rejs_piso_hold),
    .data_i(rejs_piso_data),

    //output data
    .data_valid_o(mldsa_rejs_dv),
    .data_o(mldsa_rejs_data_q)
  );
  
  rej_sampler_ctrl#(
    .REJ_NUM_SAMPLERS(MLKEM_REJS_NUM_SAMPLERS),
    .REJ_SAMPLE_W(MLKEM_REJS_SAMPLE_W),
    .REJ_VLD_SAMPLES(REJS_VLD_SAMPLES),
    .REJ_VLD_SAMPLES_W(MLKEM_Q_WIDTH),
    .REJ_VALUE(MLKEM_Q)
  ) mlkem_rej_sampler_inst (
    .clk(clk),
    .rst_b(rst_b),
    .zeroize(zeroize_mlkem_rejs), 
    //input data
    .data_valid_i(mlkem_rejs_piso_dv),
    .data_hold_o(mlkem_rejs_piso_hold),
    .data_i(rejs_piso_data),

    //output data
    .data_valid_o(mlkem_rejs_dv),
    .data_o(mlkem_rejs_data_q)
  );

//optimization - align sampler data in ntt
  always_comb begin
    for (int i = 0; i < COEFF_PER_CLK; i++) begin
      sampler_ntt_data[0][i] = {MLDSA_Q_WIDTH{(sampler_mode_i == MLDSA_REJ_SAMPLER)}} & mldsa_rejs_data_q[i] | 
                               {MLDSA_Q_WIDTH{(sampler_mode_i == MLKEM_REJ_SAMPLER)}} & {{MLDSA_Q_WIDTH-MLKEM_Q_WIDTH{1'b0}},mlkem_rejs_data_q[i]};
    end
  end

generate
  for (genvar g_stage = 1; g_stage <= SRAM_LATENCY; g_stage++) begin : ntt_data_stage
    always_ff  @(posedge clk or negedge rst_b) begin : delay_rejs_data
      if (!rst_b) begin
        sampler_ntt_data[g_stage] <= '0;
      end
      else if (zeroize) begin
        sampler_ntt_data[g_stage] <= '0;
      end
      else if (sampler_mode_i inside {MLDSA_REJ_SAMPLER,MLKEM_REJ_SAMPLER})begin
        for (int i = 0; i < COEFF_PER_CLK; i++) begin
          sampler_ntt_data[g_stage][i] <= sampler_ntt_data[g_stage-1][i];
        end
      end
    end  
  end
endgenerate

//rej sampler output gets sent to NTT
always_comb sampler_ntt_dv_o = mldsa_rejs_dv | mlkem_rejs_dv;
always_comb sampler_ntt_data_o = sampler_ntt_data[SRAM_LATENCY];

//rej bounded
  rej_bounded_ctrl #(
    .REJ_NUM_SAMPLERS(REJB_NUM_SAMPLERS),
    .REJ_SAMPLE_W(REJB_SAMPLE_W),
    .REJ_VLD_SAMPLES(REJB_VLD_SAMPLES),
    .REJ_VLD_SAMPLES_W(REJB_VLD_SAMPLES_W),
    .REJ_VALUE(REJB_VALUE),
    .REJ_NUM_SAMPLERS_ETA4(REJB_NUM_SAMPLERS_ETA4)
  ) rej_bounded_inst (
    .clk(clk),
    .rst_b(rst_b),
    .zeroize(zeroize_rejb), 
    .eta4_i(mldsa_eta4_i),
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
    .gamma1_17_i(gamma1_17_i), 
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

  //Expand encoded sample in ball data
  always_comb begin
    for (int i = 0; i < 4; i++) begin
      unique case (sib_mem_rddata[0][i]) inside
        2'b00: sib_mem_rd_data_o[i] = 0;
        2'b01: sib_mem_rd_data_o[i] = 1;
        2'b11: sib_mem_rd_data_o[i] = MLDSA_Q-1;
        default: sib_mem_rd_data_o[i] = '0;
      endcase
    end
  end

  sib_mem
  #(
    .DATA_WIDTH(2*COEFF_PER_CLK), //encoded 2 bits per sample
    .DEPTH     (MLDSA_N/COEFF_PER_CLK),
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

  sample_in_ball_ctrl
  #(
    .SIB_NUM_SAMPLERS(SIB_NUM_SAMPLERS),
    .SIB_SAMPLE_W(SIB_SAMPLE_W),
    .SIB_TAU(SIB_TAU)
  ) sib_inst (
    .clk(clk),
    .rst_b(rst_b),
    .zeroize(zeroize_sib), 
    //input data
    .data_valid_i(sib_piso_dv),
    .tau_i(mldsa_tau_i),
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

  cbd_sampler_ctrl
  cbd_sampler_inst (
  .clk(clk),
  .rst_b(rst_b),
  .zeroize(zeroize_cbd), 
  //input data
  .data_valid_i(cbd_piso_dv),
  .data_hold_o(cbd_piso_hold),
  .data_i(cbd_piso_data),
  .eta3_i(eta3_i),

  //output data
  .data_valid_o(cbd_dv),
  .data_o(cbd_data)
  );

  // --- Arithmetic share splitter ---
  // Splits sampler memory writes into share0 (random) and share1 (data - random mod q).
  // 2-cycle latency; address and write-enable are delayed to align.
  logic [ABR_MEM_DATA_WIDTH-1:0] splitter_share0, splitter_share1;
  logic splitter_mode; // 0 = MLDSA, 1 = MLKEM
  assign splitter_mode = (sampler_mode_i == ABR_CBD_SAMPLER);

  abr_splitter u_splitter (
    .clk     (clk),
    .reset_n (rst_b),
    .zeroize (zeroize),
    .en_i    (splitter_en),
    .mode    (splitter_mode),
    .data_i  (sampler_mem_data_pre),
    .rand_i  (rand_i),
    .share0_o(splitter_share0),
    .share1_o(splitter_share1),
    .ready_o (splitter_ready)
  );

  // Address delay chain to align with splitter output (2-cycle pipeline)
  logic [ABR_MEM_ADDR_WIDTH-1:0] split_addr_d1, split_addr_d2;
  always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b) begin
      split_addr_d1 <= '0;
      split_addr_d2 <= '0;
    end
    else if (zeroize) begin
      split_addr_d1 <= '0;
      split_addr_d2 <= '0;
    end
    else begin
      split_addr_d1 <= sampler_mem_addr_pre;
      split_addr_d2 <= split_addr_d1;
    end
  end

  // Output mux: split path or bypass
  always_comb begin
    if (split_en_i) begin
      sampler_mem_dv_o     = splitter_ready;
      sampler_mem_data_o[0] = splitter_share0;
      sampler_mem_addr_o   = split_addr_d2;
    end else begin
      sampler_mem_dv_o     = sampler_mem_dv_pre;
      sampler_mem_data_o[0] = sampler_mem_data_pre;
      sampler_mem_addr_o   = sampler_mem_addr_pre;
    end
  end

  // share[1] output — present only when masking is enabled.
  generate if (ABR_NUM_NTT > 1) begin : g_sampler_share1_out
    always_comb begin
      sampler_mem_data_o[1] = split_en_i ? splitter_share1 : sampler_mem_data_pre;
    end
  end endgenerate

  `ABR_ASSERT_MUTEX(ERR_SAMPLER_O_MUTEX, {sampler_ntt_dv_o,sampler_mem_dv_o,sampler_state_dv_o}, clk, !rst_b)

  `ABR_ASSERT_NEVER(ERR_SIBMEM_ACCESS, (sib_mem_rd_req_i.rd_wr_en == RW_READ) && |sib_mem_cs, clk, !rst_b)

  `ABR_ASSERT_KNOWN(ERR_SAMPLER_FSM_X, sampler_fsm_ps, clk, !rst_b)
  `ABR_ASSERT_KNOWN(ERR_SAMPLER_MODE_X, sampler_mode_i, clk, !rst_b)
  `ABR_ASSERT_KNOWN(ERR_SAMPLER_NTT_DATA_X, sampler_ntt_data_o, clk, !rst_b, sampler_ntt_dv_o)
  `ABR_ASSERT_KNOWN(ERR_SAMPLER_MEM_DATA_X, sampler_mem_data_o[0], clk, !rst_b, sampler_mem_dv_o)
  `ABR_ASSERT_KNOWN(ERR_SAMPLER_STATE_DATA_X, sampler_state_data_o, clk, !rst_b, sampler_state_dv_o)

  // Every ABR_REJ_BOUNDED request must run masked (same-cycle check).
  `ABR_ASSERT_NEVER(ERR_REJB_UNMASKED_ON_MASKED_BUILD,
      sampler_start_i && (sampler_mode_i == ABR_REJ_BOUNDED) && Sha3EnMasking && !sha3_masked_i,
      clk, !rst_b)

  // The eta = 4 bank needs REJB_NUM_SAMPLERS_ETA4 half bytes per cycle to stay
  // demand limited (see docs/AdamsBridge_MLDSA.md, "eta = 4 (ML-DSA-65)").
  // If the PISO were ever left in the eta = 2 mode while eta4 is selected the
  // bank would silently become supply limited and the RejBounded loop length
  // would start tracking the rejection pattern of the secret s1/s2.
  `ABR_ASSERT(ERR_REJB_PISO_MODE_MISMATCH,
      ((sampler_mode_i == ABR_REJ_BOUNDED) && ABR_NEED_ETA4) |->
        (piso_mode == (mldsa_eta4_i ? ABR_REJB4_MODE : ABR_REJB_MODE)),
      clk, !rst_b)

  // The constant-time stall must be sized for the active eta. Loading the
  // category-5 value while eta4 is selected reopens the same leak.
  `ABR_ASSERT(ERR_REJB_HOLD_VAL_MISMATCH,
      (Sha3EnMasking && ABR_NEED_ETA4 && mldsa_eta4_i) |->
        (rejb_hold_val == $bits(rejb_hold_val)'(REJB_MASKED_KECCAK_HOLD_ETA4)),
      clk, !rst_b)

  // The pad must always be longer than the natural completion, otherwise the
  // activation escapes through the un-padded path and the length becomes secret
  // dependent again. This fires if REJB_ETA4_FIXED_LEN is ever sized too short
  // for the masked Keccak latency it has to cover.
  `ABR_ASSERT(ERR_REJB_ETA4_PAD_UNDERSIZED,
      (ABR_NEED_ETA4 && mldsa_eta4_i && (sampler_mode_i == ABR_REJ_BOUNDED) && sampler_done)
        |-> rejb_pad_hold,
      clk, !rst_b)

  // The pad exists only for eta = 4. Category 5 must never enter it.
  `ABR_ASSERT_NEVER(ERR_REJB_PAD_AT_ETA2,
      (sampler_fsm_ps == ABR_SAMPLER_PAD) && !mldsa_eta4_i, clk, !rst_b)

`ifndef SYNTHESIS
  //--------------------------------------------------------------------------
  //RejBounded loop-length profiler (simulation only, off unless +abr_rejb_profile
  //is passed). The constant-time argument for RejBounded is a claim about the
  //number of cycles between activation and completion being independent of the
  //secret seed, so it needs to be measurable rather than argued. Enable the
  //plusarg and grep the log for ABR_REJB_LEN; a constant-time build prints the
  //same length for every activation at a given parameter set.
  //
  //The statistics are binned per eta, because eta=2 and eta=4 legitimately have
  //different (but individually constant) loop lengths. A test that switches
  //parameter sets mid-run visits both bins, and pooling them would report a
  //spread that reflects the parameter set rather than the secret.
  //
  //Two lengths are reported.
  //  nat = sampler_start_i -> sampler_done. This is the *natural* length of the
  //        sampling loop. At eta = 4 it is constant only up to the 7e-6 chance
  //        of needing a third Keccak squeeze.
  //  obs = sampler_start_i -> sampler_busy_o falling. This is what the sequencer
  //        and therefore an external observer actually sees, and it is the one
  //        the constant-time claim rests on. ABR_SAMPLER_PAD makes it constant at
  //        eta = 4 whether or not a third squeeze happened.
  //min/max/spread track obs; natmin/natmax/natspread track nat.
  //--------------------------------------------------------------------------
  // synopsys translate_off
  bit         rejb_prof_en;
  int         rejb_prof_cnt;
  int         rejb_prof_nat;
  bit         rejb_prof_active;
  int         rejb_prof_min [0:1];
  int         rejb_prof_max [0:1];
  int         rejb_prof_natmin [0:1];
  int         rejb_prof_natmax [0:1];
  int         rejb_prof_num [0:1];
  bit         rejb_prof_eta4;
  //Write trace: the cycle of the first and last sampler_mem_dv_o beat, and the
  //number of beats, all relative to sampler_start_i. This is the *internal*
  //activity trace. It is not visible outside abr_top - the sequencer only sees
  //sampler_busy_o - but making it a measured constant rather than an assumed
  //one is what the category-5 constant-time argument itself rests on, so it is
  //measured here too.
  int         rejb_prof_wf;
  int         rejb_prof_wl;
  int         rejb_prof_wn;
  int         rejb_prof_wfmin [0:1];
  int         rejb_prof_wfmax [0:1];
  int         rejb_prof_wlmin [0:1];
  int         rejb_prof_wlmax [0:1];
  int         rejb_prof_wnmin [0:1];
  int         rejb_prof_wnmax [0:1];

  initial begin
    rejb_prof_en  = $test$plusargs("abr_rejb_profile");
    for (int b = 0; b < 2; b++) begin
      rejb_prof_min[b]    = 32'h7fff_ffff;
      rejb_prof_max[b]    = 0;
      rejb_prof_natmin[b] = 32'h7fff_ffff;
      rejb_prof_natmax[b] = 0;
      rejb_prof_num[b]    = 0;
      rejb_prof_wfmin[b]  = 32'h7fff_ffff;
      rejb_prof_wfmax[b]  = 0;
      rejb_prof_wlmin[b]  = 32'h7fff_ffff;
      rejb_prof_wlmax[b]  = 0;
      rejb_prof_wnmin[b]  = 32'h7fff_ffff;
      rejb_prof_wnmax[b]  = 0;
    end
  end

  always @(posedge clk) begin
    if (!rst_b) begin
      rejb_prof_active <= 1'b0;
      rejb_prof_cnt    <= 0;
      rejb_prof_nat    <= 0;
      rejb_prof_wf     <= 0;
      rejb_prof_wl     <= 0;
      rejb_prof_wn     <= 0;
    end else if (rejb_prof_en) begin
      if (sampler_start_i && (sampler_mode_i == ABR_REJ_BOUNDED)) begin
        rejb_prof_active <= 1'b1;
        rejb_prof_cnt    <= 0;
        rejb_prof_nat    <= 0;
        rejb_prof_wf     <= 0;
        rejb_prof_wl     <= 0;
        rejb_prof_wn     <= 0;
        rejb_prof_eta4   <= mldsa_eta4_i;
      end else if (rejb_prof_active) begin
        if (sampler_done && (sampler_mode_i == ABR_REJ_BOUNDED)) begin
          rejb_prof_nat <= rejb_prof_cnt;
        end
        if (sampler_mem_dv_o) begin
          if (rejb_prof_wn == 0) rejb_prof_wf <= rejb_prof_cnt;
          rejb_prof_wl <= rejb_prof_cnt;
          rejb_prof_wn <= rejb_prof_wn + 1;
        end
        if (!sampler_busy_o) begin
          rejb_prof_active <= 1'b0;
          rejb_prof_num[rejb_prof_eta4] = rejb_prof_num[rejb_prof_eta4] + 1;
          if (rejb_prof_cnt < rejb_prof_min[rejb_prof_eta4])
            rejb_prof_min[rejb_prof_eta4] = rejb_prof_cnt;
          if (rejb_prof_cnt > rejb_prof_max[rejb_prof_eta4])
            rejb_prof_max[rejb_prof_eta4] = rejb_prof_cnt;
          if (rejb_prof_nat < rejb_prof_natmin[rejb_prof_eta4])
            rejb_prof_natmin[rejb_prof_eta4] = rejb_prof_nat;
          if (rejb_prof_nat > rejb_prof_natmax[rejb_prof_eta4])
            rejb_prof_natmax[rejb_prof_eta4] = rejb_prof_nat;
          $display({"ABR_REJB_LEN eta4=%0d len=%0d nat=%0d n=%0d min=%0d max=%0d ",
                    "spread=%0d natmin=%0d natmax=%0d natspread=%0d"},
                   rejb_prof_eta4, rejb_prof_cnt, rejb_prof_nat,
                   rejb_prof_num[rejb_prof_eta4],
                   rejb_prof_min[rejb_prof_eta4], rejb_prof_max[rejb_prof_eta4],
                   rejb_prof_max[rejb_prof_eta4] - rejb_prof_min[rejb_prof_eta4],
                   rejb_prof_natmin[rejb_prof_eta4], rejb_prof_natmax[rejb_prof_eta4],
                   rejb_prof_natmax[rejb_prof_eta4] - rejb_prof_natmin[rejb_prof_eta4]);
          if (rejb_prof_wf < rejb_prof_wfmin[rejb_prof_eta4])
            rejb_prof_wfmin[rejb_prof_eta4] = rejb_prof_wf;
          if (rejb_prof_wf > rejb_prof_wfmax[rejb_prof_eta4])
            rejb_prof_wfmax[rejb_prof_eta4] = rejb_prof_wf;
          if (rejb_prof_wl < rejb_prof_wlmin[rejb_prof_eta4])
            rejb_prof_wlmin[rejb_prof_eta4] = rejb_prof_wl;
          if (rejb_prof_wl > rejb_prof_wlmax[rejb_prof_eta4])
            rejb_prof_wlmax[rejb_prof_eta4] = rejb_prof_wl;
          if (rejb_prof_wn < rejb_prof_wnmin[rejb_prof_eta4])
            rejb_prof_wnmin[rejb_prof_eta4] = rejb_prof_wn;
          if (rejb_prof_wn > rejb_prof_wnmax[rejb_prof_eta4])
            rejb_prof_wnmax[rejb_prof_eta4] = rejb_prof_wn;
          $display({"ABR_REJB_WTRACE eta4=%0d first=%0d last=%0d beats=%0d ",
                    "firstspread=%0d lastspread=%0d beatspread=%0d"},
                   rejb_prof_eta4, rejb_prof_wf, rejb_prof_wl, rejb_prof_wn,
                   rejb_prof_wfmax[rejb_prof_eta4] - rejb_prof_wfmin[rejb_prof_eta4],
                   rejb_prof_wlmax[rejb_prof_eta4] - rejb_prof_wlmin[rejb_prof_eta4],
                   rejb_prof_wnmax[rejb_prof_eta4] - rejb_prof_wnmin[rejb_prof_eta4]);
        end else begin
          rejb_prof_cnt <= rejb_prof_cnt + 1;
        end
      end
    end
  end
  // synopsys translate_on
`endif

endmodule
