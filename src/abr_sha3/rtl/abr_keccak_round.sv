// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Keccak full round logic based on given input `Width`
// e.g. Width 800 requires 22 rounds

`include "abr_sva.svh"
`include "abr_prim_assert.sv"

module abr_keccak_round
  import abr_prim_mubi_pkg::*;
#(
  parameter int Width = 1600, // b= {25, 50, 100, 200, 400, 800, 1600}
  parameter int RoundsPerClock = 1,

  // Derived
  localparam int W        = Width/25,
  localparam int L        = $clog2(W),
  localparam int MaxRound = 12 + 2*L,           // Keccak-f only
  localparam int RndW     = $clog2(MaxRound+1), // Representing up to MaxRound-1
 
  // Control parameters
  parameter  bit EnMasking = 1'b0,  // Enable SCA hardening, requires Width >= 50
  localparam int Share     = EnMasking ? 2 : 1
) (
  input clk_i,
  input rst_b,
  input logic zeroize,

  // Message Feed
  input [Width-1:0] data_i [Share],
  output            ready_o,

  // In-process control
  input logic               run_i,  // Pulse signal to initiates Keccak full round
  input logic               squeezing_i,
  input logic               rand_valid_i,
  input logic               rand_early_i,
  input logic [Width/2-1:0] rand_data_i,
  input logic               rand_aux_i,
  output logic              rand_consumed_o,

  output logic             complete_o, // Indicates full round is done

  // State out. This can be used as Digest
  output logic [Width-1:0] state_o [Share],

  // Errors:
  //  sparse_fsm_error: Checking if FSM state falls into unknown value
  output logic             sparse_fsm_error_o,
  //  round_count_error: abr_prim_count checks round value consistency
  output logic             round_count_error_o,
  //  rst_storage_error: check if reset signal asserted out of the
  //                     permitted window
  output logic             rst_storage_error_o,

  input  abr_prim_mubi_pkg::mubi4_t clear_i     // Clear internal state to '0
);

  /////////////////////
  // Control signals //
  /////////////////////

  // Update storage register
  logic update_storage;
  logic update_serial_buffer;

  // Reset the storage to 0 to initiate new Hash operation
  logic rst_storage;
  logic rst_serial_buffer;

  // XOR message into storage register
  logic xor_message;

  // Select Keccak_p datapath
  // 0: Select Phase1 (Theta -> Rho -> Pi)
  // 1: Select Phase2 (Chi -> Iota)
  // `phase_sel` needs to be asserted until the Chi stage is consumed,
  mubi4_t phase_sel;

  // Cycle index used for controlling input/output muxes and write enables inside
  // keccak_2share.
  logic [1:0] cycle;

  // Increase/ Reset Round number
  logic inc_rnd_num;
  logic rst_rnd_num;

  // Round reaches end
  // This signal indicates the round reaches desired number, which is MaxRound -1.
  // MaxRound is dependant on the Width. In case of SHA3/SHAKE, MaxRound is 24.
  logic rnd_eq_end;

  // Complete of Keccak_f
  // State machine asserts `complete_d` when it reaches at the end of round and
  // operation (Phase3 if Masked). The the stage, the storage still doesn't have
  // the valid states. So precisely it is not completed yet.
  // State generated `complete_d` is latched with the clock and creates a pulse
  // signal one cycle later. The signal is the indication of completion.
  //
  // Intentionally removed any intermediate step (so called StComplete) in order
  // to save a clock to proceeds next round.
  logic complete_d;

  //////////////////////
  // Datapath Signals //
  //////////////////////

  // Single round keccak output data
  logic [Width-1:0] keccak_out [Share];

  // Keccak Round indicator: range from 0 .. MaxRound
  logic [RndW-1:0] round;

  // Random value and valid signal used in Keccak_p
  logic               keccak_rand_consumed;
  logic [Width/2-1:0] keccak_rand_data;
  logic               keccak_rand_aux;

  //////////////////////
  // Keccak Round FSM //
  //////////////////////

  // state inputs
  assign rnd_eq_end = (int'(round) == MaxRound - RoundsPerClock);

  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 3 -m 8 -n 6 \
  //      -s 1363425333 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: |||||||||||||||||||| (57.14%)
  //  4: ||||||||||||||| (42.86%)
  //  5: --
  //  6: --
  //
  // Minimum Hamming distance: 3
  // Maximum Hamming distance: 4
  // Minimum Hamming weight: 1
  // Maximum Hamming weight: 5
  //
  localparam int StateWidth = 6;
  typedef enum logic [StateWidth-1:0] {
      StIdle = 6'b011111,

      // Active state is used in Unmasked version only.
      // It handles keccak round in a cycle
      StActive = 6'b000100,

      // Phase1 --> Phase2Cycle1 --> Phase2Cycle2 --> Phase2Cycle3
      // Activated only in Masked version.
      // Phase1 processes Theta, Rho, Pi steps in a cycle and stores the states
      // into storage. It only moves to Phase2 once the randomness required for
      // Phase2 is available.
      StPhase1 = 6'b101101,

      // Chi Stage 1 for first lane halves. Unconditionally move to Phase2Cycle2.
      StPhase2Cycle1 = 6'b000011,

      // Chi Stage 2 and Iota for first lane halves. Chi Stage 1 for second
      // lane halves. We only move forward if the fresh randomness required for
      // remasking is available. Otherwise, keep computing Phase2Cycle1.
      StPhase2Cycle2 = 6'b011000,

      // Chi Stage 2 and Iota for second lane halves.
      // This state doesn't require random value as it is XORed into the states
      // in Phase1 and Phase2Cycle2. When doing the last round (MaxRound -1)
      // it completes the process and goes back to Idle. If not, it repeats
      // the phases again.
      StPhase2Cycle3 = 6'b101010,

      // Error state. Not clearly defined yet.
      // Intention is if any unexpected input in the process, state moves to
      // here and report through the error fifo with debugging information.
      StError = 6'b110001,

      StTerminalError = 6'b110110
  } keccak_st_e;
  keccak_st_e keccak_st, keccak_st_d;
  `ABR_PRIM_FLOP_SPARSE_FSM(u_state_regs, keccak_st_d, keccak_st, keccak_st_e, StIdle)

  // Next state logic and output logic
  // SEC_CM: FSM.SPARSE
  always_comb begin
    // Default values
    keccak_st_d = keccak_st;

    xor_message          = 1'b 0;
    update_storage       = 1'b 0;
    rst_storage          = 1'b 0;
    rst_serial_buffer    = 1'b 0;

    inc_rnd_num = 1'b 0;
    rst_rnd_num = 1'b 0;

    keccak_rand_consumed = 1'b 0;

    phase_sel = MuBi4False;
    cycle = 2'h 0;

    complete_d = 1'b 0;

    sparse_fsm_error_o = 1'b 0;

    unique case (keccak_st)
      StIdle: begin
        if (abr_prim_mubi_pkg::mubi4_test_true_strict(clear_i)) begin
          // Opt1. State machine allows resetting the storage only in Idle
          // Opt2. storage resets regardless of states but clear_i
          // Both are added in the design at this time. Will choose the
          // direction later.
          keccak_st_d = StIdle;

          rst_storage = 1'b 1;
          rst_serial_buffer = 1'b 1;
        end else if (EnMasking && run_i) begin
          // Masked version of Keccak handling
          keccak_st_d = StPhase1;
          xor_message = ~squeezing_i;
          update_storage = ~squeezing_i;
        end else if (!EnMasking && run_i) begin
          // Unmasked version of Keccak handling
          keccak_st_d = StActive;
          xor_message = ~squeezing_i;
          update_storage = ~squeezing_i;
        end else begin
          keccak_st_d = StIdle;
        end
      end

      StActive: begin
        // Run Keccak single round logic until it reaches MaxRound - 1
        update_storage = 1'b 1;

        if (rnd_eq_end) begin
          keccak_st_d = StIdle;

          rst_rnd_num = 1'b 1;
          complete_d  = 1'b 1;
        end else begin
          keccak_st_d = StActive;

          inc_rnd_num = 1'b 1;
        end
      end

      StPhase1: begin
        // Theta, Rho and Pi
        phase_sel = MuBi4False;
        cycle =  2'h 0;

        // Only update state and move on once we know the randomness required
        // for Phase2 will be available in the next clock cycle. This way the
        // DOM multipliers inside keccak_2share will be presented the new
        // state (updated with update_storage) at the same time as the new
        // randomness (updated with rand_early_i). Otherwise, stale entropy is
        // paired with fresh data or vice versa. This could lead to undesired
        // SCA leakage.
        if (rand_early_i || rand_valid_i) begin
          keccak_st_d = StPhase2Cycle1;
          update_storage = 1'b 1;
        end else begin
          keccak_st_d = StPhase1;
        end
      end

      StPhase2Cycle1: begin
        // Chi Stage 1 for first lane halves.
        phase_sel = MuBi4True;
        cycle =  2'h 1;

        // Trigger randomness update for next cycle.
        keccak_rand_consumed = 1'b 1;

        // Unconditionally move to next phase/cycle.
        keccak_st_d = StPhase2Cycle2;
      end

      StPhase2Cycle2: begin
        // Chi Stage 1 for second lane halves.
        // Chi Stage 2 and Iota for first lane halves.
        phase_sel = MuBi4True;

        // Only update state and move on if the required randomness is
        // available. This way the DOM multipliers inside keccak_2share will be
        // presented the second lane halves at the same time as the new
        // randomness. Otherwise, stale entropy is paired with fresh data or
        // vice versa. This could lead to undesired SCA leakage.
        if (rand_valid_i) begin
          cycle =  2'h 2;

          // Trigger randomness update for next round.
          keccak_rand_consumed = 1'b 1;

          // Update first lane halves.
          update_storage = 1'b 1;

          keccak_st_d = StPhase2Cycle3;
        end else begin
          cycle =  2'h 1;
          keccak_st_d = StPhase2Cycle2;
        end
      end

      StPhase2Cycle3: begin
        // Chi Stage 2 and Iota for second lane halves.
        phase_sel = MuBi4True;
        cycle =  2'h 3;

        // Update second lane halves.
        update_storage = 1'b 1;

        if (rnd_eq_end) begin
          keccak_st_d = StIdle;

          rst_rnd_num    = 1'b 1;
          complete_d     = 1'b 1;
        end else begin
          keccak_st_d = StPhase1;

          inc_rnd_num = 1'b 1;
        end
      end

      StError: begin
        keccak_st_d = StError;
      end

      StTerminalError: begin
        //this state is terminal
        keccak_st_d = keccak_st;
        sparse_fsm_error_o = 1'b 1;
      end

      default: begin
        keccak_st_d = StTerminalError;
        sparse_fsm_error_o = 1'b 1;
      end
    endcase

    if (zeroize) keccak_st_d =StIdle;

  end

  // Ready indicates the keccak_round is able to receive new message.
  // While keccak_round is processing the data, it blocks the new message to be
  // XORed into the current state.
  assign ready_o = (keccak_st == StIdle) ? 1'b 1 : 1'b 0;

  ////////////////////////////
  // Keccak state registers //
  ////////////////////////////

  // SEC_CM: LOGIC.INTEGRITY
  logic rst_n;
  abr_prim_sec_anchor_buf #(
   .Width(1)
  ) u_abr_prim_sec_anchor_buf (
    .in_i(rst_b),
    .out_o(rst_n)
  );

  logic [Width-1:0] storage_datapath[RoundsPerClock:0][Share];
  logic [Width-1:0] storage   [Share];
  logic [Width-1:0] storage_d [Share];
  always_ff @(posedge clk_i or negedge rst_n) begin
    if (!rst_n) begin
      storage <= '{default:'0};
    end else if (zeroize) begin
      storage <= '{default:'0};
    end else if (rst_storage) begin
      storage <= '{default:'0};
    end else if (update_storage) begin
      storage <= storage_d;
    end
  end

  assign state_o = storage;

  // Storage register input
  // The incoming message is XORed with the existing storage registers.
  always_comb begin
    storage_d = storage_datapath[RoundsPerClock];
    if (xor_message) begin
      for (int j = 0 ; j < Share ; j++) begin
        storage_d[j] = storage[j] ^ data_i[j];
      end // for j
    end // if xor_message
  end

  // Check the rst_storage integrity
  logic rst_storage_error;

  always_comb begin : chk_rst_storage
    rst_storage_error = 1'b 0;

    if (rst_storage) begin
      // FSM should be in StIdle and clear_i should be high
      if ((keccak_st != StIdle) ||
        abr_prim_mubi_pkg::mubi4_test_false_loose(clear_i)) begin
        rst_storage_error = 1'b 1;
      end
    end
  end : chk_rst_storage

  assign rst_storage_error_o = rst_storage_error ;

  //////////////
  // Datapath //
  //////////////
  assign storage_datapath[0] = storage;

  generate
    for (genvar inst_g = 0; inst_g < RoundsPerClock; inst_g++) begin : round_gen
      abr_keccak_2share #(
        .Width     (Width),
        .EnMasking (EnMasking)
      ) u_keccak_p (
        .clk_i,
        .rst_b,

        .rnd_i           (RndW'(round+inst_g)),
        .phase_sel_i     (phase_sel),
        .cycle_i         (cycle),
        .rand_aux_i      (keccak_rand_aux),
        .rand_i          (keccak_rand_data),
        .s_i             (storage_datapath[inst_g]),
        .s_o             (storage_datapath[inst_g+1])
      );
    end
  endgenerate

  // keccak entropy handling
  assign rand_consumed_o = keccak_rand_consumed;

  assign keccak_rand_data = rand_data_i;
  assign keccak_rand_aux = rand_aux_i;

  // Round number
  // This primitive is used to place a hardened counter
  // SEC_CM: CTR.REDUN
  abr_prim_count #(
    .Width(RndW)
  ) u_round_count (
    .clk_i,
    .rst_b,
    .clr_i(rst_rnd_num | zeroize),
    .set_i(1'b0),
    .set_cnt_i('0),
    .incr_en_i(inc_rnd_num),
    .decr_en_i(1'b0),
    .step_i(RndW'(RoundsPerClock)),
    .cnt_o(round),
    .cnt_next_o(),
    .err_o(round_count_error_o)
  );

  // completion signal
  always_ff @(posedge clk_i or negedge rst_b) begin
    if (!rst_b) begin
      complete_o <= 1'b 0;
    end else if (zeroize) begin
      complete_o <= 1'b 0;
    end else begin
      complete_o <= complete_d;
    end
  end

  ////////////////
  // Assertions //
  ////////////////

  // Only allow RoundsPerClock of 1-4
  `ABR_ASSERT_INIT(RoundsPerClockLTE_4_A, (RoundsPerClock > 0) && (RoundsPerClock <= 4))

  // If `run_i` triggerred, it shall complete
  //`ABR_ASSERT(RunResultComplete_A, run_i ##[MaxRound:] complete_o, clk_i, !rst_b)

  // run_i only asserted in Idle state
  `ABR_ASSERT(ValidRunAssertStIdle_A, run_i |-> keccak_st == StIdle, clk_i, !rst_b)

  // clear_i is assumed to be asserted in Idle state
  `ABR_ASSERT(ClearAssertStIdle_A,
    abr_prim_mubi_pkg::mubi4_test_true_strict(clear_i)
     |-> keccak_st == StIdle, clk_i, !rst_b)

  // EnMasking controls the valid states
  if (EnMasking) begin : gen_mask_st_chk
    `ABR_ASSERT(EnMaskingValidStates_A, keccak_st != StActive, clk_i, !rst_b)
  end else begin : gen_unmask_st_chk
    `ABR_ASSERT(UnmaskValidStates_A, !(keccak_st
        inside {StPhase1, StPhase2Cycle1, StPhase2Cycle2, StPhase2Cycle3}),
        clk_i, !rst_b)
  end

endmodule
