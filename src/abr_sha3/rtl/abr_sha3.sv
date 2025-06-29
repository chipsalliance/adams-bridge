// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// SHA3 core is a fully functional SHA3/SHAKE/cSHAKE hashing module.
//
// It instantiates a keccak_round with 1600 bits of the state.

`include "abr_sva.svh"
`include "abr_prim_assert.sv"

module abr_sha3
  import abr_sha3_pkg::*;
#(
  // Number of Keccak Rounds performed each clock cycle
  parameter int RoundsPerClock = 1,
  // Enable Masked Keccak if 1
  parameter  bit EnMasking = 0,
  // derived parameter
  localparam int Share = (EnMasking) ? 2 : 1
) (
  input logic clk_i,
  input logic rst_b,
  input logic zeroize,
  // MSG interface
  input logic                      msg_start_i,
  input logic                      msg_valid_i,
  input logic       [MsgWidth-1:0] msg_data_i [Share],
  input logic       [MsgStrbW-1:0] msg_strb_i,         // one strobe for shares
  output logic                     msg_ready_o,

  // Entropy interface
  input logic                    rand_valid_i,
  input logic                    rand_early_i,
  input logic     [StateW/2-1:0] rand_data_i,
  input logic                    rand_aux_i,
  output logic                   rand_consumed_o,

  // N, S: Used in cSHAKE mode only
  input logic [NSRegisterSize*8-1:0] ns_data_i, // See abr_sha3_pkg for details

  // configurations
  input sha3_mode_e       mode_i,     // see abr_sha3pad for details
  input keccak_strength_e strength_i, // see abr_sha3pad for details

  // controls
  input logic start_i,   // see abr_sha3pad for details
  input logic process_i, // see abr_sha3pad for details

  // run_i is a pulse signal to trigger the keccak_round manually by SW.
  // It is used to run additional keccak_f after sponge absorbing is completed.
  // See `keccak_run` signal
  input logic                       run_i,

  output abr_prim_mubi_pkg::mubi4_t absorbed_o,
  output logic                      squeezing_o,

  // Indicate of one block processed. KMAC main state tracks the progression
  // based on this signal.
  output logic block_processed_o,

  output sha3_st_e sha3_fsm_o,

  // digest output
  // This value is valid only after all absorbing process is completed.
  // In invalid state, the output `state` will be zero to prevent information
  // leakage.
  output logic              state_valid_o,
  input  logic              state_valid_hold_i,
  output logic [StateW-1:0] state_o [Share],

  // error_o value is pushed to Error FIFO at KMAC/SHA3 top and reported to SW
  output err_t error_o,

  // sparse_fsm_alert
  output logic sparse_fsm_error_o,

  // counter error
  output logic count_error_o,

  // error on rst_storage in Keccak
  output logic keccak_storage_rst_error_o

);
  /////////////////
  // Definitions //
  /////////////////

  typedef enum logic[2:0] {
    MuxGuard   = 3'b 010,
    MuxRelease = 3'b 101
  } state_mux_sel_e;

  /////////////
  // Signals //
  /////////////

  // State --> Digest
  // State is exposed to the outside if the hashing process is completed.
  logic              state_valid;
  logic [StateW-1:0] state [Share];
  logic [StateW-1:0] state_guarded [Share];

  // State --> digest mux select signal
  state_mux_sel_e mux_sel;

  // absorbed is a pulse signal that indicates sponge absorbing is done.
  // After this, sha3 core allows software to manually run until squeezing
  // is completed
  abr_prim_mubi_pkg::mubi4_t absorbed;

  // `squeezing` is a status indicator that SHA3 core is in sponge squeezing
  // stage. In this stage, the state output is valid, and software can manually
  // trigger keccak_round logic to get more digest outputs in case the output
  // length is bigger than the block limit.
  logic squeezing;

  // If process_i is received, the logic initiates the final absorbing process.
  // While absorbing, the processing inticator is turned on. This signal is used
  // to check if multiple process_i is received or not.
  logic processing;

  // FSM variable
  sha3_st_sparse_e st, st_d;

  // Keccak control signal (filtered by State Machine)
  logic keccak_start, keccak_process;
  abr_prim_mubi_pkg::mubi4_t keccak_done;

  // alert signals
  logic round_count_error, msg_count_error;
  assign count_error_o =  round_count_error | msg_count_error;

  logic sha3_state_error;
  logic keccak_round_state_error;
  logic sha3pad_state_error;

  assign sparse_fsm_error_o = sha3_state_error | keccak_round_state_error | sha3pad_state_error;

  // Keccak rst_storage is asserted unexpectedly
  logic keccak_storage_rst_error;
  assign keccak_storage_rst_error_o = keccak_storage_rst_error;

  /////////////////
  // Connections //
  /////////////////

  logic [abr_sha3_pkg::StateW-1:0] keccak_data [Share];
  logic             keccak_ready;

  // Keccak round run signal can be controlled by sha3pad and also by software
  // after all message feeding is done. it is mainly used for sponge squeezing
  // operation after absorbing is completed when output length is longer than
  // the block size.
  logic keccak_run, sha3pad_keccak_run, sw_keccak_run;
  logic keccak_complete;

  assign keccak_run = sha3pad_keccak_run | sw_keccak_run;

  // Absorb pulse output : used to generate interrupts
  // Latch absorbed signal as kmac_keymgr asserts `CmdDone` when it sees
  // `absorbed` signal. When this signal goes out, the state is still in
  // `StAbsorb`. Next state is `StSqueeze`.
  always_ff @(posedge clk_i or negedge rst_b) begin
    if (!rst_b) absorbed_o <= abr_prim_mubi_pkg::MuBi4False;
    else if (zeroize) absorbed_o <= abr_prim_mubi_pkg::MuBi4False;
    else              absorbed_o <= absorbed;
  end

  // Squeezing output
  assign squeezing_o = squeezing;

  // processing
  always_ff @(posedge clk_i or negedge rst_b) begin
    if (!rst_b)         processing <= 1'b 0;
    else if (zeroize)   processing <= 1'b 0;
    else if (process_i) processing <= 1'b 1;
    else if (abr_prim_mubi_pkg::mubi4_test_true_strict(absorbed)) begin
      processing <= 1'b 0;
    end
  end

  always_ff  @(posedge clk_i or negedge rst_b) begin
    if      (!rst_b)                                                state_valid <= 1'b0; //reset
    else if (zeroize)                                               state_valid <= 1'b0; //zeroize
    else if ((st_d == StSqueeze_sparse) & (st != StSqueeze_sparse)) state_valid <= 1'b1; //assert on transition to squeeze
    else if (state_valid_hold_i)                                    state_valid <= state_valid; //hold current value
    else                                                            state_valid <= 1'b0; //de-assert
  end

  assign block_processed_o = keccak_complete;

  // State connection
  assign state_valid_o = state_valid;
  assign state_o = state_guarded;

  assign sha3_fsm_o = sparse2logic(st);



  ///////////////////
  // State Machine //
  ///////////////////

  // State Register
  `ABR_PRIM_FLOP_SPARSE_FSM(u_state_regs, st_d, st, sha3_st_sparse_e, StIdle_sparse)


  // Next State and Output Logic
  // Mainly the FSM controls the input signal access
  // StIdle:    only start_i signal is allowed
  // StAbsorb:  only process_i signal is allowed
  // StSqueeze: only run_i is allowed

  always_comb begin
    st_d = st;

    // default output values
    keccak_start = 1'b 0;
    keccak_process = 1'b 0;
    sw_keccak_run = 1'b 0;
    keccak_done = abr_prim_mubi_pkg::MuBi4False;

    squeezing = 1'b 0;

    sha3_state_error = 1'b 0;

    unique case (st)
      StIdle_sparse: begin
        if (start_i) begin
          st_d = StAbsorb_sparse;

          keccak_start = 1'b 1;
        end else begin
          st_d = StIdle_sparse;
        end
      end

      StAbsorb_sparse: begin
        if (process_i && !processing) begin
          st_d = StAbsorb_sparse;

          keccak_process = 1'b 1;
        end else if (abr_prim_mubi_pkg::mubi4_test_true_strict(absorbed)) begin
          st_d = StSqueeze_sparse;
        end else begin
          st_d = StAbsorb_sparse;
        end
      end

      StSqueeze_sparse: begin

        squeezing = 1'b 1;

        if (run_i) begin
          st_d = StManualRun_sparse;

          sw_keccak_run = 1'b 1;
        end else begin
          st_d = StSqueeze_sparse;
        end
      end

      StManualRun_sparse: begin
        squeezing = 1'b 1;
        if (keccak_complete) begin
          st_d = StSqueeze_sparse;
        end else begin
          st_d = StManualRun_sparse;
        end
      end

      StTerminalError_sparse: begin
        //this state is terminal
        st_d = StTerminalError_sparse;
        sha3_state_error = 1'b 1;
      end

      default: begin
        st_d = StTerminalError_sparse;
        sha3_state_error = 1'b 1;
      end
    endcase

    if (zeroize) st_d = StIdle_sparse;

  end

  //////////////
  // Datapath //
  //////////////

  // State --> Digest output
  always_comb begin
    if (state_valid) mux_sel = MuxRelease; // Expose state to register interfac
    else mux_sel = MuxGuard ;
  end

  always_comb begin : state_guarded_mux
    unique case (mux_sel)
      MuxGuard:   state_guarded = '{default: '0};
      MuxRelease: state_guarded = state;
      default:    state_guarded = '{default: '0}; // a valid, safe output
    endcase
  end


  // Error Detecting
  // ErrSha3SwControl:
  //   info[ 0]: start_i set
  //   info[ 1]: process_i set
  //   info[ 2]: run_i set
  //  - Sw set process_i, run_i, without start_i

  always_comb begin
    error_o = '{valid: 1'b0, code: ErrNone, info: '0};

    unique case (st)
      StIdle_sparse: begin
        if (process_i || run_i) begin
          error_o = '{
            valid: 1'b 1,
            code: ErrSha3SwControl,
            info: 24'({run_i, process_i, start_i})
          };
        end
      end

      StAbsorb_sparse: begin
        if (start_i || run_i || (process_i && processing)) begin
          error_o = '{
            valid: 1'b 1,
            code: ErrSha3SwControl,
            info: 24'({run_i, process_i, start_i})
          };
        end
      end

      StSqueeze_sparse: begin
        if (start_i || process_i) begin
          error_o = '{
            valid: 1'b 1,
            code: ErrSha3SwControl,
            info: 24'({run_i, process_i, start_i})
          };
        end
      end

      StManualRun_sparse: begin
        if (start_i || process_i || run_i) begin
          error_o = '{
            valid: 1'b 1,
            code: ErrSha3SwControl,
            info: 24'({run_i, process_i, start_i})
          };
        end
      end

      default: begin
      end
    endcase
  end
  ///////////////
  // Instances //
  ///////////////

  // SHA3 pad logic
  abr_sha3pad #(
    .EnMasking (EnMasking)
  ) u_pad (
    .clk_i,
    .rst_b,
    .zeroize,

    // MSG_FIFO (or from KMAC core)
    .msg_valid_i,
    .msg_data_i, // [Share]
    .msg_strb_i,
    .msg_ready_o,

    // Encoded N, S
    .ns_data_i,

    // output to keccak_round: message path
    .keccak_data_o  (keccak_data ), // [Share]
    .keccak_ready_i (keccak_ready & ~squeezing),

    .keccak_run_o      (sha3pad_keccak_run),
    .keccak_complete_i (keccak_complete   ),

    // configurations
    .mode_i,
    .strength_i,

    // controls
    .start_i   (msg_start_i),
    .process_i (keccak_process),

    // output
    .absorbed_o         (absorbed),
    .sparse_fsm_error_o (sha3pad_state_error),
    .msg_count_error_o  (msg_count_error)
  );

  // Keccak round logic
  abr_keccak_round #(
    .Width         (abr_sha3_pkg::StateW),
    .RoundsPerClock(RoundsPerClock),
    .EnMasking     (EnMasking)
  ) u_keccak (
    .clk_i,
    .rst_b,
    .zeroize,
    
    .data_i  (keccak_data ),
    .ready_o (keccak_ready),

    .rand_valid_i,
    .rand_early_i,
    .rand_data_i,
    .rand_aux_i,
    .rand_consumed_o,

    .run_i      (keccak_run     ),
    .squeezing_i(squeezing      ),
    .complete_o (keccak_complete),

    .state_o    (state),

    .sparse_fsm_error_o  (keccak_round_state_error),
    .round_count_error_o (round_count_error),
    .rst_storage_error_o (keccak_storage_rst_error),

    .clear_i    (keccak_done)
  );

  ////////////////
  // Assertions //
  ////////////////

  // Unknown check for case statement
  `ABR_ASSERT(MuxSelKnown_A, mux_sel inside {MuxGuard, MuxRelease})
  `ABR_ASSERT(FsmKnown_A, st inside {StIdle_sparse, StAbsorb_sparse, StSqueeze_sparse,
                                     StManualRun_sparse, StTerminalError_sparse})

  // `state` shall be 0 in invalid
  if (EnMasking) begin: gen_chk_digest_masked
    `ABR_ASSERT(StateZeroInvalid_A, !state_valid_o |-> ((|state_o[0]) | (|state_o[1])) == 1'b 0)
  end else begin : gen_chk_digest_unmasked
    `ABR_ASSERT(StateZeroInvalid_A, !state_valid_o |-> (|state_o[0]) == 1'b 0)
  end

  // `state_valid_o` asserts only in between the completion and done
  //`ABR_ASSERT(StateValidPeriod_A, state_valid_o |-> )

  // skip the msg interface assertions as they are in abr_sha3pad.sv

  // Software run signal happens in Squeezing stage
  `ABR_ASSERT(SwRunInSqueezing_a, run_i |-> error_o.valid || (st == StSqueeze_sparse))

  // If control received but not propagated into submodules, it is error condition
  `ABR_ASSERT(ErrDetection_A, error_o.valid
    |-> {start_i,      process_i,      run_i}
     != {keccak_start, keccak_process, sw_keccak_run})

endmodule
