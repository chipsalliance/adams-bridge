// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// abr_sha3_pkg

package abr_sha3_pkg;

  // StateW represents the width of Keccak state variable.
  // As Sha3 assume the state value as 1600, this shouldn't be modified.
  // Note that keccak_round is flexible. It can have any values defined in SHA3
  // specification. But sha3pad logic assumes the value as 1600.
  parameter int StateW = 1600;

  // Datapath width in KMAC, this also affects the output of MSG_FIFO
  // This is assumed as 64 in KMAC design. If this value is changed, some parts
  // of the KMAC design need to be changed.
  //
  // 1. keccak_round logic datapath. Keccak round logic assumes MsgWidth
  //    divides 1600 keccak state `Width`. Choose the value accordingly.
  // 2. sha3pad module has fixed width mux for funcpad logic. If MsgWidth is
  //    changed, the logic also need to be revised.
  // 3. kmac core logic also has fixed size mux for appeding output length.
  //    Revise the case statement to fit into revised MsgWidth value.
  parameter int MsgWidth = 64;
  parameter int MsgStrbW = MsgWidth / 8;

  // Keccak module supports SHA3, SHAKE functions.
  // Mode chooses the padding value.
  //
  //    mode   |  little-endian
  //    -------|----------------
  //    Sha3   |  2'b   10
  //    Shake  |  4'b 1111
  //
  typedef enum logic[1:0] {
    Sha3   = 2'b 01,
    Shake  = 2'b 10
  } sha3_mode_e;

  // keccak_strength_e determines the security strength against collision attack
  // This value decides the _rate_ and _capacity_ of the keccak states.
  // It affects the sha3pad module too. the padding module implements
  typedef enum logic [2:0] {
    L128 = 3'b 000, // rate: 1344 bit / capacity:  256 bit Keccak[ 256](, 128)
    L224 = 3'b 001, // rate: 1152 bit / capacity:  448 bit Keccak[ 448](, 224)
    L256 = 3'b 010, // rate: 1088 bit / capacity:  512 bit Keccak[ 512](, 256)
    L384 = 3'b 011, // rate:  832 bit / capacity:  768 bit Keccak[ 768](, 384)
    L512 = 3'b 100  // rate:  576 bit / capacity: 1024 bit Keccak[1024](, 512)
  } keccak_strength_e;

  parameter int unsigned KeccakRate [5] = '{
    (1344+MsgWidth-1)/MsgWidth,  // 21 depth := (1600 - 128*2)
    (1152+MsgWidth-1)/MsgWidth,  // 18 depth := (1600 - 224*2)
    (1088+MsgWidth-1)/MsgWidth,  // 17 depth := (1600 - 256*2)
     (832+MsgWidth-1)/MsgWidth,  // 13 depth := (1600 - 384*2)
     (576+MsgWidth-1)/MsgWidth   //  9 depth := (1600 - 512*2)
  };

  parameter int unsigned MaxBlockSize = KeccakRate[0];

  parameter int unsigned MsgEntries = (StateW+MsgWidth-1)/MsgWidth;
  parameter int unsigned MsgAddrW = $clog2(MsgEntries);

  parameter int unsigned MsgCountW = $clog2(MsgEntries+1);

  // SHA3 core state. This state value is used in sha3core module
  // and also in KMAC top module and the register interface for sw to track the
  // sha3 status.
  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 3 -m 7 -n 6 \
  //      -s 4082450958 --language=sv
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
  // Maximum Hamming weight: 4
  //
  localparam int StateWidth = 6;
  typedef enum logic [StateWidth-1:0] {
    StIdle_sparse = 6'b101100,

    // Absorb stage receives the message bitstream and computes the keccak
    // rounds. This internal operation is mainly done inside sha3pad module
    // not sha3core. The core module and this state machine observe the status
    // of the process and mainly waits until all the sponge absorbing is
    // completed. The main indicator is `absorbed` signal.
    StAbsorb_sparse = 6'b100001,

    // Squeeze stage allows the software to read the internal state.
    // If `EnMasking`, it opens the read permission of two share of the state.
    // The squeezing in SHA3 specification describes the software to read up to
    // the rate of SHA3 algorithm but this logic opens up the entire 1600 bits
    // of the state (3200bits if `EnMasking`).
    StSqueeze_sparse = 6'b001011,

    // ManualRun stage initiaties the keccak round and waits the completion.
    // This state is moved from Squeeze state by writing 1 to manual_run CSR.
    // When keccak round is completed, it goes back to Squeeze state.
    StManualRun_sparse = 6'b010000,

    StTerminalError_sparse = 6'b111010
  } sha3_st_sparse_e;

  localparam int StateWidthLogic = 3;
  typedef enum logic [StateWidthLogic-1:0] {
    StIdle,
    StAbsorb,
    StSqueeze,
    StManualRun,
    StFlush,
    StError
  } sha3_st_e;

  function automatic sha3_st_e sparse2logic(sha3_st_sparse_e st);
    unique case (st)
      StIdle_sparse          : return StIdle;
      StAbsorb_sparse        : return StAbsorb;
      StSqueeze_sparse       : return StSqueeze;
      StManualRun_sparse     : return StManualRun;
      StTerminalError_sparse : return StError;
      default                : return StError;
    endcase
  endfunction : sparse2logic


  //////////////////////
  // Keccak Round FSM //
  //////////////////////

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
  localparam int KeccakFsmWidth = 6;
  typedef enum logic [KeccakFsmWidth-1:0] {
    KeccakStIdle = 6'b011111,

    // Active state is used in Unmasked version only.
    // It handles keccak round in a cycle
    KeccakStActive = 6'b000100,

    // Phase1 --> Phase2Cycle1 --> Phase2Cycle2 --> Phase2Cycle3
    // Activated only in Masked version.
    // Phase1 processes Theta, Rho, Pi steps in a cycle and stores the states
    // into storage. It only moves to Phase2 once the randomness required for
    // Phase2 is available.
    KeccakStPhase1 = 6'b101101,

    // Chi Stage 1 for first lane halves. Unconditionally move to Phase2Cycle2.
    KeccakStPhase2Cycle1 = 6'b000011,

    // Chi Stage 2 and Iota for first lane halves. Chi Stage 1 for second
    // lane halves. Unconditionally move to Phase2Cycle3.
    KeccakStPhase2Cycle2 = 6'b011000,

    // Chi Stage 2 and Iota for second lane halves.
    // When doing the last round (MaxRound -1) it completes the process and
    // goes back to Idle. If not, it repeats the phases again.
    KeccakStPhase2Cycle3 = 6'b101010,

    // Error state. Not clearly defined yet.
    // Intention is if any unexpected input in the process, state moves to
    // here and report through the error fifo with debugging information.
    KeccakStError = 6'b110001,

    KeccakStTerminalError = 6'b110110
  } keccak_st_e;

  //////////////////
  // Error Report //
  //////////////////
  typedef enum logic [7:0] {
    ErrNone = 8'h 00,

    // ErrSha3SwControl occurs when software sent wrong flow signal.
    // e.g) Sw set `process_i` without `start_i`. The state machine ignores
    //      the signal and report through the error FIFO.
    ErrSha3SwControl = 8'h 80
  } err_code_e;

  typedef struct packed {
    logic        valid;
    err_code_e   code; // Type of error
    logic [23:0] info; // Additional Debug info
  } err_t;

endpackage : abr_sha3_pkg
