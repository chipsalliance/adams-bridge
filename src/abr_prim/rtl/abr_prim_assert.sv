// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Macros and helper code for using assertions.
//  - Provides default clk and rst options to simplify code
//  - Provides boiler plate template for common assertions

`ifndef ABR_PRIM_ASSERT_SV
`define ABR_PRIM_ASSERT_SV

///////////////////
// Helper macros //
///////////////////

`include "abr_sva.svh"
`ifndef ABR_SVA
// Default clk and reset signals used by assertion macros below.
`define ABR_ASSERT_DEFAULT_CLK clk_i
`define ABR_ASSERT_DEFAULT_RST !rst_b
`endif

// Converts an arbitrary block of code into a Verilog string
`define ABR_PRIM_STRINGIFY(__x) `"__x`"

// ABR_ASSERT_ERROR logs an error message with either `uvm_error or with $error.
//
// This somewhat duplicates `DV_ERROR macro defined in hw/dv/sv/dv_utils/dv_macros.svh. The reason
// for redefining it here is to avoid creating a dependency.
`define ABR_ASSERT_ERROR(__name)                                                             \
`ifdef UVM                                                                                        \
  uvm_pkg::uvm_report_error("ABR_ASSERT FAILED", `ABR_PRIM_STRINGIFY(__name), uvm_pkg::UVM_NONE, \
                            `__FILE__, `__LINE__);                                                \
`else                                                                                             \
  $error("%0t: (%0s:%0d) [%m] [ABR_ASSERT FAILED] %0s", $time, `__FILE__, `__LINE__,         \
         `ABR_PRIM_STRINGIFY(__name));                                                                \
`endif

// This macro is suitable for conditionally triggering lint errors, e.g., if a Sec parameter takes
// on a non-default value. This may be required for pre-silicon/FPGA evaluation but we don't want
// to allow this for tapeout.
`define ABR_ASSERT_STATIC_LINT_ERROR(__name, __prop)     \
  localparam int __name = (__prop) ? 1 : 2;                   \
  always_comb begin                                           \
    logic unused_assert_static_lint_error;                    \
    unused_assert_static_lint_error = __name'(1'b1);          \
  end

// Static assertions for checks inside SV packages. If the conditions is not true, this will
// trigger an error during elaboration.
`define ABR_ASSERT_STATIC_IN_PACKAGE(__name, __prop)              \
  function automatic logic assert_static_in_package_``__name();        \
    logic unused_bit [((__prop) ? 1 : -1)];                            \
    unused_bit = '{default: 1'b0};                                     \
    return unused_bit[0];                                              \
  endfunction

// The basic helper macros are actually defined in "implementation headers". The macros should do
// the same thing in each case (except for the dummy flavour), but in a way that the respective
// tools support.
//
// If the tool supports assertions in some form, we also define ABR_INC_ASSERT (which can be 
// used to hide signal definitions that are only used for assertions).
//
// The list of basic macros supported is:
//
//  ABR_ASSERT_I:     Immediate assertion. Note that immediate assertions are sensitive to simulation
//                         glitches.
//
//  ABR_ASSERT_INIT:  Assertion in initial block. Can be used for things like parameter checking.
//
//  ABR_ASSERT_INIT_NET: Assertion in initial block. Can be used for initial value of a net.
//
//  ABR_ASSERT_FINAL: Assertion in final block. Can be used for things like queues being empty at end of
//                         sim, all credits returned at end of sim, state machines in idle at end of sim.
//
//  ABR_ASSERT:       Assert a concurrent property directly. It can be called as a module (or
//                         interface) body item.
//
//                         Note: We use (__rst !== '0) in the disable iff statements instead of (__rst ==
//                         '1). This properly disables the assertion in cases when reset is X at the
//                         beginning of a simulation. For that case, (reset == '1) does not disable the
//                         assertion.
//
//  ABR_ASSERT_NEVER: Assert a concurrent property NEVER happens
//
//  ABR_ASSERT_KNOWN: Assert that signal has a known value (each bit is either '0' or '1') after reset.
//                         It can be called as a module (or interface) body item.
//
//  ABR_COVER:        Cover a concurrent property
//
//  ABR_ASSUME:       Assume a concurrent property
//
//  ABR_ASSUME_I:     Assume an immediate property

`ifdef VERILATOR
 `include "abr_prim_assert_dummy_macros.svh"
`elsif SYNTHESIS
 `include "abr_prim_assert_dummy_macros.svh"
`elsif YOSYS
 `include "abr_prim_assert_yosys_macros.svh"
 `define ABR_INC_ASSERT
`else
 `include "abr_prim_assert_standard_macros.svh"
 `define ABR_INC_ASSERT
`endif

//////////////////////////////
// Complex assertion macros //
//////////////////////////////

// Assert that signal is an active-high pulse with pulse length of 1 clock cycle
`define ABR_ASSERT_PULSE(__name, __sig, __clk = `ABR_ASSERT_DEFAULT_CLK, __rst = `ABR_ASSERT_DEFAULT_RST) \
  `ABR_ASSERT(__name, $rose(__sig) |=> !(__sig), __clk, __rst)

// Assert that a property is true only when an enable signal is set.  It can be called as a module
// (or interface) body item.
`define ABR_ASSERT_IF(__name, __prop, __enable, __clk = `ABR_ASSERT_DEFAULT_CLK, __rst = `ABR_ASSERT_DEFAULT_RST) \
  `ABR_ASSERT(__name, (__enable) |-> (__prop), __clk, __rst)

// Assert that signal has a known value (each bit is either '0' or '1') after reset if enable is
// set.  It can be called as a module (or interface) body item.
`define ABR_ASSERT_KNOWN_IF(__name, __sig, __enable, __clk = `ABR_ASSERT_DEFAULT_CLK, __rst = `ABR_ASSERT_DEFAULT_RST) \
  `ABR_ASSERT_KNOWN(__name``KnownEnable, __enable, __clk, __rst)                                               \
  `ABR_ASSERT_IF(__name, !$isunknown(__sig), __enable, __clk, __rst)

//////////////////////////////////
// For formal verification only //
//////////////////////////////////

// Note that the existing set of ABR_ASSERT macros specified above shall be used for FPV,
// thereby ensuring that the assertions are evaluated during DV simulations as well.

// ABR_ASSUME_FPV
// Assume a concurrent property during formal verification only.
`define ABR_ASSUME_FPV(__name, __prop, __clk = `ABR_ASSERT_DEFAULT_CLK, __rst = `ABR_ASSERT_DEFAULT_RST) \
`ifdef FPV_ON                                                                                \
   `ABR_ASSUME(__name, __prop, __clk, __rst)                                                     \
`endif

// ABR_ASSUME_I_FPV
// Assume a concurrent property during formal verification only.
`define ABR_ASSUME_I_FPV(__name, __prop) \
`ifdef FPV_ON                        \
   `ABR_ASSUME_I(__name, __prop)         \
`endif

// ABR_COVER_FPV
// Cover a concurrent property during formal verification
`define ABR_COVER_FPV(__name, __prop, __clk = `ABR_ASSERT_DEFAULT_CLK, __rst = `ABR_ASSERT_DEFAULT_RST) \
`ifdef FPV_ON                                                                               \
   `ABR_COVER(__name, __prop, __clk, __rst)                                                     \
`endif

// FPV assertion that proves that the FSM control flow is linear (no loops)
// The sequence triggers whenever the state changes and stores the current state as "initial_state".
// Then thereafter we must never see that state again until reset.
// It is possible for the reset to release ahead of the clock.
// Create a small "gray" window beyond the usual rst time to avoid
// checking.
`define ABR_ASSERT_FPV_LINEAR_FSM(__name, __state, __type, __clk = `ABR_ASSERT_DEFAULT_CLK, __rst = `ABR_ASSERT_DEFAULT_RST) \
  `ifdef ABR_INC_ASSERT                                                                                              \
     bit __name``_cond;                                                                                          \
     always_ff @(posedge __clk or posedge __rst) begin                                                           \
       if (__rst) begin                                                                                          \
         __name``_cond <= 0;                                                                                     \
       end else begin                                                                                            \
         __name``_cond <= 1;                                                                                     \
       end                                                                                                       \
     end                                                                                                         \
     property __name``_p;                                                                                        \
       __type initial_state;                                                                                     \
       (!$stable(__state) & __name``_cond, initial_state = $past(__state)) |->                                   \
           (__state != initial_state) until (__rst == 1'b1);                                                     \
     endproperty                                                                                                 \
   `ABR_ASSERT(__name, __name``_p, __clk, __rst)                                                                     \
  `endif

`include "abr_prim_assert_sec_cm.svh"
`include "abr_prim_flop_macros.sv"

`endif // PRIM_ASSERT_SV
