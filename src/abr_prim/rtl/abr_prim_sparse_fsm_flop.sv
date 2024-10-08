// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "abr_prim_assert.sv"

module abr_prim_sparse_fsm_flop
  import abr_prim_sparse_fsm_pkg::*;
#(
  parameter int               Width      = 1,
  parameter type              StateEnumT = state_t,
  parameter logic [Width-1:0] ResetValue = '0,
  // This should only be disabled in special circumstances, for example
  // in non-comportable IPs where an error does not trigger an alert.
  parameter bit               EnableAlertTriggerSVA = 1
`ifdef ABR_SIMULATION
  ,
  // In case this parameter is set to a non-empty string, the
  // abr_prim_sparse_fsm_flop_if will also force the signal with this name
  // in the parent module that instantiates abr_prim_sparse_fsm_flop.
  parameter string            CustomForceName = ""
`endif
) (
  input             clk_i,
  input             rst_b,
  input  StateEnumT state_i,
  output StateEnumT state_o
);

  logic unused_err_o;

  logic [Width-1:0] state_raw;
  abr_prim_flop #(
    .Width(Width),
    .ResetValue(ResetValue)
  ) u_state_flop (
    .clk_i,
    .rst_b,
    .d_i(state_i),
    .q_o(state_raw)
  );
  assign state_o = StateEnumT'(state_raw);

  `ifdef ABR_INC_ASSERT
  assign unused_err_o = is_undefined_state(state_o);

  function automatic logic is_undefined_state(StateEnumT sig);
    // This is written with a vector in order to make it amenable to x-prop analysis.
    logic is_defined = 1'b0;
    for (int i = 0, StateEnumT t = t.first(); i < t.num(); i += 1, t = t.next()) begin
      is_defined |= (sig === t);
    end
    return ~is_defined;
  endfunction

  `else
    assign unused_err_o = 1'b0;
  `endif

  // If ABR_ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT is declared, the unused_assert_connected signal will
  // be set to 1 and the below check will pass.
  // If the assertion is not declared however, the statement below will fail.
  `ifdef ABR_INC_ASSERT
  logic unused_assert_connected;

  `ABR_ASSERT_INIT_NET(AssertConnected_A, unused_assert_connected === 1'b1 || !EnableAlertTriggerSVA)
  `endif

endmodule
