// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// // Macros and helper code for security countermeasures.

`ifndef ABR_PRIM_ASSERT_SEC_CM_SVH
`define ABR_PRIM_ASSERT_SEC_CM_SVH

`define _ABR_SEC_CM_ALERT_MAX_CYC 30

// Helper macros
`define ABR_ASSERT_ERROR_TRIGGER_ALERT(NAME_, PRIM_HIER_, ALERT_, GATE_, MAX_CYCLES_, ERR_NAME_) \
  `ABR_ASSERT(FpvSecCm``NAME_``, \
          $rose(PRIM_HIER_.ERR_NAME_) && !(GATE_) \
          |-> ##[0:MAX_CYCLES_] (ALERT_.alert_p)) \
  `ifdef ABR_INC_ASSERT \
  assign PRIM_HIER_.unused_assert_connected = 1'b1; \
  `endif \
  `ABR_ASSUME_FPV(``NAME_``TriggerAfterAlertInit_S, $stable(rst_b) == 0 |-> \
                       PRIM_HIER_.ERR_NAME_ == 0 [*10])

`define ABR_ASSERT_ERROR_TRIGGER_ERR(NAME_, PRIM_HIER_, ERR_, GATE_, MAX_CYCLES_, ERR_NAME_, CLK_, RST_) \
  `ABR_ASSERT(FpvSecCm``NAME_``, \
          $rose(PRIM_HIER_.ERR_NAME_) && !(GATE_) \
          |-> ##[0:MAX_CYCLES_] (ERR_), CLK_, RST_) \
  `ifdef ABR_INC_ASSERT \
  assign PRIM_HIER_.unused_assert_connected = 1'b1; \
  `endif

// macros for security countermeasures that will trigger alert
`define ABR_ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(NAME_, PRIM_HIER_, ALERT_, GATE_ = 0, MAX_CYCLES_ = `_ABR_SEC_CM_ALERT_MAX_CYC) \
  `ABR_ASSERT_ERROR_TRIGGER_ALERT(NAME_, PRIM_HIER_, ALERT_, GATE_, MAX_CYCLES_, err_o)

`define ABR_ASSERT_PRIM_DOUBLE_LFSR_ERROR_TRIGGER_ALERT(NAME_, PRIM_HIER_, ALERT_, GATE_ = 0, MAX_CYCLES_ = `_ABR_SEC_CM_ALERT_MAX_CYC) \
  `ABR_ASSERT_ERROR_TRIGGER_ALERT(NAME_, PRIM_HIER_, ALERT_, GATE_, MAX_CYCLES_, err_o)

`define ABR_ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(NAME_, PRIM_HIER_, ALERT_, GATE_ = 0, MAX_CYCLES_ = `_ABR_SEC_CM_ALERT_MAX_CYC) \
  `ABR_ASSERT_ERROR_TRIGGER_ALERT(NAME_, PRIM_HIER_, ALERT_, GATE_, MAX_CYCLES_, unused_err_o)

`define ABR_ASSERT_PRIM_ONEHOT_ERROR_TRIGGER_ALERT(NAME_, PRIM_HIER_, ALERT_, GATE_ = 0, MAX_CYCLES_ = `_ABR_SEC_CM_ALERT_MAX_CYC) \
  `ABR_ASSERT_ERROR_TRIGGER_ALERT(NAME_, PRIM_HIER_, ALERT_, GATE_, MAX_CYCLES_, err_o)

`define ABR_ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(NAME_, REG_TOP_HIER_, ALERT_, GATE_ = 0, MAX_CYCLES_ = `_ABR_SEC_CM_ALERT_MAX_CYC) \
  `ABR_ASSERT_PRIM_ONEHOT_ERROR_TRIGGER_ALERT(NAME_, \
    REG_TOP_HIER_.u_abr_prim_reg_we_check.u_abr_prim_onehot_check, ALERT_, GATE_, MAX_CYCLES_)

`endif // PRIM_ASSERT_SEC_CM_SVH
