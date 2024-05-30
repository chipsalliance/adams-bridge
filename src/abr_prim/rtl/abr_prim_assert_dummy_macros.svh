// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Macro bodies included by abr_prim_assert.sv for tools that don't support assertions. See
// abr_prim_assert.sv for documentation for each of the macros.

`define ABR_ASSERT_I(__name, __prop)
`define ABR_ASSERT_INIT(__name, __prop)
`define ABR_ASSERT_INIT_NET(__name, __prop)
`define ABR_ASSERT_FINAL(__name, __prop)
`ifndef ABR_SVA
`define ABR_ASSERT(__name, __prop, __clk = `ABR_ASSERT_DEFAULT_CLK, __rst = `ABR_ASSERT_DEFAULT_RST)
`define ABR_ASSERT_NEVER(__name, __prop, __clk = `ABR_ASSERT_DEFAULT_CLK, __rst = `ABR_ASSERT_DEFAULT_RST)
`define ABR_ASSERT_KNOWN(__name, __sig, __clk = `ABR_ASSERT_DEFAULT_CLK, __rst = `ABR_ASSERT_DEFAULT_RST)
`endif
`define ABR_COVER(__name, __prop, __clk = `ABR_ASSERT_DEFAULT_CLK, __rst = `ABR_ASSERT_DEFAULT_RST)
`define ABR_ASSUME(__name, __prop, __clk = `ABR_ASSERT_DEFAULT_CLK, __rst = `ABR_ASSERT_DEFAULT_RST)
`define ABR_ASSUME_I(__name, __prop)
