// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This file is auto-generated.
// Used parser: Fallback (regex)

`include "abr_prim_module_name_macros.svh"

`ifndef ABR_PRIM_DEFAULT_IMPL
  `define ABR_PRIM_DEFAULT_IMPL abr_prim_pkg::ImplGeneric
`endif

module abr_prim_flop

#(

  parameter int               Width      = 1,
  parameter logic [Width-1:0] ResetValue = 0

) (
  input                    clk_i,
  input                    rst_b,
  input        [Width-1:0] d_i,
  output logic [Width-1:0] q_o
);
  parameter abr_prim_pkg::impl_e Impl = `ABR_PRIM_DEFAULT_IMPL;

if (Impl == abr_prim_pkg::ImplXilinx) begin : gen_xilinx
    abr_prim_xilinx_flop #(
      .ResetValue(ResetValue),
      .Width(Width)
    ) u_impl_xilinx (
      .clk_i  (clk_i),
      .rst_ni (rst_b),
      .d_i    (d_i),
      .q_o    (q_o)
    );
end else begin : gen_generic
    `ABR_PRIM_MODULE_NAME(flop) #(
      .ResetValue(ResetValue),
      .Width(Width)
    ) u_impl_generic (
      .clk_i  (clk_i),
      .rst_ni (rst_b),
      .d_i    (d_i),
      .q_o    (q_o)
    );
end

endmodule
