// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Abstract prim wrapper for an enabled flop. Selects between the generic
// implementation (default) and a technology-specific one. The generic module
// name is resolved through the abr_prim module-name macro so it can be swapped
// via ABR_PRIM_MODULE_PREFIX without editing this wrapper.

`include "abr_prim_module_name_macros.svh"

`ifndef ABR_PRIM_DEFAULT_IMPL
  `define ABR_PRIM_DEFAULT_IMPL abr_prim_pkg::ImplGeneric
`endif

module abr_prim_flop_en

#(

  parameter int               Width      = 1,
  parameter bit               EnSecBuf   = 0,
  parameter logic [Width-1:0] ResetValue = 0

) (
  input                    clk_i,
  input                    rst_b,
  input                    en_i,
  input        [Width-1:0] d_i,
  output logic [Width-1:0] q_o
);
  parameter abr_prim_pkg::impl_e Impl = `ABR_PRIM_DEFAULT_IMPL;

if (Impl == abr_prim_pkg::ImplXilinx) begin : gen_xilinx
    abr_prim_xilinx_flop_en #(
      .EnSecBuf(EnSecBuf),
      .ResetValue(ResetValue),
      .Width(Width)
    ) u_impl_xilinx (
      .clk_i  (clk_i),
      .rst_ni (rst_b),
      .en_i   (en_i),
      .d_i    (d_i),
      .q_o    (q_o)
    );
end else begin : gen_generic
    `ABR_PRIM_MODULE_NAME(flop_en) #(
      .EnSecBuf(EnSecBuf),
      .ResetValue(ResetValue),
      .Width(Width)
    ) u_impl_generic (
      .clk_i  (clk_i),
      .rst_ni (rst_b),
      .en_i   (en_i),
      .d_i    (d_i),
      .q_o    (q_o)
    );
end

endmodule
