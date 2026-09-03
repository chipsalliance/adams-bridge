// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Abstract prim wrapper for a 2-input XOR. Selects between the generic
// implementation (default) and a technology-specific one. The generic module
// name is resolved through the abr_prim module-name macro so it can be swapped
// via ABR_PRIM_MODULE_PREFIX without editing this wrapper.

`include "abr_prim_module_name_macros.svh"

`ifndef ABR_PRIM_DEFAULT_IMPL
  `define ABR_PRIM_DEFAULT_IMPL abr_prim_pkg::ImplGeneric
`endif

// This is to prevent AscentLint warnings in the abstract prim wrapper. These
// warnings occur due to the .* use.
//ri lint_check_off OUTPUT_NOT_DRIVEN INPUT_NOT_READ HIER_BRANCH_NOT_READ
module abr_prim_xor2

#(
parameter int Width = 1
) (
  input        [Width-1:0] in0_i,
  input        [Width-1:0] in1_i,
  output logic [Width-1:0] out_o
);
  parameter abr_prim_pkg::impl_e Impl = `ABR_PRIM_DEFAULT_IMPL;

if (Impl == abr_prim_pkg::ImplXilinx) begin : gen_xilinx
    abr_prim_xilinx_xor2 #(
      .Width(Width)
    ) u_impl_xilinx (
      .*
    );
end else begin : gen_generic
    `ABR_PRIM_MODULE_NAME(xor2) #(
      .Width(Width)
    ) u_impl_generic (
      .*
    );
end

endmodule
//ri lint_check_on OUTPUT_NOT_DRIVEN INPUT_NOT_READ HIER_BRANCH_NOT_READ
