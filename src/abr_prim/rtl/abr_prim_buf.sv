// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This file is auto-generated.
// Used parser: Verible

`ifndef ABR_PRIM_DEFAULT_IMPL
  `define ABR_PRIM_DEFAULT_IMPL abr_prim_pkg::ImplGeneric
`endif

// This is to prevent AscentLint warnings in the generated
// abstract prim wrapper. These warnings occur due to the .*
// use. TODO: we may want to move these inline waivers
// into a separate, generated waiver file for consistency.
//ri lint_check_off OUTPUT_NOT_DRIVEN INPUT_NOT_READ HIER_BRANCH_NOT_READ
module abr_prim_buf

#(
parameter int Width = 1
) (
  input        [Width-1:0] in_i,
  output logic [Width-1:0] out_o
);
  parameter abr_prim_pkg::impl_e Impl = `ABR_PRIM_DEFAULT_IMPL;

if (Impl == abr_prim_pkg::ImplXilinx) begin : gen_xilinx
    abr_prim_xilinx_buf #(
      .Width(Width)
    ) u_impl_xilinx (
      .*
    );
end else begin : gen_generic
    abr_prim_generic_buf #(
      .Width(Width)
    ) u_impl_generic (
      .*
    );
end

endmodule
//ri lint_check_on OUTPUT_NOT_DRIVEN INPUT_NOT_READ HIER_BRANCH_NOT_READ
