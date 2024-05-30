// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "abr_prim_assert.sv"

module abr_prim_generic_flop_en #(
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

  logic en;
  if (EnSecBuf) begin : gen_en_sec_buf
    abr_prim_sec_anchor_buf #(
      .Width(1)
    ) u_en_buf (
      .in_i(en_i),
      .out_o(en)
    );
  end else begin : gen_en_no_sec_buf
    assign en = en_i;
  end

  always_ff @(posedge clk_i or negedge rst_b) begin
    if (!rst_b) begin
      q_o <= ResetValue;
    end else if (en) begin
      q_o <= d_i;
    end
  end

endmodule
