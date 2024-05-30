// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Generic double-synchronizer flop
// This may need to be moved to abr_prim_generic if libraries have a specific cell
// for synchronization

module abr_prim_flop_2sync #(
  parameter int               Width      = 16,
  parameter logic [Width-1:0] ResetValue = '0,
  parameter bit               EnablePrimCdcRand = 1
) (
  input                    clk_i,
  input                    rst_b,
  input        [Width-1:0] d_i,
  output logic [Width-1:0] q_o
);

  logic [Width-1:0] d_o;
  logic [Width-1:0] intq;

`ifdef ABR_SIMULATION

  abr_prim_cdc_rand_delay #(
    .DataWidth(Width),
    .Enable(EnablePrimCdcRand)
  ) u_abr_prim_cdc_rand_delay (
    .clk_i,
    .rst_b,
    .src_data_i(d_i),
    .prev_data_i(intq),
    .dst_data_o(d_o)
  );
`else // !`ifdef ABR_SIMULATION
  logic unused_sig;
  assign unused_sig = EnablePrimCdcRand;
  always_comb d_o = d_i;
`endif // !`ifdef ABR_SIMULATION

  abr_prim_flop #(
    .Width(Width),
    .ResetValue(ResetValue)
  ) u_sync_1 (
    .clk_i,
    .rst_b,
    .d_i(d_o),
    .q_o(intq)
  );

  abr_prim_flop #(
    .Width(Width),
    .ResetValue(ResetValue)
  ) u_sync_2 (
    .clk_i,
    .rst_b,
    .d_i(intq),
    .q_o
  );

endmodule : abr_prim_flop_2sync
