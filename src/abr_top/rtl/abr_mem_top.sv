// SPDX-License-Identifier: Apache-2.0
// Copyright 2019 Western Digital Corporation or its affiliates.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
`include "abr_config_defines.svh"
module abr_mem_top
  import abr_params_pkg::*;
  import abr_ctrl_pkg::*;
  #(
    parameter SRAM_LATENCY = 1,
    parameter bit MASKING_EN = 0
  )
(
  input logic clk_i,
  abr_mem_if.resp abr_memory_export
);

`ABR_MEM(ABR_MEM_W1_DEPTH,ABR_MEM_W1_DATA_W,w1_mem,SRAM_LATENCY)
`ABR_MEM(ABR_MEM_INST0_DEPTH,ABR_MEM_DATA_WIDTH,mem_inst0_bank0,SRAM_LATENCY)
`ABR_MEM(ABR_MEM_INST0_DEPTH,ABR_MEM_DATA_WIDTH,mem_inst0_bank1,SRAM_LATENCY)
`ABR_MEM(ABR_MEM_INST1_DEPTH,ABR_MEM_DATA_WIDTH,mem_inst1,SRAM_LATENCY)
`ABR_MEM(ABR_MEM_INST2_DEPTH,ABR_MEM_DATA_WIDTH,mem_inst2,SRAM_LATENCY)

// Masked memory instances — gated by MASKING_EN
// Inlined (not using ABR_MEM macro) to avoid nested generate/endgenerate
generate
if (MASKING_EN) begin : masked_mem_gen

  logic [ABR_MEM_DATA_WIDTH-1:0] mem_inst0_bank0_masked_rdata_o [SRAM_LATENCY:1];
  abr_1r1w_ram #(.DEPTH(ABR_MEM_INST0_DEPTH), .DATA_WIDTH(ABR_MEM_DATA_WIDTH))
    abr_mem_inst0_bank0_masked_inst (
      .clk_i(clk_i),
      .we_i(abr_memory_export.mem_inst0_bank0_masked_we_i),
      .waddr_i(abr_memory_export.mem_inst0_bank0_masked_waddr_i),
      .wdata_i(abr_memory_export.mem_inst0_bank0_masked_wdata_i),
      .re_i(abr_memory_export.mem_inst0_bank0_masked_re_i),
      .raddr_i(abr_memory_export.mem_inst0_bank0_masked_raddr_i),
      .rdata_o(mem_inst0_bank0_masked_rdata_o[1])
    );
  if (SRAM_LATENCY > 1) begin : mem_inst0_bank0_masked_lat
    for (genvar g_i = 2; g_i <= SRAM_LATENCY; g_i++) begin : stages
      always_ff @(posedge clk_i) mem_inst0_bank0_masked_rdata_o[g_i] <= mem_inst0_bank0_masked_rdata_o[g_i-1];
    end
  end
  assign abr_memory_export.mem_inst0_bank0_masked_rdata_o = mem_inst0_bank0_masked_rdata_o[SRAM_LATENCY];

  logic [ABR_MEM_DATA_WIDTH-1:0] mem_inst0_bank1_masked_rdata_o [SRAM_LATENCY:1];
  abr_1r1w_ram #(.DEPTH(ABR_MEM_INST0_DEPTH), .DATA_WIDTH(ABR_MEM_DATA_WIDTH))
    abr_mem_inst0_bank1_masked_inst (
      .clk_i(clk_i),
      .we_i(abr_memory_export.mem_inst0_bank1_masked_we_i),
      .waddr_i(abr_memory_export.mem_inst0_bank1_masked_waddr_i),
      .wdata_i(abr_memory_export.mem_inst0_bank1_masked_wdata_i),
      .re_i(abr_memory_export.mem_inst0_bank1_masked_re_i),
      .raddr_i(abr_memory_export.mem_inst0_bank1_masked_raddr_i),
      .rdata_o(mem_inst0_bank1_masked_rdata_o[1])
    );
  if (SRAM_LATENCY > 1) begin : mem_inst0_bank1_masked_lat
    for (genvar g_i = 2; g_i <= SRAM_LATENCY; g_i++) begin : stages
      always_ff @(posedge clk_i) mem_inst0_bank1_masked_rdata_o[g_i] <= mem_inst0_bank1_masked_rdata_o[g_i-1];
    end
  end
  assign abr_memory_export.mem_inst0_bank1_masked_rdata_o = mem_inst0_bank1_masked_rdata_o[SRAM_LATENCY];

  logic [ABR_MEM_DATA_WIDTH-1:0] mem_inst1_masked_rdata_o [SRAM_LATENCY:1];
  abr_1r1w_ram #(.DEPTH(ABR_MEM_INST1_DEPTH), .DATA_WIDTH(ABR_MEM_DATA_WIDTH))
    abr_mem_inst1_masked_inst (
      .clk_i(clk_i),
      .we_i(abr_memory_export.mem_inst1_masked_we_i),
      .waddr_i(abr_memory_export.mem_inst1_masked_waddr_i),
      .wdata_i(abr_memory_export.mem_inst1_masked_wdata_i),
      .re_i(abr_memory_export.mem_inst1_masked_re_i),
      .raddr_i(abr_memory_export.mem_inst1_masked_raddr_i),
      .rdata_o(mem_inst1_masked_rdata_o[1])
    );
  if (SRAM_LATENCY > 1) begin : mem_inst1_masked_lat
    for (genvar g_i = 2; g_i <= SRAM_LATENCY; g_i++) begin : stages
      always_ff @(posedge clk_i) mem_inst1_masked_rdata_o[g_i] <= mem_inst1_masked_rdata_o[g_i-1];
    end
  end
  assign abr_memory_export.mem_inst1_masked_rdata_o = mem_inst1_masked_rdata_o[SRAM_LATENCY];

  logic [ABR_MEM_DATA_WIDTH-1:0] mem_inst2_masked_rdata_o [SRAM_LATENCY:1];
  abr_1r1w_ram #(.DEPTH(ABR_MEM_INST2_DEPTH), .DATA_WIDTH(ABR_MEM_DATA_WIDTH))
    abr_mem_inst2_masked_inst (
      .clk_i(clk_i),
      .we_i(abr_memory_export.mem_inst2_masked_we_i),
      .waddr_i(abr_memory_export.mem_inst2_masked_waddr_i),
      .wdata_i(abr_memory_export.mem_inst2_masked_wdata_i),
      .re_i(abr_memory_export.mem_inst2_masked_re_i),
      .raddr_i(abr_memory_export.mem_inst2_masked_raddr_i),
      .rdata_o(mem_inst2_masked_rdata_o[1])
    );
  if (SRAM_LATENCY > 1) begin : mem_inst2_masked_lat
    for (genvar g_i = 2; g_i <= SRAM_LATENCY; g_i++) begin : stages
      always_ff @(posedge clk_i) mem_inst2_masked_rdata_o[g_i] <= mem_inst2_masked_rdata_o[g_i-1];
    end
  end
  assign abr_memory_export.mem_inst2_masked_rdata_o = mem_inst2_masked_rdata_o[SRAM_LATENCY];

end else begin : no_masked_mem_gen
  assign abr_memory_export.mem_inst0_bank0_masked_rdata_o = '0;
  assign abr_memory_export.mem_inst0_bank1_masked_rdata_o = '0;
  assign abr_memory_export.mem_inst1_masked_rdata_o = '0;
  assign abr_memory_export.mem_inst2_masked_rdata_o = '0;
end
endgenerate

`ABR_MEM(SK_MEM_BANK_DEPTH,SK_MEM_BANK_DATA_W,sk_mem_bank0,SRAM_LATENCY)
`ABR_MEM(SK_MEM_BANK_DEPTH,SK_MEM_BANK_DATA_W,sk_mem_bank1,SRAM_LATENCY)
`ABR_MEM_BE(SIG_Z_MEM_DEPTH,SIG_Z_MEM_DATA_W,sig_z_mem,SRAM_LATENCY)
`ABR_MEM_BE(PK_MEM_DEPTH,PK_MEM_DATA_W,pk_mem,SRAM_LATENCY)

endmodule