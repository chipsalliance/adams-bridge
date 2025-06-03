// SPDX-License-Identifier: Apache-2.0
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
`ifndef ABR_CFG_SV
`define ABR_CFG_SV

   `include "abr_sva.svh"
   // `define RV_FPGA_OPTIMIZE
   // `define RV_FPGA_SCA
   `define MLDSA_MASKING

  `define ABR_ICG           abr_clk_gate

  `define ABR_MEM(_depth, _width, _mem_name) \
  abr_1r1w_ram \
  #( .DEPTH(``_depth``), \
     .DATA_WIDTH(``_width``)) \
   mldsa_``_mem_name``_inst\
   (\
      .clk_i(clk_i),\
      .we_i(abr_memory_export.``_mem_name``_we_i),\
      .waddr_i(abr_memory_export.``_mem_name``_waddr_i),\
      .wdata_i(abr_memory_export.``_mem_name``_wdata_i),\
      .re_i(abr_memory_export.``_mem_name``_re_i),\
      .raddr_i(abr_memory_export.``_mem_name``_raddr_i),\
      .rdata_o(abr_memory_export.``_mem_name``_rdata_o)\
   );

  `define ABR_MEM_BE(_depth, _width, _mem_name) \
  abr_1r1w_be_ram \
  #( .DEPTH(``_depth``), \
     .DATA_WIDTH(``_width``))  \
     mldsa_``_mem_name``_inst\
     (\
        .clk_i(clk_i),\
        .we_i(abr_memory_export.``_mem_name``_we_i),\
        .waddr_i(abr_memory_export.``_mem_name``_waddr_i),\
        .wdata_i(abr_memory_export.``_mem_name``_wdata_i),\
        .wstrobe_i(abr_memory_export.``_mem_name``_wstrobe_i),\
        .re_i(abr_memory_export.``_mem_name``_re_i),\
        .raddr_i(abr_memory_export.``_mem_name``_raddr_i),\
        .rdata_o(abr_memory_export.``_mem_name``_rdata_o)\
     );
  
`endif
