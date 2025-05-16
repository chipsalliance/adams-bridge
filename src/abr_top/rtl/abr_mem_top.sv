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
(
  input logic clk_i,
  abr_mem_if.resp abr_memory_export
);

`ABR_MEM(ABR_MEM_W1_DEPTH,ABR_MEM_W1_DATA_W,w1_mem)
`ABR_MEM(ABR_MEM_INST0_DEPTH,ABR_MEM_DATA_WIDTH,mem_inst0_bank0)
`ABR_MEM(ABR_MEM_INST0_DEPTH,ABR_MEM_DATA_WIDTH,mem_inst0_bank1)
`ABR_MEM(ABR_MEM_INST1_DEPTH,ABR_MEM_DATA_WIDTH,mem_inst1)
`ABR_MEM(ABR_MEM_INST2_DEPTH,ABR_MEM_DATA_WIDTH,mem_inst2)
`ABR_MEM(ABR_MEM_INST3_DEPTH,ABR_MEM_MASKED_DATA_WIDTH,mem_inst3)
`ABR_MEM(SK_MEM_BANK_DEPTH,SK_MEM_BANK_DATA_W,sk_mem_bank0)
`ABR_MEM(SK_MEM_BANK_DEPTH,SK_MEM_BANK_DATA_W,sk_mem_bank1)
`ABR_MEM_BE(SIG_Z_MEM_DEPTH,SIG_Z_MEM_DATA_W,sig_z_mem)
`ABR_MEM_BE(PK_MEM_DEPTH,PK_MEM_DATA_W,pk_mem)

endmodule