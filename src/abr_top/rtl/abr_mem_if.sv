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
// Description:
//      Signals for SRAM interfaces needed for mldsa
//

import abr_params_pkg::*;
import abr_ctrl_pkg::*;

`define ABR_MEM_IF_SIGNALS(_PARAM_PREFIX, _signal_prefix)\
logic ``_signal_prefix``_we_i;\
logic [``_PARAM_PREFIX``_ADDR_W-1:0] ``_signal_prefix``_waddr_i;\
logic [``_PARAM_PREFIX``_DATA_W-1:0] ``_signal_prefix``_wdata_i;\
logic ``_signal_prefix``_re_i;\
logic [``_PARAM_PREFIX``_ADDR_W-1:0] ``_signal_prefix``_raddr_i;\
logic [``_PARAM_PREFIX``_DATA_W-1:0] ``_signal_prefix``_rdata_o;

`define ABR_MEM_BE_IF_SIGNALS(_PARAM_PREFIX, _signal_prefix)\
logic ``_signal_prefix``_we_i;\
logic [``_PARAM_PREFIX``_ADDR_W-1:0] ``_signal_prefix``_waddr_i;\
logic [``_PARAM_PREFIX``_DATA_W-1:0] ``_signal_prefix``_wdata_i;\
logic [``_PARAM_PREFIX``_WSTROBE_W-1:0] ``_signal_prefix``_wstrobe_i;\
logic ``_signal_prefix``_re_i;\
logic [``_PARAM_PREFIX``_ADDR_W-1:0] ``_signal_prefix``_raddr_i;\
logic [``_PARAM_PREFIX``_DATA_W-1:0] ``_signal_prefix``_rdata_o;

`define ABR_MEM_IF_REQ_PORTS(_signal_prefix)\
  output ``_signal_prefix``_we_i, ``_signal_prefix``_waddr_i, ``_signal_prefix``_wdata_i, ``_signal_prefix``_re_i, ``_signal_prefix``_raddr_i,\
  input ``_signal_prefix``_rdata_o

`define ABR_MEM_BE_IF_REQ_PORTS(_signal_prefix)\
  output ``_signal_prefix``_we_i, ``_signal_prefix``_waddr_i, ``_signal_prefix``_wdata_i, ``_signal_prefix``_wstrobe_i, ``_signal_prefix``_re_i, ``_signal_prefix``_raddr_i,\
  input ``_signal_prefix``_rdata_o

`define ABR_MEM_IF_RESP_PORTS(_signal_prefix)\
  input ``_signal_prefix``_we_i, ``_signal_prefix``_waddr_i, ``_signal_prefix``_wdata_i, ``_signal_prefix``_re_i, ``_signal_prefix``_raddr_i,\
  output ``_signal_prefix``_rdata_o

`define ABR_MEM_BE_IF_RESP_PORTS(_signal_prefix)\
  input ``_signal_prefix``_we_i, ``_signal_prefix``_waddr_i, ``_signal_prefix``_wdata_i, ``_signal_prefix``_wstrobe_i, ``_signal_prefix``_re_i, ``_signal_prefix``_raddr_i,\
  output ``_signal_prefix``_rdata_o

interface abr_mem_if;

  `ABR_MEM_IF_SIGNALS(ABR_MEM_W1, w1_mem)
  `ABR_MEM_IF_SIGNALS(ABR_MEM_INST0, mem_inst0_bank0)
  `ABR_MEM_IF_SIGNALS(ABR_MEM_INST0, mem_inst0_bank1)
  `ABR_MEM_IF_SIGNALS(ABR_MEM_INST1, mem_inst1)
  `ABR_MEM_IF_SIGNALS(ABR_MEM_INST2, mem_inst2)
  `ABR_MEM_IF_SIGNALS(ABR_MEM_INST3, mem_inst3)
  `ABR_MEM_IF_SIGNALS(SK_MEM_BANK, sk_mem_bank0)
  `ABR_MEM_IF_SIGNALS(SK_MEM_BANK, sk_mem_bank1)
  `ABR_MEM_BE_IF_SIGNALS(SIG_Z_MEM, sig_z_mem)
  `ABR_MEM_BE_IF_SIGNALS(PK_MEM, pk_mem)

  modport req (
    `ABR_MEM_IF_REQ_PORTS(w1_mem),
    `ABR_MEM_IF_REQ_PORTS(mem_inst0_bank0),
    `ABR_MEM_IF_REQ_PORTS(mem_inst0_bank1),
    `ABR_MEM_IF_REQ_PORTS(mem_inst1),
    `ABR_MEM_IF_REQ_PORTS(mem_inst2),
    `ABR_MEM_IF_REQ_PORTS(mem_inst3),
    `ABR_MEM_IF_REQ_PORTS(sk_mem_bank0),
    `ABR_MEM_IF_REQ_PORTS(sk_mem_bank1),
    `ABR_MEM_BE_IF_REQ_PORTS(sig_z_mem),
    `ABR_MEM_BE_IF_REQ_PORTS(pk_mem)
  );

  modport resp (
    `ABR_MEM_IF_RESP_PORTS(w1_mem),
    `ABR_MEM_IF_RESP_PORTS(mem_inst0_bank0),
    `ABR_MEM_IF_RESP_PORTS(mem_inst0_bank1),
    `ABR_MEM_IF_RESP_PORTS(mem_inst1),
    `ABR_MEM_IF_RESP_PORTS(mem_inst2),
    `ABR_MEM_IF_RESP_PORTS(mem_inst3),
    `ABR_MEM_IF_RESP_PORTS(sk_mem_bank0),
    `ABR_MEM_IF_RESP_PORTS(sk_mem_bank1),
    `ABR_MEM_BE_IF_RESP_PORTS(sig_z_mem),
    `ABR_MEM_BE_IF_RESP_PORTS(pk_mem)
  );

endinterface

interface abr_sram_if #(parameter integer ADDR_W = 16, parameter integer DATA_W = 32);

logic we_i;
logic [ADDR_W-1:0] waddr_i;
logic [DATA_W-1:0] wdata_i;
logic re_i;
logic [ADDR_W-1:0] raddr_i;
logic [DATA_W-1:0] rdata_o;

  modport req (
      output we_i, waddr_i, wdata_i, re_i, raddr_i,
      input rdata_o
  );

  modport resp (
      input we_i, waddr_i, wdata_i, re_i, raddr_i,
      output rdata_o
  );

endinterface

interface abr_sram_be_if #(parameter integer ADDR_W = 16, parameter integer DATA_W = 32);

  logic we_i;
  logic [ADDR_W-1:0] waddr_i;
  logic [DATA_W-1:0] wdata_i;
  logic [DATA_W/8-1:0] wstrobe_i;
  logic re_i;
  logic [ADDR_W-1:0] raddr_i;
  logic [DATA_W-1:0] rdata_o;
  
    modport req (
        output we_i, waddr_i, wdata_i, wstrobe_i, re_i, raddr_i,
        input rdata_o
    );
  
    modport resp (
        input we_i, waddr_i, wdata_i, wstrobe_i, re_i, raddr_i,
        output rdata_o
    );
  
  endinterface