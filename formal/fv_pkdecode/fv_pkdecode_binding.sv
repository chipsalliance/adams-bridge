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

// +---------------------------------------------------+
// | Copyright (c) LUBIS EDA GmbH, all rights reserved |
// | Created on 07.01.2025 at 18:20                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import abr_params_pkg::*;
import fv_pkdecode_functions::*;


module fv_pkdecode_ref_wrapper_m;


st_Request write_request_port;
assign write_request_port = '{addresses: '{pkdecode.mem_a_wr_req.addr, pkdecode.mem_b_wr_req.addr}, idle: (pkdecode.mem_a_wr_req.rd_wr_en == RW_IDLE) && (pkdecode.mem_b_wr_req.rd_wr_en == RW_IDLE), read: (pkdecode.mem_a_wr_req.rd_wr_en == RW_READ) && (pkdecode.mem_b_wr_req.rd_wr_en == RW_READ), write: (pkdecode.mem_a_wr_req.rd_wr_en == RW_WRITE) && (pkdecode.mem_b_wr_req.rd_wr_en == RW_WRITE)};

st_BaseAddress base_address;
assign base_address = '{source: pkdecode.locked_src_addr, destination: pkdecode.locked_dest_addr};


fv_pkdecode_m fv_pkdecode(
  .rst(!pkdecode.reset_n || pkdecode.zeroize),
  .clk(pkdecode.clk),

  // Ports
  .base_address_port(fv_pkdecode_pkg::st_BaseAddress'({pkdecode.src_base_addr, pkdecode.dest_base_addr})),

  .read_data_port(pkdecode.API_rd_data),

  .start_port_vld(pkdecode.pkdecode_enable),
  .start_port_rdy(1'b1),
  .start_port(),

  .done_port(pkdecode.pkdecode_done),

  .read_address_port(pkdecode.API_rd_address),

  .write_data_port({pkdecode.mem_b_wr_data,pkdecode.mem_a_wr_data}),

  .write_request_port(write_request_port),

  // Registers
  .api_operands(pkdecode.num_api_operands),
  .base_address(base_address),
  .mem_operands(pkdecode.num_mem_operands),

  // States
  .DONE(pkdecode.state == pkdecode.DONE),
  .IDLE(pkdecode.state == pkdecode.IDLE),
  .READ(pkdecode.state == pkdecode.READ),
  .READ_EXEC(pkdecode.state == pkdecode.READ_and_EXEC),
  .READ_WRITE(pkdecode.state == pkdecode.READ_and_WRITE),
  .WRITE(pkdecode.state == pkdecode.WRITE)
);


endmodule


bind pkdecode fv_pkdecode_ref_wrapper_m fv_pkdecode_ref_wrapper();
