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
//======================================================================
//
// sigencode_z_defines_pkg.sv
// --------
// sigencode_z parameters for Mldsa
//======================================================================

`ifndef MLDSA_SIGENCODE_Z_DEFINES
`define MLDSA_SIGENCODE_Z_DEFINES

package sigencode_z_defines_pkg;
    import abr_params_pkg::*;

    parameter API_ADDR_WIDTH = ABR_MEM_ADDR_WIDTH;
    parameter MLDSA_L = 7;

    typedef struct packed {
        mem_rw_mode_e rd_wr_en;
        logic [API_ADDR_WIDTH-1:0] addr;
    } sig_mem_if_t;

endpackage

`endif