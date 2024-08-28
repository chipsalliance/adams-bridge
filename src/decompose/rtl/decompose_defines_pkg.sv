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
// decompose_defines_pkg.sv
// --------
// Decompose parameters for Mldsa
//======================================================================

`ifndef MLDSA_DECOMPOSE_DEFINES
`define MLDSA_DECOMPOSE_DEFINES

package decompose_defines_pkg;

    typedef enum logic {DCMP_RD_IDLE, DCMP_RD_MEM} dcmp_read_state_e;
    typedef enum logic {DCMP_WR_IDLE, DCMP_WR_MEM} dcmp_write_state_e;

    localparam sign_op = 'h0,
               verify_op = 'h1;

    typedef logic dcmp_mode_t;
endpackage

`endif