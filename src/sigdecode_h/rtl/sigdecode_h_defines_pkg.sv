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
// sigdecode_h_defines_pkg.sv
// --------
// sigdecode_h parameters for Mldsa
//======================================================================

`ifndef MLDSA_SIGDECODE_H_DEFINES
`define MLDSA_SIGDECODE_H_DEFINES

package sigdecode_h_defines_pkg;

    typedef enum logic [1:0] {SDH_RD_IDLE, SDH_RD_HINTSUM, SDH_RD_INIT, SDH_RD_EXEC} sdh_read_state_e;
    typedef enum logic [1:0] {SDH_WR_IDLE, SDH_WR_INIT, SDH_WR_MEM} sdh_write_state_e;

endpackage

`endif