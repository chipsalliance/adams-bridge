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
// power2round_defines_pkg.sv
// --------
// power2round parameters for Mldsa
//======================================================================

`ifndef MLDSA_POWER2ROUND_DEFINES
`define MLDSA_POWER2ROUND_DEFINES

package power2round_defines_pkg;

    typedef enum logic [1:0] {T_RD_IDLE, T_RD_MEM, T_RD_DONE} power2round_read_state_type;
    typedef enum logic [1:0] {SK_WR_IDLE, SK_WR_WAIT, SK_WR_MEM, SK_WR_DONE} power2round_sk_write_state_type;
    typedef enum logic [1:0] {PK_WR_IDLE, PK_WR_API, PK_WR_DONE} power2round_pk_write_state_type;

endpackage

`endif