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
// norm_check_defines_pkg.sv
// --------
// Validity norm check parameters for the digital signature algorithm (DSA).
//
//
//======================================================================

`ifndef ABR_NORM_CHECK_DEFINES
`define ABR_NORM_CHECK_DEFINES

package norm_check_defines_pkg;

    parameter z_bound = 2'h0, r0_bound = 2'h1, ct0_bound = 2'h2;
    typedef logic [1:0] chk_norm_mode_t;

    typedef enum logic [1:0] {CHK_IDLE, CHK_RD_MEM, CHK_WAIT, CHK_DONE} chk_read_state_e;
endpackage

`endif