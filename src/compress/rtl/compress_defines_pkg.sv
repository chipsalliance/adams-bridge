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
// compress_defines_pkg.sv
// --------
// compress parameters for mlkem
//======================================================================

`ifndef MLKEM_COMPRESS_DEFINES
`define MLKEM_COMPRESS_DEFINES

package compress_defines_pkg;

    typedef enum logic {CMP_RD_IDLE, CMP_RD_MEM} cmp_read_state_e;
    typedef enum logic {CMP_WR_IDLE, CMP_WR_MEM} cmp_write_state_e;

    localparam compress1 = 'h0,
               compress5 = 'h1,
               compress11 = 'h2,
               compress12 = 'h3;

    typedef logic [1:0] compress_mode_t;
endpackage

`endif