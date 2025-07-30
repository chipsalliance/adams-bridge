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
// decompress_defines_pkg.sv
// --------
// decompress parameters for mlkem
//======================================================================

`ifndef MLKEM_DECOMPRESS_DEFINES
`define MLKEM_DECOMPRESS_DEFINES

package decompress_defines_pkg;

    typedef enum logic {DCMP_RD_IDLE, DCMP_RD_MEM} decomp_read_state_e;
    typedef enum logic {DCMP_WR_IDLE, DCMP_WR_MEM} decomp_write_state_e;

    localparam DECOMPRESS1 = 'h0,
               DECOMPRESS5 = 'h1,
               DECOMPRESS11 = 'h2,
               DECOMPRESS12 = 'h3;

    typedef logic [1:0] decompress_mode_t;
endpackage

`endif