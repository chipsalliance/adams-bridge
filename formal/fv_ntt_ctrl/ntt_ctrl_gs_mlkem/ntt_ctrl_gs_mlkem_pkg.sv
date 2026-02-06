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
// | Created on 04.08.2025 at 17:50                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


package ntt_ctrl_gs_mlkem_pkg;


typedef enum logic unsigned [1:0] { GsReadIdle, GsReadStage, GsReadExec } e_GsReadStatesType;

typedef enum logic unsigned [2:0] { GsWriteIdle, GsWriteStage, GsWriteBuf, GsWriteMem, GsWriteWait } e_GsWriteStatesType;

typedef struct packed {
  logic unsigned [13:0] src_base_addr;
  logic unsigned [13:0] interim_base_addr;
  logic unsigned [13:0] dest_base_addr;
} st_NttBaseAddrs;

typedef logic unsigned [7:0][6:0] a_unsigned_7_8;


// Constants

parameter a_unsigned_7_8 twiddle_offsets = '{ 0: 7'd0, 1: 7'd64, 2: 7'd80, 3: 7'd84, 4: 7'd0, 5: 7'd0, 6: 7'd0, 7: 7'd0 };


endpackage
