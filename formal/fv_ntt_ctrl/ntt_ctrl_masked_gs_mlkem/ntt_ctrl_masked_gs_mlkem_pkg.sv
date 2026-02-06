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
// | Created on 04.08.2025 at 09:46                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


package ntt_ctrl_masked_gs_mlkem_pkg;


typedef enum logic unsigned [1:0] { MaskedGsReadIdle, MaskedGsReadStage, MaskedGsReadExec } e_MaskedGsReadStatesType;

typedef enum logic unsigned [2:0] { MaskedGsWriteIdle, MaskedGsWriteStage, MaskedGsWriteBuf, MaskedGsWriteMem, MaskedGsWriteWait } e_MaskedGsWriteStatesType;

typedef struct packed {
  logic unsigned [14:0] src_base_addr;
  logic unsigned [14:0] interim_base_addr;
  logic unsigned [14:0] dest_base_addr;
} st_NttMemBaseAddrs;

typedef logic unsigned [7:0][6:0] a_unsigned_7_8;


endpackage
