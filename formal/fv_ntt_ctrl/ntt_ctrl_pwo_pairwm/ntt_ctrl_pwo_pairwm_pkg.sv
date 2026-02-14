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
// | Created on 22.08.2025 at 11:32                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


package ntt_ctrl_pwo_pairwm_pkg;


typedef enum logic unsigned [1:0] { PwoReadIdle, PwoReadStage, PwoReadExec, PwoReadExecWait } e_PwoReadStatesType;

typedef enum logic unsigned [1:0] { PwoWriteIdle, PwoWriteStage, PwoWriteWait, PwoWriteMem } e_PwoWriteStatesType;

typedef struct packed {
  logic unsigned [14:0] pw_base_addr_a;
  logic unsigned [14:0] pw_base_addr_b;
  logic unsigned [14:0] pw_base_addr_c;
} st_PwoMemAddrs;

typedef logic unsigned [7:0][6:0] a_unsigned_7_8;


endpackage
