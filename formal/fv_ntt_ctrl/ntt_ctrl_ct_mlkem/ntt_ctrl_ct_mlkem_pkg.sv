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
// | Created on 05.08.2025 at 16:36                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


package ntt_ctrl_ct_mlkem_pkg;


typedef enum logic unsigned [2:0] { CtReadIdle, CtReadStage, CtReadBuf, CtReadExec, CtReadExecwait } e_CtReadStatesType;

typedef enum logic unsigned [1:0] { CtWriteIdle, CtWriteStage, CtWriteMem } e_CtWriteStatesType;

typedef struct packed {
  logic unsigned [13:0] source;
  logic unsigned [13:0] interim;
  logic unsigned [13:0] destination;
} st_Base_Address;

typedef struct packed {
  logic request;
  logic unsigned [14:0] address;
} st_Request_and_Address;


endpackage
