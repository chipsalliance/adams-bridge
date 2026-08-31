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
// | Created on 10.03.2025 at 09:40                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


package fv_sigdecode_h_states_pkg;


typedef enum logic unsigned [1:0] { ReadIdle, ReadInit, ReadHintSum, ReadExec } e_ReadStatesType;

typedef enum logic unsigned [1:0] { WriteIdle, WriteInit, WriteMem } e_WriteStatesType;

typedef struct packed {
  logic unsigned [13:0] address;
  logic idle;
  logic read;
  logic write;
} st_Request;

typedef logic unsigned [3:0][7:0] a_unsigned_8_4;

typedef logic unsigned [82:0][7:0] a_unsigned_8_83;


endpackage
