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
// | Created on 20.01.2025 at 15:50                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


package decompose_verify_mode_pkg;


typedef enum logic unsigned [0:0] { RW_IDLE, RW_READ } e_mem_rw_mode;

typedef struct packed {
  logic unsigned [13:0] source;
  logic unsigned [13:0] destination;
  logic unsigned [13:0] hint_source;
} st_BaseAddress;

typedef struct packed {
  e_mem_rw_mode rd_wr_en;
  logic unsigned [13:0] addr;
} st_mem_if_t;

typedef logic [3:0] a_bool_4;

typedef logic unsigned [3:0][15:0] a_unsigned_16_4;

typedef logic unsigned [3:0][18:0] a_unsigned_19_4;

typedef logic unsigned [3:0][0:0] a_unsigned_1_4;

typedef logic unsigned [3:0][22:0] a_unsigned_23_4;

typedef logic unsigned [3:0][3:0] a_unsigned_4_4;


endpackage
