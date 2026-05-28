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
// | Created on 29.03.2025 at 21:28                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


package fv_skdecode_top_pkg;


typedef enum logic unsigned [1:0] { fv_RW_IDLE, fv_RW_READ, fv_RW_WRITE } e_mem_rw_mode;

typedef struct packed {
  logic unsigned [13:0] source;
  logic unsigned [13:0] destination;
} st_BaseAddress;

typedef struct packed {
  e_mem_rw_mode rd_wr_en;
  logic unsigned [13:0] addr;
} st_mem_if_t;

typedef logic unsigned [3:0][12:0] a_unsigned_13_4;

typedef logic unsigned [3:0][23:0] a_unsigned_24_4;

typedef logic unsigned [7:0][2:0] a_unsigned_3_8;


endpackage
