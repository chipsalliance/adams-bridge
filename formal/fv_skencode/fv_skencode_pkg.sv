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
// | Created on 05.04.2025 at 12:39                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


package fv_skencode_pkg;


typedef enum logic unsigned [1:0] { RW_IDLE, RW_READ, RW_WRITE } e_mem_rw_mode;

typedef struct packed {
  logic unsigned [14:0] source;
  logic unsigned [14:0] destination;
} st_BaseAddress;

typedef struct packed {
  e_mem_rw_mode rd_wr_en;
  logic unsigned [13:0] addr;
} st_mem_if_t;

typedef logic unsigned [7:0][23:0] a_unsigned_24_8;


endpackage
