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
// | Created on 14.02.2025 at 11:54                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


package fv_makehint_pkg;


typedef enum logic unsigned [0:0] { RW_IDLE, RW_READ } e_mem_rw_mode_e_makehint;

typedef struct packed {
  logic unsigned [13:0] mem_base_addr;
  logic unsigned [13:0] dest_base_addr;
} st_BaseAddress_makehint;

typedef struct packed {
  e_mem_rw_mode_e_makehint rd_wr_en;
  logic unsigned [13:0] addr;
} st_mem_if_t_makehint;

typedef logic unsigned [3:0][0:0] a_unsigned_1_4;

typedef logic unsigned [3:0][7:0] a_unsigned_8_4;

typedef logic unsigned [7:0][7:0] a_unsigned_8_8;


endpackage
