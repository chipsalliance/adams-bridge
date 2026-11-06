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
// | Contact: contact@lubis-eda.com                    |
// +---------------------------------------------------+


package fv_skdecode_top_pkg;

import abr_params_pkg::*;

typedef enum logic unsigned [1:0] { fv_rw_idle_type, fv_rw_read_type, fv_rw_write_type } fvMemRwModeType;

typedef struct packed {
  logic unsigned [13:0] source;
  logic unsigned [13:0] destination;
} fv_base_address_type;

typedef struct packed {
  fvMemRwModeType rd_wr_en;
  logic unsigned [13:0] addr;
} fv_mem_if_type;

typedef logic unsigned [3:0][12:0] fv_unsigned_13_4_type;

typedef logic unsigned [3:0][23:0] fv_unsigned_24_4_type;

typedef logic unsigned [1:0][ABR_MEM_DATA_WIDTH-1:0] fv_unsigned_96_2_type;

typedef logic unsigned [7:0][2:0] fv_unsigned_3_8_type;


endpackage
