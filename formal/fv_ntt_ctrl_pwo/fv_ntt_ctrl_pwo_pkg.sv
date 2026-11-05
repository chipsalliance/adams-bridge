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


package fv_ntt_ctrl_pwo_pkg;


typedef enum logic unsigned [1:0] { fv_pwo_read_idle_type, fv_pwo_read_stage_type, fv_pwo_read_exec_type, fv_pwo_read_exec_wait_type } pwoReadStatesType;

typedef enum logic unsigned [1:0] { fv_pwo_write_idle_type, fv_pwo_write_stage_type, fv_pwo_write_wait_type, fv_pwo_write_mem_type } pwoWriteStatesType;

typedef struct packed {
  logic unsigned [14:0] pw_base_addr_a;
  logic unsigned [14:0] pw_base_addr_b;
  logic unsigned [14:0] pw_base_addr_c;
} fv_pwo_mem_addrs_type;

typedef logic unsigned [7:0][6:0] fv_unsigned_7_8_type;


endpackage
