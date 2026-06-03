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
// | Created on 18.02.2025 at 14:01                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


package fv_norm_check_top_pkg;


typedef struct packed {
  logic unsigned [13:0] address;
  logic unsigned [1:0] rd_wr_en;
} st_mem_if_it;

typedef logic unsigned [3:0][22:0] a_unsigned_22_4;

typedef logic unsigned [3:0][23:0] a_unsigned_24_4;


endpackage
