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
// | Created on 03.05.2025 at 11:33                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


package fv_power2round_top_pkg;


typedef struct packed {
  logic unsigned [13:0] source;
  logic unsigned [13:0] destination;
} st_BaseAddress;

typedef struct packed {
  logic unsigned [7:0] address;
  logic enable;
} st_PkRequest;

typedef logic unsigned [1:0][13:0] a_unsigned_14_2;

typedef struct packed {
  a_unsigned_14_2 addresses;
  logic idle;
  logic read;
  logic write;
} st_Request;

typedef logic unsigned [1:0][31:0] a_unsigned_32_2;

typedef struct packed {
  logic unsigned [167:0] the_buffer;
  a_unsigned_32_2 the_output;
} st_SampleBuffer;

typedef logic unsigned [7:0][9:0] a_unsigned_10_8;

typedef logic unsigned [7:0][12:0] a_unsigned_13_8;

typedef logic unsigned [7:0][23:0] a_unsigned_24_8;


endpackage
