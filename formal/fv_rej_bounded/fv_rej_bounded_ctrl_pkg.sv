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
// | Created on 19.12.2024 at 18:34                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


package fv_rej_bounded_ctrl_pkg;


typedef enum logic unsigned [1:0] { RBC_RD, RBC_RW, RBC_WR } e_states;

typedef logic unsigned [3:0][23:0] a_unsigned_24_4;

typedef logic unsigned [3:0][2:0] a_unsigned_3_4;

typedef logic unsigned [7:0][2:0] a_unsigned_3_8;

typedef logic unsigned [7:0][3:0] a_unsigned_4_8;


endpackage
