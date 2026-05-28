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
// | Created on 25.02.2025 at 12:37                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


package fv_sample_in_ball_ctrl_pkg;


typedef enum logic unsigned [1:0] { SIB_IDLE, SIB_SIGN_BUFFER, SIB_ACTIVE, SIB_DONE } e_states;

typedef logic [3:0] a_bool_4;

typedef logic unsigned [3:0][0:0] a_unsigned_1_4;

typedef logic unsigned [3:0][22:0] a_unsigned_23_4;

typedef logic unsigned [1:0][5:0] a_unsigned_6_2;

typedef logic unsigned [3:0][7:0] a_unsigned_8_4;


endpackage
