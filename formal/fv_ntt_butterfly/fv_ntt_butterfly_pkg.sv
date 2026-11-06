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


package fv_ntt_butterfly_pkg;


typedef enum logic unsigned [2:0] { fv_ct_type, fv_gs_type, fv_pwm_type, fv_pwa_type, fv_pws_type, fv_pwm_intt_type } eNttMode;

localparam logic [22:0] MLDSA_Q          = 23'd8380417;
localparam logic [22:0] MLKEM_Q          = 23'd3329;
localparam logic [22:0] MLDSA_Q_DIV2_ODD = 23'd4190209; // (8380417+1)/2
localparam logic [22:0] MLKEM_Q_DIV2_ODD = 23'd1665;    // (3329+1)/2


endpackage
