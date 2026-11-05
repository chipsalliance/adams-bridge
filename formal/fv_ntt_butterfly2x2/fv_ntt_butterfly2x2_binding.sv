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

import ntt_defines_pkg::*;

bind ntt_butterfly2x2 fv_ntt_butterfly2x2 fv_ntt_butterfly2x2_i (
  .pi_clk                    (ntt_butterfly2x2.clk),
  .pi_reset_n                (ntt_butterfly2x2.reset_n),
  .pi_zeroize                (ntt_butterfly2x2.zeroize),
  .pi_mode                   (ntt_butterfly2x2.mode),
  .pi_enable                 (ntt_butterfly2x2.enable),
  .pi_uvw_i                  (ntt_butterfly2x2.uvw_i),
  .pi_pw_uvw_i               (ntt_butterfly2x2.pw_uvw_i),
  .pi_accumulate             (ntt_butterfly2x2.accumulate),
  .pi_mlkem                  (ntt_butterfly2x2.mlkem),
  .pi_mlkem_pairwm_zeta13_i  (ntt_butterfly2x2.mlkem_pairwm_zeta13_i),
  .po_uv_o                   (ntt_butterfly2x2.uv_o),
  .po_pwo_uv_o               (ntt_butterfly2x2.pwo_uv_o),
  .po_ready_o                (ntt_butterfly2x2.ready_o)
);
