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

// -------------------------------------------------
// Copyright(c) LUBIS EDA GmbH, All rights reserved
// Contact: contact@lubis-eda.com
// -------------------------------------------------

`include "abr_prim_assert.sv"
`include "abr_prim_assert_standard_macros.svh"

package fv_sampler_top_pkg;
    import abr_sampler_pkg::*;
    import abr_sha3_pkg::*;
    import abr_params_pkg::*;
    import abr_prim_alert_pkg::*;

typedef enum logic unsigned [2:0] { fv_mldsa_sampler_idle_type, fv_mldsa_sampler_proc_type, fv_mldsa_sampler_wait_type, fv_mldsa_sampler_run_type, fv_mldsa_sampler_done_type } fvStates;

endpackage
