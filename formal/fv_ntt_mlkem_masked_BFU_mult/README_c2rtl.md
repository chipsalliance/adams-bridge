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

# masked_barrett_reduction c2rtl
Date: 22-09-2025
Author: LUBIS EDA


## tcl file description
The tcl file (prove_c2rtl.tcl) can be found in the following directory **<project_root>/formal/fv_ntt_mlkem_masked_BFU_mult/**
The tcl file contains in line assumptions and assertions as follows:


## Constraints overview

- **of_u:** assume the shared input u (u0 + u1) is less than MLKEM_Q

- **of_v:** assume the shared input v (v0 + v1) is less than MLKEM_Q

- **no_zero:** assume zeroize signal is not asserted for simplicity purpose


## Assertion IP Overview

The in-line assertions are divided for each operation of the module starting from the input until reaching the primary outputs. 

- **spec_mul:** Checks the result of multiplication against spec

- **spec_reduce:** Checks the result of the reduction against spec

- **imp_reduce:** Checks the result of the reduction using implementation signals

- **mbr_check_t:** Checks if t is tmp/2^24 inside the inside the masked_barret_reduction.

- **mbr_check_x_reg:** Checks if x_reg latches the primary inputs inside the inside the masked_barret_reduction.

- **mbr_check_qt:** Checks if qt is correctly computed after t has been computed in the previous CC inside the inside the masked_barret_reduction.

- **mbr_check_c:** Checks if c is the result of x - qt inside the inside the masked_barret_reduction.

- **mbr_check_c_reg_CC3:** Checks if the intermediate value of c is propagated across CC inside the inside the masked_barret_reduction.

- **mbr_check_c_reg_CC5:** Checks if the intermediate value of c is propagated across CC inside the inside the masked_barret_reduction.

- **mbr_check_c_rolled0:** Checks for the value of c to determine possible correction of y inside the inside the masked_barret_reduction.

- **mbr_check_c_rolled1:** Checks for the value of c to determine possible correction of y inside the inside the masked_barret_reduction.

- **mbr_check_y:** Checks for the result y, based on the intermediate computations of c inside the inside the masked_barret_reduction, taking correction of modulo into account.

- **mbr_e2e_check_y:** Checks the computation of y from end-to-end inside the inside the masked_barret_reduction.


## Reproduce results

The AIP has been tested with Jasper C2RTL and results are hold bounded.

To reproduce the results, load the tcl script in Jasper Gold.

Feel free to reach out to contact@lubis-eda.com to request the loadscripts.
