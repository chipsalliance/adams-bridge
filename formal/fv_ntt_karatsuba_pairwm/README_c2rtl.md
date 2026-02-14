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

# ntt_karatsuba_pairwm c2rtl
Date: 22.09.2025
Author: LUBIS EDA

## Cpp model description

The cpp model file can be found in the following directory: **<project_root>/formal/fv_ntt_karatsuba_pairwm/fv_ntt_karatsuba_pairwm.cpp**. This file contains the primary inputs and outputs of the design (treated as a skeleton file).


## TCL file description

The tcl file (prove_c2rtl.tcl) can be found in the following directory **<project_root>/formal/fv_ntt_karatsuba_pairwm/**. The tcl file contains in line assumptions and assertions, as well as the proof structure as follows: 

## Constraints overview

- assume_stable_accumulate: Assume the accumulate signal is stable throughout the verification window

- assume_u_range: Assume the u0 and u1 primary inputs are in range of the prime Q

- assume_v_range: Assume the v0 and v1 primary inputs are in range of the prime Q

- assume_w_range: Assume the w0 and w1 primary inputs are in range of the prime Q

- assume_zeta_range: Assume the zeta primary input is in range of the prime Q

- assume_no_zeroize: Assume zeroize signal is not asserted for simplicity purpose


## Assertion IP Overview

The in-line assertions are divided for each operation of the module starting from the input until reaching the primary outputs. 

- assert_uv00: Assertion to check uv00_reduced register, which is (u0*v0)%Q

- assert_uv11: Assertion to check uv11_reduced register, which is (u1*v1)%Q

- assert_u0_plus_u1: Assertion to check add_res_u register, which is the addition of of u0+u1

- assert_v0_plus_v1: Assertion to check add_res_v register, which is the addition of v0+v1

<br><br>


- assert_uv12: Assertion to check mul_res_uv12_reduced register, which is (add_res_u*add_res_v)%Q


<br><br>


- assert_uv12_sub_uv00: Assertion to check sub_res0 register, which is (uv12-uv00)%Q



<br><br>


- assert_uv1_o_no_accumulate: Assertion to check the primary output pwo_uv_o.uv1_o in case of no accumulate, which is (sub_res0-uv11)%Q


<br><br>


- assert_uvz11: Assertion to check uvz11_reduced register, which is (zeta*uv11)%Q

<br><br>


- assert_uv0_o_no_accumulate: Assertion to check the primary output pwo_uv_o.uv0_o in case of no accumulation, which is (uvz11+uv00)%Q


<br><br>


- assert_uv0_o_accumulate: Assertion to check the primary output pwo_uv_o.uv0_o, which is (uv0_o_int+w0_reg)%Q

- assert_uv1_o_accumulate: Assertion to check the primary output pwo_uv_o.uv1_o, which is (uv1_o_int_reg+w1_reg)%Q

<br><br>



## Reproduce results

The AIP has been tested and proven with Jasper C2RTL

To reproduce the results, load the tcl script in Jasper Gold.

Feel free to reach out to contact@lubis-eda.com to request the loadscripts. 