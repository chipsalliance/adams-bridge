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

# ntt_mlkem_masked_butterfly1x2 c2rtl
Date: 18.09.2025
Author: LUBIS EDA

## Cpp model description

The cpp model file can be found in the following directory: **<project_root>/formal/fv_ntt_mlkem_masked_butterfly1x2/fv_ntt_mlkem_masked_butterfly1x2.cpp**. This file models the operations which are performed by ntt_mlkem_masked_butterfly_1x2 module such as computation of u and v in masked GS mode for its shared inputs followed by division of 2 as the outputs. 

## tcl file description

The tcl file (prove_c2rtl.tcl)can be found in the following directory **<project_root>/formal/fv_ntt_mlkem_masked_butterfly1x2/jasper**. The tcl file contains in line assumptions and assertions as follows: 

## Constraints overview

- no_zero: assume zeroize signal is not asserted for simplicity purpose

- assume_xyz: assume xyz shared input or intermediate register value is less than MLKEM_Q (Prime number)

## Assertion IP Overview

The in-line assertions are divided for each operation of the module starting from the input until reaching the primary outputs. 

- u10_int: assertion to check u10_int register, which is the output U of masked GS butterfly instance 0

- u20_o: assertion to check uv_o.u20_o primary output, which is u10_int / 2

- sub_res_0: assertion to check (u-v) operation in masked GS butterfly instance 0

- mul_res_0: assertion to check (sub_res_0 * w) operation in masked GS butterfly instance 0

- v20_o: assertion to check v20_o primary output, which is v10_int / 2

- u11_int: assertion to check u11_int register, which is the output U of masked GS butterfly instance 1

- v20_o: assertion to check uv_o.v20_o primary output, which is u11_int / 2

- sub_res_1: assertion to check (u-v) operation in masked GS butterfly instance 1

- mul_res_1: assertion to check (sub_res_0 * w) operation in masked GS butterfly instance 1

- v21_o: assertion to check v21_o primary output, which is v11_int / 2

The following assertions are for intermediate checks of masked barret reduction instance (**masked_barrett_mult_inst**) inside instantiation of ntt_mlkem_masked_BFU_mult sub-block (**mult_inst_0**) in the following mlkem_masked_gs_butterfly instances: **mlkem_masked_bf_inst00** & **mlkem_masked_bf_inst01**. These intermediate checks are intended to help with the proof convergence

- mbr_check_tmp_x: Assertion to prove the tmp register within the masked_barrett_reduction module, which is x*5029 (of masked_gs_butterfly instance x)

- mbr_check_t_x: Assertion to prove the t register within the masked_barrett_reduction module, which is tmp >> 24

- mbr_check_x_reg_x: Assertion to prove the x_reg register within the masked_barrett_reduction module, which is the addition of the shares of the x primary input, x0 + x1

- mbr_check_qt_x: Assertion to prove the qt register within the masked_barrett_reduction module, which is t*3329

- mbr_check_c_x: Assertion to prove the c register within the masked_barrett_reduction module, which is x_reg - qt

- mbr_check_c_reg_CC3_x: Assertion to prove the c_reg[2][1] register within the masked_barrett_reduction module. c_reg is 3x2x13 bits, and shifts c (2x13) from 2->1->0. After computing c, it is stored in c_reg[2] in the 3rd cycle

- mbr_check_c_reg_CC5_x: Assertion to prove the c_reg[0][1] register within the masked_barrett_reduction module. c_reg is 3x2x13 bits, and shifts c (2x13) from 2->1->0. After computing c, it is stored in c_reg[2] in the 3rd cycle, before used in 5th cycle in y_int

- mbr_check_c_rolled0_x: Assertion to prove the c_rolled[0] register within the masked_barrett_reduction module, which is c0 + (Roller-carry)

- mbr_check_c_rolled1_x: Assertion to prove the c_rolled[1] register within the masked_barrett_reduction module, which is c1

- mbr_check_y_x: Assertion to prove the y_int register within the masked_barrett_reduction module, which is the reduction of the c_reg

- mbr_e2e_check_y_x: Assertion for end-to-end check of the masked barret reduction sub-block 

## Reproduce results

The AIP has been tested with Jasper C2RTL and results are hold bounded.

To reproduce the results, load the tcl script in Jasper Gold.

Feel free to reach out to contact@lubis-eda.com to request the loadscripts. 