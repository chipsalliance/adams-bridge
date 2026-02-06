# ntt_mlkem_masked_gs_butterfly c2rtl
Date: 18.09.2025
Author: LUBIS EDA

## Cpp model description

The cpp model file can be found in the following directory: **<project_root>/formal/fv_ntt_mlkem_masked_gs_butterfly.cpp**. This file models the operations which are performed by ntt_mlkem_masked_gs_butterfly module such as computation of u and v in masked GS mode for its shared inputs. 

## tcl file description

The tcl file (prove_c2rtl.tcl)can be found in the following directory **<project_root>/formal/fv_ntt_mlkem_masked_gs_butterfly/jasper**. The tcl file contains in line assumptions and assertions as follows: 

## Constraints overview

- no_zero: assume zeroize signal is not asserted for simplicity purpose

- assume_xyz: assume xyz shared input or intermediate register value is less than MLKEM_Q (Prime number)

## Assertion IP Overview

The in-line assertions are divided for each operation of the module starting from the input until reaching the primary outputs. 

- add_res_0: assertion to check (u+v) operation in masked GS butterfly

- sub_res_0: assertion to check (u-v) operation in masked GS butterfly

- mul_res_0: assertion to check (sub_res_0 * w) operation in masked GS butterfly

The following assertions are for intermediate checks of masked barret reduction instance (**masked_barrett_mult_inst**) inside **mult_inst_0** instantiation of ntt_mlkem_masked_BFU_mult sub-block: 
These intermediate checks are intended to help with the proof convergence

- mbr_check_tmp: Assertion to prove the tmp register within the masked_barrett_reduction module, which is x*5029

- mbr_check_t: Assertion to prove the t register within the masked_barrett_reduction module, which is tmp >> 24

- mbr_check_x_reg: Assertion to prove the x_reg register within the masked_barrett_reduction module, which is the addition of the shares of the x primary input, x0 + x1

- mbr_check_qt: Assertion to prove the qt register within the masked_barrett_reduction module, which is t*3329

- mbr_check_c: Assertion to prove the c register within the masked_barrett_reduction module, which is x_reg - qt

- mbr_check_c_reg_CC3: Assertion to prove the c_reg[2][1] register within the masked_barrett_reduction module. c_reg is 3x2x13 bits, and shifts c (2x13) from 2->1->0. After computing c, it is stored in c_reg[2] in the 3rd cycle

- mbr_check_c_reg_CC5: Assertion to prove the c_reg[0][1] register within the masked_barrett_reduction module. c_reg is 3x2x13 bits, and shifts c (2x13) from 2->1->0. After computing c, it is stored in c_reg[2] in the 3rd cycle, before used in 5th cycle in y_int

- mbr_check_c_rolled0: Assertion to prove the c_rolled[0] register within the masked_barrett_reduction module, which is c0 + (Roller-carry)

- mbr_check_c_rolled1: Assertion to prove the c_rolled[1] register within the masked_barrett_reduction module, which is c1

- mbr_check_y: Assertion to prove the y_int register within the masked_barrett_reduction module, which is the reduction of the c_reg

- mbr_e2e_check_y: Assertion for end-to-end check of the masked barret reduction sub-block 

## Reproduce results

The AIP has been tested with Jasper C2RTL and results are hold bounded.

To reproduce the results, load the tcl script in Jasper Gold.

Feel free to reach out to contact@lubis-eda.com to request the loadscripts. 