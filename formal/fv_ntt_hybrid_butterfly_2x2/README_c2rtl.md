# ntt_hybrid_butterfly_2x2 c2rtl
Date: 18.09.2025
Author: LUBIS EDA

## Cpp model description

The cpp model file can be found in the following directory: **<project_root>/formal/fv_ntt_hybrid_butterfly_2x2/fv_ntt_ntt_hybrid_butterfly_2x2.cpp**. This file models the operations which are performed by ntt_hybrid_butterfly_2x2 modules such as butterfly operations (masked/unmasked) and pairwm operations (masked/unmasked) 

## tcl file description

The tcl file (prove_c2rtl.tcl)can be found in the following directory **<project_root>/formal/fv_ntt_ntt_hybrid_butterfly_2x2**. The tcl file contains in line assumptions and assertions as follows: 

## Constraints overview

- no_zero: assume zeroize signal is not asserted for simplicity purpose

- assume_acc: assume accumulate signal = 1, as this will cover both operations of accumulate and no accumulate

- stable_mode: assume mode signal is stable

- assume_mlkem: assume mlkem = 1 to restrict to mlkem mode only

- stable_intt_passthrough: assume intt_passthrough signal is stable throughout a full butterfly operation

- stable_ntt_passthrough: assume ntt_passthrough signal is stable throughout a full butterfly operation

- assume_no_intt_passthrough_during_ct: assume intt_passthrough is 0 during CT mode

- assume_no_ntt_passthrough_during_gs: assume ntt_passthrough is 0 during GS mode

- assume_input_xyz: assume xyz inputs/shared inputs value is less than MLKEM_Q (Prime number)

## Assertion IP Overview

The in-line assertions are divided for each operation of the module starting from the input until reaching the primary outputs. 

- ct_bfu_xx_u_mlkem: to check the output U during ct mode in unmasked butterfly module instance xx (xx = {00,01,10,11})

- ct_bfu_xx_v_mlkem: to check the output V during ct mode in unmasked butterfly module instance xx

- gs_bfu_xx_u_mlkem: to check the output U during gs mode in unmasked butterfly module instance xx

- gs_bfu_xx_v_mlkem: to check the output V during gs mode in unmasked butterfly module instance xx

- xxx_no_passthrough: to check the 2nd stage butterfly outputs during no passthrough condition (xxx = {u20, u21, v20, v21})

- xxx_ntt_passthrough: to check the 2nd stage butterfly outputs on ntt_passthrough mode (xxx = {u20, u21, v20, v21})

- xxx_intt_passthrough: to check the 2nd stage butterfly outputs on intt_passthrough mode (xxx = {u20, u21, v20, v21})

- xxx_intt_passthrough_m: to check the 2nd stage butterfly outputs on intt_passthrough masking mode (xxx = {u20, u21, v20, v21})

- u10_int: assertion to check u10_int register in butterfly_1x2 sub module, which is the output U of masked GS butterfly instance 0

- u20_o: assertion to check uv_o.u20_o output of butterfly_1x2 sub module, which is u10_int / 2

- sub_res_0: assertion to check (u-v) operation in masked GS butterfly instance 0 in butterfly_1x2 sub module

- mul_res_0: assertion to check (sub_res_0 * w) operation in masked GS butterfly instance 0 in butterfly_1x2 sub module

- u21_o: assertion to check u21_o output butterfly_1x2 sub module, which is v10_int / 2

- u11_int: assertion to check u11_int register in butterfly_1x2 sub module, which is the output U of masked GS butterfly instance 1

- v20_o: assertion to check uv_o.v20_o output of butterfly_1x2 sub module, which is u11_int / 2

- sub_res_1: assertion to check (u-v) operation in masked GS butterfly instance 1 in butterfly_1x2 sub module

- mul_res_1: assertion to check (sub_res_0 * w) operation in masked GS butterfly instance 1 in butterfly_1x2 sub module

- v21_o: assertion to check v21_o output butterfly_1x2 sub module, which is v11_int / 2

The following assertions are for intermediate checks of masked barret reduction instance (**masked_barrett_mult_inst**) inside instantiation of ntt_mlkem_masked_BFU_mult sub-block (**mult_inst_0**) in the following mlkem_masked_gs_butterfly instances: **mlkem_masked_bf_inst00, mlkem_masked_bf_inst01, u0v0, u0v1, u1v0, zeta_v1, u1v1, res0, and res1**. These intermediate checks are intended to help with the proof convergence

- mbr_check_tmp_x: Assertion to prove the tmp register within the masked_barrett_reduction module, which is x*5029 (of masked barret reduction x)

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

The following assertions are for ntt_masked_pairwm instance:

The in-line assertions are divided for each operation of the module starting from the input until reaching the primary outputs. 

- assert_u0v0: Assertion to check u0v0_packed register, which is the product of u0*v0

- assert_u0v1: Assertion to check u0v1_packed register, which is the product of u0*v1

- assert_u1v0: Assertion to check u1v0_packed register, which is the product of u1*v0

- assert_zeta_v1: Assertion to check zeta_v1_packed register, which is the product of zeta*v1

<br><br>


- assert_u0v0_red: Assertion to check u0v0_reduced register, which is the reduction of the product u0*v0

- assert_u0v1_red: Assertion to check u0v1_reduced register, which is the reduction of the product u0*v1

- assert_u1v0_red: Assertion to check u1v0_reduced register, which is the reduction of the product u1*v0

- assert_zeta_v1_red: Assertion to check zeta_v1_reduced register, which is the reduction of the product zeta*v1

<br><br>

- assert_u1v1: Assertion to check u1v1_packed register, which is the product of u1*v1

<br><br>


- assert_u1v1_red: Assertion to check u1v1_reduced register, which is the reduction of the product u1*v1

<br><br>


- assert_u0v0_plus_u1v1: Assertion to check uv0 register, which is the addition of u0v0 + u1v1

- assert_u0v1_plus_u1v0: Assertion to check uv1 register, which is the addition of u0v1 + u1v0

<br><br>


- assert_acc_uv0_w0: Assertion to check uvw0 register, which is the accumulation of uv0 + w0

- assert_acc_uv1_w1: Assertion to check uvw1 register, which is the accumulation of uv1 + w1

<br><br>


- assert_res0_no_acc: Assertion to check the primary output res0, in case of no accumulation, which is the reduction of uv0

- assert_res1_no_acc: Assertion to check the primary output res1, in case of no accumulation, which is the reduction of uv1

- assert_res0_acc: Assertion to check the primary output res0, in case of accumulation, which is the reduction of uvw0

- assert_res1_acc: Assertion to check the primary output res1, in case of accumulation, which is the reduction of uvw1

## Reproduce results

The AIP has been tested with Jasper C2RTL and results are hold bounded.

To reproduce the results, load the tcl script in Jasper Gold.

Feel free to reach out to contact@lubis-eda.com to request the loadscripts. 