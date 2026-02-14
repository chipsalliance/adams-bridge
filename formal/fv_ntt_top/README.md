# ntt_top
Date: 02.09.2025
Author: LUBIS EDA

## Folder Structure
The following files are part of the main directory ****<project_root>/formal/fv_ntt_top**


- **fv_ntt_top_mlkem.sv** contains the assertions for ntt_top module

- **fv_ntt_top_mlkem_internal.sv** contains the assertions for internal submodules of ntt_top such ass hybrid_bfu_2x2, ntt_ctrl, etc.

- **fv_ntt_top_mlkem_constraints.sv** contains the assumptions/constraints for ntt_top 

- **fv_ntt_top_mlkem_top.sv** is the wrapper file.


## DUT Overview

The DUT has the primary inputs and primary outputs as shown below.

| S.No | Port                       | Direction | Description                                                                                                    |
| ---- | ---------------------      | --------- | ---------------------------------------------------------------------------------------------------------------|
| 1    | clk                        | input     | The positive edge of the clk is used for all the signals                                                       |
| 2    | reset_n                    | input     | The reset signal is active low and resets the module                                                           |
| 3    | zeroize                    | input     | The module is reseted when this signal is triggered.                                                           |
| 4    | mode                       | input     | The input for ntt mode selection (ct, gs, pwm, pwa, pws, pairwm)                                               |
| 5    | ntt_enable                 | input     | The input for enabling ntt                                                                                     |
| 6    | rnd_i [4:0][45:0]          | input     | Randomized input for masking purpose                                                                           |
| 7    | sampler_valid              | input     | The input indicating sampler valid signal from abr_ctrl block (used only in pwo mode)                          |
| 8    | accumulate                 | input     | The input to indicate accumulate case                                                                          |
| 9    |ntt_mem_base_addr[2:0][13:0]| input     | NTT Base addresses inputs, consists of source, destination, and interim base addresses each 14-bit             |
| 10   |pwo_mem_base_addr[2:0][13:0]| input     | PWO Base addresses inputs, consists of base address a, b, and c, each 14-bit                                   |
| 11   | shuffle_en                 | input     | The input for enabling shuffling operation                                                                     |
| 12   | random[5:0]                | input     | Randomized input for chunk and index randomization process                                                     |
| 13   | masking_en                 | input     | The input for enabling masked operation                                                                        |
| 14   | mlkem                      | input     | The input for enabling mlkem operation.                                                                        |
| 15   | mem_rd_data[383:0]         | input     | Memory read data input (NTT)                                                                                   |
| 16   | pwm_a_rd_data[383:0]       | input     | Memory read data input a (PWO)                                                                                 |
| 17   | pwm_b_rd_data[383:0]       | input     | Memory read data input b (PWO)                                                                                 |
| 18   | mem_wr_req                 | output    | Memory Write Request enable & address output (NTT)                                                             |
| 19   | mem_rd_req                 | output    | Memory Read Request enable & address output (NTT)                                                              |
| 20   | pwm_a_rd_req               | output    | Memory Read Request enable & address output (PWM a)                                                            |
| 21   | pwm_b_rd_req               | output    | Memory Read Request enable & address output (PWM b)                                                            |
| 22   | mem_wr_data[383:0]         | output    | Memory write data output                                                                                       |
| 23   | ntt_busy                   | output    | Output indicating busy signal                                                                                  |
| 24   | ntt_done                   | output    | Output indicating done signal                                                                                  |


ntt_top module is responsible for the following tasks:
1. Keeps track of stages of bf2x2 operation
2. Reads appropriate addr of ROM and passes w input to bf2x2
3. Orchestrates memory writes and reads and passes u and v inputs to bf2x2
4. Controls direct PWM inputs to bf2x2 in pwm mode
5. Maintains mode input to bf2x2 and related input/output muxes
6. Aligns data and control delays associated with bf2x2 module

## Assertion IP Overview

The Assertion IP signals are bound with the respective signals in the dut, where for the **rst_n** is bound with the DUT (reset_n && !zeroize), which ensures the reset functionality.

- assert_check_po_pwm_a_rd_req: Property to check request outputs when the masking is enabled (both for shuffle and not shuffle case)

- assert_check_po_pwm_a_rd_req_no_pwo: Property to check if it is not a pwo mode then no read request and addr.

- assert_check_po_pwm_a_rd_req_no_ongoing: Property to check if nothing is ongoing then no read request and addr.

- assert_check_po_pwm_b_rd_req_no_shuffle: Property to check req b when the shuffle is disabled

- assert_check_po_pwm_b_rd_req_no_shuffle_no_mask_en: Property to check req_b when the masking is disabled and the shuffle is disabled

- assert_po_pwm_b_rd_req_shuffle: Property to check req b when the shuffling is enabled irrespective of the masking

- assert_no_p_mode_no_req: Property to check if the mode is not pwo then no read request.

- assert_mem_wr_req_ct_no_shuffle: Property to check write req and addr for ct mode when shuffle is disabled

- assert_mem_wr_req_ct_shuffle: Property to check write req and addr for ct mode when shuffle is enabled

- assert_mem_wr_req_gs : Property to check write req and addr for gs mode

- assert_mem_wr_req_pwo: Property to check write req and addr for pwo mode

- assert_mem_wr_data_ct: Property to check for wr_data output during ct_mode and wr_req is write

- assert_mem_wr_data_gs: Property to check for wr_data output during gs_mode and wr_req is write

- assert_mem_wr_data_pwm_pwa_pws: Property to check for wr_data output during pwo mode when masking is disabled

- assert_mem_wr_data_pwm_masked: Property to check for wr_data output during pwo mode when masking is enabled

- assert_share_mem_wr_data : Property to check for share_mem_wr_data regs during pwm/pairwm mode and masking enabled

- assert_share_mem_wr_data_other: Property to check for share_mem_wr_data regs when not in pwm/pairwm mode and masking enabled

- assert_check_share_mem_wr_data_reset: Property to check for share_mem_wr_data regs during reset

- assert_mem_rd_req_other: Property to check read enable and addr for other modes when not in ct, gs or pwm/pairwm mode

- assert_num_rd_always_64: Property to check that mem_rd_en is always asserted 64-cycle long

- assert_num_wr_always_64: Property to check that mem_wr_en is always asserted 64-cycle long

- assert_num_pwrd_always_64: Property to check that pw_rden is always asserted 64-cycle long until done signal is asserted

- assert_num_pwwr_always_64: Property to check that pw_wren is always asserted 64-cycle long until done signal is asserted

- assert_cmd_ctrl_done_to_output: Connection check for cmd_ctrl done to ntt_done

- assert_cmd_ctrl_busy_to_output: Connection check for cmd_ctrl busy to ntt_busy

- assert_busy_eventually_not_busy: Property to check liveness condition of ntt_busy output signal

- assert_correct_cmd_ctrl_input_***: Assertions to check connectivity of command control inputs

- assert_correct_butterfly_input_***: Assertions to check connectivity of butterfly inputs

- assert_pi_mode_ct_assignment: Assertion to check uvw_i w input assignments on ct_mode

- assert_pi_mode_gs_pwm_intt_shuffle: Assertion to check uvw_i w input assignments on gs_mode & shuffling enabled

- assert_pi_mode_gs_pwm_intt_no_shuffle: Assertion to check uvw_i w input assignments on gs_mode & shuffling disabled

- assert_pi_mode_default_assignment: Assertion to check uvw_i w input assignments on other modes

- assert_mlkem_shares_pairwm_zeta: Assertions to check mlkem_shares_pairwm_zeta13_i inputs assignments in pairwm mode

- assert_mlkem_pairwm_zeta: Assertions to check mlkem_pairwm_zeta13_i inputs assignments in pairwm mode

- assert_no_mlkem_pairwm_zeta: Assertions to check mlkem_pairwm_zeta13_i inputs assignments are zero when not in pairwm mode

- assert_check_uvw_assignment_ct: Assertion to check uvw_i u & v & pw_uvw_i input assignments for ct mode

- assert_check_uvw_assignment_gs: Assertion to check uvw_i u & v & pw_uvw_i input assignments for gs mode

- assert_check_pw_uvw_assignment_pwm: Assertion to check uvw_i & pw_uvw_i input assignments during pwm mode / pairwm mode and no masking

- assert_check_pw_uvw_assignment_pwm_masking: Assertion to check uvw_i & pw_uvw_i input assignments for pwm mode / pairwm mode and masking

- assert_check_pw_uvw_assignment_pwa_pws: Assertion to check uvw_i & pw_uvw_i input assignments for pwa or pws mode

- assert_check_zero_uvw_default: Assertions for Default Case (Zeroing Out) of uvw_i

- assert_check_zero_pw_uvw_default: Assertions for Default Case (Zeroing Out) of pw_uvw_i

- assert_check_pwm_shares_in_pwm_masking_u: Assertion for the pwm shares used in pwm mode or pairwm mode with masking enable (u)

- assert_check_pwm_shares_in_pwm_masking_v: Assertion for the pwm shares used in pwm mode or pairwm mode with masking enable (v)

- assert_check_pwm_shares_in_pwm_masking_w: Assertion for the pwm shares used in pwm mode or pairwm mode with masking enable (w shuffle)

- assert_check_pwm_shares_in_pwm_masking_w_no_shuffle: Assertion for the pwm shares used in pwm mode with masking enable (w no shuffle)

- assert_check_pwm_shares_in_pairwm_masking_w_no_shuffle: Assertion for the pwm shares used in pairwm mode with masking enable (w no shuffle)

- assert_check_pwm_shares_in_pwm_no_masking: Assertion for the pwm shares used in pwm mode or pairwm mode with no masking enable

- assert_check_bf_shares_in_gs_masking: Asserion to check input to the butterfly unit the bf_shares used in case of the gs mode with ctrl masking enable

- assert_check_bf_shares_in_gs_no_masking: Asserion to check input to the butterfly unit the bf_shares used in gs mode with no masking enable

- assert_correct_buffer_input_***: Shuffle Buffer connectivity checks

- assert_check_hybrid_pw_uvw_aggregation: Assertion for hybrid_pw_uvw_i Aggregation

## Reproduce results

The AIP has been tested and proven with Onespin, Jasper, VCF, & Yosys formal tools. Coverage analysis was also performed with 100% coverage result.

To reproduce the results:
Load the design, AIP files, and fv_constraints together in your formal tool. 

Feel free to reach out to contact@lubis-eda.com to request for the loadscripts. 