# ntt_ctrl_pwo_pairwm
Date: 02.09.2025
Author: LUBIS EDA

## Folder Structure
The following files are part of the main directory **<project_root>/formal/fv_ntt_ctrl/ntt_ctrl_pwo_pairwm**

- **model/ntt_ctrl_pwo_pairwm.h** is the ESL model of ntt_ctrl block in pwo mode written in SystemC

- **model/ntt_ctrl_pwo_pairwm.luref** is the refinement file of the esl model to the rtl design, used to generate the binding file.

- **ntt_ctrl_pwo_pairwm.sv** contains the auto-generated assertion IP(AIP) by LUBIS AppBuilder for ntt_ctrl block in pwo (pwm/pwa/pws/pairwm) mode

- **ntt_ctrl_pwo_pairwm_functions.sv** contains the auto-generated functions by LUBIS AppBuilder which are used in the AIP

- **ntt_ctrl_pwo_pairwm_binding.sv** contains the auto-generated binding file by LUBIS AppBuilder which links the AIP to the DUT

- **ntt_ctrl_pwo_pairwm_pkg.sv** contains the auto-generated package/enum declaration by LUBIS AppBuilder used in the AIP

- **fv_ntt_ctrl_pwo_pairwm_additional_aips.sv** contains the additional assertions for ntt_ctrl block in pwo (pwm/pwa/pws/pairwm) mode

- **fv_ntt_ctrl_pwo_pairwm_constraints.sv** contains the assumptions/constraints for ntt_ctrl_pwo_pairwm mode

- **fv_ntt_ctrl_pwo_pairwm_top.sv** is the wrapper file.


## DUT Overview

The DUT has the primary inputs and primary outputs as shown below.

| S.No | Port                       | Direction | Description                                                                                                    |
| ---- | ---------------------      | --------- | ---------------------------------------------------------------------------------------------------------------|
| 1    | clk                        | input     | The positive edge of the clk is used for all the signals                                                       |
| 2    | reset_n                    | input     | The reset signal is active low and resets the module                                                           |
| 3    | zeroize                    | input     | The module is reseted when this signal is triggered.                                                           |
| 4    | ntt_mode                   | input     | The input for ntt mode selection (ct, gs, pwm, pwa, pws, pairwm)                                               |
| 5    | ntt_enable                 | input     | The input for enabling ntt                                                                                     |
| 6    | butterfly_ready            | input     | The input indicating ready from hybrid butterfly 2x2 module                                                    |
| 7    | buf0_valid                 | input     | The input indicating valid signal from the shuffle buffer (not used in pwo mode)                               |
| 8    | sampler_valid              | input     | The input indicating sampler valid signal from ntt_top block (used only in pwo mode)                           |
| 9    | accumulate                 | input     | The input to indicate accumulate case                                                                          |
| 10   |ntt_mem_base_addr[2:0][13:0]| input     | NTT Base addresses inputs, consists of source, destination, and interim base addresses each 14-bit             |
| 11   |pwo_mem_base_addr[2:0][13:0]| input     | PWO Base addresses inputs, consists of base address a, b, and c, each 14-bit                                   |
| 12   | shuffle_en                 | input     | The input for enabling shuffling operation                                                                     |
| 13   | random[5:0]                | input     | Randomized input for chunk and index randomization process                                                     |
| 14   | masking_en                 | input     | The input for enabling masked operation                                                                        |
| 15   | mlkem                      | input     | The input for enabling mlkem operation.                                                                        |
| 16   | bf_enable                  | output    | Output to enable butterfly operation                                                                           |
| 17   | opcode[2:0]                | output    | Output to determine ntt mode of operation                                                                      |
| 18   | masking_en_ctrl            | output    | Output to indicate opertion of masked_gs (0 for pwo mode)                                                      |
| 19   | buf_wren                   | output    | Write enable output to the shuffle buffer (0 for pwo mode)                                                     |
| 20   | buf_rden                   | output    | Read enable output to the shuffle buffer  (0 for pwo mode)                                                     |
| 21   | buf_wrptr[1:0]             | output    | Write pointer output to the shuffle buffer (0 for pwo mode)                                                    |
| 22   | buf_rdptr[1:0]             | output    | Read pointer output to the shuffle buffer  (0 for pwo mode)                                                    |
| 23   | twiddle_addr[6:0]          | output    | Twiddle address output to the twiddle_lookup block                                                             |
| 24   | mem_rd_addr[14:0]          | output    | Memory Read Address output to ntt_top block  (only for ct/gs)                                                  |
| 25   | mem_wr_addr[14:0]          | output    | Memory Write Address output to ntt_top block (only for ct/gs)                                                  |
| 26   | mem_rd_en                  | output    | Memory Read enable output (only for ct/gs)                                                                     |
| 27   | mem_wr_en                  | output    | Memory Write enable output (only for ct/gs)                                                                    |
| 28   | buf_wr_rst_count           | output    | Buffer write reset count output signal (only for ct/gs)                                                        |
| 29   | buf_rd_rst_count           | output    | Buffer read reset count output signal (only for ct/gs)                                                         |
| 30   | pw_mem_rd_addr_a[14:0]     | output    | PWO Memory Read Address a output to ntt_top block  (only for pwo)                                              |
| 31   | pw_mem_rd_addr_b[14:0]     | output    | PWO Memory Read Address b output to ntt_top block  (only for pwo)                                              |
| 32   | pw_mem_rd_addr_c[14:0]     | output    | PWO Memory Read Address c output to ntt_top block  (only for pwo)                                              |
| 33   | pw_mem_wr_addr_c[14:0]     | output    | PWO Memory Write Address c output to ntt_top block  (only for pwo)                                             |
| 34   | pw_rden                    | output    | PWO Memory Read enable output (only for pwo)                                                                   |
| 35   | pw_wren                    | output    | PWO Memory Write enable output (only for pwo)                                                                  |
| 36   | pw_share_mem_rden          | output    | PWO Shared Memory Read enable output (only for pwo)                                                            |
| 37   | busy                       | output    | Output indicating busy signal                                                                                  |
| 38   | done                       | output    | Output indicating done signal                                                                                  |
| 39   | ntt_passthrough            | output    | Output indicating ntt passthrough operation (only on ct & mlkem mode)                                          |
| 40   | intt_passthrough           | output    | Output indicating intt passthrough operation (only on gs & mlkem mode)                                         |


The ntt_ctrl is the main control module for mldsa/mlkem ntt operation. It receives control signals from ntt_top module, ready signal from hybrid butterfly module, valid signals from sampler and buffer modules. Depending on the mode of operations (ct/gs/pwm/pwa/pws/pairwm), it produces enable read/write signals, computes the appropriate addresses. In the following list are given the AIPs for ntt_ctrl during pwo mode of operations (pwm, pairwm, pws, or pwa): 

## Assertion IP Overview

The Assertion IP signals are bound with the respective signals in the dut, where for the **rst_n** is bound with the DUT (reset_n && !zeroize), which ensures the reset functionality.

- commons_reset_a: Checks all common outputs are zero upon reset

- read_reset_a: Checks all read operation related outputs are zero upon reset

- write_reset_a: Checks all write operation related outputs are zero upon reset

- commons_state_to_state_a: Checks for common output such as opcode, and also checks for non pwo outputs should be stable

- read_read_exec_to_read_exec_a: Checks for all pwo-related outputs & regs during read_exec to read_exec state transition.

- read_read_exec_to_read_exec_wait_a: Checks for all pwo-related outputs & regs during read_exec to read_exec_wait state transition.

- read_read_exec_to_read_stage_a: Checks for all pwo-related outputs & regs during read_exec to read_stage state transition.

- read_read_exec_wait_to_read_exec_a: Checks for all pwo-related outputs & regs during read_exec_wait to read_exec state transition.

- read_read_exec_wait_to_read_exec_wait_a: Checks for all pwo-related outputs & regs during read_exec_wait to read_exec_wait state transition.

- read_read_idle_to_read_idle_a: Checks for all pwo-related outputs & regs during read_idle to read_idle state transition.

- read_read_idle_to_read_stage_a: Checks for all pwo-related outputs & regs during read_idle to read_stage state transition.

- read_read_stage_to_read_exec_a: Checks for all pwo-related outputs & regs during read_stage to read_exec state transition.

- read_read_stage_to_read_idle_a: Checks for all pwo-related outputs & regs during read_stage to read_idle state transition.

- read_read_stage_to_read_stage_a: Checks for all pwo-related outputs & regs during read_stage to read_stage state transition.

- write_write_idle_to_write_idle_a: Checks for all pwo-related outputs & regs during write_idle to write_idle state transition.

- write_write_idle_to_write_stage_a: Checks for all pwo-related outputs & regs during write_idle to write_stage state transition.

- write_write_mem_to_write_mem_a: Checks for all pwo-related outputs & regs during write_mem to write_mem state transition.

- write_write_mem_to_write_stage_a: Checks for all pwo-related outputs & regs during write_mem to write_stage state transition.

- write_write_mem_to_write_wait_a: Checks for all pwo-related outputs & regs during write_mem to write_wait state transition.

- write_write_stage_to_write_idle_a: Checks for all pwo-related outputs & regs during write_stage to write_idle state transition.

- write_write_stage_to_write_mem_a: Checks for all pwo-related outputs & regs during write_stage to write_mem state transition.

- write_write_stage_to_write_wait_a: Checks for all pwo-related outputs & regs during write_stage to write_wait state transition.

- write_write_wait_to_write_mem_a: Checks for all pwo-related outputs & regs during write_wait to write_mem state transition.

- write_write_wait_to_write_stage_a: Checks for all pwo-related outputs & regs during write_wait to write_stage state transition.

- write_write_wait_to_write_wait_a: Checks for all pwo-related outputs & regs during write_wait to write_wait state transition.

- assert_bf_enable_a: Checks the bf_enable output during pwo mode.

- assert_twiddle_addr_a: Checks twiddle_addr output during pwo mode.

- assert_pw_rden_a: Checks pw_rden output during pwo mode.

- assert_pw_wren_a: Checks pw_wren output during pwo mode.

- assert_pw_shared_mem_rden_a: Checks pw_shared_mem_rden output during pwo mode.

- assert_busy_a: Checks busy signal output during pwo mode.

- assert_rst_rounds_a: Checks rst_rounds register during pwo mode.

- read_read_idle_eventually_left_a: Liveness assertion to check that state read_idle is eventually left.

- read_read_stage_eventually_left_a: Liveness assertion to check that state read_stage is eventually left.

- read_read_exec_eventually_left_a: Liveness assertion to check that state read_exec is eventually left.

- read_read_exec_wait_eventually_left_a: Liveness assertion to check that state read_exec_wait is eventually left.

- write_write_idle_eventually_left_a: Liveness assertion to check that state write_idle is eventually left.

- write_write_stage_eventually_left_a: Liveness assertion to check that state write_stage is eventually left.

- write_write_wait_eventually_left_a: Liveness assertion to check that state write_wait is eventually left.

- write_write_mem_eventually_left_a: Liveness assertion to check that state write_mem is eventually left.

- read_consistency_onehot0_state: Checks that only one read state is active at any given time.

- write_consistency_onehot0_state: Checks that only one write state is active at any given time.

## Reproduce results

The AIP has been tested and proven with Onespin, Jasper, VCF, & Yosys formal tools. Coverage analysis was also performed with 100% coverage result.

To reproduce the results:
Load the design, AIP files, and fv_constraints together in your formal tool. 

Feel free to reach out to contact@lubis-eda.com to request for the loadscripts. 