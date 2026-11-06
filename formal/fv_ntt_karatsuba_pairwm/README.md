<!--
SPDX-License-Identifier: Apache-2.0

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-->

# ntt_karatsuba_pairwm

## Folder Structure
The formal project has individual verification benches for different modules. These are listed under the toplevel directory named **formal**. Under this directory, we have a directory named **fv_ntt_karatsuba_pairwm**

The **formal/fv_ntt_karatsuba_pairwm** contains the top level verification assertion IP(AIP) named as **fv_ntt_karatsuba_pairwm_top.sv** where the properties are written, and the constraints are written in **fv_ntt_karatsuba_pairwm_constraints.sv**. **fv_ntt_karatsuba_pairwm.cpp** is the C++ reference model used for C2RTL/DPV equivalence checking.


## DUT Overview

The DUT ntt_karatsuba_pairwm has the primary inputs and primary outputs as shown below.

| S.No | Port                | Direction | Description                                                                              |
| ---- | -----------------   | --------- | -----------------------------------------------------------------------------------------|
| 1    | clk                 | input     | The positive edge of the clk is used for all the signals                                 |
| 2    | reset_n             | input     | The reset signal is active low and resets the core                                       |
| 3    | zeroize             | input     | The core is reset when this signal is triggered.                                         |
| 4    | accumulate          | input     | The input signal which indicates an accumulate feature                                   |
| 5    | pwo_uvw_i           | input     | The input struct which holds the coefficients for the karatsuba pairwise multiplication  |
| 6    | pwo_z_i             | input     | The zeta input needed for the karatsuba pairwise multiplication                          |
| 7    | m0_red_i            | input     | Reduced base product u0·v0 mod Q, tapped from the BF multiplier (2 cycles after pwo_uvw_i)|
| 8    | m1_red_i            | input     | Reduced base product u1·v1 mod Q, tapped from the BF multiplier (2 cycles after pwo_uvw_i)|
| 9    | pwo_uv_o            | output    | The output result of the karatsuba pairwise multiplication                               |

The design performs a Karatsuba technique for an optimized implementation of pairwise multiplication. It also supports accumulation as an additional input.

The computed outputs follow the Karatsuba pairwise-multiply equations:
- `uv0_o (c2i)   = m0 + m1·zeta            mod Q`   (`+ w0` when accumulate is enabled)
- `uv1_o (c2i+1) = m2 - m0 - m1            mod Q`   (`+ w1` when accumulate is enabled), where `m2 = (u0+u1)·(v0+v1) mod Q`

The two base products `m0 = u0·v0` and `m1 = u1·v1` are **not** computed inside this module. They are produced by the butterfly (BF) multipliers and enter as pre-reduced BF-tap inputs `m0_red_i` / `m1_red_i`, arriving 2 cycles after the corresponding `pwo_uvw_i`. Only `m2` and `m1·zeta` are computed locally.

The datapath is pipelined with a fixed latency from `pwo_uvw_i` to `pwo_uv_o`:
- **4 cycles** when `accumulate = 0` (`MLKEM_PAIRWM_LATENCY`)
- **5 cycles** when `accumulate = 1` (`MLKEM_PAIRWM_ACC_LATENCY`, one extra mod-add stage for `+w`)


## Verification Strategy

**Approach.** The module is verified with a combined **end-to-end** and **white-box** formal strategy. The end-to-end assertions establish the functional contract — that `pwo_uv_o.uv0_o` and `pwo_uv_o.uv1_o` match the reference Karatsuba equations after the fixed pipeline latency. The white-box assertions complement these by pinning each internal pipeline stage against a per-stage golden model, so a failure localizes to the exact stage and the shallow per-stage proofs help the tool converge.

**Abstraction.** The base products `m0_red_i` / `m1_red_i` are treated as trusted, pre-reduced primary inputs; their correctness is owned by the BF-multiplier verification and they are abstracted here through range constraints. The reference model functions `fv_mult_mod_q`, `fv_add_mod_q`, and `fv_sub_mod_q` use SystemVerilog `%` modulo arithmetic as a specification-level abstraction of the RTL's DSP-multiply-plus-Barrett-reduction datapath.

**Environment models.** The input space is constrained in `fv_ntt_karatsuba_pairwm_constraints.sv`: all coefficient inputs (`u`, `v`, `w`), the zeta input `pwo_z_i`, and the BF-tap inputs `m0_red_i` / `m1_red_i` are assumed to be valid field elements (`< MLKEM_Q`), reflecting the guarantee provided by upstream logic. The `accumulate` mode select is held stable across a transaction, matching its use as a per-operation configuration rather than a per-cycle control. All assertions are guarded by `disable iff(!pi_reset_n | pi_zeroize)`, and reset/zeroize behavior is verified separately.


## Assertion IP Overview

The Assertion IP signals are bound with the respective signals in the DUT. The assertions inside **fv_ntt_karatsuba_pairwm_top.sv** perform both white-box (per-stage) and end-to-end checks for the ntt_karatsuba_pairwm module.

### fv_ntt_karatsuba_pairwm_top.sv — White-box checks

Per-stage checks that follow the pipeline. Each registered stage is verified with a 1-cycle (`##1 ... $past(...,1)`) alignment; purely combinational stages are checked in the same cycle.

- assert_ntt_karatsuba_pwm_add_res_u: Pre-add stage — `add_res_u = (u0 + u1) mod Q`, registered after 1 cycle.
- assert_ntt_karatsuba_pwm_add_res_v: Pre-add stage — `add_res_v = (v0 + v1) mod Q`, registered after 1 cycle.
- assert_ntt_karatsuba_pwm_m2: Combinational `m2_red_comb = (add_res_u · add_res_v) mod Q` (multiply + Barrett reduction).
- assert_ntt_karatsuba_pwm_m1z_red_comb: Combinational `m1z_red_comb = (m1_red_i · z_reg[1]) mod Q` (multiply + Barrett reduction).
- assert_ntt_karatsuba_pwm_m0_red_d1: 1-cycle delay register — `m0_red_d1 = $past(m0_red_i, 1)`.
- assert_ntt_karatsuba_pwm_m1_red_d1: 1-cycle delay register — `m1_red_d1 = $past(m1_red_i, 1)`.
- assert_ntt_karatsuba_pwm_c1_int: First subtract stage — `c1_int = (m2_red_reg - m0_red_i) mod Q`, registered.
- assert_ntt_karatsuba_pwm_uv0_o_int: `uv0_o_int = (m1z_red_reg + m0_red_d1) mod Q` (= `m0 + m1·zeta`), registered.
- assert_ntt_karatsuba_pwm_uv1_o_int: `uv1_o_int = (c1_int - m1_red_d1) mod Q` (= `m2 - m0 - m1`), registered.
- assert_ntt_karatsuba_pwm_w0_reg_3: `w` delay-chain depth — `w0_reg[3] = $past(w0_i, 4)`.
- assert_ntt_karatsuba_pwm_w1_reg_3: `w` delay-chain depth — `w1_reg[3] = $past(w1_i, 4)`.
- assert_ntt_karatsuba_pwm_z_reg_1: `zeta` delay alignment — `z_reg[1] = $past(pwo_z_i, 2)`.
- assert_ntt_karatsuba_pwm_uv0_o_acc: Accumulate stage — `uv0_o_acc = (uv0_o_int + w0_reg[3]) mod Q`, registered.
- assert_ntt_karatsuba_pwm_uv1_o_acc: Accumulate stage — `uv1_o_acc = (uv1_o_int + w1_reg[3]) mod Q`, registered.

### fv_ntt_karatsuba_pairwm_top.sv — End-to-end checks

- assert_ntt_karatsuba_pwm_uv0_o_no_accumulate: Checks that the output `pwo_uv_o.uv0_o` is calculated properly according to the c2i karatsuba pairwm equation, when accumulate is disabled. Performed end-to-end after `MLKEM_PAIRWM_LATENCY`.
- assert_ntt_karatsuba_pwm_uv1_o_no_accumulate: Checks that the output `pwo_uv_o.uv1_o` is calculated properly according to the c2i+1 karatsuba pairwm equation, when accumulate is disabled. Performed end-to-end after `MLKEM_PAIRWM_LATENCY`.
- assert_ntt_karatsuba_pwm_uv0_o_accumulate: Checks that the output `pwo_uv_o.uv0_o` is calculated properly according to the c2i karatsuba pairwm equation, when accumulate is enabled. Performed end-to-end after `MLKEM_PAIRWM_ACC_LATENCY`.
- assert_ntt_karatsuba_pwm_uv1_o_accumulate: Checks that the output `pwo_uv_o.uv1_o` is calculated properly according to the c2i+1 karatsuba pairwm equation, when accumulate is enabled. Performed end-to-end after `MLKEM_PAIRWM_ACC_LATENCY`.
- assert_ntt_karatsuba_pwm_reset: Checks that the output `pwo_uv_o` is reset properly after reset or zeroize.
- assert_ntt_karatsuba_pwm_output_range: Data-integrity check — both output fields `uv0_o` and `uv1_o` are always reduced (`< MLKEM_Q`).

### fv_ntt_karatsuba_pairwm_constraints.sv — Constraints

- assume_stable_accumulate: The `accumulate` select is held stable across a transaction.
- assume_u_range: `u0_i` and `u1_i` are valid field elements (`< MLKEM_Q`).
- assume_v_range: `v0_i` and `v1_i` are valid field elements (`< MLKEM_Q`).
- assume_w_range: `w0_i` and `w1_i` accumulate inputs are valid field elements (`< MLKEM_Q`).
- assume_zeta_range: `pwo_z_i` (zeta) is a valid field element (`< MLKEM_Q`).
- assume_m0_range: BF-tap input `m0_red_i` is a valid field element (`< MLKEM_Q`).
- assume_m1_range: BF-tap input `m1_red_i` is a valid field element (`< MLKEM_Q`).

## Reproduce Results
The AIP has been tested and proven with atleast one of these formals tools (Onespin ,Jasper , vcf).

To reproduce the results:
Load the AIP with all the necessary constraints together in your formal tool.

Feel free to reach out to contact@lubis-eda.com to request the loadscripts or the lubis modules.
