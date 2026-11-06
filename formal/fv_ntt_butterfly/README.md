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

# ntt_butterfly

## Folder Structure
The following files and subdirectories are part of the main directory **formal/fv_ntt_butterfly**

- `fv_ntt_butterfly_m.sv`: Assertion IP (AIP) — functional correctness properties for all operating modes
- `fv_ntt_butterfly_conn_m.sv`: Connectivity-checking properties (mux and pipeline routing)
- `fv_ntt_butterfly_pkg.sv`: Package definitions — shared types, mode encodings, and prime constants (MLDSA/MLKEM)
- `fv_ntt_butterfly_functions.sv`: Reference model helper functions (dual-mode: MLDSA and MLKEM)
- `fv_ntt_butterfly_constraints.sv`: Assumptions constraining the formal input space
- `fv_ntt_butterfly_binding.sv`: Binding of AIP ports to DUT internal signals
- `fv_ntt_butterfly_top.sv`: Top-level wrapper
- model: Contains the high level abstracted model
  - `model/ntt_butterfly.h`: C-style reference model (Lubis luref / OneSpin)
  - `model/ntt_butterfly_spec.cpp`: C++ reference model for VC Formal DPV / JasperGold C2RTL

## DUT Overview

The DUT `ntt_butterfly` has the primary inputs and primary outputs as shown below.

| S.No | Port                   | Direction | Description                                                                                         |
| ---- | ---------------------- | --------- | ----------------------------------------------------------------------------------------------------|
| 1    | clk                    | input     | The positive edge of clk is used for all signals.                                                   |
| 2    | reset_n                | input     | Active-low synchronous reset; resets all registers and primary outputs to their initial values.     |
| 3    | zeroize                | input     | Forces a reset when asserted; combined with reset_n in the AIP as `reset_n && !zeroize`.           |
| 4    | opu_i [22:0]           | input     | Coefficient input U (first butterfly operand ).                                                      |
| 5    | opv_i [22:0]           | input     | Coefficient input V (second butterfly operand).                                                     |
| 6    | opw_i [22:0]           | input     | Twiddle factor input W (from NTT ROM).                                                              |
| 7    | mode [2:0]             | input     | Selects the operation mode (CT=0, GS=1, PWM=2, PWA=3, PWS=4, PAIRWM=5).                           |
| 8    | accumulate             | input     | Enables accumulation in PWM mode; stable for the duration of one transaction.                       |
| 9    | mlkem                  | input     | Selects the prime modulus: 1 = MLKEM (Q=3329), 0 = MLDSA (Q=8 380 417).                           |
| 10   | u_o [22:0]             | output    | Butterfly output U; valid after the latency defined by the active mode.                             |
| 11   | v_o [22:0]             | output    | Butterfly output V; valid after the latency defined by the active mode.                             |
| 12   | pwm_res_o [22:0]       | output    | Point-wise multiply / add / subtract result (modes PWM, PWA, PWS).                                 |
| 13   | pairwm_mul_red_o [22:0]| output    | MLKEM pairwise multiply result: `(opu_i × opv_i) % 3329`; valid in PAIRWM mode only.              |

### Operating Modes

| `mode` | Name   | Description                              | Output latency |
| ------ | ------ | ---------------------------------------- | -------------- |
| 0      | CT     | Cooley-Tukey butterfly                   | 3 cycles       |
| 1      | GS     | Gentleman-Sande butterfly                | 3 cycles       |
| 2      | PWM    | Point-wise multiply (with/without accum) | 3 cycles       |
| 3      | PWA    | Point-wise add                           | 1 cycle        |
| 4      | PWS    | Point-wise subtract                      | 1 cycle        |
| 5      | PAIRWM | Pairwise multiply (MLKEM only)           | 2 cycles       |

The design accepts three 23-bit coefficient inputs and a mode selector, performs the selected butterfly or point-wise arithmetic modulo the active prime, and returns the results on the appropriate output ports.

## Assertion IP Overview

The Assertion IP signals are bound to the respective DUT signals via `fv_ntt_butterfly_binding.sv`. The reset signal is bound to `(reset_n && !zeroize)`, so either a low `reset_n` or an asserted `zeroize` triggers the reset condition.

### Constraints (`fv_ntt_butterfly_constraints.sv`)

- `assume_stable_mode`: The `mode` input is stable (does not change) within a transaction.
- `assume_max_input`: All three coefficient inputs (`opu_i`, `opv_i`, `opw_i`) are bounded below the active prime — below 3 329 in MLKEM mode and below 8 380 417 in MLDSA mode.
- `assume_stable_acc`: The `accumulate` signal is stable throughout a transaction.
- `assume_stable_mlkem`: The `mlkem` signal is stable throughout a transaction, fixing the prime for the duration of one proof run.

### Functional Assertions (`fv_ntt_butterfly_m.sv`)

- `run_reset_a`: After reset, all primary outputs (`u_o`, `v_o`, `pwm_res_o`) and pipeline registers (`u_reg`, `u_reg_d2`, `w_reg`, `w_reg_d2`, `add_res_d1`, `add_res_d2`) are zero and the FSM is in the INIT state.

- `run_INIT_to_CT_a`: CT mode (mode=0). Verifies that at cycle 1 from INIT the multiplier operands are `mul_opa=opv_i`, `mul_opb=opw_i` and the input pipeline registers latch correctly; at cycle 3, `u_o` equals `(opu_i + (opv_i × opw_i)) % Q` and `v_o` equals `(opu_i − (opv_i × opw_i)) % Q` (both mod the active prime). `pwm_res_o` is zero.

- `run_INIT_to_GS_a`: GS mode (mode=1). Verifies pipeline register correctness over three cycles; at cycle 2, `mul_opa` carries `div2(opu_i − opv_i)` and `mul_opb` carries `opw_i`; at cycle 3, `u_o` equals `(opu_i + opv_i) / 2 % Q` and `v_o` equals `(div2(opu_i − opv_i) × opw_i) % Q`. `pwm_res_o` is zero.

- `run_INIT_to_PWA_PWS_a`: PWA (mode=3) and PWS (mode=4) modes. At cycle 1, `pwm_res_o` equals `(opu_i + opv_i) % Q` for PWA or `(opu_i − opv_i) % Q` for PWS; `u_o` and `v_o` are zero; multiplier inputs are zero (adder path only).

- `run_INIT_to_PAIRWM_a`: PAIRWM mode (mode=5, MLKEM only). Combinationally, `mul_opa=opu_i` and `mul_opb=opv_i`; `u_o`, `v_o`, and `pwm_res_o` are zero at INIT. After 2 cycles, `pairwm_mul_red_o` equals `(opu_i × opv_i) % 3329`.

- `run_INIT_to_PWM_ACC_a`: PWM accumulate mode (mode=2, accumulate=1). Pipeline registers checked at cycles 1 and 2; at cycle 3, `pwm_res_o` equals `(opw_i + (opu_i × opv_i)) % Q`. `u_o` and `v_o` are zero.

- `run_INIT_to_PWM_NOT_ACC_a`: PWM non-accumulate mode (mode=2, accumulate=0). At cycle 2, `pwm_res_o` equals `(opu_i × opv_i) % Q`. `u_o` and `v_o` are zero.

### Whitebox — Multiplication Pipeline (`fv_ntt_butterfly_m.sv`)

These assertions verify the internal multiplier and Barrett reduction pipeline step by step.

- `mul_res_product_a`: The DSP output `mul_res` equals `mul_opa × mul_opb` (combinational).
- `mul_res_reg_a`: `mul_res_reg` captures the low 24 bits of `mul_res` on the next clock edge.
- `mldsa_mul_res_reg_a` / `mldsa_mul_res_reg_zero_a`: `mldsa_mul_res_reg` captures the full 46-bit product when `!mlkem`; it is zero when `mlkem`.
- `mlkem_mul_reduced_range_a`: The MLKEM Barrett output `mlkem_mul_res_reduced` is always in `[0, 3329)`.
- `mldsa_mul_reduced_comb_range_a`: The MLDSA combinational Barrett output `mldsa_mul_res_reduced_comb` is always in `[0, 8 380 417)`.
- `mlkem_mul_res_reduced_reg_a`: `mlkem_mul_res_reduced_reg` registers the MLKEM Barrett output when `mlkem`.
- `mldsa_mul_res_reduced_reg_a`: `mldsa_mul_res_reduced` registers the MLDSA combinational Barrett output when `!mlkem`.
- `mul_res_to_u_o_ct_mlkem_a` / `mul_res_to_u_o_ct_mldsa_a`: In CT mode, `u_o` equals the modular sum of `u_reg_d2` and the registered Barrett-reduced multiplication result for the respective prime.

### Whitebox — Adder / Subtracter (`fv_ntt_butterfly_m.sv`)

- `add_res_correct_a`: `add_res` equals `(add_opa + add_opb) % Q`, where Q is the active prime. Holds for all modes because the adder inputs are always driven to the correct mode-specific values.
- `sub_res_correct_a`: `sub_res` equals `(u_reg_d2 − reduced_mul_result) % Q` for both primes.
- `add_Res_range_a`: In MLKEM mode, `add_res` is always in `[0, 3329)`.
- `u_minus_v_range_a`: `u_minus_v` is always in `[0, 8 380 417)`.
- `u_minus_v_correct_mlkem_a`: In MLKEM mode, `u_minus_v` equals `(opu_i − opv_i) % 3329`.

### Output Range Checks (`fv_ntt_butterfly_m.sv`)

Each primary output is bounded to `[0, Q)` for the active prime:

- `u_o_range_mlkem_a` / `u_o_range_mldsa_a`
- `v_o_range_mlkem_a` / `v_o_range_mldsa_a`
- `pwm_res_o_range_mlkem_a` / `pwm_res_o_range_mldsa_a`
- `pairwm_mul_red_o_range_mlkem_a`

### Whitebox — MLDSA Barrett Reduction (`fv_ntt_butterfly_m.sv`)

Step-by-step verification of `mldsa_mul_redux_inst_0` (REG_SIZE=23, prime=8 380 417, K=46, m=8 396 807):

- `mldsa_mult_full_a`: `mult_full = mldsa_mul_res_reg × 8 396 807`
- `mldsa_u_est_a`: `u_est = mult_full >> 46`
- `mldsa_u_prime_a`: `u_prime = u_est × 8 380 417`
- `mldsa_r_est_a`: `r_est = {0, x} − u_prime`
- `mldsa_r_sub_prime_a`: `r_sub_prime = r_est − 8 380 417`
- `mldsa_u_plus_one_a`: `u_plus_one = u_est + 1`
- `mldsa_additional_red_a`: `additional_red = (r_est >= 8 380 417)`
- `mldsa_reduced_comb_mux_a`: `mldsa_mul_res_reduced_comb = additional_red ? r_sub_prime[22:0] : r_est[22:0]`

### Whitebox — MLKEM Barrett Reduction (`fv_ntt_butterfly_m.sv`)

Step-by-step verification of `mlkem_mul_redux_inst_0` (REG_SIZE=12, prime=3 329, K=24, m=5 039):

- `mlkem_mult_full_a`: `mult_full = (mlkem ? mul_res_reg : 0) × 5039`
- `mlkem_u_est_a`: `u_est = mult_full >> 24`
- `mlkem_u_prime_a`: `u_prime = u_est × 3329`
- `mlkem_r_est_a`: `r_est = {0, x} − u_prime`
- `mlkem_r_sub_prime_a`: `r_sub_prime = r_est − 3329`
- `mlkem_u_plus_one_a`: `u_plus_one = u_est + 1`
- `mlkem_additional_red_a`: `additional_red = (r_est >= 3329)`
- `mlkem_reduced_mux_a`: `mlkem_mul_res_reduced = additional_red ? r_sub_prime[11:0] : r_est[11:0]`

### Connectivity Assertions (`fv_ntt_butterfly_conn_m.sv`)

A dedicated module `fv_ntt_butterfly_conn_m` verifies internal mux and pipeline routing, independent of functional correctness.

**Group 1 — Input pipeline register connectivity**

- `conn_u_reg_a`: `u_reg` captures `opu_i` each rising edge.
- `conn_u_reg_d2_a`: `u_reg_d2` is one cycle behind `u_reg`.
- `conn_w_reg_a`: `w_reg` captures `opw_i` each rising edge.
- `conn_w_reg_d2_a`: `w_reg_d2` is one cycle behind `w_reg`.
- `conn_add_res_d1_a`: `add_res_d1` captures `add_res` each rising edge.
- `conn_add_res_d2_a`: `add_res_d2` is two cycles behind `add_res`.

**Group 2 — Multiplier input mux connectivity**

- `conn_mul_ct_a`: CT mode — `mul_opa=opv_i`, `mul_opb=opw_i`.
- `conn_mul_opb_gs_a`: GS mode — `mul_opb=w_reg` (one-cycle delayed `opw_i`).
- `conn_mul_opa_gs_mldsa_a`: GS MLDSA — `mul_opa = div2(u_minus_v)`.
- `conn_mul_opa_gs_mlkem_a`: GS MLKEM — `mul_opa = div2_12bit(u_minus_v)`.
- `conn_mul_pwm_a`: PWM mode — `mul_opa=opu_i`, `mul_opb=opv_i`.
- `conn_mul_pairwm_mlkem_a`: PAIRWM MLKEM — `mul_opa=opu_i`, `mul_opb=opv_i`.

**Group 3 — Adder input mux connectivity**

- `conn_add_ct_mlkem_a`: CT MLKEM — `add_opa=u_reg_d2`, `add_opb=mlkem_mul_res_reduced_reg`.
- `conn_add_ct_mldsa_a`: CT MLDSA — `add_opa=u_reg_d2`, `add_opb=mldsa_mul_res_reduced`.
- `conn_add_gs_a`: GS — `add_opa=opu_i`, `add_opb=opv_i`.
- `conn_add_pwm_mlkem_a`: PWM MLKEM — adder inputs forced to zero (result routes via PAIRWM path).
- `conn_add_pwm_mldsa_a`: PWM MLDSA — `add_opa=w_reg_d2`, `add_opb=mldsa_mul_res_reduced`.
- `conn_add_pwa_a`: PWA — `add_opa=opu_i`, `add_opb=opv_i`.

**Group 4 — Output mux connectivity**

- `conn_u_o_ct_a`: CT — `u_o` wired directly to `add_res`.
- `conn_v_o_ct_a`: CT — `v_o` wired directly to `sub_res`.
- `conn_u_o_gs_mldsa_a` / `conn_u_o_gs_mlkem_a`: GS — `u_o` driven by `div2(add_res_d2)` for the active prime.
- `conn_v_o_gs_mldsa_a` / `conn_v_o_gs_mlkem_a`: GS — `v_o` driven by the registered Barrett-reduced product for the active prime.
- `conn_pwm_res_o_pwm_mldsa_acc_a`: PWM MLDSA accumulate — `pwm_res_o=add_res`.
- `conn_pwm_res_o_pwm_mldsa_nacc_a`: PWM MLDSA non-accumulate — `pwm_res_o=mldsa_mul_res_reduced`.
- `conn_pwm_res_o_pwa_a`: PWA — `pwm_res_o=add_res` (= `(opu_i + opv_i) % Q`).
- `conn_pwm_res_o_pws_a`: PWS — `pwm_res_o=u_minus_v` (= `(opu_i − opv_i) % Q`).
- `conn_pairwm_mul_red_o_mlkem_a`: PAIRWM MLKEM — `pairwm_mul_red_o` carries the MLKEM Barrett-reduced product from `mlkem_mul_res_reduced_reg`.

## Reproduce Results
The AIP has been tested and proven with atleast one of these formals tools (Onespin ,Jasper , vcf).

To reproduce the results:
Load the AIP with all the necessary constraints together in your formal tool.

Feel free to reach out to contact@lubis-eda.com to request the loadscripts or the lubis modules.
