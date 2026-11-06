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

# abr_splitter

## Folder Structure
The formal project has individual verification benches for different modules. These are listed under the toplevel directory named **formal**. Under this directory, we have a directory named **fv_abr_splitter**

The **formal/fv_abr_splitter** contains the top level verification assertion IP named as **fv_abr_splitter_top.sv** where the properties are written, and the constraints are written in **fv_abr_splitter_constraints.sv**. The end-to-end data-integrity check uses the LUBIS scoreboard AIP (`lubis_scoreboard`), which is not part of this repository; contact contact@lubis-eda.com to obtain it.


## DUT Overview

The DUT abr_splitter has the primary inputs and primary outputs as shown below.

| S.No | Port      | Direction | Description                                                                        |
| ---- | --------- | --------- | -----------------------------------------------------------------------------------|
| 1    | clk       | input     | The positive edge of the clk is used for all the signals                           |
| 2    | reset_n   | input     | The reset signal is active low and asynchronous, and resets the core               |
| 3    | zeroize   | input     | The core registers are cleared (secret-wipe) when this signal is triggered         |
| 4    | en_i      | input     | The input valid qualifier — a fresh word on data_i/rand_i is accepted when high    |
| 5    | mode      | input     | Scheme select: 0 = ML-DSA (q = 8380417, 23-bit), 1 = ML-KEM (q = 3329, 12-bit)     |
| 6    | data_i    | input     | The 96-bit input word holding 4 secret coefficients (24-bit slots) to be split     |
| 7    | rand_i    | input     | The 96-bit randomness from the external LFSR (4 random values)                     |
| 8    | share0_o  | output    | Share 0 — the reduced random value r, packed as 4 coefficients                     |
| 9    | share1_o  | output    | Share 1 — (data − r) mod q, packed as 4 coefficients                               |
| 10   | ready_o   | output    | The output valid strobe — high when the shares are stable (2 cycles after en_i)    |

The design implements first-order arithmetic masking (an SCA countermeasure): each secret coefficient `d` is split into two shares such that neither share alone reveals anything about `d`, while their recombination recovers it:

- `share0 = r` — the input randomness reduced into `[0, q)` by one conditional subtraction
- `share1 = (d − r) mod q` — the masked data
- reconstruction identity: `share0 + share1 ≡ d (mod q)`

Four coefficient lanes are processed in parallel per 96-bit word. The datapath is pipelined with a fixed latency from `en_i` to `ready_o`:
- **2 cycles** for both shares (`share1`: 1 cycle in `abr_ntt_add_sub_mod` + 1 output register; `share0`: 2-stage delay of the reduced random), so all output legs align.


## Verification Strategy

**Approach.** The module is verified with a combined **scoreboard end-to-end** and **reference-model** formal strategy. The end-to-end check establishes the functional contract: the `lubis_scoreboard` AIP tracks one symbolic word from push (`en_i`) to pop (`ready_o`) and asserts that the reconstructed output — `(share0 + share1) mod q` per lane, computed in auxiliary bench logic — matches the pushed `data_i` word, together with in-order delivery, no duplication/loss, and bounded forward progression. A forward reference model complements this by pinning each share to the actual input randomness, so a DUT that mangled or ignored `rand_i` (delivering the data effectively unmasked while still reconstructing correctly) is caught.

**Abstraction.** The reconstruction and the reference model use a single conditional subtraction as a complete `mod q` reduction. This is exact because both shares are proven `< q` (so their sum is `< 2q`) and is significantly cheaper for the solver than a modulo operator. The mode-selected prime (`MLDSA_Q` / `MLKEM_Q`) and coefficient widths (23/12 bits within 24-bit slots) are handled per lane.

**Environment models.** The input space is constrained in `fv_abr_splitter_constraints.sv`: each coefficient slot of `data_i` is assumed to be a valid field element (`< q`) for the selected mode, reflecting the guarantee provided by upstream logic, and `mode` is held stable across a transaction since it selects the prime combinationally. `rand_i` is deliberately unconstrained — the DUT reduces it internally.


## Assertion IP Overview

The Assertion IP signals are bound with the respective signals in the DUT. The scoreboard and the assertions inside **fv_abr_splitter_top.sv** perform end-to-end, reference-model, range, reset/zeroize, and input-contract checks for the abr_splitter module.

### fv_abr_splitter_top.sv — Scoreboard end-to-end check

`lubis_scoreboard` instance (`OUTPUT_DATA_WIDTH = 96`, `DEPTH = 4`, `MAX_DELAY = 2`, `BYPASS = 0`), with push = `en_i`, pop = `ready_o`, expected_data = `data_i`, observed_data = the reconstructed word, and rst = `!reset_n || zeroize`.

- assert_data_ordering_and_integrity: The reconstructed output word `(share0 + share1) mod q` matches the `data_i` word captured at push, checked at pop via a symbolic bit index.
- assert_L0_only_pop_after_push … assert_L3_tracking_counter_not_zero_if_data_in: Scoreboard invariants — no pop before push, depth sufficiency, no out-before-in, tracking-counter consistency.
- number_of_elements_validity: Consistency of the configured fill level at push.
- forward_progression_liveness: A tracked word eventually leaves the pipeline (bounded by `MAX_DELAY`).
- cover_sampled_in / cover_sampled_out: Sanity covers — tracking can start and complete.

### fv_abr_splitter_top.sv — Range checks

- assert_abr_splitter_mldsa_output_range: In ML-DSA mode at `ready_o`, both 24-bit output slots are `< MLDSA_Q` (also proves the packed top bit is 0).
- assert_abr_splitter_mlkem_output_range: In ML-KEM mode at `ready_o`, both 24-bit output slots are `< MLKEM_Q` (also proves slot bits [23:12] are 0).
- assert_abr_splitter_rand_reduced_range: The internally reduced random is `< q` for the selected mode. Together these establish the `sum < 2q` precondition of the conditional-subtraction reconstruction.

### fv_abr_splitter_top.sv — Randomness path / reference model

Auxiliary code re-computes the reduction and the split from primary inputs only (no hierarchical references).

- assert_abr_splitter_share0_is_reduced_rand: `share0_o` equals the correctly reduced value of the actual `rand_i`, delayed 2 cycles (unconditional — the RTL delay chain is ungated).
- assert_abr_splitter_share1_is_masked_data: After a qualified push, `share1_o` equals the reference `(data − rand_reduced) mod q` from 2 cycles earlier.

### fv_abr_splitter_top.sv — Reset / zeroize checks

- assert_abr_splitter_reset_clears: One cycle after any reset cycle, both share outputs are 0 and `ready_o` is low.
- assert_abr_splitter_zeroize_clears: One cycle after a zeroize pulse, both share outputs are 0 and `ready_o` is low.
- assert_abr_splitter_reset_clears_regs / assert_abr_splitter_zeroize_clears_regs: Per lane, the same extended to every internal register (`rand_d1/d2`, `share1_coeff_reg`, and the `abr_ntt_add_sub_mod` state) — no register is missed by reset or zeroize.

### fv_abr_splitter_top.sv — Input contract

- assert_abr_splitter_mldsa_data_bit23_zero: Restates the RTL's built-in `MldsaDataBit23Zero_A` input assertion.
- assert_abr_splitter_mlkem_data_upper_zero: Restates the RTL's built-in `MlkemDataUpperZero_A` input assertion. Both are provable from `assume_data_range` and kept as sanity checks that the environment constraint implies the RTL's own input contract.

### fv_abr_splitter_constraints.sv — Constraints

- assume_data_range: Each 24-bit coefficient slot of `data_i` is a valid field element (`< MLKEM_Q` in ML-KEM mode, `< MLDSA_Q` in ML-DSA mode).
- assume_stable_mode: The `mode` select is held stable across a transaction.

Note: `rand_i` carries no constraint — the DUT's internal single conditional subtraction is sufficient for the full LFSR range in both modes.

## Formal Setup
This AIP instantiates the LUBIS library module `lubis_scoreboard`, which is not part of this repository.

## Reproduce Results
The AIP has been tested and proven with atleast one of these formals tools (Onespin ,Jasper , vcf).

To reproduce the results:
Load the AIP with all the necessary constraints together in your formal tool.

Feel free to reach out to contact@lubis-eda.com to request the loadscripts or the lubis modules.
