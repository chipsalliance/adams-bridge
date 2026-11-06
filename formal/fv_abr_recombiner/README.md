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

# abr_recombiner - Formal Verification

## Folder Structure
The following files are part of the main directory **formal/fv_abr_recombiner**
- `fv_abr_recombiner_wrapper.sv`: Wrapper around the combinational `abr_recombiner` that adds the clock and reset pins for the formal tool.
- `fv_abr_recombiner_constraints.sv`: Input contract: every share coefficient is pre-reduced to [0, q-1] for the selected mode.
- `fv_abr_recombiner_top.sv`: Unit-level assertions on `abr_recombiner` and the `bind` to the wrapper.

## DUT Overview
`abr_recombiner` is the arithmetic counterpart of `abr_splitter`. It recombines two arithmetic shares of a 96-bit memory word (4 coefficients of 23 bits in 24-bit slots) into the unmasked word:
`data_o = (share0_i + share1_i) mod q` per coefficient, with q = MLDSA_Q (8380417) for `mode = 0` and q = MLKEM_Q (3329) for `mode = 1`. The module is purely combinational; bit 23 of each input slot is ignored and bit 23 of each output slot is zero.

| S.No | Port | Direction | Description |
| ---- | ---- | --------- | ----------- |
| 1 | mode | input | 0 = MLDSA modulus, 1 = MLKEM modulus |
| 2 | share0_i[95:0] | input | Share 0 of the memory word |
| 3 | share1_i[95:0] | input | Share 1 of the memory word |
| 4 | data_o[95:0] | output | Recombined memory word |

## Assertion IP Overview
The AIP (`fv_abr_recombiner_top`) is bound to `fv_abr_recombiner_wrapper`. Assertions end in `_a`, covers in `_c`.

Assertions (per coefficient lane where applicable):
- assert_data_mod_q_a: Checks that each recombined coefficient equals `(share0 + share1) mod q`, computed with the `%` operator independently of the RTL structure.
- assert_data_lt_q_a: Checks that each recombined coefficient is below q.
- assert_data_msb_zero_a: Checks that bit 23 of each output slot is zero.
- assert_zero_shares_zero_data_a: Checks that all-zero shares recombine to an all-zero word.
- cover_lane_[no_]wrap_{mldsa,mlkem}_c: Both branches of the modular reduction are reachable in both modes.

Assumptions:
- assume_share0_lt_q / assume_share1_lt_q: share coefficients are below q.

## Reproduce Results
The AIP has been tested and proven with atleast one of these formals tools (Onespin ,Jasper , vcf).

To reproduce the results:
Load the AIP with all the necessary constraints together in your formal tool.

Feel free to reach out to contact@lubis-eda.com to request the loadscripts or the lubis modules.
