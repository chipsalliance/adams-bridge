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

# abr_sha3 - properties

## Files
This directory contains the Assertion IP files of the abr_sha3 bench:
- fv_abr_sha3_m.sv: FSM assertions (reset, state transitions, liveness, one-hot state check).
- fv_abr_sha3_binding.sv: Wrapper that maps the DUT signals onto the FSM assertions and binds it
  to `abr_sha3`.
- fv_abr_sha3_whitebox.sv: White-box assertions for the sub-block connections, the digest output
  guard and the error outputs.
- fv_abr_sha3_constraints.sv: Environment constraints that only allow valid input stimuli.
- fv_abr_sha3_pkg.sv: The `eState` type used by the FSM assertions.
- fv_abr_sha3_incr_counter_m.sv: Local copy of the incrementing counter helper (the constraints
  instantiate the LUBIS library module lubis_incr_counter_m instead; contact
  contact@lubis-eda.com to obtain it).
- fv_abr_sha3_cov_waivers.tcl: Coverage waivers for the u_pad and u_keccak sub-blocks, sourced after
  elaboration.
- waiver_list_done_i_disabled.tcl: GUI-exported waiver list from an earlier RTL version (not
  needed for the current RTL).

## Reproduce Results
The AIP has been tested and proven with atleast one of these formals tools (Onespin ,Jasper , vcf).

To reproduce the results:
Load the AIP with all the necessary constraints together in your formal tool.

Feel free to reach out to contact@lubis-eda.com to request the loadscripts or the lubis modules.
