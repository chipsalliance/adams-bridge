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

# ntt_ctrl - Formal Verification

## Folder Structure
The directory **formal/fv_ntt_ctrl** groups the AIPs for the **ntt_ctrl** module. Each mode of
operation has its own AIP in a sub-directory, with its own README:

- `fv_ntt_ctrl_ct_mldsa/`: CT (forward NTT) mode, ML-DSA
- `fv_ntt_ctrl_ct_mlkem/`: CT (forward NTT) mode, ML-KEM
- `fv_ntt_ctrl_gs_mldsa/`: GS (inverse NTT) mode, ML-DSA
- `fv_ntt_ctrl_gs_mlkem/`: GS (inverse NTT) mode, ML-KEM

The point-wise operation modes (PWM, PWA, PWS, PAIRWM) are verified by the separate AIP in
**formal/fv_ntt_ctrl_pwo**.

Each sub-directory contains the generated AIP (`fv_ntt_ctrl_<mode>_m.sv`), its package
(`_pkg.sv`), functions (`_functions.sv`), binding (`_binding.sv`), constraints (`_constraints.sv`),
additional hand-written assertions (`_additional_aips.sv`) and the SystemC model
(`model/ntt_ctrl_<mode>.h`).

The AIPs share package and type names, so load one sub-directory at a time.

## DUT Overview
The ntt_ctrl is the main control module for the ML-DSA/ML-KEM NTT operation. It receives control
signals from ntt_top, the ready signal from the hybrid butterfly module and valid signals from the
sampler and buffer modules. Depending on the mode of operation (CT, GS, PWM, PWA, PWS, PAIRWM), it
produces the read/write enables and computes the memory and twiddle addresses. See the
sub-directory READMEs for the port list and the per-mode details.

## Assertion IP Overview
Each AIP is bound to `ntt_ctrl`, with reset bound to `reset_n && !zeroize`. The assertions of each
mode are listed in the README of its sub-directory.

## Reproduce Results
The AIP has been tested and proven with atleast one of these formals tools (Onespin ,Jasper , vcf).

To reproduce the results:
Load the AIP with all the necessary constraints together in your formal tool.

Feel free to reach out to contact@lubis-eda.com to request the loadscripts or the lubis modules.
