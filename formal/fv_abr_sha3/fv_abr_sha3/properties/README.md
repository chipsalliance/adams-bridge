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

# abr_sha3
Date: 26.03.2025
Author: LUBIS EDA GmbH

## Folder Structure
The provided Assertion IP consists of the following files:
- fv_abr_sha3.h: A systemC model that models the behavior of abr_sha3 to be used for simulation and formal properties generation.
- abr_sha3.luref: A LUBIS refinement file that is used to bind the set of generated properties to the Design Under Test (DUT).
- waiver_list_done_i_disabled.tcl: Contains a set of waived signals and registers from formal coverage results that are either out of scope or cannot be covered due to design's limitations.
- properties/fv_abr_sha3_binding.sv: Contains the required binding statement, to bind the DUT to the Assertion IP.
- properties/fv_abr_sha3_constraints.sv: Contains a set of enivronment constraints to only allow valid input stimuli.
- properties/fv_abr_sha3_pkg.sv: Contains the definition of any necessary user defined structs and types.
- properties/fv_abr_sha3.sv: Contains a set of properties that verifies the core functionality of the design, specifically the FSM in this design.
- properties/fv_abr_sha3_whitebox.sv: Contains a set of properties that verifies parts of the internals to ensure correct interaction between the top design and the sub-blocks.

## Reproduce Results

The AIP has been tested and proven with atleast one of these formals tools (Onespin ,Jasper , vcf) and formal coverage is at 100 0.000000e+00xcluding valid unreachable and deadcode. 

To reproduce the results:
Load the AIP with all the necessary constraints together in your formal tool. 

Feel free to reach out to contact@lubis-eda.com to request the loadscripts or the lubis modules.
