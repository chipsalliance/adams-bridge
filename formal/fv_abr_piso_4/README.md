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

# abr_piso_4 - Formal Verification

Date: 26.03.2025
Author: LUBIS EDA GmbH

## Folder Structure

The following files are part of the main directory **formal/fv_abr_piso_4**

- `fv_abr_piso_4.sv`: Main assertion IP with hold, valid, and data integrity checks
- `fv_abr_piso_4_top.sv`: Top-level wrapper instantiating the AIP, constraints, and handshake protocol checkers
- `fv_abr_piso_4_constraints.sv`: Environment constraints restricting input stimuli to valid scenarios

## DUT Overview

The DUT `abr_piso_4` is a Parallel-In Serial-Out (PISO) buffer supporting 4 configurable modes with different input and output rates. It is used in the MLDSA sampler pipeline for data rate conversion between wide parallel input data and narrow serial output data. Reset is bound to `(!abr_piso_4.rst_b || abr_piso_4.zeroize)`.

| S.No | Port        | Direction | Description                                                             |
| ---- | ----------- | --------- | ----------------------------------------------------------------------- |
| 1    | clk         | input     | Clock signal                                                            |
| 2    | rst_b       | input     | Active-low reset                                                        |
| 3    | zeroize     | input     | Secure clear — resets all buffer state                                  |
| 4    | mode        | input     | 2-bit mode select (0–3), determines active input/output rate pair       |
| 5    | valid_i     | input     | Input valid — data on data_i is valid and ready to be pushed            |
| 6    | hold_o      | output    | Input hold — asserted when buffer cannot accept the current input_rate  |
| 7    | data_i      | input     | Parallel input data (`PISO_ACT_INPUT_RATE` bits wide)                   |
| 8    | valid_o     | output    | Output valid — buffer holds at least `output_rate` bits                 |
| 9    | hold_i      | input     | Output hold from downstream — suppresses pop when asserted              |
| 10   | data_o      | output    | Serial output data (`PISO_ACT_OUTPUT_RATE` bits wide)                   |

Mode selects one of four input/output rate pairs parameterized by `PISO_INPUT_RATE{0-3}` / `PISO_OUTPUT_RATE{0-3}`. The buffer width is `PISO_BUFFER_W` (default 1344 bits). Push occurs when `valid_i && !hold_o`; pop occurs when `valid_o && !hold_i`.

## Assertion IP Overview

### Constraints (`fv_abr_piso_4_constraints.sv`)

- **assume_stable_mode**: Mode input remains stable throughout the proof (mode changes mid-operation are not in scope).
- **assume_sym_beat_select** / **assume_stable_sym_beat_select**: A symbolic beat-select variable used to track one specific output beat is constrained to a valid range and held stable after sampling, enabling the scoreboard to track a single output transaction end-to-end.

### Hold Output Assertion

- **assert_hold_o**: When `valid_i` is asserted, `hold_o` must equal `((PISO_BUFFER_W - num_bits_in_buffer) < input_rate)` — i.e., hold is asserted exactly when the remaining buffer capacity cannot accommodate the current input rate.

### Valid Output Assertions

- **assert_valid_o**: `valid_o` is asserted whenever `num_bits_in_buffer >= output_rate`, meaning the buffer holds enough bits for a full output word.
- **assert_not_valid_o**: `valid_o` is deasserted whenever `num_bits_in_buffer < output_rate`.
- **assert_liveness_valid_o**: If the buffer is non-empty (`num_bits_in_buffer > 0`), then `valid_o` is eventually asserted — ensures no data permanently stalls in the buffer.

### Data Integrity (Scoreboard)

The main AIP instantiates `lubis_scoreboard_unroll_ext_m`, a word-unrolling scoreboard that tracks the expected output bits against observed `data_o` for the symbolically selected beat. It pushes on `valid_i && !hold_o` and pops on `valid_o && !hold_i`, verifying that the PISO serialization produces the correct bit subsequence for the tracked beat.

### Handshake Protocol Checkers (`fv_abr_piso_4_top.sv`)

Two instances of `lubis_vld_rdy_hsk_aip` verify the input and output handshake contracts:

- **destination_valid_i_hold_o**: Constrains `valid_i` as a destination-side signal and asserts that `hold_o` is eventually deasserted when `valid_i` is high — no indefinite backpressure on the input.
- **source_valid_o_hold_i**: Constrains `hold_i` as a source-side signal and asserts that `valid_o` behavior conforms to the handshaking protocol — data remains stable across hold cycles and `valid_o` is eventually cleared after acceptance.

## Reproduce Results

The AIP has been tested and proven with atleast one of these formals tools (Onespin ,Jasper , vcf) and formal coverage is at 100% excluding valid unreachable and deadcode. 

To reproduce the results:
Load the AIP with all the necessary constraints together in your formal tool. 

Feel free to reach out to contact@lubis-eda.com to request the loadscripts or the lubis modules.
