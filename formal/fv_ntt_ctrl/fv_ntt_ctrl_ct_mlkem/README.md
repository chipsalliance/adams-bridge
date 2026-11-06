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

# ntt_ctrl -- CT mode, ML-KEM

Formal verification of the `ntt_ctrl` block in forward NTT (CT) mode with `mlkem == 1` (ML-KEM). The AIP is generated from a SystemC-PPA reference model; a sibling unit (`../ntt_ctrl_ct_mldsa`) covers the same block for ML-DSA.

In CT mode the two algorithms (ML-DSA and ML-KEM) share the same control flow and addressing. The main difference is that ML-KEM bypasses one butterfly stage by asserting `ntt_passthrough` during the last round.

Compared to the previous release, the masking interface was removed (masking is performed architecturally now), memory reads are qualified by the new `mem_rd_data_valid` input, and several latencies and register widths changed.

## Folder Structure

| File | Role |
|------|------|
| `model/ntt_ctrl_ct_mlkem.h` | SystemC-PPA reference model (read and write FSMs as separate threads) |
| `fv_ntt_ctrl_ct_mlkem_m.sv` | Generated AIP: FSM operation assertions |
| `fv_ntt_ctrl_ct_mlkem_functions.sv` | Generated package with the model's functions |
| `fv_ntt_ctrl_ct_mlkem_pkg.sv` | Generated package with model state enums and struct types |
| `fv_ntt_ctrl_ct_mlkem_binding.sv` | Wrapper binding the generated AIP to `ntt_ctrl` internals |
| `fv_ntt_ctrl_ct_mlkem_additional_aips.sv` | Hand-written additional assertions not covered by the model |
| `fv_ntt_ctrl_ct_mlkem_constraints.sv` | `assume` properties constraining the DUT inputs |

## DUT Overview

`ntt_ctrl` generates buffer, twiddle, and memory read/write addressing for the NTT butterfly datapath. It consists of two FSMs: a read FSM (`RD_IDLE`, `RD_STAGE`, `RD_BUF`, `RD_EXEC`, `EXEC_WAIT`) and a write FSM (`WR_IDLE`, `WR_STAGE`, `WR_MEM`). A full NTT takes `NTT_NUM_ROUNDS = 4` rounds of 64 valid reads/writes, alternating between source/interim/destination base addresses.

Ports used by this environment:

| Port | Dir | Description |
|------|-----|-------------|
| clk, reset_n, zeroize | in | Clock, active-low reset, synchronous clear (both treated as reset) |
| ntt_mode | in | Mode select; constrained to `ct` |
| mlkem | in | Algorithm select; constrained to 1 (ML-KEM) |
| ntt_enable | in | Starts an NTT operation |
| butterfly_ready | in | Butterfly-done indication; constrained to `bf_enable` delayed by `BF_LATENCY` |
| mem_rd_data_valid | in | Memory read-data valid; constrained to `mem_rd_en` delayed by `SRAM_LATENCY` |
| buf0_valid | in | Buffer-valid handshake; constrained to fire on every 4th buffer write |
| ntt_mem_base_addr | in | Source/interim/destination base addresses |
| shuffle_en | in | Enables address shuffling (masking countermeasure) |
| random | in | Random value for the shuffled chunk/index offsets |
| sampler_valid, accumulate, pwo_mem_base_addr | in | Unused in CT mode |
| bf_enable, opcode | out | Butterfly enable and opcode (always `ct`) |
| buf_wren, buf_rden, buf_wrptr, buf_rdptr | out | Input-buffer write/read control |
| buf_wr_rst_count, buf_rd_rst_count | out | Buffer pointer-reset controls |
| twiddle_addr | out | Twiddle address |
| mem_rd_addr, mem_wr_addr, mem_rd_en, mem_wr_en | out | Memory interface (shuffled when `shuffle_en`) |
| pw_mem_rd_addr_a/b/c, pw_mem_wr_addr_c, pw_rden, pw_wren | out | Pointwise interface, inactive in CT mode |
| ntt_passthrough, intt_passthrough | out | ML-KEM passthrough controls (forward / inverse NTT) |
| busy, done | out | Operation ongoing / completed |

## Assertion IP

The generated AIP (`fv_ntt_ctrl_ct_mlkem_m.sv`) proves the two FSMs against the reference model, with reset defined as `!reset_n || zeroize`:

- `read_reset_a` / `write_reset_a`: registers and outputs take their initial values on reset.
- `read_<from>_to_<to>_a` / `write_<from>_to_<to>_a`: one assertion per FSM transition (including self-loops), checking both the transition condition and the register/output updates.
- `*_eventually_left_a`: liveness assertions -- every state is eventually left (supported by the `s_eventually(ntt_enable)` assumption).

## Additional AIPs

`fv_ntt_ctrl_ct_mlkem_additional_aips.sv` covers combinational/registered outputs not tied to a single FSM operation, e.g. `bf_enable`, `buf_wren`/`buf_rden` and pointer ordering, `twiddle_addr`, buffer-count reset controls, `mem_rd_en`/`mem_wr_en` (shuffled and non-shuffled), read/write base-address selection per round, `busy`, `ntt_done`, the random-offset latch conditions, and that simultaneous memory read/write never target the same address. ML-KEM specific: `ntt_passthrough` is asserted exactly in the last round (`rounds_count == NTT_NUM_ROUNDS - 1`), and `intt_passthrough` stays 0 (GS-only).

## Constraints

`fv_ntt_ctrl_ct_mlkem_constraints.sv` assumes:

- `ntt_mode == ct` and `mlkem == 1`, both stable while an operation is executing.
- `butterfly_ready` and `mem_rd_data_valid` modeled as delayed feedback of `bf_enable` and `mem_rd_en` (`BF_LATENCY`, `SRAM_LATENCY = 1`).
- `buf0_valid` asserted exactly on every 4th buffer write.
- Base addresses stable, 64-aligned relative to each other (source may equal destination; interim disjoint from both), and within the memory range.
- `shuffle_en` stable during operation; `s_eventually(ntt_enable)` for liveness.

## Reproduce Results
The AIP has been tested and proven with atleast one of these formals tools (Onespin ,Jasper , vcf).

To reproduce the results:
Load the AIP with all the necessary constraints together in your formal tool.

Feel free to reach out to contact@lubis-eda.com to request the loadscripts or the lubis modules.
