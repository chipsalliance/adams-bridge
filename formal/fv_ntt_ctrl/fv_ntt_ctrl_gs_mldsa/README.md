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

# ntt_ctrl -- GS mode, ML-DSA

This unit verifies the GS-mode (Gentleman-Sande, inverse-NTT) control logic of the `ntt_ctrl` block for the ML-DSA algorithm (`mlkem == 0`). The properties are generated from a SystemC-PPA reference model of the read and write FSMs; see `ntt_ctrl_gs_mlkem` for the ML-KEM counterpart, which shares the same FSM and addressing structure.

Compared to the previous release, all masking-mode support has been removed from the GS-mode datapath: the write-buffer pointer and twiddle-offset pipelines used to have separate masked/unmasked depths (`MASKED_INTT_WRBUF_LATENCY` vs `INTT_WRBUF_LATENCY`), and `opcode` had a GS-specific process to sync with the masking pipeline. These are now a single unconditional path, with pipeline depth driven by a new `SRAM_LATENCY` parameter instead. Read/write FSM states, address generation, and twiddle logic are otherwise unchanged.

## Folder Structure

| File | Role |
|---|---|
| `model/ntt_ctrl_gs_mldsa.h` | SystemC-PPA reference model (read and write FSMs as separate threads) |
| `fv_ntt_ctrl_gs_mldsa_m.sv` | Generated AIP: FSM reset, transition, and liveness properties |
| `fv_ntt_ctrl_gs_mldsa_binding.sv` | Binds the AIP and its register/state probes to the DUT |
| `fv_ntt_ctrl_gs_mldsa_pkg.sv` | Shared types (`e_GsReadStatesType`, `e_GsWriteStatesType`, `st_NttBaseAddrs`, ...) and constants |
| `fv_ntt_ctrl_gs_mldsa_functions.sv` | Generated package with the model's functions |
| `fv_ntt_ctrl_gs_mldsa_constraints.sv` | `assume` properties constraining the DUT inputs |
| `fv_ntt_ctrl_gs_mldsa_additional_aips.sv` | Hand-written `assert` properties for output muxes, buffer/address checks, and busy/done/rounds tracking |

## DUT Overview

The DUT `ntt_ctrl` in GS mode manages read and write sequencing, buffer usage, and address/twiddle generation for the Gentleman-Sande (inverse) NTT variant, fixed to `ntt_mode == gs` and `mlkem == 0` for this unit.

Read FSM (`GsReadIdle`, `GsReadStage`, `GsReadExec`): Idle -> Stage on `ntt_enable`; Stage -> Idle once `rounds_count == NTT_NUM_ROUNDS` (4), or -> Exec once the write FSM reaches `GsWriteStage` with `!intt_done`; Exec -> Stage once `rd_valid_count == VALID_COUNT-1` (63). The RTL's read-FSM enum has two further states, `RD_BUF` and `EXEC_WAIT`, but GS mode structurally never reaches them, so the model only needs the three states above.

Write FSM (`GsWriteIdle`, `GsWriteStage`, `GsWriteBuf`, `GsWriteMem`, `GsWriteWait`): Idle -> Stage on `ntt_enable`; Stage -> Idle once `rounds_count == NTT_NUM_ROUNDS`, else -> Buf; Buf -> Mem once `buf0_valid`; Mem -> Buf if `!buf0_valid && buf_count == 0 && wr_valid_count < VALID_COUNT` (64), or -> Wait once `buf0_valid && wr_valid_count == VALID_COUNT-4` (60); Wait -> Stage once `buf_count == COEFF_PER_CLK-1` (3).

Key parameters: `BF_LATENCY` (6), `SRAM_LATENCY` (1), `NTT_NUM_ROUNDS` (4), `VALID_COUNT` (64), `COEFF_PER_CLK` (4).

| Port(s) | Dir | Description |
|---|---|---|
| `clk`, `reset_n`, `zeroize` | in | Clock, active-low reset, secure clear (both treated as reset) |
| `ntt_mode`, `mlkem` | in | Mode/algorithm select; assumed `gs` and `0` respectively |
| `ntt_enable` | in | Starts the read/write FSMs |
| `shuffle_en`, `random` | in | Enables and seeds address/index/twiddle shuffling |
| `ntt_mem_base_addr` | in | Src/interim/dest base-address struct |
| `buf0_valid` | in | Write-buffer slot-0 valid, gates the Buf/Mem/Wait arcs |
| `butterfly_ready` | in | `bf_enable` delayed `BF_LATENCY` cycles |
| `mem_rd_data_valid` | in | `mem_rd_en` delayed `SRAM_LATENCY` cycles |
| `sampler_valid`, `accumulate`, `pwo_mem_base_addr` | in | PWO-path inputs, unconstrained by this unit's mode (`pw_rden`/`pw_wren` proven 0) |
| `bf_enable`, `opcode` | out | Butterfly enable and opcode (fixed to `gs`) |
| `buf_wren`, `buf_rden`, `buf_wrptr`, `buf_rdptr` | out | Write-buffer enables and pointers |
| `mem_rd_en`/`mem_rd_addr`, `mem_wr_en`/`mem_wr_addr` | out | Memory read/write request and address |
| `twiddle_addr` | out | Twiddle-factor address |
| `buf_wr_rst_count`, `buf_rd_rst_count` | out | Buffer reset-count strobes |
| `intt_passthrough`, `ntt_passthrough` | out | ML-KEM-only round-skip flag; both proven constant 0 here (`mlkem == 0`) |
| `busy`, `done` | out | Operation ongoing / all rounds complete |
| `pw_rden`, `pw_wren`, `pw_rden_dest_mem`, `pw_mem_rd_addr_{a,b,c}`, `pw_mem_wr_addr_c` | out | Pointwise-mult signals, proven constant 0/unused in GS mode |

## Assertion IP

The generated AIP `fv_ntt_ctrl_gs_mldsa_m.sv` binds with reset condition `!reset_n || zeroize` and contains:
- Structural reset properties (`read_reset_p`, `write_reset_p`)
- One property per legal FSM transition arc, e.g. `read_read_stage_to_read_exec_p`, `write_write_wait_to_write_stage_p`
- Per-state liveness properties ensuring no permanent stalls, e.g. `read_read_stage_eventually_left_p`, `write_write_buf_eventually_left_p`

The `write_write_mem_to_write_buf_a` witness cover is disabled in the proof scripts, since that arc requires `!buf0_valid && buf_count == 0` at the same cycle, and `assume_buf0_valid`/`assume_no_buf0_valid` tie `buf0_valid`'s periodic reassertion to exactly the cycle `buf_count` resets to 0 -- so the two conditions never coincide. The assert itself is left enabled and proves vacuously, since its antecedent is unreachable under these (correct) constraints.

## Additional AIPs

`fv_ntt_ctrl_gs_mldsa_additional_aips.sv` closes the DUT-output gaps the model leaves open: `assert_bf_enable_a` (shuffle/non-shuffle output mux), `assert_buf_wren_a`/`assert_buf_wren_intt_reg_a` (write-buffer enable and its registered form), `assert_buf_wr_ptr_check_a` (in-order pointer increment when not shuffling), `assert_twiddle_addr_a` (twiddle-address output mux across shuffle settings and per-round offsets), `assert_buf_rd_en_a`/`assert_buf_rdptr_a` (read-side buffer enable and pointer, which follows `buf_count` since GS reads have no input buffer), `assert_buf_wr_rst_count_a`/`assert_buf_rd_rst_count_a` (buffer reset-count strobes), `assert_mem_rd_en_a`/`assert_mem_wr_en_a` (memory enable output muxes), `assert_not_same_address_a` (no simultaneous same-address read/write), `assert_busy_a`/`assert_rst_rounds_a`/`assert_intt_done_a` (busy/rounds-reset/done tracking), `assert_latch_index_rand_offset_a`/`assert_latch_chunk_rand_offset_a` (random-offset latch timing), and `assert_mem_rd_base_addr_a` (read base-address rotation across rounds: src -> interim -> dest).

## Constraints

`fv_ntt_ctrl_gs_mldsa_constraints.sv` assumes:
- `assume_gs_mode_only` / `assume_gs_mldsa_only` -- pin `ntt_mode == gs` and `mlkem == 0`
- `assume_butterfly_ready` / `assume_mem_rd_data_valid` -- model `butterfly_ready` and `mem_rd_data_valid` as `bf_enable`/`mem_rd_en` delayed by `BF_LATENCY`/`SRAM_LATENCY` cycles
- `assume_valid_base_address` -- src/interim/dest base addresses are pairwise >=64 apart (except dest may equal src) and each <= `2**ABR_MEM_ADDR_WIDTH - 64`
- `assume_stable_base_address` / `assume_stable_mode` / `assume_stable_shuffle_en` -- hold these stable once an operation is in flight
- `assume_buf0_valid` / `assume_no_buf0_valid` -- `buf0_valid` asserted exactly on the 4th cycle of each write-buffer fill sequence
- `assume_ntt_enable` -- liveness: `ntt_enable` is eventually asserted

## Reproduce Results
The AIP has been tested and proven with atleast one of these formals tools (Onespin ,Jasper , vcf).

To reproduce the results:
Load the AIP with all the necessary constraints together in your formal tool.

Feel free to reach out to contact@lubis-eda.com to request the loadscripts or the lubis modules.
