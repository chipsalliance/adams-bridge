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

# ntt_ctrl - pwo_mode

## Folder Structure
The following files and subdirectories are part of the main directory **formal/fv_ntt_ctrl_pwo**

- `fv_ntt_ctrl_pwo_pkg.sv`: Package definitions — read/write FSM state enums (`pwoReadStatesType`, `pwoWriteStatesType`) and the packed `fv_pwo_mem_addrs_type` (the three PWO base addresses)
- `fv_ntt_ctrl_pwo_functions.sv`: Reference-model helper functions — address/offset arithmetic for the PWO read/write datapaths (chunk/index random-offset derivation, `pw_mem_*_addr` next-value computation, twiddle-address bookkeeping)
- `fv_ntt_ctrl_pwo_constraints.sv`: Assumptions restricting the formal input space to PWO-relevant scenarios
- `fv_ntt_ctrl_pwo_additional_properties.sv`: Hand-written combinational assertions for outputs that depend on both sub-FSMs or on `shuffle_en` (`bf_enable`, `twiddle_addr`, `pw_rden`, `pw_rden_dest_mem`, `pw_wren`, `busy`, `rst_rounds`) — not expressible in the single-threaded reference model below
- `fv_ntt_ctrl_pwo_binding.sv`: Binds the Lubis-generated reference model (`fv_ntt_ctrl_pwo_m`, from `fv_ntt_ctrl_pwo_m.sv`) to the DUT's internal `ntt_ctrl` signals
- `fv_ntt_ctrl_pwo_m.sv`: Lubis-tool-generated `fv_ntt_ctrl_pwo_m` module, auto-derived from `model/ntt_ctrl_pwo.h` — reset, FSM-transition, liveness, and one-hot consistency assertions for the read/write sub-FSMs (regenerate rather than hand-edit)
- `model/`: Source reference model consumed by the Lubis flow to (re)generate `fv_ntt_ctrl_pwo_m.sv`
  - `model/ntt_ctrl_pwo.h`: C++/SystemC-style reference model of the PWO read and write sub-FSMs

## DUT Overview

`fv_ntt_ctrl_pwo` verifies the shared `ntt_ctrl` module while it is driven in one of the point-wise-operation (PWO) modes — PWM (with or without accumulate), PWA, PWS, or PAIRWM (MLKEM only). In these modes `ntt_ctrl` sequences two independent sub-FSMs — a **read FSM** that streams operands out of memory into the butterfly/pairwise-multiply datapath, and a **write FSM** that streams results back — instead of the CT/GS butterfly stage sequencing used in NTT/INTT mode.

| S.No | Port                    | Direction | Description                                                                                     |
| ---- | ----------------------- | --------- | ------------------------------------------------------------------------------------------------|
| 1    | clk                     | input     | Positive edge used for all registers.                                                            |
| 2    | reset_n                 | input     | Active-low synchronous reset.                                                                    |
| 3    | zeroize                 | input     | Secure-clear; combined with `reset_n` in the AIP as `reset_n && !zeroize`.                       |
| 4    | ntt_mode [2:0]          | input     | Mode selector; constrained to PWM/PWA/PWS/PAIRWM for this unit (see `assume_ntt_mode`).          |
| 5    | ntt_enable              | input     | Starts a PWO operation.                                                                          |
| 6    | butterfly_ready         | input     | Pulses when the butterfly/pairwise-multiply datapath has a result ready to be written back.      |
| 7    | buf0_valid              | input     | Shared-buffer valid input; constrained to `0` — not exercised by the PWO datapath.                |
| 8    | sampler_valid           | input     | Valid strobe from the sampler; gates operand read progress during `RD_EXEC`/`EXEC_WAIT`.          |
| 9    | accumulate              | input     | Selects PWM-with-accumulate; also gates `pw_rden_dest_mem` and the write-address stride.          |
| 10   | ntt_mem_base_addr       | input     | Base addresses for the CT/GS memory map; not used by the PWO addressing paths.                    |
| 11   | pwo_mem_base_addr       | input     | `{pw_base_addr_a, pw_base_addr_b, pw_base_addr_c}` — base addresses of the three PWO operand/result memories, each bounded `< 16320`. |
| 12   | shuffle_en              | input     | Enables randomized (shuffled) addressing as a side-channel countermeasure.                       |
| 13   | random [5:0]            | input     | Random bits; split into a 4-bit chunk offset and a 2-bit index offset when `shuffle_en`.          |
| 14   | mlkem                   | input     | Selects MLKEM vs MLDSA; gates PAIRWM legality and several address/twiddle equations.               |
| 15   | bf_enable               | output    | One-cycle enable into the butterfly/pairwise-multiply datapath.                                  |
| 16   | opcode [2:0]            | output    | Forwards `ntt_mode` to the datapath.                                                              |
| 17   | buf_wren / buf_rden     | output    | Shared-buffer write/read enable; tied low in PWO mode.                                            |
| 18   | buf_wrptr / buf_rdptr   | output    | Shared-buffer pointers; reset-only in PWO mode.                                                   |
| 19   | buf_wr_rst_count / buf_rd_rst_count | output | Shared-buffer counter reset strobes.                                                    |
| 20   | twiddle_addr [6:0]      | output    | Twiddle-factor ROM address for the active round.                                                  |
| 21   | mem_rd_addr / mem_wr_addr, mem_rd_en / mem_wr_en | output | Shared main-memory interface; not used by PWO addressing.                       |
| 22   | pw_mem_rd_addr_a/b/c [14:0] | output | Read addresses into the three PWO operand memories.                                            |
| 23   | pw_mem_wr_addr_c [14:0] | output    | Write address into the PWO destination memory.                                                   |
| 24   | pw_rden / pw_wren       | output    | PWO memory read/write enable.                                                                     |
| 25   | pw_rden_dest_mem        | output    | Read-enable for the destination memory, active only when `accumulate`.                            |
| 26   | busy                    | output    | Asserted whenever either sub-FSM is out of its idle state.                                        |
| 27   | done                    | output    | Pulses when the PWO operation (both rounds required by `PWO_NUM_ROUNDS`) completes.                |

### Sub-FSMs

**Read FSM** (`pwoReadStatesType`): `RD_IDLE → RD_STAGE → RD_EXEC ⇄ EXEC_WAIT`, returning to `RD_STAGE`/`RD_IDLE`. Streams `sampler_valid`-gated operands from `pw_mem_rd_addr_a/b/c` into the datapath.

**Write FSM** (`pwoWriteStatesType`): `WR_IDLE → WR_STAGE → WR_WAIT/WR_MEM ⇄ ...`, returning to `WR_STAGE`/`WR_IDLE`. Streams `butterfly_ready`-gated results out to `pw_mem_wr_addr_c`.

The two FSMs run concurrently; `busy` and `rst_rounds` are functions of both.

## Assertion IP Overview

### Constraints (`fv_ntt_ctrl_pwo_constraints.sv`)

- `assume_ntt_mode`: `ntt_mode` is restricted to PWM, PWA, PWS, or PAIRWM-with-`mlkem` — the only modes this unit is scoped to prove.
- `assume_wip_butterfly_ready`: `butterfly_ready` tracks a 10-bit shift-register model (`fv_butterflylatancy`) of `bf_enable`, modeling the datapath's fixed pipeline latency between enable and result-ready.
- `assume_stable_mode`: `ntt_mode` is stable for the duration of an in-flight operation (`fv_aux_mode`, set on `ntt_enable` and cleared on `done`).
- `assume_stable_pwo_mem_base_addr`: `pwo_mem_base_addr` is stable for the duration of an in-flight operation.
- `assume_pwo_mem_base_addr`: each of `pw_base_addr_a/b/c` is bounded below `16320`.
- `assume_stable_shuffle_en`: `shuffle_en` is stable for the duration of an in-flight operation.
- `assume_buf0_valid`: `buf0_valid` is tied to `0` — not exercised by the PWO datapath.
- `assume_sampler_valid_max_64` / `assume_not_more_64_sampler_valid`: within a read round, `sampler_valid` must eventually pulse before a 64-cycle counter (`fv_sampler_valid_counter`) saturates, and cannot pulse a 65th time in the same round — models the sampler's fixed 64-entry supply per round.

### Reference-Model Assertions (`fv_ntt_ctrl_pwo_m.sv`, generated from `model/ntt_ctrl_pwo.h`)

Bound as `fv_ntt_ctrl_pwo_m` in `fv_ntt_ctrl_pwo_binding.sv`. These are auto-generated one-per-transition from the two-threaded SystemC reference model (`read`/`write` processes in the `.h` file). Listed individually below (35 assertions total).

**Reset**

- `a_commons_reset`: on reset (`!rst`) or `zeroize`, the shared-buffer outputs and reset-count registers return to their initial values — `buf_wr_rst_count`/`buf_rd_rst_count` asserted, `buf_wren`/`buf_rden`/`buf_wrptr`/`buf_rdptr`/`mem_rd_en`/`mem_wr_en`/`opcode` all zero.
- `a_read_reset`: on reset or `zeroize`, the read FSM returns to `RD_IDLE` and all its registers clear to zero — `buf_rdptr_reg`, `chunk_count_reg`, `pw_mem_rd_addr_a/b/c` (both the output and the internal `_reg` copy), `rd_valid_count`, `twiddle_addr_int`, `twiddle_addr_reg_d2`, `incr_twiddle_addr_reg`.
- `a_write_reset`: on reset or `zeroize`, the write FSM returns to `WR_IDLE` and all its registers clear to zero — `chunk_count`, `chunk_rand_offset`, `index_count`, `index_rand_offset`, `pw_mem_wr_addr_c` (output and `_reg` copy), `rounds_count`, `wr_valid_count`, `done`.

**Shared-Output Stability**

- `a_commons_state_to_state`: outside reset, the shared-buffer outputs (`buf_wr_rst_count`, `buf_rd_rst_count`, `buf_wren`, `buf_rden`, `buf_wrptr`, `buf_rdptr`, `mem_rd_en`, `mem_wr_en`) stay stable cycle-to-cycle, and `opcode` equals `ntt_mode` delayed by one cycle — these shared-datapath outputs are unused pass-throughs in PWO mode, independent of the read/write sub-FSMs.

**Read FSM Transitions**

- `a_read_fv_read_idle_to_fv_read_idle`: `RD_IDLE` holds while `ntt_enable` is low; the address/twiddle registers only move on a stray `butterfly_ready` from a prior operation still draining.
- `a_read_fv_read_idle_to_fv_read_stage`: `RD_IDLE → RD_STAGE` when `ntt_enable` is asserted.
- `a_read_fv_read_stage_to_fv_read_exec`: `RD_STAGE → RD_EXEC` when the write FSM is concurrently in `WR_STAGE` and `rounds_count != 1` — the write side has staged the next round and another round remains.
- `a_read_fv_read_stage_to_fv_read_idle`: `RD_STAGE → RD_IDLE` when `rounds_count == 1` (final round) and `ntt_enable` has dropped.
- `a_read_fv_read_stage_to_fv_read_stage`: `RD_STAGE` holds otherwise — either still waiting for the write FSM to reach `WR_STAGE`, or on the final round with `ntt_enable` still asserted (back-to-back operation).
- `a_read_fv_read_exec_to_fv_read_exec`: `RD_EXEC` holds while `sampler_valid` keeps arriving (or the 64-read counter has already saturated) and `rd_valid_count < 0x3F`; `pw_mem_rd_addr_a/b/c`, `buf_rdptr_reg`, `chunk_count_reg`, and the twiddle registers advance per the read-address/twiddle equations.
- `a_read_fv_read_exec_to_fv_read_exec_wait`: `RD_EXEC → EXEC_WAIT` when `sampler_valid` drops before `rd_valid_count` reaches 64 — the read side stalls waiting on the sampler.
- `a_read_fv_read_exec_to_fv_read_stage`: `RD_EXEC → RD_STAGE` once `rd_valid_count >= 0x3F` and `sampler_valid` is asserted (or the counter is already saturated) — the round's 64 reads are complete.
- `a_read_fv_read_exec_wait_to_fv_read_exec`: `EXEC_WAIT → RD_EXEC` once `sampler_valid` returns and `rd_valid_count < 0x40`.
- `a_read_fv_read_exec_wait_to_fv_read_exec_wait`: `EXEC_WAIT` holds while still waiting on `sampler_valid` (or the 64-read limit is already reached).

**Write FSM Transitions**

- `a_write_fv_write_idle_to_fv_write_idle`: `WR_IDLE` holds while `ntt_enable` is low; `chunk_count`/`index_count`/`index_rand_offset` still track any concurrent read-side progress, and `rounds_count`/`done` reflect a possible round reset.
- `a_write_fv_write_idle_to_fv_write_stage`: `WR_IDLE → WR_STAGE` when `ntt_enable` is asserted; latches `chunk_count` and `chunk_rand_offset` from the `random` input for the new operation.
- `a_write_fv_write_stage_to_fv_write_mem`: `WR_STAGE → WR_MEM` when `rounds_count != 1` and `shuffle_en` — shuffled addressing skips the wait state and writes directly.
- `a_write_fv_write_stage_to_fv_write_wait`: `WR_STAGE → WR_WAIT` when `rounds_count != 1` and `!shuffle_en` — non-shuffled addressing waits for the first `butterfly_ready` before writing.
- `a_write_fv_write_stage_to_fv_write_idle`: `WR_STAGE → WR_IDLE` when `rounds_count == 1` — the last round is done; `rounds_count` clears and `done` deasserts on the next cycle.
- `a_write_fv_write_wait_to_fv_write_mem`: `WR_WAIT → WR_MEM` when `!shuffle_en` and `butterfly_ready` arrives.
- `a_write_fv_write_wait_to_fv_write_stage`: `WR_WAIT → WR_STAGE` when `shuffle_en` — advances directly into the next round's staging, incrementing `rounds_count` and re-latching `chunk_rand_offset`.
- `a_write_fv_write_wait_to_fv_write_wait`: `WR_WAIT` holds while `!shuffle_en` and no `butterfly_ready` has arrived yet.
- `a_write_fv_write_mem_to_fv_write_mem`: `WR_MEM` holds while more results remain to be written (`wr_valid_count < 0x40` and not yet at the shuffled round-end condition); `pw_mem_wr_addr_c` advances via the incrementing write-address function.
- `a_write_fv_write_mem_to_fv_write_wait`: `WR_MEM → WR_WAIT` when the round isn't finished yet — either non-shuffled with no `butterfly_ready`, or shuffled and the round's last write (`wr_valid_count == 0x3F`) just landed.
- `a_write_fv_write_mem_to_fv_write_stage`: `WR_MEM → WR_STAGE` (non-shuffled only) once `wr_valid_count == 0x40` — the round's 64 writes are complete; increments `rounds_count` and re-latches `chunk_rand_offset` for the next round.

**Liveness**

- `a_read_fv_read_idle_eventually_left`: once `ntt_enable` is asserted while in `RD_IDLE`, the read FSM eventually leaves `RD_IDLE`.
- `a_read_fv_read_stage_eventually_left`: once in `RD_STAGE` with `ntt_enable` low on the final round (`rounds_count==1`), the read FSM eventually leaves `RD_STAGE` — it cannot hang waiting to finish the last round.
- `a_read_fv_read_exec_eventually_left`: `RD_EXEC` is always eventually left.
- `a_read_fv_read_exec_wait_eventually_left`: `EXEC_WAIT` is always eventually left — the sampler cannot stall the read FSM forever.
- `a_write_fv_write_idle_eventually_left`: once `ntt_enable` is asserted while in `WR_IDLE`, the write FSM eventually leaves `WR_IDLE`.
- `a_write_fv_write_stage_eventually_left`: once in `WR_STAGE` with `ntt_enable` low, the write FSM eventually leaves `WR_STAGE`.
- `a_write_fv_write_wait_eventually_left`: `WR_WAIT` is always eventually left.
- `a_write_fv_write_mem_eventually_left`: `WR_MEM` is always eventually left.

**Consistency**

- `a_read_consistency_onehot0_state`: at most one of the four read-state indicator signals (`fv_read_idle`, `fv_read_stage`, `fv_read_exec`, `fv_read_exec_wait`) is asserted at any time.
- `a_write_consistency_onehot0_state`: at most one of the four write-state indicator signals (`fv_write_idle`, `fv_write_stage`, `fv_write_mem`, `fv_write_wait`) is asserted at any time.

### Additional Properties (`fv_ntt_ctrl_pwo_additional_properties.sv`)

Hand-written because these outputs are combinational functions of *both* sub-FSMs or of `shuffle_en`, which the single-threaded reference model above cannot express directly:

- `assert_bf_enable_a`: `bf_enable` equals the shuffle-en-selected tap of the internal `bf_enable_reg` pipeline (`LATENCY` deep when `shuffle_en`, `LATENCY-1` otherwise).
- `assert_twiddle_addr_a`: `twiddle_addr` equals the correct `twiddle_addr_reg` pipeline tap, selected by `shuffle_en` and `pairwm_mode` (tap `0`, `LATENCY-1`, or `LATENCY+1`).
- `assert_pw_rden_a`: `pw_rden` equals `pw_rden_reg` when `shuffle_en`, otherwise `sampler_valid` gated by the read FSM being in `RD_EXEC`/`EXEC_WAIT`.
- `assert_pw_rden_dest_mem_a`: same expression as `pw_rden`, additionally gated by `accumulate` (else `0`).
- `assert_pw_wren_a`: `pw_wren` equals `pw_wren_reg` when `shuffle_en`, otherwise `butterfly_ready` gated by the write FSM being in `WR_MEM`/`WR_WAIT`.
- `assert_busy_a`: `busy` is asserted whenever either sub-FSM is out of its idle state.
- `assert_rst_rounds_a`: `rst_rounds` is asserted exactly when both sub-FSMs are simultaneously idle (between operations).
- `assert_buf_wren_a`: `buf_wren` is tied to `0` — the shared NTT/GS buffer write enable is unused in PWO mode.
- `assert_buf_rden_a`: `buf_rden` is tied to `0` — the shared NTT/GS buffer read enable is unused in PWO mode.
- `assert_buf_wrptr_a`: `buf_wrptr` is tied to `0` — it only advances on `buf_wren` (always `0` here) or a `gs_mode` shuffle path (never taken in PWO mode), and is reset to `0` otherwise.
- `assert_buf_rdptr_a`: `buf_rdptr` is tied to `0` — it tracks `buf_count`, which only advances on `buf0_valid` (constrained to `0` by `assume_buf0_valid`).
- `assert_mem_rd_en_a`: `mem_rd_en` is tied to `0` — every FSM state that would set it is gated by `ct_mode`/`gs_mode`/`ntt_mode inside {ct,gs}`, none of which hold in PWO mode.
- `assert_mem_wr_en_a`: `mem_wr_en` is tied to `0` — every FSM state that would set it is gated by `ct_mode`/`gs_mode`, none of which hold in PWO mode.
- `assert_buf_wr_rst_count_a`: `buf_wr_rst_count` is tied to `1` — `buf_wr_rst_count = pwo_mode ? 1'b1 : ...` keeps the unused NTT/GS write-buffer counter permanently held in reset.
- `assert_buf_rd_rst_count_a`: `buf_rd_rst_count` is tied to `1` — `buf_rd_rst_count = pwo_mode ? 1'b1 : ...` keeps the unused NTT/GS read-buffer counter permanently held in reset.

## Reproduce Results
The AIP has been tested and proven with atleast one of these formals tools (Onespin ,Jasper , vcf).

To reproduce the results:
Load the AIP with all the necessary constraints together in your formal tool.

Feel free to reach out to contact@lubis-eda.com to request the loadscripts or the lubis modules.
