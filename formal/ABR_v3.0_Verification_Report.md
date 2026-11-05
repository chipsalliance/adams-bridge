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

# ABR 3.0 Verification Report

Author: LUBIS EDA

## Overview

- Number of blocks: 19
- Number of assertions: 1724
- Number of assumptions: 569
- Lines of Code (AIP LoC): >38.7k
- Reported Bugs/Enhancements: 0

This report outlines the formal verification effort and sign-off process.

The goal of the verification effort was to verify the correct functional behavior of the design by using System
Verilog assertions. Assumptions ensure that only realistic input stimuli are considered by these assertions. The
goal of the sign-off process was to guarantee a thorough exploration of the design behavior by the created
property suite. Formal coverage analysis and bound analysis are two examples that were used to achieve this
goal.

## Summary of Key Changes

This section summarizes, for each block verified in v3.0, the Adams Bridge design changes and the AIP updates
that were reviewed for them. All changes are compared against the previous AIP release, and the counts match
the Formal Effort table.

### Architectural masking in v3.0

- The masked NTT datapath was removed, together with the `masking_en` / `rnd_i` / share-memory ports of the NTT.
- Secret polynomial coefficients are now stored as arithmetic shares mod q, created by the new splitter on the
  memory-write path of SAMPLER_TOP, DECOMPRESS and SKDECODE_TOP.
- Splitting is enabled by ABR_CTRL through the new `split_en_o`.
- Stored shares are recombined on read by the new recombiner logic (`abr_recombiner`): a combinational
  `(share0 + share1) mod q` per coefficient lane, with the ML-DSA or ML-KEM modulus selected by mode. Two
  instances (one per memory bank) sit in `abr_top` and are fused into the downstream consumers through the new
  `*_R` opcodes (`PWS_R`, `PWA_R`, `NORMCHK_R`, `COMPRESS_R`, `DECOMPOSE_R`, `SKENCODE_R`, `SIGENCODE_R`,
  `PWR2RND_R`), enabled by ABR_CTRL through `recombine_en_o` / `recombine_mode_o`. There is no separate
  RECOMBINE pass, so masking adds no cycle overhead.
- The Keccak core is masked with a DOM two-share scheme; its shares are recombined inside SAMPLER_TOP.
- All masking properties verify functional correctness (the shares recombine to the original value and the
  randomness is used as specified), not side-channel or probing security.

### KeyVault interface in v3.0

- New KV read-client interface in ABR_CTRL: key-length check with the new `KV_RD_LEN_MISMATCH` error, and abort
  on KV response errors.
- KV FSM uses a sparse encoding with a dedicated error state; KV status is cleared on zeroize.
- Seeds are cleared on any non-success KV status; all-zero seed/message values are detected as errors.
- After a KV read error, no new ML-DSA or ML-KEM command can start until zeroize is applied.
- Verified by the ABR_CTRL (KeyVault) AIP; see section 5.

### Blocks at a glance

| Block | Area | Key change reviewed |
|---|---|---|
| SPLITTER | Masking | New share splitter (new AIP) |
| SAMPLER_TOP | Samplers / masking | Splitter on CBD output, Keccak share recombination |
| SKDECODE_TOP | Samplers / masking | ML-DSA secret-key decode with two splitters |
| DECOMPRESS | Samplers / masking | Splitter on the write path |
| NTT_BUTTERFLY | NTT | Combinational Barrett reduction, pairwm path |
| NTT_BUTTERFLY2X2 | NTT | 2x2 butterfly array (new AIP; RTL removed after verification, AIP kept) |
| NTT_HYBRID_BUTTERFLY_2X2 | NTT | Unmasked hybrid butterfly |
| NTT_KARATSUBA_PAIRWM | NTT | Shares the butterfly multipliers |
| NTT_CTRL - CT (ML-DSA) | NTT | Forward NTT control, ML-DSA (new AIP) |
| NTT_CTRL - CT (ML-KEM) | NTT | Forward NTT control, ML-KEM |
| NTT_CTRL - GS (ML-DSA) | NTT | Inverse NTT control, ML-DSA (new AIP) |
| NTT_CTRL - GS (ML-KEM) | NTT | Inverse NTT control, ML-KEM |
| NTT_CTRL - PWO (incl. PAIRWM) | NTT | Point-wise operation control |
| NTT_TOP | NTT | Masking removed, new latencies |
| SHA3 - KECCAK_ROUND | Keccak masking | DOM-masked two-share Keccak round |
| SHA3 | Keccak masking | Masking controls passed through |
| SHA3 - SHA3PAD | Keccak masking | Padding on masked data |
| ABR_CTRL (whitebox only) | Controller | Split enable and new interfaces |
| ABR_CTRL (KeyVault) | KV interface | KV length check and error handling |

## 1. Masking: splitter and recombination

### SPLITTER

- Design change in v3.0:
  - New unit `abr_splitter`: splits each coefficient into two arithmetic shares mod q
    (share0 = r mod q, share1 = (d - r) mod q), 4 lanes, ML-DSA and ML-KEM moduli, fixed 2-cycle latency.
  - Instantiated on the memory-write path of SAMPLER_TOP, DECOMPRESS and SKDECODE_TOP.
- Verified and reviewed:
  - End-to-end scoreboard: (share0 + share1) mod q equals the input coefficient, in order and without loss.
  - share0 is the reduced random value and share1 the masked data, so a design that ignores `rand_i` is detected.
  - Output and reduced-randomness range checks.
  - Outputs and internal registers cleared on reset and zeroize.
  - Input contract: unused upper data bits are zero.
  - Assumptions: coefficients below q, stable mode.
- Assertions: 11 total: 11 added, 0 modified
- Assumptions: 2 total: 2 added, 0 modified

### Recombination

Recombination of shares is verified where the shares are consumed:

- SAMPLER_TOP: the two masked-Keccak state shares are recombined inside the sampler and checked against
  state == share0 ^ share1 (`a_sha3_state_recombine`).
- SHA3 - SHA3PAD: the padding scoreboard checks the recombined value (share0 ^ share1) of the input message and
  of the Keccak output.
- SPLITTER: the scoreboard checks that the stored arithmetic shares recombine to the original coefficient
  ((share0 + share1) mod q).

## 2. Samplers

### SAMPLER_TOP

- Design change in v3.0:
  - Splitter added on the CBD output path towards memory.
  - The two masked-Keccak state shares are recombined inside the sampler.
  - New Keccak DOM randomness inputs and a rejection-bounded hold counter.
- Verified and reviewed:
  - Mode multiplexer checked per share against an inline splitter model when split is enabled; bypass checked
    unmasked.
  - Keccak share recombination: state == share0 ^ share1 (`a_sha3_state_recombine`).
  - Splitter mode, enable and exactly-2-cycle latency; one-hot data-valid.
  - Busy held while the split pipeline drains; no new start while busy; mask-mode selection.
  - New assumptions: liveness of the Keccak randomness, stable split enable during an operation.
- Assertions: 76 total: 19 added, 13 modified, 2 removed
- Assumptions: 28 total: 2 added, 0 modified

### SKDECODE_TOP

- Design change in v3.0:
  - Two splitters with independent randomness on the two write ports.
  - Memory write requests delayed by the split pipeline; done held off until it drains.
- Verified and reviewed:
  - Full read/write sequencing FSM of ML-DSA secret-key decoding against a reference model.
  - Every FSM-step property in an unmasked and a masked variant; the masked variant checks both shares of each
    memory write against the splitter model.
  - done held while draining and following the internal done otherwise.
  - s1/s2 and t0 buffer scoreboards.
- Assertions: 146 total: 71 added, 59 modified, 50 removed
- Assumptions: 12 total: 6 added, 1 modified

### DECOMPRESS

- Design change in v3.0:
  - Splitter inserted on the memory-write path (ML-KEM); write data widened to two shares.
  - New inputs `split_en_i`, `rand_i`, `api_rd_data_valid`; write request and done delayed by the split pipeline.
- Verified and reviewed:
  - New scoreboard on the 192-bit shared write data, next to the existing address scoreboard.
  - Inline ML-KEM splitter model; done latency adapted to the split pipeline.
  - New assumptions: API-read latency, stable split enable during decompression.
- Assertions: 8 total: 1 added, 2 modified
- Assumptions: 13 total: 4 added, 0 modified

## 3. NTT

### NTT_BUTTERFLY

- Design change in v3.0:
  - ML-DSA reduction is now the combinational Barrett reduction (butterfly latency 10 to 6).
  - New pair-wise-multiply (pairwm) multiply path shared with the Karatsuba unit.
  - Masked datapath removed.
- Verified and reviewed:
  - ML-DSA and ML-KEM Barrett-step and result-range checks.
  - New pairwm mode.
  - 29 white-box connectivity checks.
  - Updated C/C++ reference model.
- Assertions: 74 total: 68 added, 6 modified
- Assumptions: 4 total: 1 added, 1 modified, 1 removed

### NTT_BUTTERFLY2X2

- Design change in v3.0:
  - 2x2 butterfly array with the new latency parameters.
- Verified and reviewed:
  - Results per mode (CT, GS, PWM, PWA, PWS, pairwm) for ML-DSA and ML-KEM against a C++ reference model.
  - White-box wiring checks.
- Assertions: 84 total: 84 added, 0 modified
- Assumptions: 7 total: 7 added, 0 modified
- Note: after this verification, the `ntt_butterfly2x2` RTL module was removed from the design as dead code (the design uses `ntt_hybrid_butterfly_2x2`). Only the AIP is kept in `formal/fv_ntt_butterfly2x2`, for reference; it cannot be elaborated against the current RTL.

### NTT_HYBRID_BUTTERFLY_2X2

- Design change in v3.0:
  - Masked/unmasked paths merged into a single unmasked datapath; Karatsuba taps from the butterfly multipliers.
- Verified and reviewed:
  - Masked/unmasked check pairs replaced by unmasked end-to-end checks.
  - About 70 new white-box checks: crossbar, twiddle delay, Karatsuba taps, passthrough, ready pipeline.
  - Masking constraints removed; C++ reference model updated.
- Assertions: 96 total: 81 added, 15 modified, 5 removed
- Assumptions: 8 total: 0 added, 2 modified, 1 removed

### NTT_KARATSUBA_PAIRWM

- Design change in v3.0:
  - Receives two of its products from the butterfly; computes only the remaining product and the zeta
    multiplication.
- Verified and reviewed:
  - New pipeline-stage checks for the shared-multiplier structure.
  - Range assumptions on the products supplied by the butterfly.
  - C++ reference model updated.
- Assertions: 20 total: 15 added, 4 modified
- Assumptions: 7 total: 2 added, 0 modified

### NTT_CTRL - CT (ML-DSA)

- Design change in v3.0:
  - Masking interface removed; memory reads qualified by the new `mem_rd_data_valid`; latencies and register
    widths changed.
- Verified and reviewed:
  - Read and write FSMs against a reference model.
  - Memory and buffer addressing, butterfly enable and twiddle address (incl. latency registers), shuffling
    offsets, busy and done.
- Assertions: 52 total: 52 added, 0 modified
- Assumptions: 8 total: 8 added, 0 modified

### NTT_CTRL - CT (ML-KEM)

- Design change in v3.0:
  - Masking ports removed; new latencies; memory reads qualified by `mem_rd_data_valid`.
- Verified and reviewed:
  - Reference model rewritten for the removed masking ports and new latencies.
  - New checks on the butterfly-enable and twiddle-address latency registers, done, buffer write pointer and
    destination-memory read.
  - Constraints relaxed on memory read-valid.
- Assertions: 54 total: 8 added, 28 modified, 1 removed
- Assumptions: 8 total: 1 added, 5 modified, 4 removed

### NTT_CTRL - GS (ML-DSA)

- Design change in v3.0:
  - Masking interface removed; memory reads qualified by the new `mem_rd_data_valid`; latencies and register
    widths changed.
- Verified and reviewed:
  - Read and write FSMs against a reference model.
  - Memory and buffer addressing, butterfly enable and twiddle address (incl. latency registers), shuffling
    offsets, busy and done.
- Assertions: 50 total: 50 added, 0 modified
- Assumptions: 7 total: 7 added, 0 modified

### NTT_CTRL - GS (ML-KEM)

- Design change in v3.0:
  - Masked GS mode removed; new latencies; memory reads qualified by `mem_rd_data_valid`.
- Verified and reviewed:
  - Reference model rewritten for the removed masking ports and new latencies.
  - New checks on the butterfly-enable and twiddle-address latency registers, done, buffer write pointer and
    destination-memory read.
  - Constraints relaxed on memory read-valid.
- Assertions: 52 total: 11 added, 24 modified
- Assumptions: 7 total: 0 added, 4 modified, 4 removed

### NTT_CTRL - PWO (incl. PAIRWM)

- Design change in v3.0:
  - Share-memory read enable replaced by `pw_rden_dest_mem`; PWM latency 5 to 3.
- Verified and reviewed:
  - PWM, PWA, PWS and PAIRWM read/write FSMs against a reference model.
  - Additional checks on butterfly enable, twiddle address, point-wise read enables and busy.
- Assertions: 103 total: 50 added, 0 modified
- Assumptions: 24 total: 9 added, 0 modified

### NTT_TOP

- Design change in v3.0:
  - Masked datapath, share memory and `masking_en` / `rnd_i` removed; INTT write-buffer latency 13 to 9.
- Verified and reviewed:
  - Share and masking checks retired.
  - New checks: twiddle ROM, butterfly mode inputs (passthrough, ML-KEM, shuffle), memory read-valid, buffer
    read/write, PWO registers, PWM destination memory.
  - Constraints rewritten for the new interface.
- Assertions: 69 total: 12 added, 12 modified, 19 removed
- Assumptions: 7 total: 1 added, 1 modified, 1 removed

## 4. Keccak masking

### SHA3 - KECCAK_ROUND

- Design change in v3.0:
  - Rebased onto a DOM-masked two-share scheme: run-time `masked_i`, one round per four cycles when masked, chi
    computed with DOM AND gadgets.
  - Randomness handshake `rand_update_o` / `rand_consumed_o`.
- Verified and reviewed:
  - Both state shares bound; the previous AIP bound share 0 only.
  - Masked mode: XOR of the two shares checked against the unmasked reference round (theta, rho, pi, chi, iota)
    for every round.
  - Round counting, stall while randomness is unavailable, exact `rand_update_o` / `rand_consumed_o` timing.
  - Liveness of every masked-FSM state and one-hot state encoding.
  - Verified with JasperGold, EnMasking = 1.
- Assertions: 20 total: 10 added, 6 modified
- Assumptions: 4 total: 3 added, 0 modified

### SHA3

- Design change in v3.0:
  - `masked_i` and the randomness handshake passed through to the Keccak core; cSHAKE `ns_data_i` variant
    removed.
- Verified and reviewed:
  - Existing FSM checks retained.
  - New white-box checks: randomness and masking port connections, Keccak start/absorb hand-off, SW-control
    error detection, count / sparse-FSM / storage-reset error outputs.
  - New assumptions on masking availability and randomness progress.
  - Masking coverage collected for EnMasking = 0 and EnMasking = 1 and merged.
- Assertions: 39 total: 14 added, 0 modified
- Assumptions: 18 total: 2 added, 1 modified

### SHA3 - SHA3PAD

- Design change in v3.0:
  - Masked message input; cSHAKE `ns_data_i` input removed.
- Verified and reviewed:
  - Padding scoreboard checks the recombined value (share0 ^ share1) of the input message and of the Keccak
    output.
- Assertions: 13 total: 0 added, 1 modified
- Assumptions: 21 total: 0 added, 1 modified

## 5. KV interface and controller

### ABR_CTRL (whitebox only)

- Design change in v3.0:
  - New `split_en_o` from the build-time masking parameter and the per-command masking bit.
  - Unshared message/sampler interfaces, new LFSR seed fields.
  - Seeds cleared on any non-success KV status; all-zero seed/message error detection.
- Verified and reviewed:
  - Split-enable decode (`assert_split_en_o_a`).
  - LFSR seed and entropy checks rewritten for the new seed fields.
  - Error-flag checks extended with the all-zero seed/message terms.
  - New cross-mode (ML-KEM to ML-DSA and back) covers; command-register consistency assumptions.
- Assertions: 643 total: 1 added, 24 modified
- Assumptions: 119 total: 10 added, 2 modified

### ABR_CTRL (KeyVault)

- Design change in v3.0:
  - KV read client: key-length check, new `KV_RD_LEN_MISMATCH` error, abort on KV response errors.
  - KV FSM: sparse encoding with a dedicated error state; status macros cleared on zeroize.
- Verified and reviewed:
  - Read model aborts on a KV response error, models the length mismatch and holds the error until reset or
    zeroize.
  - After a KV read error, no new ML-DSA or ML-KEM command can start until zeroize is applied.
  - Updated secret-not-leaked-to-API and SK-RAM message-write checks.
  - Shared-key write model aborts and resets its offset on a write error; write-status checks reworked.
  - PCR-signing MLDSA_MSG checks removed for the new interface.
- Assertions: 114 total: 3 added, 4 modified
- Assumptions: 265 total: 0 added, 6 modified

## Formal Effort

The table below shows the summary of the conducted formal verification activities for each block. Its columns
contain the following information:

- Version of the adamsbridge.
- Module/Block name which has a dedicated Assertion IP.
- The number of assertions: total in the current AIP, and how many were added, modified or removed.
- The number of assumptions and constraints: total in the current AIP, and how many were added, modified or
  removed.
- The Assertion IP (AIP) Lines of Code (LoC): total, and lines added / removed.
- Any bugs or enhancements identified during verification, along with their corresponding GitHub issue IDs.

The goal of this detailed breakdown is to provide information about the verification scope and outcome in a
transparent way.

The added, modified and removed counts are relative to the previous AIP release:

- Added: a check with an intent that did not exist in the previous release.
- Modified: an existing check whose intent was changed. Renames and restyling of existing checks are also counted
  as modified.
- Removed: a check from the previous release that is no longer part of the AIP.

| # | Version | Block | Assertions Total | Assertions Added | Assertions Modified | Assertions Removed | Assumptions Total | Assumptions Added | Assumptions Modified | Assumptions Removed | AIP LoC Total | AIP LoC Added / Removed | Bugs/Enhancements | Issue ID |
|---|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---:|---|
| 1 | 3.0 | ABR_CTRL (whitebox only) | 643 | 1 | 24 | 0 | 119 | 10 | 2 | 0 | 14822 | +279 / -151 | | |
| 2 | 3.0 | ABR_CTRL (KeyVault) | 114 | 3 | 4 | 0 | 265 | 0 | 6 | 0 | 3926 | +1071 / -750 | | |
| 3 | 3.0 | SHA3 - KECCAK_ROUND | 20 | 10 | 6 | 0 | 4 | 3 | 0 | 0 | 583 | +381 / -127 | | |
| 4 | 3.0 | SHA3 | 39 | 14 | 0 | 0 | 18 | 2 | 1 | 0 | 718 | +241 / -112 | | |
| 5 | 3.0 | SHA3 - SHA3PAD | 13 | 0 | 1 | 0 | 21 | 0 | 1 | 0 | 712 | +132 / -98 | | |
| 6 | 3.0 | SPLITTER | 11 | 11 | 0 | 0 | 2 | 2 | 0 | 0 | 236 | +236 / -0 | | |
| 7 | 3.0 | DECOMPRESS | 8 | 1 | 2 | 0 | 13 | 4 | 0 | 0 | 655 | +156 / -31 | | |
| 8 | 3.0 | NTT_BUTTERFLY | 74 | 68 | 6 | 0 | 4 | 1 | 1 | 1 | 891 | +637 / -128 | | |
| 9 | 3.0 | NTT_BUTTERFLY2X2 | 84 | 84 | 0 | 0 | 7 | 7 | 0 | 0 | 1243 | +1243 / -0 | | |
| 10 | 3.0 | NTT_CTRL - CT (ML-DSA) | 52 | 52 | 0 | 0 | 8 | 8 | 0 | 0 | 1159 | +1159 / -0 | | |
| 11 | 3.0 | NTT_CTRL - CT (ML-KEM) | 54 | 8 | 28 | 1 | 8 | 1 | 5 | 4 | 1126 | +363 / -345 | | |
| 12 | 3.0 | NTT_CTRL - GS (ML-DSA) | 50 | 50 | 0 | 0 | 7 | 7 | 0 | 0 | 1171 | +1171 / -0 | | |
| 13 | 3.0 | NTT_CTRL - GS (ML-KEM) | 52 | 11 | 24 | 0 | 7 | 0 | 4 | 4 | 1165 | +516 / -488 | | |
| 14 | 3.0 | NTT_CTRL - PWO (incl. PAIRWM) | 103 | 50 | 0 | 0 | 24 | 9 | 0 | 0 | 2911 | +1259 / -0 | | |
| 15 | 3.0 | NTT_HYBRID_BUTTERFLY_2X2 | 96 | 81 | 15 | 5 | 8 | 0 | 2 | 1 | 1432 | +1072 / -538 | | |
| 16 | 3.0 | NTT_KARATSUBA_PAIRWM | 20 | 15 | 4 | 0 | 7 | 2 | 0 | 0 | 260 | +176 / -54 | | |
| 17 | 3.0 | NTT_TOP | 69 | 12 | 12 | 19 | 7 | 1 | 1 | 1 | 883 | +290 / -399 | | |
| 18 | 3.0 | SAMPLER_TOP | 76 | 19 | 13 | 2 | 28 | 2 | 0 | 0 | 1130 | +419 / -184 | | |
| 19 | 3.0 | SKDECODE_TOP | 146 | 71 | 59 | 50 | 12 | 6 | 1 | 0 | 3723 | +1827 / -1344 | | |
| | | **Total** | **1724** | **561** | **198** | **77** | **569** | **65** | **24** | **11** | **38746** | **+12628 / -4749** | **0** | |

## Formal Sign-off

The sign-off section outlines details about what aspects were considered for the blocks to be said as formally
verified within the scope. This starts with the verification strategy chosen, formal coverage, quantitative
analysis like reviews, and proof time.

### Verification Strategy

Some formal checks did not conclude within the configured amount of time. This is a typical outcome when formal
verification is applied on mathematical complex design blocks with a large sequential depth. Inconclusive proofs
are caused by a large search space which increases the runtime exponentially, well-known as state space
explosion.

We addressed this issue by applying reduction and abstraction techniques such that the formal check either
concludes, or it reaches a sufficiently large sequential depth. In cases where this effort was not enough and in
cooperation with our partners, we agreed on the application of simulation to support the verification effort or
focus on critical aspects of the design behavior.

We tailored our verification efforts to every block. Overall, we used the following reduction and abstraction
techniques:

- Initial-value abstraction
- Counter abstraction
- Non-determinism
- Signal cutting
- Scoreboarding
- Parameter reduction

The application of these techniques reduced the runtime of formal checks significantly. This allowed us to
achieve a higher formal coverage. Some formal checks are still inconclusive. However, the overall result of this
verification effort is in our opinion still robust. This is supported by the achieved coverage metric and the
comprehensive reviews.

### Formal Coverage

Formal coverage is one of the key metrics we rely on to judge how complete our formal verification is. It tells
us whether:

- We've missed any important features or cases
- Our constraints are too tight and hiding valid behavior

Coverage numbers like checker and stimuli coverage help us decide if we've verified a block well enough. Higher
coverage means we've done a good job exploring the design and its behavior.

### Code, Constraints Review

We didn't rely on the tools alone. All the code, constraints were reviewed manually to make sure they reflect
what we want to test and match the expected behavior. This step also helped us avoid over-constraining the
design unintentionally.

### Bound review (Non-Converging proofs)

This bound determines the maximum number of sequential steps or cycles the tool will analyze to either prove or
disprove a property. Evaluate whether the property's behavior within the bound is sufficient to provide
meaningful confidence, even if full convergence isn't achieved. If full convergence is achieved, it could be
depicted as bound review as complete.

### Prove Time

Each block was given a minimum prove time so the tool could properly explore the design. This helps ensure
deeper or more complex behaviors aren't missed just because the proof was cut short.

| # | Version | Block | Formal Coverage\* | Coverage Review | Bound Review | Constraint Review | Code Review | Prove time minimum^ |
|---|---|---|---|---|---|---|---|---|
| 1 | 3.0 | ABR_CTRL (whitebox only) | 100% | Yes | Yes | Yes | Yes | < 24h |
| 2 | 3.0 | ABR_CTRL (KeyVault) | 100% | Yes | Yes | Yes | Yes | < 24h |
| 3 | 3.0 | SHA3 - KECCAK_ROUND | 100% | Yes | Yes | Yes | Yes | < 1h |
| 4 | 3.0 | SHA3 | 100% | Yes | Yes | Yes | Yes | < 1h |
| 5 | 3.0 | SHA3 - SHA3PAD | 100% | Yes | Yes | Yes | Yes | < 24h |
| 6 | 3.0 | SPLITTER | 100% | Yes | Yes | Yes | Yes | < 24h |
| 7 | 3.0 | DECOMPRESS | 100% | Yes | Yes | Yes | Yes | < 24h |
| 8 | 3.0 | NTT_BUTTERFLY | - | - | Yes | Yes | Yes | < 24h |
| 9 | 3.0 | NTT_BUTTERFLY2X2 | - | - | Yes | Yes | Yes | < 24h |
| 10 | 3.0 | NTT_CTRL - CT (ML-DSA) | 100% | Yes | Yes | Yes | Yes | < 24h |
| 11 | 3.0 | NTT_CTRL - CT (ML-KEM) | 100% | Yes | Yes | Yes | Yes | < 24h |
| 12 | 3.0 | NTT_CTRL - GS (ML-DSA) | 100% | Yes | Yes | Yes | Yes | < 24h |
| 13 | 3.0 | NTT_CTRL - GS (ML-KEM) | 100% | Yes | Yes | Yes | Yes | < 24h |
| 14 | 3.0 | NTT_CTRL - PWO | 100% | Yes | Yes | Yes | Yes | < 24h |
| 15 | 3.0 | NTT_HYBRID_BUTTERFLY_2X2 | - | - | Yes | Yes | Yes | < 24h |
| 16 | 3.0 | NTT_KARATSUBA_PAIRWM | 100% | Yes | Yes | Yes | Yes | < 24h |
| 17 | 3.0 | NTT_TOP | 100% | Yes | Yes | Yes | Yes | < 2h |
| 18 | 3.0 | SAMPLER_TOP | 100% | Yes | Yes | Yes | Yes | < 2h |
| 19 | 3.0 | SKDECODE_TOP | 100% | Yes | Yes | Yes | Yes | < 3h |

\*) Excluding unreachable and dead code

^) Proof time with 24h have some non-converging proofs

And the ntt compute modules like butterfly formal coverage is inconclusive since it involves arithmetic
operations like multiplication, modulo which are tough to solve in formal environment.

**Note:** The verification focus is functional, not security.
