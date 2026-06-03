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

# adamsbridge_ctrl - Formal Verification

Date: 26.03.2025
Author: LUBIS EDA GmbH

## Folder Structure

The following files and subdirectories are part of the main directory **formal/fv_abr_ctrl_mldsa**

- `fv_mldsa_ctrl_constraints.sv`: Environment constraints that abstract submodule interfaces and restrict input stimuli to valid protocol scenarios
- `fv_mldsa_ctrl_whitebox.sv`: White-box assertions for internal register state, output signal correctness, and combinational invariants
- `fv_mldsa_ctrl_wrapper.sv`: Top-level wrapper that instantiates the whitebox and constraints modules and binds them to the DUT
- `fv_mldsa_ctrl_secondary_additional_properties.sv`: Supplementary properties for the secondary control path

- model: Contains high-level abstracted model and FSM documentation
  - `model/AdamsBridge.h`: High-level abstracted model used by the formal flow
  - `model/fsm.md`: FSM state documentation
  - `model/sva/AdamsBridge.sv`: Main assertion IP with primary control path FSM transition assertions
  - `model/sva/AdamsBridge_pkg.sv`: Package definitions for types, parameters, and constants used by the AIP
  - `model/sva/AdamsBridge_functions.sv`: Helper functions used by the AIP
  - `model/sva/AdamsBridge_binding.sv`: Binding of the primary AIP to DUT signals
  - `model/sva/AdamsBridgeSecondary.sv`: Secondary control path assertion IP
  - `model/sva/AdamsBridgeSecondary_binding.sv`: Binding of the secondary AIP to DUT signals
  - `model/sva/global_package.sv`: Global verification parameters and type definitions

## DUT Overview

The DUT `mldsa_ctrl` is the top-level control unit for the Adams Bridge MLDSA processor. It orchestrates all data flow and sequencing between the NTT engine, SHA3/sampler, power2round, decompose, sk/pk encode/decode, makehint, and norm-check submodules across keygen, sign, and verify operations. Reset is bound to `(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize)`.

Primary interface groups exercised by the AIP include:
- `clk`, `rst_b`, `zeroize`: Clock, active-low reset, and secure clear
- Register interface: `abr_reg_hwif_in_o` / `abr_reg_hwif_out_i` for API command and status
- Sampler/SHA3 interface: `sha3_start_o`, `msg_start_o`, `msg_valid_o`, `msg_rdy_i`, `sampler_start_o`, `sampler_busy_i`, `sampler_state_dv_i`
- NTT interface: `ntt_enable_o[1:0]`, `ntt_mode_o[1:0]`, `ntt_mem_base_addr_o`, `pwo_mem_base_addr_o`, `ntt_busy_i[1:0]`
- Auxiliary module enables and done signals: `power2round_enable_o`, `decompose_enable_o`, `skencode_enable_o`, `skdecode_enable_o`, `makehint_enable_o`, `normcheck_enable_o` and their respective `_done_i` / `_invalid_i` handshakes
- Status outputs: `busy_o`, `error_o`, `valid_reg` outputs

## Assertion IP Overview

The AIP is split across two main SVA files (`model/sva/AdamsBridge.sv` for the primary path and `model/sva/AdamsBridgeSecondary.sv` for the secondary path) plus the whitebox and additional properties files.

### Reset Assertion

- **ctrl_reset_a**: Verifies that all output control signals, FSM state, and registered state are driven to their reset values on deassertion of `rst_b` or assertion of `zeroize`.

### Primary FSM Transition Assertions (`model/sva/AdamsBridge.sv`)

The primary AIP contains 587 FSM state transition assertions. Each assertion encodes a specific `from_state → to_state` transition along with the exact output and register values that must hold during that step. Assertions are organized by operation:

- **Idle transitions** (~34 assertions): Cover `ctrl_idle_to_idle_a`, `ctrl_idle_to_keygen_rnd_seed_SHA3_START_a`, `ctrl_idle_to_sign_rnd_seed_SHA3_START_a`, `ctrl_idle_to_verify_pk_decode_start_a` and related keygen-jump-sign transitions.

- **Keygen sequence** (~169 assertions): Cover the full keygen FSM from seed expansion (`ctrl_keygen_expand_seed_*`) through NTT-S1/S2 sampling (`ctrl_Keygen_ntt_s1_*`, `ctrl_keygen_intt_a_*`), T computation (`ctrl_keygen_compute_t_*`), power2round (`ctrl_keygen_compute_t_to_keygen_power_2_round_*`), PWM-A expansion (`ctrl_keygen_pwm_a_*`), reject-bounded sampling (`ctrl_keygen_write_rejbounded_*`), tr computation and pk write (`ctrl_keygen_compute_tr_write_pk_*`, `ctrl_keygen_compute_tr_sampling_*`), and sk encode (`ctrl_keygen_compute_tr_sampling_to_keygen_sk_encode_start_a`), ending at `ctrl_keygen_end_state_to_idle_a`.

- **Sign sequence** (~256 assertions): Cover the full sign FSM including random seed hashing (`ctrl_sign_rnd_seed_*`), mu computation (`ctrl_sign_compute_mu_*`), LFSR seed and mask expansion (`ctrl_sign_compute_lfsr_seed_*`, `ctrl_sign_expand_mask_*`), NTT on y (`ctrl_sign_ntt_y_*`), PWO-W computation (`ctrl_sign_compute_w_*`), decompose (`ctrl_sign_decompose_*`), sample-in-ball (`ctrl_sign_compute_c_*`, `ctrl_sign_sample_in_ball_*`), NTT on c (`ctrl_sign_ntt_c_*`), z and w0 computation (`ctrl_sign_compute_z_*`, `ctrl_sign_compute_w0_*`), norm check (`ctrl_sign_check_*`), makehint (`ctrl_sign_makehint_*`), sigencode (`ctrl_sign_sigencode_*`), and sign end state transitions.

- **Verify sequence** (~171 assertions): Cover pk decode (`ctrl_verify_pk_decode_*`), mu computation (`ctrl_verify_compute_mu_*`), sigdecode-z and sigdecode-h (`ctrl_verify_sigdecode_*`), NTT on z (`ctrl_verify_ntt_z_*`), PWM-A (`ctrl_verify_pwm_a_*`), INTT (`ctrl_verify_intt_*`), w1 encode / decompose (`ctrl_verify_decompose_*`, `ctrl_verify_w1_encode_*`), c computation (`ctrl_verify_compute_c_*`, `ctrl_verify_sample_in_ball_*`), norm check (`ctrl_verify_normcheck_*`), and verify end state transitions.

- **Liveness / eventuality assertions**: Each transient FSM state has a corresponding `_eventually_left` property ensuring the controller cannot stall indefinitely.

### Secondary FSM Transition Assertions (`model/sva/AdamsBridgeSecondary.sv`)

The secondary AIP contains 127 assertions covering the parallel secondary control path used during sign masking and response computation:

- **reset_a**: Secondary path output signals cleared on reset.
- **secondary_* state transitions** (~126 assertions): Cover states including `secondary_after_clear_w0_valid`, `secondary_after_clear_y_valid`, `secondary_clear_w0_valid`, `secondary_clear_y_valid`, `secondary_compute_ct_intt`, `secondary_compute_cs2_intt`, `secondary_cs1_ntt`, `secondary_decompose`, `secondary_makehint`, `secondary_normcheck`, `secondary_ntt_y`, and associated start/wait/done transitions.

### White-box Assertions (`fv_mldsa_ctrl_whitebox.sv`)

Combinational and sequential assertions checking internal register correctness:

- Reset and `rst_b` deassert behavior (`assert_reset_A`, `assert_rst_b_A`)
- `mldsa_reg_hwif_in` combinational output (`assert_mldsa_reg_hwif_in_comb_P`)
- Private key register update paths for k/rho, tr, and API writes
- Signature register read-data and stability
- Valid register set/clear timing for `c_valid`, `y_valid`, `w0_valid`, and `verify_valid`
- Sign and verify valid set/reset correctness
- Key vault seed control registers
- Private key lock, read-acknowledge, and signature/pubkey acknowledgment signals
- HW interface acknowledgment and read-data (`assert_mldsa_hwif_in_ack_P`, `assert_mldsa_hwif_rd_data_P`)
- Data-path read integrity: `assert_skdecode_read_data_out_from_mem_P`, `assert_pkdecode_read_data_out_from_mem_P`, `assert_privkey_out_rdata_update_P`
- NTT output zeroing (`assert_ntt_outputs_0_P`), norm-check output (`assert_norm_check_out_P`), busy signal (`assert_busy_o_P`), and signature hint output (`assert_signature_h_o_P`)

### Additional Secondary Properties (`fv_mldsa_ctrl_secondary_additional_properties.sv`)

- **verify_normcheck_enable_o_a**: Verifies the normcheck enable output is correctly driven during verify operations.
- **verify_normcheck_enable_onehot_a**: Verifies that the normcheck enable vector is one-hot at all times.

## Constraint Abstractions (`fv_mldsa_ctrl_constraints.sv`)

The constraints module abstracts all submodule interfaces using parameterized timing macros to make the proof tractable:

| Parameter | Default | Purpose |
|-----------|---------|---------|
| `ADAMSBRIDGE_CNTRL_RDY_DELAY` | 1 | Control-ready signal delay |
| `ADAMSBRIDGE_AUX_DLY` | 2 | Done signal delay for auxiliary modules |
| `ADAMSBRIDGE_BUSY_CNTR` | 2 | Maximum busy counter depth for sampler and NTT |

Each submodule's `_done_i` signal is constrained to assert exactly `ADAMSBRIDGE_AUX_DLY` cycles after the corresponding enable, using `assume_*_done_in_dly` and `assume_*_done_eventually` properties. Modules abstracted in this way include: `sigdecode_z`, `sigdecode_h`, `pkdecode`, `sigencode`, `skdecode`, `skencode`, `power2round`, `decompose`, `normcheck`, `makehint`, and `sampler`/`NTT` busy interfaces. Additional constraints bound address ranges (`assume_makehint_req_addr_range`), memory write enables (`assume_pwr2rnd_api_wren`), and memory response timing (`assume_pwr2rnd_mem_*`).

## Reproduce Results

The AIP has been tested and proven with atleast one of these formals tools (Onespin ,Jasper , vcf) and formal coverage is at 100% excluding valid unreachable and deadcode. 

To reproduce the results:
Load the AIP with all the necessary constraints together in your formal tool. 

Feel free to reach out to contact@lubis-eda.com to request the loadscripts or the lubis modules.
