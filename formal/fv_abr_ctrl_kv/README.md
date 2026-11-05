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

# ABR CTRL KeyVault (MLDSA / MLKEM)

## Folder Structure
The following files are part of the main directory **formal/fv_abr_ctrl_kv**. They verify
the KeyVault (KV) read and write clients of **abr_ctrl** and their interaction with the crypto
core in MLDSA and MLKEM modes.

- **fv_abr_ctrl_kv.sv** is the top-level AIP, bound to `abr_ctrl`. It selects the constraint set
  by macro and instantiates the read/write AIPs and covers.

- **fv_abr_ctrl_kv_constraints.sv** contains the default assumptions/constraints (MLDSA and MLKEM
  together).

- **fv_abr_ctrl_kv_mldsa_constraints.sv** contains the MLDSA-only constraints, used with
  `KV_MLDSA_MODE`.

- **fv_abr_ctrl_kv_mlkem_constraints.sv** contains the MLKEM-only constraints, used with
  `KV_MLKEM_MODE`.

- **fv_abr_ctrl_kv_read_aip.sv** contains the assertions for the KV read clients (MLDSA seed, MLKEM
  seed, MLKEM msg).

- **fv_abr_ctrl_kv_write_aip.sv** contains the assertions for the KV write client (MLKEM shared key).

- **fv_abr_ctrl_kv_read_covers.sv** / **fv_abr_ctrl_kv_write_covers.sv** contain the covers for the KV read
  and write clients.

- **waiver_list.tcl** contains the JasperGold waivers.

The bench is compiled with the `CALIPTRA` define, which enables the KeyVault interface of
`abr_ctrl`.

## DUT Overview

The DUT **abr_ctrl** has the primary inputs and primary outputs relevant to the KeyVault as shown
below.

| S.No | Port                                          | Direction | Description                                          |
| ---- | --------------------------------------------- | --------- | ---------------------------------------------------- |
| 1    | clk                                           | input     | Positive edge samples all signals.                   |
| 2    | rst_b                                         | input     | Active-low reset; resets the module.                 |
| 3    | zeroize                                       | output    | Zeroize indicator; clears KV data and status.        |
| 4    | abr_reg_hwif_in_o (abr_reg__in_t)             | output    | Register-block hardware inputs (KV ctrl/status, seeds, keys). |
| 5    | abr_reg_hwif_out_i (abr_reg__out_t)           | input     | Register-block outputs (KV rd/wr ctrl, MLDSA/MLKEM ctrl). |
| 6    | sampler_state_dv_i                            | input     | Sampler state data valid.                            |
| 7    | sampler_state_data_i[StateW-1:0]              | input     | Sampler (SHA3) state data.                           |
| 8    | aux_src0_base_addr_o[ABR_MEM_ADDR_WIDTH-1:0]  | output    | Aux unit source-0 base address.                      |
| 9    | kv_read[2:0] (kv_read_t)                      | output    | KV read requests: [0] MLDSA seed, [1] MLKEM seed, [2] MLKEM msg. |
| 10   | kv_rd_resp[2:0] (kv_rd_resp_t)                | input     | KV read responses (data, last, error).               |
| 11   | kv_write (kv_write_t)                         | output    | KV write request for the MLKEM shared key.           |
| 12   | kv_wr_resp (kv_wr_resp_t)                     | input     | KV write response (error).                           |
| 13   | pcr_signing_data (pcr_signing_t)              | input     | PCR signing seed data.                               |
| 14   | ocp_lock_in_progress                          | input     | OCP lock in progress; blocks reads of the OCP lock key release slot. |
| 15   | busy_o                                        | output    | Busy indicator.                                      |

For the KeyVault, abr_ctrl is responsible for the following tasks:
1. Reads the MLDSA seed, MLKEM seed and MLKEM msg from KV before the crypto operation starts
2. Selects the requested KV slot and writes the received words into the seed/msg registers
3. Locks the private key from the API when the secret was read from KV
4. Writes the MLKEM shared key to the requested KV slot with the requested destination valids
5. Reports KV ready/valid/error status and erases KV data on reset, zeroize and errors

## Assertion IP Overview

The Assertion IP signals are bound with the respective signals in the DUT. The assertions are
disabled during reset, using **disable iff (!pi_rst_b | po_zeroize)**, where **pi_rst_b** is bound
to `rst_b` and **po_zeroize** to `zeroize`. The read and write client state machines are modeled
with auxiliary logic, and the model is checked for equivalence with the RTL.

### fv_abr_ctrl_kv_read_aip.sv

The assertions cover the 3 KV read clients. In the names below, `***` is one of `mldsa_seed`,
`mlkem_seed` or `mlkem_msg`.

Requirement 1: Before computation starts, data from KV is read

- assert_kv_***_done_eq / assert_kv_***_ready_eq: Equivalence of the modeled KV client done and
  ready signals with the RTL

- assert_kv_***_offset_eq: Equivalence of the modeled word counter with kv_read.read_offset

- assert_if_busy_no_more_***_kv_read: Once the computation has started, no more KV reads happen

- assert_before_busy_kv_***_done: The KV read has completed before busy is asserted

- assert_kv_mldsa_seed_data_rd_integrity / assert_kv_mlkem_seed_d_data_rd_integrity /
  assert_kv_mlkem_seed_z_data_rd_integrity / assert_kv_mlkem_msg_rd_integrity: When the KV read
  is done, the seed/msg register holds the data read from KV

- assert_kv_mldsa_seed_data_stable / assert_kv_mlkem_seed_d_data_stable: Data read from KV is
  stable from the command until the end of the operation

- assert_mldsa_seed_we_kv_mldsa_seed_write_offset_high_match / _low_match (and the mlkem_seed
  equivalents): The HW write enable is asserted only with its corresponding write offset

- assert_sk_ram_msg_wr / assert_sk_ram_addr: The MLKEM msg read from KV is written to the SK RAM
  at the correct address

Requirement 2: Choose the specific slot meant for KV if it's a read

- assert_kv_***_rd_entry: The KV read uses the requested read_entry slot

Requirement 5: If a secret is read from KV then the associated writes shouldn't be from API

- assert_no_mldsa_secret_leaked_to_api / assert_no_mlkem_secret_leaked_to_api: If the seed came
  from KV, the private key lock is asserted and no data is leaked to the API

- assert_mldsa_default_lock_assertion / assert_mlkem_default_lock_assertion: The private key lock
  is asserted by default

- assert_lock_deasserted_after_mldsa_keygen / assert_lock_deasserted_after_mlkem_keygen: If the
  seed did not come from KV, the lock is released after keygen

Requirement 6: Reset/Zeroize erase the entire data to/from KV

- assert_erase_mldsa_seed_hw_write_enable / assert_erase_mlkem_seed_hw_write_enable: The seed HW
  write enables are reset

- assert_kv_erase_***_write_enable / assert_kv_erase_***_read_offset: The KV read client write
  enable and read offset are reset

- assert_mldsa_seed_hwclrs / assert_mlkem_seed_hwclrs: hwclr is asserted on KV read errors or
  zeroize

Requirement 7: No operation in the crypto engine without full read or write

- assert_no_crypto_engine_op_without_full_mldsa_read /
  assert_no_crypto_engine_op_without_full_mlkem_seed_read /
  assert_no_crypto_engine_op_without_full_mlkem_msg_read: No operation starts before a requested
  KV read has completed

- assert_no_mldsa_cmd_after_kv_mldsa_seed_error / assert_no_mlkem_cmd_after_kv_mlkem_seed_error /
  assert_no_mlkem_cmd_after_kv_mlkem_msg_error: A KV read error blocks new commands until
  zeroize

Requirement 8: In one mode, the KV outputs of the other mode are deasserted

- assert_no_mlkem_write_if_mldsa_mode / assert_no_mlkem_read_if_mldsa_mode: In MLDSA mode, the
  KV MLKEM read and write outputs are deasserted

- assert_no_mldsa_read_if_mlkem_mode: In MLKEM mode, the KV MLDSA read outputs are deasserted

Requirement 9: Primary Outputs assertions

- assert_kv_***_rd_ctrl_read_en_swwe / read_entry_swwe / rsvd_swwe / pcr_hash_extend_swwe: SW
  write enables of the KV read control register

- assert_kv_***_rd_ctrl_read_en_hwclr: read_en is cleared when the KV client is ready

- assert_kv_***_rd_status_ready / valid_hwclr / valid_hwset / error: KV read status register
  outputs

### fv_abr_ctrl_kv_write_aip.sv

The assertions target the KV MLKEM shared key write client.

Modeling of the state machine and write rules

- assert_kv_mlkem_sharedkey_done_eq / assert_kv_mlkem_sharedkey_ready_eq /
  assert_kv_mlkem_sharedkey_error: Equivalence of the modeled write client with the RTL

Requirement 3: Once the write is triggered it ends up in the specific slot of MLKEM

- assert_kv_mlkem_sharedkey_write_entry / write_en / offset: kv_write entry, enable and offset

- assert_kv_mlkem_sharedkey_write_dest_valid_high / _low: kv_write destination valids

Requirement 4: Write data value written to the KV is valid

- assert_kv_mlkem_sharedkey_write_data_integrity: The data written to KV is the shared key

- assert_kv_mlkem_sharedkey_data_stable: The shared key is stable during the KV write

Requirement 6: Reset/Zeroize erase the entire data to/from KV

- assert_kv_write_reset: kv_write is reset

Requirement 9: Primary Outputs assertions

- assert_kv_mlkem_sharedkey_***_swwe: SW write enables of the KV write control register (write_en,
  write_entry, each dest_valid field, rsvd)

- assert_kv_mlkem_sharedkey_write_en_hwclr: write_en is cleared by HW

- assert_kv_mlkem_sharedkey_wr_status_ready / valid_hwclr / valid_hwset / error: KV write status
  register outputs

Requirement 10: No writing to the SHARED_KEY API if data is written to or read from KV

- assert_no_sharedkey_api_write

Requirement 11: If the crypto engine is busy, no writes occur unless the rules are satisfied

- assert_no_mlkem_sharedkey_write_during_mldsa: No shared key KV write during an MLDSA operation

- assert_mlkem_busy_not_valid_no_sharedkey_write: No shared key KV write while MLKEM is busy and
  the write is not valid

### fv_abr_ctrl_kv_read_covers.sv / fv_abr_ctrl_kv_write_covers.sv

- cover_kv_***_done / cover_kv_***_read_offset / cover_kv_***_done_twice: Each read client
  completes a read, reaches every offset, and completes twice

- cover_mldsa_valid_twice / cover_mlkem_valid_twice / cover_mlkem_then_mldsa_valid /
  cover_mldsa_then_mlkem_valid / cover_kv_mldsa_seed_mlkem_seed_mlkem_msg_consecutive_requests:
  Back-to-back and mixed-mode operations

- cover_kv_write_en / entry / offset / data / dest_valid / cover_kv_write_en_and_dest_valid /
  cover_write_last / cover_kv_dest_data_avail / cover_dest_keyvault / cover_arc_rw_done: The
  shared key KV write reaches every phase

## Key Constraints

- Aux unit handshakes (compress, decompress, sigdecode_z/h, pkdecode, sigencode, normcheck,
  makehint, power2round, decompose, skencode, skdecode, sampler, ntt): assume_*_done,
  assume_*_done_eventually and assume_*_done_in_dly / _2cycles model the done timing of each aux
  unit. With `EVENTUAL_ASSUME`, done is asserted at an arbitrary time (eventually) instead of
  with fixed timing, to avoid starvation.

- KV control registers: assume_kv_***_rd_ctrl_*_stable / _clear / _rst and
  assume_kv_mlkem_sharedkey_wr_ctrl_*_stable / write_en_clear / write_en_reset keep the KV
  read/write control registers stable during an operation and model their clear and reset.

- KV responses: assume_kv_***_resp_data_zero_during_error, assume_mlkem_msg_last.

- Register interface: assume_mldsa_mlkem_ctrl_mutually_exclusive, the
  assume_if_*_for_2_cycles ordering between control and KV control register writes,
  assume_*_ctrl_value_hwclr, assume_pcr_sign_value_hwclr / _reset and the seed register
  assume_mldsa_seed_* / assume_mlkem_seed_* stable/clear/hwwrite/rst models.

- assume_ocp_lock_in_progress_stable: ocp_lock_in_progress is stable.

- Abstractions (disabled with `NO_ABSTRACTION`): assume_abstract_abr_prog_cntr_asm and the
  assume_abr_prog_cntr_*_symbolic_asm per-operation program-counter abstraction,
  assume_msg_cnt_abstracted_asm, assume_zeroize_mem_addr_abstracted_asm, together with cut points
  on the `*_process` signals.

- Zeroize: assume_zeroize_post_mldsa_valid / _mlkem_valid and assume_zeroize_pulse_*.

### Macros

- NO_ABSTRACTION: Used when IVA and cut points are not deployed, and to verify the abstracted
  counters.
- KV_ABR_PROG: Used for the KV-related checks, so that the KV interactions of the program
  counter abstraction work.
- EVENTUAL_ASSUME: The aux unit inputs are asserted at an arbitrary time instead of with fixed
  timing, to avoid starvation.
- KV_MLDSA_MODE / KV_MLKEM_MODE: Restrict the bench to a single mode by using
  fv_abr_ctrl_kv_mldsa_constraints or fv_abr_ctrl_kv_mlkem_constraints instead of fv_abr_ctrl_kv_constraints.
  In KV_MLDSA_MODE only the read AIP and read covers are instantiated. If neither is defined,
  the default constraints are used.

## Formal Setup
Use top `abr_ctrl`, defines `CALIPTRA` and `KV_ABR_PROG`, and cut points on `abr_prog_cntr`, `msg_cnt`,
`zeroize_mem_addr` and the MLDSA/MLKEM `*_process` signals. The design needs the Adams Bridge RTL
and the Caliptra KeyVault RTL (`kv_defines_pkg`, `kv_read_client`, `kv_write_client`, `kv_macros.svh`)
and caliptra_prim.

## Reproduce Results
The AIP has been tested and proven with atleast one of these formals tools (Onespin ,Jasper , vcf).

To reproduce the results:
Load the AIP with all the necessary constraints together in your formal tool.

Feel free to reach out to contact@lubis-eda.com to request the loadscripts or the lubis modules.
