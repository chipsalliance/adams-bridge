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

# ABR CTRL (MLKEM & MLDSA)

## Folder Structure
The formal project has individual verification benches for different modules. These are listed under the toplevel directory named **formal**. Under this directory, we have a directory named **fv_abr_ctrl** for the module **abr_ctrl**.

The **formal/fv_abr_ctrl** contains the following files:

| File | Description |
|------|-------------|
| **fv_abr_ctrl_wrapper.sv** | Top-level AIP wrapper. Instantiates the constraints, whitebox, MLDSA whitebox, and MLDSA stream message modules. Also contains the `bind` statement that connects the AIP to the DUT. |
| **fv_abr_ctrl_constraints.sv** | Assumption properties that constrain all primary inputs to the DUT. |
| **fv_abr_ctrl_whitebox.sv** | MLKEM-specific whitebox assertions targeting memory interfaces, register assignments, scratch registers, and interrupts. |
| **fv_abr_ctrl_mldsa_whitebox.sv** | Comprehensive whitebox assertions covering all shared and MLDSA-specific DUT behaviors across 26 organized sections. |
| **fv_abr_ctrl_mldsa_stream_msg.sv** | Assertions targeting the MLDSA message streaming interface. |
| **fv_abr_ctrl_pkg.sv** | Package file that imports all required design packages into the AIP namespace. |
| **fv_abr_ctrl_dut.sv** | DUT wrapper that instantiates the `abr_ctrl` module with all its interfaces for use in the FV environment. |
| **model/mlkem.h** | High-level model of the MLKEM sequence of the controller. |
| **model/mlkem_abr_ctrl.sv** | Induction-style assertions generated from **model/mlkem.h** (see [Model-based assertions](#model-based-assertions)). |
| **model/mlkem_abr_ctrl_pkg.sv**, **model/mlkem_functions.sv** | Data structures and functions used by the generated assertions. |
| **model/mlkem_abr_ctrl_binding.sv** | Binding file connecting the generated assertions to the design. |


## DUT Overview

The DUT **abr_ctrl** has the primary inputs and primary outputs as shown below.

|--------------------------------------------------------------------------------------|
|direction|type                                        |name                           |
|---------|--------------------------------------------|-------------------------------|
|input    |logic                                       |clk                            |
|input    |logic                                       |rst_b                          |
|output   |logic                                       |zeroize                        |
|output   |abr_reg__in_t                               |abr_reg_hwif_in_o              |
|input    |abr_reg__out_t                              |abr_reg_hwif_out_i             |
|output   |abr_sampler_mode_e                          |sampler_mode_o                 |
|output   |logic                                       |sha3_start_o                   |
|output   |logic                                       |msg_start_o                    |
|output   |logic                                       |msg_valid_o                    |
|input    |logic                                       |msg_rdy_i                      |
|output   |logic [MsgStrbW-1:0]                        |msg_strobe_o                   |
|output   |logic [MsgWidth-1:0]                        |msg_data_o                     |
|output   |logic                                       |sampler_start_o                |
|input    |logic                                       |sampler_busy_i                 |
|input    |logic                                       |sampler_state_dv_i             |
|input    |logic [abr_sha3_pkg::StateW-1:0]            |sampler_state_data_i           |
|output   |logic [ABR_MEM_ADDR_WIDTH-1:0]              |dest_base_addr_o               |
|output   |logic [ABR_NUM_NTT-1:0]                     |ntt_enable_o                   |
|output   |abr_ntt_mode_e [ABR_NUM_NTT-1:0]            |ntt_mode_o                     |
|output   |ntt_mem_addr_t [ABR_NUM_NTT-1:0]            |ntt_mem_base_addr_o            |
|output   |pwo_mem_addr_t [ABR_NUM_NTT-1:0]            |pwo_mem_base_addr_o            |
|output   |logic [ABR_NUM_NTT-1:0]                     |ntt_masking_en_o               |
|output   |logic [ABR_NUM_NTT-1:0]                     |ntt_shuffling_en_o             |
|input    |logic [ABR_NUM_NTT-1:0]                     |ntt_busy_i                     |
|output   |logic [1:0][ABR_MEM_ADDR_WIDTH-1:0]         |aux_src0_base_addr_o           |
|output   |logic [1:0][ABR_MEM_ADDR_WIDTH-1:0]         |aux_src1_base_addr_o           |
|output   |logic [1:0][ABR_MEM_ADDR_WIDTH-1:0]         |aux_dest_base_addr_o           |
|output   |logic                                       |power2round_enable_o           |
|input    |mem_if_t [1:0]                              |pwr2rnd_keymem_if_i            |
|input    |logic [1:0][DATA_WIDTH-1:0]                 |pwr2rnd_wr_data_i              |
|input    |logic                                       |pk_t1_wren_i                   |
|input    |logic [7:0][9:0]                            |pk_t1_wrdata_i                 |
|input    |logic [7:0]                                 |pk_t1_wr_addr_i                |
|input    |logic                                       |power2round_done_i             |
|output   |logic                                       |decompose_enable_o             |
|output   |logic                                       |decompose_mode_o               |
|input    |logic                                       |decompose_done_i               |
|output   |logic                                       |skencode_enable_o              |
|input    |mem_if_t                                    |skencode_keymem_if_i           |
|input    |logic [DATA_WIDTH-1:0]                      |skencode_wr_data_i             |
|input    |logic                                       |skencode_done_i                |
|output   |logic                                       |skdecode_enable_o              |
|input    |mem_if_t [1:0]                              |skdecode_keymem_if_i           |
|output   |logic [1:0][DATA_WIDTH-1:0]                 |skdecode_rd_data_o             |
|input    |logic                                       |skdecode_done_i                |
|input    |logic                                       |skdecode_error_i               |
|output   |logic                                       |makehint_enable_o              |
|input    |logic                                       |makehint_invalid_i             |
|input    |logic                                       |makehint_done_i                |
|input    |logic                                       |makehint_reg_wren_i            |
|input    |logic [3:0][7:0]                            |makehint_reg_wrdata_i          |
|input    |logic [ABR_MEM_ADDR_WIDTH-1:0]              |makehint_reg_wr_addr_i         |
|output   |logic                                       |normcheck_enable_o             |
|output   |logic [1:0]                                 |normcheck_mode_o               |
|input    |logic                                       |normcheck_invalid_i            |
|input    |logic                                       |normcheck_done_i               |
|output   |logic                                       |sigencode_enable_o             |
|input    |mem_if_t                                    |sigencode_wr_req_i             |
|input    |logic [1:0][3:0][19:0]                      |sigencode_wr_data_i            |
|input    |logic                                       |sigencode_done_i               |
|output   |logic                                       |pkdecode_enable_o              |
|input    |logic [7:0]                                 |pkdecode_rd_addr_i             |
|output   |logic [7:0][T1_COEFF_W-1:0]                 |pkdecode_rd_data_o             |
|input    |logic                                       |pkdecode_done_i                |
|output   |logic                                       |sigdecode_h_enable_o           |
|output   |logic [SIGNATURE_H_VALID_NUM_BYTES-1:0][7:0]|signature_h_o                  |
|input    |logic                                       |sigdecode_h_invalid_i          |
|input    |logic                                       |sigdecode_h_done_i             |
|output   |logic                                       |sigdecode_z_enable_o           |
|input    |mem_if_t                                    |sigdecode_z_rd_req_i           |
|output   |logic [1:0][3:0][19:0]                      |sigdecode_z_rd_data_o          |
|input    |logic                                       |sigdecode_z_done_i             |
|output   |logic                                       |compress_enable_o              |
|output   |compress_mode_t                             |compress_mode_o                |
|output   |logic                                       |compress_compare_mode_o        |
|output   |logic [2:0]                                 |compress_num_poly_o            |
|input    |logic                                       |compress_done_i                |
|input    |logic                                       |compress_compare_failed_i      |
|input    |logic [1:0]                                 |compress_api_rw_en_i           |
|input    |logic [ABR_MEM_ADDR_WIDTH-1:0]              |compress_api_rw_addr_i         |
|input    |logic [DATA_WIDTH-1:0]                      |compress_api_wr_data_i         |
|output   |logic [DATA_WIDTH-1:0]                      |compress_api_rd_data_o         |
|output   |logic                                       |decompress_enable_o            |
|input    |logic                                       |decompress_done_i              |
|output   |decompress_mode_t                           |decompress_mode_o              |
|output   |logic [2:0]                                 |decompress_num_poly_o          |
|input    |logic                                       |decompress_api_rd_en_i         |
|input    |logic [ABR_MEM_ADDR_WIDTH-1:0]              |decompress_api_rd_addr_i       |
|output   |logic [1:0][DATA_WIDTH-1:0]                 |decompress_api_rd_data_o       |
|output   |logic                                       |lfsr_enable_o                  |
|output   |logic [1:0][LFSR_W-1:0]                     |lfsr_seed_o                    |
|output   |mem_if_t                                    |zeroize_mem_o                  |
|input    |logic                                       |debugUnlock_or_scan_mode_switch|
|output   |logic                                       |busy_o                         |
|output   |logic                                       |error_intr                     |
|output   |logic                                       |notif_intr                     |


## Assertion IP Overview
The Assertion IP signals are bound with the respective signals in the DUT via `fv_abr_ctrl_wrapper.sv`. The wrapper instantiates four sub-modules, each targeting a distinct verification concern.

### fv_abr_ctrl_constraints.sv
Contains `assume` properties that constrain all primary inputs to create a legal stimulus environment. Key constraint groups include:

- **Auxiliary unit handshakes** — For each auxiliary unit (compress, decompress, sampler, NTT, power2round, decompose, skencode, skdecode, makehint, normcheck, sigencode, pkdecode, sigdecode_h, sigdecode_z), constraints enforce that `done` and error signals can only assert after the corresponding `enable` has been raised, and that completions occur within a bounded delay (`FV_ADAMSBRIDGE_AUX_DLY`).
- **MLDSA auxiliary units** — A property (`no_mldsa_aux_units`) captures that MLDSA-specific auxiliary signals remain idle when the design is operating in MLKEM mode.
- **MSG streaming interface** — Constraints on the MLDSA message streaming path enforce valid/ready protocol correctness: the input valid toggles at least once per cycle, the strobe has no internal bubbles, and the keccak ready counter ensures the message loader can make progress.
- **Register interface stability** — MLDSA and MLKEM control registers, entropy inputs, sign-random values, and context registers are constrained to be stable while `abr_ready` is de-asserted (i.e., during an active operation).
- **Mutual exclusivity** — API memory requests (encaps key, decaps key, message, ciphertext, private key, public key, signature) are constrained to be one-hot at any given time. MLDSA control, MLKEM control, and Key Vault read-control registers are also mutually exclusive.
- **Key Vault (KV) interface** — Constraints model the stable and clear behavior of the `kv_mldsa_seed_rd_ctrl`, `kv_mlkem_seed_rd_ctrl`, and `kv_mlkem_msg_rd_ctrl` registers, including hardware-clear and software-write-enable conditions.
- **Seed register modeling** — Per-dword constraints for `MLDSA_SEED` model hardware-write, hardware-clear, and software-write conditions to abstract the register behavior.

Compile-time macros:
- `NO_ABSTRACTION` — Disables IVA and cut-points; used to verify the counter abstraction directly.
- `EVENTUAL_ASSUME` — Replaces bounded-delay completion constraints with liveness (`s_eventually`) assumptions to avoid starvation.
- `CALIPTRA` — Enables the Key Vault (KV) interface constraints for `kv_mldsa_seed_rd_ctrl`, `kv_mlkem_seed_rd_ctrl`, and `kv_mlkem_msg_rd_ctrl`, including stability, clear, and mutual-exclusivity assumptions. Without this macro the KV constraint blocks are not compiled.

### fv_abr_ctrl_whitebox.sv
Contains `assert` properties targeting MLKEM-specific DUT behaviors observed through internal signals. Key assertion groups include:

- **Reset and zeroize** — Verifies that internal registers (`mlkem_valid_reg`, `abr_scratch_reg`, `error_flag_reg`, `msg_cnt`) are correctly cleared after reset or zeroize.
- **SK memory interface** — Asserts that the two SK SRAM bank outputs (write enable, write address, write data, read enable, read address) match the expected values derived from all possible write sources: API (decaps key, encaps key, ciphertext, message), compress, and zeroize counter.
- **Compress and decompress read data** — Asserts that `compress_api_rd_data_o` and `decompress_api_rd_data_o` are correctly muxed from SK bank read data.
- **MLKEM register interface** — Asserts the correctness of MLKEM name, version, ready, valid, and error status outputs; seed-D write-enable, hardware-clear, and next-value assignments; seed-Z write acknowledgement; and shared-key read acknowledgement and data.
- **API memory read/write acknowledgements** — Asserts that decaps key, encaps key, ciphertext, and message register read/write acknowledgement signals are correctly driven.
- **Scratch register updates** — Verifies that `abr_scratch_reg` fields (rho, sigma, tr, shared_key) are updated at the correct cycle in response to sampler data-valid events and API writes.
- **Sampler SK read enable and offset** — Asserts that the SK RAM read enable and read offset used for feeding data into the sampler are correctly qualified by the program counter and message counter for encapsulation key, message, and ciphertext transfers.
- **Zeroize memory counter** — Asserts that the memory write interface is active during the `ABR_ZEROIZE` program counter state and idle otherwise. The address field check is guarded by `ifndef KV_ABR_PROG` because when prog_cntr abstraction is active the counter-derived address is not meaningful.
- **NTT/PWO memory base addresses** — Asserts that NTT and PWO source/destination base addresses match the operand fields of the current instruction.
- **Error flag** — Asserts the precise conditions under which the error flag is set (compress compare failure during encaps, or TR mismatch during decaps) and that it is not set otherwise.
- **Interrupts** — Asserts that `error_intr` and `notif_intr` correctly reflect the hardware interrupt register outputs, and that internal interrupt set signals (`hwset`) are driven at the right events.
- **Control registers** — Asserts reset and hardware-clear behavior of MLDSA and MLKEM control registers, the zeroize signal derivation, and the `abr_ready` signal assignment.
- **MLKEM recombine control** — Asserts that `recombine_mode_o` matches the RTL decode (MLKEM modulus for `MLKEM_PWS` and `MLKEM_COMPRESS`) and that the fused-recombine consumers `MLKEM_PWS_R` and `COMPRESS_R` select the MLKEM modulus; a cover shows an MLKEM recombine instruction is reachable.

Compile-time macros:
- `CALIPTRA` — Enables Key Vault-aware assertion variants for seed, shared-key, and `abr_ready` checks.
- `KV_ABR_PROG` — Enables abstraction on `prog_cntr` by cutting it from the design, allowing the formal tool to reach deep states that would otherwise require many unrolling steps. Assertions that directly depend on the concrete value of `prog_cntr` (such as the zeroize memory address check) are disabled under this macro.

### fv_abr_ctrl_mldsa_whitebox.sv
Comprehensive whitebox assertion module covering shared infrastructure and all MLDSA-specific DUT behaviors. The file is organized into 26 sections:

1. Reset and Zeroization (power-on and debug-unlock)
2. Hardware Interface Combinational Outputs (HWIF)
3. Per-Word Register Checks (entropy, seed, message)
4. Memory Interface Outputs (SK, SIG_Z, PK RAMs)
5. Zeroize Memory Counter
6. Internal Scratch Register Updates (K, rho, tr)
7. Signature Register Updates (c, h fields)
8. rho_p Register Management
9. LFSR Entropy Management (XOR and fresh seed)
10. API Read-Data Multiplexer (priority encoder A3–A8)
11. API Read-Data Stability and Decode Signals
12. Private/Public Key Read Paths (register vs SRAM)
13. Error Flag Management (set and clear paths)
14. Valid Register Status (MLDSA and MLKEM)
15. Message Strobe Interface (SHA3 byte masking)
16. Message Counter (`NO_ABSTRACTION` build)
17. Verify/Sign Valid Flags (rejection sampling)
18. Key Lock Mechanism (KV isolation enforcement)
19. Keyvault Registers (`CALIPTRA` build)
20. APB Read Acknowledge Signals
21. HWIF Latency and Read Data Completeness
22. MLKEM Interface Completeness
23. Memory Read Data Paths and Valid Signals
24. Control Outputs (NTT, normcheck, busy, decompose, split enable, recombine enable/mode: `recombine_en_o` decode, idle in reset/zeroize, split/recombine exclusivity, legal fused-recombine consumers, MLDSA modulus selection)
25. Output Packing (signature H, LFSR seed)
26. Cover Properties (liveness checks)

### fv_abr_ctrl_mldsa_stream_msg.sv
Contains assertions targeting the MLDSA message streaming path through the Keccak/SHA3 interface. Verifies the correctness of message data, strobe, and valid/ready handshake signals as the controller loads message data into the hash engine during MLDSA signing and verification operations.

### fv_abr_ctrl_pkg.sv
Package file that imports all required design packages (`abr_params_pkg`, `abr_sampler_pkg`, `abr_ctrl_pkg`, `abr_sha3_pkg`, `abr_reg_pkg`, `ntt_defines_pkg`, `compress_defines_pkg`, `decompress_defines_pkg`) into the `fv_abr_ctrl_pkg` namespace for use across all AIP modules.

### fv_abr_ctrl_dut.sv
DUT wrapper module (`fv_abr_ctrl_dut`) that instantiates the `abr_ctrl` top-level design with all its interfaces exposed, providing the target for the bind statement in `fv_abr_ctrl_wrapper.sv`.

Compile-time macros:
- `CALIPTRA` — Adds the Key Vault (`kv_read_t`, `kv_rd_resp_t`, `kv_write_t`, `kv_wr_resp_t`) and PCR signing ports to the DUT wrapper interface.
- `RV_FPGA_SCA` — Exposes additional SCA trigger output ports (`NTT_trigger`, `PWM_trigger`, `PWA_trigger`, `INTT_trigger`) for FPGA-based side-channel analysis measurements.


### Model-based assertions
The assertions in **model/mlkem_abr_ctrl.sv** verify the triggers to the submodules compress, decompress, samplers and ntt, along with the addresses and data sent to keccak. They are induction checks: every event in the state machine, and every state itself, is an assertion, which gives confidence that the entire sequential state machine is unrolled and all states are covered. The checkers are generated from the high-level model **model/mlkem.h**. This allows the formal tool to apply Initial Value Abstraction on `abr_prog_cntr` (the main driver of the controller) and counter abstraction on `msg_cnt`.

## Formal Setup
This AIP instantiates the following LUBIS library modules, which are not part of this repository: `lubis_scoreboard`, `lubis_incr_decr_counter_m`.

Load all the .sv files under formal/fv_abr_ctrl (excluding the model folder) with the design.

## Reproduce Results
The AIP has been tested and proven with atleast one of these formals tools (Onespin ,Jasper , vcf).

To reproduce the results:
Load the AIP with all the necessary constraints together in your formal tool.

Feel free to reach out to contact@lubis-eda.com to request the loadscripts or the lubis modules.
