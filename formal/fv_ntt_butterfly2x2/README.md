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

# ntt_butterfly2x2

## Folder Structure
The following files are part of the main directory **formal/fv_ntt_butterfly2x2**

- **fv_ntt_butterfly2x2.sv** contains the assertion IP (AIP) for the ntt_butterfly2x2 module —
  the reference model functions (CT/GS/PWM/PWA/PWS/pairwm, MLDSA and MLKEM/Karatsuba variants),
  the per-mode output-correctness properties, and the white-box internal wiring checks, all
  defined locally in this file

- **fv_ntt_butterfly2x2_constraints.sv** contains the assumptions/constraints for
  fv_ntt_butterfly2x2 module

- **fv_ntt_butterfly2x2_top.sv** is the top-level wrapper that binds fv_ntt_butterfly2x2 (AIP)
  with fv_ntt_butterfly2x2_constraints attached

- **fv_ntt_butterfly2x2_binding.sv** contains the direct binding between the AIP instance
  (fv_ntt_butterfly2x2) & DUT (ntt_butterfly2x2), without the constraints — load only one of
  fv_ntt_butterfly2x2_top.sv or this file, not both

- **model/ntt_butterfly2x2.h** is the SystemC/ESL reference model header used to cross-check the reference
  functions against the algorithmic (C++/SystemC) golden model

- **fv_ntt_butterfly2x2.cpp** is the C++/SystemC golden reference model of the butterfly, used
  to derive/cross-check the AIP reference functions

- **model/** is reserved for a high level abstracted model (currently empty for this block; the
  reference model is embedded directly in fv_ntt_butterfly2x2.sv / model/ntt_butterfly2x2.h instead)


## DUT Overview

The DUT has the primary inputs and primary outputs as shown below.

| S.No | Port                  | Direction | Description                                         |
| ---- | --------------------- | --------- | --------------------------------------------------- |
| 1    | clk                   | input     | Clock; edge-sample reference for all signals.       |
| 2    | reset_n               | input     | Active-low reset; clears regs and outputs.          |
| 3    | zeroize               | input     | Forces regs/outputs to their initial value.         |
| 4    | mode                  | input     | Mode: ct(0) gs(1) pwm(2) pwa(3) pws(4) pairwm(5).   |
| 5    | enable                | input     | Starts computation for the selected mode.           |
| 6    | uvw_i (bf_uvwi_t)     | input     | CT/GS operands incl. stage-1/2 twiddles.            |
| 7    | pw_uvw_i (pwo_uvwi_t) | input     | 4-lane PWM/PWA/PWS/pairwm operands + accumulate in. |
| 8    | accumulate            | input     | Selects accumulate vs. non-accumulate variant.      |
| 9    | mlkem                 | input     | Selects MLKEM(Q=3329) vs MLDSA(Q=8380417).          |
| 10   | mlkem_pairwm_zeta13_i | input     | Karatsuba zeta factors z0_i, z1_i.                  |
| 11   | uv_o (bf_uvo_t)       | output    | CT/GS stage-2 results u20_o/u21_o/v20_o/v21_o.      |
| 12   | pwo_uv_o (pwo_t)      | output    | PWM/PWA/PWS/pairwm results uv0..uv3.                |
| 13   | ready_o               | output    | Valid-result pulse (mode-dependent latency).        |

The ntt_butterfly2x2 module implements a 2x2 (two-stage, two-lane) NTT/INTT butterfly datapath
that is shared across all NTT operating modes (CT, GS, PWM, PWA, PWS, pairwm) for both MLDSA and
MLKEM. It takes the CT/GS operand bundle or the pointwise operand bundle as input, performs the
selected MLDSA/MLKEM butterfly, pointwise-multiply/add/sub or Karatsuba pairwise-multiply
operation, and produces the corresponding result together with a ready_o pulse once the
mode-specific pipeline latency has elapsed.

## Assertion IP Overview

The Assertion IP signals are bound with the respective signals in the dut, either through
fv_ntt_butterfly2x2_top.sv (with the constraints attached) or directly through
fv_ntt_butterfly2x2_binding.sv — load only one of the two.

- run_reset_a: Checks that all outputs are zero on the cycle after reset_n deasserts

- run_CT_a / run_CT_mlkem_a: Checks all outputs during CT mode (MLDSA / MLKEM)

- run_GS_a / run_GS_mlkem_a: Checks all outputs during GS mode (MLDSA / MLKEM)

- run_PWM_a / run_PWMA_a: Checks all outputs during PWM non-accumulate / accumulate mode (MLDSA)

- run_PWA_a / run_PWA_mlkem_a: Checks all outputs during PWA mode (MLDSA / MLKEM)

- run_PWS_a / run_PWS_mlkem_a: Checks all outputs during PWS mode (MLDSA / MLKEM)

- run_pairwm_a: Checks pairwm mode, non-accumulate, against the internal Karatsuba
  pairwm_uv01_o/pairwm_uv23_o results (wiring/mux check)

- run_pairwm_accumulate_a: Checks that ready_o is asserted after MLKEM_PAIRWM_ACC_LATENCY in
  pairwm accumulate mode

- run_pairwm_computation_a: Checks pairwm mode, non-accumulate, against an independent Karatsuba
  reference (arithmetic check)

- run_pairwm_accumulate_computation_a: Same as run_pairwm_computation_a, for pairwm accumulate mode

### White-box Wiring Checks (wb_*)

These properties check the internal signal routing of ntt_butterfly2x2 (mode decode,
input/output muxing, register wiring), independent of the arithmetic correctness already covered
above:

1. Mode decode: wb_pwo_mode_decode_a, wb_pairwm_mode_decode_a

2. Stage-1 input mux, NTT/GS mode (bf_inst00/01 from uvw_i): wb_bf00_ntt_opu_a,
   wb_bf00_ntt_opv_a, wb_bf00_ntt_opw_a, wb_bf01_ntt_opu_a, wb_bf01_ntt_opv_a, wb_bf01_ntt_opw_a

3. Stage-1 input mux, PWO/pairwm mode (bf_inst00/01 from pw_uvw_i lanes 0/1): wb_bf00_pwo_opu_a,
   wb_bf00_pwo_opv_a, wb_bf00_pwo_opw_a, wb_bf01_pwo_opu_a, wb_bf01_pwo_opv_a, wb_bf01_pwo_opw_a

4. Stage-2 input mux, PWO/pairwm mode (bf_inst10/11 from pw_uvw_i lanes 2/3): wb_bf10_pwo_opu_a,
   wb_bf10_pwo_opv_a, wb_bf10_pwo_opw_a, wb_bf11_pwo_opu_a, wb_bf11_pwo_opv_a, wb_bf11_pwo_opw_a

5. Stage-1 → Stage-2 crossbar (NTT/GS mode): wb_crossbar_u10_a, wb_crossbar_v10_a,
   wb_crossbar_u11_a, wb_crossbar_v11_a

6. Stage-2 twiddle input mux (MLDSA vs. MLKEM): wb_bf10_twiddle_mldsa_a,
   wb_bf11_twiddle_mldsa_a, wb_bf10_twiddle_mlkem_a, wb_bf11_twiddle_mlkem_a

7. Twiddle shift-register load and propagation: wb_mlkem_w10_reg_load_a,
   wb_mlkem_w11_reg_load_a, wb_mldsa_w10_reg_propagate_a, wb_mldsa_w11_reg_propagate_a,
   wb_mlkem_w10_reg_propagate_a, wb_mlkem_w11_reg_propagate_a

8. Twiddle shift-registers cleared by reset: wb_twiddle_reg_reset_a

9. Stage-2 output wiring to po_uv_o: wb_stage2_u20_a, wb_stage2_v20_a, wb_stage2_u21_a,
   wb_stage2_v21_a

10. MLDSA PWO collection (bf pwm_res_o → mldsa_pwo_uv_o lanes): wb_mldsa_pwo_uv0_a,
    wb_mldsa_pwo_uv1_a, wb_mldsa_pwo_uv2_a, wb_mldsa_pwo_uv3_a

11. Final PWO output mux (MLKEM pairwm vs. MLDSA): wb_pwo_out_uv0_mux_a, wb_pwo_out_uv1_mux_a,
    wb_pwo_out_uv2_mux_a, wb_pwo_out_uv3_mux_a

12. Karatsuba pairwm input wiring (active only in pairwm mode): wb_pairwm_uvw01_u0_a,
    wb_pairwm_uvw01_v0_a, wb_pairwm_uvw01_w0_a, wb_pairwm_uvw01_u1_a, wb_pairwm_uvw01_v1_a,
    wb_pairwm_uvw01_w1_a, wb_pairwm_uvw23_u0_a, wb_pairwm_uvw23_v0_a, wb_pairwm_uvw23_w0_a,
    wb_pairwm_uvw23_u1_a, wb_pairwm_uvw23_v1_a, wb_pairwm_uvw23_w1_a

13. Karatsuba pairwm structs forced to zero when not in pairwm mode: wb_pairwm_uvw01_zero_a,
    wb_pairwm_uvw23_zero_a

14. Karatsuba m0/m1 tap connections from bf *_pairwm_mul_red_o: wb_karatsuba0_m0_a,
    wb_karatsuba0_m1_a, wb_karatsuba1_m0_a, wb_karatsuba1_m1_a

15. Karatsuba zeta connections (mlkem_pairwm_zeta13_i): wb_karatsuba0_zeta_a, wb_karatsuba1_zeta_a

16. ready_o is directly driven from ready_reg[0]: wb_ready_o_a

17. ready_reg clears on an undefined mode encoding : undef_mode_ready_a

## Constraints

The following assumptions in fv_ntt_butterfly2x2_constraints.sv shape the formal input space:

- assume_stable_acc / assume_stable_mode / assume_stable_mlkem: accumulate, mode and mlkem are
  held stable while the design is out of reset/zeroize (they are only expected to change between
  operations)

- pw_uvw_i_a: pw_uvw_i is forced to 0 in the cycle right after reset/zeroize

- assume_q_mlkem / assume_q_mldsa: All CT/GS/PWO operands are constrained below MLKEM_Q (3329)
  when mlkem==1, and below MLDSA_Q (8380417) when mlkem==0, matching the valid field range of
  each algorithm

- assume_mlkem_zeta_range: The MLKEM Karatsuba zeta inputs (z0_i, z1_i) are constrained below
  MLKEM_Q

## Reproduce Results
The AIP has been tested and proven with atleast one of these formals tools (Onespin ,Jasper , vcf).

To reproduce the results:
Load the AIP with all the necessary constraints together in your formal tool.

Feel free to reach out to contact@lubis-eda.com to request the loadscripts or the lubis modules.
