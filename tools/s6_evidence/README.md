# Session 6 verification evidence

Archived from `/tmp` because the shared scratch area is purge-prone and the
UVM report summary is the only reliable pass/fail record.

| File | What it is |
|---|---|
| `gate27_status.txt` | The final 27-test gate: one result line per test, parsed from the UVM report summary (`UVM_ERROR :` / `UVM_FATAL :`). `ALL_DONE` on the last line means the gate ran to completion; a missing summary is reported as `NOSUMMARY` and is never a pass. All 27 are `UVM_ERROR=0 UVM_FATAL=0`. |
| `*.summary` | The UVM report summary block of each test's `sim.log` from that same gate. |
| `rejb_profile_aggregate_final.txt` | Every `ABR_REJB_LEN` line from the gate, aggregated. 267 eta=2 activations all took 234 cycles, 99 eta=4 activations all took 260 - spread 0 in both bins. This is the constant-time claim measured rather than argued. |
| `s6_build_final.log` | The build the final gate ran against. |
| `s6_gate27.sh` | The gate itself: 27 tests in parallel batches of 4, with `+abr_rejb_profile`, no build step. |
| `s6_mix1.log`, `s6_mix_s12345.log`, `s6_mix_s987654.log` | Three extra seeds of `ML_DSA_MLKEM_param_set_mix_test`, the cross-parameter-set switching test. |
| `removability_build.log`, `removability_gate12_status.txt` | Build and 12-test category-5 gate with `ABR_MLDSA_44/65_ENABLED` and `ABR_MLKEM_512/768_ENABLED` commented out in `src/abr_top/rtl/abr_config_defines.svh` - the proof that the lower security levels elaborate away cleanly and do not perturb category 5. |
| `s6_gate_rem.sh` | The category-5-only subset used for that removability proof. |
| `gate_lib.sh` | `gate_report`, the UVM-summary parser. Grepping for `UVM_ERROR @` never matches, which is why the summary block is the only source used. |

Reproduce with `bash s6_gate27.sh` after a
`pb fe build --tb integration_lib::uvmf_mldsa --submit-timeout-arg 3600`.

Two infrastructure notes, both of which cost a gate run to learn:

- `--submit-timeout-arg N` is passed through to `job_wrapper --timeout N` and
  kills the simulator with `SIGKILL` at N seconds, log truncated mid-test. On a
  loaded farm `ML_DSA_externalmu_ACVP_KATs_test` exceeds 3600 s, so the gate
  uses 14400. A `died with <Signals.SIGKILL: 9>` traceback in the log is this,
  not a design failure.
- The same argument applies to `pb fe build`, where the default 720 s is a
  *pending* timeout: a build can fail with `BUILD_RC=246` without ever running.
