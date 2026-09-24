# Session 7 verification evidence

Two gates plus a negative control. Same parsing rules as `../s6_evidence/`:
pass/fail comes from the UVM report summary block, never from `UVM_ERROR @`.

| File | What it is |
|---|---|
| `gateA_status.txt`, `gateB_status.txt` | Two full 27-test gates, one result line per test. |
| `*.summary` | The UVM report summary block of each test's `sim.log`. |
| `rejb_profile_gateA.txt`, `rejb_profile_gateB.txt` | `ABR_REJB_LEN` / `ABR_REJB_WTRACE` lines from each gate. `obs` is the observable length and carries the constant-time claim; `nat` is the pre-pad natural length. |
| `negative_control.txt` | `REJB_NUM_SAMPLERS_ETA4` starved from 20 to 8. The natural length becomes seed dependent (`natspread=7`, 260..267) and the internal write trace stretches with it (`lastspread=7`), while the observable length stays pinned at 481 with `spread=0`. This is what shows `ABR_SAMPLER_PAD` is doing the work rather than a comfortable supply margin hiding the problem. |
| `s7_gate27B.sh`, `s7_negctl.sh`, `gate_lib7.sh` | The gate and negative-control drivers, and the UVM-summary parser. |

Note on a deleted artifact: earlier revisions of this branch carried a
`removability_status.txt` recording that a category-5-only build elaborated with
the non-category-5 parameter sets `ifdef`-ed out. That build-time configuration
was removed during review - every parameter set is now always present and is
selected at run time through `PARAM_SET` - so the property no longer exists and
the evidence for it was deleted rather than left to imply otherwise.
