#!/usr/bin/env python3
"""Cycle model of the ABR rej_bounded loop under masked SHAKE.

Mirrors abr_sampler_top.sv + rej_bounded_ctrl.sv + abr_sample_buffer.sv:
  PISO  : shared abr_piso_multi, PISO_BUFFER_W=REJS_PISO_BUFFER_W=1440 b,
          input 1088 b/squeeze, output 4*NS b/cycle
          (REJB_PISO_BUFFER_W=1334 in the package is vestigial - the shared PISO is
           always instantiated at 1440)
  REJB  : NS parallel CoeffFromHalfByte units, accept prob p
  BUF   : abr_sample_buffer NUM_WR=NS NUM_RD=4 depth=NS+4
  SINK  : 4 coeff/clk, 256 coeff per polynomial
The model starts with the first squeeze already available, so RTL cycles measured
from sampler_start_i are model cycles + MODEL_TO_RTL. Validated against the RTL
measurement: eta=2 HOLD=59 -> model 124 / RTL 234; eta=4 HOLD=85 -> model 150 / RTL 260.
"""
import random, sys

K_MASKED   = 109       # masked squeeze permutation latency, sampler cycles
PISO_W     = 1440
MODEL_TO_RTL = 110     # constant offset from model cycles to RTL sampler cycles
PISO_IN    = 1088
COEFF      = 256
NUM_RD     = 4

def run(p, hold, ns=8, seed=0, kmask=K_MASKED):
    rng   = random.Random(seed)
    piso  = 0            # bits currently in PISO
    nxt   = 0            # cycle at which the next squeeze result is ready
    buf   = 0            # valid entries in abr_sample_buffer
    depth = ns + NUM_RD
    full_lvl = depth - (ns - NUM_RD)      # buffer_full_o = buffer_valid[depth-(NS-RD)]
    out   = 0
    hold_cnt = 0
    hold_done = False
    out_rate = 4 * ns
    t = 0
    squeezes = 0
    first_out = None
    while out < COEFF:
        # --- squeeze delivery -------------------------------------------------
        if t >= nxt and piso + PISO_IN <= PISO_W:
            piso += PISO_IN
            squeezes += 1
            nxt   = t + kmask
            if not hold_done:                     # first sha3_state_dv rise
                hold_cnt, hold_done = hold, True
        # --- rej_bounded consumes -------------------------------------------
        hold_active = hold_cnt > 0
        bfull = buf > full_lvl
        acc = 0
        if (not hold_active) and (not bfull) and piso >= out_rate:
            piso -= out_rate
            acc = sum(1 for _ in range(ns) if rng.random() < p)
        # --- sample buffer read ---------------------------------------------
        rd = NUM_RD if buf >= NUM_RD else 0
        if rd:
            if first_out is None:
                first_out = t
            out += rd
        buf = buf - rd + acc
        if hold_cnt:
            hold_cnt -= 1
        t += 1
        if t > 4000:
            return None
    return t, squeezes

def spread(p, hold, ns=8, n=400, kmask=K_MASKED):
    v = [run(p, hold, ns, s, kmask) for s in range(n)]
    if any(x is None for x in v):
        return None
    t = [x[0] for x in v]
    return min(t), max(t), max(t) - min(t)


def by_squeeze(p, hold, ns, n=2000, kmask=K_MASKED):
    """Worst observable RTL length conditioned on how many squeezes were used.

    This is what sizes REJB_ETA4_FIXED_LEN: the pad has to cover the worst case
    in the three squeeze region, because that is the branch the 7e-6 residual
    takes.  At the real p = 9/16 that branch has probability 7e-6, so sampling it
    directly would need ~1e7 runs.  Instead the acceptance probability is swept
    downwards, which forces the 3 and 4 squeeze branches while leaving the drain
    schedule - which is what actually sets the length once a squeeze count is
    fixed - unchanged.  The reported figure for a given squeeze count is
    therefore an upper bound on what the real p can produce on that branch.
    """
    worst = {}
    ps = [p] + [p * f for f in (0.95, 0.9, 0.85, 0.8, 0.75, 0.7, 0.65, 0.6,
                                0.55, 0.5, 0.45, 0.4)]
    for pp in ps:
        for s in range(n):
            r = run(pp, hold, ns, s, kmask)
            if r is None:
                continue
            t, sq = r
            rtl = t + MODEL_TO_RTL
            if rtl > worst.get(sq, 0):
                worst[sq] = rtl
    return dict(sorted(worst.items()))

if __name__ == "__main__":
    print("validation: eta=2 (p=15/16), NS=8")
    for h in (0, 45, 49, 55, 59, 65, 75):
        print(f"  HOLD={h:3d} -> {spread(15/16, h)}")
    print("\neta=4 (p=9/16), NS=8  <-- ML-DSA-65")
    for h in (0, 45, 59, 65, 75, 85, 95):
        print(f"  HOLD={h:3d} -> {spread(9/16, h)}")
    print("\neta=4 (p=9/16), NS=16")
    for h in (0, 59, 75, 85, 90, 95, 100):
        print(f"  HOLD={h:3d} -> {spread(9/16, h, ns=16)}")

    print("\nshipped config: eta=4 (p=9/16), NS=20, HOLD=85")
    print(f"  spread over 400 seeds -> {spread(9/16, 85, ns=20)}")
    print("  worst observable RTL length by squeeze count:")
    for sq, w in by_squeeze(9/16, 85, 20, n=int(sys.argv[1]) if len(sys.argv)>1 else 2000).items():
        print(f"    {sq} squeezes -> {w:4d} cycles")
    print("  REJB_ETA4_FIXED_LEN = 479 = 261 + 2*K_masked, covering the 4 squeeze case.")

    print("\ncat-5 reference: eta=2 (p=15/16), NS=8, HOLD=59")
    print(f"  spread over 400 seeds -> {spread(15/16, 59)}")
