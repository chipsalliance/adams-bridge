#!/usr/bin/env python3
"""Cycle model of the ABR rej_bounded loop under masked SHAKE.

Mirrors abr_sampler_top.sv + rej_bounded_ctrl.sv + abr_sample_buffer.sv:
  PISO  : REJB_PISO_BUFFER_W=1334 b, input 1088 b/squeeze, output 4*NS b/cycle
  REJB  : NS parallel CoeffFromHalfByte units, accept prob p
  BUF   : abr_sample_buffer NUM_WR=NS NUM_RD=4 depth=NS+4
  SINK  : 4 coeff/clk, 256 coeff per polynomial
Validated against the documented cat-5 result: eta=2, HOLD=59 -> 237 cycles, spread 0.
"""
import random, sys

K_MASKED   = 109       # masked squeeze permutation latency, sampler cycles
PISO_W     = 1334
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
    first_out = None
    while out < COEFF:
        # --- squeeze delivery -------------------------------------------------
        if t >= nxt and piso + PISO_IN <= PISO_W:
            piso += PISO_IN
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
    return t

def spread(p, hold, ns=8, n=400, kmask=K_MASKED):
    v = [run(p, hold, ns, s, kmask) for s in range(n)]
    if any(x is None for x in v):
        return None
    return min(v), max(v), max(v) - min(v)

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
