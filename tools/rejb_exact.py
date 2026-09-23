# Exact underrun probability for the rej_bounded masked-Keccak PISO stall,
# using the same closed form as docs/AdamsBridge_MLDSA.md.
#   accepts in window ~ Bin( min(NS*(K-HOLD), 272), p_accept )
#   demand in window  = 4*(K-HOLD)
from math import log2
from fractions import Fraction
def comb(n,k):
    r=1
    for i in range(k): r = r*(n-i)//(i+1)
    return r
K = 109
NIB = 272          # half bytes per Keccak state (1088 bits / 4)

def p_under(hold, ns, p_num, p_den):
    w = K - hold
    if w <= 0: return 0.0
    n = min(ns*w, NIB)
    need = 4*w
    if need > n: return 1.0
    # P[Bin(n,p) < need]
    tot = 0.0
    for k in range(need):
        tot += comb(n,k) * (p_num**k) * ((p_den-p_num)**(n-k)) / (p_den**n)
    return tot

def table(ns, p_num, p_den, holds, label):
    print(f"--- {label}: NS={ns}, p={p_num}/{p_den}")
    for h in holds:
        v = p_under(h, ns, p_num, p_den)
        print(f"  HOLD={h:3d}  Pr={v:.3e}  log2={log2(v) if v>0 else float('-inf'):.1f}")

# reproduce the published eta=2 table as a model check
table(8, 15, 16, [45,47,49,55,59,65,75], "eta=2 (published)")
# eta=4, 8 lanes (what shipped before the fix)
table(8, 9, 16, [45,55,59,65,75], "eta=4 NS=8 (pre-fix)")
for ns in (12,16,20,24):
    table(ns, 9, 16, [59,70,80,85,90,95], f"eta=4 NS={ns}")

# ---------------------------------------------------------------------------
# Whole-polynomial supply: can the resident Keccak states cover 256 accepts?
# This is the residual the ABR_SAMPLER_PAD state closes. Each SHAKE256 squeeze
# supplies NIB = 272 half bytes; a polynomial needs 256 accepted coefficients.
#   Pr[fail with s squeezes] = Pr[ Bin(s*272, p) < 256 ]
# The pad is sized to always cover a fixed number of squeezes, so the residual
# is the probability that even that many squeezes fall short.
# ---------------------------------------------------------------------------
def p_short(squeezes, p_num, p_den, coeff=256):
    n = squeezes * NIB
    num = 0
    for k in range(coeff):
        num += comb(n, k) * (p_num**k) * ((p_den - p_num)**(n - k))
    return Fraction(num, p_den**n)

def poly_table(p_num, p_den, label, polys):
    print(f"--- whole polynomial supply, {label}: p={p_num}/{p_den}")
    for s in (2, 3, 4):
        v = p_short(s, p_num, p_den)
        f = float(v)
        l = log2(f) if f > 0 else (float(v.numerator.bit_length() - v.denominator.bit_length()))
        print(f"  {s} squeezes ({s*NIB:4d} half bytes) -> Pr={f:.3e}  log2={l:.1f}"
              f"   per keygen ({polys} polys) log2={l + log2(polys):.1f}")

poly_table(15, 16, "eta=2 / category 5", 15)   # ML-DSA-87: k=8 l=7
poly_table(9, 16, "eta=4 / ML-DSA-65", 11)     # ML-DSA-65: k=6 l=5
