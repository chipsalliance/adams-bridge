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
