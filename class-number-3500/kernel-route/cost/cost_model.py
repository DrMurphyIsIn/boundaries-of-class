"""Kernel cost model for the block sieve below a cut-off X (ESTIMATE, from MEASURED per-block constants).

Lanes: m = 3 (mod 4) with m < X (family A, d = m), and m = 1, 2 (mod 4) with 4m < X (families B, d = 4m); 3X/8 in all.
Per block of L lanes, the kernel walks every n <= Y_block once (Y = isqrt(d_min/4)), so the time per block is
affine in Y and nearly independent of L up to 10^5 (measured); memory grows with L and with Y.

MEASURED (h <= 1000 scratch builds, 2026-10-25, L = 10^5 lanes, Lean v4.34.1):
  Lean build of one block:       14.0 s at Y = 7555, 30.1 s at Y = 20027   (peak RSS 9.4 GB, 15.8 GB)
  Comparator, Lean-kernel replay: 28 s at Y = 7555, 43 s at Y = 20027, above a 7 s overhead
  Comparator, nanoda replay:       8 s at Y = 7555, 34 s at Y = 20027, above the same overhead
"""
import math, sys

def affine(y0, t0, y1, t1):
    b = (t1 - t0) / (y1 - y0); a = t0 - b * y0
    return a, b

def total(X, L, a, b, overhead=0.0):
    """CPU-seconds for all blocks below X: families A (d = m < X) and B (d = 4m < X)."""
    tot = 0.0
    # family A: m0 runs over [3, X) in steps of 4L; Y = isqrt((m0-1)/4)
    nA = 0; m0 = 3
    while m0 < X:
        Y = math.isqrt((m0 - 1) // 4); tot += overhead + a + b * Y; m0 += 4 * L; nA += 1
    # families B1, B2: m0 over [1, X/4) with Y = isqrt(m0 - 1), two residue classes
    nB = 0
    for _ in range(2):
        m0 = 1
        while 4 * m0 < X:
            Y = math.isqrt(max(m0 - 1, 0)); tot += overhead + a + b * Y; m0 += 4 * L; nB += 1
    return tot, nA + nB

X = int(sys.argv[1]) if len(sys.argv) > 1 else 28_000_000_000
aB, bB = affine(7555, 14.0, 20027, 30.1)      # Lean build
aL, bL = affine(7555, 28.0, 20027, 43.0)      # Comparator Lean replay (above overhead)
aN, bN = affine(7555, 8.0, 20027, 34.0)       # nanoda replay (above overhead)
aN = max(aN, 0.0)
print(f"X = {X:,}; lanes = {3*X//8:,}; Y_max (family A) = {math.isqrt(X//4):,}")
print(f"fits: build {aB:.2f} + {bB*1e3:.3f}e-3*Y s; Lean replay {aL:.1f} + {bL*1e3:.3f}e-3*Y; nanoda {aN:.1f} + {bN*1e3:.3f}e-3*Y")
for L in (100_000, 50_000, 25_000):
    tb, nb = total(X, L, aB, bB)
    tl, _ = total(X, L, aL, bL, overhead=7.0)
    tn, _ = total(X, L, aN, bN, overhead=7.0)
    h = lambda s: s / 3600
    print(f"L = {L:>7,}: {nb:>8,} blocks | Lean build {h(tb):>8,.0f} CPU-h | recompile audit {h(tb):>8,.0f} | "
          f"Comparator Lean {h(tl):>8,.0f} | nanoda {h(tn):>8,.0f} | sum {h(2*tb+tl+tn):>8,.0f}")
# first design (per-discriminant type tree), its recorded slices (not shipped): 3,994 us/radicand at N = 2000, 11,293 at N = 5000
for N, XN, us in ((2000, 7_800_000_000, 3994), (3500, X, 3994 + (11293 - 3994) * 0.5), (5000, 63_200_000_000, 11293)):
    r = 3 * XN // 8
    print(f"first design at N = {N} below X = {XN:.3g}: {r * us * 1e-6 / 3600:,.0f} CPU-h (single kernel pass; {us:.0f} us per radicand)")
# h <= 1000 sanity: X = 1.605e9 should give about 33 CPU-h for ~6,000 blocks (the measured estimate)
tb, nb = total(1_605_000_000, 100_000, aB, bB)
print(f"sanity, h <= 1000 range (X = 1.605e9, L = 1e5, whole range from 3): {nb:,} blocks, build {tb/3600:,.0f} CPU-h")
