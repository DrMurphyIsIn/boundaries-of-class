"""Numbers quoted in revision 3 of the paper (the version 2 statements), recomputed in floating point (mpmath, 30 digits).
Not a proof and not a certification: the theorems are the Lean statements; this script only checks the numbers the text
quotes about them (margins, asymptotics, boundary values, comparisons). Output: paper_numbers_v2.out, next to this script. Input: data/max_disc_by_class_number.txt.
"""
import os

import mpmath as mp

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "data", "max_disc_by_class_number.txt")

mp.mp.dps = 30
pi, e = mp.pi, mp.e
out = []


def p(*a):
    s = " ".join(str(x) for x in a)
    print(s)
    out.append(s)


def n(x, k=6):
    return mp.nstr(x, k)


def kap(x):
    return mp.exp(-x) / (1 - mp.exp(-x)) ** 2


def H(d, s):
    """1 + P/m: the per-class-floor bound with the K_{1/2} remainder (the derivation of r2_recheck.py)."""
    d, s = mp.mpf(d), mp.mpf(s)
    dl, nu = 1 - s, s - mp.mpf(1) / 2
    Z = mp.zeta(2 * s)
    K = pi ** s * mp.gamma(nu) / mp.gamma(s) * (4 / (pi * d)) ** nu * abs(mp.zeta(2 * s - 1))

    def E(a):
        c = pi * mp.sqrt(d) / (2 * a)
        return pi ** s / (2 * mp.gamma(s)) * a ** (-mp.mpf(1) / 2) * (2 / mp.sqrt(d)) ** nu * mp.sqrt(pi / c) * 4 * kap(2 * c)

    ustar = (dl * K / (s * Z)) ** (dl / (1 - 2 * dl))
    P = Z - K - E(1)
    m = (1 - dl / s) * K * ustar + E(2 * mp.sqrt(d) / 3)
    return 1 + P / m


p("== 1. (L'): H(d, sigma) log d / sqrt d, sigma = 7/8 for log d <= 16 and 1 - 2/log d beyond")
for L in [8, 9, 10, 12, 14, 16, 20, 30, 50, 100, 1000]:
    L = mp.mpf(L)
    s = mp.mpf(7) / 8 if L <= 16 else 1 - 2 / L
    p("  L =", n(L, 5), " value =", n(H(mp.e ** L, s) * L / mp.sqrt(mp.e ** L), 6))
p("  relative margin of 1/3 at L = 8:", n(H(mp.e ** 8, mp.mpf(7) / 8) * 8 / mp.sqrt(mp.e ** 8) * 3 - 1, 4))
p("  limit 2 zeta(2)/(pi e) =", n(2 * mp.zeta(2) / (pi * e), 6), "; v1 chain limit 13/(8 pi e) =", n(mp.mpf(13) / (8 * pi * e), 6))

p("== 2. (P'): H(d, 7/8)/d^(7/16) and its reciprocal")
for d in [1000, 3166, 39001, 10 ** 6, 10 ** 9, 2 ** 40, 10 ** 20, 10 ** 40]:
    v = H(d, mp.mpf(7) / 8) / mp.mpf(d) ** (mp.mpf(7) / 16)
    p("  d =", d, " H/d^(7/16) =", n(v, 6), " = 1/", n(1 / v, 6))
p("  (P') beats d^(3/8)/12 for d >= (17/12)^16 =", n((mp.mpf(17) / 12) ** 16, 6))

p("== 3. the thresholds: kernel-checked X_N against H at sigma = 7/8")
TX = [(1, 660), (2, 2210), (3, 4740), (4, 8310), (5, 13000), (10, 54500), (100, 8620000), (1000, 1605000000),
      (2000, 7800000000), (5000, 63200000000)]
for N, X in TX:
    p("  N =", N, " X_N =", X, " H(X_N, 7/8) =", n(H(X, mp.mpf(7) / 8), 10), " > N:", H(X, mp.mpf(7) / 8) > N)
for X, N in [(2 * 10 ** 9, 1101), (198 * 10 ** 8, 3007), (2 ** 40, 17450)]:
    p("  point d >=", X, ": H(X, 7/8) =", n(H(X, mp.mpf(7) / 8), 10), " > N - 1 =", N - 1, ":", H(X, mp.mpf(7) / 8) > N - 1)

p("== 4. the boundary")
cum = {1: 163, 2: 427, 3: 907, 4: 1555, 5: 2683, 10: 13843, 20: 58507, 50: 462883, 100: 2383747,
       1000: 227932027, 2000: 1062350083}


def Dp(h):
    A = 6 * mp.mpf(h)
    return max(mp.mpf(2981), (A * (mp.log(A) + mp.log(2 * mp.log(A)))) ** 2)


def Ds(h):
    return min(max(mp.mpf(1000), (17 * mp.mpf(h)) ** (mp.mpf(16) / 7)), Dp(h))


def Dv1(h):
    A = mp.mpf(100) / 9 * h
    return max(mp.mpf(2981), (A * (mp.log(A) + mp.log(2 * mp.log(A)))) ** 2)


for h in [1, 2, 3, 4, 5, 10, 20, 50, 100, 1000, 2000, 5000]:
    row = ["  h =", h, " D'(h) =", n(Dp(h), 6), " power =", n(max(mp.mpf(1000), (17 * mp.mpf(h)) ** (mp.mpf(16) / 7)), 6),
           " (B*) =", n(Ds(h), 6), " v1 D(h) =", n(Dv1(h), 6)]
    if h in cum:
        row += [" cumulative truth =", cum[h], " (B*)/truth =", n(Ds(h) / cum[h], 4), " D'/truth =", n(Dp(h) / cum[h], 4)]
    p(*row)
first = next(h for h in range(1, 10 ** 5) if (17 * mp.mpf(h)) ** (mp.mpf(16) / 7) > Dp(h))
p("  the power form is the smaller up to h =", first - 1, "; from h =", first, "on D'(h) is")
hm = {}
for line in open(DATA):
    a, c, mx, isp = map(int, line.split())
    hm[a] = mx
c, rs, rsv1 = 0, [], []
for h in range(1, 101):
    c = max(c, hm[h])
    rs.append((Ds(h) / c, h))
    rsv1.append((Dv1(h) / c, h))
p("  (B*)/cumulative truth over h <= 100: min", n(min(rs)[0], 4), "at h =", min(rs)[1], "; max", n(max(rs)[0], 4), "at h =", max(rs)[1])
rsp = []
c = 0
for h in range(1, 101):
    c = max(c, hm[h])
    rsp.append((Dp(h) / c, h))
p("  D'/cumulative truth over h <= 100: min", n(min(rsp)[0], 4), "at h =", min(rsp)[1], "; max", n(max(rsp)[0], 4), "at h =", max(rsp)[1])
p("  v1 D(h)/cumulative truth over h <= 100: min", n(min(rsv1)[0], 4), "at h =", min(rsv1)[1], "; max", n(max(rsv1)[0], 4), "at h =", max(rsv1)[1])

p("== 5. comparisons")
LL = {2: 4164, 10: 2.81e5, 100: 6.64e7, 1000: 1.18e10, 2000: 5.42e10, 5000: 4.02e11}
for N, X in TX:
    if N in LL:
        p("  N =", N, " LemmaLab posted / ours =", n(mp.mpf(LL[N]) / X, 4))
for N, X in TX:
    if N in cum:
        p("  N =", N, " ours / cumulative truth =", n(mp.mpf(X) / cum[N], 4))
p("  (L') at d = 2^40:", n(mp.sqrt(mp.mpf(2) ** 40) / mp.log(mp.mpf(2) ** 40) / 3, 8), "; (P') at 2^40:", n(mp.mpf(2) ** (40 * 7 / mp.mpf(16)) / 17, 8))
p("  Jaswal Thm 1.3 constant 1/5 vs 1/3; (U') constant at d = 2981: (log d + 7/6)/(pi log d) =", n((mp.log(2981) + mp.mpf(7) / 6) / (pi * mp.log(2981)), 6))
p("  asymptotic (U') 1/pi =", n(1 / pi, 6), "; (U'') 1/(2 pi) =", n(1 / (2 * pi), 6), "; v1 (U) 6/5")
p("  Kimura Remark 11: e^27.2 =", n(mp.e ** mp.mpf("27.2"), 4), "; e^35.4 =", n(mp.e ** mp.mpf("35.4"), 4))

# 4b. where the power form of (B*) is the smaller of the two
w = [hh for hh in range(1, 5001) if max(mp.mpf(1000), (17 * mp.mpf(hh)) ** (mp.mpf(16) / 7)) < Dp(hh)]
r, st, prev = [], w[0], w[0]
for hh in w[1:]:
    if hh != prev + 1:
        r.append((st, prev))
        st = hh
    prev = hh
r.append((st, prev))
p("== 4b. h in [1, 5000] where the power form (17h)^(16/7) is strictly smaller than D'(h):", r)

open(os.path.join(HERE, "paper_numbers_v2.out"), "w").write("\n".join(out) + "\n")
