"""Independent floating-point re-check of the per-class-minimum bound ("R2") for the next revision of the paper.

Written from a direct derivation, independently of the code that certified the thresholds in ball arithmetic. At real sigma in
(7/8, 1), with delta = 1 - sigma, nu = sigma - 1/2:
  one class:   Re(1/2 Z_Q(sigma)) >= g(a) - E(a),  g(a) = a^-sigma zeta(2 sigma) - K a^-delta,
               K = pi^sigma Gamma(nu)/Gamma(sigma) (4/(pi d))^nu |zeta(2 sigma - 1)|;
  minimum:     g(a) >= -(1 - delta/sigma) K u*,  u* = (delta K/(sigma Z))^(delta/(1 - 2 delta))  (Bernoulli);
  remainder:   |I(sigma; A, B)| <= (B/A)^(nu/2) sqrt(pi/sqrt(AB)) exp(-2 sqrt(AB))   (the K_{1/2} bound), so
               |E(a)| <= pi^sigma/(2 Gamma(sigma)) a^-1/2 (2/sqrt d)^nu sqrt(pi/c) 4 kappa(2c),  c = pi sqrt d/(2a),
               which increases with a, so the worst class has a = (2/3) sqrt d;
  sum:         0 > P - (h - 1) m,  P = Z - K - E(1),  m = (1 - delta/sigma) K u* + E((2/3) sqrt d).
Also checks the kernel bound itself against direct quadrature, and the Bernoulli minimum against a grid.
Floating point (mpmath, 30 digits); not a certification.
"""
import os

import mpmath as mp

HERE = os.path.dirname(os.path.abspath(__file__))

mp.mp.dps = 30
pi = mp.pi
out = []


def p(*a):
    s = " ".join(str(x) for x in a)
    print(s)
    out.append(s)


def kap(x):
    return mp.exp(-x) / (1 - mp.exp(-x)) ** 2


def parts(d, s):
    d, s = mp.mpf(d), mp.mpf(s)
    dl, nu = 1 - s, s - mp.mpf(1) / 2
    Z = mp.zeta(2 * s)
    K = pi ** s * mp.gamma(nu) / mp.gamma(s) * (4 / (pi * d)) ** nu * abs(mp.zeta(2 * s - 1))

    def E(a):
        c = pi * mp.sqrt(d) / (2 * a)
        return pi ** s / (2 * mp.gamma(s)) * a ** (-mp.mpf(1) / 2) * (2 / mp.sqrt(d)) ** nu * mp.sqrt(pi / c) * 4 * kap(2 * c)

    ustar = (dl * K / (s * Z)) ** (dl / (1 - 2 * dl))
    gmin = -(1 - dl / s) * K * ustar
    P = Z - K - E(1)
    m = -gmin + E(2 * mp.sqrt(d) / 3)
    return dict(Z=Z, K=K, E=E, gmin=gmin, P=P, m=m, H=1 + P / m, dl=dl)


# 1. the kernel bound, against quadrature
p("== 1. K_{1/2} kernel bound vs quadrature: I(sigma;A,B) = int t^(nu-1) e^(-At-B/t) dt")
worst = 0
for s in (mp.mpf(7) / 8 + mp.mpf(10) ** -6, mp.mpf("0.9"), mp.mpf("0.95"), mp.mpf("0.99")):
    nu = s - mp.mpf(1) / 2
    for A, B in ((0.3, 2.0), (5.0, 0.7), (1.0, 1.0), (12.0, 3.0), (0.05, 0.05)):
        A, B = mp.mpf(A), mp.mpf(B)
        I = mp.quad(lambda t: t ** (nu - 1) * mp.exp(-A * t - B / t), [0, 1, mp.inf])
        bnd = (B / A) ** (nu / 2) * mp.sqrt(pi / mp.sqrt(A * B)) * mp.exp(-2 * mp.sqrt(A * B))
        worst = max(worst, I / bnd)
p("max I/bound over the test grid:", mp.nstr(worst, 10), "(must be <= 1)")

# 2. the Bernoulli minimum, against a grid in a
p("== 2. min_a g(a) vs the closed form")
for d, s in ((2203, mp.mpf("0.87501")), (2 ** 40, mp.mpf(5671) / 6250)):
    q = parts(d, s)
    grid = min(q["Z"] * a ** (-s) - q["K"] * a ** (-q["dl"]) for a in [mp.mpf(10) ** (k / 200) for k in range(0, 2400)])
    p("d =", d, "closed-form min =", mp.nstr(q["gmin"], 12), " grid min (a in [1, 1e12]) =", mp.nstr(grid, 12))

# 3. headline thresholds
p("== 3. H(d, sigma) = 1 + P/m at the certified points")
for lab, d, s, need in (("h<=2", 2203, "0.87501", 2), ("h<=10", 54410, "0.87501", 10), ("h<=100", 8607000, "0.87501", 100),
                        ("h<=1000", 1603000000, "0.87501", 1000), ("h<=2000", 7788000000, "0.87721", 2000),
                        ("d>=2^40", 2 ** 40, mp.mpf(5671) / 6250, None), ("d>=2^40 at 7/8+1e-6", 2 ** 40, mp.mpf(7) / 8 + mp.mpf(10) ** -6, None)):
    H = parts(d, mp.mpf(s))["H"]
    p(lab, "d =", d, "sigma =", mp.nstr(mp.mpf(s), 8), "H =", mp.nstr(H, 14), ("> %d: %s" % (need, H > need)) if need else "")

# 4. uniform constant with sigma = 1 - min(1/8, 2/L)
p("== 4. H log d / sqrt d with sigma = 1 - min(1/8, 2/L)")
vals = []
for k in range(0, 2001):
    L = 8 + mp.mpf(k) / 10
    d = mp.e ** L
    H = parts(d, 1 - min(mp.mpf(1) / 8, 2 / L))["H"]
    vals.append((H * L / mp.sqrt(d), L))
mn = min(vals)
p("min over L in [8, 208] =", mp.nstr(mn[0], 8), "at L =", mp.nstr(mn[1], 5), "; at L = 8:", mp.nstr(vals[0][0], 8),
  "; max =", mp.nstr(max(vals)[0], 6), "at L =", mp.nstr(max(vals)[1], 5))
p("limit 2 zeta(2)/(pi e) =", mp.nstr(2 * mp.zeta(2) / (pi * mp.e), 8))

open(os.path.join(HERE, "r2_recheck.out"), "w").write("\n".join(out) + "\n")
