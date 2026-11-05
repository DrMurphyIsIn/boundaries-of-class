# X_3500 by entry 5's threshold engine at sigma = 7/8: the exact rational instance (q, r, s, e, fin) as in the
# public generator, with an exact integer root bracket in place of the original helper.
from fractions import Fraction as F
import math
piL = F(3141592, 10**6); GratU = F(21755, 10**4); ZmU = F(344129, 10**5); ZL = F(196232, 10**5)
pi78U = F(6807, 2500); GL = F(10861, 10**4); x34 = F(4767, 50000); xk = x34**2; kapU = xk/(1-xk)**2
def iroot_floor(a, n):
    # floor of the n-th root of the integer a
    if a < 2: return a
    x = int(round(a ** (1.0 / n)))
    while x ** n > a: x -= 1
    while (x + 1) ** n <= a: x += 1
    return x
def up(q, k, n, dg):
    # least r = U/10^dg with r^n >= q^k, exactly
    D = 10**dg
    # r^n >= q^k  <=>  U^n >= q^k * D^n
    num = q.numerator**k * D**n; den = q.denominator**k
    # smallest U with U^n * den >= num
    U = iroot_floor(num // den, n)
    while U**n * den < num: U += 1
    return F(U, D)
def dn_sqrt(X, dg):
    D = 10**dg
    num = X.numerator * D * D; den = X.denominator
    Lo = iroot_floor(num // den, 2)
    while (Lo + 1)**2 * den <= num: Lo += 1
    while Lo**2 * den > num: Lo -= 1
    return F(Lo, D)
def instance(N, X, dg=8):
    X = F(X); q = dn_sqrt(X, 4)
    r = up(4/(piL*X), 3, 8, dg)
    Kb = pi78U*GratU*r*ZmU
    s = up(Kb/(7*ZL), 1, 6, dg)
    e = up(2/q, 7, 8, dg)
    Eb = 2*pi78U/GL*e*kapU
    y = 1/(1 + piL*q/4)**4
    E1 = 2*pi78U/GL*e*(y/(1-y)**2)
    fin = ZL - Kb - E1 - (N-1)*(F(6, 7)*Kb*s + Eb)
    return q, r, s, e, fin
# sanity: reproduce the public instances
for N, X in [(1000, 1605000000), (2000, 7800000000), (5000, 63200000000), (3006, 19800000000)]:
    q, r, s, e, fin = instance(N, X)
    print("check N=%d X=%d fin=%.4e %s q=%s r=%s s=%s e=%s" % (N, X, float(fin), "OK" if fin > 0 else "FAIL", q, r, s, e))
# bisection for the least X (to 1e7 resolution) with fin > 0 at N = 3500
N = 3500
lo, hi = 7800000000, 63200000000
while hi - lo > 10**7:
    mid = (lo + hi) // 2
    if instance(N, mid)[4] > 0: hi = mid
    else: lo = mid
print("least X_3500 (1e7 grid):", hi)
for X in [28000000000, 28500000000, 29000000000, 30000000000]:
    q, r, s, e, fin = instance(N, X)
    print("N=3500 X=%d fin=%.4e %s" % (X, float(fin), "OK" if fin > 0 else "FAIL"))
    if fin > 0:
        print("  (q := (%d / %d : ℝ)) (r := (%d / %d : ℝ)) (s := (%d / %d : ℝ)) (e := (%d / %d : ℝ))" % (q.numerator, q.denominator, r.numerator, r.denominator, s.numerator, s.denominator, e.numerator, e.denominator))
