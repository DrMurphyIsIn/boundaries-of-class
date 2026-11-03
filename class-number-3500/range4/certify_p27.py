"""Range (4): re-certify Jaswal's Proposition 2.7 numbers in interval arithmetic (mpmath.iv, 300 bits).
C = Gamma(2 - d/35.0131) e^{-d/2} (pi^2/6 - 1e-4) / (2 pi), d = 1193/200000; g(x) = (2d/log x)(C sqrt x - 1e4);
check C >= 0.2609850699, g(e^35.0131) > 3561 (so h >= 3562 > 3500), and g' > 0 on [e^35.0131, oo):
sign(g') = sign(C sqrt x (log x / 2 - 1) + 1e4), positive for log x > 2."""
from mpmath import iv, mp
iv.prec = 300
d = iv.mpf(1193) / 200000
L0 = iv.mpf(350131) / 10000
C = iv.gamma(2 - d / L0) * iv.exp(-d / 2) * (iv.pi ** 2 / 6 - iv.mpf(1) / 10000) / (2 * iv.pi)
x0 = iv.exp(L0)
g0 = (2 * d / L0) * (C * iv.sqrt(x0) - 10000)
print("C  in", C)
print("C >= 0.2609850699:", C.a >= iv.mpf('0.2609850699').b)
print("g(e^35.0131) in", g0)
print("g(e^35.0131) > 3561 (so h >= 3562):", g0.a > 3561)
# monotonicity: for log x = L >= L0 > 2, C*sqrt(x)*(L/2 - 1) + 1e4 > 0 since every factor is positive
print("L0 > 2:", L0.a > 2, " C > 0:", C.a > 0)
print("3562 > 3500: the (K) range needs nothing more for N = 3500")
