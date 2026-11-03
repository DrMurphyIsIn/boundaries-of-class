# Certify Jaswal's B(x, beta) (Prop. 2.2) at x = 2^40, beta = 7/8, in Arb.
# B(x,b) = 2b(1-b) * sum_{m>=1} ( a^{-b} G(b,a) + a^{b-1} G(1-b,a) ),  a = a_m = 2*pi*m^2/sqrt(x),
# G(s,a) = upper incomplete gamma; in python-flint, a.gamma_upper(s) = G(s, a) (checked: arb(1).gamma_upper(arb(1)/2) = sqrt(pi)*erfc(1) = G(1/2, 1), an asymmetric test). Every term is positive, so a partial sum is a rigorous LOWER bound.
# Upper bound: G(s,a) <= a^{s-1} e^{-a} for 0<s<1, a>0, so term_m <= 2 e^{-a}/a; the tail m>M is bounded by
# sum_{m>M} 2 e^{-c m^2}/(c m^2) <= 2 e^{-c M^2}/(c M^2) * sum_{k>=1} e^{-c(2Mk)} <= 2 e^{-cM^2}/(cM^2 (e^{2cM}-1)).
import flint, sys
from flint import arb, ctx
ctx.prec = 256
# Argument-order self-test (asymmetric): in python-flint, a.gamma_upper(s) must equal G(s, a).
_t = arb(1).gamma_upper(arb(1)/2) - arb.pi().sqrt()*arb(1).erfc()
assert _t.contains(0) and _t.rad() < arb('1e-60'), "gamma_upper argument order"
_u = arb(1).gamma_upper(arb(1)/2) - (-arb(1)).exp()
assert not _u.contains(0), "self-test cannot tell the orders apart"
x = arb(2)**40
b = arb(7)/8
c = 2*arb.pi()/x.sqrt()
M = int(sys.argv[1]) if len(sys.argv) > 1 else 6000
S = arb(0)
for m in range(1, M+1):
    a = c*m*m
    S += a**(-b)*a.gamma_upper(b) + a**(b-1)*a.gamma_upper(1-b)
pre = 2*b*(1-b)
lo = pre*S
tail = 2*(-c*M*M).exp()/(c*M*M*((2*c*M).exp()-1))
hi = pre*(S + tail)
print("flint", flint.__version__, "prec", ctx.prec, "M", M)
print("B lower >= ", lo.lower().str(20, radius=False))
print("B upper <= ", hi.upper().str(20, radius=False))
print("B(2^40,7/8) > 3500:", bool(lo > 3500))
