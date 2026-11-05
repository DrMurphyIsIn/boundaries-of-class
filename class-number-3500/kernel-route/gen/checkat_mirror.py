"""Python mirror of Check.lean's checkAt (sieveList + mu, with ramified primes), to find for each exception lane the
smallest Y (and so the smallest prime list P = primes <= Y) with 4Y^2 < d and N < mu(sieveList P d, Y). DATA only."""
import math, sys
from functools import lru_cache
sys.setrecursionlimit(100000)
def primes_upto(n):
    s = bytearray([1]) * (n + 1); s[0:2] = b"\0\0"
    for p in range(2, math.isqrt(n) + 1):
        if s[p]: s[p * p::p] = bytearray(len(s[p * p::p]))
    return [i for i in range(n + 1) if s[i]]
def dOf(m): return m if m % 4 == 3 else 4 * m
def ptype(p, d):
    if d % p == 0: return 2
    if p == 2: return 1 if d % 8 == 7 else 0
    return 1 if pow((p - d % p) % p, (p - 1) // 2, p) == 1 else 0
def mu_of(L, Y):
    @lru_cache(maxsize=None)
    def mu(i, Y):
        if i == len(L): return 1
        p, split = L[i]
        r = mu(i + 1, Y)
        if split:
            q, j = p, 0
            while j < 64 and q <= Y:
                r += 2 * mu(i + 1, Y // q); q *= p; j += 1
        elif p <= Y:
            r += mu(i + 1, Y // p)
        return r
    return mu(0, Y)
def certify(m, N=1000, PR=None):
    d = dOf(m); Ymax = math.isqrt((d - 1) // 4)
    PR = PR or primes_upto(Ymax)
    for Y in sorted({Ymax} | {Ymax * k // 16 for k in range(1, 16)}):
        if 4 * Y * Y >= d: continue
        L = []
        for p in PR:
            if p > Y: break
            t = ptype(p, d)
            if t: L.append((p, t == 1))
        if mu_of(tuple(L), Y) > N: return Y
    return None
if __name__ == "__main__":
    for m in map(int, sys.argv[1:]):
        print(m, dOf(m), "Ymax", math.isqrt((dOf(m) - 1) // 4), "certified at Y =", certify(m))
