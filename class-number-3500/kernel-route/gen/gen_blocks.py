"""Block generator for the block sieve (pillar 1 of the kernel route; see DESIGN.md and FORMAT.md).

It mirrors lean/BoundariesOfClass/Sieve/Block/Defs.lean EXACTLY in Python: rot, rep, inv4, maskOf, mask2, masksOf,
j0Of, nsqOf, NSQ, the depth-first count (dfsY/powsY with fuel 4000), addFrom/addSt, geqFrom, count1, finalSt,
uncertified. So each block's E is the value the kernel will recompute.

    python3 gen_blocks.py <out-dir> <N> <fam: A|B1|B2> <m_start> <m_end> <L> [--shared <shared_lists.json>] [--k0 <first index>] [--verify]

Writes:
- <out-dir>/Gen/<fam>/B<k>.lean: one block each, `def` plus `theorem … : blockOK … = true := by decide +kernel`;
- <out-dir>/exceptions_<fam>.txt: the squarefree uncertified lanes (m) for the per-field stage;
- <out-dir>/MANIFEST_<fam>.json: the md5 of every generated file.

The shared modules (Defs, Base.Pats, Base.Primes) are written by gen_shared.py. The E literals are DATA: the kernel
checks them; they are never trusted.
"""
import hashlib, json, math, sys
from pathlib import Path

NP = 11

def primes_upto(n):
    s = bytearray([1]) * (n + 1); s[0:2] = b"\0\0"
    for p in range(2, math.isqrt(n) + 1):
        if s[p]: s[p * p::p] = bytearray(len(s[p * p::p]))
    return [i for i in range(n + 1) if s[i]]

def base_pattern(q):          # bit j set iff ¬ q | 4j and -4j is a square mod q (BaseOK)
    sq = {(x * x) % q for x in range(1, q)}
    return sum(1 << j for j in range(q) if (4 * j) % q != 0 and ((q * q - 4 * j) % q) in sq)

def rot(q, B, t): return ((B >> t) | (B << (q - t))) & ((1 << q) - 1)
def rep(L, q, P): return (P * (((1 << (q * ((L + q - 1) // q))) - 1) // ((1 << q) - 1))) & ((1 << L) - 1)
def inv4(q): return ((q + 1) // 2) * ((q + 1) // 2) % q
def maskOf(L, m0, q, B): return rep(L, q, rot(q, B, m0 * inv4(q) % q))
def mask2(L, m0): return rep(L, 2, 1 if m0 % 8 == 7 else 2)
def j0Of(m0, p):
    pp = p * p
    return (pp - m0 % pp) * (((pp + 1) // 2) * ((pp + 1) // 2) % pp) % pp
def nsqOf(L, m0, p):
    if p * p < L: return rep(L, p * p, 1 << j0Of(m0, p))
    j = j0Of(m0, p)
    return (1 << j) if j < L else 0
def NSQ(L, m0, sqps):
    acc = 0
    for p in sqps: acc |= nsqOf(L, m0, p)
    return acc

class St:
    def __init__(self): self.planes = [0] * NP; self.sticky = 0
    def add(self, M, k):
        c = M
        for j in range(k, NP):
            self.planes[j], c = self.planes[j] ^ c, self.planes[j] & c
        self.sticky |= c

def dfsY(Yb, fuel, masks, i, prod, M, k, s):
    # mirrors dfsY/powsY: iterate the remaining list; stop at the first q with Yb < prod * q
    for j in range(i, len(masks)):
        if fuel == 0: return
        q, S = masks[j]
        if Yb < prod * q: return
        M2 = M & S
        pk = prod * q
        f = fuel - 1
        while f > 0 and not (Yb < pk):
            s.add(M2, k + 1)
            dfsY(Yb, f - 1, masks, j + 1, pk, M2, k + 1, s)
            pk *= q; f -= 1
        fuel -= 1

def masksOf(fam, L, m0, pats):        # mirrors Defs.masksOf
    return ([(2, mask2(L, m0))] if fam == 0 else []) + [(q, maskOf(L, m0, q, B)) for q, B in pats]

def count1(L, masks, Yb, s):          # mirrors Defs.count1: over finished masks
    ALL = (1 << L) - 1
    s.add(ALL, 0)
    dfsY(Yb, 4000, masks, 0, 1, ALL, 0, s)

def geq(ALL, planes, T, sticky):
    gt, eq = 0, ALL
    for j in reversed(range(NP)):
        if (T >> j) & 1: eq &= planes[j]
        else: gt |= eq & planes[j]; eq &= ALL ^ planes[j]
    return gt | eq | sticky

def uncertified(fam, N, L, m0, Y, pats, oddPrimes):
    ALL = (1 << L) - 1
    s = St()
    masks = masksOf(fam, L, m0, pats)
    if fam == 0:
        count1(L, masks, Y, s)
    else:
        count1(L, masks, Y, s); count1(L, masks, Y // 2, s)
    sqps = [p for p in oddPrimes if p * p <= m0 + 4 * (L - 1)]
    return (ALL ^ (geq(ALL, s.planes, N + 1, s.sticky) & ALL)) & (ALL ^ NSQ(L, m0, sqps))

def block_Y(fam, m0):
    Y = math.isqrt((m0 - 1) // 4) if fam == 0 else math.isqrt(m0 - 1)
    assert (4 * Y * Y < m0) if fam == 0 else (Y * Y < m0)
    return Y

if __name__ == "__main__":
    verify = "--verify" in sys.argv          # regenerate-and-diff (FORMAT.md, acceptance): compare, write nothing
    if verify: sys.argv.remove("--verify")
    k0 = 0                                   # first block index, so that several runs over one family never collide
    if "--k0" in sys.argv:
        j = sys.argv.index("--k0"); k0 = int(sys.argv[j + 1]); del sys.argv[j:j + 2]
    shared = None
    if "--shared" in sys.argv:          # the pinned shared_lists.json from gen_shared.py: mirror EXACTLY Base.pats/oddPrimes
        k = sys.argv.index("--shared"); shared = json.loads(Path(sys.argv[k + 1]).read_text()); del sys.argv[k:k + 2]
    out, N, famname, ms, me, L = Path(sys.argv[1]), int(sys.argv[2]), sys.argv[3], int(float(sys.argv[4])), int(float(sys.argv[5])), int(sys.argv[6])
    fam = 0 if famname == "A" else 1
    res = {"A": 3, "B1": 1, "B2": 2}[famname]
    m0 = ms + ((res - ms) % 4)
    YMAX = block_Y(fam, me)
    if shared:
        assert shared["YMAX"] >= YMAX and shared["PMAX"] ** 2 >= me + 4 * L, "shared table too small for this range"
        pats = [(q, base_pattern(q)) for q in shared["pats_primes"]]
        oddPrimes = list(shared["oddPrimes"])
    else:
        pats = [(q, base_pattern(q)) for q in primes_upto(YMAX) if q > 2]
        oddPrimes = [p for p in primes_upto(math.isqrt(me + 4 * L) + 1) if p > 2]
    gdir = out / "Gen" / famname
    if not verify: gdir.mkdir(parents=True, exist_ok=True)
    man = {}; exc = []; k = k0; bad = []
    while m0 < me:
        # The last block of a run is SHORTENED so that its lanes stop below m_end (so no lane past X, or
        # past X/4 for family B, ever needs a per-field certificate); every other block has exactly L lanes.
        Lb = min(L, (me - m0 + 3) // 4)
        Y = block_Y(fam, m0)
        E = uncertified(fam, N, Lb, m0, Y, pats, oddPrimes)
        name = f"blk_{famname}_{k:05d}"
        src = (f"import BoundariesOfClass.Sieve.Block.Defs\nimport BoundariesOfClass.Sieve.Block.Base.Pats\n"
               f"import BoundariesOfClass.Sieve.Block.Base.Primes\n\nnamespace BoundariesOfClass.Sieve.Block.Gen\n\n"
               f"def {name} : Blk := ⟨{fam}, {N}, {Lb}, {m0}, {Y}, Base.pats, Base.oddPrimes, {E}⟩\n\n"
               f"set_option maxRecDepth 1000000 in\ntheorem {name}_ok : blockOK {name} = true := by decide +kernel\n\n"
               f"end BoundariesOfClass.Sieve.Block.Gen\n")
        p = gdir / f"B{k:05d}.lean"
        if verify:
            if not p.exists() or p.read_bytes() != src.encode(): bad.append(str(p.relative_to(out)))
        else:
            p.write_text(src)
        man[str(p.relative_to(out))] = hashlib.md5(src.encode()).hexdigest()
        exc += [m0 + 4 * i for i in range(Lb) if (E >> i) & 1]
        m0 += 4 * Lb; k += 1
    exc_txt = "\n".join(map(str, exc)) + "\n"
    man_txt = json.dumps(man, indent=1, sort_keys=True) + "\n"
    if verify:
        for name, txt in ((f"exceptions_{famname}_{k0:05d}.txt", exc_txt), (f"MANIFEST_{famname}_{k0:05d}.json", man_txt)):
            q = out / name
            if not q.exists() or q.read_text() != txt: bad.append(name)
        # (extra files in Gen/<fam> are judged by regen.py over all runs together, not per run)
        print(f"{famname}: REGENERATE-AND-DIFF " + ("PASS" if not bad else "FAIL: " + ", ".join(bad[:10])))
        sys.exit(0 if not bad else 1)
    (out / f"exceptions_{famname}_{k0:05d}.txt").write_text(exc_txt)
    (out / f"MANIFEST_{famname}_{k0:05d}.json").write_text(man_txt)
    print(f"{famname}: {k - k0} blocks of up to {L} lanes (the last ends below {me}), Y up to {YMAX}, {len(pats)} pattern primes, "
          f"{len(oddPrimes)} square primes; {len(exc)} squarefree uncertified lanes")
