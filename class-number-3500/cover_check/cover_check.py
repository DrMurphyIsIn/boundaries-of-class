"""Cover check for the class-number-3500 classification. CERTIFIED parts use mpmath interval arithmetic at 300 bits.
  (1) [3, 19,800,000,000)  (2) [19,800,000,000, 2^40)  (3) [2^40, 1,606,926,912,624,720]  (4) [1,606,926,912,624,721, oo)
Checks: the four ranges partition [3, oo) as integer sets; log(1,606,926,912,624,720) < 35.0131 <= log(...721);
the eleven Table-3 intervals (half-open [A, A2), the last with A2 = 1,606,926,912,624,721) tile range (3) exactly;
optionally (--runs <dir> <tag-prefix>) the intervals AS RUN, read from the run logs, equal those eleven.
Usage: cover_check.py [--runs p3/runs <prefix> <expected N> [--settled <file>]]"""
import re, sys
from pathlib import Path
from mpmath import iv
iv.prec = 300
E = 1606926912624720
R = [(3, 19800000000), (19800000000, 2**40), (2**40, E + 1), (E + 1, None)]       # half-open, last unbounded
ok = True
def check(c, msg):
    global ok; ok &= bool(c); print(("PASS " if c else "FAIL ") + msg)
check(all(R[i][1] == R[i + 1][0] for i in range(3)) and R[0][0] == 3, "the four ranges are consecutive half-open integer intervals from 3")
lo, hi = iv.log(iv.mpf(E)), iv.log(iv.mpf(E + 1)); t = iv.mpf(350131) / 10000
check(lo.b < t.a, f"log({E}) < 35.0131  (log in [{float(lo.a)}, {float(lo.b)}])")
check(hi.a >= t.b, f"log({E + 1}) >= 35.0131  (log in [{float(hi.a)}, {float(hi.b)}])")
T3 = [(2**40, 2**41, 19, 524288), (2**41, 2**42, 19, 741455), (2**42, 2**43, 19, 1048576), (2**43, 2**44, 23, 1482910),
      (2**44, 2**45, 23, 2097152), (2**45, 2**46, 29, 2965820), (2**46, 2**47, 29, 4194304), (2**47, 2**48, 29, 5931641),
      (2**48, 2**49, 29, 8388608), (2**49, 2**50, 29, 11863283), (2**50, E + 1, 29, 16777216)]
check(T3[0][0] == R[2][0] and T3[-1][1] == R[2][1] and all(T3[i][1] == T3[i + 1][0] for i in range(10)),
      "the eleven Table-3 intervals tile range (3) exactly")
from math import isqrt
check(all(Y == isqrt(A // 4) for A, _, _, Y in T3), "every Y = floor(sqrt(floor(A/4))), so 4Y^2 <= A")
# Jaswal Table 3 (jaswal.txt:1350-1361): n treated per interval (independent of N) and n reaching step 3 at N = 3000
JT = [366503875925, 733007751850, 1466015503702, 2932031007402, 5864062014805, 11728124029612, 23456248059221,
      46912496118442, 93824992236886, 187649984473770, 160342335260699]
JS3 = [94581, 764, 0, 0, 0, 0, 0, 0, 0, 0, 0]
check(sum(JT) == 535275800332314, "Jaswal's per-interval n treated sum to his total 535,275,800,332,314")
if "--runs" in sys.argv:
    # --runs <dir> <prefix> <expected N> [--settled <file>]
    i = sys.argv.index("--runs"); d, pre, NEXP = Path(sys.argv[i + 1]), sys.argv[i + 2], int(sys.argv[i + 3])
    settled = set()
    if "--settled" in sys.argv:                    # K3: lines "n h" for every leftover, settled by two exact counts
        settled = {int(l.split()[0]) for l in Path(sys.argv[sys.argv.index("--settled") + 1]).read_text().split("\n") if l.strip()}
    rows = []
    for f in sorted(d.glob(pre + "*.log")):
        t = f.read_text()
        m = re.search(r"^command \S+ (\d+) (\d+) (\d+) (\d+) (\d+) (\d+)", t, re.M)
        if not m: continue
        if not re.search(r"^end ", t, re.M) or "match=" not in t:
            check(False, f"{f.name}: run incomplete (no end line or no counts)"); continue
        g = lambda key: int(re.search(key + r"=(\d+)", t).group(1))
        out = f.with_suffix(".out")
        lefts = [int(l.split()[1]) for l in out.read_text().splitlines() if l.startswith("LEFTOVER")] if out.exists() else None
        rows.append(dict(A=int(m[2]), A2=int(m[3]), P=int(m[4]), Y=int(m[5]), N=int(m[1]), name=f.name,
                         match=g("match"), nt=g("n_treated"), s3=g("reaching_step3"), left=g("leftover"), lefts=lefts))
    rows.sort(key=lambda r: r["A"])
    check([(r["A"], r["A2"], r["P"], r["Y"]) for r in rows] == T3,
          f"exactly one run per interval: the {len(rows)} logs {pre!r} are the eleven intervals (A, A2, P, Y)")
    check(all(r["N"] == NEXP for r in rows), f"every run has N = {NEXP} (the expected value)")
    check(all(r["match"] == 1 for r in rows), "every run has n_treated == direct_count (match=1)")
    if len(rows) == 11:
        check(all(r["nt"] == JT[k] for k, r in enumerate(rows)), "every run's n_treated equals Jaswal's Table 3 value (C2)")
        if NEXP == 3000:
            check(all(r["s3"] == JS3[k] for k, r in enumerate(rows)), "at N = 3000, reaching_step3 equals Jaswal's column (C2)")
    unsettled = [n for r in rows for n in (r["lefts"] or []) if n not in settled]
    check(all(r["lefts"] is not None for r in rows) and all(r["left"] == len(r["lefts"]) for r in rows),
          "every run's leftover count equals its LEFTOVER lines")
    check(not unsettled, f"no unsettled leftover (C1/K3): {len(unsettled)} unsettled, {sum(r['left'] for r in rows)} in total")
print("COVER CHECK " + ("PASS" if ok else "FAIL"))
sys.exit(0 if ok else 1)
