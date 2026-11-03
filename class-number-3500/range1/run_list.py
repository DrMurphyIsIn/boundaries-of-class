"""Range (1), second program: list every fundamental D = -n, 3 <= n < NMAX, with h(D) <= HMAX, by PARI qfbclassno
(Shanks; PARI 2.17.4 manual: unconditionally correct for |D| < 2e10). One gp process per chunk of CH consecutive n.
Per chunk: out/c<k>.txt with 'n h' for h <= HMAX, and out/c<k>.sum with 'k lo hi fundamental sum_h n_le maxn'.
Resumable: a chunk whose .sum exists is skipped. Usage: run_list.py <workers> [NMAX] [HMAX] [CH]"""
import os, subprocess, sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
W = int(sys.argv[1]); NMAX = int(float(sys.argv[2])) if len(sys.argv) > 2 else 19800000000
HMAX = int(sys.argv[3]) if len(sys.argv) > 3 else 3500; CH = int(float(sys.argv[4])) if len(sys.argv) > 4 else 10**7
OUT = Path(__file__).resolve().parent / "out"; OUT.mkdir(exist_ok=True)
GP = "/opt/homebrew/bin/gp"
def chunk(k):
    lo, hi = max(3, k * CH), min(NMAX, (k + 1) * CH)
    s = OUT / f"c{k:05d}.sum"
    if s.exists() or lo >= hi: return k, "skip"
    txt, tmp = OUT / f"c{k:05d}.txt", OUT / f"c{k:05d}.txt.part"
    for stale in (tmp, OUT / f"c{k:05d}.sum.part"):      # a restarted chunk never appends to an old partial file
        stale.unlink(missing_ok=True)
    code = (f'my(f=0,S=0,c=0,mx=0,L=List()); for(n={lo},{hi - 1}, if(isfundamental(-n), my(h=qfbclassno(-n)); f++; '
            f'S+=h; if(h<={HMAX}, c++; mx=n; listput(L, Str(n, " ", h)); '
            f'if(#L>=200000, write("{tmp}", strjoin(Vec(L), "\\n")); L=List())))); '
            f'if(#L>0, write("{tmp}", strjoin(Vec(L), "\\n"))); '
            f'write("{OUT}/c{k:05d}.sum.part", "{k} {lo} {hi} ", f, " ", S, " ", c, " ", mx); quit')
    r = subprocess.run([GP, "-q", "-f", "-s", "1G"], input=code, capture_output=True, text=True)
    if r.returncode != 0 or not (OUT / f"c{k:05d}.sum.part").exists():
        return k, f"FAIL rc={r.returncode} {(r.stdout + r.stderr)[-300:]}"
    if tmp.exists(): tmp.rename(txt)
    else: txt.write_text("")
    (OUT / f"c{k:05d}.sum.part").rename(s)
    return k, "ok"
ks = range((NMAX + CH - 1) // CH)
with ThreadPoolExecutor(W) as ex:
    for k, st in ex.map(chunk, ks):
        if st != "skip": print(k, st, flush=True)
print("DONE", flush=True)
