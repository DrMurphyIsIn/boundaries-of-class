"""Coverage check for claimed and delivered ranges of the block sieve (FORMAT.md, section 7).

A range claim is one JSON object per line in CLAIMS.jsonl:
    {"fam": "A"|"B1"|"B2", "m_start": int, "m_end": int, "L": int, "k0": int, "who": "<name>", "status": "claimed"|"delivered"}

For the target (F, X, N) the check verifies, with no Lean:
  (1) per family, the claims tile the family's range EXACTLY, as half-open integer intervals, with no gap and no
      overlap: family A over [F + 1, X) (d = m), families B1 and B2 over [F // 4 + 1, (X + 3) // 4) (d = 4 m);
  (2) per family, the block-index ranges [k0, k0 + count) are disjoint, where count is computed exactly as
      gen_blocks.py walks a run (so two runs can never write the same block file);
  (3) optionally (--blocks <dir> ...), every DELIVERED claim's block files exist, and each file's Blk literal has the
      family's residue, the claimed N, lanes that stay inside [m_start, m_end), and consecutive blocks that abut;
  (4) optionally (--xs xs.json), every exception lane listed lies in some delivered claim's range, with the claimed N.

Usage: cover_check.py CLAIMS.jsonl F X N [--blocks <dir> ...] [--xs xs.json]
Exit 0 on PASS, 1 on FAIL. Every line of output starts with PASS or FAIL.
"""
import json, re, sys
from pathlib import Path

RES = {"A": 3, "B1": 1, "B2": 2}
ok = True

def check(c, msg):
    global ok
    ok &= bool(c); print(("PASS " if c else "FAIL ") + msg)

def run_count(r):
    m0 = r["m_start"] + ((RES[r["fam"]] - r["m_start"]) % 4); n = 0
    while m0 < r["m_end"]:
        m0 += 4 * min(r["L"], (r["m_end"] - m0 + 3) // 4); n += 1
    return n

def main(argv):
    claims_p, F, X, N = Path(argv[0]), int(argv[1]), int(argv[2]), int(argv[3])
    bdirs, xs_p = [], None
    if "--blocks" in argv:
        i = argv.index("--blocks"); j = i + 1
        while j < len(argv) and not argv[j].startswith("--"): bdirs.append(Path(argv[j])); j += 1
    if "--xs" in argv: xs_p = Path(argv[argv.index("--xs") + 1])
    claims = [json.loads(l) for l in claims_p.read_text().splitlines() if l.strip()]
    rng = {"A": (F + 1, X), "B1": (F // 4 + 1, (X + 3) // 4), "B2": (F // 4 + 1, (X + 3) // 4)}
    check(all(c["fam"] in RES for c in claims), "every claim names a family A, B1 or B2")
    check(all(c["status"] in ("claimed", "delivered") for c in claims), "every claim has status claimed or delivered")
    for fam, (lo, hi) in rng.items():
        cs = sorted((c for c in claims if c["fam"] == fam), key=lambda c: c["m_start"])
        if not cs:
            check(False, f"family {fam}: no claims (range [{lo}, {hi}) uncovered)"); continue
        check(cs[0]["m_start"] == lo, f"family {fam}: the first claim starts at {cs[0]['m_start']} = {lo}")
        check(cs[-1]["m_end"] == hi, f"family {fam}: the last claim ends at {cs[-1]['m_end']} = {hi}")
        gaps = [(a["m_end"], b["m_start"]) for a, b in zip(cs, cs[1:]) if a["m_end"] != b["m_start"]]
        check(not gaps, f"family {fam}: consecutive claims abut (no gap, no overlap); offending pairs: {gaps[:5]}")
        check(all(c["m_start"] < c["m_end"] for c in cs), f"family {fam}: every claim is a nonempty half-open interval")
        ks = sorted((c["k0"], c["k0"] + run_count(c)) for c in cs)
        over = [(a, b) for a, b in zip(ks, ks[1:]) if b[0] < a[1]]
        check(not over, f"family {fam}: block-index ranges [k0, k0 + count) are disjoint; overlaps: {over[:5]}")
    delivered = [c for c in claims if c["status"] == "delivered"]
    if bdirs:
        for c in delivered:
            fam = c["fam"]; n = run_count(c); files = []
            for k in range(c["k0"], c["k0"] + n):
                hits = [d / "Gen" / fam / f"B{k:05d}.lean" for d in bdirs if (d / "Gen" / fam / f"B{k:05d}.lean").exists()]
                files.append(hits[0] if hits else None)
            check(all(files), f"{fam} [{c['m_start']}, {c['m_end']}) by {c['who']}: all {n} block files exist")
            if not all(files): continue
            prev_end = None; good = True
            for k, p in zip(range(c["k0"], c["k0"] + n), files):
                m = re.search(r"^def (\S+) : Blk := ⟨(\d+), (\d+), (\d+), (\d+), (\d+), Base\.pats, Base\.oddPrimes, (\d+)⟩", p.read_text(), re.M)
                if not m: good = False; print(f"FAIL {p}: no Blk literal"); break
                fam_i, Nb, Lb, m0, Y, E = (int(m.group(i)) for i in range(2, 8))
                last = m0 + 4 * (Lb - 1)
                cond = (Nb == N and (fam_i == 0) == (fam == "A") and m0 % 4 == RES[fam] and c["m_start"] <= m0 and last < c["m_end"]
                        and Lb >= 1 and (prev_end is None or m0 == prev_end) and ((4 * Y * Y < m0) if fam == "A" else (Y * Y < m0)))
                if not cond: good = False; print(f"FAIL {p}: Blk ⟨{fam_i}, {Nb}, {Lb}, {m0}, {Y}, …⟩ is not consistent with the claim"); break
                prev_end = m0 + 4 * Lb
            if good:   # the shortened last block ends at or just past m_end (by less than one stride of 4)
                good = prev_end is not None and c["m_end"] <= prev_end < c["m_end"] + 4
            check(good, f"{fam} [{c['m_start']}, {c['m_end']}) by {c['who']}: the {n} Blk literals have N = {N}, the right residue, abut, and tile the claim")
    if xs_p:
        xs = json.loads(xs_p.read_text())
        check(xs.get("N") == N, f"xs.json has N = {N}")
        inside = []
        for m, Y in xs["xs"]:
            fam = "A" if m % 4 == 3 else ("B1" if m % 4 == 1 else "B2")
            inside.append(any(c["fam"] == fam and c["m_start"] <= m < c["m_end"] for c in delivered))
        check(all(inside), f"every one of the {len(xs['xs'])} exception lanes lies in a delivered claim of its family")
    print("COVER CHECK " + ("PASS" if ok else "FAIL"))
    return 0 if ok else 1

if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
