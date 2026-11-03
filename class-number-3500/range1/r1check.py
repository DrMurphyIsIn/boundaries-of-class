#!/usr/bin/env python3
"""r1check.py -- range (1) verification for the class-number-3500 release.

Verifier. Read-only outside this script's own directory. Pure Python, single process, no numpy.

This script documents and reproduces the cross-check between the two range-(1) programs (range1.c and
run_list.py) and the published lists it was checked against. It expects the full per-segment outputs of both
programs, which are NOT part of the git release (they regenerate to the full field list, which is deposited on
Zenodo with this release; see the README for how to regenerate them -- about 9-17 core-hours). Running this
script against those regenerated outputs should reproduce the digests and counts recorded in the paper and in
verify_range1_summary.md.

Inputs (read-only, all relative to this script's directory unless overridden by the environment variables below):
  L1  ours_full/r*.txt + .sum        (range1.c; .sum = "SEG lo hi fund dec ex rec sumh")        [R1_L1DIR]
  L2  out/c*.txt + .sum              (PARI qfbclassno; .sum = "k lo hi fund sum_h n_le maxn")   [R1_L2DIR]
  Jaswal  external/jaswal/data/c3_list_all.txt.gz   ("D h", D < 0)                              [R1_JASWAL_GZ]
  Kimura  external/kimura/imq_h2000.txt.xz   ("d h")                                            [R1_KIMURA_XZ]
Checks: 2 coverage, 3 L1 = L2, 4 fundamental counts, 5 external checksums, 6 per-h counts.
Outputs (written next to this script): L1_norm.txt (the normalised L1; L2's normalisation is byte-identical iff
  check 3 passes), range1_per_h.txt, per_segment_fund.txt, r1check_result.json, r1check.log.
"""
import glob, gzip, hashlib, json, lzma, os, re, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = HERE
L1DIR = os.environ.get("R1_L1DIR", os.path.join(HERE, "ours_full"))
L2DIR = os.environ.get("R1_L2DIR", os.path.join(HERE, "out"))
L1LOG = os.environ.get("R1_L1LOG", os.path.join(HERE, "logs", "ours_full_run.log"))
L2LOG = os.environ.get("R1_L2LOG", os.path.join(HERE, "logs", "pari_full_run.log"))
JASWAL_GZ = os.environ.get("R1_JASWAL_GZ", os.path.join(HERE, "external", "jaswal", "data", "c3_list_all.txt.gz"))
JASWAL_TABLE = os.environ.get("R1_JASWAL_TABLE", os.path.join(HERE, "external", "jaswal", "data", "table_h3000.txt"))
KIMURA_XZ = os.environ.get("R1_KIMURA_XZ", os.path.join(HERE, "external", "kimura", "imq_h2000.txt.xz"))
KIMURA_TABLE = os.environ.get("R1_KIMURA_TABLE", os.path.join(HERE, "external", "kimura", "h2000_table.txt"))
GP_PATH = os.environ.get("R1_GP_PATH", "/opt/homebrew/bin/gp")

NMAX = 19_800_000_000
N = 3500
CH = 10**7
NSEG = 1980
FUND_JASWAL = 6_018_478_352            # Jaswal's preprint: the number of fundamental n below NMAX
JASWAL_COUNT, JASWAL_MAXN = 36_993_853, 2_562_211_723
KIMURA_COUNT, KIMURA_MAXN = 16_453_493, 1_062_350_083
# Jaswal README v3 :160 -- SHA-256 of the "|D| h" pairs of L with h <= 1000, 1500, 2000 (4,115,897; 9,245,562; 16,453,493)
JASWAL_SHA = {1000: "075a201c8e7cce6c0b6013423a5d96c6308452afab2fa79882388fc46d8b0c45",
              1500: "c373d7c67bbecb922878481c50e6273f03ed07b93fc968a458bb0bf5389ee101",
              2000: "07100ea3589ab2b490122fa69b438cd5393bdcd2e547dfc29bb3b5c86f9f24c0"}
THRESH = (1000, 1500, 2000, 3000, 3500)
FUND_MOD16 = {3, 7, 11, 15, 4, 8}

LOG = open(os.path.join(OUT, "r1check.log"), "w")
T0 = time.time()
RESULT = {"checks": {}, "notes": []}


def log(msg):
    line = "[%7.1fs] %s" % (time.time() - T0, msg)
    print(line, flush=True); LOG.write(line + "\n"); LOG.flush()


def check(name, ok, detail=""):
    RESULT["checks"][name] = {"pass": bool(ok), "detail": detail}
    log("%s %s %s" % ("PASS" if ok else "FAIL", name, detail))
    return ok


def note(msg):
    RESULT["notes"].append(msg); log("NOTE " + msg)


def md5(path):
    h = hashlib.md5()
    with open(path, "rb") as f:
        for b in iter(lambda: f.read(1 << 20), b""):
            h.update(b)
    return h.hexdigest()


# ---------------------------------------------------------------- check 2: coverage
def coverage_L1():
    sums = sorted(glob.glob(os.path.join(L1DIR, "*.sum")))
    others = [f for f in os.listdir(L1DIR) if not (f.endswith(".sum") or f.endswith(".txt"))]
    check("2.L1.no_stray_files", not others, "stray=%r" % others[:5])
    segs = []
    bad = []
    for s in sums:
        t = open(s).read().split()
        if len(t) != 8 or t[0] != "SEG":
            bad.append((s, "format")); continue
        lo, hi, fund, dec, ex, rec, sumh = map(int, t[1:])
        if os.path.basename(s) != "r%012d.sum" % lo: bad.append((s, "name"))
        if fund != dec + ex: bad.append((s, "fund!=dec+ex"))
        if not os.path.exists(s[:-4] + ".txt"): bad.append((s, "no .txt"))
        segs.append(dict(lo=lo, hi=hi, fund=fund, dec=dec, ex=ex, rec=rec, sumh=sumh, txt=s[:-4] + ".txt"))
    check("2.L1.sum_lines_wellformed", not bad, "bad=%r" % bad[:5])
    segs.sort(key=lambda d: d["lo"])
    txts = set(os.path.basename(f) for f in glob.glob(os.path.join(L1DIR, "*.txt")))
    check("2.L1.txt_set_equals_sum_set", txts == set("r%012d.txt" % d["lo"] for d in segs),
          "txt=%d sum=%d" % (len(txts), len(segs)))
    tile = segs and segs[0]["lo"] == 3 and segs[-1]["hi"] == NMAX and \
        all(segs[i]["hi"] == segs[i + 1]["lo"] for i in range(len(segs) - 1)) and \
        all(d["lo"] < d["hi"] for d in segs)
    check("2.L1.tiling_[3,NMAX)_no_gap_no_overlap", tile, "segments=%d lo0=%d hiN=%d" % (len(segs), segs[0]["lo"], segs[-1]["hi"]))
    check("2.L1.segment_count_1980", len(segs) == NSEG, "n=%d" % len(segs))
    logtxt = open(L1LOG).read()
    check("2.L1.log_DONE_segments_1980", logtxt.strip() == "DONE segments=1980", repr(logtxt[:80]))
    note("L1 log records neither N nor the command line; N is established separately by replay, by the fact "
         "that range1.c ran as a single process (so N was read from argv once), and by agreement with L2 "
         "(see the release README).")
    return segs


def coverage_L2():
    sums = sorted(glob.glob(os.path.join(L2DIR, "*.sum")))
    others = [f for f in os.listdir(L2DIR) if not (f.endswith(".sum") or f.endswith(".txt"))]
    check("2.L2.no_stray_files", not others, "stray=%r" % others[:5])
    chunks, bad = [], []
    for s in sums:
        t = open(s).read().split()
        if len(t) != 7:
            bad.append((s, "format")); continue
        k, lo, hi, fund, sumh, nle, mx = map(int, t)
        if os.path.basename(s) != "c%05d.sum" % k: bad.append((s, "name"))
        if lo != max(3, k * CH) or hi != min(NMAX, (k + 1) * CH): bad.append((s, "lo/hi"))
        if not os.path.exists(s[:-4] + ".txt"): bad.append((s, "no .txt"))
        chunks.append(dict(k=k, lo=lo, hi=hi, fund=fund, sumh=sumh, nle=nle, mx=mx, txt=s[:-4] + ".txt"))
    check("2.L2.sum_lines_wellformed", not bad, "bad=%r" % bad[:5])
    chunks.sort(key=lambda d: d["k"])
    txts = set(os.path.basename(f) for f in glob.glob(os.path.join(L2DIR, "*.txt")))
    check("2.L2.txt_set_equals_sum_set", txts == set("c%05d.txt" % d["k"] for d in chunks),
          "txt=%d sum=%d" % (len(txts), len(chunks)))
    tile = chunks and chunks[0]["lo"] == 3 and chunks[-1]["hi"] == NMAX and \
        all(chunks[i]["hi"] == chunks[i + 1]["lo"] for i in range(len(chunks) - 1)) and \
        all(d["k"] == i for i, d in enumerate(chunks))
    check("2.L2.tiling_[3,NMAX)_no_gap_no_overlap", tile, "chunks=%d lo0=%d hiN=%d" % (len(chunks), chunks[0]["lo"], chunks[-1]["hi"]))
    check("2.L2.chunk_count_1980", len(chunks) == NSEG, "n=%d" % len(chunks))
    lines = [l.rstrip("\n") for l in open(L2LOG)]
    oks = set(); other = []
    for l in lines:
        m = re.fullmatch(r"(\d+) ok", l)
        if m: oks.add(int(m.group(1)))
        elif l != "DONE": other.append(l)
    check("2.L2.log_no_FAIL_or_other_lines", not other and lines and lines[-1] == "DONE", "other=%r" % other[:5])
    missing = sorted(set(range(NSEG)) - oks)
    check("2.L2.log_ok_lines_1..1979", missing == [0] and max(oks) == NSEG - 1 and len(oks) == NSEG - 1,
          "ok_lines=%d missing=%r" % (len(oks), missing[:5]))
    note("The L2 driver log starts at chunk 1; chunk 0 was made by an earlier invocation of run_list.py whose log "
         "was not kept, and is re-run separately as a replay (see the release README). An earlier, abandoned "
         "invocation left only empty files in a sibling directory ('out_bad_stack'), never used as input here. "
         "The L2 log records neither HMAX nor the command line.")
    bs = os.environ.get("R1_L2_BADSTACK", os.path.join(HERE, "out_bad_stack"))
    if not os.path.isdir(bs):
        check("2.L2.out_bad_stack_not_used", True, "directory not present in this copy (nothing to check)")
        return chunks
    check("2.L2.out_bad_stack_not_used", all(os.path.getsize(f) == 0 for f in glob.glob(os.path.join(bs, "*"))) and
          not glob.glob(os.path.join(bs, "*.sum")), "bad_stack files=%d (all empty, no .sum)" % len(os.listdir(bs)))
    return chunks


# ---------------------------------------------------------------- streaming helpers
class Acc:
    """Accumulates sha256 of the normalised list restricted to h <= T for each T in THRESH, per-h counts/min/max n."""
    def __init__(self):
        self.sha = {t: hashlib.sha256() for t in THRESH}
        self.cnt = {t: 0 for t in THRESH}
        self.maxn = {t: 0 for t in THRESH}
        self.perh = [0] * (N + 1)
        self.hmin = [0] * (N + 1)
        self.hmax = [0] * (N + 1)
        self.lines = 0

    def feed(self, pairs):
        """pairs: list of (n, h) in increasing n, 1 <= h <= N."""
        buf = {t: [] for t in THRESH}
        for n, h in pairs:
            s = "%d %d\n" % (n, h)
            for t in THRESH:
                if h <= t: buf[t].append(s)
            self.perh[h] += 1
            if self.hmin[h] == 0: self.hmin[h] = n
            self.hmax[h] = n
        for t in THRESH:
            if buf[t]:
                self.sha[t].update("".join(buf[t]).encode())
                self.cnt[t] += len(buf[t])
                self.maxn[t] = int(buf[t][-1].split()[0])
        self.lines += len(pairs)
        return buf[N]       # the normalised lines (all h <= N)

    def digests(self):
        return {t: self.sha[t].hexdigest() for t in THRESH}


def parse_file(path, lo, hi, prev_n, hmax=N):
    """Parse 'n h' lines; returns (pairs, noncanon, errors, last_n)."""
    pairs, noncanon, errors = [], 0, []
    with open(path, "rb") as f:
        for raw in f:
            t = raw.split()
            if len(t) != 2:
                errors.append(("format", raw[:40])); continue
            n, h = int(t[0]), int(t[1])
            if raw != b"%d %d\n" % (n, h): noncanon += 1
            if not (lo <= n < hi): errors.append(("range", n))
            if n <= prev_n: errors.append(("order", n))
            if not (1 <= h <= hmax): errors.append(("h", n, h))
            if n % 16 not in FUND_MOD16: errors.append(("mod16", n))
            prev_n = n
            pairs.append((n, h))
    return pairs, noncanon, errors, prev_n


# ---------------------------------------------------------------- check 3/4/6: L1 stream, L2 stream + compare
def stream_L1(segs):
    acc = Acc(); prev = 0; errors = []; noncanon = 0; bad_rec = []
    out = open(os.path.join(OUT, "L1_norm.txt"), "w")
    for i, d in enumerate(segs):
        pairs, nc, err, prev = parse_file(d["txt"], d["lo"], d["hi"], prev)
        noncanon += nc; errors += err[:3]
        if len(pairs) != d["rec"]: bad_rec.append((d["lo"], len(pairs), d["rec"]))
        out.write("".join(acc.feed(pairs)))
        if i % 200 == 0: log("L1 segment %d/%d lo=%d lines so far %d" % (i, len(segs), d["lo"], acc.lines))
    out.close()
    check("3.L1.lines_wellformed_sorted_in_range_h<=3500_mod16", not errors, "errors=%r" % errors[:5])
    check("3.L1.every_line_canonical_'n h'", noncanon == 0, "noncanonical=%d" % noncanon)
    check("3.L1.line_count_per_segment_equals_rec", not bad_rec, "bad=%r" % bad_rec[:5])
    return acc


def stream_L2_and_compare(chunks):
    acc = Acc(); prev = 0; errors = []; noncanon = 0; bad_cnt = []; bad_mx = []
    l1 = open(os.path.join(OUT, "L1_norm.txt"), "rb")
    first_mismatch = None; l1_lines = 0
    for i, d in enumerate(chunks):
        pairs, nc, err, prev = parse_file(d["txt"], d["lo"], d["hi"], prev)
        noncanon += nc; errors += err[:3]
        if len(pairs) != d["nle"]: bad_cnt.append((d["k"], len(pairs), d["nle"]))
        if d["mx"] != (pairs[-1][0] if pairs else 0): bad_mx.append((d["k"], d["mx"]))
        lines = acc.feed(pairs)
        for s in lines:
            a = l1.readline(); l1_lines += 1
            if first_mismatch is None and a != s.encode():
                first_mismatch = (d["k"], a[:40], s[:40])
        if i % 200 == 0: log("L2 chunk %d/%d lo=%d lines so far %d" % (i, len(chunks), d["lo"], acc.lines))
    rest = l1.readline(); l1.close()
    check("3.L2.lines_wellformed_sorted_in_range_h<=3500_mod16", not errors, "errors=%r" % errors[:5])
    check("3.L2.every_line_canonical_'n h'", noncanon == 0, "noncanonical=%d" % noncanon)
    check("3.L2.line_count_per_chunk_equals_n_le", not bad_cnt, "bad=%r" % bad_cnt[:5])
    check("3.L2.maxn_field_equals_last_n", not bad_mx, "bad=%r" % bad_mx[:5])
    check("3.L1_eq_L2.linewise", first_mismatch is None and rest == b"",
          "first_mismatch=%r L1_extra=%r" % (first_mismatch, rest[:40]))
    return acc


# ---------------------------------------------------------------- check 5: externals
def stream_external(opener, path, hmax, negate):
    sha = hashlib.sha256(); cnt = 0; prev = 0; errors = []; perh = [0] * (hmax + 1); hmaxn = [0] * (hmax + 1)
    buf = []
    with opener(path, "rb") as f:
        for raw in f:
            t = raw.split()
            if len(t) != 2: errors.append(("format", raw[:40])); continue
            n, h = int(t[0]), int(t[1])
            if negate: n = -n
            if n <= prev: errors.append(("order", n))
            if not (1 <= h <= hmax): errors.append(("h", n, h))
            prev = n; cnt += 1; perh[h] += 1; hmaxn[h] = n
            buf.append("%d %d\n" % (n, h))
            if len(buf) >= 1 << 20:
                sha.update("".join(buf).encode()); buf = []
    sha.update("".join(buf).encode())
    return sha.hexdigest(), cnt, prev, errors, perh, hmaxn


def read_table(path, ncols):
    rows = {}
    for l in open(path):
        if l.startswith("#") or not l.strip(): continue
        t = l.split()
        rows[int(t[0])] = tuple(int(x) for x in t[1:ncols])
    return rows


def externals(acc):
    dig = acc.digests()
    # Jaswal
    sha, cnt, mx, err, perh, hmaxn = stream_external(gzip.open, JASWAL_GZ, 3000, True)
    RESULT["jaswal"] = dict(sha256_norm=sha, lines=cnt, maxn=mx, gz_sha256=hashlib.sha256(open(JASWAL_GZ, "rb").read()).hexdigest())
    check("5.jaswal.list_wellformed_sorted", not err, "errors=%r" % err[:5])
    check("5.jaswal.count_36993853_max_2562211723", cnt == JASWAL_COUNT and mx == JASWAL_MAXN, "count=%d max=%d" % (cnt, mx))
    check("5.L1_h<=3000_sha256_equals_jaswal", dig[3000] == sha and acc.cnt[3000] == cnt,
          "ours=%s jaswal=%s ours_count=%d" % (dig[3000], sha, acc.cnt[3000]))
    tab = read_table(JASWAL_TABLE, 4)   # h: (F, largest, smallest)
    badt = [(h, tab[h], (acc.perh[h], acc.hmax[h], acc.hmin[h])) for h in range(1, 3001)
            if tab.get(h) != (acc.perh[h], acc.hmax[h], acc.hmin[h])]
    check("5.jaswal.table_h3000_F_largest_smallest_equal_ours", not badt and len(tab) == 3000, "bad=%r" % badt[:3])
    badj = [h for h in range(1, 3001) if perh[h] != acc.perh[h] or hmaxn[h] != acc.hmax[h]]
    check("5.jaswal.list_per_h_equals_ours", not badj, "bad_h=%r" % badj[:5])
    for t in (1000, 1500, 2000):
        check("5.jaswal.README_sha_h<=%d_equals_ours" % t, dig[t] == JASWAL_SHA[t], "ours=%s readme=%s count=%d" % (dig[t], JASWAL_SHA[t], acc.cnt[t]))
    # Kimura
    sha, cnt, mx, err, perh, hmaxn = stream_external(lzma.open, KIMURA_XZ, 2000, False)
    RESULT["kimura"] = dict(sha256_norm=sha, lines=cnt, maxn=mx, xz_sha256=hashlib.sha256(open(KIMURA_XZ, "rb").read()).hexdigest())
    check("5.kimura.list_wellformed_sorted", not err, "errors=%r" % err[:5])
    check("5.kimura.count_16453493_max_1062350083", cnt == KIMURA_COUNT and mx == KIMURA_MAXN, "count=%d max=%d" % (cnt, mx))
    check("5.L1_h<=2000_sha256_equals_kimura", dig[2000] == sha and acc.cnt[2000] == cnt,
          "ours=%s kimura=%s ours_count=%d" % (dig[2000], sha, acc.cnt[2000]))
    tab = read_table(KIMURA_TABLE, 3)   # h: (F, largest)
    badt = [(h, tab[h], (acc.perh[h], acc.hmax[h])) for h in range(1, 2001) if tab.get(h) != (acc.perh[h], acc.hmax[h])]
    check("5.kimura.table_h2000_F_largest_equal_ours", not badt and len(tab) == 2000, "bad=%r" % badt[:3])
    note("The HJKMP per-h table is not available to us (Jaswal's deposit has no copy of it, and neither does "
         "Kimura's); this check is skipped. Jaswal's Remark 4.1 states his F(h) for the 1500 odd h <= 3000 equal "
         "HJKMP's; our per-h counts equal his table_h3000.txt, so the odd-h agreement holds transitively "
         "(consistency only).")


# ---------------------------------------------------------------- check 4 and K6 outputs
def fund_counts(segs, chunks):
    f1 = sum(d["fund"] for d in segs); f2 = sum(d["fund"] for d in chunks)
    check("4.L1_fundamental_count_6018478352", f1 == FUND_JASWAL, "L1=%d" % f1)
    check("4.L2_fundamental_count_6018478352", f2 == FUND_JASWAL, "L2=%d" % f2)
    RESULT["fund"] = dict(L1=f1, L2=f2, jaswal=FUND_JASWAL, L1_decided_S2=sum(d["dec"] for d in segs),
                          L1_exact=sum(d["ex"] for d in segs), L1_recorded=sum(d["rec"] for d in segs),
                          L1_sum_h_exact=sum(d["sumh"] for d in segs), L2_sum_h_all=sum(d["sumh"] for d in chunks),
                          L2_n_le=sum(d["nle"] for d in chunks))
    with open(os.path.join(OUT, "per_segment_fund.txt"), "w") as f:
        f.write("# K6: fundamental n per segment, as COMPUTED. L1 = range1.c (SEG lo hi fund dec ex rec sumh_exact);"
                " L2 = PARI run_list.py (k lo hi fund sum_h n_le maxn). Segmentations differ (L1 lo = 3 + k*1e7).\n")
        f.write("# L1 total fund %d ; L2 total fund %d ; Jaswal 6018478352\n" % (f1, f2))
        f.write("# L1 lo hi fund dec ex rec sumh\n")
        for d in segs: f.write("L1 %d %d %d %d %d %d %d\n" % (d["lo"], d["hi"], d["fund"], d["dec"], d["ex"], d["rec"], d["sumh"]))
        f.write("# L2 k lo hi fund sum_h n_le maxn\n")
        for d in chunks: f.write("L2 %d %d %d %d %d %d %d\n" % (d["k"], d["lo"], d["hi"], d["fund"], d["sumh"], d["nle"], d["mx"]))


def per_h(acc):
    with open(os.path.join(OUT, "range1_per_h.txt"), "w") as f:
        f.write("# K6: per-h counts for h = 1..3500, as COMPUTED from L1 (range1.c, N = 3500, 3 <= n < 19,800,000,000; L1 = L2).\n")
        f.write("# h  F(h)  largest_n  smallest_n\n")
        for h in range(1, N + 1): f.write("%d %d %d %d\n" % (h, acc.perh[h], acc.hmax[h], acc.hmin[h]))
        f.write("# cumulative: h<=2000 count %d max %d ; h<=3000 count %d max %d ; h<=3500 count %d max %d\n" %
                (acc.cnt[2000], acc.maxn[2000], acc.cnt[3000], acc.maxn[3000], acc.cnt[3500], acc.maxn[3500]))
    RESULT["K6"] = {("h<=%d" % t): dict(count=acc.cnt[t], maxn=acc.maxn[t]) for t in THRESH}
    check("6.K6.h<=2000_count_maxn_equal_kimura", acc.cnt[2000] == KIMURA_COUNT and acc.maxn[2000] == KIMURA_MAXN,
          "count=%d max=%d" % (acc.cnt[2000], acc.maxn[2000]))
    check("6.K6.h<=3000_count_maxn_equal_jaswal", acc.cnt[3000] == JASWAL_COUNT and acc.maxn[3000] == JASWAL_MAXN,
          "count=%d max=%d" % (acc.cnt[3000], acc.maxn[3000]))
    check("6.K6.every_h_1..3500_occurs", all(acc.perh[h] > 0 for h in range(1, N + 1)),
          "zero_h=%r" % [h for h in range(1, N + 1) if acc.perh[h] == 0][:5])
    log("K6: h<=3500 count %d, max n %d (h = %d); h<=3000 %d / %d; h<=2000 %d / %d" %
        (acc.cnt[3500], acc.maxn[3500], acc.perh and next(h for h in range(N, 0, -1) if acc.hmax[h] == acc.maxn[3500]),
         acc.cnt[3000], acc.maxn[3000], acc.cnt[2000], acc.maxn[2000]))


def main():
    log("start; python %s" % sys.version.split()[0])
    pin_files = ["range1.c", "run_list.py"]
    for extra in ("range1", os.path.relpath(L1LOG, HERE), os.path.relpath(L2LOG, HERE)):
        if os.path.exists(os.path.join(HERE, extra)): pin_files.append(extra)
    RESULT["pins"] = {p: md5(os.path.join(HERE, p)) for p in pin_files}
    if os.path.exists(GP_PATH): RESULT["pins"]["gp"] = md5(GP_PATH)
    log("pins %s" % json.dumps(RESULT["pins"]))
    segs = coverage_L1()
    chunks = coverage_L2()
    fund_counts(segs, chunks)
    acc1 = stream_L1(segs)
    d1 = acc1.digests()
    RESULT["L1"] = dict(sha256_norm={("h<=%d" % t): d1[t] for t in THRESH}, counts={("h<=%d" % t): acc1.cnt[t] for t in THRESH},
                        lines=acc1.lines)
    log("L1 normalised: lines %d sha256 %s" % (acc1.lines, d1[3500]))
    acc2 = stream_L2_and_compare(chunks)
    d2 = acc2.digests()
    RESULT["L2"] = dict(sha256_norm={("h<=%d" % t): d2[t] for t in THRESH}, lines=acc2.lines)
    check("3.L1_eq_L2.sha256_and_count", d1[3500] == d2[3500] and acc1.lines == acc2.lines,
          "L1 %s/%d L2 %s/%d" % (d1[3500], acc1.lines, d2[3500], acc2.lines))
    externals(acc1)
    per_h(acc1)
    RESULT["L1_norm_sha256_file"] = hashlib.sha256(open(os.path.join(OUT, "L1_norm.txt"), "rb").read()).hexdigest()
    check("3.L1_norm_file_sha256_equals_stream", RESULT["L1_norm_sha256_file"] == d1[3500])
    allok = all(c["pass"] for c in RESULT["checks"].values())
    RESULT["ALL_PASS"] = allok
    json.dump(RESULT, open(os.path.join(OUT, "r1check_result.json"), "w"), indent=1)
    log("ALL %s (%d checks)" % ("PASS" if allok else "FAIL", len(RESULT["checks"])))
    return 0 if allok else 1


if __name__ == "__main__":
    sys.exit(main())
