# Range (1) verification: summary

This is a cleaned, public summary of the verification run of `r1check.py` against the two range-(1) programs'
full output (3 <= n < 19,800,000,000). It reports the same checks, counts and digests that the paper's Section
3 cites; it omits internal file references that are not part of this release and is not itself a script output.
Running `r1check.py` against a freshly regenerated copy of both programs' output should reproduce every number
below (see the main README for how).

## Coverage

Both programs' output tiles `[3, 19,800,000,000)` with no gaps and no overlaps: 1,980 segments for `range1.c`
(10,000,000 wide, by construction) and 1,980 chunks for `run_list.py`. No stray files. One early, abandoned
invocation of `run_list.py` left a handful of empty files in a side directory that was never read as input; its
one chunk (chunk 0) was separately replayed and reproduced.

## L1 = L2 (the two programs agree)

As normalised `"n h"` lists restricted to `h <= 3500`, the two programs' output is **byte-identical**:
50,299,869 lines, SHA-256 `cedfb7c440bc0814beaff0e3882649e5cd188dcc71daa7adf9bdb5e7a502057b`. This is also the
SHA-256 of the full field list (`L1_norm.txt`), which is **not** part of this git release and is instead
deposited on Zenodo with it (see the top-level README).

## Fundamental counts

Both programs find 6,018,478,352 fundamental discriminants below 19,800,000,000, matching Jaswal's count.

## Agreement with the published lists

| sub-list | count | largest `|D|` | SHA-256 | matches |
|---|---|---|---|---|
| h <= 1000 | 4,115,897 | 227,932,027 | `075a201c8e7cce6c0b6013423a5d96c6308452afab2fa79882388fc46d8b0c45` | Jaswal's published digest |
| h <= 1500 | 9,245,562 | 562,394,347 | `c373d7c67bbecb922878481c50e6273f03ed07b93fc968a458bb0bf5389ee101` | Jaswal's published digest |
| h <= 2000 | 16,453,493 | 1,062,350,083 | `07100ea3589ab2b490122fa69b438cd5393bdcd2e547dfc29bb3b5c86f9f24c0` | Jaswal's digest **and** Kimura's published list |
| h <= 3000 | 36,993,853 | 2,562,211,723 | `54cea699cdc11ecaa794445cf52ee1a6ad7a8306ab2e0a6d5aa55c2c1fb29ea7` | Jaswal's published list |
| h <= 3500 | 50,299,869 | 3,495,584,467 (h = 3477) | `cedfb7c440bc0814beaff0e3882649e5cd188dcc71daa7adf9bdb5e7a502057b` | (this release; no prior list to compare) |

Every per-h count (`range1_per_h.txt`) agrees with Jaswal's table for h <= 3000 and with Kimura's for h <= 2000.
The odd-h counts below 3000 are not compared directly against Hilbert/Jacobson-type tables (HJKMP), which
neither published deposit includes; the agreement is transitive, through Jaswal's own Remark 4.1, and is a
consistency check only, as the paper states.

## The "N not logged" gap, and how it is closed

Neither program's own driver log records the bound N (3500) or the exact command line used for the full run.
This is closed by replay, not by the log: a handful of segments and chunks were re-run from the pinned
binary/script with the recorded arguments and reproduced byte-identically (including a segment with ten lines
at exactly h = 3500, which would differ at any smaller N); every stored line has h <= 3500; every h from 1 to
3500 occurs; and the two programs, which compute independently, agree on every line. Each program also ran as a
single uninterrupted process, so N was read from its command line exactly once.

## Unit tests and rebuild

- Brute-force vs. the exact reduced-form count, and brute-force class order vs. baby-step/giant-step, agree on
  3,000 random discriminants with 0 mismatches and 0 unsafe comparisons (see `range1.c`'s `test` mode).
- `cc -O3 -o range1 range1.c -lpthread -lm` reproduces the pinned binary byte-for-byte.

## Result

**All checks pass.** See the paper, Section 3 (Checks), items 1 and 2.
