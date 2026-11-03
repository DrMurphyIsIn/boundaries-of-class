# Imaginary quadratic fields of class number at most 3500

This is the sixth entry of this repository, *The Boundaries of Class*. It extends Manvir Jaswal's classification
of the imaginary quadratic fields with class number at most 3000 to **class number at most 3500**, on the same
footing: a conditional, explicit real-zero bound for Dirichlet L-functions (Kimura's "(K)"), which Kimura reports
as checked in Lean by two independent kernels but which is not itself refereed. Under (K):

> Exactly **50,299,869** imaginary quadratic fields have class number at most 3500. The largest absolute
> discriminant among them is **3,495,584,467**, of class number 3477.

This is *not* a kernel-checked result, and we try to be exact about which parts of it are and are not (see
"What is and is not kernel-checked" below, and the paper's Section 4). The method is Jaswal's; the footing is
Kimura's; the unconditional input below `2^40` is Mosunov and Jacobson's tabulation. What this entry adds is: an
independent re-implementation of every computational step we don't just cite, sharing no code with Jaswal's or
Kimura's programs; a cross-check of every step against a second program or against the published data, including
an exact reproduction of both earlier lists; and a precise account of what rests on what.

Start with the paper, [`paper/paper.pdf`](paper/paper.pdf) (source: [`paper/paper.tex`](paper/paper.tex),
[`paper/refs.bib`](paper/refs.bib)). It is the authority for anything this README summarizes; where the two
disagree, read the paper.

## The four ranges

Following Jaswal, the classification covers every `n = |D| >= 3` (D a negative fundamental discriminant) by four
ranges, each closed by a different argument:

| range | `n = |D|` | argument | directory |
|---|---|---|---|
| (1) | `3 <= n < 19,800,000,000` | direct computation of every `h(D)`, by two independent programs | [`range1/`](range1/) |
| (2) | `19,800,000,000 <= n < 2^40` | Mosunov-Jacobson's tabulation: `min L(1,chi) ~ 0.17070`, so `h > 7640` | cited only; see the paper, Section 2 |
| (3) | `2^40 <= n <= 1,606,926,912,624,720` | a Watkins-style sieve at bound `N = 3500` (Jaswal's procedure) | [`range3/`](range3/) |
| (4) | `n >= 1,606,926,912,624,721` | (K) plus Hecke's integral representation: `h >= 3562` | [`range4/`](range4/) |

Range (2) rests entirely on a published, unconditional tabulation ([Mosunov and Jacobson 2016][mj16]); we read it
at source and cite it, and there is nothing of ours to release for it. The directory [`cover_check/`](cover_check/)
holds the checker that verifies the four ranges tile `[3, infinity)` exactly, with the right boundary between (3)
and (4), certified in interval arithmetic. [`remark2/`](remark2/) holds the independent, shorter route described
in the paper's Remark on a "7/8 hypothesis" shortcut, which does not use range (3) at all.

## Layout

- [`paper/`](paper/) — the paper: `paper.tex`, `refs.bib`, `paper.pdf`.
- [`range1/`](range1/) — range (1): `range1.c` (our program, PARI-independent) and `run_list.py` (the PARI/GP
  `qfbclassno` cross-check), their driver logs, the verification script `r1check.py` and a public summary of its
  result, the per-h and per-segment outputs, and the digest of the `h <= 3000` overlap with Jaswal's list below `10^7`.
- [`range3/`](range3/) — range (3): the sieve `rsieve_v4.c`, its driver scripts, the eleven run logs/outputs at
  `N = 3500` (the production run, `p35_*`) with their checksums (`P35_RUNS_MD5S.txt`), and the eleven run
  logs/outputs at `N = 3000` (`a2_*`), which reproduce Jaswal's own counts for that range and are cited in the
  paper's checks.
- [`range4/`](range4/) — range (4): `certify_p27.py`, the interval-arithmetic certificate for Jaswal's
  Proposition 2.7 constant, and its output.
- [`remark2/`](remark2/) — the independent "7/8 hypothesis" route of the paper's Remark: `b_h78.py` and its
  output at 6000 terms.
- [`cover_check/`](cover_check/) — `cover_check.py`, the checker that the four ranges tile the integers correctly
  and that the range-(3) production run covers exactly Jaswal's eleven intervals with no field left over, and its
  recorded output at `N = 3500` (`COVER_CHECK_p35.out`).
- `MD5SUMS.txt` — an MD5 checksum for every file in this release.

## The full list

The full list of all 50,299,869 fields with `h <= 3500` (one `"n h"` pair per line, sorted by `n`) is **not** in
this git directory — at 727 MB it belongs in a data deposit, not a source repository. It is deposited on Zenodo
together with this release (DOI to follow; see the paper's title page for the concept DOI covering all versions).
Its SHA-256 is:

```
cedfb7c440bc0814beaff0e3882649e5cd188dcc71daa7adf9bdb5e7a502057b
```

This is also the digest recorded for the `h <= 3500` line in the tables below and in `r1check.py`'s own output,
since the full list is exactly the normalised, concatenated output of range (1) (ranges (2)-(4) contribute no
fields, having certified that none of them has `h <= 3500`).

## How to rebuild and rerun each piece

Everything here uses `python3`, `cc`/`clang`, and (for range (1)'s second program) `gp` (PARI/GP). Nothing here
needs the internet, Lean, or any other external code. Pin BLAS/thread environment variables to 1 before running
anything numeric, as we did:

```sh
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1
```

**Range (4) — the interval-arithmetic certificate (seconds).**

```sh
cd range4 && pip install mpmath   # if not already installed
python3 certify_p27.py            # should reproduce certify_p27.out
```

**Remark 2 — the 7/8-hypothesis constant (well under a minute).**

```sh
cd remark2 && pip install python-flint
python3 b_h78.py 6000             # should reproduce b_h78_6000.out
```

**`cover_check/cover_check.py` — the tiling and coverage checker (seconds).**

```sh
cd cover_check
python3 cover_check.py                                              # the four-range tiling alone
python3 cover_check.py --runs ../range3/runs p35_ 3500               # against the N=3500 production logs
python3 cover_check.py --runs ../range3/runs a2_ 3000                # against the N=3000 reproduction logs
```
The first form reproduces the first six lines of either recorded output; the `--runs` forms reproduce
`COVER_CHECK_p35.out` and `cover_check_a2.out` exactly.

**Range (3) — rebuilding and spot-checking the sieve (minutes; the eleven real production runs together take
about three and a half hours per stream and are **not** meant to be rerun casually — see below).**

```sh
cd range3
cc -O3 -Wall -o rsieve_v4 rsieve_v4.c -lpthread -lm        # reproduces the pinned binary byte-for-byte
```
Each of the eleven `N = 3500` runs is a single invocation of `run_sieve.sh <tag> rsieve_v4 rsieve_v4.c <N> <A>
<A2> <P> <Y> <threads>`, with the exact arguments in `run_p35_A.sh` and `run_p35_B.sh`. The eleven intervals grow
geometrically (each is twice the size of the last), so their running times do too: the smallest, `p35_00`, took
about 11 minutes on 8 threads, and the largest, `p35_09`, took about 30 hours. Split two ways and run as two
parallel streams (`run_p35_A.sh`, six intervals; `run_p35_B.sh`, five), the two streams took about 43 and 47 hours
respectively (see the `start`/`end` timestamps in `runs/p35_*.log`) — on the order of two days total, not 30
minutes, which is why we did not rerun them for this release. `run_a2.sh` runs the same eleven intervals at
`N = 3000`, which is what reproduces Jaswal's own published counts for that range; it is comparably expensive. We
verified the recorded outputs instead: they already ran once each, successfully, with `match=1` and zero
leftovers in every interval, and we verified their outputs by checksum (`P35_RUNS_MD5S.txt`), and by the
`cover_check --runs` reproduction above, which recomputes the summary numbers straight from the recorded logs.
If you do want to rerun one, `run_sieve.sh` refuses to overwrite an existing log, so move or remove
`runs/<tag>.log` first.

**Range (1) — rebuilding and spot-checking (seconds to rebuild; the full runs take hours, see below).**

```sh
cd range1
cc -O3 -Wall -o range1 range1.c -lpthread -lm               # reproduces the pinned binary byte-for-byte
./range1 test 3000 3 1000000                                 # unit tests: ~1 second, "bad=0 unsafe=0"
```
The full range-(1) computation — every fundamental `n < 19,800,000,000`, by both programs — takes on the order of
10-20 core-hours total (the paper's own estimate: about 7 core-hours for the exact count, 10 for the class-order
test, and a comparable amount for the PARI cross-check), so it is well outside a 30-minute budget and we did not
rerun it for this release. We verified its stored output instead: `logs/ours_full_run.log` and
`logs/pari_full_run.log` record the two full runs that produced the 50,299,869-field list, and
[`verify_range1_summary.md`](range1/verify_range1_summary.md) records every digest and count that
`r1check.py` computed from their full per-segment output (which, like the merged list, is too large for this
git directory and is not included here). If you do rerun range (1) in full:
```sh
./range1 3500 3 19800000000 10000000 <threads> ours_full      # -> range1/ours_full/
python3 run_list.py <workers>                                 # -> range1/out/ (PARI qfbclassno; needs gp)
python3 r1check.py                                             # cross-checks the two, against the digests above
```
`r1check.py` also compares against Jaswal's and Kimura's published lists if you place copies of them under
`range1/external/jaswal/` and `range1/external/kimura/` (see the paper's bibliography for where to get them); it
skips that part of the comparison gracefully if they are absent. For the sub-range `n < 10^7`,
[`range1/comparison/OVERLAP_DIGESTS.md`](range1/comparison/OVERLAP_DIGESTS.md) records that the `h <= 3000` extracts
of our list and of Jaswal's are byte-identical (2,956,309 lines each), with their common SHA-256 and the command that
regenerates them; the extracts themselves are not stored, since Jaswal's data belongs to his own deposit.

## The checks, and what they show

These are the paper's Section 3 checks, in the same order:

1. **Range (1), two programs.** `range1.c` and `run_list.py` (PARI `qfbclassno`) produce byte-identical lists of
   `(n, h)` with `h <= 3500`: 50,299,869 lines. Both tile `[3, 19,800,000,000)` with no gaps. The fundamental
   count, 6,018,478,352, matches Jaswal's.
2. **Reproduction of the earlier lists.** Our `h <= 3000` sub-list has the same SHA-256 as Jaswal's published
   list; our `h <= 2000` sub-list has the same SHA-256 as Kimura's. Every per-h count agrees.
3. **Range (3) at N = 3000.** Before running at 3500, the sieve ran at Jaswal's own bound, 3000, on all eleven
   intervals; the counts treated and the counts reaching the final (exact) step equal his published values,
   interval by interval, and the totals equal his 535,275,800,332,314.
4. **Range (3) coverage at N = 3500.** `cover_check.py --runs` verifies that the eleven intervals are consecutive,
   meet the exact (3)/(4) boundary, were each run exactly once at `N = 3500`, that the number of `n` treated
   equals a direct count, and that nothing is left unsettled. It passes.
5. **Separate review.** A separate AI review session (same model family, same operator; not a human referee)
   re-ran the cover check and reproduced it byte-identically, and re-ran the first interval of range (3) at
   `N = 3500` from a copy of the pinned program, reproducing it byte-identically. This review is not a substitute
   for a human referee.

## What is and is not kernel-checked

Quoting the paper's Section 4 nearly verbatim:

- **(K)** is Lean-checked, with two independent kernels, according to Kimura; we have not replayed his
  formalization ourselves. (K) also follows from the zero-free half-plane `Re s > 7/8` for Dirichlet
  L-functions announced by OpenAI — a half-plane we *have* checked ourselves, by replaying OpenAI's Lean proof
  through two independently built checkers and, separately, through an export accepted by five checkers (see the
  paper for the exact theorem name and commit). A kernel check certifies the formal proof, not the manuscript:
  neither manuscript is refereed, and the match between the formal statement and the mathematical one was
  checked by reading it. (K) likewise follows from Cureton and Thorner's half-plane `Re s > 31/32` for Dedekind
  zeta functions, which we have not built.
- **Range (4)** is a short analytic argument plus one numerical constant, which we certified in interval
  arithmetic (`range4/certify_p27.py`). It is a natural first target for formalization.
- **Range (2)** rests on a published, unconditional, but large tabulation (Mosunov and Jacobson).
- **Range (1)** rests on agreement between two independent programs (ours and PARI/GP) and with the published
  lists — not on a kernel.
- **Range (3)** at `N = 3500` was run by our sieve alone. The evidence is that the same code reproduces Jaswal's
  counts at `N = 3000` exactly, interval by interval, together with the coverage checks at `N = 3500`; it is not
  kernel-checked. Under the "7/8 hypothesis" route of Remark 2 (`remark2/`), it is not needed at all.

A direct kernel replay of the range-(3) sieve with current tools would, by our measurements, take on the order of
hundreds of days on a single workstation, so we have not attempted it. We release the inputs, programs and logs
in a form intended to make such an effort — by us or by others — as straightforward as possible.

## What we do and do not claim

We claim the classification above under (K), with the checks described, and the same list under the "7/8
hypothesis" route of Remark 2. We do not claim the method: it is Jaswal's, on Kimura's footing and Watkins's
sieve, with Mosunov and Jacobson's tabulation; we have followed it closely. We do not claim the result is
kernel-checked. The bound 3500 was our choice, set by the computing budget for range (3). This says nothing about
real quadratic fields, non-maximal orders, or the Riemann hypothesis. Where this README or the paper states a
count or a digest and the released files disagree, the released files are the authority.

## Credits

As the paper gives them:

- **The challenge** is Terence Tao's: an experimental AI-math challenge exploring the arguments ruling out
  Landau-Siegel zeros, posted 20 October 2026, with a request that contributors disclose their use of AI and not
  race for priority.
- **The footing (K)** and the reduction to a finite search are Iwao Kimura's (arXiv:2610.21511v2), building on
  the argument released by OpenAI and its Lean formalization (openai/math). Banks, Kerr and Green have given
  independent proofs of the Siegel-zero bound.
- **The method, its parameters, and the classification up to `h <= 3000`** that we extend are Manvir Jaswal's
  (Zenodo, doi:10.5281/zenodo.23547020, programs and data doi:10.5281/zenodo.23251366); we followed his paper and
  his published data closely and checked our work against them throughout.
- **The sieve** goes back to Mark Watkins (2004); **range (2)** is the tabulation of A. S. Mosunov and
  M. J. Jacobson, Jr. (2016).
- We thank the PARI/GP developers.
- Kimura states that the explicit argument, the Lean files, the sieve program and most of the text of his paper
  were done with an AI assistant under his direction. Jaswal writes that his paper was produced by a multi-agent
  AI research system that he built and ran: apart from the work of others that it cites, the ideas, proofs,
  computations and text are due to that system.

## AI disclosure

As the paper states it: the programs, the checks and the paper were produced with extensive use of an AI
assistant (Claude, Anthropic) under the direction of the author. A separate AI session, of the same model family
and under the same operator, reviewed the plan, the statements, each completed range and the paper, and re-ran
the cover check with its own copy. That review is not a substitute for a human referee. The mathematical route is
due to the people credited above; the account of status, the attributions, and the account of how the work was
checked are the author's, stated as obtained.

## A note on the released scripts

A few comments and file paths in the scripts here have been rewritten from their working form so that every
script reads its inputs relative to its own directory and carries no internal project names. `r1check.py`'s input
paths are now overridable by environment variables (see its docstring) and it skips gracefully over inputs this
release does not ship (the full per-segment output of range (1), and the externally published Jaswal/Kimura
lists); its logic and its checks are otherwise unchanged, and it reproduces the digests quoted above. No other
behavior was changed: every rebuilt binary reproduces the pinned one byte-for-byte, and every rerun check
reproduces its recorded output byte-for-byte (see `REPORT.md` in the parent directory for the full list of
reruns and diffs).

[mj16]: https://doi.org/10.1090/mcom/3029 "Mosunov and Jacobson, Math. Comp. 85 (2016), 1983-2009"
