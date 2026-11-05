# FORMAT: the per-range certificate

This is the interchange format for a range of the block sieve: what a collaborator generates for a range, how the
files are named, what the kernel checks, what counts as accepted, and how ranges are claimed and merged. It is exact
enough to implement from; `gen/` implements it and `example/` is one instance.

## 1. The target, and what a range is

A **target** is a triple (N, F, X) with a W list: the bound N (3500), the largest |D| of class number ≤ N
(F = 3,495,584,467, from the classification), the kernel-checked threshold (X = 2.8·10^10; see README.md, "The
threshold"), and W = the radicands above F that the split-prime count cannot certify at any Y (DATA, from the scan;
unknown until it runs). The statement to prove is the range statement of DESIGN.md, section 5, over F < d < X.

Radicands are sieved by **family**, because d and the role of 2 differ:

| family | residue m mod 4 | d | radicand range for the target | lanes in all (ESTIMATE at X = 2.8·10^10) |
|---|---|---|---|---|
| A | 3 | m | [F + 1, X) | 7.0·10^9 |
| B1 | 1 | 4m | [F/4 + 1, (X + 3)/4) | 1.75·10^9 |
| B2 | 2 | 4m | [F/4 + 1, (X + 3)/4) | 1.75·10^9 |

(m ≡ 0 mod 4 is never squarefree.) A **range** is one family and a half-open integer interval [m_start, m_end) of
radicands; the generator walks it in blocks of L lanes (L = 10^5 at full scale) starting at the first m ≥ m_start of
the family's residue, and shortens the last block so that its last lane is below m_end. So ranges tile a family's
interval exactly when consecutive ranges satisfy m_end = next m_start.

Below F the same format applies, but there the exception set contains every listed field (h ≤ N, by construction
uncertifiable) and must go to pillar 3; a collaborator starting out should take ranges above F.

## 2. What a collaborator generates for a range

Inputs: the target (N, F, X), the family, [m_start, m_end), L, the first block index k0, and the shared table
(section 3) sized for the whole target. Output, per range (all relative to an output directory):

```
Gen/<fam>/B<k>.lean                 one module per block, k = k0, k0 + 1, …, zero-padded to 5 digits
exceptions_<fam>_<k0>.txt           the squarefree lanes left uncertified, one radicand per line, increasing
MANIFEST_<fam>_<k0>.json            {"Gen/<fam>/B<k>.lean": "<md5>", …}, sorted keys
```

A block module is exactly (whitespace included; `gen/gen_blocks.py` writes it):

```lean
import BoundariesOfClass.Sieve.Block.Defs
import BoundariesOfClass.Sieve.Block.Base.Pats
import BoundariesOfClass.Sieve.Block.Base.Primes

namespace BoundariesOfClass.Sieve.Block.Gen

def blk_<fam>_<k> : Blk := ⟨<fam: 0|1>, <N>, <L_b>, <m0>, <Y>, Base.pats, Base.oddPrimes, <E>⟩

set_option maxRecDepth 1000000 in
theorem blk_<fam>_<k>_ok : blockOK blk_<fam>_<k> = true := by decide +kernel

end BoundariesOfClass.Sieve.Block.Gen
```

with fam 0 for A and 1 for B1, B2; L_b = min(L, ⌈(m_end − m0)/4⌉); m0 ≡ residue (mod 4); Y = ⌊√((m0 − 1)/4)⌋ for
A and ⌊√(m0 − 1)⌋ for B (so 4Y² < d for every lane; `blockOK` checks it); E = the uncertified-lane mask as a decimal
literal (bit i ↔ lane m0 + 4i), computed by the generator's Python mirror of `Defs.lean` and recomputed by the kernel.

**The JSON form** of a block is the same eight fields, for tools and for the claims ledger:

```json
{"fam": "A", "N": 3500, "L": 100000, "m0": 3495584471, "Y": 29561, "E_md5": "<md5 of the decimal E>", "k": 0}
```

(E itself is only in the Lean file; its md5 is enough to pin it.) The exception list is the set bits of E with their
lanes; it is DATA.

**Command (the example's values):**

```
python3 gen/gen_blocks.py <out> <N> <A|B1|B2> <m_start> <m_end> <L> --shared <out>/shared_lists.json --k0 <k0>
```

## 3. The shared table (once per target)

The pattern primes are the odd primes up to YMAX = ⌊√((X − 1)/4)⌋ (83,666 at X = 2.8·10^10: about 8,200 primes) and
the square primes the odd primes up to PMAX = ⌊√(X + 4L)⌋ + 1. `gen/gen_shared.py <out> <YMAX> <PMAX>` writes

```
BoundariesOfClass/Sieve/Block/Base/Chunk_<kkk>.lean    chunk_<kkk> : List (ℕ × ℕ) of (q, basePat q), Σq ≤ 10^5 per chunk;
                                                        theorem chunk_<kkk>_ok : chunkOKB chunk_<kkk> = true := by decide +kernel
BoundariesOfClass/Sieve/Block/Base/Pats.lean            pats := (<right-nested ++ of groups of 16 chunks>).flatten;
                                                        pats_incr (decided), pats_chunks_ok (a proof TERM over the chunk theorems), pats_ok : PatsOK pats
BoundariesOfClass/Sieve/Block/Base/Primes.lean          oddPrimes, in groups of 256 (no theorem)
shared_lists.json, MANIFEST_shared.json
```

Every block imports `Base.Pats` and `Base.Primes`, so every collaborator must use the SAME shared table (same md5s),
generated from the same (YMAX, PMAX, sigma). At N = 1000 the table was 227 chunks, built in 25 minutes on 2 processes
(MEASURED); at the h ≤ 3500 size it is about 4 times larger in Σq (ESTIMATE). Note the chunk-size rule: one Lean list
literal costs about 1.7 KB of olean per element, and a literal of more than about 4,000 entries, or a term nested
more than about 200 deep, exceeds the elaborator's default `maxRecDepth`, which may be raised only on the decided
theorem. Hence the groups.

## 4. The exception list and its Y values

`gen/make_xs.py <xs.json> <N> <exceptions files…> --w W.txt` produces, for the union of the ranges' exception files,

```json
{"N": 3500, "xs": [[m, Y], …]}
```

sorted by m, where Y is the smallest value on a 16-point grid at which `checkAt N Y P m` holds (found by
`gen/checkat_mirror.py`, a Python mirror of `sieveList` + `mu` WITH ramified primes), or 0 if m is in W. Real mode
refuses any m that is neither: such an m is a new W candidate and needs an exact class number. Y is DATA; the
assembly check re-runs `checkAt` in the kernel.

## 5. The assembly (once per target, after every range is delivered)

`gen/gen_asm.py <out> <xs.json> <block dirs…> [--params F X N W.txt]` writes

```
BoundariesOfClass/Sieve/Block/Asm/SP/Chunk_<kkk>.lean   (p, sqMask p) for 2 and the odd primes ≤ max listed Y; spChunkB decided
BoundariesOfClass/Sieve/Block/Asm/SP/P.lean             P and P_ok : PrimesOK P
BoundariesOfClass/Sieve/Block/Asm/Main.lean             imports every block; Bs (a balanced ++ tree of groups of 16), xs, ONE decided theorem, asm_hB (a proof term)
MANIFEST_asm.json
```

Without `--params` the decided theorem is `asmB Bs SP.P xs = true` (the h ≤ 1000 instance, whose soundness is
proved). With `--params F X N W.txt` it is `asmP Bs SP.P xs = true`, the parametrised check whose soundness lemma is
OPEN (DESIGN.md, section 6). `Main.lean` has exactly one decided theorem; the per-block facts are assembled by a
generated proof term, never by a second `decide`.

## 6. How a range is checked

**Build.** In a copy of entry 5's `formalization/` with `lean/` added (lean/README.md), the shared table in place, and
the range's `Gen/<fam>/B*.lean` under `BoundariesOfClass/Sieve/Block/Gen/<fam>/`:

```
lake build BoundariesOfClass.Sieve.Block.Gen.<fam>.B<k>      # one block, or
lake build BoundariesOfClass.Sieve.Block.Asm.Main            # everything, at the end
```

Each block is one Lean process of 9–16 GB at Y ≤ 20,000 and L = 10^5 (MEASURED); size L so that a block fits your
RAM, and run as many processes as fit. Expected: exit 0, no `sorry`. A block whose E is wrong fails here.

**Axioms.** `#print axioms BoundariesOfClass.Sieve.Block.Gen.blk_<fam>_<k>_ok` must print exactly
`[propext, Classical.choice, Quot.sound]`. `decide +kernel` adds no axiom; `native_decide` (which adds
`Lean.ofReduceBool`), `Lean.ofReduceBool`, `debug.skipKernelTC` and `sorry` are forbidden everywhere.

**The second kernel.** The kernel check of record is a replay of the exported closure by a second, independent
checker. The h ≤ 1000 harness used nanoda (a Rust re-implementation of the Lean kernel) with `nat_extension: true`
(so that it accelerates `Nat.land`, `lor`, `xor`, `shiftLeft`, `shiftRight`, `pow` as Lean's kernel does), the three
standard axioms permitted and `unpermitted_axiom_hard_error: true`, on an export by lean4export 3.1.0, and Comparator
to drive both kernels against a challenge statement. MEASURED on prototype blocks: nanoda accepts a correct block
(exit 0, "Checked … declarations with no typechecker errors", 3 s at 10^5 lanes and Y = 3,535) and rejects a block
with one E bit flipped compiled under `skipKernelTC` (a `def_eq` panic, exit 101) and an export with a spurious axiom
("unpermitted axiom", exit 1). Two practical notes: the pinned nanoda's hard-coded 16 MiB thread stack overflows on
a full-size block and must be raised in its source (a one-constant change, reviewed and accepted as not affecting
what it accepts); and the Comparator replay costs 28–43 s (Lean kernel) plus 8–34 s (nanoda) per block above a 7 s
overhead, with peak RSS near 16 GB at Y = 20,000 (MEASURED, H1 measurement note). Whether the peak grows with the
number of blocks in one replay is unmeasured.

**Shape of the decided propositions.** Every generated module must contain exactly one `decide +kernel` theorem, of
the stated shape (`blockOK <own constant> = true`, `chunkOKB <own chunk> = true`, `incr (…) = true`,
`spChunkB … = true`, `asmB/asmP … = true`), under `set_option maxRecDepth 1000000 in` on that theorem only, and no
other `decide`; the h ≤ 1000 harness enforced this with a structural check over the oleans. Hand-written modules
contain no `decide` at all.

## 7. Acceptance criteria for a delivered range

A range is accepted when all of the following hold:
1. **Regenerate-and-diff.** `gen_blocks.py … --verify` (same arguments, same shared table) prints
   `REGENERATE-AND-DIFF PASS`: every block file and the exceptions and manifest files are byte-identical to a fresh
   regeneration by the pinned generator. The generator is deterministic (no timestamps, sorted keys).
2. **Build.** Every block module builds with exit 0 under the pinned toolchain (section 6).
3. **Axioms.** The standard three, for every block theorem.
4. **Second kernel.** The exported closure of every block module is accepted by nanoda with the settings of section
   6 (per module, or in one replay at the end), with the export's byte size recorded, and nanoda re-run on a copy
   with one digit of one block's E changed, which must exit non-zero. (The pinned nanoda prints nothing on success,
   and an empty or truncated export also exits 0.)
5. **Exceptions settled.** Every radicand in the range's exception file is in `xs.json` with a Y at which
   `checkAt N` holds, or in W. (Real-mode `make_xs.py` guarantees this or refuses.)
6. **Coverage** (section 8).
7. **Record.** The delivery names the shared-table md5s, the generator md5s, the toolchain, the build log with wall
   time and peak RSS per block, and the nanoda log.

A negative control is part of every acceptance: one block of the range with one E bit flipped must FAIL the build.

## 8. Claiming and merging ranges without gaps or overlaps

Ranges are claimed in a ledger, one JSON object per line:

```
{"fam": "A", "m_start": 3495584468, "m_end": 3600000000, "L": 100000, "k0": 0, "who": "<name>", "status": "claimed"}
```

Rules: `m_start`/`m_end` are radicand bounds of the family; the block index `k0` is unique per family and a range of
c blocks occupies [k0, k0 + c), where c is computed exactly as `gen_blocks.py` walks the range (so two ranges can
never write the same `B<k>.lean`); a claim becomes `delivered` once sections 6–7 pass. `gen/cover_check.py` checks,
with no Lean:

```
python3 gen/cover_check.py CLAIMS.jsonl <F> <X> <N> [--blocks <dir> …] [--xs xs.json]
```

- per family, the claims tile [F + 1, X) (A) or [F/4 + 1, (X + 3)/4) (B1, B2) exactly, as half-open integer
  intervals, with no gap and no overlap, and their block-index ranges are disjoint;
- with `--blocks`, every delivered claim's block files exist and each `Blk` literal has the claimed N, the family's
  residue, 4Y² < m0 (A) or Y² < m0 (B), lanes inside the claim, and consecutive blocks that abut, the last ending at
  or just past m_end;
- with `--xs`, every exception lane lies in a delivered claim of its family.

Every line of its output starts with PASS or FAIL and it ends with `COVER CHECK PASS` or `FAIL`. The kernel's own
coverage check is `coversB` inside the assembly (section 5): the ledger is for coordination, `coversB` is the proof.

## 9. Sizes and timings to plan with (at X = 2.8·10^10, L = 10^5)

| what | value | label |
|---|---|---|
| blocks in all | 105,000 | ESTIMATE (3X/8 lanes / L) |
| Y per block | 29,561 (at F) to 83,666 (at X) | exact |
| Lean build per block | 4.3 s + 1.3 ms·Y, i.e. 43–112 s | ESTIMATE from the MEASURED fit (14.0 s at Y 7,555; 30.1 s at Y 20,027) |
| RAM per block | 9.4–15.8 GB at Y ≤ 20,000; beyond that unmeasured | MEASURED / OPEN |
| olean per block | about 24 KB (the pattern table and definitions are shared modules) | MEASURED |
| exception lanes above F | at N = 1000: 214 in 5,165 blocks (18 W + 196 `checkAt`-settled, max Y 8,061) | MEASURED (Python scan) |
| exception lanes above F at N = 3500 | a few hundred to a few thousand | ESTIMATE |
