# example/: one tiny range certificate, N = 10 over F(10) < d < X_10

This is the per-range certificate format of FORMAT.md run end to end, in Python, on the smallest interesting case:
the range statement "every imaginary quadratic field with 13,843 < |D| < 54,500 has class number more than 10, except
the two fields with |D| = 16,003 and 17,803". Here 13,843 = F(10) is the largest |D| of class number at most 10, and
54,500 = X_10 is entry 5's kernel-checked threshold (`lt_classNumber_of_le_dOf_le_ten`: 54,500 ≤ |D| forces h > 10).
The two excepted fields have class number 12 (MEASURED by the first design's independent reduced-form count, and by
PARI; they are the "W" fields of this range: the split-prime count cannot certify them at any Y, so they need an exact
class number, which is pillar 3).

Everything under `run/` was produced by the commands below, on 2026-11-04, by the generators in `../gen/`. The Lean
build, the axiom check, the second kernel and both negative controls were run on 2026-11-04; the recorded outputs are
at the end of "How to build and check it".

## The generated files

```
run/shared_lists.json                                     the pattern primes (29 odd primes <= 116) and the square primes (52 odd primes <= 242)
run/BoundariesOfClass/Sieve/Block/Base/Chunk_000.lean     the shared pattern table, one chunk; theorem chunk_000_ok : chunkOKB chunk_000 = true
run/BoundariesOfClass/Sieve/Block/Base/Pats.lean          pats := ([chunk_000]).flatten; pats_incr (decided), pats_chunks_ok (a proof term), pats_ok : PatsOK pats
run/BoundariesOfClass/Sieve/Block/Base/Primes.lean        oddPrimes, the 52 odd primes <= 242 (no theorem)
run/Gen/A/B00000.lean .. B00010.lean                      11 family-A blocks (d = m, m = 3 mod 4), m from 13847, up to 1000 lanes each
run/Gen/B1/B00000.lean .. B00002.lean                     3 family-B1 blocks (d = 4m, m = 1 mod 4), m from 3461
run/Gen/B2/B00000.lean .. B00002.lean                     3 family-B2 blocks (d = 4m, m = 2 mod 4), m from 3462
run/exceptions_A_00000.txt, _B1_, _B2_                    the squarefree lanes the blocks leave uncertified (24 + 4 + 1 = 29)
run/xs.json                                               the 29 exception lanes with the Y at which checkAt 10 settles each (0 for the two W fields)
run/BoundariesOfClass/Sieve/Block/Asm/SP/Chunk_000.lean   the sieve primes of checkAt (21 primes 2..73), one chunk; spChunkB decided
run/BoundariesOfClass/Sieve/Block/Asm/SP/P.lean           P and P_ok : PrimesOK P
run/BoundariesOfClass/Sieve/Block/Asm/Main.lean           Bs (17 blocks), xs, W = [16003, 17803], asmP, asm_ok : asmP Bs SP.P xs = true (decided), asm_hB
run/MANIFEST_shared.json, MANIFEST_A_00000.json, ...      md5 of every generated file, per generator run
CLAIMS.jsonl                                              the three range claims (one per family) for cover_check.py
W10.txt                                                   the W list: 16003, 17803
```

Each block is one `Blk` literal `⟨fam, N, L, m0, Y, Base.pats, Base.oddPrimes, E⟩` and one theorem
`blockOK blk = true := by decide +kernel`. `E` is the lanes left uncertified, as a bit mask; it is DATA, and the kernel
recomputes it.

## The commands (what was run; all paths relative to this directory)

```
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
python3 ../gen/gen_shared.py run 116 242
python3 ../gen/gen_blocks.py run 10 A  13844 54500 1000 --shared run/shared_lists.json --k0 0
python3 ../gen/gen_blocks.py run 10 B1  3461 13625 1000 --shared run/shared_lists.json --k0 0
python3 ../gen/gen_blocks.py run 10 B2  3461 13625 1000 --shared run/shared_lists.json --k0 0
python3 ../gen/make_xs.py run/xs.json 10 run/exceptions_A_00000.txt run/exceptions_B1_00000.txt run/exceptions_B2_00000.txt --w W10.txt
python3 ../gen/gen_asm.py run run/xs.json run --params 13843 54500 10 W10.txt
```

The parameters: YMAX = 116 = ⌊√((54500 − 1)/4)⌋ is the largest block Y (family A at the top of the range; for
family B, ⌊√(13625 − 1)⌋ = 116 as well); PMAX = 242 = ⌊√(54500 + 4·1000)⌋ + 1 bounds the square primes of the
non-squarefree mask; family A runs over m in [F + 1, X) = [13844, 54500), families B over
[F/4 + 1, (X + 3)/4) = [3461, 13625); L = 1000 lanes per block (at full scale 10^5).

The regenerate-and-diff checks, each printing `REGENERATE-AND-DIFF PASS`:

```
python3 ../gen/gen_shared.py --verify run 116 242
python3 ../gen/gen_blocks.py run 10 A  13844 54500 1000 --shared run/shared_lists.json --k0 0 --verify
python3 ../gen/gen_blocks.py run 10 B1  3461 13625 1000 --shared run/shared_lists.json --k0 0 --verify
python3 ../gen/gen_blocks.py run 10 B2  3461 13625 1000 --shared run/shared_lists.json --k0 0 --verify
python3 ../gen/gen_asm.py --verify run run/xs.json run --params 13843 54500 10 W10.txt
```

The coverage check, printing 25 `PASS` lines and then `COVER CHECK PASS` (and 4 `FAIL` lines if family A's claim is
shortened to 54000, the negative control that was run):

```
python3 ../gen/cover_check.py CLAIMS.jsonl 13843 54500 10 --blocks run --xs run/xs.json
```

Recorded generator output (MEASURED, 2026-11-04; the whole pipeline takes under ten seconds of Python):

```
1 chunks, 29 pattern primes (<= 116), 52 odd primes (<= 242), sigma 100000
A: 11 blocks of up to 1000 lanes (the last ends below 54500), Y up to 116, 29 pattern primes, 52 square primes; 24 squarefree uncertified lanes
B1: 3 blocks of up to 1000 lanes (the last ends below 13625), Y up to 116, 29 pattern primes, 52 square primes; 4 squarefree uncertified lanes
B2: 3 blocks of up to 1000 lanes (the last ends below 13625), Y up to 116, 29 pattern primes, 52 square primes; 1 squarefree uncertified lanes
29 exception lanes (2 with Y = 0), max Y 73
17 blocks, 29 exceptions, 21 sieve primes in 1 SP chunks (parametrised asmP)
```

Cross-check against the first design's record for the same range (2026-10-23, not shipped here; COMPUTED by its C
prototype): the squarefree radicands that the full count at the field's own Y cannot certify are exactly 16003 and
17803, both with h = 12. Here `make_xs.py --test` (which marks every uncertifiable lane instead of refusing) found
exactly those two, and every other exception lane is settled by `checkAt 10` at some Y ≤ 73.

## How to build and check it (run 2026-11-04; outputs recorded below)

1. Take a copy of entry 5's `formalization/` directory, add the eight files of `../lean/` under it, and copy
   `run/BoundariesOfClass/Sieve/Block/{Base,Gen,Asm}/` and `run/Gen/` to the same places: the Gen modules must sit at
   `BoundariesOfClass/Sieve/Block/Gen/<fam>/B<k>.lean` (the generator writes them under `run/Gen/<fam>/`; move or
   symlink them to `BoundariesOfClass/Sieve/Block/Gen/<fam>/`).
2. Build, in dependency order (lake resolves it):

   ```
   lake build BoundariesOfClass.Sieve.Block.Asm.Main
   ```

   Expected: exit 0, no `sorry`, every `decide +kernel` theorem accepted. Each block should take a few seconds of
   kernel time at this size (ESTIMATE from the measured 4.8 s at 2,000 lanes and Y = 3,535); the whole example a few
   minutes after the library is built.
3. Axioms, from a scratch file importing `BoundariesOfClass.Sieve.Block.Asm.Main`:

   ```
   #print axioms BoundariesOfClass.Sieve.Block.Asm.asm_ok
   #print axioms BoundariesOfClass.Sieve.Block.Gen.blk_A_00000_ok
   #print axioms BoundariesOfClass.Sieve.Block.Base.pats_ok
   ```

   Expected: a subset of `[propext, Classical.choice, Quot.sound]` for each. `decide +kernel` adds no axiom; a
   `native_decide` proof would show an extra axiom named `<decl>._native.native_decide.ax_…` on Lean v4.34.1, and
   any axiom outside the three standard ones is a failure.
4. The second kernel: export the closure of `BoundariesOfClass.Sieve.Block.Asm.Main` with lean4export and check it
   with nanoda (`nat_extension: true`, the three standard axioms permitted, `unpermitted_axiom_hard_error: true`), as
   in FORMAT.md, section 6. Expected: exit 0. (The nanoda build pinned here prints nothing on success, so also run
   the must-reject control: change one digit of a block's `E` literal inside the export file and re-run nanoda,
   which must fail. An empty or truncated export also exits 0, so check the export's size.)
5. The negative control: flip one bit of `E` in `run/Gen/A/B00000.lean` (for example change the last digit of the
   literal) and rebuild. Expected: `decide` fails on `blk_A_00000_ok` ("evaluates to false").

Recorded outputs (2026-11-04, Apple M3 Ultra with 96 GB, macOS 26, Lean v4.34.1, in a copy of entry 5's verified fresh build
tree with its own `.lake`; one Lean process at a time):

```
lake build ........................ : exit 0, "Build completed successfully (8972 jobs)", no sorry; each of the
                                      17 block modules 32-33 s, SP.P 5.0 s, Asm.Main 4.8 s
#print axioms asm_ok .............. : [propext]
#print axioms asm_hB .............. : [propext, Classical.choice, Quot.sound]
#print axioms lt_classNumber_of_blockOK, covers_exceptionsOK_of_asmB, mu_le_classNumber
                                    : [propext, Classical.choice, Quot.sound] / [propext, Quot.sound] / the three
lean4export (asm_ok, asm_hB, covers_exceptionsOK_of_asmB, lt_classNumber_of_blockOK)
                                    : exit 0, 287 MB, 5,383,754 lines
nanoda (nat + string extensions, three axioms, hard error)
                                    : exit 0, 17.4 s, 0.66 GB peak RSS
nanoda must-reject (last digit of blk_A_00000's E changed 4 -> 6 in the export)
                                    : exit 101, "assertion failed: self.def_eq(u, v)" (src/tc.rs:955)
Lean negative control (same digit changed in Gen/A/B00000.lean, rebuilt)
                                    : exit 1, "B00000.lean:10:58: Tactic `decide` failed for proposition"; file
                                      restored (md5 f912d8ed… before and after) and the full build re-run, exit 0
```

## What this example does and does not show

- It shows the complete per-range artefact set, the naming, the regenerate-and-diff discipline and the coverage
  check of FORMAT.md, at a size where every file can be read.
- It uses the **parametrised** assembly check `asmP` (F, X, N and W as literals in the generated file). Its
  soundness lemma, the parametrised form of `covers_exceptionsOK_of_asmB`, is not yet written (lean/README.md,
  last section), so at this size the example proves `asmP Bs SP.P xs = true` and every `blockOK`, and the range
  statement itself ("h > 10 for every field in the range outside W") is one unbuilt lemma away. For h ≤ 1000 that
  lemma exists with the constants baked in.
- The range it covers starts above F(10), so no field of class number at most 10 lies in it; the example therefore
  needs no exact class numbers. A range below F(N) would leave the listed fields in its exception set, and those
  go to pillar 3 (DESIGN.md, section 7).
