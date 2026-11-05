# lean/: the soundness library of the block sieve

These eight files are the Lean 4 sources a collaborator builds against. They are copies of the files that were
built on 2026-10-25 in the h ≤ 1000 development (see DESIGN.md); three of them have had internal names removed from
docstrings and comments, and nothing else. The code (every `def`, `theorem` and proof term) is byte-for-byte the code
that compiled with no `sorry`; the comment-only edits are listed below so that the maintainer can rebuild and re-pin.

**Status of the proofs.** PROVED in Lean (compiled with exit 0, no `sorry`, `#print axioms` = `[propext,
Classical.choice, Quot.sound]` for the main theorems, as recorded in the design notes) under the pins below. Comparator
with two kernels (Lean's and nanoda's) was run on individual generated blocks and on the assembly at test scale in
October. On 2026-11-04 this exact tree (shipped md5s below) was rebuilt with the N = 10 example and checked by Lean's
kernel and nanoda; see example/README.md for the recorded outputs.

## Files

| file | lines | shipped md5 | built md5 (2026-10-25) | contents |
|---|---|---|---|---|
| `BoundariesOfClass/Sieve/Mu.lean` | 324 | `45d238dd52180142ff6907c76a0f37e6` | same | the count `mu`, its exponent vectors `vecs`, `length_vecs`, `nodup_vecs`, `adm_vecs`, `norm_vecs`; the capped count `muK` and `muK_le_mu` |
| `BoundariesOfClass/Sieve/Soundness.lean` | 473 | `719d7b5637152aa38f060a3fd058325f` | same | the family `Fam` of prime ideals, the key lemma `not_isPrincipal`, `cls_injOn`, `mu_le_classNumber_of_fam` |
| `BoundariesOfClass/Sieve/Field.lean` | 143 | `0aaa93649d69bbad8f4d9f8ce4c72cd5` | same | `ne_of_not_dvd`, `exists_root_of_dvd`, `exists_pair`, **`mu_le_classNumber`** (Lemma 3 of DESIGN.md) |
| `BoundariesOfClass/Sieve/Check.lean` | 283 | `5d831a8f874eb5b703e8cf3f5c70f7b7` | same | `IsSqMod`, `MaskOK`, `PrimesOK`, `sqMask`, `incr`, `primesOKB`, `ptype`, `sieveList`, `checkAt`, **`lt_classNumber_of_checkAt`** |
| `BoundariesOfClass/Sieve/Range.lean` | 83 | `872cdc61974f61ff1e5fd83dbaf17c76` | same | `allRange`, `rangeOK`, `lt_classNumber_of_rangeOK` (the first, per-radicand design; kept because `Block/Defs.lean` imports it) |
| `BoundariesOfClass/Sieve/Block/Defs.lean` | 184 | `c5499629246e2b58dbcfd91045cb0acc` | `09e32558528ed7e2fea0befc5cffe456` | the block-sieve definitions: `rot`, `rep`, `maskOf`, `BaseOK`, `basePat`, `primeSqB`, `chunkOKB`, `PatsOK`, `NSQ`, the bit-sliced counter, `blockOK`, `laneList`, `Covers`, `ExceptionsOK`, `W18` |
| `BoundariesOfClass/Sieve/Block/Lemmas.lean` | 769 | `980166d9e3ae0c445539f15f5b4150e8` | `bf589cfa54975c4482696e0ffa42fff6` | the 13 block-sieve lemmas (items 1–8 of DESIGN.md), including **`lt_classNumber_of_blockOK`** and the h ≤ 1000 range assembly |
| `BoundariesOfClass/Sieve/Block/AsmCheck.lean` | 130 | `29495266a77634ea6082a3b566599944` | `0f54596cd78e6b3c8aa006adb11b70ef` | `chainB`, `up4`, `coversB`, `maskFrom`, `asmB`, `spChunkB` and their soundness: `covers_of_coversB`, **`covers_exceptionsOK_of_asmB`**, `primesOK_of_spChunks` |

The comment-only edits (each applied exactly once; the code was compared with every comment stripped and is
identical):
- `Defs.lean`: 15 docstring edits (the module header, and review references in the docstrings of `BaseOK`, `trialB`,
  `primeSqB`, `chunkOKB`, `PatsOK`, `count1`, `Blk`, `blockOK`, `laneList`, the item-8 section header, `W18`,
  `ExceptionsOK`).
- `Lemmas.lean`: 2 docstring edits (`lt_mu_of_not_uncertified`, `lt_classNumber_of_blockOK`).
- `AsmCheck.lean`: 2 edits (the module header and the docstring of `coversB`).

## What these files import, and the pins

The sieve library imports the vendored `CN1` and `HCN` developments of this repository (entries 1 and 3; for
example `CN1.Finite.dOf`, `CN1.Finite.quadIntOfFoundations`, `HCN.Finite.tOf_mul_lt_four_mul_cOf`,
`HCN.Finite.exists_absNorm_eq_of_root`) and Mathlib. It does **not** import `BoundariesOfClass.Numerics` (the
thresholds): the threshold enters the range assembly as a hypothesis (`hT` in `dOf_le_or_mem_W18_of_classNumber_le_thousand`),
discharged by the solution's main module.

So the files drop into the formalization of entry 5 (`two-sided-bounds/formalization/`), next to its `CN1/`, `HCN/`
and `BoundariesOfClass/` directories, and build with its `lakefile.lean` unchanged (the `BoundariesOfClass` library
globs `BoundariesOfClass.+`).

Pins (the same as entry 5's):

| what | pin |
|---|---|
| Lean | `leanprover/lean4:v4.34.1` (`lean-toolchain` here) |
| Mathlib | `d13f23b723b8a846827a245b89c10fc7d3f11612` |
| openai/math (the only `require`; brings Mathlib and the 7/8 theorem) | `adc7f1241b42e322a6451854ab7e4b4c146bf78a` |
| `CN1/`, `HCN/` | verbatim copies of `hcn/formalization/` at release v1.2.0, as in entry 5 |

Every other package in entry 5's `lake-manifest.json` is a dependency of openai/math at the revision it pins. Do not
run `lake update`. The compatibility patches that openai/math ships for its dependencies must be applied once before
the first build (`scripts/apply_oai_patches.sh` in entry 5).

## Build

From a copy of entry 5's `formalization/` with these files added:

```
lake build BoundariesOfClass.Sieve.Block.AsmCheck
```

builds the eight files and everything they import (the first build of `CN1`/`HCN`/Mathlib takes hours; the eight
files themselves take a few minutes). Then

```
-- in a scratch file importing BoundariesOfClass.Sieve.Block.AsmCheck:
#print axioms BoundariesOfClass.Sieve.Block.lt_classNumber_of_blockOK
#print axioms BoundariesOfClass.Sieve.Block.covers_exceptionsOK_of_asmB
#print axioms BoundariesOfClass.Sieve.mu_le_classNumber
```

should each report `[propext, Classical.choice, Quot.sound]`. Note that `#print axioms` reads the module cache; the
authoritative check is the second-kernel replay described in FORMAT.md, section 6.

## What is specialised to h ≤ 1000, and what a collaborator must change for h ≤ 3500 (OPEN)

- `Defs.lean`: `NP := 11` (the comparator reads N + 1 in NP bit-planes; `blockOK` requires `N + 1 < 2 ^ NP`). For
  N = 3500 it must be 12. Every lemma is stated in terms of `NP` and should re-elaborate unchanged; this has not been
  built.
- `Defs.lean`: `W18`, `Covers`'s use in `ExceptionsOK` with `checkAt 1000`, and `Lemmas.lean`'s item 8
  `dOf_le_or_mem_W18_of_classNumber_le_thousand` (F = 227932027, X = 1605000000, N = 1000) are the h ≤ 1000 instance.
- `AsmCheck.lean`: `asmB` and `covers_exceptionsOK_of_asmB` carry the same constants.

The generalisation is mechanical: parameters `(N F X : ℕ) (W : List ℕ)` in place of the constants, a hypothesis
`X ≤ 2 ^ 128` where item 8 derives `b.Y < 2 ^ 64` from `b.Y * b.Y < X`, and `checkAt N` in place of `checkAt 1000`.
`gen/gen_asm.py --params` already emits the parametrised check `asmP`; its soundness lemma is the one to write. See
DESIGN.md, section 6.
