# DESIGN: the block sieve, its certificates and their soundness

This document gives the mathematics of each certificate type in the kernel route and the Lean lemma that makes it
sound, quoting the statements verbatim from `lean/` with file and line. Labels: **PROVED** (a compiled Lean theorem,
cited), **MEASURED** (a recorded run, cited), **ESTIMATE**, **OPEN**.

Notation. K = ℚ(√−m), m squarefree, m ∉ {1, 3}. The radicand m determines d = |disc K|: d = m when m ≡ 3 (mod 4)
(family A) and d = 4m when m ≡ 1, 2 (mod 4) (families B1, B2). In Lean this is `CN1.Finite.dOf m`. The ring of
integers is ℤ[θ] with θ² = tθ − c, where (t, c) = (1, (m + 1)/4) in family A and (0, m) in family B, so that
d = 4c − t². h = h(K) is the class number, `NumberField.classNumber K` in Mathlib.

## 1. The one lemma everything rests on (PROVED)

Let L be a list of distinct primes, each tagged **split** (p ∤ d, and X² − tX + c has a root mod p) or
**ramified** (p ∣ d). Define the count

    mu L Y = #{ exponent vectors v ∈ ℤ^L : ∏ p^{|v_p|} ≤ Y, ramified entries in {0, 1} },

that is, Σ_{a ≤ Y, a built from the listed primes} 2^{(number of split primes dividing a)}, ramified primes to the
first power. It is computed by recursion on L:

```lean
-- lean/BoundariesOfClass/Sieve/Mu.lean:31-40
def powSum (g : ℕ → ℕ) (p : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | f + 1, q, Y => if Y < q then 0 else g (Y / q) + powSum g p f (q * p) Y

def mu : List (ℕ × Bool) → ℕ → ℕ
  | [], _ => 1
  | (p, b) :: L, Y =>
    mu L Y + if b then 2 * powSum (mu L) p 64 p Y else (if p ≤ Y then mu L (Y / p) else 0)
```

**Lemma 3 (the count is at most the class number).** If 4Y² < d, then mu L Y ≤ h(K).

```lean
-- lean/BoundariesOfClass/Sieve/Field.lean:112-118   (K, t, c and D : CN1.Finite.QuadInt K t c are section variables)
theorem mu_le_classNumber (htc : t * t < 4 * c) (L : List (ℕ × Bool))
    (hL : ∀ pb ∈ L, pb.1.Prime ∧
      (pb.2 = true → ¬ (pb.1 : ℤ) ∣ 4 * c - t * t ∧ ∃ r : ℤ, (pb.1 : ℤ) ∣ r ^ 2 - t * r + c) ∧
      (pb.2 = false → (pb.1 : ℤ) ∣ 4 * c - t * t))
    (hnd : (L.map (·.1)).Nodup) {Y : ℕ} (hY : 4 * (Y * Y) < 4 * c - t * t) :
    mu L Y ≤ classNumber K
```

*Proof idea* (the full paper proof is the header of `Soundness.lean`, lines 6–33). Each listed p gives a prime
ideal P_p of norm p (Kummer–Dedekind, from the root) and J_p with P_p·J_p = (p); for a split p they differ. An
exponent vector v gives an ideal I_v = ∏ Q_p^{|v_p|} of norm n(v) = ∏ p^{|v_p|} ≤ Y and class ∏ [P_p]^{v_p}. If
two counted vectors v ≠ v′ had the same class, the vector w = v − v′ would give a principal ideal (β), β = x + yθ,
of norm n(w) ≤ Y² < d/4; but 4·n(w) = (2x + ty)² + dy² forces y = 0, n(w) = x² ≥ 2, and a prime q ∣ x then
contradicts either "ramified entries are ±1" (q² ∣ x² but q ‖ n(w)) or "P_q ≠ J_q" (the prime J_q would contain
a factor of (x) ⊆ (q) ⊆ J_q of a different norm or equal to P_q). So the counted classes are distinct, and there
are exactly mu L Y of them (`length_vecs`, `nodup_vecs`). The proof uses no reduction theory and no table.
Key Lean steps: `not_isPrincipal` (`Soundness.lean:221`), `cls_injOn` (`:412`), `mu_le_classNumber_of_fam` (`:444`).

This is the ideal-theoretic form of Watkins's count of reduced forms with 4a² < d (Math. Comp. 73 (2004), §8),
restricted to the a built from the listed primes; the same count that Kimura's and Jaswal's sieves use.

**Why a certificate implies h > N for a field.** A certificate names a list L of primes with their types at d, and a Y
with 4Y² < d, such that N < mu L Y. Lemma 3 then gives N < h. The kernel decides the types (quadratic residues by
bit masks), the inequality 4Y² < d, and the count. Dropping primes from L, or lowering Y, only lowers mu, so a
certificate may use any sub-list and is still sound; this is what lets a block use split primes only.

## 2. The per-field certificate `checkAt` (PROVED)

For one radicand m, the primes come from a shared list P of pairs (p, mask), where mask has bit s set iff s is a
square mod p. `ptype p mask d` reads the type of p at d (2 ramified, 1 split, 0 inert; for p = 2, split iff d ≡ 7 mod 8),
`sieveList P d` keeps the split and ramified ones, and `checkAt` evaluates the capped count `muK (N + 1)`, which stops
as soon as N + 1 is reached (`muK_le_mu`, `Mu.lean:300`, is its one-line soundness):

```lean
-- lean/BoundariesOfClass/Sieve/Check.lean:139-141
def checkAt (N Y : ℕ) (P : List (ℕ × ℕ)) (m : ℕ) : Bool :=
  let d := CN1.Finite.dOf m
  Nat.blt (4 * (Y * Y)) d && Nat.blt N (muK (Nat.succ N) (sieveList P d) Y)

-- lean/BoundariesOfClass/Sieve/Check.lean:269-271
theorem lt_classNumber_of_checkAt {K : Type*} [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
    {m : ℕ} (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K)) {N Y : ℕ} {P : List (ℕ × ℕ)}
    (hP : PrimesOK P) (h : checkAt N Y P m = true) : N < classNumber K
```

`PrimesOK P` (`Check.lean:40`) says every p is prime, every odd p's mask is correct in the soundness direction, and
the primes are distinct; `primesOKB` decides it linearly (`primesOK_of_B`). This is the certificate used for the
exception lanes of the block sieve (section 5) and was the whole of the first, per-radicand design (`Range.lean`:
`rangeOK`, `lt_classNumber_of_rangeOK`, lines 65–83; built end to end at N = 10 on one interval, MEASURED at 1.3 ms
of kernel time per radicand at Y ≤ 113).

## 3. The block certificate (PROVED; the heart of the design)

A **block** is 10^5 consecutive radicands of one family, m = m0 + 4i for i < L, packed as a bit lane each. The
kernel evaluates Nat arithmetic on huge numbers natively (GMP), so one operation on an L-bit number acts on all
lanes at once. A block does, for all lanes together, exactly the count of Lemma 3 with L = the lane's split primes,
at the block's common Y = ⌊√((m0 − 1)/4)⌋ (family A) or ⌊√(m0 − 1)⌋ (family B), which satisfies 4Y² < d for every
lane; then compares with N + 1.

```lean
-- lean/BoundariesOfClass/Sieve/Block/Defs.lean:119-127
structure Blk where
  fam : ℕ          -- 0 = family A (d = m), 1 = family B (d = 4m)
  N : ℕ            -- the bound certified: N < h
  L : ℕ            -- lanes
  m0 : ℕ           -- first radicand; lane i is m0 + 4 i
  Y : ℕ            -- the common Y
  pats : List (ℕ × ℕ)      -- the shared pattern table (q, B_q), odd primes q ≤ Y
  oddPrimes : List ℕ       -- the shared list from which square primes are selected
  E : ℕ            -- DATA: the lanes left uncertified, as a bit mask
```

The pieces, each with its lemma:

- **Prime masks (items 1, 2, 4).** For an odd prime q, "q splits in ℚ(√−m)" depends only on m mod q, since
  (−4m/q) = (−m/q). The table stores, per q, a q-bit **base pattern** B_q with bit j set only if q splits when
  m ≡ 4j (mod q) (`BaseOK`, `Defs.lean:27`, soundness direction only). The lane mask of q is that pattern rotated
  by m0·(4⁻¹ mod q) and replicated across L lanes: one big multiplication by a repunit (`maskOf`, `Defs.lean:23`).
  ```lean
  -- lean/BoundariesOfClass/Sieve/Block/Lemmas.lean:9-10, 66-67, 102-104
  theorem testBit_rot {q B t j : ℕ} (hB : B < 2 ^ q) (ht : t < q) (hj : j < q) :
      (rot q B t).testBit j = B.testBit ((j + t) % q)
  theorem testBit_rep {L q P i : ℕ} (hq : 0 < q) (hP : P < 2 ^ q) (hi : i < L) :
      (rep L q P).testBit i = P.testBit (i % q)
  theorem testBit_maskOf {L m0 q B i : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hB : BaseOK q B) (hi : i < L) :
      (maskOf L m0 q B).testBit i = true →
        (¬ q ∣ m0 + 4 * i ∧ ∃ s : ℕ, q ∣ s ^ 2 + (m0 + 4 * i))
  ```
  The prime 2 is constant per family: in family A it splits iff m ≡ 7 (mod 8) (`mask2`, `mask2_spec`,
  `two_split_iff_A`, `Lemmas.lean:264`); in family B it is ramified and enters as the head `(2, false)` of the
  lane list, which by `mu`'s ramified clause means the block computes two counts, at Y and at Y/2, and adds them
  (`finalSt`, `Defs.lean:137`). The conversion from "root of s² + m" to Lemma 3's "root of r² − tr + c" is
  `split_iff_root_A` (`Lemmas.lean:225`).
- **The shared table (items 3, 4a).** The patterns are checked once, linearly, against a kernel-computed reference
  `basePat q` (`Defs.lean:38`), in chunks with Σq ≤ 10^5 per chunk; primality by √p-bounded trial division
  (`primeSqB`, `Defs.lean:47`).
  ```lean
  -- lean/BoundariesOfClass/Sieve/Block/Lemmas.lean:165, 187, 194-195, 212-213
  theorem baseOK_basePat {q : ℕ} (hq : 0 < q) : BaseOK q (basePat q)
  theorem primeSqB_sound {p : ℕ} (h : primeSqB p = true) : p.Prime
  theorem entries_of_chunkOKB {l : List (ℕ × ℕ)} (h : chunkOKB l = true) :
      ∀ qB ∈ l, qB.1.Prime ∧ qB.1 ≠ 2 ∧ BaseOK qB.1 qB.2
  theorem patsOK_of_chunks {chunks : List (List (ℕ × ℕ))} (hc : ∀ l ∈ chunks, chunkOKB l = true)
      (hi : incr (chunks.flatten.map (·.1)) = true) : PatsOK chunks.flatten
  ```
- **The non-squarefree mask (item 2b).** Lanes with p² ∣ m for an odd p are excluded from the obligation in the
  kernel (`NSQ`, `Defs.lean:63`), never supplied as data:
  ```lean
  -- lean/BoundariesOfClass/Sieve/Block/Lemmas.lean:295-296
  theorem not_squarefree_of_NSQ {L m0 i : ℕ} {sqps : List ℕ} (h3 : ∀ p ∈ sqps, 3 ≤ p ∧ p % 2 = 1) (hi : i < L)
      (h : (NSQ L m0 sqps).testBit i = true) : ¬ Squarefree (m0 + 4 * i)
  ```
- **The bit-sliced counter (items 5, 6).** A depth-first walk over the n ≤ Y built from the pattern primes
  (`dfsY`/`powsY`, `Defs.lean:77-95`) carries a lane vector (the AND of the masks of the primes dividing n) and adds
  2^{ω(n)} into NP = 11 bit-planes with a sticky overflow plane (`addSt`); a comparator reads N + 1 (`geqFrom`). The
  invariant per lane is "sticky, and the lane counted at least 2^NP, or the planes hold the exact count"
  (`R`, `Lemmas.lean:377`); `blockOK` requires N + 1 < 2^NP so that sticky implies > N.
  ```lean
  -- lean/BoundariesOfClass/Sieve/Block/Lemmas.lean:590-593
  theorem lt_mu_of_not_uncertified {b : Blk} (hP : PatsOK b.pats) (hb : blockOK b = true) (hY : b.Y < 2 ^ 64)
      {i : ℕ} (hi : i < b.L) (hsq : Squarefree (b.m0 + 4 * i)) (hE : (uncertified b).testBit i = false) :
      b.N < mu (laneList b i) b.Y
  ```
  The hypothesis `b.Y < 2 ^ 64` is needed because `mu` caps split exponents at 64 (`powSum … 64`) while the walk does
  not; without it the statement is false from Y = 2^65 (found during the build; harmless for every real Y).
- **The block theorem (item 7).** One kernel check per block, `blockOK b = true` (`Defs.lean:152-160`: the lane
  mask equals E, N + 1 < 2^NP, the square primes are odd and ≥ 3, 4Y² < m0 (family A) or Y² < m0 (family B) with
  the right residue, 2 ≤ Y), gives Lemma 3's conclusion for every clear bit of E:
  ```lean
  -- lean/BoundariesOfClass/Sieve/Block/Lemmas.lean:670-674
  theorem lt_classNumber_of_blockOK {K : Type*} [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
      {m : ℕ} (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K)) {b : Blk} (hP : PatsOK b.pats)
      (hb : blockOK b = true) (hY : b.Y < 2 ^ 64) (hlo : b.m0 ≤ m) (hhi : m < b.m0 + 4 * b.L)
      (hmod : m % 4 = b.m0 % 4) (hE : b.E.testBit ((m - b.m0) / 4) = false) :
      b.N < NumberField.classNumber K
  ```
  Its proof: items 1, 2, 4 show that the lane's mask bits are split primes (`entry_split`); items 5, 6 give
  N < mu (laneList b i) Y; `mu_le_classNumber` with 4Y² < m0 ≤ m = 4c − t² gives mu ≤ h.

**Why E is data and not trust.** E is whatever the generator's Python mirror computed; the kernel recomputes the
lane mask from scratch and demands equality. A wrong E, in either direction, fails the build (MEASURED: one flipped
bit is rejected by Lean's kernel at build, and by nanoda on the exported term). A bit of E set for a lane that the
count would have certified is merely wasteful (that lane then needs a per-field certificate); a bit cleared for a
lane the count does not certify is caught.

**Cost per block (MEASURED, 2026-10-25, Lean v4.34.1, L = 10^5 lanes):** 14.0 s and 9.4 GB at Y ≈ 7,555; 30.1 s and
15.8 GB at Y ≈ 20,027 (the two ends of the h ≤ 1000 range). The time is affine in Y and nearly independent of L up
to 10^5 (4.8 s at 2,000 lanes against 5.0 s at 100,000 at Y = 3,535); the cost is the kernel's per-operation overhead,
about 85 µs per big-number operation, not the GMP arithmetic. Memory grows with both L and Y and is the binding
constraint; its growth beyond Y = 20,000 is unmeasured.

## 4. The range assembly (PROVED for h ≤ 1000; parametrisation OPEN)

A family's blocks must tile its range, and every uncertified squarefree lane must be settled elsewhere. Two
predicates say this, and item 8 turns them into the range statement:

```lean
-- lean/BoundariesOfClass/Sieve/Block/Defs.lean:174-182
def Covers (Bs : List Blk) (F X : ℕ) : Prop :=
  ∀ m : ℕ, Squarefree m → m ≠ 1 → m ≠ 3 → F < CN1.Finite.dOf m → CN1.Finite.dOf m < X →
    ∃ b ∈ Bs, b.m0 ≤ m ∧ m < b.m0 + 4 * b.L ∧ m % 4 = b.m0 % 4
def ExceptionsOK (Bs : List Blk) : Prop :=
  ∀ b ∈ Bs, ∀ i < b.L, b.E.testBit i = true → Squarefree (b.m0 + 4 * i) →
    (b.m0 + 4 * i) ∈ W18 ∨ ∃ Y P, PrimesOK P ∧ checkAt 1000 Y P (b.m0 + 4 * i) = true

-- lean/BoundariesOfClass/Sieve/Block/Lemmas.lean:733-739
theorem dOf_le_or_mem_W18_of_classNumber_le_thousand {K : Type*} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) {m : ℕ} (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hm1 : m ≠ 1) (hm3 : m ≠ 3) {Bs : List Blk} (hB : ∀ b ∈ Bs, PatsOK b.pats ∧ blockOK b = true ∧ b.N = 1000)
    (hC : Covers Bs 227932027 1605000000) (hX : ExceptionsOK Bs)
    (hT : 1605000000 ≤ CN1.Finite.dOf m → 1000 < NumberField.classNumber K)
    (hcl : NumberField.classNumber K ≤ 1000) :
    CN1.Finite.dOf m ≤ 227932027 ∨ m ∈ W18
```

Read it as: a field of class number at most N has |D| ≤ F, or is one of the W fields. The threshold enters as the
hypothesis `hT`, which entry 5's `lt_classNumber_of_le_dOf_le_thousand` discharges; the sieve library never imports
the thresholds. For h ≤ 3500 the constants become N = 3500, F = 3,495,584,467, X = the new threshold (section 8 of
README.md), and W = the fields above F with h in (3500, …] that Lemma 3 cannot certify at any Y (their number is
unknown until the scan runs: at N = 1000 there were 18, with h from 1002 to 1052).

The two predicates are decided by one more generated kernel check, `asmB`, with its soundness (PROVED for the
h ≤ 1000 constants):

```lean
-- lean/BoundariesOfClass/Sieve/Block/AsmCheck.lean:40-43, 94-95
def asmB (Bs : List Blk) (P : List (ℕ × ℕ)) (xs : List (ℕ × ℕ)) : Bool :=
  coversB Bs 227932027 1605000000 &&
    xs.all (fun mY => W18.elem mY.1 || checkAt 1000 mY.2 P mY.1) &&
    Bs.all (fun b => Nat.beq b.E (maskFrom b xs))
theorem covers_exceptionsOK_of_asmB {Bs : List Blk} {P xs : List (ℕ × ℕ)} (hP : PrimesOK P)
    (h : asmB Bs P xs = true) : Covers Bs 227932027 1605000000 ∧ ExceptionsOK Bs
```

`coversB` walks the three residue chains (3 over [F + 1, X); 1 and 2 over [F/4 + 1, (X + 3)/4)), each started at the
first number of its residue (`up4`); `chainB_sound` and `covers_of_coversB` (`AsmCheck.lean:45, 60`) are its
soundness. The E-equality is two-sided, so the exception list `xs` names exactly the uncertified lanes.

## 5. What a range certificate proves, in one sentence

For a range [A, B) of radicands of one family covered by blocks with `blockOK` and an exception list settled by
`checkAt` or named in W: **every squarefree m in [A, B) has h(ℚ(√−m)) > N, except the W fields.** By
`lt_classNumber_of_blockOK` for the lanes with a clear E bit, by `lt_classNumber_of_checkAt` for the lanes with a
set bit and a Y in xs, and by nothing for W (they are excluded from the statement, and need pillar 3).

## 6. What is specialised, and the generalisation (OPEN, mechanical)

`ExceptionsOK`, `asmB`, `covers_exceptionsOK_of_asmB` and item 8 carry N = 1000, F = 227932027, X = 1605000000 and
the list `W18` as literals. For h ≤ 3500 they must take `(N F X : ℕ) (W : List ℕ)` as parameters, with
`checkAt N`, and item 8 needs `X ≤ 2 ^ 128` to derive `b.Y < 2 ^ 64` from `b.Y * b.Y < X`. `gen/gen_asm.py --params`
already emits the parametrised check (`asmP`); the proofs are expected to go through unchanged in shape, but this has
not been built. Also `NP := 11` (`Defs.lean:97`) must become 12 for N = 3500 (`blockOK` demands N + 1 < 2^NP;
3501 < 4096). Both are hours of work for someone with the build, not days.

## 7. Pillar 3: the exact class numbers of the listed fields (OPEN)

The classification statement "h ≤ 3500 ⇔ (D, h) in the list" needs, for each of the 50,299,869 listed fields, a
kernel-checked h(D) = the listed value, and for every other field below F a certificate h > 3500. Lemma 3 gives
lower bounds only. What exists and what does not:

- **PROVED, small h.** Entries 1 and 3 of this repository (class number one, by two routes, and at most two) are
  kernel-checked; the class-number-two proof uses per-field "presentation certificates" (`HCN.Finite.Certs`,
  `ClassCert`: a short list of prime ideals with relations, giving h ≤ the product of certified orders) and
  per-field lower certificates. A class-number-three development on the same pattern was built (h ≤ 3 ⇔ 43
  fields, 3,760 weight-3 lower certificates, 16 presentation certificates; compiled with no `sorry`, `#print axioms`
  the standard three) and h ≤ 4 and h ≤ 5 were generated; none of these is released. The presentation route was
  tried at h ≤ 100 and failed on 38% of a sample (MEASURED), so it does not scale.
- **The design that scales (OPEN; not a line of Lean exists).** Prove in Lean that h = #{reduced forms (a, b, c)
  of discriminant −d} (|b| ≤ a ≤ c, b ≥ 0 when |b| = a or a = c), via Mathlib's fundamental domain for SL(2, ℤ)
  (`NumberTheory/Modular.lean`: `exists_smul_mem_fd` for existence; `eq_one_or_neg_one_of_mem_fdo_mem_fd` and
  companions for uniqueness) and the Hermite normal form of ideals already in `HCN.Statements.ClassPartition`
  (`IsHermite`, `formA/B/C`, `disc_form`). Then a per-field certificate is a count: the bulk a ≤ √(d/4) by the
  multiplicative count already used by the blocks (ramified primes restored), the top range a ∈ (√(d/4), √(d/3)]
  by explicit roots b of b² ≡ −d (mod 4a), checked against |b| ≥ √(4a² − d). The reduced-form definition reproduced
  PARI's h on 120 sampled fields (MEASURED); the top range has 0.077√d values of a. Estimated size: 800–2,000 lines
  of Lean (ideal ↔ τ bookkeeping is the risk), plus a generator. Estimated kernel cost: 10–60 ms per field at
  d ≈ 10^7–5·10^7 (ESTIMATE from the per-a work, never run in Lean); at d ≈ 10^9, 0.1–1 s per field.
- **What it buys.** The same count settles the fields below F with h > 3500 that neither the block count nor
  `checkAt` certifies (at N = 1000, below F(1000): 2.18·10^6 of 6.9·10^7 fields failed the block count; `checkAt` at
  the field's own Y with ramified primes settled 87–93 % of those in two sampled slices; the rest, a few ×10^5,
  need the exact count). And it settles the W fields.

Until this exists, the kernel route proves range statements ("no field of class number ≤ N above F outside W") and
not the classification.

## 8. Where the first design sits

The first design (`Range.lean`, `gen/` of the first sieve) was per-radicand: a type tree over the first 16 primes,
staircase budgets, and an exact count for the hard discriminants. It was built end to end at N = 10 on one interval
and measured at 1.3 ms per radicand there; its model gave 376 CPU-h for h ≤ 1000 and, by slices, about 3,800 CPU-h
for h ≤ 2000 and 85,000 for h ≤ 5000. The block design replaced it because the kernel's cost is per operation, not
per bit: a block does for 10^5 radicands what the first design did for one. `checkAt` and `lt_classNumber_of_checkAt`
survive as the per-field certificate; the tree and budgets do not.
