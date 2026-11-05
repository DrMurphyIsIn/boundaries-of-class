import BoundariesOfClass.Sieve.Block.Lemmas

/-! # The pillar-1 assembly checks (2026-10-25; DESIGN.md, section 6)

`Covers` and `ExceptionsOK` (item 8's hypotheses) as kernel-decidable Bools, with soundness proved once. -/

namespace BoundariesOfClass.Sieve.Block

open BoundariesOfClass.Sieve

/-- The residue-`r` chain: every `m ≡ r (mod 4)` with `cur ≤ m < hi` lies in a block of the list with `m0 ≡ r`.
Each residue-`r` block must start at or before the running end `cur`. -/
def chainB (r : ℕ) : ℕ → ℕ → List Blk → Bool
  | cur, hi, [] => Nat.ble hi cur
  | cur, hi, b :: bs =>
    cond (Nat.beq (b.m0 % 4) r)
      (Nat.ble b.m0 cur && chainB r (Nat.max cur (b.m0 + 4 * b.L)) hi bs)
      (chainB r cur hi bs)

/-- The first `m ≥ lo` with `m ≡ r (mod 4)` (for `r < 4`): where a residue-`r` chain must start, since its first
block's `m0` is that number. -/
def up4 (r lo : ℕ) : ℕ := lo + (r + 4 - lo % 4) % 4

/-- Coverage of `F < dOf m < X`: residue 3 (`dOf m = m`) over `[F + 1, X)`, residues 1 and 2 (`dOf m = 4m`) over
`[F / 4 + 1, (X + 3) / 4)`, each chain started at the first number of its residue (`up4`; starting
at `F + 1` itself would demand a block with `m0 ≤ F + 1` of the wrong residue). Residue 0 is never squarefree. -/
def coversB (Bs : List Blk) (F X : ℕ) : Bool :=
  chainB 3 (up4 3 (F + 1)) X Bs && chainB 1 (up4 1 (F / 4 + 1)) ((X + 3) / 4) Bs &&
    chainB 2 (up4 2 (F / 4 + 1)) ((X + 3) / 4) Bs

/-- The lane mask of the exception entries `(m, Y)` that fall in block `b`. -/
def maskFrom (b : Blk) : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (m, _) :: xs =>
    cond (Nat.ble b.m0 m && Nat.blt m (b.m0 + 4 * b.L) && Nat.beq (m % 4) (b.m0 % 4))
      (Nat.lor (1 <<< ((m - b.m0) / 4)) (maskFrom b xs)) (maskFrom b xs)

/-- **The assembly check.** Coverage, each block's `E` equal to the mask of the listed exceptions, and each listed
exception in W18 or settled by `checkAt 1000 Y P` at its own listed `Y`. -/
def asmB (Bs : List Blk) (P : List (ℕ × ℕ)) (xs : List (ℕ × ℕ)) : Bool :=
  coversB Bs 227932027 1605000000 &&
    xs.all (fun mY => W18.elem mY.1 || checkAt 1000 mY.2 P mY.1) &&
    Bs.all (fun b => Nat.beq b.E (maskFrom b xs))

theorem chainB_sound {r : ℕ} : ∀ {Bs : List Blk} {cur hi : ℕ}, chainB r cur hi Bs = true →
    ∀ m, m % 4 = r → cur ≤ m → m < hi → ∃ b ∈ Bs, b.m0 ≤ m ∧ m < b.m0 + 4 * b.L ∧ m % 4 = b.m0 % 4
  | [], cur, hi, h, m, _, h1, h2 => by
    simp only [chainB, Nat.ble_eq] at h; omega
  | b :: bs, cur, hi, h, m, hr, h1, h2 => by
    simp only [chainB, cond_beq] at h
    split_ifs at h with hb
    · simp only [Bool.and_eq_true, Nat.ble_eq] at h
      by_cases hm : m < b.m0 + 4 * b.L
      · exact ⟨b, List.mem_cons_self, by omega, hm, by omega⟩
      · obtain ⟨b', hb', h'⟩ := chainB_sound h.2 m hr (by simp only [Nat.max_def]; split_ifs <;> omega) h2
        exact ⟨b', List.mem_cons_of_mem _ hb', h'⟩
    · obtain ⟨b', hb', h'⟩ := chainB_sound h m hr h1 h2
      exact ⟨b', List.mem_cons_of_mem _ hb', h'⟩

theorem covers_of_coversB {Bs : List Blk} {F X : ℕ} (h : coversB Bs F X = true) : Covers Bs F X := by
  simp only [coversB, Bool.and_eq_true] at h
  obtain ⟨⟨h3, h1⟩, h2⟩ := h
  intro m hsq _ _ hF hX
  have h4 : m % 4 ≠ 0 := by
    intro h0
    have := hsq 2 (by omega)
    simp [Nat.isUnit_iff] at this
  unfold CN1.Finite.dOf at hF hX
  split_ifs at hF hX with hm3
  · exact chainB_sound h3 m hm3 (by unfold up4; omega) hX
  · have : m % 4 = 1 ∨ m % 4 = 2 := by omega
    rcases this with hm | hm
    · exact chainB_sound h1 m hm (by unfold up4; omega) (by omega)
    · exact chainB_sound h2 m hm (by unfold up4; omega) (by omega)

theorem testBit_maskFrom (b : Blk) (i : ℕ) : ∀ xs : List (ℕ × ℕ), (maskFrom b xs).testBit i = true →
    ∃ mY ∈ xs, mY.1 = b.m0 + 4 * i
  | [], h => by simp [maskFrom] at h
  | (m, Y) :: xs, h => by
    simp only [maskFrom] at h
    cases hc : (Nat.ble b.m0 m && Nat.blt m (b.m0 + 4 * b.L) && Nat.beq (m % 4) (b.m0 % 4))
    · rw [hc, cond_false] at h
      obtain ⟨mY, hmY, he⟩ := testBit_maskFrom b i xs h
      exact ⟨mY, List.mem_cons_of_mem _ hmY, he⟩
    · rw [hc, cond_true, tb_lor, Bool.or_eq_true] at h
      simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, Nat.beq_eq] at hc
      rcases h with h | h
      · rw [Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_eq] at h
        exact ⟨(m, Y), List.mem_cons_self, by simp only; omega⟩
      · obtain ⟨mY, hmY, he⟩ := testBit_maskFrom b i xs h
        exact ⟨mY, List.mem_cons_of_mem _ hmY, he⟩

/-- **Soundness of the assembly check.** -/
theorem covers_exceptionsOK_of_asmB {Bs : List Blk} {P xs : List (ℕ × ℕ)} (hP : PrimesOK P)
    (h : asmB Bs P xs = true) : Covers Bs 227932027 1605000000 ∧ ExceptionsOK Bs := by
  simp only [asmB, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨hc, hx⟩, hE⟩ := h
  refine ⟨covers_of_coversB hc, fun b hb i _ hbit _ => ?_⟩
  rw [Nat.eq_of_beq_eq_true (hE b hb)] at hbit
  obtain ⟨mY, hmY, he⟩ := testBit_maskFrom b i xs hbit
  have := hx mY hmY
  simp only [Bool.or_eq_true, List.elem_eq_mem, decide_eq_true_eq] at this
  rw [← he]
  rcases this with h | h
  · exact Or.inl h
  · exact Or.inr ⟨mY.2, P, hP, h⟩

/-! ### The sieve primes of `checkAt`, checked in chunks (as the Base table) -/

/-- One chunk of the sieve-prime list `P`: each entry prime (`primeSqB`), its mask exactly `sqMask p` unless `p = 2`,
and the primes increasing. -/
def spChunkB (l : List (ℕ × ℕ)) : Bool :=
  l.all (fun pm => primeSqB pm.1 && (Nat.beq pm.1 2 || Nat.beq pm.2 (sqMask pm.1))) && incr (l.map (·.1))

theorem primesOK_of_spChunks {chunks : List (List (ℕ × ℕ))} (hc : ∀ l ∈ chunks, spChunkB l = true)
    (hi : incr (chunks.flatten.map (·.1)) = true) : PrimesOK chunks.flatten := by
  refine ⟨fun pm hpm => ?_, nodup_of_incr hi⟩
  obtain ⟨l, hl, hpml⟩ := List.mem_flatten.mp hpm
  have h := hc l hl
  simp only [spChunkB, Bool.and_eq_true, List.all_eq_true] at h
  have h1 := h.1 pm hpml
  simp only [Bool.and_eq_true, Bool.or_eq_true] at h1
  obtain ⟨hpr, hm⟩ := h1
  have hp := primeSqB_sound hpr
  refine ⟨hp, fun h2 => ?_⟩
  rcases hm with hm | hm
  · exact absurd (Nat.eq_of_beq_eq_true hm) h2
  · rw [Nat.eq_of_beq_eq_true hm]; exact maskOK_sqMask hp.pos

end BoundariesOfClass.Sieve.Block
