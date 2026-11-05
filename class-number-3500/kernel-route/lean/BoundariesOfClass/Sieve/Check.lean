import Mathlib
import BoundariesOfClass.Sieve.Field
import CN1.Finite.Bridge

/-!
# The kernel check of the residue sieve, and its soundness

For a radicand `m` (`K = ℚ(√-m)`, `d = dOf m`), the splitting type of a small prime `p` is read off `d`:
* `p = 2`: ramified if `d` is even, split if `d ≡ 7 (mod 8)`, inert if `d ≡ 3 (mod 8)`;
* `p` odd: ramified if `p ∣ d`, split if `-d` is a nonzero square mod `p`, inert otherwise.

The square test uses a bit mask per prime: bit `s` of `mask` is set only if `s` is a square mod `p`
(`MaskOK`, checked once for every prime of the list by `decide`). `sieveList P d` collects the split and
ramified primes of the list `P`, and the per-radicand check `checkAt N Y P m` asks for `4Y² < d` and
`N < muK (N + 1) (sieveList P d) Y`. Its soundness, `lt_classNumber_of_checkAt`, is `muK_le_mu` followed by
`mu_le_classNumber` (`BoundariesOfClass.Sieve.Field`) for the list `sieveList P d`.

The split test gives a root of `X² - t·X + c` mod `p`: if `y² ≡ -d` and `p = 2k + 1`, then
`r = (t + y)(k + 1)` has `2r - t = (t + y)·p + y`, so `4(r² - tr + c) = (2r - t)² + d ≡ y² + d ≡ 0`. For
`p = 2` and `d ≡ 7 (mod 8)`, `t` is odd, so `4c = d + t² ≡ 0 (mod 8)` and `r = 0` is a root.

The decidable definitions use `Nat.mod`, `Nat.shiftRight` and `Nat.beq` directly, so that the kernel
evaluates them with its arbitrary-precision arithmetic and without unfolding type class instances.
-/

namespace BoundariesOfClass.Sieve

open NumberField

/-- `s` is a square mod `p`, witnessed by `y < p`. -/
def IsSqMod (p s : ℕ) : Prop := ∃ y, y < p ∧ y * y % p = s % p

/-- Every set bit `s ≤ p` of `mask` is a square mod `p`. -/
def MaskOK (p mask : ℕ) : Prop := ∀ s, s ≤ p → mask >>> s % 2 = 1 → IsSqMod p s

instance (p s : ℕ) : Decidable (IsSqMod p s) := inferInstanceAs (Decidable (∃ y, y < p ∧ _))
instance (p mask : ℕ) : Decidable (MaskOK p mask) := inferInstanceAs (Decidable (∀ s, s ≤ p → _))

/-- The sieve primes, with masks: each `p` prime, odd `p` with a correct mask, and the primes distinct. -/
def PrimesOK (P : List (ℕ × ℕ)) : Prop :=
  (∀ pm ∈ P, pm.1.Prime ∧ (pm.1 ≠ 2 → MaskOK pm.1 pm.2)) ∧ (P.map (·.1)).Nodup

instance (P : List (ℕ × ℕ)) : Decidable (PrimesOK P) := inferInstanceAs (Decidable (_ ∧ _))

/-! ### A linear checker for `PrimesOK`

Deciding `PrimesOK` directly costs `O(p²)` per prime. `primesOKB` instead asks that each mask be exactly the mask of
squares, `sqMask p` (bit `y² mod p` for every `y < p`), that each `p` pass trial division (`HCN.Finite.primeB`), and
that the primes increase. -/

/-- The bits `y² mod p` for `y < n`, or-ed into `acc`. -/
def sqMaskAux (p : ℕ) : ℕ → ℕ → ℕ
  | 0, acc => acc
  | n + 1, acc => sqMaskAux p n (Nat.lor acc (Nat.shiftLeft 1 (Nat.mod (Nat.mul n n) p)))

/-- The mask of the squares mod `p`. -/
def sqMask (p : ℕ) : ℕ := sqMaskAux p p 0

theorem testBit_sqMaskAux {p : ℕ} : ∀ (n acc s : ℕ), (sqMaskAux p n acc).testBit s = true →
    acc.testBit s = true ∨ ∃ y < n, y * y % p = s
  | 0, acc, s, h => Or.inl h
  | n + 1, acc, s, h => by
    rcases testBit_sqMaskAux n _ s h with h | ⟨y, hy, hys⟩
    · have h' : (acc ||| 1 <<< (n * n % p)).testBit s = true := h
      rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq] at h'
      rcases h' with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨n, by omega, h'⟩
    · exact Or.inr ⟨y, by omega, hys⟩

theorem maskOK_sqMask {p : ℕ} (hp : 0 < p) : MaskOK p (sqMask p) := by
  intro s _ h
  have hb : (sqMask p).testBit s = true := by
    rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq, ← Nat.shiftRight_eq_div_pow]
    exact h
  rcases testBit_sqMaskAux p 0 s hb with h0 | ⟨y, hy, hys⟩
  · simp at h0
  · refine ⟨y, hy, ?_⟩
    rw [hys, Nat.mod_eq_of_lt (hys ▸ Nat.mod_lt _ hp)]

/-- Strictly increasing. -/
def incr : List ℕ → Bool
  | a :: b :: l => Nat.blt a b && incr (b :: l)
  | _ => true

theorem incr_cons {a : ℕ} : ∀ {l : List ℕ}, incr (a :: l) = true → (∀ b ∈ l, a < b) ∧ incr l = true
  | [], _ => ⟨by simp, rfl⟩
  | b :: l, h => by
    simp only [incr, Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨hab, hl⟩ := h
    obtain ⟨hb, -⟩ := incr_cons hl
    exact ⟨fun c hc => by
      rcases List.mem_cons.mp hc with rfl | hc
      · exact hab
      · exact hab.trans (hb c hc), hl⟩

theorem nodup_of_incr : ∀ {l : List ℕ}, incr l = true → l.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    obtain ⟨ha, hl⟩ := incr_cons h
    exact List.nodup_cons.mpr ⟨fun hm => (Nat.lt_irrefl a (ha a hm)), nodup_of_incr hl⟩

/-- **The linear checker.** -/
def primesOKB (P : List (ℕ × ℕ)) : Bool :=
  P.all (fun pm => HCN.Finite.primeB pm.1 && (Nat.beq pm.1 2 || Nat.beq pm.2 (sqMask pm.1))) &&
    incr (P.map (·.1))

theorem primesOK_of_B {P : List (ℕ × ℕ)} (h : primesOKB P = true) : PrimesOK P := by
  simp only [primesOKB, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hall, hinc⟩ := h
  refine ⟨fun pm hpm => ?_, nodup_of_incr hinc⟩
  have h1 := hall pm hpm
  simp only [Bool.and_eq_true, Bool.or_eq_true] at h1
  obtain ⟨hpr, hm⟩ := h1
  have hp := HCN.Finite.primeB_sound hpr
  refine ⟨hp, fun h2 => ?_⟩
  rcases hm with hm | hm
  · exact absurd (Nat.eq_of_beq_eq_true hm) h2
  · rw [Nat.eq_of_beq_eq_true hm]
    exact maskOK_sqMask hp.pos

/-- The type of `p` at `d`: `2` ramified, `1` split, `0` inert. -/
def ptype (p mask d : ℕ) : ℕ :=
  cond (Nat.beq (Nat.mod d p) 0) 2
    (cond (Nat.beq p 2) (cond (Nat.beq (Nat.mod d 8) 7) 1 0)
      (Nat.mod (Nat.shiftRight mask (Nat.sub p (Nat.mod d p))) 2))

/-- The split and ramified primes of `P` at `d`. -/
def sieveList : List (ℕ × ℕ) → ℕ → List (ℕ × Bool)
  | [], _ => []
  | (p, mask) :: P, d =>
    match ptype p mask d with
    | 2 => (p, false) :: sieveList P d
    | 1 => (p, true) :: sieveList P d
    | _ => sieveList P d

/-- **The per-radicand check**: `4Y² < d` and `N < muK (N + 1) (sieveList P d) Y`, with `d = dOf m`. The capped
count `muK` is a lower bound for `mu` (`BoundariesOfClass.Sieve.muK_le_mu`). -/
def checkAt (N Y : ℕ) (P : List (ℕ × ℕ)) (m : ℕ) : Bool :=
  let d := CN1.Finite.dOf m
  Nat.blt (4 * (Y * Y)) d && Nat.blt N (muK (Nat.succ N) (sieveList P d) Y)

/-! ### Soundness of the types -/

theorem cond_beq {α : Type*} (a b : ℕ) (x y : α) : cond (Nat.beq a b) x y = if a = b then x else y := by
  cases h : Nat.beq a b
  · simp [Nat.ne_of_beq_eq_false h]
  · simp [Nat.eq_of_beq_eq_true h]

theorem ptype_spec (p mask d : ℕ) : ptype p mask d =
    if d % p = 0 then 2 else if p = 2 then (if d % 8 = 7 then 1 else 0) else mask >>> (p - d % p) % 2 := by
  simp only [ptype, cond_beq]
  rfl

theorem mem_sieveList {d : ℕ} : ∀ {P : List (ℕ × ℕ)} {pb : ℕ × Bool}, pb ∈ sieveList P d →
    ∃ mask, (pb.1, mask) ∈ P ∧ ptype pb.1 mask d = if pb.2 then 1 else 2
  | [], _, h => by simp [sieveList] at h
  | (p, mask) :: P, pb, h => by
    unfold sieveList at h
    split at h
    · rcases List.mem_cons.mp h with rfl | h
      · exact ⟨mask, List.mem_cons_self, by simpa⟩
      · obtain ⟨mask', hm, he⟩ := mem_sieveList h
        exact ⟨mask', List.mem_cons_of_mem _ hm, he⟩
    · rcases List.mem_cons.mp h with rfl | h
      · exact ⟨mask, List.mem_cons_self, by simpa⟩
      · obtain ⟨mask', hm, he⟩ := mem_sieveList h
        exact ⟨mask', List.mem_cons_of_mem _ hm, he⟩
    · obtain ⟨mask', hm, he⟩ := mem_sieveList h
      exact ⟨mask', List.mem_cons_of_mem _ hm, he⟩

theorem sublist_sieveList {d : ℕ} : ∀ P : List (ℕ × ℕ), ((sieveList P d).map (·.1)).Sublist (P.map (·.1))
  | [] => by simp [sieveList]
  | (p, mask) :: P => by
    unfold sieveList
    split
    · simpa using (sublist_sieveList P).cons_cons p
    · simpa using (sublist_sieveList P).cons_cons p
    · simpa using (sublist_sieveList P).cons p

/-- A square root of `-d` mod an odd prime gives a root of `X² - t·X + c`. -/
theorem exists_root_of_sq {t c p y : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hy : (p : ℤ) ∣ (y : ℤ) ^ 2 + (4 * c - t * t)) : ∃ r : ℤ, (p : ℤ) ∣ r ^ 2 - t * r + c := by
  obtain ⟨k, hk⟩ := hp.eq_two_or_odd'.resolve_left hp2
  refine ⟨((t : ℤ) + y) * (k + 1), ?_⟩
  have h4 : (4 : ℤ) * ((((t : ℤ) + y) * (k + 1)) ^ 2 - t * (((t : ℤ) + y) * (k + 1)) + c) =
      ((y : ℤ) ^ 2 + (4 * c - t * t)) + (p : ℤ) * ((t + y) ^ 2 * p + 2 * y * (t + y)) := by
    rw [show (p : ℤ) = 2 * k + 1 by exact_mod_cast hk]; ring
  have hdvd : (p : ℤ) ∣ 4 * ((((t : ℤ) + y) * (k + 1)) ^ 2 - t * (((t : ℤ) + y) * (k + 1)) + c) := by
    rw [h4]; exact dvd_add hy (dvd_mul_right _ _)
  have hcop : IsCoprime (p : ℤ) 4 := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have : Nat.Coprime p 4 := by
      rw [show (4 : ℕ) = 2 ^ 2 by rfl]
      exact Nat.Coprime.pow_right 2 ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
    exact_mod_cast this
  exact hcop.dvd_of_dvd_mul_left hdvd

/-- **The listed primes satisfy the hypotheses of `mu_le_classNumber`.** -/
theorem sieveList_spec {t c : ℕ} (htc : t * t < 4 * c) {P : List (ℕ × ℕ)} (hP : PrimesOK P) :
    ∀ pb ∈ sieveList P (4 * c - t * t), pb.1.Prime ∧
      (pb.2 = true → ¬ (pb.1 : ℤ) ∣ 4 * c - t * t ∧ ∃ r : ℤ, (pb.1 : ℤ) ∣ r ^ 2 - t * r + c) ∧
      (pb.2 = false → (pb.1 : ℤ) ∣ 4 * c - t * t) := by
  intro pb hpb
  obtain ⟨mask, hm, hty⟩ := mem_sieveList hpb
  obtain ⟨hpr, hmask⟩ := hP.1 _ hm
  set p := pb.1
  set d := 4 * c - t * t with hd
  have hdz : ((d : ℕ) : ℤ) = 4 * c - t * t := by rw [hd]; push_cast [Nat.cast_sub htc.le]; ring
  refine ⟨hpr, fun hb => ?_, fun hb => ?_⟩
  · rw [hb, if_pos rfl, ptype_spec] at hty
    have h0 : ¬ d % p = 0 := by intro h; rw [if_pos h] at hty; omega
    rw [if_neg h0] at hty
    refine ⟨fun hdvd => h0 (Nat.mod_eq_zero_of_dvd (by rw [← hdz] at hdvd; exact_mod_cast hdvd)), ?_⟩
    by_cases h2 : p = 2
    · rw [if_pos h2] at hty
      have h7 : d % 8 = 7 := by by_contra h; rw [if_neg h] at hty; omega
      -- `t` odd, `c` even, root `0`
      refine ⟨0, ?_⟩
      rw [h2]
      have hc : c % 2 = 0 := by
        have : (4 * c - t * t) % 8 = 7 := h7
        rcases Nat.even_or_odd t with ⟨u, hu⟩ | ⟨u, hu⟩
        · subst hu
          have e : (u + u) * (u + u) = 4 * (u * u) := by ring
          rw [e] at this
          generalize u * u = s at this
          omega
        · subst hu
          have e : (2 * u + 1) * (2 * u + 1) = 4 * (u * (u + 1)) + 1 := by ring
          obtain ⟨w, hw⟩ := Nat.even_mul_succ_self u
          rw [e, hw] at this
          omega
      have : (2 : ℤ) ∣ (c : ℤ) := by exact_mod_cast Nat.dvd_of_mod_eq_zero hc
      simpa using this
    · rw [if_neg h2] at hty
      have hle : p - d % p ≤ p := Nat.sub_le _ _
      obtain ⟨y, -, hy⟩ := hmask h2 _ hle hty
      apply exists_root_of_sq hpr h2 (y := y)
      -- `y² ≡ p - d % p ≡ -d (mod p)`
      have hp0 : 0 < p := hpr.pos
      have hdm : d % p < p := Nat.mod_lt _ hp0
      have key : (y * y + d) % p = 0 := by
        rw [Nat.add_mod, hy]
        rcases Nat.eq_zero_or_pos (d % p) with h | h
        · exact absurd h h0
        · rw [Nat.mod_eq_of_lt (by omega : p - d % p < p)]
          rw [show p - d % p + d % p = p by omega, Nat.mod_self]
      have : (p : ℤ) ∣ ((y * y + d : ℕ) : ℤ) := by exact_mod_cast Nat.dvd_of_mod_eq_zero key
      push_cast at this
      rw [hdz] at this
      simpa [sq] using this
  · rw [hb, if_neg (by simp), ptype_spec] at hty
    have h0 : d % p = 0 := by
      by_contra h
      rw [if_neg h] at hty
      split_ifs at hty
      all_goals first | omega | (have := Nat.mod_lt (mask >>> (p - d % p)) two_pos; omega)
    rw [← hdz]
    exact_mod_cast Nat.dvd_of_mod_eq_zero h0

theorem nodup_sieveList {P : List (ℕ × ℕ)} (hP : PrimesOK P) (d : ℕ) : ((sieveList P d).map (·.1)).Nodup :=
  (sublist_sieveList P).nodup hP.2

/-! ### The per-field statement -/

/-- **Soundness of the check.** For `K` of degree two containing `√-m`, `m` squarefree, a passing check
gives `N < classNumber K`. -/
theorem lt_classNumber_of_checkAt {K : Type*} [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
    {m : ℕ} (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K)) {N Y : ℕ} {P : List (ℕ × ℕ)}
    (hP : PrimesOK P) (h : checkAt N Y P m = true) : N < classNumber K := by
  obtain ⟨α, hα⟩ := hsq
  have D := CN1.Finite.quadIntOfFoundations hK hm hα
  have htc := HCN.Finite.tOf_mul_lt_four_mul_cOf hm.ne_zero
  have hd : CN1.Finite.dOf m = 4 * CN1.Finite.cOf m - CN1.Finite.tOf m * CN1.Finite.tOf m := by
    have := CN1.Finite.four_mul_cOf m; rw [sq] at this; omega
  simp only [checkAt, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨hY, hN⟩ := h
  rw [hd] at hY hN
  exact lt_of_lt_of_le (lt_of_lt_of_le hN (muK_le_mu _ _ _))
    (mu_le_classNumber D htc _ (sieveList_spec htc hP) (nodup_sieveList hP _) hY)

end BoundariesOfClass.Sieve
