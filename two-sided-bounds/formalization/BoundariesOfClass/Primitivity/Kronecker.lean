import CN1.Foundations.Character
import BoundariesOfClass.Primitivity.Criterion

/-!
# BoundariesOfClass.Primitivity.Kronecker: the Kronecker character `χ_{-d}` is primitive

Pinned environment: Lean v4.34.1, Mathlib d13f23b. Imports Mathlib and the Mathlib-only foundations of the CN-1
formalization (tenth-discriminant), where `kroneckerChar m : DirichletCharacter ℂ (disc m)` is defined.

* `kroneckerChar_isPrimitive`: for squarefree `m`, `χ_{-d}` (`d = disc m`) is primitive.
* `conductor_kroneckerChar`: equivalently, the conductor of `χ_{-d}` is `d`.

The proof applies the criterion `isPrimitive_of_forall_prime`. For each prime `p ∣ d` it exhibits `a` coprime to `d`
with `a ≡ 1 (mod d/p)` and `χ_{-d}(a) = -1`:

* `p` odd: `a` is a quadratic non-residue modulo `p` and `≡ 1` modulo `d/p` (Chinese remainder theorem). The factor
  `χ₄` or `χ₈` of `χ_{-d}` is `1` at `a`, since `4` or `8` divides `d/p`, and the Jacobi factor is
  `(a/p) · J(1 | m/p) = -1`;
* `p = 2` (then `d = 4m`): `a = 1 + 2m`, which is `3 (mod 4)` if `m ≡ 1 (mod 4)` and `5 (mod 8)` if `m ≡ 2 (mod 4)`, and
  `≡ 1` modulo the odd part of `m`.
-/

set_option autoImplicit false

namespace BoundariesOfClass.Primitivity

open CN1.Foundations

/-- If `a ≡ b (mod k)` in `ℕ`, then `a ≡ b (mod k)` in `ℤ`. -/
lemma intCast_emod_eq_of_modEq {a b k : ℕ} (h : a ≡ b [MOD k]) : (a : ℤ) % k = (b : ℤ) % k := by
  have h' := congrArg (fun x : ℕ => (x : ℤ)) (show a % k = b % k from h)
  push_cast at h'
  exact h'

/-- `J(a | k) = 1` when `a ≡ 1 (mod k)`. -/
lemma jacobiSym_eq_one_of_modEq {a k : ℕ} (h : a ≡ 1 [MOD k]) : jacobiSym a k = 1 := by
  rw [jacobiSym.mod_left' (a₂ := 1) (by simpa using intCast_emod_eq_of_modEq h), jacobiSym.one_left]

/-- A prime `p` with `p ∣ d = c n`, `n` squarefree and `p` coprime to `c`, does not divide `d/p`. -/
lemma not_dvd_div_of_squarefree {p n c d : ℕ} (hp : p.Prime) (hn : Squarefree n) (hpc : Nat.Coprime p c)
    (hd : d = c * n) (hpd : p ∣ d) : ¬ p ∣ d / p := by
  intro h
  have h2 : p * p ∣ c * n := hd ▸ Nat.mul_dvd_of_dvd_div hpd h
  have h3 : p * p ∣ n := (Nat.coprime_mul_iff_left.mpr ⟨hpc, hpc⟩).dvd_of_dvd_mul_left h2
  exact hp.one_lt.ne' (Nat.isUnit_iff.mp (hn p h3))

/-- If `a` is coprime to `L` and `p ∣ L`, then `a` is coprime to `p L`. -/
lemma coprime_mul_of_dvd {a p L : ℕ} (haL : Nat.Coprime a L) (hpL : p ∣ L) : Nat.Coprime a (p * L) :=
  Nat.Coprime.mul_right (Nat.Coprime.coprime_dvd_right hpL haL) haL

/-- **The witness at an odd prime.** Let `p` be an odd prime dividing the squarefree `n`, and `L` a multiple of `n/p`
prime to `p`. Then some `a ≡ 1 (mod L)` has `J(a | n) = -1` and is coprime to `p L`. -/
lemma exists_witness_odd {p n L : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : Squarefree n) (hpn : p ∣ n)
    (hnL : n / p ∣ L) (hLp : ¬ p ∣ L) :
    ∃ a : ℕ, a ≡ 1 [MOD L] ∧ jacobiSym a n = -1 ∧ Nat.Coprime a (p * L) := by
  have := Fact.mk hp
  obtain ⟨b, hb⟩ := FiniteField.exists_nonsquare (F := ZMod p) (by rw [ZMod.ringChar_zmod_n]; exact hp2)
  have hcop : Nat.Coprime L p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hLp).symm
  obtain ⟨a, ha1, hab⟩ := Nat.chineseRemainder hcop 1 b.val
  have hab' : (a : ZMod p) = b := by
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr hab, ZMod.natCast_zmod_val]
  have hleg : legendreSym p (a : ℤ) = -1 := by
    rw [legendreSym.eq_neg_one_iff, Int.cast_natCast, hab']
    exact hb
  have hpa : ¬ p ∣ a := by
    intro h
    have h0 := (ZMod.natCast_eq_zero_iff a p).mpr h
    rw [hab'] at h0
    exact hb ⟨0, by rw [h0, mul_zero]⟩
  obtain ⟨k, hk⟩ := hpn
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hn.ne_zero (by rw [hk, mul_zero])
  have hkL : k ∣ L := by
    rwa [hk, Nat.mul_div_cancel_left _ hp.pos] at hnL
  have : NeZero p := ⟨hp.ne_zero⟩
  have : NeZero k := ⟨hk0⟩
  refine ⟨a, ha1, ?_, ?_⟩
  · rw [hk, jacobiSym.mul_right, ← jacobiSym.legendreSym.to_jacobiSym, hleg,
      jacobiSym_eq_one_of_modEq (ha1.of_dvd hkL)]
    norm_num
  · have hap : Nat.Coprime a p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpa).symm
    have haL : Nat.Coprime a L := (Nat.ModEq.gcd_eq ha1).trans (Nat.gcd_one_left L)
    exact Nat.Coprime.mul_right hap haL

/-- An odd prime dividing `4m` divides `m`. -/
lemma dvd_of_dvd_four_mul {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : p ∣ 4 * m) : p ∣ m := by
  have hc : Nat.Coprime p 4 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact Nat.Coprime.pow_right 2 ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  exact hc.dvd_of_dvd_mul_left h

/-- **`χ_{-d}` is primitive:** its conductor is `d = disc m`, for every squarefree `m`. -/
theorem kroneckerChar_isPrimitive {m : ℕ} (hm : Squarefree m) : (kroneckerChar m).IsPrimitive := by
  have hm0 : m ≠ 0 := hm.ne_zero
  have hd0 : disc m ≠ 0 := by unfold disc; split_ifs <;> omega
  have : NeZero (disc m) := ⟨hd0⟩
  apply isPrimitive_of_forall_prime
  intro p hp hpd
  -- `a` with `a ≡ 1 (mod d/p)`, coprime to `d`, and `χ(a) = -1` suffices
  suffices hw : ∃ a : ℕ, a ≡ 1 [MOD disc m / p] ∧ Nat.Coprime a (disc m) ∧
      kroneckerChar m ((a : ℤ) : ZMod (disc m)) = -1 by
    obtain ⟨a, ha1, hac, hχ⟩ := hw
    refine ⟨a, hac, by simpa using (ZMod.natCast_eq_natCast_iff a 1 _).mpr ha1, ?_⟩
    rw [← Int.cast_natCast, hχ]
    norm_num
  have hpL : p * (disc m / p) = disc m := Nat.mul_div_cancel' hpd
  rcases squarefree_mod_four_cases hm with h1 | h2 | h3
  · -- `m ≡ 1 (mod 4)`, `d = 4m`, `χ = χ₄ · J(· | m)`
    have hd : disc m = 4 * m := disc_of_not_three_mod_four (by omega)
    rcases eq_or_ne p 2 with rfl | hp2
    · have hL : disc m / 2 = 2 * m := by rw [hd]; omega
      have ha1 : 1 + 2 * m ≡ 1 [MOD 2 * m] := Nat.add_mod_right 1 (2 * m)
      have hcop : Nat.Coprime (1 + 2 * m) (disc m) := by
        have := coprime_mul_of_dvd ((Nat.ModEq.gcd_eq ha1).trans (Nat.gcd_one_left _))
          (dvd_mul_right 2 m)
        rwa [show 2 * (2 * m) = disc m by omega] at this
      refine ⟨1 + 2 * m, hL ▸ ha1, hcop, ?_⟩
      rw [kroneckerChar_apply_of_one_mod_four h1 (Nat.isCoprime_iff_coprime.mpr hcop),
        ZMod.χ₄_int_three_mod_four (by push_cast; omega),
        jacobiSym_eq_one_of_modEq (ha1.of_dvd (dvd_mul_left m 2))]
      norm_num
    · have hpm : p ∣ m := dvd_of_dvd_four_mul hp hp2 (hd ▸ hpd)
      have hLp := not_dvd_div_of_squarefree hp hm
        (by rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
            exact Nat.Coprime.pow_right 2 ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)) hd hpd
      have hL : disc m / p = 4 * (m / p) := by rw [hd, Nat.mul_div_assoc 4 hpm]
      obtain ⟨a, ha1, hJ, hac⟩ := exists_witness_odd hp hp2 hm hpm (hL ▸ dvd_mul_left _ 4) hLp
      rw [hpL] at hac
      refine ⟨a, ha1, hac, ?_⟩
      have h4 : (a : ℤ) % 4 = 1 := by
        have := intCast_emod_eq_of_modEq (ha1.of_dvd (hL ▸ dvd_mul_right 4 (m / p)))
        push_cast at this
        omega
      rw [kroneckerChar_apply_of_one_mod_four h1 (Nat.isCoprime_iff_coprime.mpr hac),
        ZMod.χ₄_int_one_mod_four h4, hJ]
      norm_num
  · -- `m ≡ 2 (mod 4)`, `d = 4m = 8 (m/2)`, `χ = χ₈ or χ₈' · J(· | m/2)`
    have hd : disc m = 4 * m := disc_of_not_three_mod_four (by omega)
    rcases eq_or_ne p 2 with rfl | hp2
    · have hL : disc m / 2 = 2 * m := by rw [hd]; omega
      have ha1 : 1 + 2 * m ≡ 1 [MOD 2 * m] := Nat.add_mod_right 1 (2 * m)
      have hcop : Nat.Coprime (1 + 2 * m) (disc m) := by
        have := coprime_mul_of_dvd ((Nat.ModEq.gcd_eq ha1).trans (Nat.gcd_one_left _))
          (dvd_mul_right 2 m)
        rwa [show 2 * (2 * m) = disc m by omega] at this
      refine ⟨1 + 2 * m, hL ▸ ha1, hcop, ?_⟩
      have hm2 : m / 2 ∣ 2 * m := ⟨4, by omega⟩
      rw [kroneckerChar_apply_of_two_mod_four h2 (Nat.isCoprime_iff_coprime.mpr hcop),
        jacobiSym_eq_one_of_modEq (ha1.of_dvd hm2)]
      have h8 : ((1 + 2 * m : ℕ) : ℤ) % 8 = 5 := by push_cast; omega
      have h2' : ((1 + 2 * m : ℕ) : ℤ) % 2 = 1 := by push_cast; omega
      split_ifs
      · rw [ZMod.χ₈'_int_eq_if_mod_eight, h8, h2']; norm_num
      · rw [ZMod.χ₈_int_eq_if_mod_eight, h8, h2']; norm_num
    · have hpm : p ∣ m := dvd_of_dvd_four_mul hp hp2 (hd ▸ hpd)
      have hm' : m = 2 * (m / 2) := by omega
      have hpm' : p ∣ m / 2 := by
        have hc : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr hp2
        exact hc.dvd_of_dvd_mul_left (hm' ▸ hpm)
      have hsq' : Squarefree (m / 2) := hm.squarefree_of_dvd ⟨2, by omega⟩
      have hd8 : disc m = 8 * (m / 2) := by rw [hd]; omega
      have hLp := not_dvd_div_of_squarefree hp hsq'
        (by rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
            exact Nat.Coprime.pow_right 3 ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)) hd8 hpd
      have hL : disc m / p = 8 * (m / 2 / p) := by rw [hd8, Nat.mul_div_assoc 8 hpm']
      obtain ⟨a, ha1, hJ, hac⟩ := exists_witness_odd hp hp2 hsq' hpm' (hL ▸ dvd_mul_left _ 8) hLp
      rw [hpL] at hac
      refine ⟨a, ha1, hac, ?_⟩
      have h8 : (a : ℤ) % 8 = 1 := by
        have := intCast_emod_eq_of_modEq (ha1.of_dvd (hL ▸ dvd_mul_right 8 (m / 2 / p)))
        push_cast at this
        omega
      have h2' : (a : ℤ) % 2 = 1 := by omega
      rw [kroneckerChar_apply_of_two_mod_four h2 (Nat.isCoprime_iff_coprime.mpr hac), hJ]
      split_ifs
      · rw [ZMod.χ₈'_int_eq_if_mod_eight, h8, h2']; norm_num
      · rw [ZMod.χ₈_int_eq_if_mod_eight, h8, h2']; norm_num
  · -- `m ≡ 3 (mod 4)`, `d = m`, `χ = J(· | m)`
    have hd : disc m = m := disc_of_three_mod_four h3
    have hp2 : p ≠ 2 := by
      rintro rfl
      have : 2 ∣ m := hd ▸ hpd
      omega
    have hpm : p ∣ m := hd ▸ hpd
    have hLp := not_dvd_div_of_squarefree hp hm (Nat.coprime_one_right p) (by rw [hd, one_mul]) hpd
    obtain ⟨a, ha1, hJ, hac⟩ := exists_witness_odd hp hp2 hm hpm (by rw [hd]) hLp
    rw [hpL] at hac
    refine ⟨a, ha1, hac, ?_⟩
    rw [kroneckerChar_apply_of_three_mod_four h3 (Nat.isCoprime_iff_coprime.mpr hac), hJ]
    norm_num

/-- **The conductor of `χ_{-d}` is `d = disc m`**, for every squarefree `m`. -/
theorem conductor_kroneckerChar {m : ℕ} (hm : Squarefree m) : (kroneckerChar m).conductor = disc m :=
  (DirichletCharacter.isPrimitive_def _).mp (kroneckerChar_isPrimitive hm)

end BoundariesOfClass.Primitivity
