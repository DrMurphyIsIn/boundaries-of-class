import Mathlib

/-!
# BoundariesOfClass.ClassNumberFormula.CharSum: interval sums of a non-trivial character, and Abel's inequality

Pinned environment: Lean v4.34.1, Mathlib d13f23b. Mathlib only.

* `sum_range_eq_sum_zmod`: a sum over `ZMod q` is the sum over `0 ≤ i < q` of the natural-number casts.
* `sum_range_period_eq_zero`: for a non-trivial Dirichlet character `χ` of level `q`, any `q` consecutive values sum to
  `0` (Mathlib's `MulChar.sum_eq_zero_of_ne_one`, plus periodicity).
* `norm_sum_range_le`: every interval sum `Σ_{a ≤ n < a+ℓ} χ(n)` has norm at most `q/2`. Reduce `ℓ` modulo `q`; a sum of
  `r < q` terms is bounded by `r` directly, and by `q - r` through the complementary part of the period.
* `norm_sum_mul_le_of_antitone`: **Abel's inequality.** If every partial sum of `a` has norm at most `C`, and `b ≥ 0`
  is antitone, then `‖Σ_{i<ℓ} b_i a_i‖ ≤ C b_0`.

These are the classical ingredients of the partial-summation bound for `L(1, χ)`.
-/

set_option autoImplicit false

namespace BoundariesOfClass.ClassNumberFormula

open Finset

section CharSum

variable {q : ℕ} [NeZero q]

/-- A sum over `ZMod q` is the sum over `i ∈ range q` of the casts. -/
lemma sum_range_eq_sum_zmod (f : ZMod q → ℂ) : ∑ i ∈ range q, f (i : ZMod q) = ∑ x, f x := by
  refine Finset.sum_nbij' (fun i : ℕ => (i : ZMod q)) (fun x : ZMod q => x.val) ?_ ?_ ?_ ?_ ?_
  · intro i _; exact mem_univ _
  · intro x _; exact mem_range.mpr (ZMod.val_lt x)
  · intro i hi; exact ZMod.val_cast_of_lt (mem_range.mp hi)
  · intro x _; exact ZMod.natCast_zmod_val x
  · intro i _; rfl

omit [NeZero q] in
/-- The values of `χ` are `q`-periodic in the natural-number argument. -/
lemma apply_add_level (χ : DirichletCharacter ℂ q) (a : ℕ) :
    χ ((a + q : ℕ) : ZMod q) = χ (a : ZMod q) := by
  rw [Nat.cast_add, ZMod.natCast_self, add_zero]

/-- **A full period sums to zero**, from any starting point, for a non-trivial character. -/
lemma sum_range_period_eq_zero (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (a : ℕ) :
    ∑ i ∈ range q, χ ((a + i : ℕ) : ZMod q) = 0 := by
  induction a with
  | zero =>
    simp only [zero_add]
    rw [sum_range_eq_sum_zmod (fun x => χ x)]
    exact MulChar.sum_eq_zero_of_ne_one hχ
  | succ a ih =>
    have h1 := Finset.sum_range_succ' (fun i => χ ((a + i : ℕ) : ZMod q)) q
    have h2 := Finset.sum_range_succ (fun i => χ ((a + i : ℕ) : ZMod q)) q
    beta_reduce at h1 h2
    have hq : χ ((a + q : ℕ) : ZMod q) = χ ((a + 0 : ℕ) : ZMod q) := by
      rw [apply_add_level, add_zero]
    have hsh : ∑ i ∈ range q, χ ((a + 1 + i : ℕ) : ZMod q) = ∑ i ∈ range q, χ ((a + (i + 1) : ℕ) : ZMod q) :=
      Finset.sum_congr rfl fun i _ => by rw [show a + 1 + i = a + (i + 1) by omega]
    rw [hsh]
    linear_combination -h1 + h2 + hq + ih

/-- Adding a full period to the length does not change an interval sum. -/
lemma sum_range_level_add (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (a ℓ : ℕ) :
    ∑ i ∈ range (q + ℓ), χ ((a + i : ℕ) : ZMod q) = ∑ i ∈ range ℓ, χ ((a + i : ℕ) : ZMod q) := by
  rw [Finset.sum_range_add, sum_range_period_eq_zero χ hχ a, zero_add]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show a + (q + i) = (a + i) + q by omega, apply_add_level]

/-- **Interval sums of a non-trivial character are at most `q/2`.** -/
theorem norm_sum_range_le (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (a ℓ : ℕ) :
    ‖∑ i ∈ range ℓ, χ ((a + i : ℕ) : ZMod q)‖ ≤ q / 2 := by
  induction ℓ using Nat.strong_induction_on with
  | _ ℓ ih =>
    by_cases hℓ : q ≤ ℓ
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hℓ
      rw [sum_range_level_add χ hχ a k]
      exact ih k (by have := NeZero.pos q; omega)
    · replace hℓ := not_le.mp hℓ
      -- the direct bound: `ℓ` terms of norm at most one
      have hdir : ‖∑ i ∈ range ℓ, χ ((a + i : ℕ) : ZMod q)‖ ≤ ℓ := by
        refine (norm_sum_le _ _).trans ?_
        refine (Finset.sum_le_sum fun i _ => DirichletCharacter.norm_le_one χ _).trans ?_
        simp
      -- the complementary bound: the rest of the period, `q - ℓ` terms
      have hsplit := Finset.sum_range_add (fun i => χ ((a + i : ℕ) : ZMod q)) ℓ (q - ℓ)
      beta_reduce at hsplit
      rw [show ℓ + (q - ℓ) = q by omega, sum_range_period_eq_zero χ hχ a] at hsplit
      have hcomp : ‖∑ i ∈ range ℓ, χ ((a + i : ℕ) : ZMod q)‖ ≤ ((q - ℓ : ℕ) : ℝ) := by
        rw [show ∑ i ∈ range ℓ, χ ((a + i : ℕ) : ZMod q) =
            -∑ i ∈ range (q - ℓ), χ ((a + (ℓ + i) : ℕ) : ZMod q) by linear_combination -hsplit, norm_neg]
        refine (norm_sum_le _ _).trans ?_
        refine (Finset.sum_le_sum fun i _ => DirichletCharacter.norm_le_one χ _).trans ?_
        simp
      have hcast : ((q - ℓ : ℕ) : ℝ) = (q : ℝ) - ℓ := by rw [Nat.cast_sub hℓ.le]
      rw [hcast] at hcomp
      linarith

end CharSum

/-- **Abel's inequality.** If every partial sum of `a` has norm at most `C` and `b` is non-negative and antitone,
then `‖Σ_{i<ℓ} b_i a_i‖ ≤ C b_0`. -/
theorem norm_sum_mul_le_of_antitone {a : ℕ → ℂ} {b : ℕ → ℝ} {C : ℝ} (hb : Antitone b) (hb0 : ∀ n, 0 ≤ b n)
    (hA : ∀ ℓ, ‖∑ i ∈ range ℓ, a i‖ ≤ C) (ℓ : ℕ) :
    ‖∑ i ∈ range ℓ, (b i : ℂ) * a i‖ ≤ C * b 0 := by
  set A : ℕ → ℂ := fun k => ∑ i ∈ range k, a i with hAdef
  -- summation by parts
  have hparts : ∀ ℓ, ∑ i ∈ range ℓ, (b i : ℂ) * a i =
      (b ℓ : ℂ) * A ℓ + ∑ i ∈ range ℓ, ((b i - b (i + 1) : ℝ) : ℂ) * A (i + 1) := by
    intro ℓ
    induction ℓ with
    | zero => simp [hAdef]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      have hA1 : A (n + 1) = A n + a n := by simp [hAdef, Finset.sum_range_succ]
      rw [hA1]
      push_cast
      ring
  rw [hparts ℓ]
  have hC : 0 ≤ C := (norm_nonneg _).trans (hA 0)
  have hdiff : ∀ i, 0 ≤ b i - b (i + 1) := fun i => sub_nonneg.mpr (hb (Nat.le_succ i))
  have htel : ∑ i ∈ range ℓ, (b i - b (i + 1)) = b 0 - b ℓ := Finset.sum_range_sub' b ℓ
  calc ‖(b ℓ : ℂ) * A ℓ + ∑ i ∈ range ℓ, ((b i - b (i + 1) : ℝ) : ℂ) * A (i + 1)‖
      ≤ ‖(b ℓ : ℂ) * A ℓ‖ + ‖∑ i ∈ range ℓ, ((b i - b (i + 1) : ℝ) : ℂ) * A (i + 1)‖ := norm_add_le _ _
    _ ≤ b ℓ * C + ∑ i ∈ range ℓ, (b i - b (i + 1)) * C := by
        gcongr
        · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hb0 ℓ)]
          exact mul_le_mul_of_nonneg_left (hA ℓ) (hb0 ℓ)
        · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hdiff i)]
          exact mul_le_mul_of_nonneg_left (hA (i + 1)) (hdiff i)
    _ = C * b 0 := by rw [← Finset.sum_mul, htel]; ring

end BoundariesOfClass.ClassNumberFormula
