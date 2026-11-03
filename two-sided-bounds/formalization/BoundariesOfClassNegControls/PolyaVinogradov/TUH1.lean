import BoundariesOfClass.ClassNumberFormula.Invariants
import BoundariesOfClassNegControls.Fields
import BoundariesOfClassNegControls.PolyaVinogradov.Common

/-!
# Negative control TUH1: the textbook class-number bound with `5/3` replaced by `-3/2` is false

Refuted at `K = ℚ(√-7)`: `h ≥ 1` (Mathlib's `NumberField.classNumber_pos`), while the tampered bound is
`√7 (½ log 7 + log(log 7 + 1/3) - 3/2)/π < 3 · 0.77/π < 1` (COMPUTED value 0.2500). No class number formula is used.

The tampered statement quantifies over fields in `Type`; the challenge's `Type*` form implies it, so this refutes
the tamper.
-/

set_option autoImplicit false

open NumberField BoundariesOfClassNegControls CN1.Foundations BoundariesOfClass.ClassNumberFormula

namespace BoundariesOfClassNegControls.PolyaVinogradov

/-- The tampered statement TUH1. -/
def TUH1 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (m : ℕ), Squarefree m →
    (∃ α : K, α ^ 2 = -(m : K)) → (5 : ℝ) ≤ |(discr K : ℝ)| →
    (classNumber K : ℝ) ≤ Real.sqrt |(discr K : ℝ)| *
      (Real.log |(discr K : ℝ)| / 2 + Real.log (Real.log |(discr K : ℝ)| + 1 / 3) + -3 / 2) / Real.pi

/-- **TUH1 is false.** -/
theorem not_TUH1 : ¬ TUH1 := by
  intro h
  have hd := abs_discr_eq (rootK_sq 7) (finrank_KField 7) squarefree_7
  rw [disc_seven] at hd
  have h7 := h (KField 7) (finrank_KField 7) 7 squarefree_7 (exists_sq_eq_neg 7) (by rw [hd]; norm_num)
  rw [hd, le_div_iff₀ Real.pi_pos] at h7
  push_cast at h7
  have hh : (1 : ℝ) ≤ classNumber (KField 7) := by exact_mod_cast classNumber_pos (KField 7)
  have h1 := log_seven_lt
  have h2 := one_lt_log_seven
  have h3 : Real.log (Real.log 7 + 1 / 3) ≤ Real.log 7 + 1 / 3 - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hs := sqrt_seven_lt_three
  have hs0 := Real.sqrt_nonneg 7
  have hX : Real.log 7 / 2 + Real.log (Real.log 7 + 1 / 3) + -3 / 2 ≤ 0.77 := by linarith
  have hpi := Real.pi_gt_three
  nlinarith

end BoundariesOfClassNegControls.PolyaVinogradov
