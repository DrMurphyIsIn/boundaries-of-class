import BoundariesOfClassNegControls.Fields
import HCN.Main

/-!
# BoundariesOfClassNegControls.ClassNumberFormula.TamperHCN: TU2, refuted at `K_23`

Pinned environment: Lean v4.34.1, Mathlib d13f23b. Never imported by the solution. Kept apart from `Tampers.lean`
because it uses HCN's classification (and with it OpenAI's theorem), which the CNF controls otherwise avoid.

* `TU2` ((U′) with `1/π → 1/(2π)` and `7/6 → 0`, i.e. `h ≤ √d log d/(2π)`): at `m = 23`, `d = 23` and `h ≥ 3`
  (`HCN.classNumber_le_two_iff`: `23` is not in its list), while `√23 log 23/(2π) < 2.65`, from `log 23 < 5 log 2`,
  `√23 < 4.8` and `π > 3.14`.

Expected (pre-registered): the module builds; `not_TU2` is a theorem (control C-CNF4).
-/

set_option autoImplicit false

open NumberField

namespace BoundariesOfClassNegControls.ClassNumberFormula

lemma abs_discr_23 : |(discr (KField 23) : ℝ)| = 23 := by
  rw [abs_discr_KField 23 squarefree_23]; norm_num [CN1.Finite.dOf]

lemma three_le_classNumber_23 : 3 ≤ classNumber (KField 23) := by
  by_contra hlt
  have h2 : classNumber (KField 23) ≤ 2 := by omega
  have := (HCN.classNumber_le_two_iff (KField 23) (finrank_KField 23) 23 squarefree_23 (exists_sq_eq_neg 23)).1 h2
  revert this
  decide

/-- The tampered (U′): `1/π → 1/(2π)` and `7/6 → 0`. -/
def TU2 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (m : ℕ), Squarefree m →
    (∃ α : K, α ^ 2 = -(m : K)) → (5 : ℝ) ≤ |(discr K : ℝ)| →
    (classNumber K : ℝ) ≤ Real.sqrt |(discr K : ℝ)| * Real.log |(discr K : ℝ)| / (2 * Real.pi)

/-- **TU2 is false**, at `K_23`. -/
theorem not_TU2 : ¬ TU2 := by
  intro h
  have h1 := h (KField 23) (finrank_KField 23) 23 squarefree_23 (exists_sq_eq_neg 23)
    (by rw [abs_discr_23]; norm_num)
  rw [abs_discr_23] at h1
  have hh : (3 : ℝ) ≤ classNumber (KField 23) := by exact_mod_cast three_le_classNumber_23
  have hlog : Real.log 23 < 5 * Real.log 2 := by
    have h32 : Real.log 23 < Real.log ((2 : ℝ) ^ 5) := Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at h32
    push_cast at h32
    linarith
  have hl2 := Real.log_two_lt_d9
  have hl0 : 0 < Real.log 23 := Real.log_pos (by norm_num)
  have hs : Real.sqrt 23 < 4.8 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hs0 := Real.sqrt_nonneg 23
  have hpi := Real.pi_gt_d2
  rw [le_div_iff₀ (by positivity)] at h1
  nlinarith

end BoundariesOfClassNegControls.ClassNumberFormula
