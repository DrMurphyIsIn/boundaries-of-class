import BoundariesOfClass.ClassNumberFormula.Main
import BoundariesOfClassNegControls.Fields
import BoundariesOfClassNegControls.PolyaVinogradov.Common

/-!
# Negative controls: `L(1, χ_{-7}) > 1`, via Dirichlet's class number formula

`L(1, χ_{-7}) = π h(ℚ(√-7)) / √7 ≥ π/√7 > 1`, from the class number formula in CN-1's vocabulary
(`LFunction_kroneckerChar_one_eq`), `h ≥ 1` (Mathlib's `NumberField.classNumber_pos`), `π > 3` and `√7 < 3`. This is the
"refuted at a real field via the CNF" input for the L(1) tampers.
-/

set_option autoImplicit false

open NumberField BoundariesOfClassNegControls CN1.Foundations BoundariesOfClass.ClassNumberFormula

namespace BoundariesOfClassNegControls.PolyaVinogradov

/-- **`‖L(1, χ_{-7})‖ > 1`.** -/
theorem one_lt_norm_LFunction_seven : 1 < ‖(kroneckerChar 7).LFunction 1‖ := by
  rw [LFunction_kroneckerChar_one_eq (rootK_sq 7) (finrank_KField 7) squarefree_7 (by norm_num) (by norm_num),
    Complex.norm_real, Real.norm_of_nonneg (by positivity), disc_seven]
  have hh : (1 : ℝ) ≤ classNumber (KField 7) := by exact_mod_cast classNumber_pos (KField 7)
  have hs := sqrt_seven_lt_three
  have hs0 : 0 < Real.sqrt ((7 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  rw [lt_div_iff₀ hs0, one_mul]
  push_cast at hs0 ⊢
  nlinarith [Real.pi_gt_three]

end BoundariesOfClassNegControls.PolyaVinogradov
