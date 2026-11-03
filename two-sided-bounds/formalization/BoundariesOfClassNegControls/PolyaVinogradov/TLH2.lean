import BoundariesOfClassNegControls.PolyaVinogradov.CNFSeven

/-!
# Negative control TLH2: the `log log` bound for `L(1, χ)` with `2` replaced by `-1` is false

Refuted at `χ_{-7}` via the class number formula: `‖L(1, χ_{-7})‖ > 1`, while
`½ log 7 + log log 7 - 1 < 1` (COMPUTED value 0.6387), using `log 7 < 1.9545` and `log y ≤ y - 1`.
-/

set_option autoImplicit false

open CN1.Foundations

namespace BoundariesOfClassNegControls.PolyaVinogradov

/-- The tampered statement TLH2. -/
def TLH2 : Prop :=
  ∀ {q : ℕ} [NeZero q], 7 ≤ q → ∀ (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
    ‖χ.LFunction 1‖ ≤ Real.log q / 2 + Real.log (Real.log q) + -1

/-- **TLH2 is false.** -/
theorem not_TLH2 : ¬ TLH2 := by
  intro h
  have h7 := h (q := disc 7) (by rw [disc_seven]) (kroneckerChar 7) kronecker_seven_isPrimitive
  have hL := one_lt_norm_LFunction_seven
  have hq : ((disc 7 : ℕ) : ℝ) = 7 := by rw [disc_seven]; norm_num
  rw [hq] at h7
  have h1 := log_seven_lt
  have h2 := one_lt_log_seven
  have h3 : Real.log (Real.log 7) ≤ Real.log 7 - 1 := Real.log_le_sub_one_of_pos (by linarith)
  linarith

end BoundariesOfClassNegControls.PolyaVinogradov
