import BoundariesOfClassNegControls.PolyaVinogradov.Common

/-!
# Negative control TPV1: the Pólya–Vinogradov inequality with the constant `1/3` replaced by `-3/2` is false

Refuted at `χ_{-7}` (primitive, level 7), `M = 1`, `N = 2`: `χ(1) + χ(2) = 1 + 1 = 2`, while
`√7 (log 7 - 3/2) < 3 · 1/2 < 2` (COMPUTED value 1.1798).
-/

set_option autoImplicit false

open CN1.Foundations

namespace BoundariesOfClassNegControls.PolyaVinogradov

/-- The tampered statement TPV1. -/
def TPV1 : Prop :=
  ∀ {q : ℕ} [NeZero q], 1 < q → ∀ (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ (M : ℤ) (N : ℕ),
    ‖∑ n ∈ Finset.range N, χ ((M + n : ℤ) : ZMod q)‖ ≤ Real.sqrt q * (Real.log q + -3 / 2)

/-- **TPV1 is false.** -/
theorem not_TPV1 : ¬ TPV1 := by
  intro h
  have h7 := h (q := disc 7) (by rw [disc_seven]; norm_num) (kroneckerChar 7) kronecker_seven_isPrimitive 1 2
  rw [sum_kronecker_seven, disc_seven] at h7
  norm_num at h7
  have := log_seven_lt_two
  have := sqrt_seven_lt_three
  have := Real.sqrt_nonneg 7
  nlinarith

end BoundariesOfClassNegControls.PolyaVinogradov
