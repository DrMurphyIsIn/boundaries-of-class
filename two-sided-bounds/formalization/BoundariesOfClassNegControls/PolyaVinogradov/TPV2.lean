import BoundariesOfClassNegControls.PolyaVinogradov.Common

/-!
# Negative control TPV2: the Pólya–Vinogradov inequality without the factor `√q` is false

Refuted at `χ_{-11}` (primitive, level 11), `M = 1`, `N = 5`: `χ(1) + ⋯ + χ(5) = 1 - 1 + 1 + 1 + 1 = 3`, while
`log 11 + 1/3 < 8/3 + 1/3 = 3` (COMPUTED value 2.7312; `D = 11` is the least `D` where this tamper fails).
-/

set_option autoImplicit false

open CN1.Foundations

namespace BoundariesOfClassNegControls.PolyaVinogradov

/-- The tampered statement TPV2. -/
def TPV2 : Prop :=
  ∀ {q : ℕ} [NeZero q], 1 < q → ∀ (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ (M : ℤ) (N : ℕ),
    ‖∑ n ∈ Finset.range N, χ ((M + n : ℤ) : ZMod q)‖ ≤ (Real.log q + 1 / 3)

/-- **TPV2 is false.** -/
theorem not_TPV2 : ¬ TPV2 := by
  intro h
  have h11 := h (q := disc 11) (by rw [disc_eleven]; norm_num) (kroneckerChar 11) kronecker_eleven_isPrimitive 1 5
  rw [sum_kronecker_eleven, disc_eleven] at h11
  norm_num at h11
  have := log_eleven_lt
  linarith

end BoundariesOfClassNegControls.PolyaVinogradov
