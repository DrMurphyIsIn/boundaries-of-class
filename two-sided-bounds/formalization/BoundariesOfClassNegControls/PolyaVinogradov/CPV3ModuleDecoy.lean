import CN1.Foundations.Character
import BoundariesOfClass.PolyaVinogradov.Main

/-!
# Control C-PV3: a module-set decoy

A copy of the Pólya–Vinogradov headline whose proof binds CN-1's `kroneckerChar` in a vacuous `have`. P1 must be a
Mathlib-only result, so the closure audit must FAIL this at its module-set check: the module set acquires CN1.Foundations modules.
-/

set_option autoImplicit false

namespace BoundariesOfClassNegControls.PolyaVinogradov

theorem decoy_cn1_norm_sum_le_of_isPrimitive {q : ℕ} [NeZero q] (hq : 1 < q) (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (M : ℤ) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, χ ((M + n : ℤ) : ZMod q)‖ ≤ Real.sqrt q * (Real.log q + 1 / 3) := by
  have _h := @CN1.Foundations.kroneckerChar
  exact BoundariesOfClass.norm_sum_le_of_isPrimitive hq χ hχ M N

end BoundariesOfClassNegControls.PolyaVinogradov
