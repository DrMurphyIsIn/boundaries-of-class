import Mathlib

/-!
# Negative control TPR2: "the trivial character is primitive at every level `q > 1`" is false

Refuted at `q = 7`: the trivial character has conductor `1` (Mathlib's `DirichletCharacter.conductor_one`), not `7`.
This checks that the primitivity hypothesis of the Pólya–Vinogradov statement excludes the trivial character, whose
interval sums are unbounded. Mathlib only.
-/

set_option autoImplicit false

namespace BoundariesOfClassNegControls.PolyaVinogradov

/-- The tampered statement TPR2. -/
def TPR2 : Prop := ∀ (q : ℕ) [NeZero q], 1 < q → (1 : DirichletCharacter ℂ q).IsPrimitive

/-- **TPR2 is false.** -/
theorem not_TPR2 : ¬ TPR2 := by
  intro h
  have h7 := h 7 (by norm_num)
  rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_one] at h7
  norm_num at h7

end BoundariesOfClassNegControls.PolyaVinogradov
