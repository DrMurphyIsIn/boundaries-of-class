import BoundariesOfClass.ClassNumberFormula.Main
import BoundariesOfClass.Primitivity.Field
import BoundariesOfClassNegControls.Fields
import BoundariesOfClassNegControls.PolyaVinogradov.Common

/-!
# Negative control TPR1: "the character of `ℚ(√-m)` is never primitive" is false

The field statement with its conclusion negated. Refuted at `K = ℚ(√-7)`, with the character `χ` given by the
existence statement (`BoundariesOfClass.exists_LFunction_factorisation`), which is primitive by the true statement
(`BoundariesOfClass.isPrimitive_of_factorisation`). Fields in `Type`, as for TUH1.
-/

set_option autoImplicit false

open NumberField BoundariesOfClassNegControls CN1.Foundations BoundariesOfClass.ClassNumberFormula

namespace BoundariesOfClassNegControls.PolyaVinogradov

/-- The tampered statement TPR1. -/
def TPR1 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (m : ℕ), Squarefree m →
    (∃ α : K, α ^ 2 = -(m : K)) → ∀ [NeZero (discr K).natAbs] (χ : DirichletCharacter ℂ (discr K).natAbs),
    (∀ s : ℂ, 1 < s.re → dedekindZeta K s = riemannZeta s * χ.LFunction s) → ¬ χ.IsPrimitive

/-- **TPR1 is false.** -/
theorem not_TPR1 : ¬ TPR1 := by
  intro h
  have hN : (discr (KField 7)).natAbs = 7 := by
    rw [natAbs_discr_eq (rootK_sq 7) (finrank_KField 7) squarefree_7, disc_seven]
  have : NeZero (discr (KField 7)).natAbs := ⟨by rw [hN]; norm_num⟩
  obtain ⟨χ, hχ⟩ := BoundariesOfClass.exists_LFunction_factorisation (KField 7) (finrank_KField 7) 7 squarefree_7
    (exists_sq_eq_neg 7)
  exact h (KField 7) (finrank_KField 7) 7 squarefree_7 (exists_sq_eq_neg 7) χ hχ
    (BoundariesOfClass.isPrimitive_of_factorisation (KField 7) (finrank_KField 7) 7 squarefree_7 (exists_sq_eq_neg 7) χ hχ)

end BoundariesOfClassNegControls.PolyaVinogradov
