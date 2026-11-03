import Mathlib

/-!
# Control C-PV1: a `sorry` solution

`BoundariesOfClass.classNumber_le_half_log` declared with its proof replaced by `sorry`. As a solution, it must FAIL
the axiom check (`sorryAx` in the axiom set), and Comparator must REJECT it. Never import this module together with the
challenge or the real solution.
-/

open NumberField

namespace BoundariesOfClass

theorem classNumber_le_half_log (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hd : (5 : ℝ) ≤ |(discr K : ℝ)|) :
    (classNumber K : ℝ) ≤ Real.sqrt |(discr K : ℝ)| *
      (Real.log |(discr K : ℝ)| / 2 + Real.log (Real.log |(discr K : ℝ)| + 1 / 3) + 5 / 3) / Real.pi := by
  sorry

end BoundariesOfClass
