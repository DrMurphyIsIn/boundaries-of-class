import BoundariesOfClass.ClassNumberFormula.Main
import BoundariesOfClass.Assembly.Upper

/-!
# BoundariesOfClassNegControls.ClassNumberFormula.DecoyClassSum: control C-CNF3 (a class-sum decoy for (U′))

Pinned environment: Lean v4.34.1, Mathlib d13f23b. Never imported by the solution. A copy of
`BoundariesOfClass.classNumber_le_sharp` whose proof first names the class-sum core
`BoundariesOfClass.Assembly.classSum_le_sq` in a vacuous `have`, which keeps it (and with it HCN's class partition and
Chowla–Selberg) in the proof term, and then applies the solution's theorem.

Expected (pre-registered): the module builds. The closure of `classNumber_le_sharp_classSumDecoy` contains constants
from `BoundariesOfClass.Assembly` and HCN modules, so the CNF module allowlist of the closure audit FAILs. That is the registered
failure.
-/

set_option autoImplicit false

open NumberField

namespace BoundariesOfClassNegControls.ClassNumberFormula

/-- **C-CNF3.** `classNumber_le_sharp`, with a vacuous reference to the class-sum core. -/
theorem classNumber_le_sharp_classSumDecoy (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hd : (5 : ℝ) ≤ |(discr K : ℝ)|) :
    (classNumber K : ℝ) ≤
      Real.sqrt |(discr K : ℝ)| * (Real.log |(discr K : ℝ)| + 7 / 6) / Real.pi := by
  have _decoy := @BoundariesOfClass.Assembly.classSum_le_sq K
  exact BoundariesOfClass.classNumber_le_sharp K hK m hm hsq hd

end BoundariesOfClassNegControls.ClassNumberFormula
