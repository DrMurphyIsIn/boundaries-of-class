import BoundariesOfClass.ClassNumberFormula.Main
import CN1.Assembly.Positivity

/-!
# BoundariesOfClassNegControls.ClassNumberFormula.DecoyOAI: control C-CNF2 (an OAI decoy for (U′))

Pinned environment: Lean v4.34.1, Mathlib d13f23b. Never imported by the solution. A copy of
`BoundariesOfClass.classNumber_le_sharp` whose proof first names OpenAI's zero-free region
`OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re` in a vacuous `have`, which keeps that constant in the
proof term, and then applies the solution's theorem.

Expected (pre-registered): the module builds (the `have` is unused; at most a linter warning). The closure of
`classNumber_le_sharp_oaiDecoy` contains a constant of the third-party set T, so the edge rule ("no constant
of T in any CNF closure") FAILs, and the module allowlist FAILs on the OAI and CN1.Assembly modules.
-/

set_option autoImplicit false

open NumberField

namespace BoundariesOfClassNegControls.ClassNumberFormula

/-- **C-CNF2.** `classNumber_le_sharp`, with a vacuous reference to OpenAI's theorem. -/
theorem classNumber_le_sharp_oaiDecoy (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hd : (5 : ℝ) ≤ |(discr K : ℝ)|) :
    (classNumber K : ℝ) ≤
      Real.sqrt |(discr K : ℝ)| * (Real.log |(discr K : ℝ)| + 7 / 6) / Real.pi := by
  have _decoy := @OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re
  exact BoundariesOfClass.classNumber_le_sharp K hK m hm hsq hd

end BoundariesOfClassNegControls.ClassNumberFormula
