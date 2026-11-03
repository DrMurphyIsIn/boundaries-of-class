import OAI.NumberTheory.DirichletL.Nonvanishing
import BoundariesOfClass.PolyaVinogradov.Main

/-!
# Control C-PV2: an OAI decoy

A copy of the Pólya–Vinogradov headline whose proof first binds OpenAI's 7/8 non-vanishing theorem in a vacuous `have`,
so that the theorem's constant is in the proof term. The closure audit must FAIL it: a constant of T in the closure
(the edge rule), and a module set different from P1's (the module-set check).
-/

set_option autoImplicit false

namespace BoundariesOfClassNegControls.PolyaVinogradov

theorem decoy_oai_norm_sum_le_of_isPrimitive {q : ℕ} [NeZero q] (hq : 1 < q) (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (M : ℤ) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, χ ((M + n : ℤ) : ZMod q)‖ ≤ Real.sqrt q * (Real.log q + 1 / 3) := by
  have _h := @OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re
  exact BoundariesOfClass.norm_sum_le_of_isPrimitive hq χ hχ M N

end BoundariesOfClassNegControls.PolyaVinogradov
