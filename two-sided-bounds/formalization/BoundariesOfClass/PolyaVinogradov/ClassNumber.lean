import BoundariesOfClass.ClassNumberFormula.Main
import BoundariesOfClass.Primitivity.Kronecker
import BoundariesOfClass.PolyaVinogradov.HalfLog

/-!
# BoundariesOfClass.PolyaVinogradov.ClassNumber: `h ≤ (1/π) √d (½ log d + log log d + O(1))`

Pinned environment: Lean v4.34.1, Mathlib d13f23b. Imports Mathlib and the Mathlib-only foundations and factorisation
of the CN-1 formalization (tenth-discriminant). No zero-free region is used.

**The textbook upper bound for the class number of an imaginary quadratic field.** For `K = ℚ(√-m)` with
`d = |disc K| ≥ 5` (that is, `m ∉ {1, 3}`), Dirichlet's class number formula `h = √d L(1, χ_{-d}) / π`
(`LFunction_kroneckerChar_one_eq`) and the half-log bound for the primitive character `χ_{-d}`
(`Primitivity.kroneckerChar_isPrimitive`, `norm_LFunction_one_le_of_isPrimitive`) give

* `classNumber_le_half_log`: `h ≤ (1/π) √d (½ log d + log(log d + 1/3) + 5/3)`;
* `classNumber_le_loglog`: `h ≤ (1/π) √d (½ log d + log log d + 2)`.

Both are stated in CN-1's vocabulary (`d = disc m`) and in that of Mathlib alone (`d = |NumberField.discr K|`). They
improve on `h ≤ (1/π) √d (log d + 7/6)` for every `d ≥ 49` and every `d ≥ 123` respectively.
-/

set_option autoImplicit false

open NumberField CN1.Foundations

namespace BoundariesOfClass.PolyaVinogradov

open BoundariesOfClass.ClassNumberFormula BoundariesOfClass.Primitivity

variable {K : Type*} [Field K] [NumberField K]

/-- Any bound `‖L(1, χ_{-d})‖ ≤ X` gives `h ≤ √d X / π`, for `d ≥ 5`. -/
theorem classNumber_le_of_norm_LFunction_le {m : ℕ} {α : K} (hα : α ^ 2 = -(m : K))
    (hK : Module.finrank ℚ K = 2) (hm : Squarefree m) (hd : 5 ≤ disc m) [NeZero (disc m)] {X : ℝ}
    (hX : ‖(kroneckerChar m).LFunction 1‖ ≤ X) :
    (classNumber K : ℝ) ≤ Real.sqrt (disc m) * X / Real.pi := by
  obtain ⟨hm1, hm3⟩ := ne_one_and_ne_three_of_five_le hd
  rw [LFunction_kroneckerChar_one_eq hα hK hm hm1 hm3, Complex.norm_real] at hX
  have hd0 : (0 : ℝ) < disc m := by exact_mod_cast (by omega : 0 < disc m)
  have hsd : 0 < Real.sqrt (disc m) := Real.sqrt_pos.mpr hd0
  rw [Real.norm_of_nonneg (by positivity), div_le_iff₀ hsd] at hX
  rw [le_div_iff₀ Real.pi_pos]
  linarith

/-- **The textbook upper bound, CN-1 form:** `h ≤ (1/π) √d (½ log d + log(log d + 1/3) + 5/3)` for `d ≥ 5`. -/
theorem classNumber_le_half_log_disc {m : ℕ} {α : K} (hα : α ^ 2 = -(m : K)) (hK : Module.finrank ℚ K = 2)
    (hm : Squarefree m) (hd : 5 ≤ disc m) :
    (classNumber K : ℝ) ≤ Real.sqrt (disc m) *
      (Real.log (disc m) / 2 + Real.log (Real.log (disc m) + 1 / 3) + 5 / 3) / Real.pi := by
  have : NeZero (disc m) := ⟨by omega⟩
  exact classNumber_le_of_norm_LFunction_le hα hK hm hd
    (norm_LFunction_one_le_of_isPrimitive (seven_le_disc hd) (kroneckerChar m) (kroneckerChar_isPrimitive hm))

/-- **The textbook upper bound, CN-1 form, `log log` version:** `h ≤ (1/π) √d (½ log d + log log d + 2)` for
`d ≥ 5`. -/
theorem classNumber_le_loglog_disc {m : ℕ} {α : K} (hα : α ^ 2 = -(m : K)) (hK : Module.finrank ℚ K = 2)
    (hm : Squarefree m) (hd : 5 ≤ disc m) :
    (classNumber K : ℝ) ≤ Real.sqrt (disc m) *
      (Real.log (disc m) / 2 + Real.log (Real.log (disc m)) + 2) / Real.pi := by
  have : NeZero (disc m) := ⟨by omega⟩
  exact classNumber_le_of_norm_LFunction_le hα hK hm hd
    (norm_LFunction_one_le_loglog (seven_le_disc hd) (kroneckerChar m) (kroneckerChar_isPrimitive hm))

end BoundariesOfClass.PolyaVinogradov

namespace BoundariesOfClass

open BoundariesOfClass.ClassNumberFormula BoundariesOfClass.PolyaVinogradov

/-- **The textbook upper bound for the class number.** For `K = ℚ(√-m)` with `d = |disc K| ≥ 5` (that is,
`m ∉ {1, 3}`): `h(K) ≤ (1/π) √d (½ log d + log(log d + 1/3) + 5/3)`. -/
theorem classNumber_le_half_log (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hd : (5 : ℝ) ≤ |(discr K : ℝ)|) :
    (classNumber K : ℝ) ≤ Real.sqrt |(discr K : ℝ)| *
      (Real.log |(discr K : ℝ)| / 2 + Real.log (Real.log |(discr K : ℝ)| + 1 / 3) + 5 / 3) / Real.pi := by
  obtain ⟨α, hα⟩ := hsq
  rw [abs_discr_eq hα hK hm] at hd ⊢
  exact classNumber_le_half_log_disc hα hK hm (by exact_mod_cast hd)

/-- **The textbook upper bound for the class number, `log log` form.** For `K = ℚ(√-m)` with `d = |disc K| ≥ 5`:
`h(K) ≤ (1/π) √d (½ log d + log log d + 2)`. -/
theorem classNumber_le_loglog (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hd : (5 : ℝ) ≤ |(discr K : ℝ)|) :
    (classNumber K : ℝ) ≤ Real.sqrt |(discr K : ℝ)| *
      (Real.log |(discr K : ℝ)| / 2 + Real.log (Real.log |(discr K : ℝ)|) + 2) / Real.pi := by
  obtain ⟨α, hα⟩ := hsq
  rw [abs_discr_eq hα hK hm] at hd ⊢
  exact classNumber_le_loglog_disc hα hK hm (by exact_mod_cast hd)

end BoundariesOfClass
