import BoundariesOfClass.ClassNumberFormula.Main
import BoundariesOfClass.ClassNumberFormula.LOneEven

/-!
# BoundariesOfClass.ClassNumberFormula.MainEven: `h ≤ (1/(2π)) √d (log d + 13/5)` when `4 ∣ d`

Pinned environment: Lean v4.34.1, Mathlib d13f23b. Same imports as `Main.lean`.

When `4 ∣ d` (that is, `m ≢ 3 (mod 4)` and `d = 4m`), the level of `χ_{-d}` is even. Then the even-level bound
`‖L(1, χ)‖ ≤ (log d)/2 + 13/10` (`LOneEven.lean`) and Dirichlet's class number formula give the textbook constant
`1/(2π)`, up to the additive `13/5`. The odd case `d = m ≡ 3 (mod 4)` needs the Pólya–Vinogradov inequality. This is a
side result: the headline upper bound is the uniform `classNumber_le_sharp`.

* `classNumber_le_of_four_dvd_disc` (CN-1 form, `d = disc m`).
* `BoundariesOfClass.classNumber_le_of_four_dvd` (Mathlib form, `d = |disc K|`).
-/

set_option autoImplicit false

open NumberField CN1.Foundations

namespace BoundariesOfClass.ClassNumberFormula

variable {K : Type*} [Field K] [NumberField K]

/-- **`h ≤ (1/(2π)) √d (log d + 13/5)` when `4 ∣ d` and `d ≥ 12`**, CN-1 form. -/
theorem classNumber_le_of_four_dvd_disc {m : ℕ} {α : K} (hα : α ^ 2 = -(m : K)) (hK : Module.finrank ℚ K = 2)
    (hm : Squarefree m) (hd : 12 ≤ disc m) (h4 : 4 ∣ disc m) :
    (classNumber K : ℝ) ≤ Real.sqrt (disc m) * (Real.log (disc m) + 13 / 5) / (2 * Real.pi) := by
  have : NeZero (disc m) := ⟨by omega⟩
  obtain ⟨hm1, hm3⟩ := ne_one_and_ne_three_of_five_le (by omega : 5 ≤ disc m)
  have hB := norm_LFunction_one_le_of_even hd (dvd_trans (by norm_num) h4) (kroneckerChar m)
    (kroneckerChar_ne_one hm)
  rw [LFunction_kroneckerChar_one_eq hα hK hm hm1 hm3, Complex.norm_real] at hB
  have hd0 : (0 : ℝ) < disc m := by exact_mod_cast (by omega : 0 < disc m)
  have hsd : 0 < Real.sqrt (disc m) := Real.sqrt_pos.mpr hd0
  rw [Real.norm_of_nonneg (by positivity), div_le_iff₀ hsd] at hB
  rw [le_div_iff₀ (by positivity)]
  linarith

end BoundariesOfClass.ClassNumberFormula

namespace BoundariesOfClass

open BoundariesOfClass.ClassNumberFormula

/-- **`h ≤ (1/(2π)) √d (log d + 13/5)`** for `K = ℚ(√-m)` with `d = |disc K| ≥ 12` and `4 ∣ disc K`. -/
theorem classNumber_le_of_four_dvd (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hd : (12 : ℝ) ≤ |(discr K : ℝ)|) (h4 : (4 : ℤ) ∣ discr K) :
    (classNumber K : ℝ) ≤
      Real.sqrt |(discr K : ℝ)| * (Real.log |(discr K : ℝ)| + 13 / 5) / (2 * Real.pi) := by
  obtain ⟨α, hα⟩ := hsq
  have h4' : 4 ∣ disc m := by
    rw [discr_eq hα hK hm, dvd_neg] at h4
    exact_mod_cast h4
  rw [abs_discr_eq hα hK hm] at hd ⊢
  exact classNumber_le_of_four_dvd_disc hα hK hm (by exact_mod_cast hd) h4'

end BoundariesOfClass
