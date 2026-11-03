import HCN.Statements.ClassPartition

/-!
# BoundariesOfClass.Assembly.Common: small shared facts for the two class-sum assemblies

`dOf_pos`, `eight_lt_log` (`e⁸ < 2981`), `rpow_inv_log` (`D^{1/log D} = e`). The class representatives are taken
from the unconditional `HCN.Epstein.exists_classReps`, `IsHermite.one_le_formA` and `IsHermite.formA_le_absNorm`
(HCN/Statements/ClassPartition.lean); no interface structure (`EFacts`, `CSFacts`) is used.
-/

set_option autoImplicit false

open NumberField CN1.Finite HCN.Epstein

namespace BoundariesOfClass.Assembly

lemma dOf_pos {m : ℕ} (hm : Squarefree m) : (0 : ℝ) < (dOf m : ℝ) := by
  have h1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm.ne_zero
  have := le_dOf m
  exact_mod_cast (by omega : 0 < dOf m)

/-- `e⁸ < 2981`, so `log d > 8` for `d ≥ 2981`. -/
lemma eight_lt_log {D : ℝ} (hd : 2981 ≤ D) : 8 < Real.log D := by
  rw [Real.lt_log_iff_exp_lt (by linarith), show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, ← Real.exp_one_pow]
  have h := Real.exp_one_lt_d9
  have h0 := Real.exp_pos 1
  calc Real.exp 1 ^ 8 < (2.7182818286 : ℝ) ^ 8 := pow_lt_pow_left₀ h h0.le (by norm_num)
    _ < 2981 := by norm_num
    _ ≤ D := hd

/-- `D^{1/log D} = e`. -/
lemma rpow_inv_log {D : ℝ} (hD : 1 < D) : D ^ (1 / Real.log D) = Real.exp 1 := by
  rw [Real.rpow_def_of_pos (by linarith), mul_one_div_cancel (Real.log_pos hD).ne']


/-- `D^{c/log D} = e^c`: the choice `δ = c/log d` keeps `d^δ` exact for any rational `c`. -/
lemma rpow_div_log {D : ℝ} (hD : 1 < D) (c : ℝ) : D ^ (c / Real.log D) = Real.exp c := by
  rw [Real.rpow_def_of_pos (by linarith), mul_div_cancel₀ c (Real.log_pos hD).ne']

end BoundariesOfClass.Assembly
