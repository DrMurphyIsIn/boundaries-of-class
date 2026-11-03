import BoundariesOfClass.Numerics.LprimeB
import BoundariesOfClass.Numerics.Thresholds
import BoundariesOfClass.Numerics.PowerBound
import BoundariesOfClass.Assembly.Cutoff

/-!
# BoundariesOfClass.Assembly.Version2: (L′), (P′), (B′), (B*) and (T) in CN-1's `dOf m` vocabulary

Pinned environment: Lean v4.34.1, Mathlib d13f23b.

* `classNumber_ge_third`: `(1/3) √d / log d ≤ h(K)` for `d ≥ 2981` (`log d ∈ [8, 16]`: `third_sqrt_div_log_le_A`, at
  `σ = 7/8`; `log d ≥ 16`: `third_sqrt_div_log_le_B`, at `σ = 1 - 2/log d`).
* `dOf_le_cutoff_v2`: if `h(K) ≤ h` (`h ≥ 1`) then `d ≤ max(2981, (A (log A + log(2 log A)))²)`, `A = 6h`, by the
  inversion `exp_le_of_exp_le_mul` with `√d ≤ 3 h log d = A · (log d)/2`.

* `dOf_le_cutoff_star`: if `h(K) ≤ h` then also `d ≤ max(1000, (17h)^{16/7})`, by inverting (P′)
  (`BoundariesOfClass.Numerics.rpow_le_classNumber`, `d ≥ 1000 ⇒ d^{7/16}/17 ≤ h(K)`).

The (T) thresholds are `BoundariesOfClass.Numerics.lt_classNumber_of_le_dOf_*`.
-/

set_option autoImplicit false

open NumberField CN1.Finite

namespace BoundariesOfClass.Assembly

/-- **(L′) in `dOf m` form.** -/
theorem classNumber_ge_third {K : Type*} [Field K] [NumberField K] {m : ℕ} {α : K} (hα : α ^ 2 = -(m : K))
    (hK : Module.finrank ℚ K = 2) (hm : Squarefree m) (hm1 : m ≠ 1) (hm3 : m ≠ 3)
    (hd : (2981 : ℝ) ≤ (dOf m : ℝ)) :
    1 / 3 * Real.sqrt (dOf m) / Real.log (dOf m) ≤ (classNumber K : ℝ) := by
  have h8 := eight_lt_log hd
  rcases le_or_gt (Real.log (dOf m)) 16 with h | h
  · exact BoundariesOfClass.Numerics.third_sqrt_div_log_le_A hα hK hm hm1 hm3 h8.le h
  · exact BoundariesOfClass.Numerics.third_sqrt_div_log_le_B hα hK hm hm1 hm3 h.le

/-- **(B′) in `dOf m` form.** -/
theorem dOf_le_cutoff_v2 {K : Type*} [Field K] [NumberField K] {m : ℕ} {α : K} (hα : α ^ 2 = -(m : K))
    (hK : Module.finrank ℚ K = 2) (hm : Squarefree m) (hm1 : m ≠ 1) (hm3 : m ≠ 3)
    (h : ℕ) (hh : 1 ≤ h) (hcl : classNumber K ≤ h) :
    (dOf m : ℝ) ≤ max 2981
      (((6 : ℝ) * h * (Real.log ((6 : ℝ) * h) + Real.log (2 * Real.log ((6 : ℝ) * h)))) ^ 2) := by
  rcases lt_or_ge (dOf m : ℝ) 2981 with hd | hd
  · exact le_max_of_le_left hd.le
  refine le_max_of_le_right ?_
  set D : ℝ := (dOf m : ℝ)
  set A : ℝ := (6 : ℝ) * h with hAdef
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hA : 1 < A := by rw [hAdef]; nlinarith
  have hL := classNumber_ge_third hα hK hm hm1 hm3 hd
  have hL8 : 8 < Real.log D := eight_lt_log hd
  have hlD : 0 < Real.log D := by linarith
  have hcl' : (classNumber K : ℝ) ≤ h := by exact_mod_cast hcl
  set t : ℝ := Real.log D / 2 with htdef
  have het : Real.exp t = Real.sqrt D := by rw [htdef, Real.exp_half, Real.exp_log (by linarith)]
  have hsD : 0 ≤ Real.sqrt D := Real.sqrt_nonneg D
  have hmain : Real.exp t ≤ A * t := by
    rw [het, htdef, hAdef]
    have h1 : 1 / 3 * Real.sqrt D / Real.log D ≤ h := hL.trans hcl'
    rw [div_le_iff₀ hlD] at h1
    nlinarith
  have hinv := exp_le_of_exp_le_mul hA hmain
  rw [het] at hinv
  have hD0 : 0 ≤ D := by linarith
  calc D = Real.sqrt D ^ 2 := (Real.sq_sqrt hD0).symm
    _ ≤ (A * (Real.log A + Real.log (2 * Real.log A))) ^ 2 := pow_le_pow_left₀ hsD hinv 2
    _ = _ := by rw [hAdef]

/-- **(B*) in `dOf m` form.** -/
theorem dOf_le_cutoff_star {K : Type*} [Field K] [NumberField K] {m : ℕ} {α : K} (hα : α ^ 2 = -(m : K))
    (hK : Module.finrank ℚ K = 2) (hm : Squarefree m) (hm1 : m ≠ 1) (hm3 : m ≠ 3)
    (h : ℕ) (hh : 1 ≤ h) (hcl : classNumber K ≤ h) :
    (dOf m : ℝ) ≤ min (max 1000 (((17 : ℝ) * h) ^ ((16 : ℝ) / 7)))
      (max 2981 (((6 : ℝ) * h * (Real.log ((6 : ℝ) * h) + Real.log (2 * Real.log ((6 : ℝ) * h)))) ^ 2)) := by
  refine le_min ?_ (dOf_le_cutoff_v2 hα hK hm hm1 hm3 h hh hcl)
  rcases lt_or_ge (dOf m : ℝ) 1000 with hd | hd
  · exact le_max_of_le_left hd.le
  refine le_max_of_le_right ?_
  have hD0 : (0 : ℝ) ≤ (dOf m : ℝ) := by linarith
  have hP := BoundariesOfClass.Numerics.rpow_le_classNumber hα hK hm hm1 hm3 hd
  have hcl' : (classNumber K : ℝ) ≤ h := by exact_mod_cast hcl
  have h1 : (dOf m : ℝ) ^ ((7 : ℝ) / 16) ≤ 17 * h := by linarith
  have h2 := Real.rpow_le_rpow (Real.rpow_nonneg hD0 _) h1 (by norm_num : (0 : ℝ) ≤ 16 / 7)
  rwa [← Real.rpow_mul hD0, show (7 : ℝ) / 16 * (16 / 7) = 1 by norm_num, Real.rpow_one] at h2

end BoundariesOfClass.Assembly
