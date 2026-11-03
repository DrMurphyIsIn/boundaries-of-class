import BoundariesOfClass.Assembly.Lower

/-!
# BoundariesOfClass.Assembly.Cutoff: the class number boundary `d ≤ D(h)`, in CN-1's `dOf m` vocabulary

Pinned environment: Lean v4.34.1, Mathlib d13f23b.

* `exp_le_of_exp_le_mul` (real analysis, no number theory): if `A > 1` and `e^t ≤ A t`, then
  `e^t ≤ A (log A + log(2 log A))`. First `t ≤ 2 log A` (else `e^{t/2} > A` and `e^t > A e^{t/2} ≥ A t`, using
  `e^{t/2} ≥ 1 + t/2 + t²/8 ≥ t`); then `t ≤ log(A t) = log A + log t ≤ log A + log(2 log A)`.
* `dOf_le_cutoff`: if `h(K) ≤ h` (`h ≥ 1`) then `dOf m ≤ max(2981, (A (log A + log(2 log A)))²)`, `A = (100/9) h`,
  from (L) with `t = (log d)/2`, `e^t = √d`, `√d ≤ (50/9) h log d = A t`.

-/

set_option autoImplicit false

open NumberField CN1.Finite

namespace BoundariesOfClass.Assembly

/-- `e^{t/2} ≥ t` for all real `t`. -/
lemma le_exp_half (t : ℝ) : t ≤ Real.exp (t / 2) := by
  rcases le_or_gt t 0 with h | h
  · exact h.trans (Real.exp_pos _).le
  · have := Real.quadratic_le_exp_of_nonneg (x := t / 2) (by linarith)
    nlinarith [sq_nonneg (t - 4)]

/-- **The inversion:** `A > 1`, `e^t ≤ A t` ⟹ `e^t ≤ A (log A + log(2 log A))`. -/
theorem exp_le_of_exp_le_mul {A t : ℝ} (hA : 1 < A) (h : Real.exp t ≤ A * t) :
    Real.exp t ≤ A * (Real.log A + Real.log (2 * Real.log A)) := by
  have hA0 : 0 < A := by linarith
  have hlA : 0 < Real.log A := Real.log_pos hA
  have ht : 0 < t := by
    by_contra hc; push Not at hc
    have := Real.exp_pos t
    nlinarith
  have ht2 : t ≤ 2 * Real.log A := by
    by_contra hc; push Not at hc
    have h1 : A < Real.exp (t / 2) := by
      rw [← Real.exp_log hA0]; exact Real.exp_lt_exp.mpr (by linarith)
    have h2 : Real.exp t = Real.exp (t / 2) * Real.exp (t / 2) := by rw [← Real.exp_add]; ring_nf
    have h3 := le_exp_half t
    have : A * t < Real.exp t := by
      rw [h2]
      calc A * t ≤ A * Real.exp (t / 2) := mul_le_mul_of_nonneg_left h3 hA0.le
        _ < Real.exp (t / 2) * Real.exp (t / 2) := mul_lt_mul_of_pos_right h1 (Real.exp_pos _)
    linarith
  have hlog : t ≤ Real.log A + Real.log t := by
    rw [← Real.log_mul hA0.ne' ht.ne', ← Real.log_exp t]
    exact Real.log_le_log (Real.exp_pos _) (by rw [Real.log_exp]; exact h)
  have hlt : Real.log t ≤ Real.log (2 * Real.log A) := Real.log_le_log ht ht2
  calc Real.exp t ≤ A * t := h
    _ ≤ A * (Real.log A + Real.log (2 * Real.log A)) := mul_le_mul_of_nonneg_left (by linarith) hA0.le

/-- **(B) in `dOf m` form.** -/
theorem dOf_le_cutoff {K : Type*} [Field K] [NumberField K] {m : ℕ} {α : K} (hα : α ^ 2 = -(m : K))
    (hK : Module.finrank ℚ K = 2) (hm : Squarefree m) (hm1 : m ≠ 1) (hm3 : m ≠ 3)
    (h : ℕ) (hh : 1 ≤ h) (hcl : classNumber K ≤ h) :
    (dOf m : ℝ) ≤ max 2981
      (((100 / 9 : ℝ) * h * (Real.log ((100 / 9 : ℝ) * h) + Real.log (2 * Real.log ((100 / 9 : ℝ) * h)))) ^ 2) := by
  rcases lt_or_ge (dOf m : ℝ) 2981 with hd | hd
  · exact le_max_of_le_left hd.le
  refine le_max_of_le_right ?_
  set D : ℝ := (dOf m : ℝ)
  set A : ℝ := (100 / 9 : ℝ) * h with hAdef
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hA : 1 < A := by rw [hAdef]; nlinarith
  have hL := classNumber_ge hα hK hm hm1 hm3 hd
  have hL8 : 8 < Real.log D := eight_lt_log hd
  have hlD : 0 < Real.log D := by linarith
  have hcl' : (classNumber K : ℝ) ≤ h := by exact_mod_cast hcl
  set t : ℝ := Real.log D / 2 with htdef
  have het : Real.exp t = Real.sqrt D := by rw [htdef, Real.exp_half, Real.exp_log (by linarith)]
  have hsD : 0 ≤ Real.sqrt D := Real.sqrt_nonneg D
  -- `√d ≤ (50/9) h log d = A t`
  have hmain : Real.exp t ≤ A * t := by
    rw [het, htdef, hAdef]
    have h1 : 9 / 50 * Real.sqrt D / Real.log D ≤ h := hL.trans hcl'
    rw [div_le_iff₀ hlD] at h1
    nlinarith
  have hinv := exp_le_of_exp_le_mul hA hmain
  rw [het] at hinv
  have hD0 : 0 ≤ D := by linarith
  calc D = Real.sqrt D ^ 2 := (Real.sq_sqrt hD0).symm
    _ ≤ (A * (Real.log A + Real.log (2 * Real.log A))) ^ 2 := pow_le_pow_left₀ hsD hinv 2
    _ = _ := by rw [hAdef]

end BoundariesOfClass.Assembly
