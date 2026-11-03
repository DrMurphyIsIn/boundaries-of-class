import Mathlib
import HCN.Numerics.Threshold

/-!
# BoundariesOfClass.Numerics.Uniform: the two uniform-in-`L` numeric inequalities

Pinned environment: Lean v4.34.1, Mathlib d13f23b. Pure real arithmetic; no `riemannZeta`, no `Gamma`. With
`L = log d ≥ 8` and `κ = e^{-3π/4}/(1 - e^{-3π/4})²`:

* `lower_numeric`: `(9/50) · π e (L - 1 + 4√2 κ) ≤ (13/8) (1 - π²/(2L²)) L`. This turns the analytic lower bound
  `h ≥ (13/8) cos(π/L) √d / (π e (L - 1 + 4√2 κ))` into `h ≥ (9/50) √d / L`. The margin at `L = 8`, the worst case, is 1.91%.
* `upper_numeric`: `(L + 1/2 + (1 + 1/L)(3 + 1/L)/8)² ≤ (6/5) L · (π(L+1)/e - 4√2 π (1 + 1/L)³ κ / √e)`, and the
  bracket on the right is positive. This turns the analytic upper bound into `h ≤ (6/5) √d L`.

The brackets: `π ∈ (3.141592, 3.141593)` and `e ∈ (2.7182818283, 2.7182818286)` (Mathlib), `√2 ≤ 1.41422`,
`√e ≥ 1.6487`, and `e^{-3π/4} ≤ 4767/50000` (HCN's `exp_neg_three_pi_div_four_le`), so
`κ ≤ κU = (4767/50000)/(1 - 4767/50000)²`.
-/

set_option autoImplicit false

namespace BoundariesOfClass.Numerics

open Real

/-- `κ = e^{-3π/4} / (1 - e^{-3π/4})²`, the worst remainder factor over the classes (`c ≥ 3π/4`). -/
noncomputable def kap : ℝ := Real.exp (-(3 * π / 4)) / (1 - Real.exp (-(3 * π / 4))) ^ 2

/-- The rational upper bracket for `κ`. -/
noncomputable def kapU : ℝ := (4767 / 50000) / (1 - 4767 / 50000) ^ 2

lemma kapU_eq : kapU = 4767 / 50000 / (45233 / 50000) ^ 2 := by unfold kapU; norm_num

/-- `x ↦ x/(1-x)²` is monotone on `[0, 1)`. -/
lemma div_one_sub_sq_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y < 1) :
    x / (1 - x) ^ 2 ≤ y / (1 - y) ^ 2 := by
  have h1 : 0 < 1 - y := by linarith
  have h2 : (1 - y) ^ 2 ≤ (1 - x) ^ 2 := by nlinarith
  calc x / (1 - x) ^ 2 ≤ y / (1 - x) ^ 2 := div_le_div_of_nonneg_right hxy (by positivity)
    _ ≤ y / (1 - y) ^ 2 := div_le_div_of_nonneg_left (by linarith) (by positivity) h2

lemma kap_nonneg : 0 ≤ kap := by
  unfold kap; positivity

lemma kap_le : kap ≤ kapU :=
  div_one_sub_sq_mono (Real.exp_pos _).le HCN.Numerics.exp_neg_three_pi_div_four_le (by norm_num)

lemma kapU_le : kapU ≤ 116495 / 1000000 := by rw [kapU_eq]; norm_num

lemma sqrt_two_le : Real.sqrt 2 ≤ 141422 / 100000 := by
  rw [Real.sqrt_le_left (by norm_num)]
  norm_num

lemma sqrt_exp_one_ge : (16487 / 10000 : ℝ) ≤ Real.sqrt (Real.exp 1) := by
  rw [Real.le_sqrt (by norm_num) (Real.exp_pos 1).le]
  have := Real.exp_one_gt_d9
  norm_num at this ⊢
  linarith

lemma pi_mul_e_le : π * Real.exp 1 ≤ 3141593 / 1000000 * (27182818286 / 10000000000) := by
  have h1 : π ≤ 3141593 / 1000000 := by have := Real.pi_lt_d6; norm_num at this; linarith
  have h2 : Real.exp 1 ≤ 27182818286 / 10000000000 := by
    have := Real.exp_one_lt_d9; norm_num at this; linarith
  exact mul_le_mul h1 h2 (Real.exp_pos 1).le (by norm_num)

/-- **The lower-bound numerics, uniform in `L ≥ 8`.** -/
theorem lower_numeric {L : ℝ} (hL : 8 ≤ L) :
    9 / 50 * (π * Real.exp 1 * (L - 1 + 4 * Real.sqrt 2 * kap)) ≤ 13 / 8 * (1 - π ^ 2 / (2 * L ^ 2)) * L := by
  have hL0 : 0 < L := by linarith
  have hS0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hSK : Real.sqrt 2 * kap ≤ 141422 / 100000 * (116495 / 1000000) :=
    mul_le_mul sqrt_two_le (kap_le.trans kapU_le) kap_nonneg (by norm_num)
  have hq0 : 0 ≤ L - 1 + 4 * Real.sqrt 2 * kap := by
    have := mul_nonneg hS0 kap_nonneg; nlinarith
  have hPE := pi_mul_e_le
  have hPE0 : 0 ≤ π * Real.exp 1 := by positivity
  have hP2 : π ^ 2 ≤ (3141593 / 1000000) ^ 2 := by
    have := Real.pi_lt_d6; norm_num at this
    exact pow_le_pow_left₀ Real.pi_pos.le this.le 2
  have hR : 13 / 8 * (1 - π ^ 2 / (2 * L ^ 2)) * L = (13 / 8 * L ^ 2 - 13 / 16 * π ^ 2) / L := by
    field_simp; ring
  rw [hR, le_div_iff₀ hL0]
  have step1 : π * Real.exp 1 * (L - 1 + 4 * Real.sqrt 2 * kap) ≤
      3141593 / 1000000 * (27182818286 / 10000000000) * (L - 1 + 4 * (141422 / 100000 * (116495 / 1000000))) := by
    calc π * Real.exp 1 * (L - 1 + 4 * Real.sqrt 2 * kap)
        ≤ 3141593 / 1000000 * (27182818286 / 10000000000) * (L - 1 + 4 * Real.sqrt 2 * kap) :=
          mul_le_mul_of_nonneg_right hPE hq0
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          nlinarith
  nlinarith [mul_le_mul_of_nonneg_right step1 hL0.le]

/-- The `(U)` per-class bracket is positive, uniformly in `L ≥ 8`, with its explicit lower bound. -/
theorem upper_bracket_ge {L : ℝ} (hL : 8 ≤ L) :
    1155727 / 1000000 * (L + 1) - 1788 / 1000 ≤
      π * (L + 1) / Real.exp 1 - 4 * Real.sqrt 2 * π * (1 + 1 / L) ^ 3 * kap / Real.sqrt (Real.exp 1) := by
  have hL0 : 0 < L := by linarith
  have ht : 1 / L ≤ 1 / 8 := one_div_le_one_div_of_le (by norm_num) hL
  have ht0 : 0 < 1 / L := by positivity
  have he0 := Real.exp_pos 1
  have hpe : (1155727 / 1000000 : ℝ) ≤ π / Real.exp 1 := by
    rw [le_div_iff₀ he0]
    have h1 := Real.pi_gt_d6
    have h2 := Real.exp_one_lt_d9
    norm_num at h1 h2 ⊢
    nlinarith
  have hmain : 1155727 / 1000000 * (L + 1) ≤ π * (L + 1) / Real.exp 1 := by
    rw [mul_div_right_comm]
    exact mul_le_mul_of_nonneg_right hpe (by linarith)
  have hcube : (1 + 1 / L) ^ 3 ≤ (9 / 8) ^ 3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
  have hS0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hse := sqrt_exp_one_ge
  have hP := Real.pi_lt_d6
  norm_num at hP
  have hnum : 4 * Real.sqrt 2 * π * (1 + 1 / L) ^ 3 * kap ≤
      4 * (141422 / 100000) * (3141593 / 1000000) * (9 / 8) ^ 3 * (116495 / 1000000) := by
    have hk := kap_le.trans kapU_le
    have hk0 := kap_nonneg
    have h1 : 4 * Real.sqrt 2 * π ≤ 4 * (141422 / 100000) * (3141593 / 1000000) :=
      mul_le_mul (by linarith [sqrt_two_le]) hP.le Real.pi_pos.le (by norm_num)
    have h2 := mul_le_mul h1 hcube (by positivity) (by norm_num)
    exact mul_le_mul h2 hk hk0 (by norm_num)
  have hrem : 4 * Real.sqrt 2 * π * (1 + 1 / L) ^ 3 * kap / Real.sqrt (Real.exp 1) ≤ 1788 / 1000 := by
    rw [div_le_iff₀ (by linarith)]
    calc 4 * Real.sqrt 2 * π * (1 + 1 / L) ^ 3 * kap
        ≤ 4 * (141422 / 100000) * (3141593 / 1000000) * (9 / 8) ^ 3 * (116495 / 1000000) := hnum
      _ ≤ 1788 / 1000 * (16487 / 10000) := by norm_num
      _ ≤ 1788 / 1000 * Real.sqrt (Real.exp 1) := mul_le_mul_of_nonneg_left hse (by norm_num)
  linarith

/-- **The upper-bound numerics, uniform in `L ≥ 8`.** -/
theorem upper_numeric {L : ℝ} (hL : 8 ≤ L) :
    (L + 1 / 2 + (1 + 1 / L) * (3 + 1 / L) / 8) ^ 2 ≤
      6 / 5 * L * (π * (L + 1) / Real.exp 1 -
        4 * Real.sqrt 2 * π * (1 + 1 / L) ^ 3 * kap / Real.sqrt (Real.exp 1)) := by
  have hL0 : 0 < L := by linarith
  have ht : 1 / L ≤ 1 / 8 := one_div_le_one_div_of_le (by norm_num) hL
  have ht0 : 0 < 1 / L := by positivity
  have hq : (1 + 1 / L) * (3 + 1 / L) / 8 ≤ 225 / 512 := by nlinarith
  have hq0 : 0 ≤ (1 + 1 / L) * (3 + 1 / L) / 8 := by positivity
  have hlhs : (L + 1 / 2 + (1 + 1 / L) * (3 + 1 / L) / 8) ^ 2 ≤ (L + 1 / 2 + 225 / 512) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hb := upper_bracket_ge hL
  have hrhs : 6 / 5 * L * (1155727 / 1000000 * (L + 1) - 1788 / 1000) ≤
      6 / 5 * L * (π * (L + 1) / Real.exp 1 -
        4 * Real.sqrt 2 * π * (1 + 1 / L) ^ 3 * kap / Real.sqrt (Real.exp 1)) :=
    mul_le_mul_of_nonneg_left hb (by positivity)
  nlinarith

/-- The `(U)` bracket is positive for `L ≥ 8`. -/
theorem upper_bracket_pos {L : ℝ} (hL : 8 ≤ L) :
    0 < π * (L + 1) / Real.exp 1 - 4 * Real.sqrt 2 * π * (1 + 1 / L) ^ 3 * kap / Real.sqrt (Real.exp 1) := by
  have := upper_bracket_ge hL
  nlinarith

end BoundariesOfClass.Numerics
