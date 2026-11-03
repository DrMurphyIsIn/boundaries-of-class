import Mathlib

/-!
# BoundariesOfClass.Numerics.LprimeBNum: the rational inequality behind (L′) for `log d ≥ 16`

Pinned environment: Lean v4.34.1, Mathlib d13f23b. Mathlib only. With `t = 1/log d ∈ (0, 1/16]`, the class sum at
`σ = 1 - 2t` reduces (BoundariesOfClass.Numerics.LprimeB) to the rational inequality

  `3 (1 + (1/2)/(1 - 4t) + 1/8 - cP) ≥ (πₕ eₕ/2) T(t) (1 - 4t)/(1 - y(t)) + 4 πₕ eₕ κ t`,

where `T(t)` bounds `tan(2πt)/(2πt)`, `y(t) = 2t(ℓ - 2)/(1 - 4t)` with `ℓ = 2 + 47/64`, `κ = x²/(1-x)²` at
`x = (4767/50000)²`, `cP = 1/14`, and `πₕ = 3.141593`, `eₕ = 2.7182818286`. It is proved on the four pieces
`[0, 1/64]`, `[1/64, 1/32]`, `[1/32, 3/64]`, `[3/64, 1/16]` with monotone bounds on each factor (margins 6% to 20%;
numerics/LprimeB_check in the round notes).
-/

set_option autoImplicit false

namespace BoundariesOfClass.Numerics

/-- The upper bracket for `sin x/(x cos x)` at `x = 2πt`, with `π ∈ (3.141592, 3.141593)`. -/
noncomputable def TB (t : ℝ) : ℝ :=
  (1 - (2 * (3141592 / 1000000) * t) ^ 2 / 6 + (2 * (3141593 / 1000000) * t) ^ 4 / 100) /
    (1 - (2 * (3141593 / 1000000) * t) ^ 2 / 2)

/-- `y(t) = 2t(ℓ - 2)/(1 - 4t)`, `ℓ = 2 + 47/64`. -/
noncomputable def yB (t : ℝ) : ℝ := 2 * t * (47 / 64) / (1 - 4 * t)

/-- `κ` at `(4767/50000)²`. -/
noncomputable def kapB : ℝ := (4767 / 50000 : ℝ) ^ 2 / (1 - (4767 / 50000 : ℝ) ^ 2) ^ 2

lemma kapB_le : kapB ≤ 926 / 100000 := by unfold kapB; norm_num

lemma TB_le {t tb Tb : ℝ} (ht0 : 0 ≤ t) (htb : t ≤ tb) (htb1 : tb ≤ 1 / 16)
    (hTb : 1 - (2 * (3141592 / 1000000) * tb) ^ 2 / 6 + (2 * (3141593 / 1000000) * tb) ^ 4 / 100 ≤
      Tb * (1 - (2 * (3141593 / 1000000) * tb) ^ 2 / 2))
    (hTb1 : 1 ≤ Tb) : TB t ≤ Tb := by
  unfold TB
  have hden : 0 < 1 - (2 * (3141593 / 1000000) * t) ^ 2 / 2 := by nlinarith
  rw [div_le_iff₀ hden]
  -- `f(x) = 1 - a x/6 + b x²/100 - Tb (1 - c x/2)` is convex in `x = t²` and `≤ 0` at both ends
  set x := t ^ 2 with hx
  have hx0 : 0 ≤ x := sq_nonneg t
  have hxb : x ≤ tb ^ 2 := by rw [hx]; exact pow_le_pow_left₀ ht0 htb 2
  have hxb0 : 0 ≤ tb ^ 2 := sq_nonneg tb
  -- write everything in `x`; the function is `≤ 0` at `x = 0` (Tb ≥ 1) and at `x = tb²` (hTb), and convex
  have e1 : (2 * (3141592 / 1000000 : ℝ) * t) ^ 2 = (2 * (3141592 / 1000000)) ^ 2 * x := by rw [hx]; ring
  have e2 : (2 * (3141593 / 1000000 : ℝ) * t) ^ 4 = (2 * (3141593 / 1000000)) ^ 4 * x ^ 2 := by rw [hx]; ring
  have e3 : (2 * (3141593 / 1000000 : ℝ) * t) ^ 2 = (2 * (3141593 / 1000000)) ^ 2 * x := by rw [hx]; ring
  have f1 : (2 * (3141592 / 1000000 : ℝ) * tb) ^ 2 = (2 * (3141592 / 1000000)) ^ 2 * tb ^ 2 := by ring
  have f2 : (2 * (3141593 / 1000000 : ℝ) * tb) ^ 4 = (2 * (3141593 / 1000000)) ^ 4 * (tb ^ 2) ^ 2 := by ring
  have f3 : (2 * (3141593 / 1000000 : ℝ) * tb) ^ 2 = (2 * (3141593 / 1000000)) ^ 2 * tb ^ 2 := by ring
  rw [e1, e2, e3]
  rw [f1, f2, f3] at hTb
  -- convexity: `f(x) ≤ (1 - x/tb²) f(0) + (x/tb²) f(tb²)`, via `x² ≤ x · tb²`
  have hsq : x ^ 2 ≤ x * tb ^ 2 := by nlinarith
  nlinarith [hsq, hTb, hTb1, mul_nonneg hx0 (sub_nonneg.mpr hxb)]

lemma yB_mono {t tb : ℝ} (ht0 : 0 ≤ t) (htb : t ≤ tb) (htb1 : tb ≤ 1 / 16) : yB t ≤ yB tb := by
  unfold yB
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- **The rational inequality**, uniformly on `t ∈ (0, 1/16]`. -/
theorem lprimeB_numeric {t : ℝ} (ht0 : 0 < t) (ht : t ≤ 1 / 16) :
    3141593 / 1000000 * (27182818286 / 10000000000) / 2 * TB t * (1 - 4 * t) / (1 - yB t) +
        4 * (3141593 / 1000000) * (27182818286 / 10000000000) * kapB * t ≤
      3 * (1 + 1 / 2 / (1 - 4 * t) + 1 / 8 - 1 / 14) := by
  have hk := kapB_le
  have hk0 : 0 ≤ kapB := by unfold kapB; norm_num
  -- one piece `[ta, tb]`: monotone bounds, then a rational check
  have piece : ∀ ta tb Tb : ℝ, 0 ≤ ta → ta ≤ t → t ≤ tb → tb ≤ 1 / 16 →
      1 - (2 * (3141592 / 1000000) * tb) ^ 2 / 6 + (2 * (3141593 / 1000000) * tb) ^ 4 / 100 ≤
        Tb * (1 - (2 * (3141593 / 1000000) * tb) ^ 2 / 2) → 1 ≤ Tb →
      3141593 / 1000000 * (27182818286 / 10000000000) / 2 * Tb * (1 - 4 * ta) / (1 - yB tb) +
          4 * (3141593 / 1000000) * (27182818286 / 10000000000) * (926 / 100000) * tb ≤
        3 * (1 + 1 / 2 / (1 - 4 * ta) + 1 / 8 - 1 / 14) →
      3141593 / 1000000 * (27182818286 / 10000000000) / 2 * TB t * (1 - 4 * t) / (1 - yB t) +
          4 * (3141593 / 1000000) * (27182818286 / 10000000000) * kapB * t ≤
        3 * (1 + 1 / 2 / (1 - 4 * t) + 1 / 8 - 1 / 14) := by
    intro ta tb Tb hta htat httb htb hTb hTb1 hcheck
    have hT := TB_le (by linarith) httb htb hTb hTb1
    have hT0 : 0 ≤ TB t := by
      unfold TB
      apply div_nonneg _ (by nlinarith)
      nlinarith [sq_nonneg t, pow_two_nonneg (t ^ 2)]
    have hy := yB_mono (by linarith) httb htb
    have hyb : yB tb < 1 := by unfold yB; rw [div_lt_one (by linarith)]; nlinarith
    have hy0 : 0 ≤ yB t := by unfold yB; apply div_nonneg (by positivity) (by linarith)
    have h1 : 1 - yB tb ≤ 1 - yB t := by linarith
    have h2 : 0 < 1 - yB tb := by linarith
    -- LHS ≤ the piece's LHS
    have hA : 3141593 / 1000000 * (27182818286 / 10000000000) / 2 * TB t * (1 - 4 * t) / (1 - yB t) ≤
        3141593 / 1000000 * (27182818286 / 10000000000) / 2 * Tb * (1 - 4 * ta) / (1 - yB tb) := by
      have h4a : 0 ≤ 1 - 4 * ta := by linarith
      have h4t : 0 ≤ 1 - 4 * t := by linarith
      apply div_le_div₀ (by positivity) _ h2 h1
      apply mul_le_mul (mul_le_mul_of_nonneg_left hT (by norm_num)) (by linarith) h4t (by positivity)
    have hB : 4 * (3141593 / 1000000) * (27182818286 / 10000000000) * kapB * t ≤
        4 * (3141593 / 1000000) * (27182818286 / 10000000000) * (926 / 100000) * tb := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left hk (by norm_num)) httb ht0.le (by positivity)
    have hC : 1 / 2 / (1 - 4 * ta) ≤ 1 / 2 / (1 - 4 * t) :=
      div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
    linarith
  rcases le_or_gt t (1 / 64) with h1 | h1
  · exact piece 0 (1 / 64) (10035 / 10000) le_rfl ht0.le h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num [yB])
  rcases le_or_gt t (1 / 32) with h2 | h2
  · exact piece (1 / 64) (1 / 32) (10135 / 10000) (by norm_num) h1.le h2 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [yB])
  rcases le_or_gt t (3 / 64) with h3 | h3
  · exact piece (1 / 32) (3 / 64) (10310 / 10000) (by norm_num) h2.le h3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [yB])
  exact piece (3 / 64) (1 / 16) (10570 / 10000) (by norm_num) h3.le ht (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [yB])

end BoundariesOfClass.Numerics
