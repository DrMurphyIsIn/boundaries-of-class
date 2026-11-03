import Mathlib

/-!
# BoundariesOfClass.Analytic.GammaNearOne: the Γ-ratio brackets near `σ = 1`

Pinned environment: Lean v4.34.1, Mathlib d13f23b. Mathlib only. The Chowla–Selberg coefficient of `ζ(2σ - 1)` carries
`G(σ) = Γ(σ - 1/2)/Γ(σ)`; at `σ = 1 ∓ δ` we need it to `O(δ²)`, not just to a constant.

* `Gamma_sq_le_Gamma_two_mul_add_one`: log-convexity gives `Γ(1+δ)² ≤ Γ(1) Γ(1+2δ) = Γ(1+2δ)`.
* `Gamma_one_sub_two_mul_cos_le`: `Γ(1-2δ) cos(πδ) ≤ Γ(1-δ)²` for `0 < δ < 1/2`. By reflection,
  `Γ(1-2δ)/Γ(1-δ)² = sin(πδ) Γ(1+δ)² / (πδ cos(πδ) Γ(1+2δ))`; then `sin x ≤ x` and log-convexity.
* `Gamma_ratio_le`: `Γ(1/2-δ)/Γ(1-δ) ≤ 4^δ √π / cos(πδ)` (Legendre duplication at `s = 1/2 - δ`), the lower route.
* `Gamma_one_sub_two_mul_le_tan`, `Gamma_ratio_le_tan`: the same with `sin(πδ)/(πδ)` kept (only log-convexity
  is lost), and `sin_div_mul_cos_le`, an elementary bracket for `tan x/x`.
* `Gamma_ratio_plus_ge`: `4^{-δ} √π ≤ Γ(1/2+δ)/Γ(1+δ)` (duplication at `s = 1/2 + δ` and log-convexity), the upper
  route's main term.
* `Gamma_ratio_plus_le`: `Γ(1/2+δ)/Γ(1+δ) ≤ 4^{-δ} √π (1+δ)²` for `0 < δ ≤ 1/2` (`Γ ≤ 1` on `[1, 2]`, `Γ ≥ 1` on
  `[2, ∞)`, both by convexity with `Γ(1) = Γ(2) = 1`), the upper route's remainder.

Numerical check (mpmath): the identities hold to `10⁻³⁵`. `Gamma_ratio_le` loses a factor `1 + O(δ²)`: about `3·10⁻⁶`
at `δ = 0.001` and `4.65%` at `δ = 1/8`.
-/

set_option autoImplicit false

namespace BoundariesOfClass.Analytic

open Real

/-- Log-convexity at the midpoint of `1` and `1 + 2δ`: `Γ(1+δ)² ≤ Γ(1+2δ)`. -/
theorem Gamma_sq_le_Gamma_two_mul_add_one {δ : ℝ} (hδ : 0 ≤ δ) :
    Real.Gamma (δ + 1) ^ 2 ≤ Real.Gamma (2 * δ + 1) := by
  have hG1 : 0 < Real.Gamma (δ + 1) := Real.Gamma_pos_of_pos (by linarith)
  have hG2 : 0 < Real.Gamma (2 * δ + 1) := Real.Gamma_pos_of_pos (by linarith)
  have h := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma (s := 1) (t := 2 * δ + 1)
    (a := 1 / 2) (b := 1 / 2) one_pos (by linarith) (by norm_num) (by norm_num) (by norm_num)
  rw [show (1 / 2 : ℝ) * 1 + 1 / 2 * (2 * δ + 1) = δ + 1 by ring, Real.Gamma_one, Real.one_rpow,
    one_mul] at h
  calc Real.Gamma (δ + 1) ^ 2 ≤ (Real.Gamma (2 * δ + 1) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ hG1.le h 2
    _ = Real.Gamma (2 * δ + 1) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hG2.le]; norm_num

/-- **`Γ(1-2δ) cos(πδ) ≤ Γ(1-δ)²`** for `0 < δ < 1/2`. -/
theorem Gamma_one_sub_two_mul_cos_le {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ < 1 / 2) :
    Real.Gamma (1 - 2 * δ) * Real.cos (π * δ) ≤ Real.Gamma (1 - δ) ^ 2 := by
  have hpd : 0 < π * δ := by positivity
  have hpd2 : π * δ < π / 2 := by nlinarith [Real.pi_pos]
  have hsin : 0 < Real.sin (π * δ) := Real.sin_pos_of_pos_of_lt_pi hpd (by linarith)
  have hcos : 0 < Real.cos (π * δ) := Real.cos_pos_of_mem_Ioo ⟨by linarith, hpd2⟩
  have hsin2 : 0 < Real.sin (π * (2 * δ)) := by
    rw [show π * (2 * δ) = 2 * (π * δ) by ring, Real.sin_two_mul]; positivity
  have r1 := Real.Gamma_mul_Gamma_one_sub δ
  have r2 := Real.Gamma_mul_Gamma_one_sub (2 * δ)
  have g1 : Real.Gamma (δ + 1) = δ * Real.Gamma δ := Real.Gamma_add_one hδ.ne'
  have g2 : Real.Gamma (2 * δ + 1) = 2 * δ * Real.Gamma (2 * δ) := Real.Gamma_add_one (by positivity)
  have hGd : 0 < Real.Gamma δ := Real.Gamma_pos_of_pos hδ
  have hG2d : 0 < Real.Gamma (2 * δ) := Real.Gamma_pos_of_pos (by linarith)
  have hconv := Gamma_sq_le_Gamma_two_mul_add_one hδ.le
  have hsinle : Real.sin (π * δ) ≤ π * δ := Real.sin_le hpd.le
  have e1 : Real.Gamma (1 - δ) = π / (Real.sin (π * δ) * Real.Gamma δ) := by
    rw [eq_div_iff (by positivity), show Real.Gamma (1 - δ) * (Real.sin (π * δ) * Real.Gamma δ) =
      Real.sin (π * δ) * (Real.Gamma δ * Real.Gamma (1 - δ)) by ring, r1]
    field_simp
  have e2 : Real.Gamma (1 - 2 * δ) = π / (Real.sin (π * (2 * δ)) * Real.Gamma (2 * δ)) := by
    rw [eq_div_iff (by positivity), show Real.Gamma (1 - 2 * δ) * (Real.sin (π * (2 * δ)) * Real.Gamma (2 * δ)) =
      Real.sin (π * (2 * δ)) * (Real.Gamma (2 * δ) * Real.Gamma (1 - 2 * δ)) by ring, r2, mul_comm]
    exact div_mul_cancel₀ π hsin2.ne'
  rw [e1, e2, show π * (2 * δ) = 2 * (π * δ) by ring, Real.sin_two_mul]
  rw [g1, g2] at hconv
  rw [div_mul_eq_mul_div, div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  have key : Real.sin (π * δ) * Real.Gamma δ ^ 2 ≤ π * (2 * Real.Gamma (2 * δ)) := by
    have h1 : δ ^ 2 * Real.Gamma δ ^ 2 ≤ 2 * δ * Real.Gamma (2 * δ) := by nlinarith [hconv]
    have h2 : δ * Real.Gamma δ ^ 2 ≤ 2 * Real.Gamma (2 * δ) := by
      have := h1; nlinarith [hδ]
    calc Real.sin (π * δ) * Real.Gamma δ ^ 2 ≤ π * δ * Real.Gamma δ ^ 2 :=
          mul_le_mul_of_nonneg_right hsinle (by positivity)
      _ = π * (δ * Real.Gamma δ ^ 2) := by ring
      _ ≤ π * (2 * Real.Gamma (2 * δ)) := mul_le_mul_of_nonneg_left h2 Real.pi_pos.le
  have hpi := Real.pi_pos
  nlinarith [key, mul_pos hsin hcos, mul_pos hpi hsin, mul_pos (mul_pos hpi hsin) hcos]

/-- `cos(πδ) > 0` for `0 < δ < 1/2`. -/
lemma cos_pi_mul_pos {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ < 1 / 2) : 0 < Real.cos (π * δ) :=
  Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩

/-- **The lower route's bracket:** `Γ(1/2-δ)/Γ(1-δ) ≤ 4^δ √π / cos(πδ)` for `0 < δ < 1/2`. -/
theorem Gamma_ratio_le {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ < 1 / 2) :
    Real.Gamma (1 / 2 - δ) / Real.Gamma (1 - δ) ≤ (4 : ℝ) ^ δ * Real.sqrt π / Real.cos (π * δ) := by
  have hcos := cos_pi_mul_pos hδ hδ2
  have hG : 0 < Real.Gamma (1 - δ) := Real.Gamma_pos_of_pos (by linarith)
  have hdup := Real.Gamma_mul_Gamma_add_half (1 / 2 - δ)
  rw [show (1 / 2 - δ) + 1 / 2 = 1 - δ by ring, show 2 * (1 / 2 - δ) = 1 - 2 * δ by ring,
    show (1 : ℝ) - (1 - 2 * δ) = 2 * δ by ring] at hdup
  have h4 : (2 : ℝ) ^ (2 * δ) = (4 : ℝ) ^ δ := by
    rw [Real.rpow_mul (by norm_num)]; norm_num
  have hc := Gamma_one_sub_two_mul_cos_le hδ hδ2
  rw [div_le_div_iff₀ hG hcos]
  have e : Real.Gamma (1 / 2 - δ) = Real.Gamma (1 - 2 * δ) * (4 : ℝ) ^ δ * Real.sqrt π / Real.Gamma (1 - δ) := by
    rw [eq_div_iff hG.ne', hdup, h4]
  rw [e, div_mul_eq_mul_div, div_le_iff₀ hG]
  have hs : 0 ≤ (4 : ℝ) ^ δ * Real.sqrt π := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hc hs]

/-- Duplication at `s = 1/2 + δ`: `Γ(1/2+δ)/Γ(1+δ) = 4^{-δ} √π Γ(1+2δ) / Γ(1+δ)²`. -/
lemma Gamma_ratio_plus_eq {δ : ℝ} (hδ : 0 ≤ δ) :
    Real.Gamma (1 / 2 + δ) / Real.Gamma (1 + δ) =
      (4 : ℝ) ^ (-δ) * Real.sqrt π * Real.Gamma (2 * δ + 1) / Real.Gamma (δ + 1) ^ 2 := by
  have hG : 0 < Real.Gamma (1 + δ) := Real.Gamma_pos_of_pos (by linarith)
  have hdup := Real.Gamma_mul_Gamma_add_half (1 / 2 + δ)
  rw [show (1 / 2 + δ) + 1 / 2 = 1 + δ by ring, show 2 * (1 / 2 + δ) = 2 * δ + 1 by ring,
    show (1 : ℝ) - (2 * δ + 1) = -(2 * δ) by ring] at hdup
  have h4 : (2 : ℝ) ^ (-(2 * δ)) = (4 : ℝ) ^ (-δ) := by
    rw [show -(2 * δ) = 2 * (-δ) by ring, Real.rpow_mul (by norm_num)]; norm_num
  rw [h4] at hdup
  rw [show δ + 1 = 1 + δ by ring, div_eq_div_iff hG.ne' (by positivity), sq, ← mul_assoc, hdup]
  ring

/-- **The upper route's main-term bracket:** `4^{-δ} √π ≤ Γ(1/2+δ)/Γ(1+δ)` for `δ ≥ 0`. -/
theorem Gamma_ratio_plus_ge {δ : ℝ} (hδ : 0 ≤ δ) :
    (4 : ℝ) ^ (-δ) * Real.sqrt π ≤ Real.Gamma (1 / 2 + δ) / Real.Gamma (1 + δ) := by
  rw [Gamma_ratio_plus_eq hδ]
  have hG1 : 0 < Real.Gamma (δ + 1) := Real.Gamma_pos_of_pos (by linarith)
  have hc := Gamma_sq_le_Gamma_two_mul_add_one hδ
  rw [le_div_iff₀ (by positivity)]
  have : 0 ≤ (4 : ℝ) ^ (-δ) * Real.sqrt π := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hc this]

/-- `Γ ≤ 1` on `[1, 2]` (convexity, `Γ(1) = Γ(2) = 1`). -/
lemma Gamma_le_one_of_mem_Icc {x : ℝ} (h1 : 1 ≤ x) (h2 : x ≤ 2) : Real.Gamma x ≤ 1 := by
  have h := Real.convexOn_Gamma.le_on_segment (x := 1) (y := 2) (z := x) (by norm_num [Set.mem_Ioi])
    (by norm_num [Set.mem_Ioi]) (by rw [segment_eq_Icc (by norm_num)]; exact ⟨h1, h2⟩)
  rw [Real.Gamma_one, Real.Gamma_two, max_self] at h
  exact h

/-- `Γ ≥ 1` on `[2, ∞)` (convexity through `Γ(1) = Γ(2) = 1`). -/
lemma one_le_Gamma_of_two_le {x : ℝ} (hx : 2 ≤ x) : 1 ≤ Real.Gamma x := by
  rcases eq_or_lt_of_le hx with h | h
  · rw [← h, Real.Gamma_two]
  have hx1 : 0 < x - 1 := by linarith
  have ha0 : (0 : ℝ) ≤ (x - 2) / (x - 1) := div_nonneg (by linarith) hx1.le
  have hb0 : (0 : ℝ) ≤ 1 / (x - 1) := by positivity
  have hab : (x - 2) / (x - 1) + 1 / (x - 1) = 1 := by
    have : (x - 2) / (x - 1) + 1 / (x - 1) = (x - 2 + 1) / (x - 1) := by ring
    rw [this, div_eq_one_iff_eq hx1.ne']; ring
  have hm1 : (1 : ℝ) ∈ Set.Ioi 0 := by norm_num [Set.mem_Ioi]
  have hmx : x ∈ Set.Ioi (0 : ℝ) := by simp only [Set.mem_Ioi]; linarith
  have hc := Real.convexOn_Gamma.2 hm1 hmx ha0 hb0 hab
  simp only [smul_eq_mul] at hc
  have e : (x - 2) / (x - 1) * 1 + 1 / (x - 1) * x = 2 := by
    have : (x - 2) / (x - 1) * 1 + 1 / (x - 1) * x = (x - 2 + x) / (x - 1) := by ring
    rw [this, div_eq_iff hx1.ne']; ring
  rw [e, Real.Gamma_one, Real.Gamma_two] at hc
  have h' := mul_le_mul_of_nonneg_left hc hx1.le
  have e2 : (x - 1) * ((x - 2) / (x - 1) * 1 + 1 / (x - 1) * Real.Gamma x) = (x - 2) + Real.Gamma x := by
    field_simp
  rw [e2, mul_one] at h'
  linarith

/-- **The upper route's remainder bracket:** `Γ(1/2+δ)/Γ(1+δ) ≤ 4^{-δ} √π (1+δ)²` for `0 ≤ δ ≤ 1/2`. -/
theorem Gamma_ratio_plus_le {δ : ℝ} (hδ : 0 ≤ δ) (hδ2 : δ ≤ 1 / 2) :
    Real.Gamma (1 / 2 + δ) / Real.Gamma (1 + δ) ≤ (4 : ℝ) ^ (-δ) * Real.sqrt π * (1 + δ) ^ 2 := by
  rw [Gamma_ratio_plus_eq hδ]
  have hG1 : 0 < Real.Gamma (δ + 1) := Real.Gamma_pos_of_pos (by linarith)
  have hup : Real.Gamma (2 * δ + 1) ≤ 1 := Gamma_le_one_of_mem_Icc (by linarith) (by linarith)
  -- `Γ(1+δ) = Γ(2+δ)/(1+δ) ≥ 1/(1+δ)`
  have hlo : 1 ≤ Real.Gamma (δ + 1) * (1 + δ) := by
    have h := Real.Gamma_add_one (s := δ + 1) (by linarith)
    rw [show δ + 1 + 1 = δ + 2 by ring] at h
    have h2 := one_le_Gamma_of_two_le (x := δ + 2) (by linarith)
    rw [h] at h2
    linarith
  have hk : 0 ≤ (4 : ℝ) ^ (-δ) * Real.sqrt π := by positivity
  rw [div_le_iff₀ (by positivity)]
  have hsq : 1 ≤ Real.Gamma (δ + 1) ^ 2 * (1 + δ) ^ 2 := by
    have := pow_le_pow_left₀ zero_le_one hlo 2
    rw [one_pow, mul_pow] at this
    exact this
  calc (4 : ℝ) ^ (-δ) * Real.sqrt π * Real.Gamma (2 * δ + 1) ≤ (4 : ℝ) ^ (-δ) * Real.sqrt π * 1 :=
        mul_le_mul_of_nonneg_left hup hk
    _ ≤ (4 : ℝ) ^ (-δ) * Real.sqrt π * (Real.Gamma (δ + 1) ^ 2 * (1 + δ) ^ 2) :=
        mul_le_mul_of_nonneg_left hsq hk
    _ = (4 : ℝ) ^ (-δ) * Real.sqrt π * (1 + δ) ^ 2 * Real.Gamma (δ + 1) ^ 2 := by ring

/-- **The reflection bracket in its sharp form:** `Γ(1-2δ) · πδ cos(πδ) ≤ Γ(1-δ)² · sin(πδ)` for `0 < δ < 1/2`, i.e.
`Γ(1-2δ)/Γ(1-δ)² ≤ tan(πδ)/(πδ)`. Only log-convexity is lost (`sin x ≤ x` is not used). -/
theorem Gamma_one_sub_two_mul_le_tan {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ < 1 / 2) :
    Real.Gamma (1 - 2 * δ) * (π * δ * Real.cos (π * δ)) ≤ Real.Gamma (1 - δ) ^ 2 * Real.sin (π * δ) := by
  have hpd : 0 < π * δ := by positivity
  have hpd2 : π * δ < π / 2 := by nlinarith [Real.pi_pos]
  have hsin : 0 < Real.sin (π * δ) := Real.sin_pos_of_pos_of_lt_pi hpd (by linarith)
  have hcos : 0 < Real.cos (π * δ) := Real.cos_pos_of_mem_Ioo ⟨by linarith, hpd2⟩
  have hsin2 : 0 < Real.sin (π * (2 * δ)) := by
    rw [show π * (2 * δ) = 2 * (π * δ) by ring, Real.sin_two_mul]; positivity
  have r1 := Real.Gamma_mul_Gamma_one_sub δ
  have r2 := Real.Gamma_mul_Gamma_one_sub (2 * δ)
  have g1 : Real.Gamma (δ + 1) = δ * Real.Gamma δ := Real.Gamma_add_one hδ.ne'
  have g2 : Real.Gamma (2 * δ + 1) = 2 * δ * Real.Gamma (2 * δ) := Real.Gamma_add_one (by positivity)
  have hGd : 0 < Real.Gamma δ := Real.Gamma_pos_of_pos hδ
  have hG2d : 0 < Real.Gamma (2 * δ) := Real.Gamma_pos_of_pos (by linarith)
  have hconv := Gamma_sq_le_Gamma_two_mul_add_one hδ.le
  rw [g1, g2] at hconv
  have h2 : δ * Real.Gamma δ ^ 2 ≤ 2 * Real.Gamma (2 * δ) := by nlinarith
  have e1 : Real.Gamma (1 - δ) = π / (Real.sin (π * δ) * Real.Gamma δ) := by
    rw [eq_div_iff (by positivity), show Real.Gamma (1 - δ) * (Real.sin (π * δ) * Real.Gamma δ) =
      Real.sin (π * δ) * (Real.Gamma δ * Real.Gamma (1 - δ)) by ring, r1]
    field_simp
  have e2 : Real.Gamma (1 - 2 * δ) = π / (Real.sin (π * (2 * δ)) * Real.Gamma (2 * δ)) := by
    rw [eq_div_iff (by positivity), show Real.Gamma (1 - 2 * δ) * (Real.sin (π * (2 * δ)) * Real.Gamma (2 * δ)) =
      Real.sin (π * (2 * δ)) * (Real.Gamma (2 * δ) * Real.Gamma (1 - 2 * δ)) by ring, r2, mul_comm]
    exact div_mul_cancel₀ π hsin2.ne'
  rw [e1, e2, show π * (2 * δ) = 2 * (π * δ) by ring, Real.sin_two_mul]
  -- `π/(2 s c Γ(2δ)) · πδ c ≤ π²/(s² Γ(δ)²) · s`, i.e. `δ Γ(δ)² ≤ 2 Γ(2δ)`
  have hpi := Real.pi_pos
  rw [div_pow, mul_pow, div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have key : π * (π * δ * Real.cos (π * δ)) * (Real.sin (π * δ) ^ 2 * Real.Gamma δ ^ 2) ≤
      π ^ 2 * Real.sin (π * δ) * (2 * Real.sin (π * δ) * Real.cos (π * δ) * Real.Gamma (2 * δ)) := by
    have hk : 0 ≤ π ^ 2 * Real.sin (π * δ) ^ 2 * Real.cos (π * δ) := by positivity
    have := mul_le_mul_of_nonneg_left h2 hk
    nlinarith
  linarith

/-- **The lower route's sharp bracket:** `Γ(1/2-δ)/Γ(1-δ) ≤ 4^δ √π · sin(πδ)/(πδ cos(πδ))` for `0 < δ < 1/2`. -/
theorem Gamma_ratio_le_tan {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ < 1 / 2) :
    Real.Gamma (1 / 2 - δ) / Real.Gamma (1 - δ) ≤
      (4 : ℝ) ^ δ * Real.sqrt π * Real.sin (π * δ) / (π * δ * Real.cos (π * δ)) := by
  have hcos := cos_pi_mul_pos hδ hδ2
  have hpd : 0 < π * δ := by positivity
  have hG : 0 < Real.Gamma (1 - δ) := Real.Gamma_pos_of_pos (by linarith)
  have hdup := Real.Gamma_mul_Gamma_add_half (1 / 2 - δ)
  rw [show (1 / 2 - δ) + 1 / 2 = 1 - δ by ring, show 2 * (1 / 2 - δ) = 1 - 2 * δ by ring,
    show (1 : ℝ) - (1 - 2 * δ) = 2 * δ by ring] at hdup
  have h4 : (2 : ℝ) ^ (2 * δ) = (4 : ℝ) ^ δ := by
    rw [Real.rpow_mul (by norm_num)]; norm_num
  have hc := Gamma_one_sub_two_mul_le_tan hδ hδ2
  have e : Real.Gamma (1 / 2 - δ) = Real.Gamma (1 - 2 * δ) * (4 : ℝ) ^ δ * Real.sqrt π / Real.Gamma (1 - δ) := by
    rw [eq_div_iff hG.ne', hdup, h4]
  rw [e, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have hs : 0 ≤ (4 : ℝ) ^ δ * Real.sqrt π := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hc hs]

/-- **Elementary bracket for `tan x / x`:** for `0 < x ≤ 1`, `sin x/(x cos x) ≤ (1 - x²/6 + x⁴/100)/(1 - x²/2)`
(Mathlib's `Real.sin_bound` and `Real.one_sub_sq_div_two_le_cos`). At `x = π/8` this is `1.0591` against the true
`1.0548`, where `1/cos x` gives `1.0824`. -/
theorem sin_div_mul_cos_le {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    Real.sin x / (x * Real.cos x) ≤ (1 - x ^ 2 / 6 + x ^ 4 / 100) / (1 - x ^ 2 / 2) := by
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  have hx2 : 0 < 1 - x ^ 2 / 2 := by nlinarith
  have hcos : 0 < Real.cos x := lt_of_lt_of_le hx2 hc
  have hs := Real.sin_bound (x := x) (by rw [abs_of_pos hx]; exact hx1)
  rw [abs_of_pos hx] at hs
  have hsin : Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 100 := by linarith [le_abs_self (Real.sin x - (x - x ^ 3 / 6))]
  rw [div_le_div_iff₀ (by positivity) hx2]
  have hnum : 0 ≤ 1 - x ^ 2 / 6 + x ^ 4 / 100 := by nlinarith
  calc Real.sin x * (1 - x ^ 2 / 2) ≤ (x - x ^ 3 / 6 + x ^ 5 / 100) * (1 - x ^ 2 / 2) :=
        mul_le_mul_of_nonneg_right hsin hx2.le
    _ = (1 - x ^ 2 / 6 + x ^ 4 / 100) * (x * (1 - x ^ 2 / 2)) := by ring
    _ ≤ (1 - x ^ 2 / 6 + x ^ 4 / 100) * (x * Real.cos x) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hc hx.le) hnum

end BoundariesOfClass.Analytic
