import BoundariesOfClass.CS.RealSigma
import BoundariesOfClass.CS.FullDecay

/-!
# BoundariesOfClass.Assembly.PerClass: one class's contribution at real `σ` near `1`, uniformly in the class

Pinned environment: Lean v4.34.1, Mathlib d13f23b. For a positive form `(a, b, c)` of discriminant `D` with
`1 ≤ a ≤ (2/3)√D` (the range of every Hermite representative, HCN's `exists_classReps`), and `C₁ = coeffR 1 D σ`:

* `re_class_ge_minus` (`1/2 < σ ≤ 1`, `re ζ(2σ-1) ≤ 0`):
  `a^{-σ} re ζ(2σ) + C₁ · (re ζ(2σ-1) - 2√2 κ) ≤ re (mainTermg + Eg)(σ)`.
  The pole term uses `coeffR a = a^{σ-1} C₁ ≤ C₁` (`a^{-δ} ≤ 1`), the remainder `BgR a = 2·2^{σ-1/2} κ_c coeffR a`
  with `2^{σ-1/2} ≤ √2`, `κ_c ≤ κ` (`c ≥ 3π/4`).
* `re_class_ge_minus_lam`: the same with the full-decay remainder of `BoundariesOfClass.CS.FullDecay`.
* `re_class_ge_plus` (`1 ≤ σ ≤ 3/2`, `re ζ(2σ) ≥ 0`, `re ζ(2σ-1) ≥ 0`):
  `C₁ · (re ζ(2σ-1) - 2·2^{σ-1/2} κ (√D)^{σ-1}) ≤ re (mainTermg + Eg)(σ)`
  (`coeffR a = a^{σ-1} C₁ ≥ C₁`; `a^{σ-1} ≤ (√D)^{σ-1}` in the remainder).

-/

set_option autoImplicit false

open Complex
open scoped Real

namespace BoundariesOfClass.Assembly

open HCN.CS BoundariesOfClass.CS

lemma re_ge_sub_norm (z w : ℂ) : z.re - ‖w‖ ≤ (z + w).re := by
  rw [Complex.add_re]
  have := Complex.abs_re_le_norm w
  have := neg_abs_le w.re
  linarith

/-- **One class, `σ ≤ 1`.** -/
theorem re_class_ge_minus {a b c D σ : ℝ} (hD : 0 < D) (hdisc : disc a b c = D) (ha : 1 ≤ a)
    (hamax : a ≤ 2 / 3 * Real.sqrt D) (hσ : 1 / 2 < σ) (hσ1 : σ ≤ 1)
    (hZm : (riemannZeta ((2 * σ - 1 : ℝ) : ℂ)).re ≤ 0) :
    a ^ (-σ) * (riemannZeta ((2 * σ : ℝ) : ℂ)).re +
        coeffR 1 D σ * ((riemannZeta ((2 * σ - 1 : ℝ) : ℂ)).re - 2 * Real.sqrt 2 * BoundariesOfClass.Numerics.kap) ≤
      (mainTermg a b c σ + Eg a b c σ).re := by
  have ha0 : 0 < a := by linarith
  have hD' : 0 < disc a b c := hdisc ▸ hD
  have hmain := mainTermg_re_ofReal ha0 hD' σ
  have hE := norm_Eg_ofReal_le ha0 hD' hσ
  rw [hdisc] at hmain hE
  have hC1 : 0 < coeffR 1 D σ := coeffR_pos one_pos hD hσ
  have hca : coeffR a D σ ≤ coeffR 1 D σ := by
    rw [coeffR_eq ha0 hD]
    have : a ^ (σ - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ha (by linarith)
    nlinarith
  have hca0 : 0 ≤ coeffR a D σ := (coeffR_pos ha0 hD hσ).le
  have h2 : (2 : ℝ) ^ (σ - 1 / 2) ≤ Real.sqrt 2 := by
    rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hk := kappaC_le_kap ha0 hD hamax
  have hk0 := kappaC_nonneg a D
  have hkap0 := BoundariesOfClass.Numerics.kap_nonneg
  have hB : BgR a D σ ≤ 2 * Real.sqrt 2 * BoundariesOfClass.Numerics.kap * coeffR 1 D σ := by
    rw [BgR_eq ha0 hD]
    have h20 : 0 ≤ (2 : ℝ) ^ (σ - 1 / 2) := by positivity
    have s1 : (2 : ℝ) ^ (σ - 1 / 2) * kappaC a D ≤ Real.sqrt 2 * BoundariesOfClass.Numerics.kap :=
      mul_le_mul h2 hk hk0 (Real.sqrt_nonneg 2)
    have s2 : (2 : ℝ) ^ (σ - 1 / 2) * kappaC a D * coeffR a D σ ≤ Real.sqrt 2 * BoundariesOfClass.Numerics.kap * coeffR 1 D σ :=
      mul_le_mul s1 hca hca0 (by positivity)
    nlinarith
  have hpole : coeffR 1 D σ * (riemannZeta ((2 * σ - 1 : ℝ) : ℂ)).re ≤
      coeffR a D σ * (riemannZeta ((2 * σ - 1 : ℝ) : ℂ)).re :=
    mul_le_mul_of_nonpos_right hca hZm
  have := re_ge_sub_norm (mainTermg a b c σ) (Eg a b c σ)
  nlinarith

/-- **One class, `σ ≥ 1`.** -/
theorem re_class_ge_plus {a b c D σ : ℝ} (hD : 0 < D) (hdisc : disc a b c = D) (ha : 1 ≤ a)
    (hamax : a ≤ 2 / 3 * Real.sqrt D) (hσ : 1 ≤ σ)
    (hZ2 : 0 ≤ (riemannZeta ((2 * σ : ℝ) : ℂ)).re) (hZp : 0 ≤ (riemannZeta ((2 * σ - 1 : ℝ) : ℂ)).re) :
    coeffR 1 D σ * ((riemannZeta ((2 * σ - 1 : ℝ) : ℂ)).re -
        2 * (2 : ℝ) ^ (σ - 1 / 2) * BoundariesOfClass.Numerics.kap * Real.sqrt D ^ (σ - 1)) ≤
      (mainTermg a b c σ + Eg a b c σ).re := by
  have ha0 : 0 < a := by linarith
  have hσ' : 1 / 2 < σ := by linarith
  have hD' : 0 < disc a b c := hdisc ▸ hD
  have hmain := mainTermg_re_ofReal ha0 hD' σ
  have hE := norm_Eg_ofReal_le ha0 hD' hσ'
  rw [hdisc] at hmain hE
  have hC1 : 0 < coeffR 1 D σ := coeffR_pos one_pos hD hσ'
  have hsD : 0 < Real.sqrt D := Real.sqrt_pos.mpr hD
  have hpow1 : 1 ≤ a ^ (σ - 1) := Real.one_le_rpow ha (by linarith)
  have hpow2 : a ^ (σ - 1) ≤ Real.sqrt D ^ (σ - 1) :=
    Real.rpow_le_rpow ha0.le (by nlinarith) (by linarith)
  have hca : coeffR 1 D σ ≤ coeffR a D σ := by
    rw [coeffR_eq ha0 hD]; nlinarith
  have hk := kappaC_le_kap ha0 hD hamax
  have hk0 := kappaC_nonneg a D
  have hkap0 := BoundariesOfClass.Numerics.kap_nonneg
  have h20 : 0 ≤ (2 : ℝ) ^ (σ - 1 / 2) := by positivity
  have hB : BgR a D σ ≤ 2 * (2 : ℝ) ^ (σ - 1 / 2) * BoundariesOfClass.Numerics.kap * Real.sqrt D ^ (σ - 1) * coeffR 1 D σ := by
    rw [BgR_eq ha0 hD, coeffR_eq ha0 hD]
    have s1 : kappaC a D * a ^ (σ - 1) ≤ BoundariesOfClass.Numerics.kap * Real.sqrt D ^ (σ - 1) :=
      mul_le_mul hk hpow2 (by linarith) hkap0
    have s2 := mul_le_mul_of_nonneg_left s1 (show 0 ≤ 2 * (2 : ℝ) ^ (σ - 1 / 2) * coeffR 1 D σ by positivity)
    nlinarith
  have hpole : coeffR 1 D σ * (riemannZeta ((2 * σ - 1 : ℝ) : ℂ)).re ≤
      coeffR a D σ * (riemannZeta ((2 * σ - 1 : ℝ) : ℂ)).re :=
    mul_le_mul_of_nonneg_right hca hZp
  have hy0 : 0 ≤ a ^ (-σ) * (riemannZeta ((2 * σ : ℝ) : ℂ)).re := mul_nonneg (by positivity) hZ2
  have := re_ge_sub_norm (mainTermg a b c σ) (Eg a b c σ)
  nlinarith

/-- **One class, `σ ≤ 1`, with the full-decay remainder** (parameter `λ ∈ (0, 1)`, `x_λ = √(1-λ) · 3π/2`,
`κ(x) = e^{-x}/(1-e^{-x})²`): `a^{-σ} re ζ(2σ) + C₁ (re ζ(2σ-1) - 2 λ^{-(σ-1/2)} κ(x_λ)) ≤ re (mainTermg + Eg)(σ)`. -/
theorem re_class_ge_minus_lam {a b c D σ lam : ℝ} (hD : 0 < D) (hdisc : disc a b c = D) (ha : 1 ≤ a)
    (hamax : a ≤ 2 / 3 * Real.sqrt D) (hσ : 1 / 2 < σ) (hσ1 : σ ≤ 1) (hl0 : 0 < lam) (hl1 : lam < 1)
    (hZm : (riemannZeta ((2 * σ - 1 : ℝ) : ℂ)).re ≤ 0) :
    a ^ (-σ) * (riemannZeta ((2 * σ : ℝ) : ℂ)).re +
        coeffR 1 D σ * ((riemannZeta ((2 * σ - 1 : ℝ) : ℂ)).re -
          2 * lam ^ (-(σ - 1 / 2)) * (Real.exp (-(Real.sqrt (1 - lam) * (3 * π / 2))) /
            (1 - Real.exp (-(Real.sqrt (1 - lam) * (3 * π / 2)))) ^ 2)) ≤
      (mainTermg a b c σ + Eg a b c σ).re := by
  have ha0 : 0 < a := by linarith
  have hD' : 0 < disc a b c := hdisc ▸ hD
  have hmain := mainTermg_re_ofReal ha0 hD' σ
  have hE := norm_Eg_ofReal_le_lam ha0 hD' hσ hl0 hl1
  rw [hdisc] at hmain hE
  have hC1 : 0 < coeffR 1 D σ := coeffR_pos one_pos hD hσ
  have hca : coeffR a D σ ≤ coeffR 1 D σ := by
    rw [coeffR_eq ha0 hD]
    have : a ^ (σ - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ha (by linarith)
    nlinarith
  have hca0 : 0 ≤ coeffR a D σ := (coeffR_pos ha0 hD hσ).le
  set kx := Real.exp (-(Real.sqrt (1 - lam) * (3 * π / 2))) / (1 - Real.exp (-(Real.sqrt (1 - lam) * (3 * π / 2)))) ^ 2
  have hk := kappaL_le ha0 hD hamax hl1
  have hk0 := kappaL_nonneg a D lam
  have hl : 0 ≤ lam ^ (-(σ - 1 / 2)) := Real.rpow_nonneg hl0.le _
  have hB : BgRL a D σ lam ≤ 2 * lam ^ (-(σ - 1 / 2)) * kx * coeffR 1 D σ := by
    rw [BgRL_eq ha0 hD σ hl0]
    have s1 : kappaL a D lam * coeffR a D σ ≤ kx * coeffR 1 D σ :=
      mul_le_mul hk hca hca0 (le_trans hk0 hk)
    have := mul_le_mul_of_nonneg_left s1 (show 0 ≤ 2 * lam ^ (-(σ - 1 / 2)) by positivity)
    nlinarith
  have hpole : coeffR 1 D σ * (riemannZeta ((2 * σ - 1 : ℝ) : ℂ)).re ≤
      coeffR a D σ * (riemannZeta ((2 * σ - 1 : ℝ) : ℂ)).re :=
    mul_le_mul_of_nonpos_right hca hZm
  have := re_ge_sub_norm (mainTermg a b c σ) (Eg a b c σ)
  nlinarith

end BoundariesOfClass.Assembly
