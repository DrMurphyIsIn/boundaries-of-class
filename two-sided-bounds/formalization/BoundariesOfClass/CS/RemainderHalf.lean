import BoundariesOfClass.CS.BesselHalf
import BoundariesOfClass.CS.RealSigma
import BoundariesOfClass.Analytic.Floor

/-!
# BoundariesOfClass.CS.RemainderHalf: the Chowla–Selberg remainder with the `K_{1/2}` kernel bound

Pinned environment: Lean v4.34.1, Mathlib d13f23b. For real `σ ∈ (1/2, 1]`, `ν = σ - 1/2 ∈ (0, 1/2]`:

* `norm_I_ofReal_le_half`: `‖I(σ; A, B)‖ ≤ (√(B/A))^{ν-1/2} √(π/A) e^{-2√(AB)}` (from `integral_rpow_kernF_le`);
* `norm_tsum_T_le_half`: with `A_y = α y²`, `B_k = β k²`, `c = √(αβ)`,
  `‖Σ T σ p‖ ≤ (√(β/α))^{ν-1/2} √(π/α) · 4 κ(2c)`; each term uses `|k|^{ν-1/2} |y|^{-ν-1/2} ≤ 1` and HCN's sharp split
  `|y||k| ≥ |y| + |k| - 1`;
* `norm_Eg_ofReal_le_half`: `‖E_Q(σ)‖ ≤ (2 π^σ/Γ(σ)) (2/√D)^σ κ(π√D/a)`. The `a`-dependence is only through
  `κ(π√D/a)`, which increases with `a`; so `‖E_Q(σ)‖ ≤ (2 π^σ/Γ(σ)) (2/√D)^σ κ(3π/2)` on `a ≤ (2/3)√D`
  (`norm_Eg_ofReal_le_half_max`).

This is the exact `K_{1/2}` bound `|I| ≤ 2 (B/A)^{ν/2} K_{1/2}(2√(AB))`, against CN-1's `e^{-√(AB)}` and the `λ`-split.
-/

set_option autoImplicit false

open Complex Set MeasureTheory Filter Topology
open scoped Real

namespace BoundariesOfClass.CS

open CN1.CS HCN.CS BoundariesOfClass.Analytic

/-- **The kernel bound at a real point, `1/2 < σ ≤ 1`.** -/
theorem norm_I_ofReal_le_half {A B σ : ℝ} (hA : 0 < A) (hB : 0 < B) (hσ : 1 / 2 < σ) (hσ1 : σ ≤ 1) :
    ‖I (σ : ℂ) A B‖ ≤ Real.sqrt (B / A) ^ ((σ - 1 / 2) - 1 / 2) *
      (Real.sqrt (π / A) * Real.exp (-(2 * Real.sqrt (A * B)))) := by
  rw [I_ofReal, Complex.norm_real, Real.norm_eq_abs]
  have hbound := integral_rpow_kernF_le (ν := σ - 1 / 2) hA hB (by linarith) (by linarith)
  have e : ∀ t : ℝ, t ^ (σ - 3 / 2) * Real.exp (-(A * t + B / t)) = t ^ ((σ - 1 / 2) - 1) * kernF A B t := by
    intro t; rw [show σ - 3 / 2 = (σ - 1 / 2) - 1 by ring]; rfl
  simp_rw [e]
  have h0 : 0 ≤ ∫ t in Ioi 0, t ^ ((σ - 1 / 2) - 1) * kernF A B t :=
    setIntegral_nonneg measurableSet_Ioi fun t ht =>
      mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (Real.exp_pos _).le
  rw [abs_of_nonneg h0]
  exact hbound

section Bounds

open HCN.CSAux

variable {u : ℤ → ℤ → ℂ} {A Bk : ℤ → ℝ} {α β : ℝ}
variable (hu : ∀ k y, ‖u k y‖ = 1) (hα : 0 < α) (hβ : 0 < β)
  (hA : ∀ y : ℤ, A y = α * (y : ℝ) ^ 2) (hB : ∀ k : ℤ, Bk k = β * (k : ℝ) ^ 2)
include hu hα hβ hA hB

/-- **Termwise `K_{1/2}` bound**, real `σ ∈ (1/2, 1]`, `c = √(αβ)`:
`‖T σ (y,k)‖ ≤ (√(β/α))^{ν-1/2} √(π/α) · e^{2c} e^{-2c|y|} e^{-2c|k|}`. -/
theorem norm_T_le_half {σ : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ ≤ 1) (p : ℤ × ℤ) :
    ‖T u A Bk (σ : ℂ) p‖ ≤ Real.sqrt (β / α) ^ ((σ - 1 / 2) - 1 / 2) * Real.sqrt (π / α) *
      maj (2 * Real.sqrt (α * β)) p := by
  set c := Real.sqrt (α * β) with hcdef
  have hc : 0 < c := Real.sqrt_pos.mpr (mul_pos hα hβ)
  have hK0 : 0 ≤ Real.sqrt (β / α) ^ ((σ - 1 / 2) - 1 / 2) * Real.sqrt (π / α) := by positivity
  have hm := maj_nonneg (2 * c) p
  unfold T
  split_ifs with h
  · rw [norm_zero]; exact mul_nonneg hK0 hm
  · obtain ⟨hy, hk⟩ := not_or.mp h
    rw [norm_mul, hu, one_mul]
    have hy1 : (1 : ℝ) ≤ |(p.1 : ℝ)| := by exact_mod_cast Int.one_le_abs hy
    have hk1 : (1 : ℝ) ≤ |(p.2 : ℝ)| := by exact_mod_cast Int.one_le_abs hk
    set Y := |(p.1 : ℝ)| with hY
    set Kk := |(p.2 : ℝ)| with hKk
    have hY0 : 0 < Y := by linarith
    have hK0' : 0 < Kk := by linarith
    have hAy : A p.1 = α * Y ^ 2 := by rw [hA, hY, sq_abs]
    have hBk : Bk p.2 = β * Kk ^ 2 := by rw [hB, hKk, sq_abs]
    have hAy0 : 0 < A p.1 := by rw [hAy]; positivity
    have hBk0 : 0 < Bk p.2 := by rw [hBk]; positivity
    refine (norm_I_ofReal_le_half hAy0 hBk0 hσ hσ1).trans ?_
    set e := (σ - 1 / 2) - 1 / 2 with he
    have he0 : e ≤ 0 := by rw [he]; linarith
    have he1 : -1 / 2 < e := by rw [he]; linarith
    -- the three factors
    have f1 : Real.sqrt (Bk p.2 / A p.1) = Real.sqrt (β / α) * (Kk / Y) := by
      rw [hAy, hBk, show β * Kk ^ 2 / (α * Y ^ 2) = β / α * (Kk / Y) ^ 2 by field_simp,
        Real.sqrt_mul (div_pos hβ hα).le, Real.sqrt_sq (by positivity)]
    have f2 : Real.sqrt (π / A p.1) = Real.sqrt (π / α) / Y := by
      rw [hAy, show π / (α * Y ^ 2) = π / α / Y ^ 2 by field_simp, Real.sqrt_div' _ (sq_nonneg Y),
        Real.sqrt_sq hY0.le]
    have f3 : 2 * Real.sqrt (A p.1 * Bk p.2) = 2 * c * (Y * Kk) := by
      rw [hAy, hBk, show α * Y ^ 2 * (β * Kk ^ 2) = (α * β) * (Y * Kk) ^ 2 by ring,
        Real.sqrt_mul (mul_pos hα hβ).le, Real.sqrt_sq (by positivity)]; ring
    rw [f1, f2, f3, Real.mul_rpow (Real.sqrt_nonneg _) (by positivity)]
    -- `(K/Y)^e / Y ≤ 1`
    have hfac : (Kk / Y) ^ e / Y ≤ 1 := by
      rw [Real.div_rpow hK0'.le hY0.le, div_div, div_le_one (by positivity)]
      have h1 : Kk ^ e ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hk1 he0
      have h2 : 1 ≤ Y ^ e * Y := by
        rw [← Real.rpow_add_one hY0.ne']
        exact Real.one_le_rpow hy1 (by linarith)
      linarith
    have hexp : Real.exp (-(2 * c * (Y * Kk))) ≤ maj (2 * c) p := by
      simp only [maj, gmaj]
      rw [if_neg hy, if_neg hk]
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have key : Y + Kk - 1 ≤ Y * Kk := by nlinarith [mul_nonneg (sub_nonneg.mpr hy1) (sub_nonneg.mpr hk1)]
      rw [← hY, ← hKk]
      nlinarith [mul_le_mul_of_nonneg_left key (by linarith : (0 : ℝ) ≤ 2 * c)]
    have hpos : 0 ≤ Real.sqrt (β / α) ^ e * Real.sqrt (π / α) := by positivity
    calc Real.sqrt (β / α) ^ e * (Kk / Y) ^ e * (Real.sqrt (π / α) / Y * Real.exp (-(2 * c * (Y * Kk))))
        = Real.sqrt (β / α) ^ e * Real.sqrt (π / α) * ((Kk / Y) ^ e / Y) * Real.exp (-(2 * c * (Y * Kk))) := by
          ring
      _ ≤ Real.sqrt (β / α) ^ e * Real.sqrt (π / α) * 1 * maj (2 * c) p := by
          apply mul_le_mul _ hexp (Real.exp_pos _).le (by positivity)
          exact mul_le_mul_of_nonneg_left hfac hpos
      _ = _ := by ring

/-- **The `K_{1/2}` bound on the remainder sum.** -/
theorem norm_tsum_T_le_half {σ : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ ≤ 1) :
    ‖∑' p : ℤ × ℤ, T u A Bk (σ : ℂ) p‖ ≤ Real.sqrt (β / α) ^ ((σ - 1 / 2) - 1 / 2) * Real.sqrt (π / α) *
      (4 * BoundariesOfClass.Analytic.kappa (2 * Real.sqrt (α * β))) := by
  have hc : 0 < 2 * Real.sqrt (α * β) := by have := Real.sqrt_pos.mpr (mul_pos hα hβ); positivity
  have hs : 1 / 2 < (σ : ℂ).re := by simpa using hσ
  have hsn := summable_norm_T hu hα hβ hA hB hs
  calc ‖∑' p : ℤ × ℤ, T u A Bk (σ : ℂ) p‖ ≤ ∑' p : ℤ × ℤ, ‖T u A Bk (σ : ℂ) p‖ := norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' p : ℤ × ℤ, Real.sqrt (β / α) ^ ((σ - 1 / 2) - 1 / 2) * Real.sqrt (π / α) *
          maj (2 * Real.sqrt (α * β)) p :=
        Summable.tsum_le_tsum (norm_T_le_half hu hα hβ hA hB hσ hσ1) hsn ((summable_maj hc).mul_left _)
    _ = _ := by rw [tsum_mul_left, tsum_maj hc]; rfl

end Bounds

variable {a b c : ℝ}

/-- **The remainder at real `σ ∈ (1/2, 1]` with the `K_{1/2}` bound:**
`‖E_Q(σ)‖ ≤ (2 π^σ/Γ(σ)) (2/√D)^σ κ(π√D/a)`. -/
theorem norm_Eg_ofReal_le_half (ha : 0 < a) (hD : 0 < disc a b c) {σ : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ ≤ 1) :
    ‖Eg a b c σ‖ ≤ 2 * π ^ σ / Real.Gamma σ * (2 / Real.sqrt (disc a b c)) ^ σ *
      BoundariesOfClass.Analytic.kappa (π * Real.sqrt (disc a b c) / a) := by
  set D := disc a b c with hDdef
  have hSb := norm_tsum_T_le_half (Glue.norm_phase a b) (Glue.alpha_pos ha hD) (Glue.beta_pos ha)
    (Glue.ayg_eq a b c) (Glue.bkg_eq a) hσ hσ1
  rw [← Glue.Sg_eq, Glue.sqrt_alpha_beta ha hD] at hSb
  have hsD : 0 < Real.sqrt D := Real.sqrt_pos.mpr hD
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  -- `√(β/α) = 2/√D`, `√(π/α) = 2√a/√D`, `2 cstg = π√D/a`
  have g1 : Real.sqrt (π / a / (π * D / (4 * a))) = 2 / Real.sqrt D := by
    rw [show π / a / (π * D / (4 * a)) = (2 / Real.sqrt D) ^ 2 by
      rw [div_pow, Real.sq_sqrt hD.le]; field_simp; ring]
    exact Real.sqrt_sq (by positivity)
  have g2 : Real.sqrt (π / (π * D / (4 * a))) = 2 * Real.sqrt a / Real.sqrt D := by
    rw [show π / (π * D / (4 * a)) = (2 * Real.sqrt a / Real.sqrt D) ^ 2 by
      rw [div_pow, mul_pow, Real.sq_sqrt hD.le, Real.sq_sqrt ha.le]; field_simp; ring]
    exact Real.sqrt_sq (by positivity)
  have g3 : 2 * cstg a D = π * Real.sqrt D / a := by unfold cstg; field_simp
  rw [g1, g2, g3] at hSb
  have hπ : ‖(π : ℂ) ^ (σ : ℂ)‖ = π ^ σ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos, Complex.ofReal_re]
  have hG : Gamma (σ : ℂ) = (Real.Gamma σ : ℂ) := Complex.Gamma_ofReal σ
  have hGpos : 0 < Real.Gamma σ := Real.Gamma_pos_of_pos (by linarith)
  have hC : ‖((((Real.sqrt a)⁻¹ : ℝ) : ℂ))‖ = (Real.sqrt a)⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [Eg, norm_mul, norm_mul, norm_div, norm_mul, hπ, hG, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hGpos, hC, h2]
  have hK : 0 ≤ π ^ σ * (Real.Gamma σ)⁻¹ / 2 * (Real.sqrt a)⁻¹ := by positivity
  have hpow : (2 / Real.sqrt D) ^ ((σ - 1 / 2) - 1 / 2) * (2 / Real.sqrt D) = (2 / Real.sqrt D) ^ σ := by
    rw [show σ = ((σ - 1 / 2) - 1 / 2) + 1 by ring, Real.rpow_add_one (by positivity)]
    ring_nf
  calc π ^ σ * (Real.Gamma σ)⁻¹ / 2 * (Real.sqrt a)⁻¹ * ‖Sg a b c σ‖
      ≤ π ^ σ * (Real.Gamma σ)⁻¹ / 2 * (Real.sqrt a)⁻¹ *
          ((2 / Real.sqrt D) ^ ((σ - 1 / 2) - 1 / 2) * (2 * Real.sqrt a / Real.sqrt D) *
            (4 * BoundariesOfClass.Analytic.kappa (π * Real.sqrt D / a))) := mul_le_mul_of_nonneg_left hSb hK
    _ = 2 * π ^ σ / Real.Gamma σ * ((2 / Real.sqrt D) ^ ((σ - 1 / 2) - 1 / 2) * (2 / Real.sqrt D)) *
          BoundariesOfClass.Analytic.kappa (π * Real.sqrt D / a) := by field_simp; ring
    _ = _ := by rw [hpow]

/-- **The same, uniform over the classes:** for `1 ≤ a ≤ (2/3)√D`, `κ(π√D/a) ≤ κ(3π/2)`. -/
theorem norm_Eg_ofReal_le_half_max (ha : 0 < a) (hD : 0 < disc a b c) (hamax : a ≤ 2 / 3 * Real.sqrt (disc a b c))
    {σ : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ ≤ 1) :
    ‖Eg a b c σ‖ ≤ 2 * π ^ σ / Real.Gamma σ * (2 / Real.sqrt (disc a b c)) ^ σ * BoundariesOfClass.Analytic.kappa (3 * π / 2) := by
  refine (norm_Eg_ofReal_le_half ha hD hσ hσ1).trans ?_
  have hsD : 0 < Real.sqrt (disc a b c) := Real.sqrt_pos.mpr hD
  have hK : 0 ≤ 2 * π ^ σ / Real.Gamma σ * (2 / Real.sqrt (disc a b c)) ^ σ := by
    have := Real.Gamma_pos_of_pos (show 0 < σ by linarith); positivity
  apply mul_le_mul_of_nonneg_left _ hK
  -- `κ` decreasing, and `π√D/a ≥ 3π/2`
  have hmono := rpow_neg_mul_kappa_mono (δ := 0) le_rfl zero_le_one (C := π * Real.sqrt (disc a b c))
    (by positivity) ha hamax (by positivity)
  rw [neg_zero, Real.rpow_zero, Real.rpow_zero, one_mul, one_mul] at hmono
  have e : π * Real.sqrt (disc a b c) / (2 / 3 * Real.sqrt (disc a b c)) = 3 * π / 2 := by
    field_simp
  rwa [e] at hmono

end BoundariesOfClass.CS
