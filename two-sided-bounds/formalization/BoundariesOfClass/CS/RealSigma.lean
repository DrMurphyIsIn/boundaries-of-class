import HCN.Statements.GeneralCS
import BoundariesOfClass.Numerics.Uniform
import BoundariesOfClass.Analytic.GammaNearOne

/-!
# BoundariesOfClass.CS.RealSigma: the general Chowla–Selberg formula at a real point `σ > 1/2`, one class at a time

Pinned environment: Lean v4.34.1, Mathlib d13f23b. HCN proved the general form's identity and holomorphy for every
`s` (`HCN.CS.CS_main_general`, `differentiableOn_mainTermg_add_Eg`, HCN/Statements/GeneralCS.lean:166, :221) but
evaluated the main term and bounded the remainder at `s = 7/8` only (:265, :294). Here the same two facts at any real
`σ > 1/2`:

* `mainTermg_re_ofReal`: `re mainTermg(σ) = a^{-σ} re ζ(2σ) + coeffR a D σ · re ζ(2σ - 1)`, with
  `coeffR a D σ = π^σ Γ(σ-1/2)/Γ(σ) · a^{-1/2} (4a/(πD))^{σ-1/2}`;
* `norm_Eg_ofReal_le`: `‖E_Q(σ)‖ ≤ BgR a D σ = 2 π^σ Γ(σ-1/2)/Γ(σ) · a^{-1/2} (8a/(πD))^{σ-1/2} · κ_c`,
  `κ_c = e^{-c}/(1-e^{-c})²`, `c = π√D/(2a)`, from HCN's kernel bound `HCN.CSAux.norm_tsum_T_le` (any `re s > 1/2`).

Then the algebra that makes the class sum uniform in the class:
* `coeffR_eq`: `coeffR a D σ = a^{σ-1} · coeffR 1 D σ` (the whole `a`-dependence; so `≤ coeffR 1` for `σ ≤ 1` and
  `≥ coeffR 1` for `σ ≥ 1` when `a ≥ 1`; no analogue of HCN's 7/8-only `Bg_mono` is needed);
* `BgR_eq`: `BgR a D σ = 2 · 2^{σ-1/2} · κ_c · coeffR a D σ`;
* `kappa_le_kap`: `κ_c ≤ κ = κ_{3π/4}` when `a ≤ (2/3)√D`;
* `coeffR_one_eq`: `coeffR 1 D σ = √π · Γ(σ-1/2)/Γ(σ) · 4^{σ-1/2} · D^{-(σ-1/2)}`;
* the near-one brackets `coeffR_one_le_minus` and its sharp form `coeffR_one_le_minus_tan` (`σ = 1 - δ`), `coeffR_one_ge_plus`, `coeffR_one_le_plus`
  (`σ = 1 + δ`), from BoundariesOfClass.Analytic.GammaNearOne.

-/

set_option autoImplicit false

open Complex Set
open scoped Real

namespace BoundariesOfClass.CS

open HCN.CS

/-- The real coefficient of `ζ(2σ - 1)` in `mainTermg` at real `σ`. -/
noncomputable def coeffR (a D σ : ℝ) : ℝ :=
  π ^ σ * Real.Gamma (σ - 1 / 2) / Real.Gamma σ * (Real.sqrt a)⁻¹ * (4 * a / (π * D)) ^ (σ - 1 / 2)

/-- The class factor `κ_c = e^{-c}/(1 - e^{-c})²`, `c = π√D/(2a)`. -/
noncomputable def kappaC (a D : ℝ) : ℝ := Real.exp (-cstg a D) / (1 - Real.exp (-cstg a D)) ^ 2

/-- The remainder majorant at real `σ`: `2 π^σ Γ(σ-1/2)/Γ(σ) · a^{-1/2} (8a/(πD))^{σ-1/2} · κ_c` (`Bg` at `σ = 7/8`). -/
noncomputable def BgR (a D σ : ℝ) : ℝ :=
  2 * π ^ σ * Real.Gamma (σ - 1 / 2) / Real.Gamma σ * (Real.sqrt a)⁻¹ * (8 * a / (π * D)) ^ (σ - 1 / 2) * kappaC a D

variable {a b c : ℝ}

/-- **The main term at real `σ`, real part.** -/
theorem mainTermg_re_ofReal (ha : 0 < a) (hD : 0 < disc a b c) (σ : ℝ) :
    (mainTermg a b c σ).re =
      a ^ (-σ) * (riemannZeta ((2 * σ : ℝ) : ℂ)).re +
        coeffR a (disc a b c) σ * (riemannZeta ((2 * σ - 1 : ℝ) : ℂ)).re := by
  unfold mainTermg coeffR
  have h1 : (2 : ℂ) * (σ : ℂ) = ((2 * σ : ℝ) : ℂ) := by push_cast; ring
  have h2 : (2 : ℂ) * (σ : ℂ) - 1 = ((2 * σ - 1 : ℝ) : ℂ) := by push_cast; ring
  have h3 : (σ : ℂ) - 1 / 2 = ((σ - 1 / 2 : ℝ) : ℂ) := by push_cast; ring
  have hn : -(σ : ℂ) = ((-σ : ℝ) : ℂ) := by push_cast; ring
  have hD' : 0 ≤ 4 * a / (π * disc a b c) := by positivity
  rw [h2, h1, h3, hn, ← Complex.ofReal_cpow ha.le, ← Complex.ofReal_cpow Real.pi_pos.le,
    Complex.Gamma_ofReal, Complex.Gamma_ofReal, ← Complex.ofReal_cpow hD']
  rw [show ((Real.pi ^ σ : ℝ) : ℂ) * ((Real.Gamma (σ - 1 / 2) : ℝ) : ℂ) * ((Real.Gamma σ : ℝ) : ℂ)⁻¹ *
      (((Real.sqrt a)⁻¹ : ℝ) : ℂ) * (((4 * a / (π * disc a b c)) ^ (σ - 1 / 2) : ℝ) : ℂ) =
      ((π ^ σ * Real.Gamma (σ - 1 / 2) / Real.Gamma σ * (Real.sqrt a)⁻¹ *
        (4 * a / (π * disc a b c)) ^ (σ - 1 / 2) : ℝ) : ℂ) by push_cast; ring]
  rw [Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]

/-- **The remainder at real `σ > 1/2`:** `‖E_Q(σ)‖ ≤ BgR a D σ`. -/
theorem norm_Eg_ofReal_le (ha : 0 < a) (hD : 0 < disc a b c) {σ : ℝ} (hσ : 1 / 2 < σ) :
    ‖Eg a b c σ‖ ≤ BgR a (disc a b c) σ := by
  have hs : 1 / 2 < (σ : ℂ).re := by simpa using hσ
  have hSb := HCN.CSAux.norm_tsum_T_le (Glue.norm_phase a b) (Glue.alpha_pos ha hD) (Glue.beta_pos ha)
    (Glue.ayg_eq a b c) (Glue.bkg_eq a) hs
  rw [Complex.ofReal_re, Glue.two_div_alpha ha hD, Glue.sqrt_alpha_beta ha hD, ← Glue.Sg_eq] at hSb
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
  calc π ^ σ * (Real.Gamma σ)⁻¹ / 2 * (Real.sqrt a)⁻¹ * ‖Sg a b c σ‖
      ≤ π ^ σ * (Real.Gamma σ)⁻¹ / 2 * (Real.sqrt a)⁻¹ *
          (Real.Gamma (σ - 1 / 2) * (8 * a / (π * disc a b c)) ^ (σ - 1 / 2) *
            (4 * (Real.exp (-cstg a (disc a b c)) / (1 - Real.exp (-cstg a (disc a b c))) ^ 2))) :=
        mul_le_mul_of_nonneg_left hSb hK
    _ = BgR a (disc a b c) σ := by
        unfold BgR kappaC
        field_simp
        ring

/-! ### The `a`-dependence -/

lemma sqrt_inv_mul_rpow {a : ℝ} (ha : 0 < a) (t : ℝ) : (Real.sqrt a)⁻¹ * a ^ t = a ^ (t - 1 / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg ha.le, ← Real.rpow_add ha]; ring_nf

/-- **`coeffR a D σ = a^{σ-1} · coeffR 1 D σ`.** -/
theorem coeffR_eq {a D : ℝ} (ha : 0 < a) (hD : 0 < D) (σ : ℝ) : coeffR a D σ = a ^ (σ - 1) * coeffR 1 D σ := by
  unfold coeffR
  have hsplit : (4 * a / (π * D)) ^ (σ - 1 / 2) = a ^ (σ - 1 / 2) * (4 * 1 / (π * D)) ^ (σ - 1 / 2) := by
    rw [← Real.mul_rpow ha.le (by positivity)]; congr 1; ring
  rw [hsplit, Real.sqrt_one, inv_one]
  have e := sqrt_inv_mul_rpow ha (σ - 1 / 2)
  rw [show σ - 1 / 2 - 1 / 2 = σ - 1 by ring] at e
  calc π ^ σ * Real.Gamma (σ - 1 / 2) / Real.Gamma σ * (Real.sqrt a)⁻¹ *
        (a ^ (σ - 1 / 2) * (4 * 1 / (π * D)) ^ (σ - 1 / 2))
      = π ^ σ * Real.Gamma (σ - 1 / 2) / Real.Gamma σ * ((Real.sqrt a)⁻¹ * a ^ (σ - 1 / 2)) *
          (4 * 1 / (π * D)) ^ (σ - 1 / 2) := by ring
    _ = _ := by rw [e]; ring

/-- **`BgR a D σ = 2 · 2^{σ-1/2} · κ_c · coeffR a D σ`.** -/
theorem BgR_eq {a D : ℝ} (ha : 0 < a) (hD : 0 < D) (σ : ℝ) :
    BgR a D σ = 2 * (2 : ℝ) ^ (σ - 1 / 2) * kappaC a D * coeffR a D σ := by
  unfold BgR coeffR
  have hsplit : (8 * a / (π * D)) ^ (σ - 1 / 2) = (2 : ℝ) ^ (σ - 1 / 2) * (4 * a / (π * D)) ^ (σ - 1 / 2) := by
    rw [← Real.mul_rpow (by norm_num) (by positivity)]; congr 1; ring
  rw [hsplit]; ring

lemma coeffR_pos {a D σ : ℝ} (ha : 0 < a) (hD : 0 < D) (hσ : 1 / 2 < σ) : 0 < coeffR a D σ := by
  unfold coeffR
  have := Real.Gamma_pos_of_pos (show 0 < σ - 1 / 2 by linarith)
  have := Real.Gamma_pos_of_pos (show 0 < σ by linarith)
  have := Real.sqrt_pos.mpr ha
  positivity

lemma kappaC_nonneg (a D : ℝ) : 0 ≤ kappaC a D := by
  unfold kappaC; positivity

/-- **`κ_c ≤ κ`** when `0 < a ≤ (2/3)√D`: then `c ≥ 3π/4`. -/
theorem kappaC_le_kap {a D : ℝ} (ha : 0 < a) (hD : 0 < D) (hamax : a ≤ 2 / 3 * Real.sqrt D) :
    kappaC a D ≤ BoundariesOfClass.Numerics.kap := by
  have hsD : 0 < Real.sqrt D := Real.sqrt_pos.mpr hD
  have hc : 3 * π / 4 ≤ cstg a D := by
    unfold cstg
    rw [le_div_iff₀ (by positivity)]
    have := Real.pi_pos
    nlinarith
  have he : Real.exp (-cstg a D) ≤ Real.exp (-(3 * π / 4)) := Real.exp_le_exp.mpr (by linarith)
  have h1 : Real.exp (-(3 * π / 4)) < 1 := Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos])
  exact BoundariesOfClass.Numerics.div_one_sub_sq_mono (Real.exp_pos _).le he h1

/-! ### `coeffR 1 D σ` near `σ = 1` -/

/-- `coeffR 1 D σ = √π · Γ(σ-1/2)/Γ(σ) · 4^{σ-1/2} · D^{-(σ-1/2)}`. -/
theorem coeffR_one_eq {D : ℝ} (hD : 0 < D) {σ : ℝ} (hσ : 1 / 2 < σ) :
    coeffR 1 D σ = Real.sqrt π * (Real.Gamma (σ - 1 / 2) / Real.Gamma σ) * (4 : ℝ) ^ (σ - 1 / 2) *
      D ^ (-(σ - 1 / 2)) := by
  unfold coeffR
  rw [Real.sqrt_one, inv_one, mul_one, mul_one, Real.div_rpow (by norm_num) (by positivity),
    Real.mul_rpow Real.pi_pos.le hD.le, Real.rpow_neg hD.le, Real.sqrt_eq_rpow,
    show (1 / 2 : ℝ) = σ - (σ - 1 / 2) by ring, Real.rpow_sub Real.pi_pos]
  have h1 : 0 < π ^ (σ - (σ - 1 / 2)) := by positivity
  have h2 : 0 < π ^ (σ - 1 / 2) := by positivity
  have h3 : 0 < D ^ (σ - 1 / 2) := by positivity
  have h4 : 0 < Real.Gamma σ := Real.Gamma_pos_of_pos (by linarith)
  field_simp

lemma four_rpow_half : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
  rw [← Real.sqrt_eq_rpow, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

lemma rpow_neg_half_add {D : ℝ} (hD : 0 < D) (x : ℝ) : D ^ (-(1 / 2 + x)) = D ^ (-x) / Real.sqrt D := by
  rw [Real.sqrt_eq_rpow, show -(1 / 2 + x) = -x - 1 / 2 by ring, Real.rpow_sub hD]

/-- **`σ = 1 - δ`:** `coeffR 1 D (1-δ) ≤ 2π D^δ / (√D cos(πδ))` for `0 < δ < 1/2`. -/
theorem coeffR_one_le_minus {D δ : ℝ} (hD : 0 < D) (hδ : 0 < δ) (hδ2 : δ < 1 / 2) :
    coeffR 1 D (1 - δ) ≤ 2 * π * D ^ δ / (Real.sqrt D * Real.cos (π * δ)) := by
  have hcos := BoundariesOfClass.Analytic.cos_pi_mul_pos hδ hδ2
  have hsD : 0 < Real.sqrt D := Real.sqrt_pos.mpr hD
  rw [coeffR_one_eq hD (by linarith), show (1 - δ) - 1 / 2 = 1 / 2 + -δ by ring, rpow_neg_half_add hD, neg_neg,
    show (1 / 2 : ℝ) + -δ = 1 / 2 - δ by ring, Real.rpow_sub (by norm_num : (0 : ℝ) < 4), four_rpow_half]
  have hG := BoundariesOfClass.Analytic.Gamma_ratio_le hδ hδ2
  have h4 : 0 < (4 : ℝ) ^ δ := by positivity
  have hpi : Real.sqrt π * Real.sqrt π = π := Real.mul_self_sqrt Real.pi_pos.le
  have hGr : 0 ≤ Real.Gamma (1 / 2 - δ) / Real.Gamma (1 - δ) :=
    div_nonneg (Real.Gamma_pos_of_pos (by linarith)).le (Real.Gamma_pos_of_pos (by linarith)).le
  calc Real.sqrt π * (Real.Gamma (1 / 2 - δ) / Real.Gamma (1 - δ)) * (2 / (4 : ℝ) ^ δ) * (D ^ δ / Real.sqrt D)
      ≤ Real.sqrt π * ((4 : ℝ) ^ δ * Real.sqrt π / Real.cos (π * δ)) * (2 / (4 : ℝ) ^ δ) *
          (D ^ δ / Real.sqrt D) := by gcongr
    _ = (Real.sqrt π * Real.sqrt π) * ((4 : ℝ) ^ δ * ((4 : ℝ) ^ δ)⁻¹) * 2 * D ^ δ /
          (Real.sqrt D * Real.cos (π * δ)) := by ring
    _ = 2 * π * D ^ δ / (Real.sqrt D * Real.cos (π * δ)) := by rw [hpi, mul_inv_cancel₀ h4.ne']; ring

/-- **`σ = 1 + δ`, main term:** `2π D^{-δ}/√D ≤ coeffR 1 D (1+δ)` for `δ ≥ 0`. -/
theorem coeffR_one_ge_plus {D δ : ℝ} (hD : 0 < D) (hδ : 0 ≤ δ) :
    2 * π * D ^ (-δ) / Real.sqrt D ≤ coeffR 1 D (1 + δ) := by
  have hsD : 0 < Real.sqrt D := Real.sqrt_pos.mpr hD
  rw [coeffR_one_eq hD (by linarith), show (1 + δ) - 1 / 2 = 1 / 2 + δ by ring, rpow_neg_half_add hD,
    Real.rpow_add (by norm_num : (0 : ℝ) < 4), four_rpow_half]
  have hG := BoundariesOfClass.Analytic.Gamma_ratio_plus_ge hδ
  have h4 : 0 < (4 : ℝ) ^ δ := by positivity
  have hpi : Real.sqrt π * Real.sqrt π = π := Real.mul_self_sqrt Real.pi_pos.le
  have h4n : (4 : ℝ) ^ (-δ) * (4 : ℝ) ^ δ = 1 := by
    rw [← Real.rpow_add (by norm_num), neg_add_cancel, Real.rpow_zero]
  calc 2 * π * D ^ (-δ) / Real.sqrt D
      = (Real.sqrt π * Real.sqrt π) * ((4 : ℝ) ^ (-δ) * (4 : ℝ) ^ δ) * 2 * D ^ (-δ) / Real.sqrt D := by
        rw [hpi, h4n]; ring
    _ = Real.sqrt π * ((4 : ℝ) ^ (-δ) * Real.sqrt π) * (2 * (4 : ℝ) ^ δ) * (D ^ (-δ) / Real.sqrt D) := by ring
    _ ≤ Real.sqrt π * (Real.Gamma (1 / 2 + δ) / Real.Gamma (1 + δ)) * (2 * (4 : ℝ) ^ δ) *
          (D ^ (-δ) / Real.sqrt D) := by gcongr

/-- **`σ = 1 + δ`, remainder:** `coeffR 1 D (1+δ) ≤ 2π (1+δ)² D^{-δ}/√D` for `0 ≤ δ ≤ 1/2`. -/
theorem coeffR_one_le_plus {D δ : ℝ} (hD : 0 < D) (hδ : 0 ≤ δ) (hδ2 : δ ≤ 1 / 2) :
    coeffR 1 D (1 + δ) ≤ 2 * π * (1 + δ) ^ 2 * D ^ (-δ) / Real.sqrt D := by
  have hsD : 0 < Real.sqrt D := Real.sqrt_pos.mpr hD
  rw [coeffR_one_eq hD (by linarith), show (1 + δ) - 1 / 2 = 1 / 2 + δ by ring, rpow_neg_half_add hD,
    Real.rpow_add (by norm_num : (0 : ℝ) < 4), four_rpow_half]
  have hG := BoundariesOfClass.Analytic.Gamma_ratio_plus_le hδ hδ2
  have h4 : 0 < (4 : ℝ) ^ δ := by positivity
  have hpi : Real.sqrt π * Real.sqrt π = π := Real.mul_self_sqrt Real.pi_pos.le
  have h4n : (4 : ℝ) ^ (-δ) * (4 : ℝ) ^ δ = 1 := by
    rw [← Real.rpow_add (by norm_num), neg_add_cancel, Real.rpow_zero]
  calc Real.sqrt π * (Real.Gamma (1 / 2 + δ) / Real.Gamma (1 + δ)) * (2 * (4 : ℝ) ^ δ) * (D ^ (-δ) / Real.sqrt D)
      ≤ Real.sqrt π * ((4 : ℝ) ^ (-δ) * Real.sqrt π * (1 + δ) ^ 2) * (2 * (4 : ℝ) ^ δ) *
          (D ^ (-δ) / Real.sqrt D) := by gcongr
    _ = (Real.sqrt π * Real.sqrt π) * ((4 : ℝ) ^ (-δ) * (4 : ℝ) ^ δ) * 2 * (1 + δ) ^ 2 * D ^ (-δ) /
          Real.sqrt D := by ring
    _ = 2 * π * (1 + δ) ^ 2 * D ^ (-δ) / Real.sqrt D := by rw [hpi, h4n]; ring

/-- **`σ = 1 - δ`, sharp form:** `coeffR 1 D (1-δ) ≤ 2π D^δ sin(πδ) / (√D · πδ cos(πδ))` for `0 < δ < 1/2`. -/
theorem coeffR_one_le_minus_tan {D δ : ℝ} (hD : 0 < D) (hδ : 0 < δ) (hδ2 : δ < 1 / 2) :
    coeffR 1 D (1 - δ) ≤
      2 * π * D ^ δ * Real.sin (π * δ) / (Real.sqrt D * (π * δ * Real.cos (π * δ))) := by
  have hcos := BoundariesOfClass.Analytic.cos_pi_mul_pos hδ hδ2
  have hpd : 0 < π * δ := by positivity
  have hsD : 0 < Real.sqrt D := Real.sqrt_pos.mpr hD
  rw [coeffR_one_eq hD (by linarith), show (1 - δ) - 1 / 2 = 1 / 2 + -δ by ring, rpow_neg_half_add hD, neg_neg,
    show (1 / 2 : ℝ) + -δ = 1 / 2 - δ by ring, Real.rpow_sub (by norm_num : (0 : ℝ) < 4), four_rpow_half]
  have hG := BoundariesOfClass.Analytic.Gamma_ratio_le_tan hδ hδ2
  have h4 : 0 < (4 : ℝ) ^ δ := by positivity
  have hpi : Real.sqrt π * Real.sqrt π = π := Real.mul_self_sqrt Real.pi_pos.le
  calc Real.sqrt π * (Real.Gamma (1 / 2 - δ) / Real.Gamma (1 - δ)) * (2 / (4 : ℝ) ^ δ) * (D ^ δ / Real.sqrt D)
      ≤ Real.sqrt π * ((4 : ℝ) ^ δ * Real.sqrt π * Real.sin (π * δ) / (π * δ * Real.cos (π * δ))) *
          (2 / (4 : ℝ) ^ δ) * (D ^ δ / Real.sqrt D) := by gcongr
    _ = (Real.sqrt π * Real.sqrt π) * ((4 : ℝ) ^ δ * ((4 : ℝ) ^ δ)⁻¹) * 2 * D ^ δ * Real.sin (π * δ) /
          (Real.sqrt D * (π * δ * Real.cos (π * δ))) := by ring
    _ = _ := by rw [hpi, mul_inv_cancel₀ h4.ne']; ring

end BoundariesOfClass.CS
