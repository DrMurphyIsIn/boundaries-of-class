import BoundariesOfClass.CS.RealSigma

/-!
# BoundariesOfClass.CS.FullDecay: the Chowla–Selberg remainder with (almost) the full Bessel decay

Pinned environment: Lean v4.34.1, Mathlib d13f23b. CN-1's kernel bound `CN1.CS.norm_I_le` splits
`a t + b/t ≥ √(ab) + (a/2) t` and so keeps only `e^{-√(ab)}` of the true decay `e^{-2√(ab)}` of
`I(s; a, b) = ∫₀^∞ t^{s-3/2} e^{-a t - b/t} dt`. For a free parameter `λ ∈ (0, 1)`,
`a t + b/t = λ a t + ((1-λ) a t + b/t) ≥ λ a t + 2√((1-λ) a b)` gives

* `norm_I_le_lam`: `‖I(s; a, b)‖ ≤ e^{-2√((1-λ) a b)} (1/(λ a))^{σ-1/2} Γ(σ-1/2)` (`σ = re s > 1/2`);

and, following HCN's sharp split `|y||k| ≥ |y| + |k| - 1` (`HCN.CSAux.norm_T_le`) with `c_λ = 2√(1-λ) √(αβ)`,

* `norm_T_le_lam`, `norm_tsum_T_le_lam`: `‖Σ T s p‖ ≤ Γ(σ-1/2) (1/(λα))^{σ-1/2} · 4e^{-c_λ}/(1 - e^{-c_λ})²`;
* `norm_Eg_ofReal_le_lam`: `‖E_Q(σ)‖ ≤ BgRL a D σ λ = 2 π^σ Γ(σ-1/2)/Γ(σ) a^{-1/2} (4a/(λπD))^{σ-1/2} κ_λ`, with
  `κ_λ = e^{-c}/(1 - e^{-c})²` at `c = √(1-λ) π√D/a` (CN-1/HCN have `π√D/(2a)`, the case `λ = 1/2` up to `√2`);
* `BgRL_eq`: `BgRL a D σ λ = 2 λ^{-(σ-1/2)} κ_λ · coeffR a D σ`;
* `kappaL_le`: `κ_λ ≤ e^{-x}/(1-e^{-x})²` at `x = √(1-λ) · 3π/2` when `a ≤ (2/3)√D`.

The vendored modules are untouched; this module only adds lemmas.
-/

set_option autoImplicit false

open Complex Set MeasureTheory Filter Topology
open scoped Real

namespace BoundariesOfClass.CS

open CN1.CS HCN.CS

section Kernel

variable {a b t : ℝ} {s : ℂ} {lam : ℝ}

/-- The pointwise bound `e^{-(a t + b/t)} ≤ e^{-2√((1-λ) a b)} e^{-λ a t}` for `t > 0`, `0 ≤ λ ≤ 1`. -/
lemma exp_kern_le_lam (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 < t) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) :
    Real.exp (-(a * t + b / t)) ≤
      Real.exp (-(2 * Real.sqrt ((1 - lam) * a * b))) * Real.exp (-(lam * a * t)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := two_sqrt_le (a := (1 - lam) * a) (b := b) (by nlinarith) hb ht
  nlinarith

/-- The majorant integral `∫₀^∞ t^{σ-3/2} e^{-λ a t} dt = (1/(λa))^{σ-1/2} Γ(σ-1/2)`. -/
lemma integral_majorant_lam {σ : ℝ} (ha : 0 < a) (hl0 : 0 < lam) (hσ : 1 / 2 < σ) :
    ∫ t in Ioi 0, t ^ (σ - 1 / 2 - 1) * Real.exp (-(lam * a * t)) =
      (1 / (lam * a)) ^ (σ - 1 / 2) * Real.Gamma (σ - 1 / 2) := by
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith) (by positivity)]

/-- **The kernel bound with parameter `λ`.** -/
theorem norm_I_le_lam (ha : 0 < a) (hb : 0 ≤ b) (hs : 1 / 2 < s.re) (hl0 : 0 < lam) (hl1 : lam ≤ 1) :
    ‖I s a b‖ ≤ Real.exp (-(2 * Real.sqrt ((1 - lam) * a * b))) *
      ((1 / (lam * a)) ^ (s.re - 1 / 2) * Real.Gamma (s.re - 1 / 2)) := by
  rw [I_eq_integral]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hint : IntegrableOn (fun t : ℝ => Real.exp (-(2 * Real.sqrt ((1 - lam) * a * b))) *
      (t ^ (s.re - 1 / 2 - 1) * Real.exp (-(lam * a * t)))) (Ioi 0) :=
    (integrableOn_rpow_mul_exp (by linarith) (by positivity)).const_mul _
  calc ∫ t : ℝ in Ioi 0, ‖(t : ℂ) ^ (s - 3 / 2) * kern a b t‖
      ≤ ∫ t in Ioi 0, Real.exp (-(2 * Real.sqrt ((1 - lam) * a * b))) *
          (t ^ (s.re - 1 / 2 - 1) * Real.exp (-(lam * a * t))) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _) hint ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht' : 0 < t := mem_Ioi.mp ht
        have hre : (s - 3 / 2).re = s.re - 1 / 2 - 1 := by simp; ring
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht', norm_kern, hre]
        calc t ^ (s.re - 1 / 2 - 1) * Real.exp (-(a * t + b / t))
            ≤ t ^ (s.re - 1 / 2 - 1) *
                (Real.exp (-(2 * Real.sqrt ((1 - lam) * a * b))) * Real.exp (-(lam * a * t))) :=
              mul_le_mul_of_nonneg_left (exp_kern_le_lam ha.le hb ht' hl0.le hl1) (Real.rpow_nonneg ht'.le _)
          _ = _ := by ring
    _ = _ := by rw [integral_const_mul, integral_majorant_lam ha hl0 hs]

end Kernel

/-! ### The remainder sum with parameter `λ` -/

section Bounds

open HCN.CSAux

variable {u : ℤ → ℤ → ℂ} {A Bk : ℤ → ℝ} {α β lam : ℝ}
variable (hu : ∀ k y, ‖u k y‖ = 1) (hα : 0 < α) (hβ : 0 < β)
  (hA : ∀ y : ℤ, A y = α * (y : ℝ) ^ 2) (hB : ∀ k : ℤ, Bk k = β * (k : ℝ) ^ 2)
  (hl0 : 0 < lam) (hl1 : lam < 1)
include hu hα hβ hA hB hl0 hl1

/-- **Termwise bound with parameter `λ`**, `c_λ = 2√(1-λ) √(αβ)`:
`‖T s (y,k)‖ ≤ Γ(σ-1/2) (1/(λα))^{σ-1/2} · e^{c_λ} e^{-c_λ|y|} e^{-c_λ|k|}`. -/
theorem norm_T_le_lam {s : ℂ} (hs : 1 / 2 < s.re) (p : ℤ × ℤ) :
    ‖T u A Bk s p‖ ≤ Real.Gamma (s.re - 1 / 2) * (1 / (lam * α)) ^ (s.re - 1 / 2) *
      maj (2 * Real.sqrt (1 - lam) * Real.sqrt (α * β)) p := by
  set c := 2 * Real.sqrt (1 - lam) * Real.sqrt (α * β) with hcdef
  have hc : 0 < c := by
    have := Real.sqrt_pos.mpr (show 0 < 1 - lam by linarith)
    have := Real.sqrt_pos.mpr (mul_pos hα hβ)
    positivity
  have hΓ : 0 ≤ Real.Gamma (s.re - 1 / 2) := (Real.Gamma_pos_of_pos (by linarith)).le
  have h2 : 0 ≤ (1 / (lam * α)) ^ (s.re - 1 / 2) := Real.rpow_nonneg (by positivity) _
  have hm := maj_nonneg c p
  unfold T
  split_ifs with h
  · rw [norm_zero]; exact mul_nonneg (mul_nonneg hΓ h2) hm
  · obtain ⟨hy, hk⟩ := not_or.mp h
    rw [norm_mul, hu, one_mul]
    have hy1 : (1 : ℝ) ≤ |(p.1 : ℝ)| := by exact_mod_cast Int.one_le_abs hy
    have hk1 : (1 : ℝ) ≤ |(p.2 : ℝ)| := by exact_mod_cast Int.one_le_abs hk
    have hy2 : (1 : ℝ) ≤ (p.1 : ℝ) ^ 2 := by nlinarith [sq_abs (p.1 : ℝ)]
    have hAy : 0 < A p.1 := by rw [hA]; positivity
    have hBk : 0 ≤ Bk p.2 := by rw [hB]; positivity
    refine (norm_I_le_lam hAy hBk hs hl0 hl1.le).trans ?_
    have hsq : 2 * Real.sqrt ((1 - lam) * A p.1 * Bk p.2) = c * (|(p.1 : ℝ)| * |(p.2 : ℝ)|) := by
      rw [hA, hB, show (1 - lam) * (α * (p.1 : ℝ) ^ 2) * (β * (p.2 : ℝ) ^ 2) =
          ((1 - lam) * (α * β)) * (|(p.1 : ℝ)| * |(p.2 : ℝ)|) ^ 2 by rw [mul_pow, sq_abs, sq_abs]; ring,
        Real.sqrt_mul (by nlinarith [mul_pos hα hβ]), Real.sqrt_sq (by positivity),
        Real.sqrt_mul (by linarith)]
      ring
    have hexp : Real.exp (-(2 * Real.sqrt ((1 - lam) * A p.1 * Bk p.2))) ≤ maj c p := by
      rw [hsq]
      simp only [maj, gmaj, ite_cond_eq_false _ _ (eq_false hy), ite_cond_eq_false _ _ (eq_false hk)]
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have key : |(p.1 : ℝ)| + |(p.2 : ℝ)| - 1 ≤ |(p.1 : ℝ)| * |(p.2 : ℝ)| := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hy1) (sub_nonneg.mpr hk1)]
      nlinarith [mul_le_mul_of_nonneg_left key hc.le]
    have hpow : (1 / (lam * A p.1)) ^ (s.re - 1 / 2) ≤ (1 / (lam * α)) ^ (s.re - 1 / 2) := by
      refine Real.rpow_le_rpow (by positivity) ?_ (by linarith)
      rw [hA]
      apply one_div_le_one_div_of_le (by positivity)
      have : α ≤ α * (p.1 : ℝ) ^ 2 := le_mul_of_one_le_right hα.le hy2
      nlinarith
    calc Real.exp (-(2 * Real.sqrt ((1 - lam) * A p.1 * Bk p.2))) *
          ((1 / (lam * A p.1)) ^ (s.re - 1 / 2) * Real.Gamma (s.re - 1 / 2))
        ≤ maj c p * ((1 / (lam * α)) ^ (s.re - 1 / 2) * Real.Gamma (s.re - 1 / 2)) :=
          mul_le_mul hexp (mul_le_mul_of_nonneg_right hpow hΓ) (by positivity) hm
      _ = _ := by ring

/-- **The sum with parameter `λ`:** `‖Σ T s p‖ ≤ Γ(σ-1/2) (1/(λα))^{σ-1/2} · 4e^{-c_λ}/(1 - e^{-c_λ})²`. -/
theorem norm_tsum_T_le_lam {s : ℂ} (hs : 1 / 2 < s.re) :
    ‖∑' p : ℤ × ℤ, T u A Bk s p‖ ≤ Real.Gamma (s.re - 1 / 2) * (1 / (lam * α)) ^ (s.re - 1 / 2) *
      (4 * (Real.exp (-(2 * Real.sqrt (1 - lam) * Real.sqrt (α * β))) /
        (1 - Real.exp (-(2 * Real.sqrt (1 - lam) * Real.sqrt (α * β)))) ^ 2)) := by
  have hc : 0 < 2 * Real.sqrt (1 - lam) * Real.sqrt (α * β) := by
    have := Real.sqrt_pos.mpr (show 0 < 1 - lam by linarith)
    have := Real.sqrt_pos.mpr (mul_pos hα hβ)
    positivity
  have hsn := summable_norm_T hu hα hβ hA hB hs
  calc ‖∑' p : ℤ × ℤ, T u A Bk s p‖ ≤ ∑' p : ℤ × ℤ, ‖T u A Bk s p‖ := norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' p : ℤ × ℤ, Real.Gamma (s.re - 1 / 2) * (1 / (lam * α)) ^ (s.re - 1 / 2) *
          maj (2 * Real.sqrt (1 - lam) * Real.sqrt (α * β)) p :=
        Summable.tsum_le_tsum (norm_T_le_lam hu hα hβ hA hB hl0 hl1 hs) hsn ((summable_maj hc).mul_left _)
    _ = _ := by rw [tsum_mul_left, tsum_maj hc]

end Bounds

/-! ### The general form at real `σ` -/

/-- The class factor with parameter `λ`: `κ_λ = e^{-c}/(1 - e^{-c})²`, `c = √(1-λ) π√D/a`. -/
noncomputable def kappaL (a D lam : ℝ) : ℝ :=
  Real.exp (-(Real.sqrt (1 - lam) * (π * Real.sqrt D / a))) /
    (1 - Real.exp (-(Real.sqrt (1 - lam) * (π * Real.sqrt D / a)))) ^ 2

/-- The remainder majorant with parameter `λ`: `2 π^σ Γ(σ-1/2)/Γ(σ) a^{-1/2} (4a/(λπD))^{σ-1/2} κ_λ`. -/
noncomputable def BgRL (a D σ lam : ℝ) : ℝ :=
  2 * π ^ σ * Real.Gamma (σ - 1 / 2) / Real.Gamma σ * (Real.sqrt a)⁻¹ * (4 * a / (lam * π * D)) ^ (σ - 1 / 2) *
    kappaL a D lam

variable {a b c : ℝ}

/-- `2 √(1-λ) · cstg a D = √(1-λ) π√D/a`. -/
lemma two_sqrt_mul_cstg (a D lam : ℝ) :
    2 * Real.sqrt (1 - lam) * cstg a D = Real.sqrt (1 - lam) * (π * Real.sqrt D / a) := by
  unfold cstg; field_simp

/-- **The remainder at real `σ > 1/2` with parameter `λ ∈ (0, 1)`:** `‖E_Q(σ)‖ ≤ BgRL a D σ λ`. -/
theorem norm_Eg_ofReal_le_lam (ha : 0 < a) (hD : 0 < disc a b c) {σ lam : ℝ} (hσ : 1 / 2 < σ)
    (hl0 : 0 < lam) (hl1 : lam < 1) :
    ‖Eg a b c σ‖ ≤ BgRL a (disc a b c) σ lam := by
  have hs : 1 / 2 < (σ : ℂ).re := by simpa using hσ
  have hSb := norm_tsum_T_le_lam (Glue.norm_phase a b) (Glue.alpha_pos ha hD) (Glue.beta_pos ha)
    (Glue.ayg_eq a b c) (Glue.bkg_eq a) hl0 hl1 hs
  have hα : 1 / (lam * (π * disc a b c / (4 * a))) = 4 * a / (lam * π * disc a b c) := by
    have := Real.pi_pos
    field_simp
  have hc : 2 * Real.sqrt (1 - lam) * Real.sqrt (π * disc a b c / (4 * a) * (π / a)) =
      Real.sqrt (1 - lam) * (π * Real.sqrt (disc a b c) / a) := by
    rw [Glue.sqrt_alpha_beta ha hD, two_sqrt_mul_cstg]
  rw [Complex.ofReal_re, hα, hc, ← Glue.Sg_eq] at hSb
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
          (Real.Gamma (σ - 1 / 2) * (4 * a / (lam * π * disc a b c)) ^ (σ - 1 / 2) *
            (4 * (Real.exp (-(Real.sqrt (1 - lam) * (π * Real.sqrt (disc a b c) / a))) /
              (1 - Real.exp (-(Real.sqrt (1 - lam) * (π * Real.sqrt (disc a b c) / a)))) ^ 2))) :=
        mul_le_mul_of_nonneg_left hSb hK
    _ = BgRL a (disc a b c) σ lam := by
        unfold BgRL kappaL
        field_simp
        ring

/-- **`BgRL a D σ λ = 2 λ^{-(σ-1/2)} κ_λ · coeffR a D σ`.** -/
theorem BgRL_eq {a D : ℝ} (ha : 0 < a) (hD : 0 < D) (σ : ℝ) {lam : ℝ} (hl0 : 0 < lam) :
    BgRL a D σ lam = 2 * lam ^ (-(σ - 1 / 2)) * kappaL a D lam * coeffR a D σ := by
  unfold BgRL coeffR
  have hsplit : (4 * a / (lam * π * D)) ^ (σ - 1 / 2) = lam ^ (-(σ - 1 / 2)) * (4 * a / (π * D)) ^ (σ - 1 / 2) := by
    rw [Real.rpow_neg hl0.le, ← Real.inv_rpow hl0.le, ← Real.mul_rpow (by positivity) (by positivity)]
    congr 1; field_simp
  rw [hsplit]; ring

lemma kappaL_nonneg (a D lam : ℝ) : 0 ≤ kappaL a D lam := by
  unfold kappaL; positivity

/-- **`κ_λ ≤ κ(x)`, `x = √(1-λ) · 3π/2`,** when `0 < a ≤ (2/3)√D` and `λ < 1`. -/
theorem kappaL_le {a D lam : ℝ} (ha : 0 < a) (hD : 0 < D) (hamax : a ≤ 2 / 3 * Real.sqrt D) (hl1 : lam < 1) :
    kappaL a D lam ≤ Real.exp (-(Real.sqrt (1 - lam) * (3 * π / 2))) /
      (1 - Real.exp (-(Real.sqrt (1 - lam) * (3 * π / 2)))) ^ 2 := by
  have hsD : 0 < Real.sqrt D := Real.sqrt_pos.mpr hD
  have hsl : 0 < Real.sqrt (1 - lam) := Real.sqrt_pos.mpr (by linarith)
  have hc : 3 * π / 2 ≤ π * Real.sqrt D / a := by
    rw [le_div_iff₀ ha]
    have := Real.pi_pos
    nlinarith
  have he : Real.exp (-(Real.sqrt (1 - lam) * (π * Real.sqrt D / a))) ≤
      Real.exp (-(Real.sqrt (1 - lam) * (3 * π / 2))) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have h1 : Real.exp (-(Real.sqrt (1 - lam) * (3 * π / 2))) < 1 :=
    Real.exp_lt_one_iff.mpr (by have := Real.pi_pos; nlinarith)
  exact BoundariesOfClass.Numerics.div_one_sub_sq_mono (Real.exp_pos _).le he h1

end BoundariesOfClass.CS
