import BoundariesOfClass.Assembly.Common
import BoundariesOfClass.Assembly.PerClass
import BoundariesOfClass.Analytic.ZetaNearOne
import CN1.Assembly.Positivity
import CN1.Epstein.Factorization
import CN1.ChowlaSelberg.Continuation

/-!
# BoundariesOfClass.Assembly.Lower: the explicit lower bound `h ≥ (9/50) √d / log d`, in CN-1's `dOf m` vocabulary

Pinned environment: Lean v4.34.1, Mathlib d13f23b. For `K = ℚ(α)`, `α² = -m`, `m` squarefree, `m ∉ {1, 3}`,
`d = dOf m` (CN-1's `|disc K|`):

* `classSum_lt_zero` (any real `σ ∈ (7/8, 1)`): with `C₁ = coeffR 1 d σ`,
  `re ζ(2σ) + h · C₁ (re ζ(2σ-1) - 2√2 κ) < 0`.
  Proof: HCN's class partition and general Chowla–Selberg on `re s > 1`, continued to `σ` by CN-1's identity theorem;
  the left side `ζ(σ) L(σ, χ)` is negative because `ζ(σ) < 0` and `L(σ, χ) > 0` (**OpenAI's 7/8 theorem, at the real
  point `σ`**, through CN-1's `LFunction_ofReal_re_pos_of_seven_eighths_lt_of_isQuadratic`); the right side is at least
  the stated sum by `re_class_ge_minus` (principal class `a = 1`; every other `a^{-σ} ζ(2σ) ≥ 0`).
* `classSum_lt_zero_y0`: the same keeping every class's `y = 0` term; `classNumber_lower_general`: the bound for a
  general `δ`, with the cheap sharpenings (`π²/6`, the `tan` bracket, the `y = 0` terms), free of numerics.
* `classNumber_ge_explicit` (`d ≥ 2981`, `σ = 1 - 1/log d`): `h ≥ (13/8) cos(π/L) √d / (π e (L - 1 + 4√2 κ))`.
* `classNumber_ge` (`d ≥ 2981`): `(9/50) √d / log d ≤ h`, by `BoundariesOfClass.Numerics.lower_numeric`.

The interface to the challenge statements (`|discr K|` in place of `dOf m`, and `m ∉ {1, 3}` from `d ≥ 2981`) is separate.
-/

set_option autoImplicit false

open NumberField Ideal Complex Set CN1.Finite HCN.CS HCN.Epstein BoundariesOfClass.CS
open scoped nonZeroDivisors Real

namespace BoundariesOfClass.Assembly

/-- **The class sum at a real point `σ ∈ (7/8, 1)`, keeping every class's `y = 0` term.** With `Y = ((2/3)√d)^{-σ}`
(so `a_C^{-σ} ≥ Y` for every class) and `C₁ = coeffR 1 d σ`:
`re ζ(2σ) · (1 + (h - 1) Y) + h · C₁ (re ζ(2σ-1) - 2√2 κ) < 0`. -/
theorem classSum_lt_zero_y0 {K : Type*} [Field K] [NumberField K] {m : ℕ} {α : K} (hα : α ^ 2 = -(m : K))
    (hK : Module.finrank ℚ K = 2) (hm : Squarefree m) (hm1 : m ≠ 1) (hm3 : m ≠ 3) {σ : ℝ}
    (hσ78 : 7 / 8 < σ) (hσ1 : σ < 1) :
    (riemannZeta ((2 * σ : ℝ) : ℂ)).re * (1 + ((classNumber K : ℝ) - 1) * (2 / 3 * Real.sqrt (dOf m)) ^ (-σ)) +
      (classNumber K : ℝ) * (coeffR 1 (dOf m) σ *
        ((riemannZeta ((2 * σ - 1 : ℝ) : ℂ)).re - 2 * Real.sqrt 2 * BoundariesOfClass.Numerics.kap)) < 0 := by
  classical
  obtain ⟨J, A, B, C, -, hH, ⟨-, hA1, -, hC1⟩, hN, hZ⟩ := exists_classReps hα hK hm hm1 hm3
  have hD0 := dOf_pos hm
  set D : ℝ := (dOf m : ℝ) with hDdef
  have hdisc : ∀ Cl, HCN.CS.disc (formA (A Cl) (C Cl)) (formB m (B Cl) (C Cl)) (formC m (A Cl) (B Cl) (C Cl))
      = D := fun Cl => disc_form m (hH Cl).A_pos.ne' (hH Cl).C_pos.ne'
  have ha1 : ∀ Cl, 1 ≤ formA (A Cl) (C Cl) := fun Cl => (hH Cl).one_le_formA hα hK hm
  have hamax : ∀ Cl, formA (A Cl) (C Cl) ≤ 2 / 3 * Real.sqrt D :=
    fun Cl => ((hH Cl).formA_le_absNorm hα hK hm).trans (hN Cl)
  have hpos : ∀ Cl, 0 < formA (A Cl) (C Cl) := fun Cl => by linarith [ha1 Cl]
  have hdpos : ∀ Cl, 0 < HCN.CS.disc (formA (A Cl) (C Cl)) (formB m (B Cl) (C Cl))
      (formC m (A Cl) (B Cl) (C Cl)) := fun Cl => by rw [hdisc]; exact hD0
  -- the identity at `σ`
  have : NeZero (CN1.Foundations.disc m) := ⟨CN1.Epstein.disc_ne_zero hm.ne_zero⟩
  have hχ1 := CN1.Foundations.kroneckerChar_ne_one hm
  have hLd : Differentiable ℂ (DirichletCharacter.LFunction (CN1.Foundations.kroneckerChar m)) :=
    DirichletCharacter.differentiable_LFunction hχ1
  have hF : DifferentiableOn ℂ
      (fun s => riemannZeta s * DirichletCharacter.LFunction (CN1.Foundations.kroneckerChar m) s)
      ({s : ℂ | 1 / 2 < s.re} \ {1}) := by
    intro s hs
    have hs1 : s ≠ 1 := fun h => hs.2 (mem_singleton_iff.mpr h)
    exact ((differentiableAt_riemannZeta hs1).mul (hLd s)).differentiableWithinAt
  have hG : DifferentiableOn ℂ
      (fun s => ∑ Cl : ClassGroup (𝓞 K),
        (mainTermg (formA (A Cl) (C Cl)) (formB m (B Cl) (C Cl)) (formC m (A Cl) (B Cl) (C Cl)) s +
          Eg (formA (A Cl) (C Cl)) (formB m (B Cl) (C Cl)) (formC m (A Cl) (B Cl) (C Cl)) s))
      ({s : ℂ | 1 / 2 < s.re} \ {1}) :=
    DifferentiableOn.fun_sum fun Cl _ => differentiableOn_mainTermg_add_Eg (hpos Cl) (hdpos Cl)
  have hFG : ∀ s : ℂ, 1 < s.re →
      riemannZeta s * DirichletCharacter.LFunction (CN1.Foundations.kroneckerChar m) s =
        ∑ Cl : ClassGroup (𝓞 K),
          (mainTermg (formA (A Cl) (C Cl)) (formB m (B Cl) (C Cl)) (formC m (A Cl) (B Cl) (C Cl)) s +
            Eg (formA (A Cl) (C Cl)) (formB m (B Cl) (C Cl)) (formC m (A Cl) (B Cl) (C Cl)) s) := by
    intro s hs
    rw [← CN1.Epstein.dedekindZeta_eq_riemannZeta_mul_LFunction hα hK hm hs, hZ s hs]
    exact Finset.sum_congr rfl fun Cl _ => CS_main_general (hpos Cl) (hdpos Cl) hs
  have hσ := CN1.CS.eq_at_ofReal_of_differentiableOn_sdiff (a := 1 / 2) (x := σ) (by linarith) hσ1 hF hG hFG
  -- the left side is negative
  have hre := congrArg Complex.re hσ
  obtain ⟨hzim, -, -⟩ := BoundariesOfClass.Analytic.riemannZeta_ofReal_bracket (by linarith : (0 : ℝ) < σ) hσ1.ne
  rw [Complex.mul_re, hzim, zero_mul, sub_zero, Complex.re_sum] at hre
  have hz := BoundariesOfClass.Analytic.riemannZeta_ofReal_re_neg (by linarith : (0 : ℝ) < σ) hσ1
  have hL := CN1.LFunction_ofReal_re_pos_of_seven_eighths_lt_of_isQuadratic (CN1.Foundations.kroneckerChar m)
    (CN1.Foundations.kroneckerChar_isQuadratic m) hχ1 hσ78
  have hleft : (riemannZeta σ).re * (DirichletCharacter.LFunction (CN1.Foundations.kroneckerChar m) σ).re < 0 :=
    mul_neg_of_neg_of_pos hz hL
  -- the right side, class by class
  have h2σ : (0 : ℝ) < 2 * σ - 1 := by linarith
  have h2σ1 : 2 * σ - 1 < 1 := by linarith
  have hZm : (riemannZeta ((2 * σ - 1 : ℝ) : ℂ)).re ≤ 0 :=
    (BoundariesOfClass.Analytic.riemannZeta_ofReal_re_neg h2σ h2σ1).le
  have hZ2 : (13 / 8 : ℝ) ≤ (riemannZeta ((2 * σ : ℝ) : ℂ)).re :=
    BoundariesOfClass.Analytic.thirteen_eighths_le_riemannZeta (by linarith) (by linarith)
  set T : ℝ := coeffR 1 D σ * ((riemannZeta ((2 * σ - 1 : ℝ) : ℂ)).re - 2 * Real.sqrt 2 * BoundariesOfClass.Numerics.kap)
    with hT
  set Z2 : ℝ := (riemannZeta ((2 * σ : ℝ) : ℂ)).re with hZ2def
  have hcl : ∀ Cl : ClassGroup (𝓞 K), formA (A Cl) (C Cl) ^ (-σ) * Z2 + T ≤
      (mainTermg (formA (A Cl) (C Cl)) (formB m (B Cl) (C Cl)) (formC m (A Cl) (B Cl) (C Cl)) σ +
        Eg (formA (A Cl) (C Cl)) (formB m (B Cl) (C Cl)) (formC m (A Cl) (B Cl) (C Cl)) σ).re := fun Cl =>
    re_class_ge_minus hD0 (hdisc Cl) (ha1 Cl) (hamax Cl) (by linarith) hσ1.le hZm
  have hsum := Finset.sum_le_sum fun Cl (_ : Cl ∈ (Finset.univ : Finset (ClassGroup (𝓞 K)))) => hcl Cl
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.sum_mul] at hsum
  set Y : ℝ := (2 / 3 * Real.sqrt D) ^ (-σ) with hYdef
  have hcard : (Fintype.card (ClassGroup (𝓞 K)) : ℝ) = (classNumber K : ℝ) := rfl
  have hone : 1 + ((classNumber K : ℝ) - 1) * Y ≤ ∑ Cl : ClassGroup (𝓞 K), formA (A Cl) (C Cl) ^ (-σ) := by
    have h1 : formA (A 1) (C 1) ^ (-σ) = 1 := by simp [hA1, hC1, formA]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : ClassGroup (𝓞 K))), h1]
    have hs := Finset.card_nsmul_le_sum ((Finset.univ : Finset (ClassGroup (𝓞 K))).erase 1)
      (fun Cl => formA (A Cl) (C Cl) ^ (-σ)) Y
      (fun Cl _ => Real.rpow_le_rpow_of_nonpos (hpos Cl) (hamax Cl) (by linarith))
    rw [nsmul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ] at hs
    have hc1 : 1 ≤ Fintype.card (ClassGroup (𝓞 K)) := Fintype.card_pos
    rw [Nat.cast_sub hc1, Nat.cast_one, hcard] at hs
    linarith
  have hZ20 : 0 ≤ Z2 := by linarith
  rw [hcard] at hsum
  nlinarith [mul_le_mul_of_nonneg_right hone hZ20]

/-- **The class sum at a real point `σ ∈ (7/8, 1)`** (the `y = 0` terms of the non-principal classes dropped). -/
theorem classSum_lt_zero {K : Type*} [Field K] [NumberField K] {m : ℕ} {α : K} (hα : α ^ 2 = -(m : K))
    (hK : Module.finrank ℚ K = 2) (hm : Squarefree m) (hm1 : m ≠ 1) (hm3 : m ≠ 3) {σ : ℝ}
    (hσ78 : 7 / 8 < σ) (hσ1 : σ < 1) :
    (riemannZeta ((2 * σ : ℝ) : ℂ)).re + (classNumber K : ℝ) *
      (coeffR 1 (dOf m) σ * ((riemannZeta ((2 * σ - 1 : ℝ) : ℂ)).re - 2 * Real.sqrt 2 * BoundariesOfClass.Numerics.kap)) < 0 := by
  have h := classSum_lt_zero_y0 hα hK hm hm1 hm3 hσ78 hσ1
  have hZ2 : (13 / 8 : ℝ) ≤ (riemannZeta ((2 * σ : ℝ) : ℂ)).re :=
    BoundariesOfClass.Analytic.thirteen_eighths_le_riemannZeta (by linarith) (by linarith)
  have hh : (1 : ℝ) ≤ (classNumber K : ℝ) := by exact_mod_cast (classNumber_pos (K := K))
  have hY : 0 ≤ (2 / 3 * Real.sqrt (dOf m : ℝ)) ^ (-σ) := Real.rpow_nonneg (by positivity) _
  have : 0 ≤ (riemannZeta ((2 * σ : ℝ) : ℂ)).re * (((classNumber K : ℝ) - 1) * (2 / 3 * Real.sqrt (dOf m)) ^ (-σ)) :=
    mul_nonneg (by linarith) (mul_nonneg (by linarith) hY)
  nlinarith

/-- **The explicit lower bound** (`σ = 1 - 1/log d`). -/
theorem classNumber_ge_explicit {K : Type*} [Field K] [NumberField K] {m : ℕ} {α : K} (hα : α ^ 2 = -(m : K))
    (hK : Module.finrank ℚ K = 2) (hm : Squarefree m) (hm1 : m ≠ 1) (hm3 : m ≠ 3)
    (hd : (2981 : ℝ) ≤ (dOf m : ℝ)) :
    13 / 8 * Real.cos (π / Real.log (dOf m)) * Real.sqrt (dOf m) /
        (π * Real.exp 1 * (Real.log (dOf m) - 1 + 4 * Real.sqrt 2 * BoundariesOfClass.Numerics.kap)) ≤ (classNumber K : ℝ) := by
  set D : ℝ := (dOf m : ℝ) with hDdef
  set L : ℝ := Real.log D with hLdef
  have hL8 : 8 < L := eight_lt_log hd
  have hL0 : 0 < L := by linarith
  set δ : ℝ := 1 / L with hδdef
  have hδ0 : 0 < δ := by positivity
  have hδ8 : δ < 1 / 8 := by rw [hδdef]; exact one_div_lt_one_div_of_lt (by norm_num) hL8
  have hσ78 : 7 / 8 < 1 - δ := by linarith
  have hσ1 : 1 - δ < 1 := by linarith
  have hcore := classSum_lt_zero hα hK hm hm1 hm3 hσ78 hσ1
  rw [← hDdef] at hcore
  -- `ζ(2σ) ≥ 13/8`, `ζ(2σ-1) ≥ -(L-1)/2`
  have hZ2 : (13 / 8 : ℝ) ≤ (riemannZeta ((2 * (1 - δ) : ℝ) : ℂ)).re :=
    BoundariesOfClass.Analytic.thirteen_eighths_le_riemannZeta (by linarith) (by linarith)
  obtain ⟨-, hZm, -⟩ := BoundariesOfClass.Analytic.riemannZeta_ofReal_bracket (show (0 : ℝ) < 2 * (1 - δ) - 1 by linarith)
    (show 2 * (1 - δ) - 1 ≠ 1 by linarith)
  have hZm' : -(L - 1) / 2 ≤ (riemannZeta ((2 * (1 - δ) - 1 : ℝ) : ℂ)).re := by
    have e : 1 / (2 * (1 - δ) - 1 - 1) = -L / 2 := by
      rw [show 2 * (1 - δ) - 1 - 1 = -(2 / L) by rw [hδdef]; ring]
      field_simp
    rw [e] at hZm; linarith
  -- `C₁ ≤ 2π e / (√D cos(πδ))`
  have hD1 : 1 < D := by linarith
  have hC1le := coeffR_one_le_minus (by linarith : 0 < D) hδ0 (by linarith : δ < 1 / 2)
  rw [hδdef, rpow_inv_log hD1, ← hδdef] at hC1le
  have hC1 : 0 < coeffR 1 D (1 - δ) := coeffR_pos one_pos (by linarith) (by linarith)
  have hcos : 0 < Real.cos (π * δ) := BoundariesOfClass.Analytic.cos_pi_mul_pos hδ0 (by linarith)
  have hsD : 0 < Real.sqrt D := Real.sqrt_pos.mpr (by linarith)
  have hkap0 := BoundariesOfClass.Numerics.kap_nonneg
  have hQ : 0 < L - 1 + 4 * Real.sqrt 2 * BoundariesOfClass.Numerics.kap := by
    have := mul_nonneg (Real.sqrt_nonneg 2) hkap0; nlinarith
  set h : ℝ := (classNumber K : ℝ) with hhdef
  have hh0 : 0 ≤ h := Nat.cast_nonneg _
  -- `13/8 < h C₁ (2√2κ - Zm) ≤ h C₁ ((L-1)/2 + 2√2κ)`
  set Zm : ℝ := (riemannZeta ((2 * (1 - δ) - 1 : ℝ) : ℂ)).re
  have step1 : 13 / 8 < h * (coeffR 1 D (1 - δ) * ((L - 1) / 2 + 2 * Real.sqrt 2 * BoundariesOfClass.Numerics.kap)) := by
    have : h * (coeffR 1 D (1 - δ) * (Zm - 2 * Real.sqrt 2 * BoundariesOfClass.Numerics.kap)) ≥
        -(h * (coeffR 1 D (1 - δ) * ((L - 1) / 2 + 2 * Real.sqrt 2 * BoundariesOfClass.Numerics.kap))) := by
      have := mul_le_mul_of_nonneg_left (show -((L - 1) / 2 + 2 * Real.sqrt 2 * BoundariesOfClass.Numerics.kap) ≤
        Zm - 2 * Real.sqrt 2 * BoundariesOfClass.Numerics.kap by linarith) (mul_nonneg hh0 hC1.le)
      nlinarith
    linarith
  have hπ := Real.pi_pos
  have he := Real.exp_pos 1
  have step2 : 13 / 8 < h * (2 * π * Real.exp 1 / (Real.sqrt D * Real.cos (π * δ)) *
      ((L - 1) / 2 + 2 * Real.sqrt 2 * BoundariesOfClass.Numerics.kap)) := by
    have hq : 0 ≤ (L - 1) / 2 + 2 * Real.sqrt 2 * BoundariesOfClass.Numerics.kap := by linarith
    calc (13 / 8 : ℝ) < _ := step1
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hC1le hq) hh0
  have hpd : π * δ = π / L := by rw [hδdef]; ring
  rw [hpd] at step2
  rw [div_le_iff₀ (by positivity)]
  have hcos' : 0 < Real.cos (π / L) := by rw [← hpd]; exact hcos
  have e : h * (2 * π * Real.exp 1 / (Real.sqrt D * Real.cos (π / L)) *
      ((L - 1) / 2 + 2 * Real.sqrt 2 * BoundariesOfClass.Numerics.kap)) =
      h * (π * Real.exp 1 * (L - 1 + 4 * Real.sqrt 2 * BoundariesOfClass.Numerics.kap)) / (Real.sqrt D * Real.cos (π / L)) := by
    field_simp; ring
  rw [e, lt_div_iff₀ (by positivity)] at step2
  nlinarith

/-- **(L) in `dOf m` form:** `(9/50) √d / log d ≤ h` for `d ≥ 2981`. -/
theorem classNumber_ge {K : Type*} [Field K] [NumberField K] {m : ℕ} {α : K} (hα : α ^ 2 = -(m : K))
    (hK : Module.finrank ℚ K = 2) (hm : Squarefree m) (hm1 : m ≠ 1) (hm3 : m ≠ 3)
    (hd : (2981 : ℝ) ≤ (dOf m : ℝ)) :
    9 / 50 * Real.sqrt (dOf m) / Real.log (dOf m) ≤ (classNumber K : ℝ) := by
  refine le_trans ?_ (classNumber_ge_explicit hα hK hm hm1 hm3 hd)
  set D : ℝ := (dOf m : ℝ)
  set L : ℝ := Real.log D
  have hL8 : 8 < L := eight_lt_log hd
  have hL0 : 0 < L := by linarith
  have hnum := BoundariesOfClass.Numerics.lower_numeric hL8.le
  have hcos : 1 - π ^ 2 / (2 * L ^ 2) ≤ Real.cos (π / L) := by
    have := Real.one_sub_sq_div_two_le_cos (x := π / L)
    rw [div_pow] at this
    linarith [show (π ^ 2 / L ^ 2) / 2 = π ^ 2 / (2 * L ^ 2) by ring]
  have hsD : 0 < Real.sqrt D := Real.sqrt_pos.mpr (by linarith)
  have hkap0 := BoundariesOfClass.Numerics.kap_nonneg
  have hQ : 0 < L - 1 + 4 * Real.sqrt 2 * BoundariesOfClass.Numerics.kap := by
    have := mul_nonneg (Real.sqrt_nonneg 2) hkap0; nlinarith
  have hπe : 0 < π * Real.exp 1 := by positivity
  rw [div_le_div_iff₀ hL0 (by positivity)]
  have h2 : 9 / 50 * (π * Real.exp 1 * (L - 1 + 4 * Real.sqrt 2 * BoundariesOfClass.Numerics.kap)) ≤
      13 / 8 * Real.cos (π / L) * L := by
    have := mul_le_mul_of_nonneg_right hcos (show (0 : ℝ) ≤ 13 / 8 * L by positivity)
    nlinarith
  have := mul_le_mul_of_nonneg_left h2 hsD.le
  nlinarith

/-- **The lower bound for a general `δ ∈ (0, 1/8)`** (`σ = 1 - δ`), with every cheap sharpening kept: the `y = 0`
term of every class (`Y = ((2/3)√d)^{-(1-δ)}`), `ζ(2σ) ≥ ζ(2) = π²/6`, the Γ bracket in its `tan` form
(`Ĉ = 2π d^δ sin(πδ)/(√d · πδ cos(πδ)) ≥ C₁`), and `ζ(1-2δ) ≥ -1/(2δ) + 1/2`:
`(π²/6)(1 - Y) < h · (Ĉ (1/(2δ) - 1/2 + 2√2 κ) - (π²/6) Y)`.
No numerics: `δ` is free (for instance `δ = c/log d`, where `d^δ = e^c` by `rpow_div_log`). -/
theorem classNumber_lower_general {K : Type*} [Field K] [NumberField K] {m : ℕ} {α : K} (hα : α ^ 2 = -(m : K))
    (hK : Module.finrank ℚ K = 2) (hm : Squarefree m) (hm1 : m ≠ 1) (hm3 : m ≠ 3) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ8 : δ < 1 / 8) :
    Real.pi ^ 2 / 6 * (1 - (2 / 3 * Real.sqrt (dOf m)) ^ (-(1 - δ))) <
      (classNumber K : ℝ) *
        (2 * π * (dOf m : ℝ) ^ δ * Real.sin (π * δ) / (Real.sqrt (dOf m) * (π * δ * Real.cos (π * δ))) *
            (1 / (2 * δ) - 1 / 2 + 2 * Real.sqrt 2 * BoundariesOfClass.Numerics.kap) -
          Real.pi ^ 2 / 6 * (2 / 3 * Real.sqrt (dOf m)) ^ (-(1 - δ))) := by
  have hcore := classSum_lt_zero_y0 hα hK hm hm1 hm3 (σ := 1 - δ) (by linarith) (by linarith)
  set D : ℝ := (dOf m : ℝ) with hDdef
  have hD0 : 0 < D := dOf_pos hm
  set Y : ℝ := (2 / 3 * Real.sqrt D) ^ (-(1 - δ)) with hYdef
  have hamax1 : 1 ≤ 2 / 3 * Real.sqrt D := HCN.Epstein.one_le_two_thirds_sqrt_dOf hm
  have hY0 : 0 ≤ Y := Real.rpow_nonneg (by linarith) _
  have hY1 : Y ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hamax1 (by linarith)
  have hZ2 : Real.pi ^ 2 / 6 ≤ (riemannZeta ((2 * (1 - δ) : ℝ) : ℂ)).re :=
    BoundariesOfClass.Analytic.pi_sq_div_six_le_riemannZeta (by linarith) (by linarith)
  obtain ⟨-, hZm, -⟩ := BoundariesOfClass.Analytic.riemannZeta_ofReal_bracket
    (show (0 : ℝ) < 2 * (1 - δ) - 1 by linarith) (show 2 * (1 - δ) - 1 ≠ 1 by linarith)
  have e : 1 / (2 * (1 - δ) - 1 - 1) = -(1 / (2 * δ)) := by
    rw [show 2 * (1 - δ) - 1 - 1 = -(2 * δ) by ring, one_div_neg_eq_neg_one_div]
  rw [e] at hZm
  have hZm0 : (riemannZeta ((2 * (1 - δ) - 1 : ℝ) : ℂ)).re ≤ 0 :=
    (BoundariesOfClass.Analytic.riemannZeta_ofReal_re_neg (by linarith) (by linarith)).le
  have hC1le := coeffR_one_le_minus_tan hD0 hδ0 (by linarith)
  have hC1 : 0 < coeffR 1 D (1 - δ) := coeffR_pos one_pos hD0 (by linarith)
  have hkap0 := BoundariesOfClass.Numerics.kap_nonneg
  have hS0 : 0 ≤ Real.sqrt 2 * BoundariesOfClass.Numerics.kap := mul_nonneg (Real.sqrt_nonneg 2) hkap0
  set h : ℝ := (classNumber K : ℝ) with hhdef
  have hh0 : 0 ≤ h := Nat.cast_nonneg _
  set Z2 := (riemannZeta ((2 * (1 - δ) : ℝ) : ℂ)).re
  set Zm := (riemannZeta ((2 * (1 - δ) - 1 : ℝ) : ℂ)).re
  set C1 := coeffR 1 D (1 - δ)
  set Chat := 2 * π * D ^ δ * Real.sin (π * δ) / (Real.sqrt D * (π * δ * Real.cos (π * δ)))
  set k := 2 * Real.sqrt 2 * BoundariesOfClass.Numerics.kap
  have hk0 : 0 ≤ k := by simp only [k]; linarith
  have hChat0 : 0 ≤ Chat := le_trans hC1.le hC1le
  have a1 : Real.pi ^ 2 / 6 * (1 - Y) ≤ Z2 * (1 - Y) := mul_le_mul_of_nonneg_right hZ2 (by linarith)
  have a2 : h * (Real.pi ^ 2 / 6 * Y) ≤ h * (Z2 * Y) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hZ2 hY0) hh0
  have a3 : C1 * (k - Zm) ≤ Chat * (1 / (2 * δ) - 1 / 2 + k) :=
    mul_le_mul hC1le (by linarith) (by linarith) hChat0
  have a4 := mul_le_mul_of_nonneg_left a3 hh0
  have e1 : Z2 * (1 + (h - 1) * Y) = Z2 * (1 - Y) + h * (Z2 * Y) := by ring
  have e2 : h * (C1 * (Zm - k)) = -(h * (C1 * (k - Zm))) := by ring
  rw [e1, e2] at hcore
  have e3 : h * (Chat * (1 / (2 * δ) - 1 / 2 + k) - Real.pi ^ 2 / 6 * Y) =
      h * (Chat * (1 / (2 * δ) - 1 / 2 + k)) - h * (Real.pi ^ 2 / 6 * Y) := by ring
  rw [e3]
  linarith

end BoundariesOfClass.Assembly
