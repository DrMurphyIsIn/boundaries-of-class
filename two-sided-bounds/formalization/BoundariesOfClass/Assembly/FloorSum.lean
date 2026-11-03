import BoundariesOfClass.Assembly.Common
import BoundariesOfClass.Assembly.PerClass
import BoundariesOfClass.Analytic.ZetaNearOne
import BoundariesOfClass.Analytic.Floor
import BoundariesOfClass.CS.RemainderHalf
import CN1.Assembly.Positivity
import CN1.Epstein.Factorization
import CN1.ChowlaSelberg.Continuation

/-!
# BoundariesOfClass.Assembly.FloorSum: the class sum with every class charged its exact floor

Pinned environment: Lean v4.34.1, Mathlib d13f23b. At real `σ ∈ [7/8, 1)`, `δ = 1 - σ`, `ν = σ - 1/2`, with
`C₁ = coeffR 1 d σ`, `Z = ζ(2σ)`, `K = C₁ · (-ζ(2σ - 1))`, `u* = (δK/(σZ))^{δ/(1-2δ)}`, and the full-decay remainder
with parameter `λ ∈ (0, 1/2]` (`C_λ = √(1-λ) π √d`):

* `re_class_ge_floor` (one class, `1 ≤ a ≤ (2/3)√d`): `-(1 - δ/σ) K u* - E_max ≤ re (mainTermg + Eg)(σ)`, where
  `E_max = 2 λ^{-ν} C₁ ((2/3)√d)^{-δ} κ(√(1-λ) · 3π/2)`. The main term is charged its exact minimum over `a`
  (`Analytic.floor_le`), and the remainder its value at the largest `a` (`Analytic.rpow_neg_mul_kappa_mono`).
* `re_class_ge_principal` (`a = 1`): `Z - K - 2 λ^{-ν} C₁ κ(C_λ) ≤ re (mainTermg + Eg)(σ)`.
* `classSum_floor`: `P - (h - 1) m ≤ 0`, with `P = Z - K - 2λ^{-ν} C₁ κ(C_λ)` and `m = (1 - δ/σ) K u* + E_max`.
  The left side `ζ(σ) L(σ, χ)` is `≤ 0`: `ζ(σ) < 0`, and `L(σ, χ) ≥ 0` for `σ ≥ 7/8` (OpenAI's theorem at the real
  point `σ`; at `σ = 7/8` by continuity, CN-1's `LFunction_seven_eighths_nonneg_of_isQuadratic`).

* `classSum_core`, `re_class_ge_floor_half`, `re_class_ge_principal_half`, `classSum_floor_half`: the same with the
  `K_{1/2}` remainder of `BoundariesOfClass.CS.RemainderHalf` (R2).

So `h ≥ 1 + P/m` whenever `m > 0`. No numerics here.
-/

set_option autoImplicit false

open NumberField Ideal Complex Set CN1.Finite HCN.CS HCN.Epstein BoundariesOfClass.CS BoundariesOfClass.Analytic
open scoped nonZeroDivisors Real

namespace BoundariesOfClass.Assembly

/-- `κ_λ(a)` is `κ(C_λ/a)` with `C_λ = √(1-λ) π √D`. -/
lemma kappaL_eq (a D lam : ℝ) : kappaL a D lam = kappa (Real.sqrt (1 - lam) * π * Real.sqrt D / a) := by
  unfold kappaL kappa; ring_nf

/-- **One class, charged its floor.** -/
theorem re_class_ge_floor {a b c D σ lam : ℝ} (hD : 0 < D) (hdisc : disc a b c = D) (ha : 1 ≤ a)
    (hamax : a ≤ 2 / 3 * Real.sqrt D) (hσ : 1 / 2 < σ) (hσ1 : σ < 1) (hl0 : 0 < lam) (hl1 : lam ≤ 1 / 2)
    (hZ : 0 < (riemannZeta ((2 * σ : ℝ) : ℂ)).re) (hZm : (riemannZeta ((2 * σ - 1 : ℝ) : ℂ)).re ≤ 0) :
    -((1 - (1 - σ) / σ) * (coeffR 1 D σ * -(riemannZeta ((2 * σ - 1 : ℝ) : ℂ)).re) *
        ((1 - σ) * (coeffR 1 D σ * -(riemannZeta ((2 * σ - 1 : ℝ) : ℂ)).re) /
          (σ * (riemannZeta ((2 * σ : ℝ) : ℂ)).re)) ^ ((1 - σ) / (1 - 2 * (1 - σ)))) -
      2 * lam ^ (-(σ - 1 / 2)) * coeffR 1 D σ * (2 / 3 * Real.sqrt D) ^ (-(1 - σ)) *
        kappa (Real.sqrt (1 - lam) * (3 * π / 2)) ≤
      (mainTermg a b c σ + Eg a b c σ).re := by
  have ha0 : 0 < a := by linarith
  have hD' : 0 < disc a b c := hdisc ▸ hD
  have hmain := mainTermg_re_ofReal ha0 hD' σ
  have hE := norm_Eg_ofReal_le_lam ha0 hD' hσ hl0 (by linarith)
  rw [hdisc] at hmain hE
  have hC1 : 0 < coeffR 1 D σ := coeffR_pos one_pos hD hσ
  set Z := (riemannZeta ((2 * σ : ℝ) : ℂ)).re
  set Zm := (riemannZeta ((2 * σ - 1 : ℝ) : ℂ)).re
  set K := coeffR 1 D σ * -Zm with hKdef
  have hK0 : 0 ≤ K := mul_nonneg hC1.le (by linarith)
  -- the main term: `a^{-σ} Z + a^{-δ} C₁ Zm = a^{-σ} Z - K a^{-δ} ≥ floor`
  have hca : coeffR a D σ = a ^ (-(1 - σ)) * coeffR 1 D σ := by
    rw [coeffR_eq ha0 hD, show σ - 1 = -(1 - σ) by ring]
  have hfl := floor_le hσ hσ1 hZ hK0 ha0
  have hmain' : (mainTermg a b c σ).re = a ^ (-σ) * Z - K * a ^ (-(1 - σ)) := by
    rw [hmain, hca, hKdef]; ring
  -- the remainder at the largest `a`
  have hsD : 0 < Real.sqrt D := Real.sqrt_pos.mpr hD
  have hsl : 0 < Real.sqrt (1 - lam) := Real.sqrt_pos.mpr (by linarith)
  set Cl := Real.sqrt (1 - lam) * π * Real.sqrt D with hCl
  have hCl0 : 0 < Cl := by positivity
  have hamax0 : 0 < 2 / 3 * Real.sqrt D := by positivity
  have hCa : Cl / (2 / 3 * Real.sqrt D) = Real.sqrt (1 - lam) * (3 * π / 2) := by
    rw [hCl]; field_simp
  have hδC : 1 - σ ≤ Cl / (2 / 3 * Real.sqrt D) := by
    rw [hCa]
    have h1 : (1 : ℝ) / 2 ≤ Real.sqrt (1 - lam) := by
      rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
    nlinarith [Real.pi_gt_three]
  have hmono := rpow_neg_mul_kappa_mono (δ := 1 - σ) (by linarith) (by linarith) hCl0 ha0 hamax hδC
  rw [hCa] at hmono
  have hl : 0 ≤ lam ^ (-(σ - 1 / 2)) := Real.rpow_nonneg hl0.le _
  have hB : BgRL a D σ lam ≤ 2 * lam ^ (-(σ - 1 / 2)) * coeffR 1 D σ * (2 / 3 * Real.sqrt D) ^ (-(1 - σ)) *
      kappa (Real.sqrt (1 - lam) * (3 * π / 2)) := by
    rw [BgRL_eq ha0 hD σ hl0, hca, kappaL_eq, ← hCl]
    have h2 : 0 ≤ 2 * lam ^ (-(σ - 1 / 2)) * coeffR 1 D σ := by positivity
    have := mul_le_mul_of_nonneg_left hmono h2
    nlinarith [this]
  have := re_ge_sub_norm (mainTermg a b c σ) (Eg a b c σ)
  rw [hmain'] at this
  linarith

/-- **The principal class** (`a = 1`). -/
theorem re_class_ge_principal {b c D σ lam : ℝ} (hD : 0 < D) (hdisc : disc 1 b c = D) (hσ : 1 / 2 < σ)
    (hl0 : 0 < lam) (hl1 : lam < 1) :
    (riemannZeta ((2 * σ : ℝ) : ℂ)).re + coeffR 1 D σ * (riemannZeta ((2 * σ - 1 : ℝ) : ℂ)).re -
      2 * lam ^ (-(σ - 1 / 2)) * coeffR 1 D σ * kappa (Real.sqrt (1 - lam) * π * Real.sqrt D) ≤
      (mainTermg 1 b c σ + Eg 1 b c σ).re := by
  have hD' : 0 < disc 1 b c := hdisc ▸ hD
  have hmain := mainTermg_re_ofReal one_pos hD' σ
  have hE := norm_Eg_ofReal_le_lam one_pos hD' hσ hl0 hl1
  rw [hdisc] at hmain hE
  rw [BgRL_eq one_pos hD σ hl0, kappaL_eq, div_one] at hE
  rw [Real.one_rpow, one_mul] at hmain
  have := re_ge_sub_norm (mainTermg 1 b c σ) (Eg 1 b c σ)
  rw [hmain] at this
  nlinarith

/-- `L(σ, χ) ≥ 0` for real `σ ≥ 7/8` and a real non-trivial character. -/
lemma LFunction_ofReal_re_nonneg {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hq : χ.IsQuadratic) (hχ1 : χ ≠ 1)
    {σ : ℝ} (hσ : 7 / 8 ≤ σ) : 0 ≤ (DirichletCharacter.LFunction χ σ).re := by
  rcases eq_or_lt_of_le hσ with h | h
  · rw [← h, show ((7 / 8 : ℝ) : ℂ) = 7 / 8 by push_cast; ring]
    exact (CN1.LFunction_seven_eighths_nonneg_of_isQuadratic χ hq hχ1).2
  · exact (CN1.LFunction_ofReal_re_pos_of_seven_eighths_lt_of_isQuadratic χ hq hχ1 h).le

/-- **The class sum with every class charged its floor**, at real `σ ∈ [7/8, 1)` and `λ ∈ (0, 1/2]`:
`P - (h - 1) m ≤ 0`. -/
theorem classSum_floor {K : Type*} [Field K] [NumberField K] {m : ℕ} {α : K} (hα : α ^ 2 = -(m : K))
    (hK : Module.finrank ℚ K = 2) (hm : Squarefree m) (hm1 : m ≠ 1) (hm3 : m ≠ 3) {σ lam : ℝ}
    (hσ78 : 7 / 8 ≤ σ) (hσ1 : σ < 1) (hl0 : 0 < lam) (hl1 : lam ≤ 1 / 2) :
    ((riemannZeta ((2 * σ : ℝ) : ℂ)).re + coeffR 1 (dOf m) σ * (riemannZeta ((2 * σ - 1 : ℝ) : ℂ)).re -
        2 * lam ^ (-(σ - 1 / 2)) * coeffR 1 (dOf m) σ *
          kappa (Real.sqrt (1 - lam) * π * Real.sqrt (dOf m))) -
      ((classNumber K : ℝ) - 1) *
        ((1 - (1 - σ) / σ) * (coeffR 1 (dOf m) σ * -(riemannZeta ((2 * σ - 1 : ℝ) : ℂ)).re) *
            ((1 - σ) * (coeffR 1 (dOf m) σ * -(riemannZeta ((2 * σ - 1 : ℝ) : ℂ)).re) /
              (σ * (riemannZeta ((2 * σ : ℝ) : ℂ)).re)) ^ ((1 - σ) / (1 - 2 * (1 - σ))) +
          2 * lam ^ (-(σ - 1 / 2)) * coeffR 1 (dOf m) σ * (2 / 3 * Real.sqrt (dOf m)) ^ (-(1 - σ)) *
            kappa (Real.sqrt (1 - lam) * (3 * π / 2))) ≤ 0 := by
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
  -- the left side is `≤ 0`
  have hre := congrArg Complex.re hσ
  obtain ⟨hzim, -, -⟩ := riemannZeta_ofReal_bracket (by linarith : (0 : ℝ) < σ) hσ1.ne
  rw [Complex.mul_re, hzim, zero_mul, sub_zero, Complex.re_sum] at hre
  have hz := riemannZeta_ofReal_re_neg (by linarith : (0 : ℝ) < σ) hσ1
  have hL := LFunction_ofReal_re_nonneg (CN1.Foundations.kroneckerChar m)
    (CN1.Foundations.kroneckerChar_isQuadratic m) hχ1 hσ78
  have hleft : (riemannZeta σ).re * (DirichletCharacter.LFunction (CN1.Foundations.kroneckerChar m) σ).re ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hz.le hL
  -- the right side
  have hZm : (riemannZeta ((2 * σ - 1 : ℝ) : ℂ)).re ≤ 0 :=
    (riemannZeta_ofReal_re_neg (by linarith) (by linarith)).le
  have hZ2 : 0 < (riemannZeta ((2 * σ : ℝ) : ℂ)).re := by
    have := thirteen_eighths_le_riemannZeta (x := 2 * σ) (by linarith) (by linarith); linarith
  set Pv : ℝ := (riemannZeta ((2 * σ : ℝ) : ℂ)).re + coeffR 1 D σ * (riemannZeta ((2 * σ - 1 : ℝ) : ℂ)).re -
    2 * lam ^ (-(σ - 1 / 2)) * coeffR 1 D σ * kappa (Real.sqrt (1 - lam) * π * Real.sqrt D) with hPv
  set Mv : ℝ := (1 - (1 - σ) / σ) * (coeffR 1 D σ * -(riemannZeta ((2 * σ - 1 : ℝ) : ℂ)).re) *
      ((1 - σ) * (coeffR 1 D σ * -(riemannZeta ((2 * σ - 1 : ℝ) : ℂ)).re) /
        (σ * (riemannZeta ((2 * σ : ℝ) : ℂ)).re)) ^ ((1 - σ) / (1 - 2 * (1 - σ))) +
    2 * lam ^ (-(σ - 1 / 2)) * coeffR 1 D σ * (2 / 3 * Real.sqrt D) ^ (-(1 - σ)) *
      kappa (Real.sqrt (1 - lam) * (3 * π / 2)) with hMv
  set f : ClassGroup (𝓞 K) → ℝ := fun Cl =>
    (mainTermg (formA (A Cl) (C Cl)) (formB m (B Cl) (C Cl)) (formC m (A Cl) (B Cl) (C Cl)) σ +
      Eg (formA (A Cl) (C Cl)) (formB m (B Cl) (C Cl)) (formC m (A Cl) (B Cl) (C Cl)) σ).re with hf
  have hcl : ∀ Cl, -Mv ≤ f Cl := fun Cl => by
    have := re_class_ge_floor hD0 (hdisc Cl) (ha1 Cl) (hamax Cl) (by linarith) hσ1 hl0 hl1 hZ2 hZm
    simp only [hf, hMv]; linarith
  have hprin : Pv ≤ f 1 := by
    have hA : formA (A 1) (C 1) = 1 := by simp [hA1, hC1, formA]
    have h := re_class_ge_principal (b := formB m (B 1) (C 1)) (c := formC m (A 1) (B 1) (C 1)) hD0
      (by rw [← hA]; exact hdisc 1) (by linarith : (1 : ℝ) / 2 < σ) hl0 (by linarith)
    simp only [hf, hPv]
    rw [hA]; exact h
  have hsum : Pv + ((classNumber K : ℝ) - 1) * (-Mv) ≤ ∑ Cl : ClassGroup (𝓞 K), f Cl := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : ClassGroup (𝓞 K)))]
    have hs := Finset.card_nsmul_le_sum ((Finset.univ : Finset (ClassGroup (𝓞 K))).erase 1) f (-Mv)
      (fun Cl _ => hcl Cl)
    rw [nsmul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ] at hs
    have hc1 : 1 ≤ Fintype.card (ClassGroup (𝓞 K)) := Fintype.card_pos
    have hcard : (Fintype.card (ClassGroup (𝓞 K)) : ℝ) = (classNumber K : ℝ) := rfl
    rw [Nat.cast_sub hc1, Nat.cast_one, hcard] at hs
    linarith
  have hre' : ∑ Cl : ClassGroup (𝓞 K), f Cl =
      (riemannZeta σ).re * (DirichletCharacter.LFunction (CN1.Foundations.kroneckerChar m) σ).re := by
    rw [hre]
  have : Pv - ((classNumber K : ℝ) - 1) * Mv ≤ 0 := by nlinarith
  exact this

/-! ### The same with the `K_{1/2}` remainder (R2) -/

/-- **The class sum at real `σ ∈ [7/8, 1)`, structural form:** Hermite representatives with `disc = d`,
`1 ≤ a ≤ (2/3)√d`, principal `a = 1`, and `Σ_Cl re (mainTermg + Eg)(σ) ≤ 0`. -/
theorem classSum_core {K : Type*} [Field K] [NumberField K] {m : ℕ} {α : K} (hα : α ^ 2 = -(m : K))
    (hK : Module.finrank ℚ K = 2) (hm : Squarefree m) (hm1 : m ≠ 1) (hm3 : m ≠ 3) {σ : ℝ}
    (hσ78 : 7 / 8 ≤ σ) (hσ1 : σ < 1) :
    ∃ A B C : ClassGroup (𝓞 K) → ℤ,
      (∀ Cl, HCN.CS.disc (formA (A Cl) (C Cl)) (formB m (B Cl) (C Cl)) (formC m (A Cl) (B Cl) (C Cl)) = dOf m) ∧
      (∀ Cl, 1 ≤ formA (A Cl) (C Cl)) ∧ (∀ Cl, formA (A Cl) (C Cl) ≤ 2 / 3 * Real.sqrt (dOf m)) ∧
      formA (A 1) (C 1) = 1 ∧
      ∑ Cl : ClassGroup (𝓞 K),
        (mainTermg (formA (A Cl) (C Cl)) (formB m (B Cl) (C Cl)) (formC m (A Cl) (B Cl) (C Cl)) σ +
          Eg (formA (A Cl) (C Cl)) (formB m (B Cl) (C Cl)) (formC m (A Cl) (B Cl) (C Cl)) σ).re ≤ 0 := by
  classical
  obtain ⟨J, A, B, C, -, hH, ⟨-, hA1, -, hC1⟩, hN, hZ⟩ := exists_classReps hα hK hm hm1 hm3
  have hD0 := dOf_pos hm
  have hdisc : ∀ Cl, HCN.CS.disc (formA (A Cl) (C Cl)) (formB m (B Cl) (C Cl)) (formC m (A Cl) (B Cl) (C Cl))
      = dOf m := fun Cl => disc_form m (hH Cl).A_pos.ne' (hH Cl).C_pos.ne'
  have ha1 : ∀ Cl, 1 ≤ formA (A Cl) (C Cl) := fun Cl => (hH Cl).one_le_formA hα hK hm
  have hamax : ∀ Cl, formA (A Cl) (C Cl) ≤ 2 / 3 * Real.sqrt (dOf m) :=
    fun Cl => ((hH Cl).formA_le_absNorm hα hK hm).trans (hN Cl)
  have hpos : ∀ Cl, 0 < formA (A Cl) (C Cl) := fun Cl => by linarith [ha1 Cl]
  have hdpos : ∀ Cl, 0 < HCN.CS.disc (formA (A Cl) (C Cl)) (formB m (B Cl) (C Cl))
      (formC m (A Cl) (B Cl) (C Cl)) := fun Cl => by rw [hdisc]; exact hD0
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
  have hre := congrArg Complex.re hσ
  obtain ⟨hzim, -, -⟩ := riemannZeta_ofReal_bracket (by linarith : (0 : ℝ) < σ) hσ1.ne
  rw [Complex.mul_re, hzim, zero_mul, sub_zero, Complex.re_sum] at hre
  have hz := riemannZeta_ofReal_re_neg (by linarith : (0 : ℝ) < σ) hσ1
  have hL := LFunction_ofReal_re_nonneg (CN1.Foundations.kroneckerChar m)
    (CN1.Foundations.kroneckerChar_isQuadratic m) hχ1 hσ78
  have hleft : (riemannZeta σ).re * (DirichletCharacter.LFunction (CN1.Foundations.kroneckerChar m) σ).re ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hz.le hL
  refine ⟨A, B, C, hdisc, ha1, hamax, by simp [hA1, hC1, formA], ?_⟩
  rw [← hre]; exact hleft

/-- **One class, charged its floor, with the `K_{1/2}` remainder.** `E₂ = (2π^σ/Γ(σ)) (2/√d)^σ κ(3π/2)`. -/
theorem re_class_ge_floor_half {a b c D σ : ℝ} (hD : 0 < D) (hdisc : disc a b c = D) (ha : 1 ≤ a)
    (hamax : a ≤ 2 / 3 * Real.sqrt D) (hσ : 1 / 2 < σ) (hσ1 : σ < 1)
    (hZ : 0 < (riemannZeta ((2 * σ : ℝ) : ℂ)).re) (hZm : (riemannZeta ((2 * σ - 1 : ℝ) : ℂ)).re ≤ 0) :
    -((1 - (1 - σ) / σ) * (coeffR 1 D σ * -(riemannZeta ((2 * σ - 1 : ℝ) : ℂ)).re) *
        ((1 - σ) * (coeffR 1 D σ * -(riemannZeta ((2 * σ - 1 : ℝ) : ℂ)).re) /
          (σ * (riemannZeta ((2 * σ : ℝ) : ℂ)).re)) ^ ((1 - σ) / (1 - 2 * (1 - σ)))) -
      2 * π ^ σ / Real.Gamma σ * (2 / Real.sqrt D) ^ σ * kappa (3 * π / 2) ≤
      (mainTermg a b c σ + Eg a b c σ).re := by
  have ha0 : 0 < a := by linarith
  have hD' : 0 < disc a b c := hdisc ▸ hD
  have hmain := mainTermg_re_ofReal ha0 hD' σ
  have hE := norm_Eg_ofReal_le_half_max ha0 hD' (hdisc ▸ hamax) hσ hσ1.le
  rw [hdisc] at hmain hE
  have hC1 : 0 < coeffR 1 D σ := coeffR_pos one_pos hD hσ
  set Z := (riemannZeta ((2 * σ : ℝ) : ℂ)).re
  set Zm := (riemannZeta ((2 * σ - 1 : ℝ) : ℂ)).re
  set K := coeffR 1 D σ * -Zm with hKdef
  have hK0 : 0 ≤ K := mul_nonneg hC1.le (by linarith)
  have hca : coeffR a D σ = a ^ (-(1 - σ)) * coeffR 1 D σ := by
    rw [coeffR_eq ha0 hD, show σ - 1 = -(1 - σ) by ring]
  have hfl := floor_le hσ hσ1 hZ hK0 ha0
  have hmain' : (mainTermg a b c σ).re = a ^ (-σ) * Z - K * a ^ (-(1 - σ)) := by
    rw [hmain, hca, hKdef]; ring
  have := re_ge_sub_norm (mainTermg a b c σ) (Eg a b c σ)
  rw [hmain'] at this
  linarith

/-- **The principal class with the `K_{1/2}` remainder.** -/
theorem re_class_ge_principal_half {b c D σ : ℝ} (hD : 0 < D) (hdisc : disc 1 b c = D) (hσ : 1 / 2 < σ)
    (hσ1 : σ ≤ 1) :
    (riemannZeta ((2 * σ : ℝ) : ℂ)).re + coeffR 1 D σ * (riemannZeta ((2 * σ - 1 : ℝ) : ℂ)).re -
      2 * π ^ σ / Real.Gamma σ * (2 / Real.sqrt D) ^ σ * kappa (π * Real.sqrt D) ≤
      (mainTermg 1 b c σ + Eg 1 b c σ).re := by
  have hD' : 0 < disc 1 b c := hdisc ▸ hD
  have hmain := mainTermg_re_ofReal one_pos hD' σ
  have hE := norm_Eg_ofReal_le_half one_pos hD' hσ hσ1
  rw [hdisc, div_one] at hE
  rw [hdisc, Real.one_rpow, one_mul] at hmain
  have := re_ge_sub_norm (mainTermg 1 b c σ) (Eg 1 b c σ)
  rw [hmain] at this
  linarith

/-- **The class sum with every class charged its floor, `K_{1/2}` remainder (R2)**, real `σ ∈ [7/8, 1)`:
`P₂ - (h - 1) m₂ ≤ 0`, `P₂ = Z - K - E₂(1)`, `m₂ = (1 - δ/σ) K u* + E₂`, with `E₂(1) = (2π^σ/Γ(σ))(2/√d)^σ κ(π√d)` and
`E₂ = (2π^σ/Γ(σ))(2/√d)^σ κ(3π/2)`. -/
theorem classSum_floor_half {K : Type*} [Field K] [NumberField K] {m : ℕ} {α : K} (hα : α ^ 2 = -(m : K))
    (hK : Module.finrank ℚ K = 2) (hm : Squarefree m) (hm1 : m ≠ 1) (hm3 : m ≠ 3) {σ : ℝ}
    (hσ78 : 7 / 8 ≤ σ) (hσ1 : σ < 1) :
    ((riemannZeta ((2 * σ : ℝ) : ℂ)).re + coeffR 1 (dOf m) σ * (riemannZeta ((2 * σ - 1 : ℝ) : ℂ)).re -
        2 * π ^ σ / Real.Gamma σ * (2 / Real.sqrt (dOf m)) ^ σ * kappa (π * Real.sqrt (dOf m))) -
      ((classNumber K : ℝ) - 1) *
        ((1 - (1 - σ) / σ) * (coeffR 1 (dOf m) σ * -(riemannZeta ((2 * σ - 1 : ℝ) : ℂ)).re) *
            ((1 - σ) * (coeffR 1 (dOf m) σ * -(riemannZeta ((2 * σ - 1 : ℝ) : ℂ)).re) /
              (σ * (riemannZeta ((2 * σ : ℝ) : ℂ)).re)) ^ ((1 - σ) / (1 - 2 * (1 - σ))) +
          2 * π ^ σ / Real.Gamma σ * (2 / Real.sqrt (dOf m)) ^ σ * kappa (3 * π / 2)) ≤ 0 := by
  classical
  obtain ⟨A, B, C, hdisc, ha1, hamax, hA1, hsum0⟩ := classSum_core hα hK hm hm1 hm3 hσ78 hσ1
  have hD0 := dOf_pos hm
  have hZm : (riemannZeta ((2 * σ - 1 : ℝ) : ℂ)).re ≤ 0 :=
    (riemannZeta_ofReal_re_neg (by linarith) (by linarith)).le
  have hZ2 : 0 < (riemannZeta ((2 * σ : ℝ) : ℂ)).re := by
    have := thirteen_eighths_le_riemannZeta (x := 2 * σ) (by linarith) (by linarith); linarith
  set f : ClassGroup (𝓞 K) → ℝ := fun Cl =>
    (mainTermg (formA (A Cl) (C Cl)) (formB m (B Cl) (C Cl)) (formC m (A Cl) (B Cl) (C Cl)) σ +
      Eg (formA (A Cl) (C Cl)) (formB m (B Cl) (C Cl)) (formC m (A Cl) (B Cl) (C Cl)) σ).re with hf
  set Pv := (riemannZeta ((2 * σ : ℝ) : ℂ)).re + coeffR 1 (dOf m) σ * (riemannZeta ((2 * σ - 1 : ℝ) : ℂ)).re -
    2 * π ^ σ / Real.Gamma σ * (2 / Real.sqrt (dOf m)) ^ σ * kappa (π * Real.sqrt (dOf m)) with hPv
  set Mv := (1 - (1 - σ) / σ) * (coeffR 1 (dOf m) σ * -(riemannZeta ((2 * σ - 1 : ℝ) : ℂ)).re) *
      ((1 - σ) * (coeffR 1 (dOf m) σ * -(riemannZeta ((2 * σ - 1 : ℝ) : ℂ)).re) /
        (σ * (riemannZeta ((2 * σ : ℝ) : ℂ)).re)) ^ ((1 - σ) / (1 - 2 * (1 - σ))) +
    2 * π ^ σ / Real.Gamma σ * (2 / Real.sqrt (dOf m)) ^ σ * kappa (3 * π / 2) with hMv
  have hcl : ∀ Cl, -Mv ≤ f Cl := fun Cl => by
    have := re_class_ge_floor_half hD0 (hdisc Cl) (ha1 Cl) (hamax Cl) (by linarith) hσ1 hZ2 hZm
    simp only [hf, hMv]; linarith
  have hprin : Pv ≤ f 1 := by
    have h := re_class_ge_principal_half (b := formB m (B 1) (C 1)) (c := formC m (A 1) (B 1) (C 1)) hD0
      (by rw [← hA1]; exact hdisc 1) (by linarith : (1 : ℝ) / 2 < σ) hσ1.le
    simp only [hf, hPv]
    rw [hA1]; exact h
  have hsum : Pv + ((classNumber K : ℝ) - 1) * (-Mv) ≤ ∑ Cl : ClassGroup (𝓞 K), f Cl := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : ClassGroup (𝓞 K)))]
    have hs := Finset.card_nsmul_le_sum ((Finset.univ : Finset (ClassGroup (𝓞 K))).erase 1) f (-Mv)
      (fun Cl _ => hcl Cl)
    rw [nsmul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ] at hs
    have hc1 : 1 ≤ Fintype.card (ClassGroup (𝓞 K)) := Fintype.card_pos
    have hcard : (Fintype.card (ClassGroup (𝓞 K)) : ℝ) = (classNumber K : ℝ) := rfl
    rw [Nat.cast_sub hc1, Nat.cast_one, hcard] at hs
    linarith
  have h0 : ∑ Cl : ClassGroup (𝓞 K), f Cl ≤ 0 := hsum0
  nlinarith

end BoundariesOfClass.Assembly
