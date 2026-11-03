import BoundariesOfClass.Assembly.Common
import BoundariesOfClass.Assembly.PerClass
import BoundariesOfClass.Analytic.ZetaNearOne
import CN1.Epstein.Factorization

/-!
# BoundariesOfClass.Assembly.Upper: the explicit upper bound `h ≤ (6/5) √d log d`, in CN-1's `dOf m` vocabulary

Pinned environment: Lean v4.34.1, Mathlib d13f23b. **No zero-free region and no continuation:** everything is on
`re s > 1`, where `ζ_K = ζ · L = Σ_Cl ½ Z_{Q_Cl}` holds outright (CN-1's factorisation, HCN's class partition and
general Chowla–Selberg). This module does not import CN-1's Positivity (the module that uses OpenAI's theorem).

* `classSum_le_sq` (any real `σ > 1`): with `C₁ = coeffR 1 d σ`,
  `h · C₁ (re ζ(2σ-1) - 2·2^{σ-1/2} κ (√d)^{σ-1}) ≤ (re ζ(σ))²`, since `re (ζ(σ) L(σ, χ)) ≤ ζ(σ) ‖L(σ, χ)‖ ≤ ζ(σ)²`.
* `classNumber_le_explicit` (`d ≥ 2981`, `σ = 1 + 1/log d`):
  `h · (π(L+1)/e - 4√2 π (1+1/L)³ κ/√e) / √d ≤ (L + 1/2 + (1+1/L)(3+1/L)/8)²`.
* `classNumber_le` (`d ≥ 2981`): `h ≤ (6/5) √d log d`, by `BoundariesOfClass.Numerics.upper_numeric`.

-/

set_option autoImplicit false

open NumberField Ideal Complex Set CN1.Finite HCN.CS HCN.Epstein BoundariesOfClass.CS
open scoped nonZeroDivisors Real

namespace BoundariesOfClass.Assembly

/-- **The class sum at a real point `σ > 1`.** -/
theorem classSum_le_sq {K : Type*} [Field K] [NumberField K] {m : ℕ} {α : K} (hα : α ^ 2 = -(m : K))
    (hK : Module.finrank ℚ K = 2) (hm : Squarefree m) (hm1 : m ≠ 1) (hm3 : m ≠ 3) {σ : ℝ} (hσ1 : 1 < σ) :
    (classNumber K : ℝ) * (coeffR 1 (dOf m) σ * ((riemannZeta ((2 * σ - 1 : ℝ) : ℂ)).re -
        2 * (2 : ℝ) ^ (σ - 1 / 2) * BoundariesOfClass.Numerics.kap * Real.sqrt (dOf m) ^ (σ - 1))) ≤
      (riemannZeta σ).re ^ 2 := by
  classical
  obtain ⟨J, A, B, C, -, hH, -, hN, hZ⟩ := exists_classReps hα hK hm hm1 hm3
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
  have : NeZero (CN1.Foundations.disc m) := ⟨CN1.Epstein.disc_ne_zero hm.ne_zero⟩
  have hs : 1 < (σ : ℂ).re := by simpa using hσ1
  -- `ζ(σ) L(σ) = Σ_Cl (mainTermg + Eg)(σ)` directly on `re s > 1`
  have hid : riemannZeta σ * DirichletCharacter.LFunction (CN1.Foundations.kroneckerChar m) σ =
      ∑ Cl : ClassGroup (𝓞 K),
        (mainTermg (formA (A Cl) (C Cl)) (formB m (B Cl) (C Cl)) (formC m (A Cl) (B Cl) (C Cl)) σ +
          Eg (formA (A Cl) (C Cl)) (formB m (B Cl) (C Cl)) (formC m (A Cl) (B Cl) (C Cl)) σ) := by
    rw [← CN1.Epstein.dedekindZeta_eq_riemannZeta_mul_LFunction hα hK hm hs, hZ σ hs]
    exact Finset.sum_congr rfl fun Cl _ => CS_main_general (hpos Cl) (hdpos Cl) hs
  have hre := congrArg Complex.re hid
  rw [Complex.re_sum] at hre
  -- the left side is at most `ζ(σ)²`
  obtain ⟨hzim, hzlo, -⟩ := BoundariesOfClass.Analytic.riemannZeta_ofReal_bracket (by linarith : (0 : ℝ) < σ) hσ1.ne'
  have hz0 : 0 ≤ (riemannZeta σ).re := by
    have : 0 < 1 / (σ - 1) := one_div_pos.mpr (by linarith)
    linarith
  have hnz : ‖riemannZeta σ‖ = (riemannZeta σ).re := by
    rw [← Complex.re_add_im (riemannZeta σ), hzim]
    simp [Complex.norm_real, abs_of_nonneg hz0]
  have hLn := BoundariesOfClass.Analytic.norm_LFunction_le_riemannZeta (CN1.Foundations.kroneckerChar m) hσ1
  have hleft : (riemannZeta σ * DirichletCharacter.LFunction (CN1.Foundations.kroneckerChar m) σ).re ≤
      (riemannZeta σ).re ^ 2 := by
    calc _ ≤ ‖riemannZeta σ * DirichletCharacter.LFunction (CN1.Foundations.kroneckerChar m) σ‖ :=
          Complex.re_le_norm _
      _ = (riemannZeta σ).re * ‖DirichletCharacter.LFunction (CN1.Foundations.kroneckerChar m) σ‖ := by
          rw [norm_mul, hnz]
      _ ≤ (riemannZeta σ).re * (riemannZeta σ).re := mul_le_mul_of_nonneg_left hLn hz0
      _ = _ := by ring
  -- the right side, class by class
  obtain ⟨-, hZ2lo, -⟩ := BoundariesOfClass.Analytic.riemannZeta_ofReal_bracket (show (0 : ℝ) < 2 * σ by linarith)
    (show 2 * σ ≠ 1 by linarith)
  obtain ⟨-, hZplo, -⟩ := BoundariesOfClass.Analytic.riemannZeta_ofReal_bracket (show (0 : ℝ) < 2 * σ - 1 by linarith)
    (show 2 * σ - 1 ≠ 1 by linarith)
  have hZ2 : 0 ≤ (riemannZeta ((2 * σ : ℝ) : ℂ)).re := by
    have : 0 < 1 / (2 * σ - 1) := one_div_pos.mpr (by linarith)
    linarith
  have hZp : 0 ≤ (riemannZeta ((2 * σ - 1 : ℝ) : ℂ)).re := by
    have : 0 < 1 / (2 * σ - 1 - 1) := one_div_pos.mpr (by linarith)
    linarith
  set X : ℝ := coeffR 1 D σ * ((riemannZeta ((2 * σ - 1 : ℝ) : ℂ)).re -
    2 * (2 : ℝ) ^ (σ - 1 / 2) * BoundariesOfClass.Numerics.kap * Real.sqrt D ^ (σ - 1)) with hX
  have hcl : ∀ Cl : ClassGroup (𝓞 K), X ≤
      (mainTermg (formA (A Cl) (C Cl)) (formB m (B Cl) (C Cl)) (formC m (A Cl) (B Cl) (C Cl)) σ +
        Eg (formA (A Cl) (C Cl)) (formB m (B Cl) (C Cl)) (formC m (A Cl) (B Cl) (C Cl)) σ).re := fun Cl =>
    re_class_ge_plus hD0 (hdisc Cl) (ha1 Cl) (hamax Cl) hσ1.le hZ2 hZp
  have hsum := Finset.sum_le_sum fun Cl (_ : Cl ∈ (Finset.univ : Finset (ClassGroup (𝓞 K)))) => hcl Cl
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have hcard : (Fintype.card (ClassGroup (𝓞 K)) : ℝ) = (classNumber K : ℝ) := rfl
  rw [hcard] at hsum
  linarith

/-- **The explicit upper bound** (`σ = 1 + 1/log d`). -/
theorem classNumber_le_explicit {K : Type*} [Field K] [NumberField K] {m : ℕ} {α : K} (hα : α ^ 2 = -(m : K))
    (hK : Module.finrank ℚ K = 2) (hm : Squarefree m) (hm1 : m ≠ 1) (hm3 : m ≠ 3)
    (hd : (2981 : ℝ) ≤ (dOf m : ℝ)) :
    (classNumber K : ℝ) * ((π * (Real.log (dOf m) + 1) / Real.exp 1 -
        4 * Real.sqrt 2 * π * (1 + 1 / Real.log (dOf m)) ^ 3 * BoundariesOfClass.Numerics.kap / Real.sqrt (Real.exp 1)) /
          Real.sqrt (dOf m)) ≤
      (Real.log (dOf m) + 1 / 2 + (1 + 1 / Real.log (dOf m)) * (3 + 1 / Real.log (dOf m)) / 8) ^ 2 := by
  set D : ℝ := (dOf m : ℝ) with hDdef
  set L : ℝ := Real.log D with hLdef
  have hL8 : 8 < L := eight_lt_log hd
  have hL0 : 0 < L := by linarith
  set δ : ℝ := 1 / L with hδdef
  have hδ0 : 0 < δ := by positivity
  have hδ8 : δ < 1 / 8 := by rw [hδdef]; exact one_div_lt_one_div_of_lt (by norm_num) hL8
  have hcore := classSum_le_sq hα hK hm hm1 hm3 (show 1 < 1 + δ by linarith)
  rw [← hDdef] at hcore
  have hD1 : 1 < D := by linarith
  have hD0 : 0 < D := by linarith
  have hsD : 0 < Real.sqrt D := Real.sqrt_pos.mpr hD0
  have he := Real.exp_pos 1
  have hse : 0 < Real.sqrt (Real.exp 1) := Real.sqrt_pos.mpr he
  have hee : Real.sqrt (Real.exp 1) * Real.sqrt (Real.exp 1) = Real.exp 1 := Real.mul_self_sqrt he.le
  -- `D^{-δ} = 1/e`, `(√D)^δ = √e`
  have hDδ : D ^ δ = Real.exp 1 := by rw [hδdef]; exact rpow_inv_log hD1
  have hDmδ : D ^ (-δ) = (Real.exp 1)⁻¹ := by rw [Real.rpow_neg hD0.le, hDδ]
  have hsDδ : Real.sqrt D ^ ((1 + δ) - 1) = Real.sqrt (Real.exp 1) := by
    rw [show (1 + δ) - 1 = δ by ring, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hD0.le,
      mul_comm, Real.rpow_mul hD0.le, hDδ]
  -- `ζ(σ) ≤ L + 1/2 + (1+δ)(3+δ)/8`, `ζ(2σ-1) ≥ (L+1)/2`
  obtain ⟨-, hzlo, hzhi⟩ := BoundariesOfClass.Analytic.riemannZeta_ofReal_bracket (show (0 : ℝ) < 1 + δ by linarith)
    (show 1 + δ ≠ 1 by linarith)
  have hz1 : 1 / (1 + δ - 1) = L := by rw [show 1 + δ - 1 = δ by ring, hδdef, one_div_one_div]
  rw [hz1] at hzlo hzhi
  obtain ⟨-, hZplo, -⟩ := BoundariesOfClass.Analytic.riemannZeta_ofReal_bracket (show (0 : ℝ) < 2 * (1 + δ) - 1 by linarith)
    (show 2 * (1 + δ) - 1 ≠ 1 by linarith)
  have hz2 : 1 / (2 * (1 + δ) - 1 - 1) = L / 2 := by
    rw [show 2 * (1 + δ) - 1 - 1 = 2 * δ by ring, hδdef]; field_simp
  rw [hz2] at hZplo
  -- `C₁` brackets
  have hC1lo := coeffR_one_ge_plus hD0 hδ0.le
  have hC1hi := coeffR_one_le_plus hD0 hδ0.le (by linarith)
  rw [hDmδ] at hC1lo hC1hi
  have hC1 : 0 < coeffR 1 D (1 + δ) := coeffR_pos one_pos hD0 (by linarith)
  -- `2^{σ-1/2} ≤ √2 (1+δ)`
  have h2 : (2 : ℝ) ^ ((1 + δ) - 1 / 2) ≤ Real.sqrt 2 * (1 + δ) := by
    rw [show (1 + δ) - 1 / 2 = 1 / 2 + δ by ring, Real.rpow_add (by norm_num), ← Real.sqrt_eq_rpow]
    have hb := rpow_one_add_le_one_add_mul_self (s := 1) (by norm_num) hδ0.le (by linarith)
    rw [show (1 : ℝ) + 1 = 2 by norm_num, mul_one] at hb
    exact mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg 2)
  have hkap0 := BoundariesOfClass.Numerics.kap_nonneg
  set h : ℝ := (classNumber K : ℝ) with hhdef
  have hh0 : 0 ≤ h := Nat.cast_nonneg _
  set Zp : ℝ := (riemannZeta ((2 * (1 + δ) - 1 : ℝ) : ℂ)).re
  -- the bracket `X ≥ B/√D`
  have hrem : 2 * (2 : ℝ) ^ ((1 + δ) - 1 / 2) * BoundariesOfClass.Numerics.kap * Real.sqrt D ^ ((1 + δ) - 1) ≤
      2 * (Real.sqrt 2 * (1 + δ)) * BoundariesOfClass.Numerics.kap * Real.sqrt (Real.exp 1) := by
    rw [hsDδ]
    have := mul_le_mul_of_nonneg_right h2 (show 0 ≤ 2 * BoundariesOfClass.Numerics.kap * Real.sqrt (Real.exp 1) by positivity)
    nlinarith
  have hX : (π * (L + 1) / Real.exp 1 - 4 * Real.sqrt 2 * π * (1 + δ) ^ 3 * BoundariesOfClass.Numerics.kap /
      Real.sqrt (Real.exp 1)) / Real.sqrt D ≤
      coeffR 1 D (1 + δ) * (Zp - 2 * (2 : ℝ) ^ ((1 + δ) - 1 / 2) * BoundariesOfClass.Numerics.kap *
        Real.sqrt D ^ ((1 + δ) - 1)) := by
    have hZp0 : 0 ≤ (L + 1) / 2 := by linarith
    have hA : 2 * π * (Real.exp 1)⁻¹ / Real.sqrt D * ((L + 1) / 2) ≤ coeffR 1 D (1 + δ) * Zp :=
      mul_le_mul hC1lo (by linarith) hZp0 hC1.le
    have hR0 : 0 ≤ 2 * (Real.sqrt 2 * (1 + δ)) * BoundariesOfClass.Numerics.kap * Real.sqrt (Real.exp 1) := by positivity
    have hB : coeffR 1 D (1 + δ) * (2 * (2 : ℝ) ^ ((1 + δ) - 1 / 2) * BoundariesOfClass.Numerics.kap *
        Real.sqrt D ^ ((1 + δ) - 1)) ≤
        2 * π * (1 + δ) ^ 2 * (Real.exp 1)⁻¹ / Real.sqrt D *
          (2 * (Real.sqrt 2 * (1 + δ)) * BoundariesOfClass.Numerics.kap * Real.sqrt (Real.exp 1)) :=
      mul_le_mul hC1hi hrem (by rw [hsDδ]; positivity) (by positivity)
    have e1 : (π * (L + 1) / Real.exp 1 - 4 * Real.sqrt 2 * π * (1 + δ) ^ 3 * BoundariesOfClass.Numerics.kap /
        Real.sqrt (Real.exp 1)) / Real.sqrt D =
        2 * π * (Real.exp 1)⁻¹ / Real.sqrt D * ((L + 1) / 2) -
          2 * π * (1 + δ) ^ 2 * (Real.exp 1)⁻¹ / Real.sqrt D *
            (2 * (Real.sqrt 2 * (1 + δ)) * BoundariesOfClass.Numerics.kap * Real.sqrt (Real.exp 1)) := by
      clear_value D L δ
      set s := Real.sqrt (Real.exp 1) with hs
      rw [← hee]
      field_simp
      ring
    rw [e1, mul_sub]
    linarith
  -- assemble
  have hfin : h * ((π * (L + 1) / Real.exp 1 - 4 * Real.sqrt 2 * π * (1 + δ) ^ 3 * BoundariesOfClass.Numerics.kap /
      Real.sqrt (Real.exp 1)) / Real.sqrt D) ≤ (riemannZeta ((1 + δ : ℝ) : ℂ)).re ^ 2 :=
    le_trans (mul_le_mul_of_nonneg_left hX hh0) hcore
  have hz0 : 0 ≤ (riemannZeta ((1 + δ : ℝ) : ℂ)).re := by linarith
  have hsq : (riemannZeta ((1 + δ : ℝ) : ℂ)).re ^ 2 ≤ (L + 1 / 2 + (1 + δ) * (3 + δ) / 8) ^ 2 := by
    apply pow_le_pow_left₀ hz0
    have : (1 + δ) * (1 + δ + 2) / 8 = (1 + δ) * (3 + δ) / 8 := by ring
    linarith
  linarith

/-- **(U) in `dOf m` form:** `h ≤ (6/5) √d log d` for `d ≥ 2981`. -/
theorem classNumber_le {K : Type*} [Field K] [NumberField K] {m : ℕ} {α : K} (hα : α ^ 2 = -(m : K))
    (hK : Module.finrank ℚ K = 2) (hm : Squarefree m) (hm1 : m ≠ 1) (hm3 : m ≠ 3)
    (hd : (2981 : ℝ) ≤ (dOf m : ℝ)) :
    (classNumber K : ℝ) ≤ 6 / 5 * Real.sqrt (dOf m) * Real.log (dOf m) := by
  have hex := classNumber_le_explicit hα hK hm hm1 hm3 hd
  set D : ℝ := (dOf m : ℝ)
  set L : ℝ := Real.log D
  have hL8 : 8 < L := eight_lt_log hd
  have hnum := BoundariesOfClass.Numerics.upper_numeric hL8.le
  have hBpos := BoundariesOfClass.Numerics.upper_bracket_pos hL8.le
  have hsD : 0 < Real.sqrt D := Real.sqrt_pos.mpr (by linarith)
  set B : ℝ := π * (L + 1) / Real.exp 1 - 4 * Real.sqrt 2 * π * (1 + 1 / L) ^ 3 * BoundariesOfClass.Numerics.kap /
    Real.sqrt (Real.exp 1)
  set h : ℝ := (classNumber K : ℝ)
  have h1 : h * (B / Real.sqrt D) ≤ 6 / 5 * L * B := le_trans hex hnum
  have h2 : h * B ≤ 6 / 5 * Real.sqrt D * L * B := by
    have := mul_le_mul_of_nonneg_left h1 hsD.le
    rw [show Real.sqrt D * (h * (B / Real.sqrt D)) = h * B by field_simp] at this
    linarith
  have := le_of_mul_le_mul_right (by linarith : h * B ≤ 6 / 5 * Real.sqrt D * L * B) hBpos
  linarith

end BoundariesOfClass.Assembly
