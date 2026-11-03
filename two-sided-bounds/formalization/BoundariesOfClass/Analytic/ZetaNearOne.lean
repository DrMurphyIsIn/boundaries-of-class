import Mathlib
import CN1.Numerics.ZetaReal

/-!
# BoundariesOfClass.Analytic.ZetaNearOne: `ζ` and `L(·, χ)` at real points near `1`

Pinned environment: Lean v4.34.1, Mathlib d13f23b. From CN-1's Euler–Maclaurin formula with explicit remainder
(`CN1.Numerics.riemannZeta_ofReal_eulerMaclaurin`, CN1/Numerics/ZetaReal.lean:304):

* `riemannZeta_ofReal_bracket`: for real `σ > 0`, `σ ≠ 1`, `ζ(σ)` is real and
  `1/(σ-1) + 1/2 ≤ ζ(σ) ≤ 1/(σ-1) + 1/2 + σ(σ+2)/8` (`M = 0`).
* `riemannZeta_ofReal_re_neg`: `ζ(σ) < 0` for `0 < σ < 1`.
* `thirteen_eighths_le_riemannZeta`: `ζ(x) ≥ 13/8` for `1 < x ≤ 2` (`M = 1`; `ζ(2) = 1.6449`).
* `pi_sq_div_six_le_riemannZeta`: `ζ(x) ≥ ζ(2) = π²/6` for `1 < x ≤ 2` (sharpens the `13/8` above).
* `norm_LFunction_le_riemannZeta`: `‖L(σ, χ)‖ ≤ ζ(σ)` for real `σ > 1` and any Dirichlet character (`|χ| ≤ 1`, the
  L-series converges absolutely there). Mathlib has no such lemma.

-/

set_option autoImplicit false

namespace BoundariesOfClass.Analytic

open Complex

/-- **Euler–Maclaurin at `M = 0`:** `ζ(σ)` is real and `1/(σ-1) + 1/2 ≤ ζ(σ) ≤ 1/(σ-1) + 1/2 + σ(σ+2)/8`. -/
theorem riemannZeta_ofReal_bracket {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≠ 1) :
    (riemannZeta σ).im = 0 ∧ 1 / (σ - 1) + 1 / 2 ≤ (riemannZeta σ).re ∧
      (riemannZeta σ).re ≤ 1 / (σ - 1) + 1 / 2 + σ * (σ + 2) / 8 := by
  obtain ⟨R, hR, hR0, hR1⟩ := CN1.Numerics.riemannZeta_ofReal_eulerMaclaurin hσ hσ1 0
  simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, zero_add, Real.one_rpow, zero_add] at hR hR1
  rw [hR, Complex.ofReal_im, Complex.ofReal_re]
  refine ⟨rfl, by linarith, by linarith⟩

/-- `ζ(σ) < 0` for `0 < σ < 1`: `ζ(σ) ≤ 1/(σ-1) + 1/2 + 3/8 ≤ -1 + 7/8`. -/
theorem riemannZeta_ofReal_re_neg {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) : (riemannZeta σ).re < 0 := by
  obtain ⟨-, -, hup⟩ := riemannZeta_ofReal_bracket hσ hσ1.ne
  have h1 : 1 / (σ - 1) ≤ -1 := by
    rw [div_le_iff_of_neg (by linarith)]; linarith
  have h2 : σ * (σ + 2) / 8 ≤ 3 / 8 := by nlinarith
  linarith

/-- **`ζ(x) ≥ 13/8` for `1 < x ≤ 2`** (Euler–Maclaurin at `M = 1`: `1 + 2^{1-x}/(x-1) + 2^{-x}/2 + R`, `R ≥ 0`). -/
theorem thirteen_eighths_le_riemannZeta {x : ℝ} (hx1 : 1 < x) (hx2 : x ≤ 2) :
    (13 / 8 : ℝ) ≤ (riemannZeta x).re := by
  obtain ⟨R, hR, hR0, -⟩ := CN1.Numerics.riemannZeta_ofReal_eulerMaclaurin (by linarith : (0 : ℝ) < x) hx1.ne' 1
  rw [hR, Complex.ofReal_re]
  simp only [Finset.sum_range_one, Nat.cast_zero, zero_add, Real.one_rpow, Nat.cast_one]
  rw [show (1 : ℝ) + 1 = 2 by norm_num]
  have h2a : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (1 - x) := by
    have := Real.rpow_le_rpow_of_exponent_le (x := 2) (y := -1) (z := 1 - x) (by norm_num) (by linarith)
    rwa [Real.rpow_neg_one, ← one_div] at this
  have h2b : (1 / 4 : ℝ) ≤ (2 : ℝ) ^ (-x) := by
    have := Real.rpow_le_rpow_of_exponent_le (x := 2) (y := -2) (z := -x) (by norm_num) (by linarith)
    rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by norm_num), Real.rpow_natCast] at this
    norm_num at this ⊢
    linarith
  have h3 : 1 / 2 ≤ (2 : ℝ) ^ (1 - x) / (x - 1) := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith
  linarith

/-- **`‖L(σ, χ)‖ ≤ ζ(σ)`** for real `σ > 1` and any Dirichlet character. -/
theorem norm_LFunction_le_riemannZeta {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {σ : ℝ} (hσ : 1 < σ) :
    ‖DirichletCharacter.LFunction χ σ‖ ≤ (riemannZeta σ).re := by
  have hs : 1 < (σ : ℂ).re := by simpa using hσ
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs, ← LSeries_one_eq_riemannZeta hs]
  have hsum1 : LSeriesSummable 1 (σ : ℂ) := LSeriesSummable_one_iff.mpr hs
  have hn1 : Summable fun n => ‖LSeries.term 1 (σ : ℂ) n‖ := summable_norm_iff.mpr hsum1
  have hle : ∀ n, ‖LSeries.term (fun n => χ n) (σ : ℂ) n‖ ≤ ‖LSeries.term 1 (σ : ℂ) n‖ := fun n =>
    LSeries.norm_term_le _ (by simpa using DirichletCharacter.norm_le_one χ n)
  have hnχ : Summable fun n => ‖LSeries.term (fun n => χ n) (σ : ℂ) n‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hn1
  -- the terms of `L 1 σ` are nonnegative reals
  have hre : ∀ n, (LSeries.term 1 (σ : ℂ) n).re = ‖LSeries.term 1 (σ : ℂ) n‖ := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [LSeries.term_of_ne_zero hn, Pi.one_apply]
      have e : ((n : ℂ) ^ (σ : ℂ)) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
        rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]; push_cast; rfl
      rw [e, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖LSeries (fun n => χ n) (σ : ℂ)‖ ≤ ∑' n, ‖LSeries.term (fun n => χ n) (σ : ℂ) n‖ :=
        norm_tsum_le_tsum_norm hnχ
    _ ≤ ∑' n, ‖LSeries.term 1 (σ : ℂ) n‖ := Summable.tsum_le_tsum hle hnχ hn1
    _ = (LSeries 1 (σ : ℂ)).re := by
        rw [LSeries, Complex.re_tsum hsum1]
        exact tsum_congr fun n => (hre n).symm

/-- For real `x > 1`, `ζ(x)` is the real series `Σ_{n ≥ 0} (n+1)^{-x}`, which is summable. -/
theorem riemannZeta_ofReal_re_eq_tsum {x : ℝ} (hx : 1 < x) :
    (riemannZeta x).re = ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ x ∧ Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ x := by
  have hs : 1 < (x : ℂ).re := by simpa using hx
  have hsum : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ x := by
    have h := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_rpow.mpr hx)
    simpa [Nat.cast_add, Nat.cast_one] using h
  refine ⟨?_, hsum⟩
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  have e : ∀ n : ℕ, (1 : ℂ) / ((n : ℂ) + 1) ^ (x : ℂ) = ((1 / ((n : ℝ) + 1) ^ x : ℝ) : ℂ) := by
    intro n
    rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_cpow (by positivity)]
    push_cast; rfl
  simp_rw [e]
  rw [← Complex.ofReal_tsum, Complex.ofReal_re]

/-- **`ζ(x) ≥ ζ(2) = π²/6` for `1 < x ≤ 2`** (termwise comparison of the two series). -/
theorem pi_sq_div_six_le_riemannZeta {x : ℝ} (hx1 : 1 < x) (hx2 : x ≤ 2) :
    Real.pi ^ 2 / 6 ≤ (riemannZeta x).re := by
  obtain ⟨hx, hsx⟩ := riemannZeta_ofReal_re_eq_tsum hx1
  obtain ⟨h2, hs2⟩ := riemannZeta_ofReal_re_eq_tsum (x := 2) (by norm_num)
  have hz2 : (riemannZeta ((2 : ℝ) : ℂ)).re = Real.pi ^ 2 / 6 := by
    rw [show ((2 : ℝ) : ℂ) = 2 by norm_num, riemannZeta_two]
    rw [show (Real.pi : ℂ) ^ 2 / 6 = ((Real.pi ^ 2 / 6 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
  rw [hz2] at h2
  rw [hx, h2]
  refine Summable.tsum_le_tsum (fun n => ?_) hs2 hsx
  have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  apply one_div_le_one_div_of_le (by positivity)
  exact Real.rpow_le_rpow_of_exponent_le h1 hx2

end BoundariesOfClass.Analytic
