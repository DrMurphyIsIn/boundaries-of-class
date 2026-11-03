import BoundariesOfClass.Numerics.LprimeA
import BoundariesOfClass.Numerics.LprimeBNum

/-!
# BoundariesOfClass.Numerics.LprimeB: the uniform lower bound `(1/3) √d / log d ≤ h` for `log d ≥ 16`

Pinned environment: Lean v4.34.1, Mathlib d13f23b. With `u = log d ≥ 16`, `t = 1/u`, the class sum is taken at
`σ = 1 - 2t` (`classSum_floor_half`, every class charged its exact floor, `K_{1/2}` remainder). Then `d^{2t} = e²`
exactly, and:

* `ζ(2σ) ≥ 1 + (1/2)/(1 - 4t) + 1/8` (Euler–Maclaurin, `M = 1`; `one_add_half_div_le_riemannZeta`);
* `-ζ(2σ - 1) ≤ (1 - 2t)/(4t)` (Euler–Maclaurin, `M = 0`);
* `C₁ ≤ 2π e² T(t)/√d` (the `tan` bracket, `T = TB`);
* the floor `(1 - δ/σ) K u* ≤ (π e T/2)(1 - 4t)/(t (1 - y)) / √d`, from `u* ≤ e^{-1} e^{y}` (`y = yB t`), using
  `π e² T/ζ(2σ) ≤ e^{2 + 47/64}` and `e^y ≤ 1/(1 - y)`;
* `E₂ ≤ 4 π e κ/√d` (`π^σ ≤ π`, `Γ(σ) ≥ 1`, `(2/√d)^σ = 2^σ e/√d`), and `K + E₂(1) ≤ 1/14` (from `u/√d ≤ 16 e^{-8}`).

The resulting rational inequality is `lprimeB_numeric`. Then `h ≥ 1 + (t/3) √d`.
-/

set_option autoImplicit false

open NumberField CN1.Finite HCN.CS BoundariesOfClass.CS BoundariesOfClass.Analytic
open scoped Real

namespace BoundariesOfClass.Numerics

/-- `ζ(x) ≥ 1 + (1/2)/(x - 1) + 1/8` for `1 < x ≤ 2` (Euler–Maclaurin, `M = 1`). -/
theorem one_add_half_div_le_riemannZeta {x : ℝ} (hx1 : 1 < x) (hx2 : x ≤ 2) :
    1 + 1 / 2 / (x - 1) + 1 / 8 ≤ (riemannZeta x).re := by
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
  have h3 : 1 / 2 / (x - 1) ≤ (2 : ℝ) ^ (1 - x) / (x - 1) :=
    div_le_div_of_nonneg_right h2a (by linarith)
  linarith

/-- `Γ(y) ≥ y - 1` for `1 < y ≤ 2`: convexity of `Γ` on the chord through `y` and `3`, at `2`. -/
theorem sub_one_le_Gamma {y : ℝ} (hy1 : 1 < y) (hy2 : y ≤ 2) : y - 1 ≤ Real.Gamma y := by
  rcases eq_or_lt_of_le hy2 with h | h
  · rw [h, Real.Gamma_two]; norm_num
  have h3y : 0 < 3 - y := by linarith
  have ha : (0 : ℝ) ≤ 1 / (3 - y) := div_nonneg zero_le_one h3y.le
  have hb : (0 : ℝ) ≤ (2 - y) / (3 - y) := div_nonneg (by linarith) h3y.le
  have hab : 1 / (3 - y) + (2 - y) / (3 - y) = 1 := by
    rw [← add_div, div_eq_one_iff_eq h3y.ne']; ring
  have hmy : y ∈ Set.Ioi (0 : ℝ) := by simp only [Set.mem_Ioi]; linarith
  have hm3 : (3 : ℝ) ∈ Set.Ioi (0 : ℝ) := by norm_num [Set.mem_Ioi]
  have hc := Real.convexOn_Gamma.2 hmy hm3 ha hb hab
  simp only [smul_eq_mul] at hc
  have e : 1 / (3 - y) * y + (2 - y) / (3 - y) * 3 = 2 := by
    field_simp; ring
  have hG3 : Real.Gamma 3 = 2 := by
    rw [show (3 : ℝ) = 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num), Real.Gamma_two]; norm_num
  rw [e, Real.Gamma_two, hG3] at hc
  -- `1 ≤ Γ(y)/(3 - y) + 2(2 - y)/(3 - y)`, so `3 - y ≤ Γ(y) + 4 - 2y`
  have h1 : (3 - y) * 1 ≤ (3 - y) * (1 / (3 - y) * Real.Gamma y + (2 - y) / (3 - y) * 2) :=
    mul_le_mul_of_nonneg_left hc h3y.le
  have e2 : (3 - y) * (1 / (3 - y) * Real.Gamma y + (2 - y) / (3 - y) * 2) = Real.Gamma y + 2 * (2 - y) := by
    field_simp
  rw [e2] at h1
  linarith

/-- `Γ(x) ≥ 1` for `0 < x ≤ 1`, from `Γ(x + 1) = x Γ(x) ≥ x`. -/
theorem one_le_Gamma_of_le_one {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) : 1 ≤ Real.Gamma x := by
  have h := sub_one_le_Gamma (y := x + 1) (by linarith) (by linarith)
  rw [Real.Gamma_add_one hx.ne', add_sub_cancel_right] at h
  have : x * 1 ≤ x * Real.Gamma x := by linarith
  exact le_of_mul_le_mul_left this hx

/-- `u e^{-u/2} ≤ 16 e^{-8}` for `u ≥ 16`. -/
lemma mul_exp_neg_half_le {u : ℝ} (hu : 16 ≤ u) : u * Real.exp (-(u / 2)) ≤ 16 * Real.exp (-8) := by
  have h1 : 1 + (u - 16) / 2 ≤ Real.exp ((u - 16) / 2) := by linarith [Real.add_one_le_exp ((u - 16) / 2)]
  have h2 : u ≤ 16 * Real.exp ((u - 16) / 2) := by nlinarith
  have h3 : Real.exp ((u - 16) / 2) * Real.exp (-(u / 2)) = Real.exp (-8) := by
    rw [← Real.exp_add]; ring_nf
  calc u * Real.exp (-(u / 2)) ≤ 16 * Real.exp ((u - 16) / 2) * Real.exp (-(u / 2)) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = 16 * Real.exp (-8) := by rw [mul_assoc, h3]

/-- The pure-real last step: from the class sum to `h ≥ (t/3)√d`. -/
lemma final_B {h S t P0 Fl E2 Pl Mb : ℝ} (hS : 0 < S) (_ht : 0 < t)
    (hcore : P0 - (h - 1) * (Fl + E2) ≤ 0) (hPl : Pl ≤ P0) (hPl0 : 0 < Pl) (hm0 : 0 ≤ Fl + E2)
    (hm : Fl + E2 ≤ Mb / S) (hMb : 0 < Mb) (hratio : t * Mb ≤ 3 * Pl) : 1 / 3 * S * t ≤ h := by
  have h1 : 0 < (h - 1) * (Fl + E2) := by linarith
  have hh1 : 0 < h - 1 := by
    rcases eq_or_lt_of_le hm0 with h0 | h0
    · rw [← h0, mul_zero] at h1; exact absurd h1 (lt_irrefl 0)
    · exact pos_of_mul_pos_left h1 h0.le
  have h2 : Pl ≤ (h - 1) * (Mb / S) := by
    calc Pl ≤ P0 := hPl
      _ ≤ (h - 1) * (Fl + E2) := by linarith
      _ ≤ (h - 1) * (Mb / S) := mul_le_mul_of_nonneg_left hm hh1.le
  have h3 : Pl * S ≤ (h - 1) * Mb := by
    have := mul_le_mul_of_nonneg_right h2 hS.le
    rwa [mul_assoc, div_mul_cancel₀ _ hS.ne'] at this
  have h4 : t * S * Mb ≤ 3 * ((h - 1) * Mb) := by nlinarith
  have h5 : t * S ≤ 3 * (h - 1) := by
    have := le_of_mul_le_mul_right (show t * S * Mb ≤ (3 * (h - 1)) * Mb by linarith) hMb
    exact this
  linarith

/-- `(1 - x²/6 + x⁴/100)/(1 - x²/2) ≤ TB t` for `x = π · 2t`, `0 < t ≤ 1/16`. -/
lemma sin_bracket_le_TB {t : ℝ} (ht0 : 0 < t) (ht : t ≤ 1 / 16) :
    Real.sin (π * (2 * t)) / (π * (2 * t) * Real.cos (π * (2 * t))) ≤ TB t := by
  have hpL : (3141592 / 1000000 : ℝ) ≤ π := by have := Real.pi_gt_d6; norm_num at this; linarith
  have hpU : π ≤ (3141593 / 1000000 : ℝ) := by have := Real.pi_lt_d6; norm_num at this; linarith
  set x := π * (2 * t) with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 := by rw [hx]; nlinarith
  refine (sin_div_mul_cos_le hx0 hx1).trans ?_
  have hxL : 2 * (3141592 / 1000000) * t ≤ x := by rw [hx]; nlinarith
  have hxU : x ≤ 2 * (3141593 / 1000000) * t := by rw [hx]; nlinarith
  have hxU2 : x ^ 2 ≤ (2 * (3141593 / 1000000) * t) ^ 2 := pow_le_pow_left₀ hx0.le hxU 2
  have hxL2 : (2 * (3141592 / 1000000) * t) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ (by positivity) hxL 2
  have hxU4 : x ^ 4 ≤ (2 * (3141593 / 1000000) * t) ^ 4 := pow_le_pow_left₀ hx0.le hxU 4
  have hden : 0 < 1 - (2 * (3141593 / 1000000) * t) ^ 2 / 2 := by nlinarith
  have hden' : 0 < 1 - x ^ 2 / 2 := by nlinarith
  unfold TB
  apply div_le_div₀ (by nlinarith) (by nlinarith) hden (by nlinarith)

lemma yB_nonneg {t : ℝ} (ht0 : 0 < t) (ht : t ≤ 1 / 16) : 0 ≤ yB t := by
  unfold yB; apply div_nonneg (by positivity) (by linarith)

lemma yB_lt_one {t : ℝ} (ht0 : 0 < t) (ht : t ≤ 1 / 16) : yB t < 1 := by
  unfold yB; rw [div_lt_one (by linarith)]; linarith

lemma one_le_TB {t : ℝ} (ht0 : 0 < t) (ht : t ≤ 1 / 16) : 1 ≤ TB t := by
  unfold TB
  rw [le_div_iff₀ (by nlinarith)]
  nlinarith [sq_nonneg t, pow_two_nonneg (t ^ 2)]

set_option maxHeartbeats 4000000 in
/-- **(L′) for `log d ≥ 16`**, at `σ = 1 - 2/log d`. -/
theorem third_sqrt_div_log_le_B {K : Type*} [Field K] [NumberField K] {m : ℕ} {α : K}
    (hα : α ^ 2 = -(m : K)) (hK : Module.finrank ℚ K = 2) (hm : Squarefree m) (hm1 : m ≠ 1) (hm3 : m ≠ 3)
    (hu16 : 16 ≤ Real.log (dOf m)) :
    1 / 3 * Real.sqrt (dOf m) / Real.log (dOf m) ≤ (classNumber K : ℝ) := by
  have hD0 : (0 : ℝ) < (dOf m : ℝ) := BoundariesOfClass.Assembly.dOf_pos hm
  set D : ℝ := (dOf m : ℝ) with hDdef
  set u := Real.log D with hudef
  have hu0 : 0 < u := by linarith
  set t := 1 / u with htdef
  have ht0 : 0 < t := by positivity
  have ht16 : t ≤ 1 / 16 := by rw [htdef]; exact one_div_le_one_div_of_le (by norm_num) hu16
  have hut : u * t = 1 := by rw [htdef]; field_simp
  have hσ78 : 7 / 8 ≤ 1 - 2 * t := by linarith
  have hσ1 : 1 - 2 * t < 1 := by linarith
  have hcore := BoundariesOfClass.Assembly.classSum_floor_half hα hK hm hm1 hm3 hσ78 hσ1
  rw [← hDdef] at hcore
  rw [show 2 * (1 - 2 * t) - 1 = 1 - 4 * t by ring, show 2 * (1 - 2 * t) = 2 - 4 * t by ring,
    show 1 - (1 - 2 * t) = 2 * t by ring, show 1 - 2 * (2 * t) = 1 - 4 * t by ring] at hcore
  -- `√D = e^{u/2}`
  set S := Real.sqrt D with hSdef
  have hS : S = Real.exp (u / 2) := by rw [hSdef, hudef, Real.exp_half, Real.exp_log hD0]
  have hS0 : 0 < S := by rw [hS]; exact Real.exp_pos _
  -- brackets for π and e
  have hpL : (3141592 / 1000000 : ℝ) ≤ π := by have := Real.pi_gt_d6; norm_num at this; linarith
  have hpU : π ≤ (3141593 / 1000000 : ℝ) := by have := Real.pi_lt_d6; norm_num at this; linarith
  have heL : (27182818283 / 10000000000 : ℝ) ≤ Real.exp 1 := by
    have := Real.exp_one_gt_d9; norm_num at this ⊢; linarith
  have heU : Real.exp 1 ≤ (27182818286 / 10000000000 : ℝ) := by
    have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
  have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  -- F1, F2, F3: the ζ values
  set Zs := (riemannZeta ((2 - 4 * t : ℝ) : ℂ)).re with hZs
  set Zm := (riemannZeta ((1 - 4 * t : ℝ) : ℂ)).re with hZm
  have hF1 : 1 + 1 / 2 / (1 - 4 * t) + 1 / 8 ≤ Zs := by
    have := one_add_half_div_le_riemannZeta (x := 2 - 4 * t) (by linarith) (by linarith)
    rwa [show (2 - 4 * t) - 1 = 1 - 4 * t by ring] at this
  have hZl : (13 / 8 : ℝ) ≤ 1 + 1 / 2 / (1 - 4 * t) + 1 / 8 := by
    have : (1 : ℝ) / 2 ≤ 1 / 2 / (1 - 4 * t) := by
      rw [le_div_iff₀ (by linarith)]; nlinarith
    linarith
  obtain ⟨-, hZmlo, -⟩ := riemannZeta_ofReal_bracket (σ := 1 - 4 * t) (by linarith) (by linarith)
  have hF2 : -Zm ≤ (1 - 2 * t) / (4 * t) := by
    have e : 1 / ((1 - 4 * t) - 1) = -(1 / (4 * t)) := by
      rw [show (1 - 4 * t) - 1 = -(4 * t) by ring, one_div_neg_eq_neg_one_div]
    rw [e] at hZmlo
    have : (1 - 2 * t) / (4 * t) = 1 / (4 * t) - 1 / 2 := by field_simp; ring
    rw [this]; linarith
  have hF3 : Zm ≤ 0 := (riemannZeta_ofReal_re_neg (by linarith) (by linarith)).le
  -- F4: `C₁ ≤ 2π e² T/S`
  set C1 := coeffR 1 D (1 - 2 * t) with hC1def
  have hC1pos : 0 < C1 := coeffR_pos one_pos hD0 (by linarith)
  have hT := sin_bracket_le_TB ht0 ht16
  have hTle : TB t ≤ 10570 / 10000 := TB_le ht0.le ht16 le_rfl (by norm_num) (by norm_num)
  have hT1 : 1 ≤ TB t := one_le_TB ht0 ht16
  have hF4 : C1 ≤ 2 * π * Real.exp 2 * TB t / S := by
    have h := coeffR_one_le_minus_tan hD0 (δ := 2 * t) (by positivity) (by linarith)
    have hDd : D ^ (2 * t) = Real.exp 2 := by
      rw [Real.rpow_def_of_pos hD0, ← hudef, show u * (2 * t) = 2 * (u * t) by ring, hut, mul_one]
    rw [hDd, ← hSdef] at h
    refine h.trans ?_
    have hc : 0 < Real.cos (π * (2 * t)) := cos_pi_mul_pos (by positivity) (by linarith)
    have hpos : 0 < π * (2 * t) * Real.cos (π * (2 * t)) := by positivity
    have e : 2 * π * Real.exp 2 * Real.sin (π * (2 * t)) / (S * (π * (2 * t) * Real.cos (π * (2 * t)))) =
        2 * π * Real.exp 2 / S * (Real.sin (π * (2 * t)) / (π * (2 * t) * Real.cos (π * (2 * t)))) := by
      field_simp
    rw [e, show 2 * π * Real.exp 2 * TB t / S = 2 * π * Real.exp 2 / S * TB t by ring]
    exact mul_le_mul_of_nonneg_left hT (by positivity)
  set Kq := C1 * -Zm with hKq
  have hK0 : 0 ≤ Kq := mul_nonneg hC1pos.le (by linarith)
  have hKle : Kq ≤ 2 * π * Real.exp 2 * TB t / S * ((1 - 2 * t) / (4 * t)) :=
    mul_le_mul hF4 hF2 (by linarith) (by positivity)
  -- F5: the floor
  set y := yB t with hydef
  have hy0 : 0 ≤ y := yB_nonneg ht0 ht16
  have hy1 : y < 1 := yB_lt_one ht0 ht16
  have hbase : 2 * t * Kq / ((1 - 2 * t) * Zs) ≤ Real.exp (2 + 47 / 64 - u / 2) := by
    have hZs0 : 0 < Zs := by linarith
    have h1 : 2 * t * Kq / ((1 - 2 * t) * Zs) ≤ π * Real.exp 2 * TB t / ((1 + 1 / 2 / (1 - 4 * t) + 1 / 8) * S) := by
      rw [div_le_div_iff₀ (by nlinarith) (by positivity)]
      have h2 : 2 * t * Kq ≤ π * Real.exp 2 * TB t * (1 - 2 * t) / S := by
        have := mul_le_mul_of_nonneg_left hKle (show 0 ≤ 2 * t by positivity)
        refine this.trans (le_of_eq ?_)
        field_simp
        ring
      have h3 : 0 ≤ π * Real.exp 2 * TB t * (1 - 2 * t) / S := by
        have : 0 ≤ 1 - 2 * t := by linarith
        positivity
      calc 2 * t * Kq * ((1 + 1 / 2 / (1 - 4 * t) + 1 / 8) * S)
          ≤ π * Real.exp 2 * TB t * (1 - 2 * t) / S * ((1 + 1 / 2 / (1 - 4 * t) + 1 / 8) * S) :=
            mul_le_mul_of_nonneg_right h2 (by positivity)
        _ = π * Real.exp 2 * TB t * ((1 - 2 * t) * (1 + 1 / 2 / (1 - 4 * t) + 1 / 8)) := by
            field_simp
        _ ≤ π * Real.exp 2 * TB t * ((1 - 2 * t) * Zs) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_left hF1 (by linarith)
    refine h1.trans ?_
    rw [Real.exp_sub, ← hS]
    rw [div_le_div_iff₀ (by positivity) hS0]
    rw [show Real.exp (2 + 47 / 64) * ((1 + 1 / 2 / (1 - 4 * t) + 1 / 8) * S) =
      Real.exp (2 + 47 / 64) * (1 + 1 / 2 / (1 - 4 * t) + 1 / 8) * S by ring]
    apply mul_le_mul_of_nonneg_right _ hS0.le
    have hl := exp_nat_add_div_ge 2 47
    push_cast at hl
    have hpe : π * Real.exp 2 * TB t ≤ 3141593 / 1000000 * ((27182818286 / 10000000000) *
        (27182818286 / 10000000000)) * (10570 / 10000) := by
      rw [he2]
      apply mul_le_mul (mul_le_mul hpU (mul_le_mul heU heU (by positivity) (by norm_num)) (by positivity)
        (by norm_num)) hTle (by linarith) (by norm_num)
    have hc : 3141593 / 1000000 * ((27182818286 / 10000000000 : ℝ) * (27182818286 / 10000000000)) *
        (10570 / 10000) ≤ (27182818283 / 10000000000 : ℝ) ^ 2 * (1 + 1 / 64 + 1 / 8192) ^ 47 * (13 / 8) := by
      norm_num
    have : (27182818283 / 10000000000 : ℝ) ^ 2 * (1 + 1 / 64 + 1 / 8192) ^ 47 * (13 / 8) ≤
        Real.exp (2 + 47 / 64) * (1 + 1 / 2 / (1 - 4 * t) + 1 / 8) :=
      mul_le_mul hl hZl (by norm_num) (Real.exp_pos _).le
    linarith
  have h4t0 : (1 : ℝ) - 4 * t ≠ 0 := by linarith
  have he3 : (2 + 47 / 64 - u / 2) * (2 * t / (1 - 4 * t)) = -1 + y := by
    rw [hydef]; unfold yB
    calc (2 + 47 / 64 - u / 2) * (2 * t / (1 - 4 * t)) = ((2 + 47 / 64) * (2 * t) - u * t) / (1 - 4 * t) := by
          ring
      _ = ((2 + 47 / 64) * (2 * t) - 1) / (1 - 4 * t) := by rw [hut]
      _ = -1 + 2 * t * (47 / 64) / (1 - 4 * t) := by
          have hm1 : (-1 : ℝ) = -(1 - 4 * t) / (1 - 4 * t) := by rw [neg_div, div_self h4t0]
          rw [hm1, ← add_div]; congr 1; ring
  have hB : (2 * t * Kq / ((1 - 2 * t) * Zs)) ^ (2 * t / (1 - 4 * t)) ≤ Real.exp (-1) / (1 - y) := by
    have hb0 : 0 ≤ 2 * t * Kq / ((1 - 2 * t) * Zs) := by
      apply div_nonneg (by positivity)
      have : 0 < Zs := by linarith
      nlinarith
    have hexp : 0 ≤ 2 * t / (1 - 4 * t) := div_nonneg (by positivity) (by linarith)
    refine (Real.rpow_le_rpow hb0 hbase hexp).trans ?_
    rw [← Real.exp_mul, he3, Real.exp_add, le_div_iff₀ (by linarith), mul_assoc]
    apply mul_le_of_le_one_right (Real.exp_pos _).le
    have := Real.add_one_le_exp (-y)
    have h2 : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos y]
  have hF5 : (1 - 2 * t / (1 - 2 * t)) * Kq * (2 * t * Kq / ((1 - 2 * t) * Zs)) ^ (2 * t / (1 - 4 * t)) ≤
      π * Real.exp 1 * TB t / 2 * (1 - 4 * t) / (t * (1 - y)) / S := by
    have hc0 : 0 ≤ 1 - 2 * t / (1 - 2 * t) := by
      rw [sub_nonneg, div_le_one (by linarith)]; linarith
    have hcoef : 1 - 2 * t / (1 - 2 * t) = (1 - 4 * t) / (1 - 2 * t) := by
      have h2t : (1 : ℝ) - 2 * t ≠ 0 := by linarith
      rw [eq_div_iff h2t, sub_mul, div_mul_cancel₀ _ h2t]; ring
    have h1 := mul_le_mul (mul_le_mul_of_nonneg_left hKle hc0) hB (Real.rpow_nonneg (by
      apply div_nonneg (by positivity); have : 0 < Zs := by linarith
      nlinarith) _) (by positivity)
    refine h1.trans (le_of_eq ?_)
    rw [hcoef, he2, Real.exp_neg]
    have h1e : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
    have h2t : (1 : ℝ) - 2 * t ≠ 0 := by linarith
    have hyt : (1 : ℝ) - y ≠ 0 := by linarith
    have ht' : t ≠ 0 := ht0.ne'
    have hS' : S ≠ 0 := hS0.ne'
    have h4t' : (4 : ℝ) * t ≠ 0 := by positivity
    have key : (1 - 4 * t) / (1 - 2 * t) * ((1 - 2 * t) / (4 * t)) = (1 - 4 * t) / (4 * t) := by
      rw [div_mul_div_comm, mul_comm (1 - 2 * t) (4 * t), mul_div_mul_right _ _ h2t]
    calc (1 - 4 * t) / (1 - 2 * t) * (2 * π * (Real.exp 1 * Real.exp 1) * TB t / S * ((1 - 2 * t) / (4 * t))) *
          ((Real.exp 1)⁻¹ / (1 - y))
        = 2 * π * (Real.exp 1 * Real.exp 1) * TB t / S * ((1 - 4 * t) / (1 - 2 * t) * ((1 - 2 * t) / (4 * t))) *
          ((Real.exp 1)⁻¹ / (1 - y)) := by ring
      _ = π * Real.exp 1 * TB t / 2 * (1 - 4 * t) / (t * (1 - y)) / S := by
          rw [key]; field_simp; ring
  -- F6: the remainders
  have hσpos : 0 < 1 - 2 * t := by linarith
  have hπσ : π ^ (1 - 2 * t) ≤ π := by
    calc π ^ (1 - 2 * t) ≤ π ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) (by linarith)
      _ = π := Real.rpow_one π
  have hΓ := one_le_Gamma_of_le_one hσpos hσ1.le
  have hSσ : S ^ (1 - 2 * t) = S / Real.exp 1 := by
    rw [hS, ← Real.exp_mul, ← Real.exp_sub]; congr 1
    have : u * t = 1 := hut
    nlinarith
  have h2σ : (2 : ℝ) ^ (1 - 2 * t) ≤ 2 := by
    calc (2 : ℝ) ^ (1 - 2 * t) ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := Real.rpow_one 2
  have hpref : 2 * π ^ (1 - 2 * t) / Real.Gamma (1 - 2 * t) * (2 / S) ^ (1 - 2 * t) ≤ 4 * π * Real.exp 1 / S := by
    rw [Real.div_rpow (by norm_num) hS0.le, hSσ]
    have hG0 : 0 < Real.Gamma (1 - 2 * t) := by linarith
    have h1 : 2 * π ^ (1 - 2 * t) / Real.Gamma (1 - 2 * t) ≤ 2 * π := by
      rw [div_le_iff₀ hG0]; nlinarith [Real.rpow_pos_of_pos Real.pi_pos (1 - 2 * t)]
    have h2 : (2 : ℝ) ^ (1 - 2 * t) / (S / Real.exp 1) ≤ 2 * Real.exp 1 / S := by
      rw [div_div_eq_mul_div, div_le_div_iff_of_pos_right hS0]
      exact mul_le_mul_of_nonneg_right h2σ (Real.exp_pos _).le
    calc 2 * π ^ (1 - 2 * t) / Real.Gamma (1 - 2 * t) * ((2 : ℝ) ^ (1 - 2 * t) / (S / Real.exp 1))
        ≤ 2 * π * (2 * Real.exp 1 / S) := mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = 4 * π * Real.exp 1 / S := by ring
  have hpref0 : 0 ≤ 2 * π ^ (1 - 2 * t) / Real.Gamma (1 - 2 * t) * (2 / S) ^ (1 - 2 * t) := by
    have : 0 < Real.Gamma (1 - 2 * t) := by linarith
    positivity
  have hk32 := kappa_three_pi_div_two_le
  have hk0 := kappa_nonneg (3 * π / 2)
  have hE2 : 2 * π ^ (1 - 2 * t) / Real.Gamma (1 - 2 * t) * (2 / S) ^ (1 - 2 * t) * kappa (3 * π / 2) ≤
      4 * π * Real.exp 1 * kapB / S := by
    have := mul_le_mul hpref hk32 hk0 (by positivity)
    unfold kapB; refine this.trans (le_of_eq ?_); ring
  have hSbig : 3 / 2 ≤ S := by
    rw [hS]
    have := Real.add_one_le_exp (u / 2); linarith
  have hκ1 : kappa (π * S) ≤ kappa (3 * π / 2) := by
    have := rpow_neg_mul_kappa_mono (δ := 0) le_rfl zero_le_one (C := π * S) (by positivity) (a := 1)
      (a' := 2 * S / 3) one_pos (by linarith) (by field_simp; linarith)
    rw [neg_zero, Real.rpow_zero, Real.rpow_zero, one_mul, one_mul, div_one] at this
    rwa [show π * S / (2 * S / 3) = 3 * π / 2 by field_simp] at this
  have hE21 : 2 * π ^ (1 - 2 * t) / Real.Gamma (1 - 2 * t) * (2 / S) ^ (1 - 2 * t) * kappa (π * S) ≤
      2 * π ^ (1 - 2 * t) / Real.Gamma (1 - 2 * t) * (2 / S) ^ (1 - 2 * t) * kappa (3 * π / 2) :=
    mul_le_mul_of_nonneg_left hκ1 hpref0
  -- F7: `P₀ ≥ Z̲ - 1/14`
  have huS : u / S ≤ 16 * Real.exp (-8) := by
    rw [hS, div_eq_mul_inv, ← Real.exp_neg]; exact mul_exp_neg_half_le hu16
  have hSinv : 1 / S ≤ Real.exp (-8) := by
    rw [hS, one_div, ← Real.exp_neg]; exact Real.exp_le_exp.mpr (by linarith)
  have he8 : Real.exp (-8) ≤ 1 / (27182818283 / 10000000000 : ℝ) ^ 8 := by
    rw [Real.exp_neg, show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, ← Real.exp_one_pow, one_div]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by norm_num) heL 8)
  have hKP : Kq ≤ π * Real.exp 2 * TB t / 2 * (u / S) := by
    refine hKle.trans (le_of_eq_of_le rfl ?_)
    have : (1 - 2 * t) / (4 * t) ≤ u / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    calc 2 * π * Real.exp 2 * TB t / S * ((1 - 2 * t) / (4 * t)) ≤ 2 * π * Real.exp 2 * TB t / S * (u / 4) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = π * Real.exp 2 * TB t / 2 * (u / S) := by field_simp; ring
  have hP7 : 1 + 1 / 2 / (1 - 4 * t) + 1 / 8 - 1 / 14 ≤
      Zs + C1 * Zm - 2 * π ^ (1 - 2 * t) / Real.Gamma (1 - 2 * t) * (2 / S) ^ (1 - 2 * t) * kappa (π * S) := by
    have hcK : π * Real.exp 2 * TB t / 2 * (u / S) ≤ 3141593 / 1000000 * ((27182818286 / 10000000000) *
        (27182818286 / 10000000000)) * (10570 / 10000) / 2 * (16 * (1 / (27182818283 / 10000000000 : ℝ) ^ 8)) := by
      rw [he2]
      apply mul_le_mul _ (huS.trans (by linarith)) (by positivity) (by positivity)
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact mul_le_mul (mul_le_mul hpU (mul_le_mul heU heU (by positivity) (by norm_num)) (by positivity)
        (by norm_num)) hTle (by linarith) (by norm_num)
    have hcE : 4 * π * Real.exp 1 * kapB / S ≤ 4 * (3141593 / 1000000) * (27182818286 / 10000000000) *
        (926 / 100000) * (1 / (27182818283 / 10000000000 : ℝ) ^ 8) := by
      rw [div_eq_mul_one_div]
      apply mul_le_mul _ (hSinv.trans he8) (by positivity) (by positivity)
      apply mul_le_mul (mul_le_mul_of_nonneg_left heU (by positivity) |>.trans
        (mul_le_mul_of_nonneg_right (by linarith) (by norm_num))) kapB_le (by unfold kapB; norm_num) (by positivity)
    have hnum : 3141593 / 1000000 * ((27182818286 / 10000000000 : ℝ) * (27182818286 / 10000000000)) *
        (10570 / 10000) / 2 * (16 * (1 / (27182818283 / 10000000000 : ℝ) ^ 8)) +
        4 * (3141593 / 1000000) * (27182818286 / 10000000000) * (926 / 100000) *
          (1 / (27182818283 / 10000000000 : ℝ) ^ 8) ≤ 1 / 14 := by norm_num
    have : C1 * Zm = -Kq := by rw [hKq]; ring
    rw [this]
    linarith [hE21, hE2, hcK, hcE, hKP, hF1]
  -- F8: the ratio, and conclude
  have hratio : t * (π * Real.exp 1 * TB t / 2 * (1 - 4 * t) / (t * (1 - y)) + 4 * π * Real.exp 1 * kapB) ≤
      3 * (1 + 1 / 2 / (1 - 4 * t) + 1 / 8 - 1 / 14) := by
    have hnum := lprimeB_numeric ht0 ht16
    have e : t * (π * Real.exp 1 * TB t / 2 * (1 - 4 * t) / (t * (1 - y)) + 4 * π * Real.exp 1 * kapB) =
        π * Real.exp 1 / 2 * TB t * (1 - 4 * t) / (1 - y) + 4 * π * Real.exp 1 * kapB * t := by
      field_simp
    rw [e]
    refine le_trans ?_ hnum
    have hpe : π * Real.exp 1 ≤ 3141593 / 1000000 * (27182818286 / 10000000000) :=
      mul_le_mul hpU heU (Real.exp_pos _).le (by norm_num)
    have hT0 : 0 ≤ TB t := by linarith
    have h4t : 0 ≤ 1 - 4 * t := by linarith
    have hk0' : 0 ≤ kapB := by unfold kapB; norm_num
    have a1 : π * Real.exp 1 / 2 * TB t * (1 - 4 * t) / (1 - y) ≤
        3141593 / 1000000 * (27182818286 / 10000000000) / 2 * TB t * (1 - 4 * t) / (1 - y) := by
      apply div_le_div_of_nonneg_right _ (by linarith)
      apply mul_le_mul_of_nonneg_right _ h4t
      apply mul_le_mul_of_nonneg_right _ hT0
      linarith
    have a2 : 4 * π * Real.exp 1 * kapB * t ≤ 4 * (3141593 / 1000000) * (27182818286 / 10000000000) * kapB * t := by
      apply mul_le_mul_of_nonneg_right _ ht0.le
      apply mul_le_mul_of_nonneg_right _ hk0'
      linarith
    linarith
  have hMb0 : 0 < π * Real.exp 1 * TB t / 2 * (1 - 4 * t) / (t * (1 - y)) + 4 * π * Real.exp 1 * kapB := by
    have h1 : 0 ≤ π * Real.exp 1 * TB t / 2 * (1 - 4 * t) / (t * (1 - y)) := by
      have : 0 ≤ 1 - 4 * t := by linarith
      have : 0 < 1 - y := by linarith
      positivity
    have h2 : 0 < 4 * π * Real.exp 1 * kapB := by unfold kapB; positivity
    linarith
  have hPl0 : 0 < 1 + 1 / 2 / (1 - 4 * t) + 1 / 8 - 1 / 14 := by linarith
  have hm0 : 0 ≤ (1 - 2 * t / (1 - 2 * t)) * Kq * (2 * t * Kq / ((1 - 2 * t) * Zs)) ^ (2 * t / (1 - 4 * t)) +
      2 * π ^ (1 - 2 * t) / Real.Gamma (1 - 2 * t) * (2 / S) ^ (1 - 2 * t) * kappa (3 * π / 2) := by
    have hc0 : 0 ≤ 1 - 2 * t / (1 - 2 * t) := by
      rw [sub_nonneg, div_le_one (by linarith)]; linarith
    have hb : 0 ≤ (2 * t * Kq / ((1 - 2 * t) * Zs)) ^ (2 * t / (1 - 4 * t)) := Real.rpow_nonneg (by
      apply div_nonneg (by positivity); have : 0 < Zs := by linarith
      nlinarith) _
    have := mul_nonneg (mul_nonneg hc0 hK0) hb
    have := mul_nonneg hpref0 hk0
    linarith
  have hm : (1 - 2 * t / (1 - 2 * t)) * Kq * (2 * t * Kq / ((1 - 2 * t) * Zs)) ^ (2 * t / (1 - 4 * t)) +
      2 * π ^ (1 - 2 * t) / Real.Gamma (1 - 2 * t) * (2 / S) ^ (1 - 2 * t) * kappa (3 * π / 2) ≤
      (π * Real.exp 1 * TB t / 2 * (1 - 4 * t) / (t * (1 - y)) + 4 * π * Real.exp 1 * kapB) / S := by
    rw [add_div]; linarith [hF5, hE2]
  have hfin := final_B hS0 ht0 hcore hP7 hPl0 hm0 hm hMb0 hratio
  have e : 1 / 3 * Real.sqrt (dOf m) / Real.log (dOf m) = 1 / 3 * S * t := by
    rw [hSdef, htdef, hudef, hDdef]; ring
  rw [e]; exact hfin

end BoundariesOfClass.Numerics
