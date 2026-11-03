import BoundariesOfClass.Numerics.Thresholds

/-!
# BoundariesOfClass.Numerics.PowerBound: the power lower bound `d^{7/16}/17 ≤ h` for `d ≥ 1000`

Pinned environment: Lean v4.34.1, Mathlib d13f23b. Two pieces, both at `σ = 7/8` through `lt_classNumber_of_bounds_real`
(every class charged its exact floor, `K_{1/2}` remainder):

* **Head, `1000 ≤ d ≤ 39001`.** Five intervals. On each, a threshold theorem of `Thresholds` gives `h ≥ N + 1`, and
  `d^7 ≤ (17(N + 1))^16` at the right end gives `d^{7/16}/17 ≤ N + 1`.
* **Tail, `d ≥ 39001`.** The threshold theorem at `X = d` itself, with `Hc = d^{7/16}/17` and data in `w = d^{1/16}`:
  `q = w⁸`, `r = c_r w⁻⁶`, `s = c_s w⁻¹`, `e = c_e w⁻⁷`. The non-principal classes then cost `A w⁻⁷` each, with `A`
  a constant, so `(Hc - 1) A w⁻⁷ ≤ A/17`, and the principal class pays for it once `d ≥ 39001`.

The constants are from numerics/pprime_plan.py.
-/

set_option autoImplicit false

open NumberField CN1.Finite

namespace BoundariesOfClass.Numerics

/-- `D⁷ ≤ M¹⁶` and `M ≤ 17 h` give `D^{7/16}/17 ≤ h`. -/
lemma rpow_div_le_of_pow_le {D M h : ℝ} (hD : 0 ≤ D) (hM : 0 ≤ M) (hpow : D ^ 7 ≤ M ^ 16) (hMh : M ≤ 17 * h) :
    D ^ ((7 : ℝ) / 16) / 17 ≤ h := by
  have h1 : D ^ ((7 : ℝ) / 16) ≤ M :=
    HCN.Numerics.rpow_le_of_pow_le (k := 7) (n := 16) hD hM (by norm_num) (by norm_num) hpow
  linarith

/-- One head interval: `X_N ≤ d ≤ B` with `B⁷ ≤ (17(N + 1))¹⁶`. -/
lemma head_step {D B : ℝ} {N : ℕ} {hcl : ℕ} (hD : 0 ≤ D) (hDB : D ≤ B) (hB : B ^ 7 ≤ (17 * ((N : ℝ) + 1)) ^ 16)
    (hN : N < hcl) : D ^ ((7 : ℝ) / 16) / 17 ≤ (hcl : ℝ) := by
  have hN' : (N : ℝ) + 1 ≤ hcl := by exact_mod_cast hN
  refine rpow_div_le_of_pow_le hD (by positivity) ((pow_le_pow_left₀ hD hDB 7).trans hB) (by linarith)

set_option maxHeartbeats 1600000 in
/-- **The tail, `d ≥ 39001`.** -/
theorem rpow_lt_classNumber_tail {K : Type*} [Field K] [NumberField K] {m : ℕ} {α : K} (hα : α ^ 2 = -(m : K))
    (hK : Module.finrank ℚ K = 2) (hm : Squarefree m) (hm1 : m ≠ 1) (hm3 : m ≠ 3)
    (hd : (39001 : ℝ) ≤ (dOf m : ℝ)) :
    (dOf m : ℝ) ^ ((7 : ℝ) / 16) / 17 < (classNumber K : ℝ) := by
  set D : ℝ := (dOf m : ℝ) with hDdef
  have hD0 : 0 < D := by linarith
  set w : ℝ := D ^ ((1 : ℝ) / 16) with hw
  have hw0 : 0 < w := Real.rpow_pos_of_pos hD0 _
  have hwne : w ≠ 0 := hw0.ne'
  have hw16 : w ^ 16 = D := by
    rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul hD0.le]; norm_num
  have hw7 : D ^ ((7 : ℝ) / 16) = w ^ 7 := by
    rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul hD0.le]; norm_num
  have hwlo : (484041 / 250000 : ℝ) ≤ w := by
    by_contra h
    push Not at h
    have h1 := pow_lt_pow_left₀ h hw0.le (by norm_num : (16 : ℕ) ≠ 0)
    rw [hw16] at h1
    norm_num at h1
    linarith
  rw [hw7]
  -- the data
  set cr : ℝ := 1094817 / 1000000 with hcr
  set cs : ℝ := 135531 / 125000 with hcs
  set ce : ℝ := 1834009 / 1000000 with hce
  set u6 : ℝ := (w ^ 6)⁻¹ with hu6
  set u7 : ℝ := (w ^ 7)⁻¹ with hu7
  have hu60 : 0 ≤ u6 := by positivity
  have hu70 : 0 ≤ u7 := by positivity
  have hw6lo : (484041 / 250000 : ℝ) ^ 6 ≤ w ^ 6 := pow_le_pow_left₀ (by norm_num) hwlo 6
  have hw7lo : (484041 / 250000 : ℝ) ^ 7 ≤ w ^ 7 := pow_le_pow_left₀ (by norm_num) hwlo 7
  have hu6le : u6 ≤ ((484041 / 250000 : ℝ) ^ 6)⁻¹ := inv_anti₀ (by positivity) hw6lo
  have hu7le : u7 ≤ ((484041 / 250000 : ℝ) ^ 7)⁻¹ := inv_anti₀ (by positivity) hw7lo
  have hw8lo : (484041 / 250000 : ℝ) ^ 8 ≤ w ^ 8 := pow_le_pow_left₀ (by norm_num) hwlo 8
  have hHc : (1 : ℝ) ≤ w ^ 7 / 17 := by
    rw [le_div_iff₀ (by norm_num)]
    have : (17 : ℝ) ≤ (484041 / 250000 : ℝ) ^ 7 := by norm_num
    linarith
  -- the remainder factor at `q = w⁸`
  set a : ℝ := 1 + 3141592 / 1000000 * w ^ 8 / 4 with ha
  have ha2 : 2 ≤ a := by
    rw [ha]
    have : (1 : ℝ) ≤ (484041 / 250000 : ℝ) ^ 8 := by norm_num
    nlinarith
  have hy : 1 / a ^ 4 ≤ 1 / 16 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (2 : ℝ) ^ 4 ≤ a ^ 4 := pow_le_pow_left₀ (by norm_num) ha2 4
    linarith
  have hY : (1 / a ^ 4) / (1 - 1 / a ^ 4) ^ 2 ≤ (1 / 16) / (1 - 1 / 16) ^ 2 :=
    div_one_sub_sq_mono (by positivity) hy (by norm_num)
  have hY0 : 0 ≤ (1 / a ^ 4) / (1 - 1 / a ^ 4) ^ 2 := by
    apply div_nonneg (by positivity) (sq_nonneg _)
  refine lt_classNumber_of_bounds_real hα hK hm hm1 hm3 (w ^ 7 / 17) hHc (X := D) (q := w ^ 8) (r := cr * u6)
    (s := cs * w⁻¹) (e := ce * u7) hD0 le_rfl (by positivity) ?_ (by positivity) ?_ (by positivity) ?_
    (by positivity) ?_ ?_
  · -- `q² ≤ X`
    rw [← hw16]; apply le_of_eq; ring
  · -- `(4/(πₗ X))³ ≤ r⁸`
    have e1 : (4 / (3141592 / 1000000 * D)) ^ 3 = (4 / (3141592 / 1000000)) ^ 3 * u6 ^ 8 := by
      rw [← hw16, hu6]; field_simp
    rw [e1, mul_pow]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    rw [hcr]; norm_num
  · -- `K̄/(7 · 1.96232) ≤ s⁶`
    have e1 : 6807 / 2500 * (21755 / 10000) * (cr * u6) * (344129 / 100000) / (7 * (196232 / 100000)) =
        6807 / 2500 * (21755 / 10000) * cr * (344129 / 100000) / (7 * (196232 / 100000)) * u6 := by ring
    have e2 : (cs * w⁻¹) ^ 6 = cs ^ 6 * u6 := by rw [hu6, mul_pow, inv_pow]
    rw [e1, e2]
    apply mul_le_mul_of_nonneg_right _ hu60
    rw [hcr, hcs]; norm_num
  · -- `(2/q)⁷ ≤ e⁸`
    have e1 : (2 / w ^ 8) ^ 7 = 2 ^ 7 * (u7 ^ 8) := by rw [hu7]; field_simp
    rw [e1, mul_pow]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    rw [hce]; norm_num
  · -- the final inequality
    set Y : ℝ := (1 / a ^ 4) / (1 - 1 / a ^ 4) ^ 2 with hYdef
    set κ : ℝ := (4767 / 50000 : ℝ) ^ 2 / (1 - (4767 / 50000 : ℝ) ^ 2) ^ 2 with hκ
    set A : ℝ := 6 / 7 * (6807 / 2500 * (21755 / 10000) * cr * (344129 / 100000)) * cs +
      2 * (6807 / 2500) / (10861 / 10000) * ce * κ with hA
    have hw7u : w ^ 7 * u7 = 1 := by rw [hu7]; exact mul_inv_cancel₀ (pow_ne_zero 7 hwne)
    have hu6w : u6 * w⁻¹ = u7 := by rw [hu6, hu7, ← mul_inv, ← pow_succ]
    have hexpr : 196232 / 100000 - 6807 / 2500 * (21755 / 10000) * (cr * u6) * (344129 / 100000) -
        2 * (6807 / 2500) / (10861 / 10000) * (ce * u7) * Y -
        (w ^ 7 / 17 - 1) * (6 / 7 * (6807 / 2500 * (21755 / 10000) * (cr * u6) * (344129 / 100000)) * (cs * w⁻¹) +
          2 * (6807 / 2500) / (10861 / 10000) * (ce * u7) * κ) =
        196232 / 100000 - 6807 / 2500 * (21755 / 10000) * cr * (344129 / 100000) * u6 -
          2 * (6807 / 2500) / (10861 / 10000) * ce * (u7 * Y) - A / 17 + A * u7 := by
      have h1 : 6 / 7 * (6807 / 2500 * (21755 / 10000) * (cr * u6) * (344129 / 100000)) * (cs * w⁻¹) +
          2 * (6807 / 2500) / (10861 / 10000) * (ce * u7) * κ = A * u7 := by
        rw [hA, ← hu6w]; ring
      rw [h1]
      have h2 : (w ^ 7 / 17 - 1) * (A * u7) = A / 17 * (w ^ 7 * u7) - A * u7 := by ring
      rw [h2, hw7u]; ring
    rw [hexpr]
    have hA0 : A ≤ 2083 / 100 := by rw [hA, hκ, hcr, hcs, hce]; norm_num
    have hA00 : 0 ≤ A := by rw [hA, hκ, hcr, hcs, hce]; norm_num
    have hKt : 6807 / 2500 * (21755 / 10000) * cr * (344129 / 100000) * u6 ≤
        6807 / 2500 * (21755 / 10000) * cr * (344129 / 100000) * ((484041 / 250000 : ℝ) ^ 6)⁻¹ :=
      mul_le_mul_of_nonneg_left hu6le (by rw [hcr]; norm_num)
    have huY : u7 * Y ≤ ((484041 / 250000 : ℝ) ^ 7)⁻¹ * ((1 / 16) / (1 - 1 / 16) ^ 2) :=
      mul_le_mul hu7le hY hY0 (by positivity)
    have hE : 2 * (6807 / 2500) / (10861 / 10000) * ce * (u7 * Y) ≤
        2 * (6807 / 2500) / (10861 / 10000) * ce * (((484041 / 250000 : ℝ) ^ 7)⁻¹ * ((1 / 16) / (1 - 1 / 16) ^ 2)) :=
      mul_le_mul_of_nonneg_left huY (by rw [hce]; norm_num)
    have hAu : 0 ≤ A * u7 := mul_nonneg hA00 hu70
    have hnum : 0 < 196232 / 100000 - 6807 / 2500 * (21755 / 10000) * cr * (344129 / 100000) *
        ((484041 / 250000 : ℝ) ^ 6)⁻¹ -
        2 * (6807 / 2500) / (10861 / 10000) * ce * (((484041 / 250000 : ℝ) ^ 7)⁻¹ * ((1 / 16) / (1 - 1 / 16) ^ 2)) -
        2083 / 100 / 17 := by
      rw [hcr, hce]; norm_num
    linarith

/-- **(P′) in `dOf m` form**: for `d ≥ 1000`, `d^{7/16}/17 ≤ h(K)`. -/
theorem rpow_le_classNumber {K : Type*} [Field K] [NumberField K] {m : ℕ} {α : K} (hα : α ^ 2 = -(m : K))
    (hK : Module.finrank ℚ K = 2) (hm : Squarefree m) (hm1 : m ≠ 1) (hm3 : m ≠ 3)
    (hd : (1000 : ℝ) ≤ (dOf m : ℝ)) :
    (dOf m : ℝ) ^ ((7 : ℝ) / 16) / 17 ≤ (classNumber K : ℝ) := by
  have hD0 : (0 : ℝ) ≤ (dOf m : ℝ) := by linarith
  rcases le_or_gt (dOf m : ℝ) 3166 with h1 | h1
  · exact head_step (N := 1) hD0 h1 (by norm_num)
      (lt_classNumber_of_le_dOf_le_one hα hK hm hm1 hm3 (by linarith))
  rcases le_or_gt (dOf m : ℝ) 7998 with h2 | h2
  · exact head_step (N := 2) hD0 h2 (by norm_num)
      (lt_classNumber_of_le_dOf_le_two hα hK hm hm1 hm3 (by linarith))
  rcases le_or_gt (dOf m : ℝ) 15438 with h3 | h3
  · exact head_step (N := 3) hD0 h3 (by norm_num)
      (lt_classNumber_of_le_dOf_le_three hα hK hm hm1 hm3 (by linarith))
  rcases le_or_gt (dOf m : ℝ) 25709 with h4 | h4
  · exact head_step (N := 4) hD0 h4 (by norm_num)
      (lt_classNumber_of_le_dOf_le_four hα hK hm hm1 hm3 (by linarith))
  rcases le_or_gt (dOf m : ℝ) 39001 with h5 | h5
  · exact head_step (N := 5) hD0 h5 (by norm_num)
      (lt_classNumber_of_le_dOf_le_five hα hK hm hm1 hm3 (by linarith))
  exact (rpow_lt_classNumber_tail hα hK hm hm1 hm3 h5.le).le

end BoundariesOfClass.Numerics
