import Mathlib

/-!
# BoundariesOfClass.PolyaVinogradov.Geometric: incomplete exponential sums on `ZMod q`

Pinned environment: Lean v4.34.1, Mathlib d13f23b. Mathlib only.

Write `e(x) = ZMod.stdAddChar x = exp(2πi x/q)` for `x ∈ ZMod q`, and `v = j.val ∈ [0, q)`.

* `norm_stdAddChar_sub_one`: `‖e(j) - 1‖ = 2 sin(π v/q)`.
* `two_mul_min_div_le_sin`: `sin(π v/q) ≥ 2 min(v, q - v)/q` (Jordan's inequality `Real.mul_le_sin`, after the
  reflection `v ↦ q - v`).
* `norm_sum_stdAddChar_le`: for `j ≠ 0`, every sum `Σ_{i<ℓ} e(j(a + i))` has norm at most `q/(2 min(v, q - v))`.
  It is a geometric sum, of norm at most `2/‖e(j) - 1‖ = 1/sin(π v/q)`.
* `sum_div_min_le`: `Σ_{0 ≤ v < q} q/(2 min(v, q - v)) ≤ q H_{⌊q/2⌋}`. The `v = 0` term is `q/0 = 0`.
-/

set_option autoImplicit false

namespace BoundariesOfClass.PolyaVinogradov

open ZMod Finset

variable {q : ℕ} [NeZero q]

/-- `e(x)` has norm one. -/
lemma norm_stdAddChar (x : ZMod q) : ‖stdAddChar x‖ = 1 := by
  rw [stdAddChar_apply]; exact Circle.norm_coe _

/-- `e(j) = exp(i · 2π v/q)`. -/
lemma stdAddChar_eq_exp (j : ZMod q) :
    stdAddChar j = Complex.exp (Complex.I * ((2 * Real.pi * j.val / q : ℝ) : ℂ)) := by
  rw [stdAddChar_apply, toCircle_apply]
  congr 1
  push_cast
  ring

/-- `0 < sin(π v/q)` for `0 < v < q`. -/
lemma sin_pos_of_ne_zero {j : ZMod q} (hj : j ≠ 0) : 0 < Real.sin (Real.pi * j.val / q) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hv0 : 0 < j.val := Nat.pos_of_ne_zero ((ZMod.val_ne_zero j).mpr hj)
  have hv : (0 : ℝ) < j.val := by exact_mod_cast hv0
  have hvq : (j.val : ℝ) < q := by exact_mod_cast ZMod.val_lt j
  apply Real.sin_pos_of_pos_of_lt_pi
  · positivity
  · rw [mul_div_assoc]
    have : (j.val : ℝ) / q < 1 := (div_lt_one hq).mpr hvq
    nlinarith [Real.pi_pos]

/-- **`‖e(j) - 1‖ = 2 sin(π v/q)`** for `j ≠ 0`. -/
lemma norm_stdAddChar_sub_one {j : ZMod q} (hj : j ≠ 0) :
    ‖stdAddChar j - 1‖ = 2 * Real.sin (Real.pi * j.val / q) := by
  rw [stdAddChar_eq_exp, Complex.norm_exp_I_mul_ofReal_sub_one]
  have h : 2 * Real.pi * j.val / q / 2 = Real.pi * j.val / q := by ring
  rw [h, Real.norm_eq_abs, abs_of_pos (by have := sin_pos_of_ne_zero hj; positivity)]

/-- **Jordan's inequality, reflected:** `2 min(v, q - v)/q ≤ sin(π v/q)` for `v = j.val`. -/
lemma two_mul_min_div_le_sin (j : ZMod q) :
    2 * ((min j.val (q - j.val) : ℕ) : ℝ) / q ≤ Real.sin (Real.pi * j.val / q) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hvq : j.val < q := ZMod.val_lt j
  have hpi := Real.pi_pos
  rcases le_total (2 * j.val) q with h | h
  · -- `v ≤ q/2`: Jordan at `x = π v/q ∈ [0, π/2]`
    have hmin : min j.val (q - j.val) = j.val := min_eq_left (by omega)
    rw [hmin]
    have hx0 : 0 ≤ Real.pi * j.val / q := by positivity
    have hx1 : Real.pi * j.val / q ≤ Real.pi / 2 := by
      rw [div_le_div_iff₀ hq (by norm_num)]
      have : (2 * j.val : ℝ) ≤ q := by exact_mod_cast h
      nlinarith
    have hJ := Real.mul_le_sin hx0 hx1
    have he : 2 / Real.pi * (Real.pi * j.val / q) = 2 * (j.val : ℝ) / q := by
      field_simp
    linarith
  · -- `v ≥ q/2`: `sin(π v/q) = sin(π (q - v)/q)`, then Jordan
    have hmin : min j.val (q - j.val) = q - j.val := min_eq_right (by omega)
    rw [hmin, Nat.cast_sub hvq.le]
    have hrefl : Real.sin (Real.pi * j.val / q) = Real.sin (Real.pi * (q - j.val) / q) := by
      rw [← Real.sin_pi_sub]
      congr 1
      field_simp
    rw [hrefl]
    have hv : (j.val : ℝ) < q := by exact_mod_cast hvq
    have hx0 : 0 ≤ Real.pi * (q - j.val) / q := by
      have : (0 : ℝ) ≤ q - j.val := by linarith
      positivity
    have hx1 : Real.pi * (q - j.val) / q ≤ Real.pi / 2 := by
      rw [div_le_div_iff₀ hq (by norm_num)]
      have : (q : ℝ) ≤ 2 * j.val := by exact_mod_cast h
      nlinarith
    have hJ := Real.mul_le_sin hx0 hx1
    have he : 2 / Real.pi * (Real.pi * (q - j.val) / q) = 2 * ((q : ℝ) - j.val) / q := by
      field_simp
    linarith

/-- `e(j(a + i)) = e(ja) e(j)^i`. -/
lemma stdAddChar_mul_add (j a : ZMod q) (i : ℕ) :
    stdAddChar (j * (a + (i : ZMod q))) = stdAddChar (j * a) * stdAddChar j ^ i := by
  rw [mul_add, AddChar.map_add_eq_mul, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, mul_comm (i : ZMod q)]

/-- **The incomplete exponential sum.** For `j ≠ 0`, `‖Σ_{i<ℓ} e(j(a + i))‖ ≤ q/(2 min(v, q - v))`. -/
theorem norm_sum_stdAddChar_le {j : ZMod q} (hj : j ≠ 0) (a : ZMod q) (ℓ : ℕ) :
    ‖∑ i ∈ range ℓ, stdAddChar (j * (a + (i : ZMod q)))‖ ≤ q / (2 * ((min j.val (q - j.val) : ℕ) : ℝ)) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hz1 : stdAddChar j ≠ 1 := by
    intro h
    apply hj
    rw [← AddChar.map_zero_eq_one (stdAddChar (N := q))] at h
    exact (ZMod.injective_stdAddChar (N := q)) h
  have hsin := sin_pos_of_ne_zero hj
  have hmin0 : 0 < min j.val (q - j.val) := by
    have := Nat.pos_of_ne_zero ((ZMod.val_ne_zero j).mpr hj)
    have := ZMod.val_lt j
    omega
  have hm : (0 : ℝ) < ((min j.val (q - j.val) : ℕ) : ℝ) := by exact_mod_cast hmin0
  simp_rw [stdAddChar_mul_add, ← Finset.mul_sum]
  rw [geom_sum_eq hz1, norm_mul, norm_stdAddChar, one_mul, norm_div, norm_stdAddChar_sub_one hj]
  have hnum : ‖stdAddChar j ^ ℓ - 1‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_pow, norm_stdAddChar, one_pow, norm_one]
    norm_num
  have hJ := two_mul_min_div_le_sin j
  -- `‖z^ℓ - 1‖/(2 sin) ≤ 1/sin ≤ q/(2 min)`
  calc ‖stdAddChar j ^ ℓ - 1‖ / (2 * Real.sin (Real.pi * j.val / q))
      ≤ 2 / (2 * Real.sin (Real.pi * j.val / q)) :=
        div_le_div_of_nonneg_right hnum (by positivity)
    _ = 1 / Real.sin (Real.pi * j.val / q) := by field_simp
    _ ≤ 1 / (2 * ((min j.val (q - j.val) : ℕ) : ℝ) / q) :=
        one_div_le_one_div_of_le (by positivity) hJ
    _ = q / (2 * ((min j.val (q - j.val) : ℕ) : ℝ)) := by field_simp

/-- The half-range reciprocal: `f(v) = 1/v` for `2v ≤ q`, and `0` otherwise (`1/0 = 0` at `v = 0`). -/
noncomputable def halfRecip (q v : ℕ) : ℝ := if 2 * v ≤ q then 1 / (v : ℝ) else 0

lemma halfRecip_nonneg (q v : ℕ) : 0 ≤ halfRecip q v := by
  unfold halfRecip; split_ifs <;> positivity

/-- `Σ_{v<q} f(v) = H_{⌊q/2⌋}`. -/
lemma sum_halfRecip (q : ℕ) : ∑ v ∈ range q, halfRecip q v = (harmonic (q / 2) : ℝ) := by
  rcases Nat.lt_or_ge q 2 with hq | hq
  · interval_cases q <;> simp [halfRecip, harmonic]
  have hsplit : q = (q / 2 + 1) + (q - (q / 2 + 1)) := by omega
  rw [hsplit, Finset.sum_range_add, ← hsplit]
  have htail : ∑ i ∈ range (q - (q / 2 + 1)), halfRecip q (q / 2 + 1 + i) = 0 :=
    Finset.sum_eq_zero fun i _ => by unfold halfRecip; rw [ite_eq_right (by omega)]
  rw [htail, add_zero, Finset.sum_range_succ', harmonic]
  have h0 : halfRecip q 0 = 0 := by simp [halfRecip]
  rw [h0, add_zero]
  push_cast
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  unfold halfRecip
  rw [ite_eq_left (by omega)]
  push_cast
  ring

/-- The reflected sum: `Σ_{v<q} f(q - v) = Σ_{v<q} f(v)`. -/
lemma sum_halfRecip_reflect (q : ℕ) [NeZero q] :
    ∑ v ∈ range q, halfRecip q (q - v) = ∑ v ∈ range q, halfRecip q v := by
  have hq := NeZero.pos q
  have hq0 : halfRecip q q = 0 := by unfold halfRecip; rw [ite_eq_right (by omega)]
  have h00 : halfRecip q (q - q) = 0 := by simp [halfRecip]
  have h1 := Finset.sum_range_succ (fun v => halfRecip q (q - v)) q
  have h2 := Finset.sum_range_succ (fun v => halfRecip q v) q
  have h3 := Finset.sum_range_reflect (fun v => halfRecip q v) (q + 1)
  simp only [Nat.add_sub_cancel] at h3
  rw [h00, add_zero] at h1
  rw [hq0, add_zero] at h2
  linarith

/-- **`Σ_{0 ≤ v < q} q/(2 min(v, q - v)) ≤ q H_{⌊q/2⌋}`.** -/
theorem sum_div_min_le :
    ∑ v ∈ range q, (q : ℝ) / (2 * ((min v (q - v) : ℕ) : ℝ)) ≤ q * (harmonic (q / 2) : ℝ) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  -- termwise, `q/(2 min(v, q - v)) ≤ (q/2)(f(v) + f(q - v))`
  have hterm : ∀ v ∈ range q, (q : ℝ) / (2 * ((min v (q - v) : ℕ) : ℝ)) ≤
      (q : ℝ) / 2 * (halfRecip q v + halfRecip q (q - v)) := by
    intro v hv
    have hv' := Finset.mem_range.mp hv
    rw [div_mul_eq_div_div, div_eq_mul_one_div ((q : ℝ) / 2)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rcases le_total (2 * v) q with h | h
    · rw [min_eq_left (by omega)]
      have : halfRecip q v = 1 / (v : ℝ) := by unfold halfRecip; rw [ite_eq_left h]
      rw [this]
      linarith [halfRecip_nonneg q (q - v)]
    · rw [min_eq_right (by omega)]
      have : halfRecip q (q - v) = 1 / ((q - v : ℕ) : ℝ) := by unfold halfRecip; rw [ite_eq_left (by omega)]
      rw [this]
      linarith [halfRecip_nonneg q v]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib, sum_halfRecip_reflect, sum_halfRecip]
  linarith

end BoundariesOfClass.PolyaVinogradov
