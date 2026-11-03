import BoundariesOfClass.ClassNumberFormula.CharSum

/-!
# BoundariesOfClass.ClassNumberFormula.LOne: the explicit bound `‖L(1, χ)‖ ≤ log q + 7/6`

Pinned environment: Lean v4.34.1, Mathlib d13f23b. Mathlib only.

The classical partial-summation estimate, worked at real `s > 1` (where the L-series converges absolutely) and carried
to `s = 1` by continuity of Mathlib's `DirichletCharacter.LFunction` (entire for `χ ≠ 1`):

* `norm_LFunction_le_of_one_lt`: for real `s > 1`, `‖L(s, χ)‖ ≤ H_{q-1} + 1/2`. Split the series at `n = q`. The head is
  at most `Σ_{1 ≤ n < q} 1/n = H_{q-1}`. The tail is at most `(q/2) q^{-s} ≤ 1/2`, by Abel's inequality against the
  interval sums of `χ` (`CharSum.lean`).
* `norm_LFunction_one_le_harmonic`: the same bound at `s = 1`.
* `harmonic_pred_le`: `H_{q-1} ≤ log q + 2/3` for `q ≥ 7` (Mathlib's `eulerMascheroniSeq'` is decreasing, and is below
  `2/3` at `6`).
* `norm_LFunction_one_le`: **`‖L(1, χ)‖ ≤ log q + 7/6`** for every non-trivial Dirichlet character of level `q ≥ 7`.
-/

set_option autoImplicit false

namespace BoundariesOfClass.ClassNumberFormula

open Finset Filter Topology

variable {q : ℕ} [NeZero q]

omit [NeZero q] in
/-- The terms of the L-series of `χ` at real `s ≥ 1` have norm at most `1/n`. -/
lemma norm_term_le_inv (χ : DirichletCharacter ℂ q) {s : ℝ} (hs : 1 ≤ s) (n : ℕ) :
    ‖LSeries.term (fun n => χ n) s n‖ ≤ if n = 0 then 0 else (n : ℝ)⁻¹ := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [LSeries.term_of_ne_zero hn, ite_eq_right hn, norm_div, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn),
    Complex.ofReal_re]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hpow : (n : ℝ) ≤ (n : ℝ) ^ s := by
    simpa using Real.rpow_le_rpow_of_exponent_le hn1 hs
  have hpos : (0 : ℝ) < n := by linarith
  calc ‖χ (n : ZMod q)‖ / (n : ℝ) ^ s ≤ 1 / (n : ℝ) ^ s :=
        div_le_div_of_nonneg_right (DirichletCharacter.norm_le_one χ _) (by positivity)
    _ ≤ 1 / (n : ℝ) := one_div_le_one_div_of_le hpos hpow
    _ = (n : ℝ)⁻¹ := one_div _

/-- The head of the series: `Σ_{n<q} ‖term n‖ ≤ H_{q-1}`. -/
lemma sum_norm_term_le_harmonic (χ : DirichletCharacter ℂ q) {s : ℝ} (hs : 1 ≤ s) :
    ∑ n ∈ range q, ‖LSeries.term (fun n => χ n) s n‖ ≤ (harmonic (q - 1) : ℝ) := by
  obtain ⟨p, hp⟩ : ∃ p, q = p + 1 := ⟨q - 1, by have := NeZero.pos q; omega⟩
  rw [show range q = range (p + 1) by rw [hp], show q - 1 = p by omega, Finset.sum_range_succ']
  have h0 : ‖LSeries.term (fun n => χ n) s 0‖ = 0 := by simp
  rw [h0, add_zero, harmonic]
  push_cast
  refine Finset.sum_le_sum fun i _ => ?_
  have := norm_term_le_inv χ hs (i + 1)
  rw [ite_eq_right (Nat.succ_ne_zero i)] at this
  simpa using this

/-- The tail of the series, by Abel's inequality: `‖Σ_{i<ℓ} term (q + i)‖ ≤ (q/2) q^{-s}`. -/
lemma norm_sum_term_tail_le (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℝ} (hs : 0 ≤ s) (ℓ : ℕ) :
    ‖∑ i ∈ range ℓ, LSeries.term (fun n => χ n) s (q + i)‖ ≤ (q : ℝ) / 2 * ((q : ℝ) ^ s)⁻¹ := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  set b : ℕ → ℝ := fun i => (((q + i : ℕ) : ℝ) ^ s)⁻¹ with hb
  have hterm : ∀ i, LSeries.term (fun n => χ n) s (q + i) = (b i : ℂ) * χ ((q + i : ℕ) : ZMod q) := by
    intro i
    have hne : q + i ≠ 0 := by have := NeZero.pos q; omega
    rw [LSeries.term_of_ne_zero hne]
    simp only [hb]
    rw [Complex.ofReal_inv, Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_natCast, div_eq_mul_inv,
      mul_comm]
  simp_rw [hterm]
  have hanti : Antitone b := by
    intro i j hij
    simp only [hb]
    have hpos : (0 : ℝ) < ((q + i : ℕ) : ℝ) := by
      have := NeZero.pos q
      exact_mod_cast (by omega : 0 < q + i)
    refine inv_anti₀ (Real.rpow_pos_of_pos hpos s) (Real.rpow_le_rpow (Nat.cast_nonneg _) ?_ hs)
    exact_mod_cast Nat.add_le_add_left hij q
  have hb0 : ∀ n, 0 ≤ b n := fun n => by simp only [hb]; positivity
  have h := norm_sum_mul_le_of_antitone hanti hb0 (fun ℓ => norm_sum_range_le χ hχ q ℓ) ℓ
  have hb00 : b 0 = ((q : ℝ) ^ s)⁻¹ := by simp [hb]
  rw [hb00] at h
  exact h

/-- **The bound at real `s > 1`:** `‖L(s, χ)‖ ≤ H_{q-1} + 1/2`. -/
theorem norm_LFunction_le_of_one_lt (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℝ} (hs : 1 < s) :
    ‖χ.LFunction s‖ ≤ (harmonic (q - 1) : ℝ) + 1 / 2 := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hsre : 1 < (s : ℂ).re := by simpa using hs
  rw [DirichletCharacter.LFunction_eq_LSeries χ hsre]
  have hsum := (DirichletCharacter.LSeriesSummable_of_one_lt_re χ hsre).LSeriesHasSum
  -- the partial sums `Σ_{n < q + ℓ}` converge to the L-series
  have ht : Tendsto (fun ℓ => ∑ n ∈ range (q + ℓ), LSeries.term (fun n => χ n) s n) atTop
      (𝓝 (LSeries (fun n => χ n) s)) :=
    (HasSum.tendsto_sum_nat hsum).comp (tendsto_atTop_atTop_of_monotone (f := fun ℓ : ℕ => q + ℓ)
      (fun _ _ h => Nat.add_le_add_left h q) (fun b => ⟨b, Nat.le_add_left b q⟩))
  refine le_of_tendsto' ht.norm fun ℓ => ?_
  rw [Finset.sum_range_add]
  refine (norm_add_le _ _).trans (add_le_add ((norm_sum_le _ _).trans
    (sum_norm_term_le_harmonic χ hs.le)) ?_)
  refine (norm_sum_term_tail_le χ hχ (by linarith) ℓ).trans ?_
  -- `(q/2) q^{-s} ≤ (q/2) q^{-1} = 1/2`
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hpow : (q : ℝ) ≤ (q : ℝ) ^ s := by simpa using Real.rpow_le_rpow_of_exponent_le hq1 hs.le
  have : ((q : ℝ) ^ s)⁻¹ ≤ (q : ℝ)⁻¹ := inv_anti₀ hq0 hpow
  calc (q : ℝ) / 2 * ((q : ℝ) ^ s)⁻¹ ≤ (q : ℝ) / 2 * (q : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = 1 / 2 := by have := hq0.ne'; field_simp

/-- For `χ ≠ 1`, `L(s, χ) → L(1, χ)` as real `s → 1⁺` (Mathlib: `L(·, χ)` is entire). -/
lemma tendsto_LFunction_nhdsGT (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    Tendsto (fun s : ℝ => χ.LFunction s) (𝓝[>] 1) (𝓝 (χ.LFunction 1)) := by
  have h := ((DirichletCharacter.differentiable_LFunction hχ).continuous.tendsto (1 : ℂ)).comp
    (Complex.continuous_ofReal.tendsto (1 : ℝ))
  exact h.mono_left nhdsWithin_le_nhds

/-- **The bound at `s = 1`**, by continuity: `‖L(1, χ)‖ ≤ H_{q-1} + 1/2`. -/
theorem norm_LFunction_one_le_harmonic (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ‖χ.LFunction 1‖ ≤ (harmonic (q - 1) : ℝ) + 1 / 2 := by
  exact le_of_tendsto (tendsto_LFunction_nhdsGT χ hχ).norm (eventually_nhdsWithin_of_forall fun s hs =>
    norm_LFunction_le_of_one_lt χ hχ (Set.mem_Ioi.mp hs))

/-- `H_{q-1} ≤ log q + 2/3` for `q ≥ 7`. -/
lemma harmonic_pred_le {q : ℕ} (hq : 7 ≤ q) : (harmonic (q - 1) : ℝ) ≤ Real.log q + 2 / 3 := by
  have h6 : 6 ≤ q - 1 := by omega
  have hanti := Real.strictAnti_eulerMascheroniSeq'.antitone h6
  have hlt := Real.eulerMascheroniSeq'_six_lt_two_thirds
  have hdef : Real.eulerMascheroniSeq' (q - 1) = (harmonic (q - 1) : ℝ) - Real.log (q - 1 : ℕ) := by
    rw [Real.eulerMascheroniSeq', ite_eq_right (by omega)]
  have h6' : (6 : ℝ) ≤ (q - 1 : ℕ) := by exact_mod_cast h6
  have hlog : Real.log (q - 1 : ℕ) ≤ Real.log q :=
    Real.log_le_log (by linarith) (by exact_mod_cast Nat.sub_le q 1)
  linarith

/-- **`‖L(1, χ)‖ ≤ log q + 7/6`** for every non-trivial Dirichlet character of level `q ≥ 7`. -/
theorem norm_LFunction_one_le (hq : 7 ≤ q) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ‖χ.LFunction 1‖ ≤ Real.log q + 7 / 6 := by
  have h1 := norm_LFunction_one_le_harmonic χ hχ
  have h2 := harmonic_pred_le hq
  linarith

end BoundariesOfClass.ClassNumberFormula
