import BoundariesOfClass.ClassNumberFormula.LOne

/-!
# BoundariesOfClass.ClassNumberFormula.LOneEven: `‖L(1, χ)‖ ≤ ½ log q + 13/10` for characters of even level

Pinned environment: Lean v4.34.1, Mathlib d13f23b. Mathlib only.

A Dirichlet character of even level `q` vanishes at every even `n` (such `n` is not a unit mod `q`). So the head of the
partial-summation bound (`LOne.lean`) runs over odd `n < q` only, and
`Σ_{j<k} 1/(2j+1) = H_{2k} - ½ H_k ≤ ½ log k + log 2 + 5/12` for `k ≥ 6`. With the same tail `1/2`:

* `sum_odd_inv_eq`, `sum_odd_inv_le`: the odd harmonic sum, and its bound from Mathlib's two Euler–Mascheroni sequences.
* `norm_LFunction_le_of_one_lt_of_head`: for real `s > 1`, `‖L(s, χ)‖ ≤ H + 1/2` whenever the head `Σ_{n<q} ‖term n‖` is
  at most `H` for all `s ≥ 1` (the argument of `norm_LFunction_le_of_one_lt`, with the head left abstract).
* `norm_LFunction_one_le_of_even`: **`‖L(1, χ)‖ ≤ (log q)/2 + 13/10`** for every non-trivial `χ` of even level `q ≥ 12`.

The general odd-level case needs the Pólya–Vinogradov inequality and is not treated here.
-/

set_option autoImplicit false

namespace BoundariesOfClass.ClassNumberFormula

open Finset Filter Topology

/-- `Σ_{n < 2k} f n = Σ_{j < k} (f (2j) + f (2j+1))`. -/
lemma sum_range_two_mul (f : ℕ → ℝ) (k : ℕ) :
    ∑ n ∈ range (2 * k), f n = ∑ j ∈ range k, (f (2 * j) + f (2 * j + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    ring

/-- `Σ_{j<k} 1/(2j+1) = H_{2k} - ½ H_k`. -/
lemma sum_odd_inv_eq (k : ℕ) :
    ∑ j ∈ range k, ((2 * j + 1 : ℕ) : ℝ)⁻¹ = (harmonic (2 * k) : ℝ) - (harmonic k : ℝ) / 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, show 2 * (k + 1) = 2 * k + 1 + 1 by ring, harmonic_succ, harmonic_succ,
      harmonic_succ]
    push_cast
    field_simp
    ring

/-- `Σ_{j<k} 1/(2j+1) ≤ ½ log k + log 2 + 5/12` for `k ≥ 6`. -/
lemma sum_odd_inv_le {k : ℕ} (hk : 6 ≤ k) :
    ∑ j ∈ range k, ((2 * j + 1 : ℕ) : ℝ)⁻¹ ≤ Real.log k / 2 + Real.log 2 + 5 / 12 := by
  rw [sum_odd_inv_eq]
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  -- upper: `H_{2k} ≤ log (2k) + 2/3`
  have hup : (harmonic (2 * k) : ℝ) ≤ Real.log (2 * k : ℕ) + 2 / 3 := by
    have h1 := Real.strictAnti_eulerMascheroniSeq'.antitone (show 6 ≤ 2 * k by omega)
    have h2 := Real.eulerMascheroniSeq'_six_lt_two_thirds
    rw [Real.eulerMascheroniSeq', ite_eq_right (by omega)] at h1
    linarith
  -- lower: `H_k ≥ log (k+1) + 1/2 ≥ log k + 1/2`
  have hlo : Real.log k + 1 / 2 ≤ (harmonic k : ℝ) := by
    have h1 := Real.strictMono_eulerMascheroniSeq.monotone hk
    have h2 := Real.one_half_lt_eulerMascheroniSeq_six
    have h3 : Real.eulerMascheroniSeq k = (harmonic k : ℝ) - Real.log (k + 1) := rfl
    have : Real.log k ≤ Real.log (k + 1) := Real.log_le_log hk0 (by linarith)
    linarith
  have hlog2k : Real.log (2 * k : ℕ) = Real.log 2 + Real.log k := by
    push_cast
    exact Real.log_mul (by norm_num) hk0.ne'
  linarith

/-- For a character of even level, the terms at even `n` vanish. -/
lemma term_two_mul_eq_zero {q : ℕ} [NeZero q] (h2 : 2 ∣ q) (χ : DirichletCharacter ℂ q) (s : ℂ) (j : ℕ) :
    LSeries.term (fun n => χ n) s (2 * j) = 0 := by
  rcases eq_or_ne j 0 with rfl | hj
  · simp
  rw [LSeries.term_of_ne_zero (by omega), χ.map_nonunit, zero_div]
  rw [ZMod.isUnit_iff_coprime]
  intro hcop
  have := Nat.Coprime.coprime_dvd_left (dvd_mul_right 2 j) hcop
  have h22 : (2 : ℕ) ∣ Nat.gcd 2 q := Nat.dvd_gcd dvd_rfl h2
  rw [this] at h22
  omega

/-- The head, for even level `q = 2k`: `Σ_{n<q} ‖term n‖ ≤ Σ_{j<k} 1/(2j+1)`. -/
lemma sum_norm_term_le_odd {q : ℕ} [NeZero q] (k : ℕ) (hq : q = 2 * k) (χ : DirichletCharacter ℂ q) {s : ℝ}
    (hs : 1 ≤ s) :
    ∑ n ∈ range q, ‖LSeries.term (fun n => χ n) s n‖ ≤ ∑ j ∈ range k, ((2 * j + 1 : ℕ) : ℝ)⁻¹ := by
  rw [show range q = range (2 * k) by rw [hq], sum_range_two_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [term_two_mul_eq_zero ⟨k, hq⟩ χ s j, norm_zero, zero_add]
  have := norm_term_le_inv χ hs (2 * j + 1)
  rwa [ite_eq_right (by omega)] at this

/-- For real `s > 1`, `‖L(s, χ)‖ ≤ H + 1/2`, whenever `H` bounds the head `Σ_{n<q} ‖term n‖` for all `s ≥ 1`. -/
theorem norm_LFunction_le_of_one_lt_of_head {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (H : ℝ)
    (hH : ∀ s : ℝ, 1 ≤ s → ∑ n ∈ range q, ‖LSeries.term (fun n => χ n) s n‖ ≤ H) {s : ℝ} (hs : 1 < s) :
    ‖χ.LFunction s‖ ≤ H + 1 / 2 := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hsre : 1 < (s : ℂ).re := by simpa using hs
  rw [DirichletCharacter.LFunction_eq_LSeries χ hsre]
  have hsum := (DirichletCharacter.LSeriesSummable_of_one_lt_re χ hsre).LSeriesHasSum
  have ht : Tendsto (fun ℓ => ∑ n ∈ range (q + ℓ), LSeries.term (fun n => χ n) s n) atTop
      (𝓝 (LSeries (fun n => χ n) s)) :=
    (HasSum.tendsto_sum_nat hsum).comp (tendsto_atTop_atTop_of_monotone (f := fun ℓ : ℕ => q + ℓ)
      (fun _ _ h => Nat.add_le_add_left h q) (fun b => ⟨b, Nat.le_add_left b q⟩))
  refine le_of_tendsto' ht.norm fun ℓ => ?_
  rw [Finset.sum_range_add]
  refine (norm_add_le _ _).trans (add_le_add ((norm_sum_le _ _).trans (hH s hs.le)) ?_)
  refine (norm_sum_term_tail_le χ hχ (by linarith) ℓ).trans ?_
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hpow : (q : ℝ) ≤ (q : ℝ) ^ s := by simpa using Real.rpow_le_rpow_of_exponent_le hq1 hs.le
  have : ((q : ℝ) ^ s)⁻¹ ≤ (q : ℝ)⁻¹ := inv_anti₀ hq0 hpow
  calc (q : ℝ) / 2 * ((q : ℝ) ^ s)⁻¹ ≤ (q : ℝ) / 2 * (q : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = 1 / 2 := by have := hq0.ne'; field_simp

/-- **`‖L(1, χ)‖ ≤ (log q)/2 + 13/10`** for every non-trivial Dirichlet character of even level `q ≥ 12`. -/
theorem norm_LFunction_one_le_of_even {q : ℕ} [NeZero q] (hq : 12 ≤ q) (h2 : 2 ∣ q) (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) : ‖χ.LFunction 1‖ ≤ Real.log q / 2 + 13 / 10 := by
  obtain ⟨k, hk⟩ := h2
  have hk6 : 6 ≤ k := by omega
  have hH := fun s (hs : (1 : ℝ) ≤ s) => sum_norm_term_le_odd k hk χ hs
  have h1 : ‖χ.LFunction 1‖ ≤ ∑ j ∈ range k, ((2 * j + 1 : ℕ) : ℝ)⁻¹ + 1 / 2 :=
    le_of_tendsto (tendsto_LFunction_nhdsGT χ hχ).norm (eventually_nhdsWithin_of_forall fun s hs =>
      norm_LFunction_le_of_one_lt_of_head χ hχ _ hH (Set.mem_Ioi.mp hs))
  have h2 := sum_odd_inv_le hk6
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hlogq : Real.log q = Real.log 2 + Real.log k := by
    rw [hk]; push_cast; exact Real.log_mul (by norm_num) hk0.ne'
  have hl2 := Real.log_two_lt_d9
  linarith

end BoundariesOfClass.ClassNumberFormula
