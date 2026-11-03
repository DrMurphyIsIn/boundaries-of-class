import BoundariesOfClass.ClassNumberFormula.LOne
import BoundariesOfClass.PolyaVinogradov.Main

/-!
# BoundariesOfClass.PolyaVinogradov.HalfLog: `‖L(1, χ)‖ ≤ ½ log q + log log q + O(1)` for primitive `χ`

Pinned environment: Lean v4.34.1, Mathlib d13f23b. Mathlib only.

The classical consequence of the Pólya–Vinogradov inequality. Split the series for `L(s, χ)` at `N`:

* `norm_LFunction_le_split_of_one_lt`: if every sum of `χ` over consecutive integers starting at `N` has norm at most
  `B`, then `‖L(s, χ)‖ ≤ H_{N-1} + B/N` for real `s > 1`. The head is bounded termwise, and the tail by Abel's
  inequality against the partial sums (`norm_sum_mul_le_of_antitone`).
* `norm_LFunction_one_le_split`: the same at `s = 1`, by continuity.
* `norm_LFunction_one_le_log_B`: for primitive `χ` of level `q ≥ 7`, Pólya–Vinogradov gives `B = √q (log q + 1/3)`.
  Take `N = ⌈B⌉ ≥ 7`. Then `H_{N-1} ≤ log(N - 1) + 2/3 ≤ log B + 2/3` (Mathlib's `eulerMascheroniSeq'` is decreasing
  and below `2/3` at `6`), and `B/N ≤ 1`.
* `BoundariesOfClass.norm_LFunction_one_le_of_isPrimitive`: `‖L(1, χ)‖ ≤ ½ log q + log(log q + 1/3) + 5/3`.
* `BoundariesOfClass.norm_LFunction_one_le_loglog`: `‖L(1, χ)‖ ≤ ½ log q + log log q + 2`.
-/

set_option autoImplicit false

namespace BoundariesOfClass.PolyaVinogradov

open Finset Filter Topology BoundariesOfClass.ClassNumberFormula

variable {q : ℕ} [NeZero q]

omit [NeZero q] in
/-- The head of the series: `Σ_{n<N} ‖term n‖ ≤ H_{N-1}`. -/
lemma sum_norm_term_le_harmonic_pred (χ : DirichletCharacter ℂ q) {s : ℝ} (hs : 1 ≤ s) (N : ℕ) :
    ∑ n ∈ range N, ‖LSeries.term (fun n => χ n) s n‖ ≤ (harmonic (N - 1) : ℝ) := by
  rcases N with _ | p
  · simp
  rw [Finset.sum_range_succ', show p + 1 - 1 = p by omega]
  have h0 : ‖LSeries.term (fun n => χ n) s 0‖ = 0 := by simp
  rw [h0, add_zero, harmonic]
  push_cast
  refine Finset.sum_le_sum fun i _ => ?_
  have := norm_term_le_inv χ hs (i + 1)
  rw [ite_eq_right (Nat.succ_ne_zero i)] at this
  simpa using this

omit [NeZero q] in
/-- The tail of the series, by Abel's inequality: `‖Σ_{i<ℓ} term (N + i)‖ ≤ B N^{-s}`. -/
lemma norm_sum_term_tail_le_of_bound (χ : DirichletCharacter ℂ q) {s : ℝ} (hs : 0 ≤ s) {N : ℕ} (hN : 0 < N)
    {B : ℝ} (hB : ∀ ℓ, ‖∑ i ∈ range ℓ, χ ((N + i : ℕ) : ZMod q)‖ ≤ B) (ℓ : ℕ) :
    ‖∑ i ∈ range ℓ, LSeries.term (fun n => χ n) s (N + i)‖ ≤ B * ((N : ℝ) ^ s)⁻¹ := by
  set b : ℕ → ℝ := fun i => (((N + i : ℕ) : ℝ) ^ s)⁻¹ with hb
  have hterm : ∀ i, LSeries.term (fun n => χ n) s (N + i) = (b i : ℂ) * χ ((N + i : ℕ) : ZMod q) := by
    intro i
    rw [LSeries.term_of_ne_zero (by omega)]
    simp only [hb]
    rw [Complex.ofReal_inv, Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_natCast, div_eq_mul_inv,
      mul_comm]
  simp_rw [hterm]
  have hanti : Antitone b := by
    intro i j hij
    simp only [hb]
    have hpos : (0 : ℝ) < ((N + i : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < N + i)
    refine inv_anti₀ (Real.rpow_pos_of_pos hpos s) (Real.rpow_le_rpow (Nat.cast_nonneg _) ?_ hs)
    exact_mod_cast Nat.add_le_add_left hij N
  have hb0 : ∀ n, 0 ≤ b n := fun n => by simp only [hb]; positivity
  have h := norm_sum_mul_le_of_antitone hanti hb0 hB ℓ
  have hb00 : b 0 = ((N : ℝ) ^ s)⁻¹ := by simp [hb]
  rwa [hb00] at h

/-- **The split bound at real `s > 1`:** `‖L(s, χ)‖ ≤ H_{N-1} + B/N`. -/
theorem norm_LFunction_le_split_of_one_lt (χ : DirichletCharacter ℂ q) {N : ℕ} (hN : 0 < N) {B : ℝ}
    (hB : ∀ ℓ, ‖∑ i ∈ range ℓ, χ ((N + i : ℕ) : ZMod q)‖ ≤ B) {s : ℝ} (hs : 1 < s) :
    ‖χ.LFunction s‖ ≤ (harmonic (N - 1) : ℝ) + B / N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hsre : 1 < (s : ℂ).re := by simpa using hs
  rw [DirichletCharacter.LFunction_eq_LSeries χ hsre]
  have hsum := (DirichletCharacter.LSeriesSummable_of_one_lt_re χ hsre).LSeriesHasSum
  have ht : Tendsto (fun ℓ => ∑ n ∈ range (N + ℓ), LSeries.term (fun n => χ n) s n) atTop
      (𝓝 (LSeries (fun n => χ n) s)) :=
    (HasSum.tendsto_sum_nat hsum).comp (tendsto_atTop_atTop_of_monotone (f := fun ℓ : ℕ => N + ℓ)
      (fun _ _ h => Nat.add_le_add_left h N) (fun b => ⟨b, Nat.le_add_left b N⟩))
  refine le_of_tendsto' ht.norm fun ℓ => ?_
  rw [Finset.sum_range_add]
  refine (norm_add_le _ _).trans (add_le_add ((norm_sum_le _ _).trans
    (sum_norm_term_le_harmonic_pred χ hs.le N)) ?_)
  refine (norm_sum_term_tail_le_of_bound χ (by linarith) hN hB ℓ).trans ?_
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpow : (N : ℝ) ≤ (N : ℝ) ^ s := by simpa using Real.rpow_le_rpow_of_exponent_le hN1 hs.le
  have : ((N : ℝ) ^ s)⁻¹ ≤ (N : ℝ)⁻¹ := inv_anti₀ hN0 hpow
  calc B * ((N : ℝ) ^ s)⁻¹ ≤ B * (N : ℝ)⁻¹ := mul_le_mul_of_nonneg_left this hB0
    _ = B / N := by rw [div_eq_mul_inv]

/-- **The split bound at `s = 1`**, by continuity. -/
theorem norm_LFunction_one_le_split (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {N : ℕ} (hN : 0 < N) {B : ℝ}
    (hB : ∀ ℓ, ‖∑ i ∈ range ℓ, χ ((N + i : ℕ) : ZMod q)‖ ≤ B) :
    ‖χ.LFunction 1‖ ≤ (harmonic (N - 1) : ℝ) + B / N :=
  le_of_tendsto (tendsto_LFunction_nhdsGT χ hχ).norm (eventually_nhdsWithin_of_forall fun _s hs =>
    norm_LFunction_le_split_of_one_lt χ hN hB (Set.mem_Ioi.mp hs))

/-- `H_n ≤ log n + 2/3` for `n ≥ 6`. -/
lemma harmonic_le_log_add_two_thirds {n : ℕ} (hn : 6 ≤ n) : (harmonic n : ℝ) ≤ Real.log n + 2 / 3 := by
  have hanti := Real.strictAnti_eulerMascheroniSeq'.antitone hn
  have hlt := Real.eulerMascheroniSeq'_six_lt_two_thirds
  have hdef : Real.eulerMascheroniSeq' n = (harmonic n : ℝ) - Real.log n := by
    rw [Real.eulerMascheroniSeq', ite_eq_right (by omega)]
  linarith

/-- `log 7 > 1.9365`: `log 7 = 3 log 2 - log (8/7)`, with `log (8/7) ≤ 1/7`. -/
lemma log_seven_gt : (1.9365 : ℝ) < Real.log 7 := by
  have h2 := Real.log_two_gt_d9
  have h87 : Real.log (8 / 7) ≤ 8 / 7 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have hdiv : Real.log (8 / 7) = Real.log 8 - Real.log 7 := Real.log_div (by norm_num) (by norm_num)
  linarith

/-- The Pólya–Vinogradov constant `B = √q (log q + 1/3)` exceeds `6` for `q ≥ 7`. -/
lemma six_lt_pvBound {q : ℕ} (hq : 7 ≤ q) : 6 < Real.sqrt q * (Real.log q + 1 / 3) := by
  have hq7 : (7 : ℝ) ≤ q := by exact_mod_cast hq
  have hs7 : (2.6457 : ℝ) < Real.sqrt 7 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hsq : Real.sqrt 7 ≤ Real.sqrt q := Real.sqrt_le_sqrt hq7
  have hl7 : Real.log 7 ≤ Real.log q := Real.log_le_log (by norm_num) hq7
  have hl := log_seven_gt
  have h1 : (2.6457 : ℝ) < Real.sqrt q := by linarith
  have h2 : (2.2698 : ℝ) < Real.log q + 1 / 3 := by linarith
  nlinarith

/-- **`‖L(1, χ)‖ ≤ log B + 5/3`**, `B = √q (log q + 1/3)`, for a primitive `χ` of level `q ≥ 7`. -/
theorem norm_LFunction_one_le_log_B (hq : 7 ≤ q) {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    ‖χ.LFunction 1‖ ≤ Real.log (Real.sqrt q * (Real.log q + 1 / 3)) + 5 / 3 := by
  set B := Real.sqrt q * (Real.log q + 1 / 3) with hBdef
  have hB6 : 6 < B := six_lt_pvBound hq
  have hχ1 : χ ≠ 1 := by
    intro h
    have hc := (DirichletCharacter.eq_one_iff_conductor_eq_one (χ := χ)).mp h
    rw [(DirichletCharacter.isPrimitive_def χ).mp hχ] at hc
    omega
  -- `N = ⌈B⌉`: `6 < B ≤ N < B + 1`
  set N := ⌈B⌉₊ with hNdef
  have hBN : B ≤ N := Nat.le_ceil B
  have hNB : (N : ℝ) < B + 1 := Nat.ceil_lt_add_one (by linarith)
  have hN7 : 7 ≤ N := by
    have : (6 : ℝ) < N := by linarith
    exact_mod_cast (show (6 : ℝ) < N from this)
  have hN0 : (0 : ℝ) < N := by linarith
  -- Pólya–Vinogradov from the start `N`
  have hPV : ∀ ℓ, ‖∑ i ∈ range ℓ, χ ((N + i : ℕ) : ZMod q)‖ ≤ B := by
    intro ℓ
    have h := norm_sum_le_sqrt_mul_harmonic (by omega) hχ (N : ZMod q) ℓ
    simp_rw [Nat.cast_add]
    exact h.trans (mul_le_mul_of_nonneg_left (harmonic_half_le (by omega)) (Real.sqrt_nonneg _))
  have hsplit := norm_LFunction_one_le_split χ hχ1 (by omega) hPV
  -- the head: `H_{N-1} ≤ log (N - 1) + 2/3 ≤ log B + 2/3`
  have hH := harmonic_le_log_add_two_thirds (n := N - 1) (by omega)
  have hN1 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hlog : Real.log (N - 1 : ℕ) ≤ Real.log B := by
    rw [hN1]
    exact Real.log_le_log (by linarith) (by linarith)
  -- the tail: `B/N ≤ 1`
  have htail : B / N ≤ 1 := (div_le_one hN0).mpr hBN
  linarith

end BoundariesOfClass.PolyaVinogradov

namespace BoundariesOfClass

open BoundariesOfClass.PolyaVinogradov

/-- **The half-log bound for `L(1, χ)`.** For a primitive Dirichlet character `χ` of level `q ≥ 7`:
`‖L(1, χ)‖ ≤ ½ log q + log(log q + 1/3) + 5/3`. -/
theorem norm_LFunction_one_le_of_isPrimitive {q : ℕ} [NeZero q] (hq : 7 ≤ q) (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) :
    ‖χ.LFunction 1‖ ≤ Real.log q / 2 + Real.log (Real.log q + 1 / 3) + 5 / 3 := by
  have h := norm_LFunction_one_le_log_B hq hχ
  have hq7 : (7 : ℝ) ≤ q := by exact_mod_cast hq
  have hl : 0 < Real.log q + 1 / 3 := by
    have := Real.log_le_log (by norm_num) hq7
    have := log_seven_gt
    linarith
  rw [Real.log_mul (Real.sqrt_pos.mpr (by linarith)).ne' hl.ne', Real.log_sqrt (by linarith)] at h
  exact h

/-- **The half-log bound for `L(1, χ)`, `log log` form.** For a primitive Dirichlet character `χ` of level `q ≥ 7`:
`‖L(1, χ)‖ ≤ ½ log q + log log q + 2`. -/
theorem norm_LFunction_one_le_loglog {q : ℕ} [NeZero q] (hq : 7 ≤ q) (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) :
    ‖χ.LFunction 1‖ ≤ Real.log q / 2 + Real.log (Real.log q) + 2 := by
  have h := norm_LFunction_one_le_of_isPrimitive hq χ hχ
  have hq7 : (7 : ℝ) ≤ q := by exact_mod_cast hq
  -- `log (x + 1/3) ≤ log x + 1/(3x) ≤ log x + 1/3` for `x = log q ≥ 1`
  have hx : 1 ≤ Real.log q := by
    have := Real.log_le_log (by norm_num) hq7
    have := log_seven_gt
    linarith
  have hx0 : 0 < Real.log q := by linarith
  have hratio : Real.log ((Real.log q + 1 / 3) / Real.log q) ≤ (Real.log q + 1 / 3) / Real.log q - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div (by linarith) hx0.ne'] at hratio
  have hfrac : (Real.log q + 1 / 3) / Real.log q - 1 ≤ 1 / 3 := by
    rw [div_sub_one hx0.ne', div_le_iff₀ hx0]
    linarith
  linarith

end BoundariesOfClass
