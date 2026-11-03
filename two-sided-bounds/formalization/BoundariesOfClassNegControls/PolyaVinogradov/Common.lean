import BoundariesOfClass.Primitivity.Kronecker

/-!
# Negative controls for the Pólya–Vinogradov statements: shared facts

The characters `χ_{-7}` and `χ_{-11}` (CN-1's `kroneckerChar 7` and `kroneckerChar 11`, of levels `disc 7 = 7` and
`disc 11 = 11`): primitivity, the values used in the refutations, and the numeric brackets
`log 7 < 2`, `log 7 < 1.9545`, `log 11 < 8/3` and `√7 < 3`.
-/

set_option autoImplicit false

open CN1.Foundations

namespace BoundariesOfClassNegControls.PolyaVinogradov

lemma disc_seven : disc 7 = 7 := disc_of_three_mod_four (by norm_num)

lemma disc_eleven : disc 11 = 11 := disc_of_three_mod_four (by norm_num)

instance : NeZero (disc 7) := ⟨by rw [disc_seven]; norm_num⟩

instance : NeZero (disc 11) := ⟨by rw [disc_eleven]; norm_num⟩

lemma kronecker_seven_isPrimitive : (kroneckerChar 7).IsPrimitive :=
  BoundariesOfClass.Primitivity.kroneckerChar_isPrimitive (by norm_num : Nat.Prime 7).prime.squarefree

lemma kronecker_eleven_isPrimitive : (kroneckerChar 11).IsPrimitive :=
  BoundariesOfClass.Primitivity.kroneckerChar_isPrimitive (by norm_num : Nat.Prime 11).prime.squarefree

/-- `χ_{-7}(a) = J(a | 7)` for `a` coprime to `7`. -/
lemma kronecker_seven_apply (a : ℤ) (ha : Int.gcd a 7 = 1) :
    kroneckerChar 7 (a : ZMod (disc 7)) = (jacobiSym a 7 : ℂ) :=
  kroneckerChar_apply_of_three_mod_four (by norm_num)
    (by rw [disc_seven]; exact Int.isCoprime_iff_gcd_eq_one.mpr (by exact_mod_cast ha))

/-- `χ_{-11}(a) = J(a | 11)` for `a` coprime to `11`. -/
lemma kronecker_eleven_apply (a : ℤ) (ha : Int.gcd a 11 = 1) :
    kroneckerChar 11 (a : ZMod (disc 11)) = (jacobiSym a 11 : ℂ) :=
  kroneckerChar_apply_of_three_mod_four (by norm_num)
    (by rw [disc_eleven]; exact Int.isCoprime_iff_gcd_eq_one.mpr (by exact_mod_cast ha))

/-- `χ_{-7}(1) + χ_{-7}(2) = 2`. -/
lemma sum_kronecker_seven :
    ∑ n ∈ Finset.range 2, kroneckerChar 7 (((1 : ℤ) + n : ℤ) : ZMod (disc 7)) = 2 := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  have h1 := kronecker_seven_apply (1 + ((0 : ℕ) : ℤ)) (by norm_num)
  have h2 := kronecker_seven_apply (1 + ((1 : ℕ) : ℤ)) (by norm_num)
  rw [h1, h2]
  norm_num

/-- `χ_{-11}(1) + ⋯ + χ_{-11}(5) = 1 - 1 + 1 + 1 + 1 = 3`. -/
lemma sum_kronecker_eleven :
    ∑ n ∈ Finset.range 5, kroneckerChar 11 (((1 : ℤ) + n : ℤ) : ZMod (disc 11)) = 3 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [kronecker_eleven_apply _ (by norm_num), kronecker_eleven_apply _ (by norm_num),
    kronecker_eleven_apply _ (by norm_num), kronecker_eleven_apply _ (by norm_num),
    kronecker_eleven_apply _ (by norm_num)]
  norm_num

/-- `log 7 < 2`, since `7 < e²`. -/
lemma log_seven_lt_two : Real.log 7 < 2 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num), show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
  have := Real.exp_one_gt_d9
  nlinarith

/-- `log 7 < 1.9545`: `log 7 = 3 log 2 - log (8/7)`, with `log (8/7) ≥ 1 - 7/8`. -/
lemma log_seven_lt : Real.log 7 < 1.9545 := by
  have h2 := Real.log_two_lt_d9
  have h87 : 1 - (8 / 7 : ℝ)⁻¹ ≤ Real.log (8 / 7) := Real.one_sub_inv_le_log_of_pos (by norm_num)
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have hdiv : Real.log (8 / 7) = Real.log 8 - Real.log 7 := Real.log_div (by norm_num) (by norm_num)
  norm_num at h87
  linarith

/-- `log 7 > 1`, since `7 > e`. -/
lemma one_lt_log_seven : 1 < Real.log 7 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

/-- `log 11 < 8/3`, since `11³ = 1331 < e⁸`. -/
lemma log_eleven_lt : Real.log 11 < 8 / 3 := by
  have h : Real.log ((11 : ℝ) ^ 3) < 8 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num), show (8 : ℝ) = ((8 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
    have he := Real.exp_one_gt_d9
    have hp : (2.7182818283 : ℝ) ^ 8 ≤ Real.exp 1 ^ 8 := pow_le_pow_left₀ (by norm_num) he.le 8
    norm_num at hp ⊢
    linarith
  rw [Real.log_pow] at h
  push_cast at h
  linarith

/-- `√7 < 3`. -/
lemma sqrt_seven_lt_three : Real.sqrt 7 < 3 := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num

end BoundariesOfClassNegControls.PolyaVinogradov
