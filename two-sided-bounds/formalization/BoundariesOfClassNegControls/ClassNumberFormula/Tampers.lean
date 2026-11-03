import BoundariesOfClassNegControls.Fields
import BoundariesOfClass.ClassNumberFormula.Main

/-!
# BoundariesOfClassNegControls.ClassNumberFormula.Tampers: TU1, TL1, TC1 and the non-vacuity witness at `K_7`

Pinned environment: Lean v4.34.1, Mathlib d13f23b. Never imported by the solution. Each tampered statement is a
statement of the class number formula challenge with one constant changed, stated as a `def` (over fields in `Type`,
which the challenge's `Type*` form implies), and refuted at the real field `K_7 = ℚ(√-7)` of the shared Fields module
(`d = 7`, `h ≥ 1`):

* `TU1` ((U′) with `7/6 → -1`): the tampered bound `√7 (log 7 - 1)/π` is below `1 ≤ h`, from `log 7 < 2`
  (`7 < e²`), `√7 < 3` and `π > 3`.
* `TL1` ((L1) with `7/6 → -1`), **via the class number formula**: `L(1, χ_{-7}) = π h/√7 ≥ π/√7 > 1 > log 7 - 1`.
* `TC1` ((CNF) with `π → 2π`): with the true formula it would give `πh/√7 = 2πh/√7`, so `h = 0`.
* `nonvacuity_K7`: `K_7` satisfies the hypotheses of all five challenge statements, with the factorising character.

Expected (pre-registered): the module builds; every theorem here is a theorem (control C-CNF4).
-/

set_option autoImplicit false

open NumberField CN1.Foundations

namespace BoundariesOfClassNegControls.ClassNumberFormula

lemma disc_7 : disc 7 = 7 := by decide

instance : NeZero (disc 7) := ⟨by decide⟩

lemma abs_discr_7 : |(discr (KField 7) : ℝ)| = 7 := by
  rw [abs_discr_KField 7 squarefree_7]; norm_num [CN1.Finite.dOf]

instance : NeZero (discr (KField 7)).natAbs := ⟨Int.natAbs_ne_zero.mpr (discr_ne_zero _)⟩

lemma one_le_classNumber_7 : (1 : ℝ) ≤ classNumber (KField 7) := by
  exact_mod_cast classNumber_pos (KField 7)

lemma log_seven_lt_two : Real.log 7 < 2 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num), show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
  have := Real.exp_one_gt_d9
  nlinarith

lemma one_lt_log_seven : 1 < Real.log 7 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

lemma sqrt_seven_lt_three : Real.sqrt 7 < 3 := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- The tampered (U′): `7/6 → -1`. -/
def TU1 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (m : ℕ), Squarefree m →
    (∃ α : K, α ^ 2 = -(m : K)) → (5 : ℝ) ≤ |(discr K : ℝ)| →
    (classNumber K : ℝ) ≤ Real.sqrt |(discr K : ℝ)| * (Real.log |(discr K : ℝ)| - 1) / Real.pi

/-- **TU1 is false**, at `K_7`. -/
theorem not_TU1 : ¬ TU1 := by
  intro h
  have h1 := h (KField 7) (finrank_KField 7) 7 squarefree_7 (exists_sq_eq_neg 7) (by rw [abs_discr_7]; norm_num)
  rw [abs_discr_7] at h1
  have hh := one_le_classNumber_7
  have hl := log_seven_lt_two
  have hl1 := one_lt_log_seven
  have hs := sqrt_seven_lt_three
  have hs0 := Real.sqrt_nonneg 7
  have hpi := Real.pi_gt_three
  have hprod : Real.sqrt 7 * (Real.log 7 - 1) < 3 := by nlinarith
  rw [le_div_iff₀ Real.pi_pos] at h1
  nlinarith

/-- The tampered (L1): `7/6 → -1`. -/
def TL1 : Prop :=
  ∀ (q : ℕ) [NeZero q], 7 ≤ q → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ‖χ.LFunction 1‖ ≤ Real.log q - 1

/-- **TL1 is false**, at `χ_{-7}`, through the class number formula at `K_7`. -/
theorem not_TL1 : ¬ TL1 := by
  intro h
  have h1 := h (disc 7) (by rw [disc_7]) (kroneckerChar 7) (kroneckerChar_ne_one squarefree_7)
  rw [BoundariesOfClass.ClassNumberFormula.LFunction_kroneckerChar_one_eq (rootK_sq 7) (finrank_KField 7)
    squarefree_7 (by decide) (by decide), Complex.norm_real, disc_7] at h1
  have hh := one_le_classNumber_7
  have hs := sqrt_seven_lt_three
  have hs0 : 0 < Real.sqrt 7 := Real.sqrt_pos.mpr (by norm_num)
  have hpi := Real.pi_gt_three
  have hl := log_seven_lt_two
  have hval : 1 < Real.pi * classNumber (KField 7) / Real.sqrt 7 := by
    rw [lt_div_iff₀ hs0]; nlinarith
  rw [Real.norm_of_nonneg (by positivity)] at h1
  push_cast at h1
  linarith

/-- The tampered (CNF): `π → 2π`. -/
def TC1 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (m : ℕ), Squarefree m →
    (∃ α : K, α ^ 2 = -(m : K)) → (5 : ℝ) ≤ |(discr K : ℝ)| →
    ∀ [NeZero (discr K).natAbs] (χ : DirichletCharacter ℂ (discr K).natAbs),
      (∀ s : ℂ, 1 < s.re → dedekindZeta K s = riemannZeta s * χ.LFunction s) →
      χ.LFunction 1 = 2 * Real.pi * classNumber K / Real.sqrt |(discr K : ℝ)|

/-- **TC1 is false**, at `K_7`: together with the true formula it forces `h = 0`. -/
theorem not_TC1 : ¬ TC1 := by
  intro h
  obtain ⟨χ, hχ⟩ := BoundariesOfClass.exists_LFunction_factorisation (KField 7) (finrank_KField 7) 7 squarefree_7
    (exists_sq_eq_neg 7)
  have hd : (5 : ℝ) ≤ |(discr (KField 7) : ℝ)| := by rw [abs_discr_7]; norm_num
  have h1 := h (KField 7) (finrank_KField 7) 7 squarefree_7 (exists_sq_eq_neg 7) hd χ hχ
  have h2 := BoundariesOfClass.LFunction_one_eq (KField 7) (finrank_KField 7) 7 squarefree_7 (exists_sq_eq_neg 7)
    hd χ hχ
  rw [h2, abs_discr_7] at h1
  have hreal : Real.pi * classNumber (KField 7) / Real.sqrt 7 =
      2 * Real.pi * classNumber (KField 7) / Real.sqrt 7 := by exact_mod_cast h1
  have hs0 : 0 < Real.sqrt 7 := Real.sqrt_pos.mpr (by norm_num)
  have hpos : 0 < Real.pi * classNumber (KField 7) / Real.sqrt 7 := by
    have := one_le_classNumber_7
    positivity
  have : 2 * Real.pi * classNumber (KField 7) / Real.sqrt 7 = 2 * (Real.pi * classNumber (KField 7) / Real.sqrt 7) :=
    by ring
  linarith

/-- **Non-vacuity at `K_7`.** `K_7` satisfies the hypotheses of the five challenge statements: degree two, the root,
`7` squarefree, `|disc K_7| = 7 ≥ 5`, a character factorising `ζ_{K_7}`, and, for (L1), the non-trivial character
`χ_{-7}` of level `7 ≥ 7`. The conclusions then hold at `K_7` (here: (U′)). -/
theorem nonvacuity_K7 :
    Module.finrank ℚ (KField 7) = 2 ∧ Squarefree 7 ∧ (∃ α : KField 7, α ^ 2 = -((7 : ℕ) : KField 7)) ∧
      (5 : ℝ) ≤ |(discr (KField 7) : ℝ)| ∧
      (∃ χ : DirichletCharacter ℂ (discr (KField 7)).natAbs,
        ∀ s : ℂ, 1 < s.re → dedekindZeta (KField 7) s = riemannZeta s * χ.LFunction s) ∧
      7 ≤ disc 7 ∧ kroneckerChar 7 ≠ 1 ∧
      (classNumber (KField 7) : ℝ) ≤ Real.sqrt 7 * (Real.log 7 + 7 / 6) / Real.pi := by
  have hd : (5 : ℝ) ≤ |(discr (KField 7) : ℝ)| := by rw [abs_discr_7]; norm_num
  refine ⟨finrank_KField 7, squarefree_7, exists_sq_eq_neg 7, hd,
    BoundariesOfClass.exists_LFunction_factorisation (KField 7) (finrank_KField 7) 7 squarefree_7
      (exists_sq_eq_neg 7), by rw [disc_7], kroneckerChar_ne_one squarefree_7, ?_⟩
  have := BoundariesOfClass.classNumber_le_sharp (KField 7) (finrank_KField 7) 7 squarefree_7 (exists_sq_eq_neg 7) hd
  rwa [abs_discr_7] at this

end BoundariesOfClassNegControls.ClassNumberFormula
