import BoundariesOfClass.ClassNumberFormula.Invariants
import BoundariesOfClass.ClassNumberFormula.Residue
import CN1.Epstein.Factorization

/-!
# BoundariesOfClass.ClassNumberFormula.Main: Dirichlet's class number formula for `ℚ(√-m)`, and `h ≤ (1/π) √d (log d + 7/6)`

Pinned environment: Lean v4.34.1, Mathlib d13f23b. Imports Mathlib and the Mathlib-only foundations and factorisation
of the CN-1 formalization (tenth-discriminant). No zero-free region, no continuation beyond Mathlib's `LFunction`, and
no class sums are used.

**Dirichlet's class number formula** (Dirichlet, 1839) for `K = ℚ(√-m)`, `d = |disc K|`, `w = #μ(K)`:
`L(1, χ_{-d}) = 2π h(K) / (w √d)`, so `L(1, χ_{-d}) = π h(K) / √d` for `m ∉ {1, 3}`. The proof combines Mathlib's
residue formula for the Dedekind zeta function (`NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`) with CN-1's
factorisation `ζ_K = ζ · L(·, χ_{-d})` (`CN1.Epstein.dedekindZeta_eq_riemannZeta_mul_LFunction`), and computes
`r₁ = 0`, `r₂ = 1`, `R = 1`, `w = 2` (`Invariants.lean`).

In CN-1's vocabulary (`d = disc m`, `χ_{-d} = kroneckerChar m`):

* `LFunction_kroneckerChar_one_eq`: `L(1, χ_{-d}) = π h / √d` for `m ∉ {1, 3}`.
* `classNumber_le_sharp_disc`: `h ≤ (1/π) √d (log d + 7/6)` for `d ≥ 5`, from the formula and
  `‖L(1, χ)‖ ≤ log d + 7/6` (`LOne.lean`).

In the vocabulary of Mathlib alone (`d = |NumberField.discr K|`; the character is pinned down by the factorisation, since
the Kronecker character is not a Mathlib definition):

* `BoundariesOfClass.LFunction_one_eq_general`: `L(1, χ) = 2π h / (w √d)`.
* `BoundariesOfClass.LFunction_one_eq`: `L(1, χ) = π h / √d` for `d ≥ 5`.
* `BoundariesOfClass.exists_LFunction_factorisation`: such a `χ` exists (it is `χ_{-d}`).
* `BoundariesOfClass.classNumber_le_sharp`: **`h ≤ (1/π) √d (log d + 7/6)`** for `d ≥ 5`.
* `BoundariesOfClass.norm_LFunction_one_le`: `‖L(1, χ)‖ ≤ log q + 7/6` for every non-trivial `χ` of level `q ≥ 7`.
* `BoundariesOfClass.ClassNumberFormula.classNumber_le_six_fifths`: the weaker `h ≤ (6/5) √d log d`, for `d ≥ 5`.
-/

set_option autoImplicit false

open NumberField CN1.Foundations

namespace BoundariesOfClass.ClassNumberFormula

variable {K : Type*} [Field K] [NumberField K]

/-- **Dirichlet's class number formula, CN-1 form:** `L(1, χ_{-d}) = π h / √d` for `m ∉ {1, 3}`. -/
theorem LFunction_kroneckerChar_one_eq {m : ℕ} {α : K} (hα : α ^ 2 = -(m : K)) (hK : Module.finrank ℚ K = 2)
    (hm : Squarefree m) (hm1 : m ≠ 1) (hm3 : m ≠ 3) [NeZero (disc m)] :
    (kroneckerChar m).LFunction 1 = ((Real.pi * classNumber K / Real.sqrt (disc m) : ℝ) : ℂ) := by
  rw [LFunction_one_eq_residue K _ (kroneckerChar_ne_one hm)
      (fun s hs => CN1.Epstein.dedekindZeta_eq_riemannZeta_mul_LFunction hα hK hm hs),
    dedekindZeta_residue_eq hα hK hm.ne_zero, torsionOrder_eq_two hα hK hm hm1 hm3, abs_discr_eq hα hK hm]
  push_cast
  ring

/-- **(U′), CN-1 form:** `h ≤ (1/π) √d (log d + 7/6)` for `d ≥ 5`. -/
theorem classNumber_le_sharp_disc {m : ℕ} {α : K} (hα : α ^ 2 = -(m : K)) (hK : Module.finrank ℚ K = 2)
    (hm : Squarefree m) (hd : 5 ≤ disc m) :
    (classNumber K : ℝ) ≤ Real.sqrt (disc m) * (Real.log (disc m) + 7 / 6) / Real.pi := by
  have : NeZero (disc m) := ⟨by omega⟩
  obtain ⟨hm1, hm3⟩ := ne_one_and_ne_three_of_five_le hd
  have hB := norm_LFunction_one_le (seven_le_disc hd) (kroneckerChar m) (kroneckerChar_ne_one hm)
  rw [LFunction_kroneckerChar_one_eq hα hK hm hm1 hm3, Complex.norm_real] at hB
  have hd0 : (0 : ℝ) < disc m := by exact_mod_cast (by omega : 0 < disc m)
  have hsd : 0 < Real.sqrt (disc m) := Real.sqrt_pos.mpr hd0
  rw [Real.norm_of_nonneg (by positivity), div_le_iff₀ hsd] at hB
  rw [le_div_iff₀ Real.pi_pos]
  linarith

/-- The weaker `h ≤ (6/5) √d log d` follows for `d ≥ 5`, since `(log d + 7/6)/π ≤ (6/5) log d` once `log d ≥ 1/2`. -/
theorem classNumber_le_six_fifths {m : ℕ} {α : K} (hα : α ^ 2 = -(m : K)) (hK : Module.finrank ℚ K = 2)
    (hm : Squarefree m) (hd : 5 ≤ disc m) :
    (classNumber K : ℝ) ≤ 6 / 5 * Real.sqrt (disc m) * Real.log (disc m) := by
  have h := classNumber_le_sharp_disc hα hK hm hd
  have hd5 : (5 : ℝ) ≤ disc m := by exact_mod_cast hd
  have hL : (1 / 2 : ℝ) ≤ Real.log (disc m) := by
    have h2 := Real.log_two_gt_d9
    have : Real.log 2 ≤ Real.log (disc m) := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hsd : 0 ≤ Real.sqrt (disc m) := Real.sqrt_nonneg _
  have hpi := Real.pi_gt_three
  have hk : Real.sqrt (disc m) * (Real.log (disc m) + 7 / 6) / Real.pi ≤
      6 / 5 * Real.sqrt (disc m) * Real.log (disc m) := by
    rw [div_le_iff₀ Real.pi_pos]
    have : Real.log (disc m) + 7 / 6 ≤ 6 / 5 * Real.log (disc m) * Real.pi := by nlinarith
    nlinarith
  linarith

end BoundariesOfClass.ClassNumberFormula

namespace BoundariesOfClass

open BoundariesOfClass.ClassNumberFormula

/-- **An explicit bound for `L(1, χ)`.** For every non-trivial Dirichlet character `χ` of level `q ≥ 7`:
`‖L(1, χ)‖ ≤ log q + 7/6`. -/
theorem norm_LFunction_one_le {q : ℕ} [NeZero q] (hq : 7 ≤ q) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ‖χ.LFunction 1‖ ≤ Real.log q + 7 / 6 :=
  ClassNumberFormula.norm_LFunction_one_le hq χ hχ

/-- **Dirichlet's class number formula, general `w`.** For `K = ℚ(√-m)` and every Dirichlet character `χ` of level
`|disc K|` with `ζ_K(s) = ζ(s) L(s, χ)` on `Re s > 1`: `L(1, χ) = 2π h(K) / (w(K) √|disc K|)`. -/
theorem LFunction_one_eq_general (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    [NeZero (discr K).natAbs] (χ : DirichletCharacter ℂ (discr K).natAbs)
    (hχ : ∀ s : ℂ, 1 < s.re → dedekindZeta K s = riemannZeta s * χ.LFunction s) :
    χ.LFunction 1 =
      2 * Real.pi * classNumber K / (Units.torsionOrder K * Real.sqrt |(discr K : ℝ)|) := by
  obtain ⟨α, hα⟩ := hsq
  rw [LFunction_one_eq_residue K χ (ne_one_of_factorisation K χ hχ) hχ, dedekindZeta_residue_eq hα hK hm.ne_zero]
  push_cast
  ring

/-- **Dirichlet's class number formula.** For `K = ℚ(√-m)` with `|disc K| ≥ 5` (that is, `m ∉ {1, 3}`) and every
Dirichlet character `χ` of level `|disc K|` with `ζ_K(s) = ζ(s) L(s, χ)` on `Re s > 1`:
`L(1, χ) = π h(K) / √|disc K|`. -/
theorem LFunction_one_eq (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hd : (5 : ℝ) ≤ |(discr K : ℝ)|)
    [NeZero (discr K).natAbs] (χ : DirichletCharacter ℂ (discr K).natAbs)
    (hχ : ∀ s : ℂ, 1 < s.re → dedekindZeta K s = riemannZeta s * χ.LFunction s) :
    χ.LFunction 1 = Real.pi * classNumber K / Real.sqrt |(discr K : ℝ)| := by
  rw [LFunction_one_eq_general K hK m hm hsq χ hχ]
  obtain ⟨α, hα⟩ := hsq
  have hd' : 5 ≤ disc m := by rw [abs_discr_eq hα hK hm] at hd; exact_mod_cast hd
  obtain ⟨hm1, hm3⟩ := ne_one_and_ne_three_of_five_le hd'
  rw [torsionOrder_eq_two hα hK hm hm1 hm3]
  push_cast
  ring

/-- **Such a character exists** (so the two statements above are not vacuous): the Kronecker character `χ_{-d}`. -/
theorem exists_LFunction_factorisation (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    [NeZero (discr K).natAbs] :
    ∃ χ : DirichletCharacter ℂ (discr K).natAbs,
      ∀ s : ℂ, 1 < s.re → dedekindZeta K s = riemannZeta s * χ.LFunction s := by
  rename_i hN
  obtain ⟨α, hα⟩ := hsq
  have he : (discr K).natAbs = disc m := natAbs_discr_eq hα hK hm
  revert hN
  rw [he]
  intro hN
  exact ⟨kroneckerChar m, fun s hs => CN1.Epstein.dedekindZeta_eq_riemannZeta_mul_LFunction hα hK hm hs⟩

/-- **(U′) The sharper upper bound.** For `K = ℚ(√-m)` with `d = |disc K| ≥ 5`:
`h(K) ≤ (1/π) √d (log d + 7/6)`. -/
theorem classNumber_le_sharp (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hd : (5 : ℝ) ≤ |(discr K : ℝ)|) :
    (classNumber K : ℝ) ≤
      Real.sqrt |(discr K : ℝ)| * (Real.log |(discr K : ℝ)| + 7 / 6) / Real.pi := by
  obtain ⟨α, hα⟩ := hsq
  rw [abs_discr_eq hα hK hm] at hd ⊢
  exact classNumber_le_sharp_disc hα hK hm (by exact_mod_cast hd)

end BoundariesOfClass
