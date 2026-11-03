import Mathlib

/-!
# Comparator challenge, version 1 (ARCHIVED): explicit two-sided growth of the class number, and the class number boundary

Archived: superseded by version 2, `BoundariesOfClassChallenges/BoundaryV2.lean`. This file lies outside every Lean
library and is in its own namespace `BoundariesOfClassV1`, so its names, which version 2 reuses with different types,
can never share an environment with version 2's. Apart from this paragraph, the title and the namespace, the text is
version 1's.

Statements only (`sorry`); the proofs are the solution side. The import closure is Mathlib alone (Lean v4.34.1, Mathlib
d13f23b, the openai/math 7/8 environment). Trust base: these statements; the Mathlib definitions they use
(`NumberField`, `NumberField.classNumber`, `NumberField.discr`, `Module.finrank`, `Squarefree`, `Real.sqrt`, `Real.log`,
`abs`, `max`, real division, and the casts `ℤ → ℝ` and `ℕ → ℝ`); the Lean kernel and nanoda; and the axioms `propext`,
`Classical.choice`, `Quot.sound`.

Vocabulary as in `CN1.classNumber_eq_one_iff` and `HCN.classNumber_le_two_iff` (tenth-discriminant): `K` is an abstract
number field of degree two over `ℚ` containing a square root of `-m`, `m` a squarefree natural number (so `m ≥ 1`, `α`
is irrational and `K ≅ ℚ(√-m)`). The discriminant is Mathlib's `NumberField.discr K`; for these fields `|discr K| = m` if
`m ≡ 3 (mod 4)` and `4m` otherwise, and `d := |discr K|` below. The hypothesis `2981 ≤ d` excludes `m = 1` (`d = 4`)
and `m = 3` (`d = 3`), so no separate `m ∉ {1, 3}` hypothesis is needed. `2981` is the least integer above
`e⁸ = 2980.958`, where `σ = 1 - 1/log d` passes `7/8`. `Real.log` is applied only to quantities `≥ 2981`, `≥ 100/9` and
`≥ 2 log(100/9) = 4.816`, so no junk value is reached.

Constants (computed with mpmath and exact rationals; not themselves Lean facts): with `L = log d` and
`κ = e^{-3π/4}/(1 - e^{-3π/4})²`, the route gives `h ≥ (13/8) cos(π/L) √d / (π e (L - 1 + 4√2 κ))`. Times `L/√d` this is
`0.18374` at `L = 8`, its minimum on `L ≥ 8`; the fully rational form used in the proof gives `0.18343` there. So
`c₁ = 9/50`. The upper-bound route gives `h ≤ 1.1580 √d log d` at `L = 8` with exact constants (`1.1597` with the
rational brackets), and less beyond, so `c₂ = 6/5`. The boundary inverts the lower bound with `A = 2h/c₁ = (100/9) h`.

**Scope (the other side of the boundary).** These statements bound `d` above in terms of `h`. They say nothing about
fields of class number exactly `h` existing near the bound; a statement that `max {d : h(-d) = h}` is at least about
`h²/log² h` is NOT provable by this route, and none is made here.

The lower bound and the boundary use OpenAI's 7/8 theorem (openai/math) at real points `σ ∈ (7/8, 1)` only; the upper
bound uses no zero-free region. The route: the Chowla–Selberg formula (S. Chowla and A. Selberg) for every positive
definite form, through the class-sum extension posted in the comments of Tao's challenge (LemmaLab), evaluated near
`s = 1` instead of at `s = 7/8`.
-/

open NumberField

namespace BoundariesOfClassV1

/-- **(L) Explicit lower bound.** For `K = ℚ(√-m)` with `d = |disc K| ≥ 2981`: `(9/50) · √d / log d ≤ h(K)`. -/
theorem classNumber_lower (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hd : (2981 : ℝ) ≤ |(discr K : ℝ)|) :
    (9 / 50 : ℝ) * Real.sqrt |(discr K : ℝ)| / Real.log |(discr K : ℝ)| ≤ (classNumber K : ℝ) := by
  sorry

/-- **(U) Explicit upper bound** (unconditional). For `K = ℚ(√-m)` with `d = |disc K| ≥ 2981`:
`h(K) ≤ (6/5) · √d · log d`. -/
theorem classNumber_upper (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hd : (2981 : ℝ) ≤ |(discr K : ℝ)|) :
    (classNumber K : ℝ) ≤ (6 / 5 : ℝ) * Real.sqrt |(discr K : ℝ)| * Real.log |(discr K : ℝ)| := by
  sorry

/-- **(B) The class number boundary.** For every `h ≥ 1`, every `K = ℚ(√-m)` with `h(K) ≤ h` has
`|disc K| ≤ max(2981, (A (log A + log(2 log A)))²)`, `A = (100/9) h`. This is of size `(C h log h)²`. -/
theorem abs_discr_le_of_classNumber_le (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (h : ℕ) (hh : 1 ≤ h) (hcl : classNumber K ≤ h) :
    |(discr K : ℝ)| ≤ max 2981
      (((100 / 9 : ℝ) * h * (Real.log ((100 / 9 : ℝ) * h) + Real.log (2 * Real.log ((100 / 9 : ℝ) * h)))) ^ 2) := by
  sorry

end BoundariesOfClassV1
