import Mathlib

/-!
# Comparator challenge, version 2: explicit class number bounds for imaginary quadratic fields

Statements only (`sorry`); the proofs are the solution side. This version supersedes version 1, which is archived as
`v1/Boundary.lean` outside every Lean library, in its own namespace. It also supersedes the earlier standalone drafts of
the class number formula and Pólya–Vinogradov statements, which are not part of this repository. The import closure is
Mathlib alone (Lean v4.34.1, Mathlib d13f23b, the openai/math 7/8 environment).

Trust base: these statements; the Mathlib definitions they use (`NumberField`, `NumberField.classNumber`,
`NumberField.discr`, `NumberField.dedekindZeta`, `NumberField.Units.torsionOrder`, `riemannZeta`, `DirichletCharacter`,
the trivial character `1`, `DirichletCharacter.IsPrimitive`, `DirichletCharacter.LFunction`, `Module.finrank`,
`Squarefree`, `Int.natAbs`, `NeZero`, `ExistsUnique`, `Finset.range` and `Finset.sum`, `Real.sqrt`, `Real.log`, `Real.pi`,
the real power `x ^ (y : ℝ)`, natural powers, `abs`, `min`, `max`, `Complex.re`, the norm on `ℂ`, the field operations and
real and complex division, and the casts `ℕ → K`, `ℕ → ℤ`, `ℤ → ZMod q`, `ℕ → ℝ`, `ℤ → ℝ`, `ℕ → ℂ` and `ℝ → ℂ`); the Lean
kernel and nanoda; and the axioms `propext`, `Classical.choice`, `Quot.sound`.

Vocabulary as in `CN1.classNumber_eq_one_iff` and `HCN.classNumber_le_two_iff` (tenth-discriminant): `K` is an abstract
number field of degree two over `ℚ` containing a square root of `-m`, `m` a squarefree natural number (so `m ≥ 1`, `α`
is irrational and `K ≅ ℚ(√-m)`). The discriminant is Mathlib's `NumberField.discr K`; for these fields `|discr K| = m` if
`m ≡ 3 (mod 4)` and `4m` otherwise, and `d := |discr K|` below.

* **(L′) Lower bound.** `(1/3) √d / log d ≤ h(K)` for `d ≥ 2981`.
* **(P′) Power lower bound.** `d^{7/16} / 17 ≤ h(K)` for `d ≥ 1000`.
* **(L1), (CNF) Dirichlet's class number formula.** `‖L(1, χ)‖ ≤ log q + 7/6` for every non-trivial Dirichlet character
  of level `q ≥ 7`; `L(1, χ) = 2π h(K) / (w(K) √d)` in general and `L(1, χ) = π h(K) / √d` for `d ≥ 5`, for every
  Dirichlet character `χ` of level `d` with `ζ_K(s) = ζ(s) L(s, χ)` on `Re s > 1`; and exactly one such `χ` exists.
* **(U′) Upper bound.** `h(K) ≤ (1/π) √d (log d + 7/6)` for `d ≥ 5`. No zero-free region is used.
* **(PV) The Pólya–Vinogradov inequality** with an explicit constant, the half-log bound for `L(1, χ)` at a primitive
  character, the textbook upper bound `h(K) ≤ (1/π) √d (½ log d + log(log d + 1/3) + 5/3)` for `d ≥ 5` (and its
  `log log` form), and the primitivity of every character pinned down by the factorisation above.
* **(B′) The boundary.** If `h(K) ≤ h` then `d ≤ max(2981, (A (log A + log(2 log A)))²)`, `A = 6h`.
* **(B*) The boundary, power form.** If `h(K) ≤ h` then also `d ≤ max(1000, (17h)^{16/7})`.
* **(T) Thresholds.** If `h(K) ≤ N` then `d < X_N`, for ten values of `N`; and three point values: `d ≥ X` implies
  `h(K) ≥ N`.

**The character.** The Kronecker character `χ_{-d}` is not a Mathlib definition. The class number formula is therefore
stated for every Dirichlet character `χ` of level `d` with `ζ_K(s) = ζ(s) L(s, χ)` on `Re s > 1`. That property
forces `χ ≠ 1`, so `L(1, χ)` is the value of an entire function, not a junk value.
`existsUnique_LFunction_factorisation` states that exactly one such `χ` exists (it is the Kronecker character; the
coefficients of an L-series are unique), so the class number formula statements are not vacuous and are about one
character, and `isPrimitive_of_factorisation` states that it is primitive.

No junk value is reached. `Real.log` is applied to `q ≥ 2` and `q ≥ 7` (characters), to `d ≥ 5` and `d ≥ 2981`, to
`log q ≥ log 7 > 1` and `log d ≥ log 5 > 1` (inside a second logarithm), and to `6h ≥ 6` and `2 log 6h ≥ 2 log 6 > 3.58`.
Every divisor is nonzero, and the real power is applied only to `d ≥ 1000` and `17h ≥ 17`. The hypotheses `1000 ≤ d`,
`2981 ≤ d` and `5 ≤ d` exclude `m = 1` (`d = 4`) and `m = 3` (`d = 3`). The level hypothesis `1 < q` in the
Pólya–Vinogradov inequality is necessary: the trivial character of level `1` is primitive and its interval sums are
unbounded.

**The routes and credits.**
- (L′), (P′), (B′), (B*) and (T): the Chowla–Selberg formula (S. Chowla and A. Selberg) for every positive definite form,
  through the class-sum extension posted in the comments of Tao's challenge (LemmaLab), with each ideal class charged the
  exact minimum over its leading coefficient of its Chowla–Selberg main term, and OpenAI's theorem that no Dirichlet
  L-function vanishes for `Re s > 7/8` (openai/math), used at real points only.
- (CNF) is Dirichlet's class number formula. It is proved from Mathlib's residue formula for the Dedekind zeta function
  (`NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`) and the factorisation `ζ_K = ζ · L(·, χ_{-d})` of
  tenth-discriminant's CN-1 formalization. (L1) is classical partial summation against the periodic character sum, and
  (U′) combines the two. No zero-free region, no class sums and no Chowla–Selberg formula are used.
- (PV) is the inequality of G. Pólya and I. M. Vinogradov (1918), proved through Gauss sums and the finite Fourier
  expansion of a primitive character, with Mathlib's Gauss sums (M. Stoll) and its discrete Fourier transform on `ZMod N`
  and Fourier formula for primitive characters (D. Loeffler).

**Scope (the other side of the boundary).** These statements bound `d` above in terms of `h`. They say nothing about
fields of class number exactly `h` existing near the bound.
-/

open NumberField

namespace BoundariesOfClass

/-! ### Lower bounds -/

/-- **(L′) Explicit lower bound.** For `K = ℚ(√-m)` with `d = |disc K| ≥ 2981`: `(1/3) · √d / log d ≤ h(K)`. -/
theorem classNumber_lower (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hd : (2981 : ℝ) ≤ |(discr K : ℝ)|) :
    (1 / 3 : ℝ) * Real.sqrt |(discr K : ℝ)| / Real.log |(discr K : ℝ)| ≤ (classNumber K : ℝ) := by
  sorry

/-- **(P′) Power lower bound.** For `K = ℚ(√-m)` with `d = |disc K| ≥ 1000`: `d^{7/16} / 17 ≤ h(K)`. -/
theorem classNumber_ge_rpow (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hd : (1000 : ℝ) ≤ |(discr K : ℝ)|) :
    |(discr K : ℝ)| ^ ((7 : ℝ) / 16) / 17 ≤ (classNumber K : ℝ) := by
  sorry

/-! ### Dirichlet's class number formula and the upper bound (U′) -/

/-- **An explicit bound for `L(1, χ)`.** For every non-trivial Dirichlet character `χ` of level `q ≥ 7`:
`‖L(1, χ)‖ ≤ log q + 7/6`. -/
theorem norm_LFunction_one_le {q : ℕ} [NeZero q] (hq : 7 ≤ q) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ‖χ.LFunction 1‖ ≤ Real.log q + 7 / 6 := by
  sorry

/-- **Dirichlet's class number formula, general `w`.** For `K = ℚ(√-m)` and every Dirichlet character `χ` of level
`|disc K|` with `ζ_K(s) = ζ(s) L(s, χ)` on `Re s > 1`: `L(1, χ) = 2π h(K) / (w(K) √|disc K|)`. -/
theorem LFunction_one_eq_general (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    [NeZero (discr K).natAbs] (χ : DirichletCharacter ℂ (discr K).natAbs)
    (hχ : ∀ s : ℂ, 1 < s.re → dedekindZeta K s = riemannZeta s * χ.LFunction s) :
    χ.LFunction 1 =
      2 * Real.pi * classNumber K / (Units.torsionOrder K * Real.sqrt |(discr K : ℝ)|) := by
  sorry

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
  sorry

/-- **Such a character exists, and it is unique** (so the two statements above are not vacuous, and they are about one
character): the Kronecker character `χ_{-d}`. -/
theorem existsUnique_LFunction_factorisation (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    [NeZero (discr K).natAbs] :
    ∃! χ : DirichletCharacter ℂ (discr K).natAbs,
      ∀ s : ℂ, 1 < s.re → dedekindZeta K s = riemannZeta s * χ.LFunction s := by
  sorry

/-- **(U′) Explicit upper bound.** For `K = ℚ(√-m)` with `d = |disc K| ≥ 5`: `h(K) ≤ (1/π) √d (log d + 7/6)`. -/
theorem classNumber_le_sharp (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hd : (5 : ℝ) ≤ |(discr K : ℝ)|) :
    (classNumber K : ℝ) ≤
      Real.sqrt |(discr K : ℝ)| * (Real.log |(discr K : ℝ)| + 7 / 6) / Real.pi := by
  sorry

/-! ### The Pólya–Vinogradov inequality and the textbook upper bound -/

/-- **The Pólya–Vinogradov inequality** (G. Pólya and I. M. Vinogradov, 1918), with an explicit constant. For a
primitive Dirichlet character `χ` of level `q > 1`, every sum of `χ` over `N` consecutive integers starting at `M` has
norm at most `√q (log q + 1/3)`. -/
theorem norm_sum_le_of_isPrimitive {q : ℕ} [NeZero q] (hq : 1 < q) (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (M : ℤ) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, χ ((M + n : ℤ) : ZMod q)‖ ≤ Real.sqrt q * (Real.log q + 1 / 3) := by
  sorry

/-- **The half-log bound for `L(1, χ)`.** For a primitive Dirichlet character `χ` of level `q ≥ 7`:
`‖L(1, χ)‖ ≤ ½ log q + log(log q + 1/3) + 5/3`. -/
theorem norm_LFunction_one_le_of_isPrimitive {q : ℕ} [NeZero q] (hq : 7 ≤ q) (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) :
    ‖χ.LFunction 1‖ ≤ Real.log q / 2 + Real.log (Real.log q + 1 / 3) + 5 / 3 := by
  sorry

/-- **The half-log bound for `L(1, χ)`, `log log` form.** For a primitive Dirichlet character `χ` of level `q ≥ 7`:
`‖L(1, χ)‖ ≤ ½ log q + log log q + 2`. -/
theorem norm_LFunction_one_le_loglog {q : ℕ} [NeZero q] (hq : 7 ≤ q) (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) :
    ‖χ.LFunction 1‖ ≤ Real.log q / 2 + Real.log (Real.log q) + 2 := by
  sorry

/-- **The textbook upper bound for the class number.** For `K = ℚ(√-m)` with `d = |disc K| ≥ 5` (that is,
`m ∉ {1, 3}`): `h(K) ≤ (1/π) √d (½ log d + log(log d + 1/3) + 5/3)`. -/
theorem classNumber_le_half_log (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hd : (5 : ℝ) ≤ |(discr K : ℝ)|) :
    (classNumber K : ℝ) ≤ Real.sqrt |(discr K : ℝ)| *
      (Real.log |(discr K : ℝ)| / 2 + Real.log (Real.log |(discr K : ℝ)| + 1 / 3) + 5 / 3) / Real.pi := by
  sorry

/-- **The textbook upper bound for the class number, `log log` form.** For `K = ℚ(√-m)` with `d = |disc K| ≥ 5`:
`h(K) ≤ (1/π) √d (½ log d + log log d + 2)`. -/
theorem classNumber_le_loglog (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hd : (5 : ℝ) ≤ |(discr K : ℝ)|) :
    (classNumber K : ℝ) ≤ Real.sqrt |(discr K : ℝ)| *
      (Real.log |(discr K : ℝ)| / 2 + Real.log (Real.log |(discr K : ℝ)|) + 2) / Real.pi := by
  sorry

/-- **The character of an imaginary quadratic field is primitive.** For `K = ℚ(√-m)`, every Dirichlet character `χ`
of level `|disc K|` with `ζ_K(s) = ζ(s) L(s, χ)` on `Re s > 1` is primitive.

This bears on every statement that pins a character down by this factorisation, such as Dirichlet's class number
formula in Mathlib's vocabulary. The proof shows that the factorisation determines `χ` uniquely: an L-series determines
its coefficients, so `χ` is the Kronecker character `χ_{-d}`, `d = |disc K|`. That character is primitive, so its
conductor is `d`. -/
theorem isPrimitive_of_factorisation (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    [NeZero (discr K).natAbs] (χ : DirichletCharacter ℂ (discr K).natAbs)
    (hχ : ∀ s : ℂ, 1 < s.re → dedekindZeta K s = riemannZeta s * χ.LFunction s) :
    χ.IsPrimitive := by
  sorry

/-! ### The boundary -/

/-- **(B′) The class number boundary.** For every `h ≥ 1`, every `K = ℚ(√-m)` with `h(K) ≤ h` has
`|disc K| ≤ max(2981, (A (log A + log(2 log A)))²)`, `A = 6h`. -/
theorem abs_discr_le_of_classNumber_le (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (h : ℕ) (hh : 1 ≤ h) (hcl : classNumber K ≤ h) :
    |(discr K : ℝ)| ≤ max 2981
      (((6 : ℝ) * h * (Real.log ((6 : ℝ) * h) + Real.log (2 * Real.log ((6 : ℝ) * h)))) ^ 2) := by
  sorry

/-- **(B*) The class number boundary, power form.** For every `h ≥ 1`, every `K = ℚ(√-m)` with `h(K) ≤ h` has
`|disc K| ≤ min(max(1000, (17h)^{16/7}), max(2981, (A (log A + log(2 log A)))²))`, `A = 6h`. -/
theorem abs_discr_le_of_classNumber_le' (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (h : ℕ) (hh : 1 ≤ h) (hcl : classNumber K ≤ h) :
    |(discr K : ℝ)| ≤ min (max 1000 (((17 : ℝ) * h) ^ ((16 : ℝ) / 7)))
      (max 2981
        (((6 : ℝ) * h * (Real.log ((6 : ℝ) * h) + Real.log (2 * Real.log ((6 : ℝ) * h)))) ^ 2)) := by
  sorry

/-! ### (T) Thresholds: `h(K) ≤ N ⇒ |disc K| < X_N` -/

theorem abs_discr_lt_of_classNumber_le_one (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hcl : classNumber K ≤ 1) : |(discr K : ℝ)| < 660 := by
  sorry

theorem abs_discr_lt_of_classNumber_le_two (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hcl : classNumber K ≤ 2) : |(discr K : ℝ)| < 2210 := by
  sorry

theorem abs_discr_lt_of_classNumber_le_three (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hcl : classNumber K ≤ 3) : |(discr K : ℝ)| < 4740 := by
  sorry

theorem abs_discr_lt_of_classNumber_le_four (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hcl : classNumber K ≤ 4) : |(discr K : ℝ)| < 8310 := by
  sorry

theorem abs_discr_lt_of_classNumber_le_five (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hcl : classNumber K ≤ 5) : |(discr K : ℝ)| < 13000 := by
  sorry

theorem abs_discr_lt_of_classNumber_le_ten (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hcl : classNumber K ≤ 10) : |(discr K : ℝ)| < 54500 := by
  sorry

theorem abs_discr_lt_of_classNumber_le_hundred (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hcl : classNumber K ≤ 100) : |(discr K : ℝ)| < 8620000 := by
  sorry

theorem abs_discr_lt_of_classNumber_le_thousand (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hcl : classNumber K ≤ 1000) : |(discr K : ℝ)| < 1605000000 := by
  sorry

theorem abs_discr_lt_of_classNumber_le_two_thousand (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hcl : classNumber K ≤ 2000) : |(discr K : ℝ)| < 7800000000 := by
  sorry

theorem abs_discr_lt_of_classNumber_le_five_thousand (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hcl : classNumber K ≤ 5000) : |(discr K : ℝ)| < 63200000000 := by
  sorry

/-! ### (T) Point values: `|disc K| ≥ X ⇒ h(K) ≥ N` -/

theorem classNumber_ge_of_two_e9_le (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hd : (2000000000 : ℝ) ≤ |(discr K : ℝ)|) : 1101 ≤ classNumber K := by
  sorry

theorem classNumber_ge_of_one_nine_eight_e10_le (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hd : (19800000000 : ℝ) ≤ |(discr K : ℝ)|) : 3007 ≤ classNumber K := by
  sorry

theorem classNumber_ge_of_two_pow_forty_le (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hd : (2 : ℝ) ^ 40 ≤ |(discr K : ℝ)|) : 17450 ≤ classNumber K := by
  sorry

end BoundariesOfClass
