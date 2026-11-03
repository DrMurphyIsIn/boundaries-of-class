import Mathlib
import CN1.Foundations.Discr
import CN1.Finite.Params

/-!
# BoundariesOfClassNegControls.Fields: the shared fields `K_m = ℚ(√-m)` for the negative controls

Pinned environment: Lean v4.34.1, Mathlib d13f23b. For a positive natural number `m`, `KField m` is
`AdjoinRoot (X² + m)` over `ℚ`. It is a number field of degree two containing the root `rootK m` of `X² + m`, so every
statement in the challenge vocabulary (`Module.finrank ℚ K = 2`, `∃ α : K, α² = -m`, `Squarefree m`) can be
instantiated at it. Used by the field-level tampers of the negative controls (`m = 7, 11, 23, 163, 427, 2983`).

* `KField m`, with `Field`, `NumberField` (for `[NeZero m]`);
* `finrank_KField : Module.finrank ℚ (KField m) = 2`;
* `rootK m : KField m`, `rootK_sq : rootK m ^ 2 = -(m : KField m)`, `exists_sq_eq_neg : ∃ α, α ^ 2 = -(m : KField m)`;
* `abs_discr_KField (hm : Squarefree m) : |(NumberField.discr (KField m) : ℝ)| = (CN1.Finite.dOf m : ℝ)`;
* `squarefree_7`, `_11`, `_23`, `_163`, `_427`, `_2983`.

Never import this library together with the solution's main module and a challenge module.
-/

set_option autoImplicit false

open Polynomial

namespace BoundariesOfClassNegControls

/-- The polynomial `X² + m` over `ℚ`. -/
noncomputable def polyK (m : ℕ) : ℚ[X] := X ^ 2 + C (m : ℚ)

lemma polyK_eq (m : ℕ) : polyK m = X ^ 2 - C (-(m : ℚ)) := by
  unfold polyK; rw [C_neg, sub_neg_eq_add]

lemma polyK_irreducible (m : ℕ) [NeZero m] : Irreducible (polyK m) := by
  rw [polyK_eq]
  refine X_pow_sub_C_irreducible_of_prime Nat.prime_two (fun b hb => ?_)
  have h0 : (0 : ℚ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have : (0 : ℚ) ≤ b ^ 2 := sq_nonneg b
  linarith

instance (m : ℕ) [NeZero m] : Fact (Irreducible (polyK m)) := ⟨polyK_irreducible m⟩

/-- `K_m = ℚ(√-m)`. -/
abbrev KField (m : ℕ) : Type := AdjoinRoot (polyK m)

lemma polyK_ne_zero (m : ℕ) : polyK m ≠ 0 := by
  intro h
  have := congrArg natDegree h
  rw [polyK, natDegree_X_pow_add_C] at this
  simp at this

lemma natDegree_polyK (m : ℕ) : (polyK m).natDegree = 2 := by
  rw [polyK, natDegree_X_pow_add_C]

theorem finrank_KField (m : ℕ) [NeZero m] : Module.finrank ℚ (KField m) = 2 := by
  rw [(AdjoinRoot.powerBasis (polyK_ne_zero m)).finrank, AdjoinRoot.powerBasis_dim, natDegree_polyK]

instance (m : ℕ) [NeZero m] : FiniteDimensional ℚ (KField m) :=
  (AdjoinRoot.powerBasis (polyK_ne_zero m)).finite

instance (m : ℕ) [NeZero m] : NumberField (KField m) := NumberField.mk

/-- The root `√-m`. -/
noncomputable def rootK (m : ℕ) : KField m := AdjoinRoot.root (polyK m)

theorem rootK_sq (m : ℕ) : rootK m ^ 2 = -((m : ℕ) : KField m) := by
  have h := AdjoinRoot.eval₂_root (polyK m)
  have e : eval₂ (AdjoinRoot.of (polyK m)) (AdjoinRoot.root (polyK m)) (polyK m) =
      AdjoinRoot.root (polyK m) ^ 2 + ((m : ℕ) : KField m) := by
    unfold polyK
    rw [eval₂_add, eval₂_X_pow, eval₂_C]
    congr 1
  rw [e] at h
  rw [rootK, eq_neg_iff_add_eq_zero]
  exact h

theorem exists_sq_eq_neg (m : ℕ) : ∃ α : KField m, α ^ 2 = -((m : ℕ) : KField m) := ⟨rootK m, rootK_sq m⟩

/-- `|disc K_m| = dOf m` (CN-1's `discr_eq`). -/
theorem abs_discr_KField (m : ℕ) [NeZero m] (hm : Squarefree m) :
    |(NumberField.discr (KField m) : ℝ)| = (CN1.Finite.dOf m : ℝ) := by
  have h := CN1.Foundations.discr_eq (rootK_sq m) (finrank_KField m) hm
  rw [h]
  push_cast
  rw [abs_neg, abs_of_nonneg (by positivity)]
  have : CN1.Foundations.disc m = CN1.Finite.dOf m := rfl
  rw [this]

theorem squarefree_7 : Squarefree (7 : ℕ) := (by norm_num : Nat.Prime 7).squarefree
theorem squarefree_11 : Squarefree (11 : ℕ) := (by norm_num : Nat.Prime 11).squarefree
theorem squarefree_23 : Squarefree (23 : ℕ) := (by norm_num : Nat.Prime 23).squarefree
theorem squarefree_163 : Squarefree (163 : ℕ) := (by norm_num : Nat.Prime 163).squarefree
theorem squarefree_427 : Squarefree (427 : ℕ) := by
  rw [show (427 : ℕ) = 7 * 61 by norm_num, Nat.squarefree_mul_iff]
  exact ⟨by norm_num, (by norm_num : Nat.Prime 7).squarefree, (by norm_num : Nat.Prime 61).squarefree⟩
theorem squarefree_2983 : Squarefree (2983 : ℕ) := by
  rw [show (2983 : ℕ) = 19 * 157 by norm_num, Nat.squarefree_mul_iff]
  exact ⟨by norm_num, (by norm_num : Nat.Prime 19).squarefree, (by norm_num : Nat.Prime 157).squarefree⟩

end BoundariesOfClassNegControls
