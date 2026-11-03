import BoundariesOfClass.ClassNumberFormula.Invariants
import BoundariesOfClass.Primitivity.Kronecker
import CN1.Epstein.Factorization

/-!
# BoundariesOfClass.Primitivity.Field: the character of an imaginary quadratic field is primitive

Pinned environment: Lean v4.34.1, Mathlib d13f23b. Imports Mathlib and the Mathlib-only foundations and factorisation
of the CN-1 formalization (tenth-discriminant).

* `BoundariesOfClass.isPrimitive_of_factorisation`: for `K = ℚ(√-m)`, every Dirichlet character `χ` of level
  `|disc K|` with `ζ_K(s) = ζ(s) L(s, χ)` on `Re s > 1` is primitive. Its conductor is therefore `|disc K|`.

The statement uses Mathlib's vocabulary only. The proof identifies `χ` with the Kronecker character `χ_{-d}`. Both
factorisations hold on `Re s > 1`, where `ζ(s) ≠ 0`, so the two L-series agree there, and an L-series determines its
coefficients (Mathlib's `LSeries.eq_of_LSeries_eventually_eq`). Then `kroneckerChar_isPrimitive` applies.

So the character pinned down by the factorisation in the statements of Dirichlet's class number formula is unique, and
it is the primitive Kronecker character.
-/

set_option autoImplicit false

open NumberField CN1.Foundations

namespace BoundariesOfClass.Primitivity

/-- Two Dirichlet characters of the same level whose L-functions agree on `Re s > 1` are equal. -/
theorem eq_of_LFunction_eq {N : ℕ} [NeZero N] {χ ψ : DirichletCharacter ℂ N}
    (h : ∀ s : ℂ, 1 < s.re → χ.LFunction s = ψ.LFunction s) : χ = ψ := by
  have hab : ∀ φ : DirichletCharacter ℂ N, LSeries.abscissaOfAbsConv (fun n => φ n) < ⊤ := fun φ =>
    (LSeries.abscissaOfAbsConv_le_of_le_const ⟨1, fun n _ => DirichletCharacter.norm_le_one φ _⟩).trans_lt
      (by exact_mod_cast EReal.coe_lt_top 1)
  have hcoef : ∀ n : ℕ, n ≠ 0 → χ n = ψ n := by
    intro n hn
    refine LSeries.eq_of_LSeries_eventually_eq (f := fun n => χ n) (g := fun n => ψ n) (hab χ) (hab ψ) ?_ hn
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
    have hx' : 1 < (x : ℂ).re := by simpa using hx
    rw [← DirichletCharacter.LFunction_eq_LSeries χ hx', ← DirichletCharacter.LFunction_eq_LSeries ψ hx']
    exact h x hx'
  refine MulChar.ext' fun a => ?_
  have hne : a.val + N ≠ 0 := by have := NeZero.pos N; omega
  have hcast : ((a.val + N : ℕ) : ZMod N) = a := by
    rw [Nat.cast_add, ZMod.natCast_self, add_zero, ZMod.natCast_zmod_val]
  have := hcoef _ hne
  rwa [hcast] at this

end BoundariesOfClass.Primitivity

namespace BoundariesOfClass

open BoundariesOfClass.ClassNumberFormula BoundariesOfClass.Primitivity

/-- **The character of an imaginary quadratic field is primitive.** For `K = ℚ(√-m)`, every Dirichlet character `χ`
of level `|disc K|` with `ζ_K(s) = ζ(s) L(s, χ)` on `Re s > 1` is primitive.

This bears on every statement that pins a character down by this factorisation, such as Dirichlet's class number
formula in Mathlib's vocabulary. The proof shows that the factorisation determines `χ` uniquely: an L-series determines
its coefficients (`eq_of_LFunction_eq`), so `χ` is the Kronecker character `χ_{-d}`, `d = |disc K|`. That character is
primitive, so its conductor is `d`. -/
theorem isPrimitive_of_factorisation (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    [NeZero (discr K).natAbs] (χ : DirichletCharacter ℂ (discr K).natAbs)
    (hχ : ∀ s : ℂ, 1 < s.re → dedekindZeta K s = riemannZeta s * χ.LFunction s) :
    χ.IsPrimitive := by
  obtain ⟨α, hα⟩ := hsq
  -- work at the level `disc m`, which is `|disc K|`
  suffices H : ∀ (N : ℕ) [NeZero N], N = disc m → ∀ ψ : DirichletCharacter ℂ N,
      (∀ s : ℂ, 1 < s.re → dedekindZeta K s = riemannZeta s * ψ.LFunction s) → ψ.IsPrimitive from
    H _ (natAbs_discr_eq hα hK hm) χ hχ
  intro N _ hN ψ hψ
  subst hN
  have hk : ψ = kroneckerChar m := eq_of_LFunction_eq fun s hs =>
    mul_left_cancel₀ (riemannZeta_ne_zero_of_one_lt_re hs)
      ((hψ s hs).symm.trans (CN1.Epstein.dedekindZeta_eq_riemannZeta_mul_LFunction hα hK hm hs))
  rw [hk]
  exact kroneckerChar_isPrimitive hm

end BoundariesOfClass
