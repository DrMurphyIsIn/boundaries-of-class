import Mathlib

/-!
# BoundariesOfClass.PolyaVinogradov.GaussSum: the Gauss sum of a primitive character, and the Fourier expansion

Pinned environment: Lean v4.34.1, Mathlib d13f23b. Mathlib only.

For a primitive Dirichlet character `χ` of level `q`, write `τ(χ) = Σ_a χ(a) e(a/q)` (Mathlib's
`gaussSum χ ZMod.stdAddChar`).

* `gaussSum_mul_star_gaussSum`: `τ(χ) · conj τ(χ) = q`, so `‖τ(χ)‖ = √q` (`norm_gaussSum`). Mathlib's
  `gaussSum_mul_gaussSum_eq_card` covers prime level only; here the identity is read off the discrete Fourier inversion
  formula `ZMod.dft_dft`, together with Mathlib's formula `𝓕 χ = χ⁻¹(-·) τ(χ)` for primitive characters
  (`DirichletCharacter.IsPrimitive.fourierTransform_eq_inv_mul_gaussSum`), applied to `χ` and to `χ⁻¹`.
* `apply_eq_sum_gaussSum`: the Fourier expansion `χ(n) = q⁻¹ τ(χ) Σ_j χ⁻¹(-j) e(jn/q)`.

These are the classical inputs to the Pólya–Vinogradov inequality. Mathlib's Gauss sums are due to M. Stoll, and the
discrete Fourier transform on `ZMod N`, with the Gauss-sum formula for primitive characters, to D. Loeffler.
-/

set_option autoImplicit false

namespace BoundariesOfClass.PolyaVinogradov

open ZMod DirichletCharacter

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

omit [NeZero q] in
/-- The inverse of a primitive character is primitive (Mathlib's `conductor_inv`). -/
lemma isPrimitive_inv (hχ : χ.IsPrimitive) : χ⁻¹.IsPrimitive := by
  rw [isPrimitive_def, conductor_inv]; exact hχ

/-- Mathlib's formula `𝓕 χ = χ⁻¹(-·) τ(χ)` for a primitive character, as an equality of functions. -/
lemma dft_eq_of_isPrimitive (hχ : χ.IsPrimitive) :
    𝓕 χ = fun k => χ⁻¹ (-k) * gaussSum χ stdAddChar :=
  funext fun k => hχ.fourierTransform_eq_inv_mul_gaussSum k

/-- **`τ(χ) · conj τ(χ) = q`** for a primitive character `χ` of level `q`. -/
theorem gaussSum_mul_star_gaussSum (hχ : χ.IsPrimitive) :
    gaussSum χ stdAddChar * star (gaussSum χ stdAddChar) = q := by
  -- Fourier inversion at `1`: `𝓕 (𝓕 χ) 1 = q χ(-1)`, and `𝓕 (𝓕 χ) 1 = τ(χ⁻¹) τ(χ)`
  have h1 := congrFun (dft_dft (χ : ZMod q → ℂ)) 1
  rw [dft_eq_of_isPrimitive hχ, dft_mul_const, dft_comp_neg (fun k => χ⁻¹ k),
    dft_eq_of_isPrimitive (isPrimitive_inv hχ), inv_inv] at h1
  simp only [neg_neg, map_one, one_mul, smul_eq_mul] at h1
  -- `conj τ(χ) = χ(-1) τ(χ⁻¹)`
  have h2 : star (gaussSum χ stdAddChar) = χ (-1) * gaussSum χ⁻¹ stdAddChar := by
    have h := gaussSum_mulShift_eq χ⁻¹ stdAddChar (-1)
    rw [inv_inv, Units.coe_neg_one] at h
    rw [star_gaussSum_eq, AddChar.inv_mulShift, h]
  have h3 : χ (-1) * χ (-1) = 1 := by rw [← map_mul, neg_one_mul, neg_neg, map_one]
  rw [h2]
  linear_combination (χ (-1)) * h1 + (q : ℂ) * h3

/-- **`‖τ(χ)‖ = √q`** for a primitive character `χ` of level `q`. -/
theorem norm_gaussSum (hχ : χ.IsPrimitive) : ‖gaussSum χ stdAddChar‖ = Real.sqrt q := by
  have h := gaussSum_mul_star_gaussSum hχ
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
  have h' : ‖gaussSum χ stdAddChar‖ ^ 2 = (q : ℝ) := by exact_mod_cast h
  rw [← h', Real.sqrt_sq (norm_nonneg _)]

/-- **The Fourier expansion of a primitive character:** `χ(n) = q⁻¹ τ(χ) Σ_j χ⁻¹(-j) e(jn/q)`. -/
theorem apply_eq_sum_gaussSum (hχ : χ.IsPrimitive) (n : ZMod q) :
    χ n = (q : ℂ)⁻¹ * gaussSum χ stdAddChar * ∑ j : ZMod q, χ⁻¹ (-j) * stdAddChar (j * n) := by
  have h := congrFun (LinearEquiv.symm_apply_apply (dft (N := q) (E := ℂ)) (χ : ZMod q → ℂ)) n
  rw [invDFT_apply, dft_eq_of_isPrimitive hχ] at h
  rw [← h]
  simp only [smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end BoundariesOfClass.PolyaVinogradov
