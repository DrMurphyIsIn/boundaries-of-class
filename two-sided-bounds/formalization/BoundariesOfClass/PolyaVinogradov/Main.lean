import BoundariesOfClass.PolyaVinogradov.GaussSum
import BoundariesOfClass.PolyaVinogradov.Geometric

/-!
# BoundariesOfClass.PolyaVinogradov.Main: the Pólya–Vinogradov inequality

Pinned environment: Lean v4.34.1, Mathlib d13f23b. Mathlib only.

**The Pólya–Vinogradov inequality** (G. Pólya and I. M. Vinogradov, 1918). For a primitive Dirichlet character `χ`
of level `q > 1`, every sum of `χ` over consecutive integers has norm at most `√q H_{⌊q/2⌋} ≤ √q (log q + 1/3)`.

The proof is the classical one. By the Fourier expansion (`GaussSum.lean`),
`Σ_{i<ℓ} χ(a + i) = q⁻¹ τ(χ) Σ_j χ⁻¹(-j) Σ_{i<ℓ} e(j(a + i)/q)`, with `‖τ(χ)‖ = √q`. The term `j = 0` vanishes because
`χ⁻¹(0) = 0`. Every other inner sum is a geometric sum of norm at most `q/(2 min(v, q - v))`, `v = j.val`, and these
add up to at most `q H_{⌊q/2⌋}` (`Geometric.lean`). Finally `H_n ≤ 1 + log n` and `1 - log 2 < 1/3`.

* `norm_sum_le_sqrt_mul_harmonic`: `‖Σ_{i<ℓ} χ(a + i)‖ ≤ √q H_{⌊q/2⌋}`, for every start `a ∈ ZMod q`.
* `harmonic_half_le`: `H_{⌊q/2⌋} ≤ log q + 1/3` for `q ≥ 2`.
* `BoundariesOfClass.norm_sum_le_sqrt_mul_harmonic_of_isPrimitive`: `‖Σ_{0 ≤ n < N} χ(M + n)‖ ≤ √q H_{⌊q/2⌋}` for every
  integer `M`.
* `BoundariesOfClass.norm_sum_le_of_isPrimitive`: `‖Σ_{0 ≤ n < N} χ(M + n)‖ ≤ √q (log q + 1/3)` for every integer
  `M`.
-/

set_option autoImplicit false

namespace BoundariesOfClass.PolyaVinogradov

open ZMod Finset DirichletCharacter

variable {q : ℕ} [NeZero q]

/-- A sum over `ZMod q` is the sum over `0 ≤ v < q` of the casts. -/
lemma sum_zmod_eq_sum_range {M : Type*} [AddCommMonoid M] (f : ZMod q → M) :
    ∑ x, f x = ∑ v ∈ range q, f (v : ZMod q) := by
  refine (Finset.sum_nbij' (fun i : ℕ => (i : ZMod q)) (fun x : ZMod q => x.val) ?_ ?_ ?_ ?_ ?_).symm
  · intro i _; exact mem_univ _
  · intro x _; exact mem_range.mpr (ZMod.val_lt x)
  · intro i hi; exact ZMod.val_cast_of_lt (mem_range.mp hi)
  · intro x _; exact ZMod.natCast_zmod_val x
  · intro i _; rfl

/-- **Pólya–Vinogradov, harmonic form.** For a primitive character `χ` of level `q ≠ 1`, every sum of `ℓ` consecutive
values has norm at most `√q H_{⌊q/2⌋}`. -/
theorem norm_sum_le_sqrt_mul_harmonic (hq : q ≠ 1) {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (a : ZMod q) (ℓ : ℕ) :
    ‖∑ i ∈ range ℓ, χ (a + (i : ZMod q))‖ ≤ Real.sqrt q * (harmonic (q / 2) : ℝ) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  set τ := gaussSum χ stdAddChar with hτ
  -- the Fourier expansion, summed over the interval
  have hexp : ∑ i ∈ range ℓ, χ (a + (i : ZMod q)) =
      (q : ℂ)⁻¹ * τ * ∑ j : ZMod q, χ⁻¹ (-j) * ∑ i ∈ range ℓ, stdAddChar (j * (a + (i : ZMod q))) := by
    rw [Finset.sum_congr rfl fun (i : ℕ) _ => apply_eq_sum_gaussSum hχ (a + (i : ZMod q)), ← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => (Finset.mul_sum _ _ _).symm
  -- each term is at most `q/(2 min(v, q - v))`
  have hterm : ∀ j : ZMod q, ‖χ⁻¹ (-j) * ∑ i ∈ range ℓ, stdAddChar (j * (a + (i : ZMod q)))‖ ≤
      (q : ℝ) / (2 * ((min j.val (q - j.val) : ℕ) : ℝ)) := by
    intro j
    by_cases hj : j = 0
    · subst hj
      simp [DirichletCharacter.map_zero' _ hq]
    · rw [norm_mul]
      have h1 := DirichletCharacter.norm_le_one χ⁻¹ (-j)
      have h2 := norm_sum_stdAddChar_le hj a ℓ
      have h3 : 0 ≤ ‖∑ i ∈ range ℓ, stdAddChar (j * (a + (i : ZMod q)))‖ := norm_nonneg _
      nlinarith [norm_nonneg (χ⁻¹ (-j))]
  have hsum : ∑ j : ZMod q, (q : ℝ) / (2 * ((min j.val (q - j.val) : ℕ) : ℝ)) =
      ∑ v ∈ range q, (q : ℝ) / (2 * ((min v (q - v) : ℕ) : ℝ)) := by
    rw [sum_zmod_eq_sum_range]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [ZMod.val_cast_of_lt (mem_range.mp hv)]
  have hnorm : ‖(q : ℂ)⁻¹ * τ‖ = (q : ℝ)⁻¹ * Real.sqrt q := by
    rw [norm_mul, norm_inv, Complex.norm_natCast, hτ, norm_gaussSum hχ]
  rw [hexp, norm_mul, hnorm]
  calc (q : ℝ)⁻¹ * Real.sqrt q * ‖∑ j : ZMod q, χ⁻¹ (-j) * ∑ i ∈ range ℓ, stdAddChar (j * (a + (i : ZMod q)))‖
      ≤ (q : ℝ)⁻¹ * Real.sqrt q * ∑ j : ZMod q, (q : ℝ) / (2 * ((min j.val (q - j.val) : ℕ) : ℝ)) := by
        gcongr
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hterm j)
    _ ≤ (q : ℝ)⁻¹ * Real.sqrt q * (q * (harmonic (q / 2) : ℝ)) := by
        rw [hsum]
        gcongr
        exact sum_div_min_le
    _ = Real.sqrt q * (harmonic (q / 2) : ℝ) := by
        field_simp

/-- `H_{⌊q/2⌋} ≤ log q + 1/3` for `q ≥ 2`, from `H_n ≤ 1 + log n` and `1 - log 2 < 1/3`. -/
lemma harmonic_half_le {q : ℕ} (hq : 2 ≤ q) : (harmonic (q / 2) : ℝ) ≤ Real.log q + 1 / 3 := by
  have hH := harmonic_le_one_add_log (q / 2)
  have h1 : (1 : ℝ) ≤ (q / 2 : ℕ) := by exact_mod_cast (by omega : 1 ≤ q / 2)
  have h2 : ((q / 2 : ℕ) : ℝ) ≤ (q : ℝ) / 2 := Nat.cast_div_le
  have hlog : Real.log (q / 2 : ℕ) ≤ Real.log ((q : ℝ) / 2) := Real.log_le_log (by linarith) h2
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  rw [Real.log_div hq0.ne' (by norm_num)] at hlog
  have := Real.log_two_gt_d9
  linarith

end BoundariesOfClass.PolyaVinogradov

namespace BoundariesOfClass

open BoundariesOfClass.PolyaVinogradov

/-- **The Pólya–Vinogradov inequality, harmonic form.** For a primitive Dirichlet character `χ` of level `q > 1`, every
sum of `χ` over `N` consecutive integers starting at `M` has norm at most `√q H_{⌊q/2⌋}`. -/
theorem norm_sum_le_sqrt_mul_harmonic_of_isPrimitive {q : ℕ} [NeZero q] (hq : 1 < q) (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (M : ℤ) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, χ ((M + n : ℤ) : ZMod q)‖ ≤ Real.sqrt q * (harmonic (q / 2) : ℝ) := by
  have hcast : ∀ n : ℕ, (((M + n : ℤ)) : ZMod q) = (M : ZMod q) + (n : ZMod q) := fun n => by push_cast; rfl
  simp_rw [hcast]
  exact norm_sum_le_sqrt_mul_harmonic (by omega) hχ (M : ZMod q) N

/-- **The Pólya–Vinogradov inequality** (G. Pólya and I. M. Vinogradov, 1918), with an explicit constant. For a
primitive Dirichlet character `χ` of level `q > 1`, every sum of `χ` over `N` consecutive integers starting at `M` has
norm at most `√q (log q + 1/3)`. -/
theorem norm_sum_le_of_isPrimitive {q : ℕ} [NeZero q] (hq : 1 < q) (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (M : ℤ) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, χ ((M + n : ℤ) : ZMod q)‖ ≤ Real.sqrt q * (Real.log q + 1 / 3) :=
  (norm_sum_le_sqrt_mul_harmonic_of_isPrimitive hq χ hχ M N).trans
    (mul_le_mul_of_nonneg_left (harmonic_half_le hq) (Real.sqrt_nonneg _))

end BoundariesOfClass
