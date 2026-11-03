import BoundariesOfClass.ClassNumberFormula.LOne

/-!
# BoundariesOfClass.ClassNumberFormula.Residue: `L(1, χ)` is the residue of `ζ_K`

Pinned environment: Lean v4.34.1, Mathlib d13f23b. Mathlib only.

Let `K` be any number field and `χ` a Dirichlet character with `ζ_K(s) = ζ(s) L(s, χ)` on `Re s > 1`.

* `ne_one_of_factorisation`: then `χ ≠ 1`. Otherwise `(s-1)² ζ_K(s) = [(s-1)ζ(s)] [(s-1)L(s, 1)]` would tend to
  `∏_{p | N} (1 - 1/p) ≠ 0` as `s → 1⁺` (Mathlib's `LFunctionTrivChar_residue_one`), whereas it tends to `0` by the
  residue formula for `ζ_K`.
* `LFunction_one_eq_residue`: **`L(1, χ) = Res_{s=1} ζ_K(s)`**, Mathlib's `dedekindZeta_residue K`. Along real
  `s → 1⁺`, `(s-1)ζ_K(s) = [(s-1)ζ(s)] L(s, χ)`; the first factor tends to `1` (`riemannZeta_residue_one`) and the
  second to `L(1, χ)` (continuity), while the left side tends to the residue
  (`NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`, Mathlib's analytic class number formula for `ζ_K`).
-/

set_option autoImplicit false

namespace BoundariesOfClass.ClassNumberFormula

open NumberField Filter Topology

/-- Real `s → 1⁺` maps into the punctured neighbourhood of `1` in `ℂ`. -/
lemma tendsto_ofReal_nhdsGT_nhdsNE : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] 1) (𝓝[≠] (1 : ℂ)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, eventually_nhdsWithin_of_forall fun s hs => ?_⟩
  · exact (Complex.continuous_ofReal.tendsto' 1 1 Complex.ofReal_one).mono_left nhdsWithin_le_nhds
  · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact_mod_cast (Set.mem_Ioi.mp hs).ne'

/-- `(s - 1) ζ(s) → 1` as real `s → 1⁺`. -/
lemma tendsto_sub_one_mul_riemannZeta_nhdsGT :
    Tendsto (fun s : ℝ => ((s : ℂ) - 1) * riemannZeta s) (𝓝[>] 1) (𝓝 1) :=
  riemannZeta_residue_one.comp tendsto_ofReal_nhdsGT_nhdsNE

variable (K : Type*) [Field K] [NumberField K] {N : ℕ} [NeZero N]

/-- **A character that factors `ζ_K` is non-trivial.** -/
theorem ne_one_of_factorisation (χ : DirichletCharacter ℂ N)
    (hχ : ∀ s : ℂ, 1 < s.re → dedekindZeta K s = riemannZeta s * χ.LFunction s) : χ ≠ 1 := by
  rintro rfl
  have hlin : Tendsto (fun s : ℝ => (s : ℂ) - 1) (𝓝[>] 1) (𝓝 0) :=
    tendsto_sub_nhds_zero_iff.mpr (tendsto_nhdsWithin_iff.mp tendsto_ofReal_nhdsGT_nhdsNE).1
  -- by the residue formula, `(s-1)² ζ_K(s) → 0`
  have h0 : Tendsto (fun s : ℝ => ((s : ℂ) - 1) * (((s : ℂ) - 1) * dedekindZeta K s)) (𝓝[>] 1) (𝓝 0) := by
    have := hlin.mul (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K)
    rwa [zero_mul] at this
  -- by the factorisation with the trivial character, `(s-1)² ζ_K(s) → ∏_{p | N} (1 - 1/p)`
  have hT := (DirichletCharacter.LFunctionTrivChar_residue_one (N := N)).comp tendsto_ofReal_nhdsGT_nhdsNE
  have h1 : Tendsto (fun s : ℝ => ((s : ℂ) - 1) * (((s : ℂ) - 1) * dedekindZeta K s)) (𝓝[>] 1)
      (𝓝 (1 * ∏ p ∈ N.primeFactors, (1 - (p : ℂ)⁻¹))) := by
    refine (tendsto_sub_one_mul_riemannZeta_nhdsGT.mul hT).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : 1 < (s : ℂ).re := by simpa using Set.mem_Ioi.mp hs
    simp only [Function.comp_apply, hχ s hs', DirichletCharacter.LFunctionTrivChar]
    ring
  have h := tendsto_nhds_unique h0 h1
  rw [one_mul] at h
  refine (Finset.prod_ne_zero_iff.mpr fun p hp => ?_) h.symm
  rw [sub_ne_zero, ne_comm, ne_eq, inv_eq_one, Nat.cast_eq_one]
  exact (Nat.prime_of_mem_primeFactors hp).one_lt.ne'

/-- **`L(1, χ)` is the residue of `ζ_K` at `1`**, for any non-trivial `χ` with `ζ_K = ζ · L(·, χ)` on `Re s > 1`. -/
theorem LFunction_one_eq_residue (χ : DirichletCharacter ℂ N) (hχ1 : χ ≠ 1)
    (hχ : ∀ s : ℂ, 1 < s.re → dedekindZeta K s = riemannZeta s * χ.LFunction s) :
    χ.LFunction 1 = (dedekindZeta_residue K : ℂ) := by
  have h : Tendsto (fun s : ℝ => ((s : ℂ) - 1) * dedekindZeta K s) (𝓝[>] 1) (𝓝 (1 * χ.LFunction 1)) := by
    refine (tendsto_sub_one_mul_riemannZeta_nhdsGT.mul (tendsto_LFunction_nhdsGT χ hχ1)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : 1 < (s : ℂ).re := by simpa using Set.mem_Ioi.mp hs
    rw [hχ s hs']
    ring
  rw [one_mul] at h
  exact tendsto_nhds_unique h (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K)

end BoundariesOfClass.ClassNumberFormula
