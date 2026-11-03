import CN1.Foundations.Discr

/-!
# BoundariesOfClass.ClassNumberFormula.Invariants: the invariants of `ℚ(√-m)` in the residue formula

Pinned environment: Lean v4.34.1, Mathlib d13f23b. Imports Mathlib and the Mathlib-only foundations of the CN-1
formalization (tenth-discriminant): the field model and the units (`CN1.Foundations.Basic`) and the discriminant
(`CN1.Foundations.Discr`).

For `K` of degree `2` containing `α` with `α² = -m`, `m ≥ 1`:

* `nrRealPlaces_eq_zero`: `K` has no real place (a real embedding would send `α²` to `-m < 0`).
* `nrComplexPlaces_eq_one`, `card_infinitePlace_eq_one`: so `K` has exactly one infinite place, and it is complex.
* `regulator_eq_one`: with one infinite place the unit rank is `0`, and the regulator (Mathlib's
  `NumberField.Units.regulator`) is the determinant of an empty matrix.
* `dedekindZeta_residue_eq`: Mathlib's residue `2^{r₁} (2π)^{r₂} R h / (w √|disc K|)` is `2π h / (w √|disc K|)`.
* `torsionOrder_eq_two`: `w = 2` for `m ∉ {1, 3}` (from CN-1's unit theorem: every unit is `±1`).
* `natAbs_discr_eq`, `abs_discr_eq`: `|disc K| = d`, CN-1's `disc m` (`m` if `m ≡ 3 (mod 4)`, else `4m`).
* `ne_one_and_ne_three_of_five_le`, `seven_le_disc`: `d ≥ 5` excludes `m = 1, 3` and forces `d ≥ 7`.
-/

set_option autoImplicit false

namespace BoundariesOfClass.ClassNumberFormula

open NumberField CN1.Foundations

variable {K : Type*} [Field K] [NumberField K]

/-- An imaginary quadratic field has no real place. -/
theorem nrRealPlaces_eq_zero {m : ℕ} {α : K} (hα : α ^ 2 = -(m : K)) (hm0 : m ≠ 0) :
    InfinitePlace.nrRealPlaces K = 0 := by
  rw [NumberField.nrRealPlaces_eq_zero_iff]
  refine ⟨fun w => ?_⟩
  rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
  intro h
  set φ := w.embedding
  have hc : (starRingEnd ℂ) (φ α) = φ α := by
    have := congrArg (fun f : K →+* ℂ => f α) h
    simpa [ComplexEmbedding.conjugate_coe_eq] using this
  obtain ⟨r, hr⟩ : ∃ r : ℝ, φ α = r := ⟨(φ α).re, (Complex.conj_eq_iff_re.mp hc).symm⟩
  have h2 : φ α ^ 2 = -(m : ℂ) := by rw [← map_pow, hα]; simp
  rw [hr] at h2
  have h3 : (r ^ 2 : ℝ) = -(m : ℝ) := by exact_mod_cast h2
  have : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm0
  nlinarith [sq_nonneg r]

/-- With no real place and degree `2`, there is exactly one complex place. -/
theorem nrComplexPlaces_eq_one (hK : Module.finrank ℚ K = 2) (h0 : InfinitePlace.nrRealPlaces K = 0) :
    InfinitePlace.nrComplexPlaces K = 1 := by
  have := InfinitePlace.card_add_two_mul_card_eq_rank K
  omega

/-- With no real place and degree `2`, there is exactly one infinite place. -/
theorem card_infinitePlace_eq_one (hK : Module.finrank ℚ K = 2) (h0 : InfinitePlace.nrRealPlaces K = 0) :
    Fintype.card (InfinitePlace K) = 1 := by
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, h0, nrComplexPlaces_eq_one hK h0]

/-- The regulator of a number field with exactly one infinite place is `1`. -/
theorem regulator_eq_one (h1 : Fintype.card (InfinitePlace K) = 1) : Units.regulator K = 1 := by
  classical
  obtain ⟨w'⟩ : Nonempty (InfinitePlace K) := inferInstance
  have hrank : Units.rank K = 0 := by rw [Units.rank, h1]
  have hE : IsEmpty {w : InfinitePlace K // w ≠ w'} := by
    have : Subsingleton (InfinitePlace K) := Fintype.card_le_one_iff_subsingleton.mp h1.le
    exact ⟨fun w => w.2 (Subsingleton.elim _ _)⟩
  rw [Units.regulator_eq_det K w' (Fintype.equivOfCardEq (by rw [Fintype.card_fin, hrank]; simp))]
  simp [Matrix.det_isEmpty]

/-- **The residue of `ζ_K` at `1`** (Mathlib's `dedekindZeta_residue`) for `K = ℚ(√-m)`: `2π h / (w √|disc K|)`. -/
theorem dedekindZeta_residue_eq {m : ℕ} {α : K} (hα : α ^ 2 = -(m : K)) (hK : Module.finrank ℚ K = 2)
    (hm0 : m ≠ 0) :
    dedekindZeta_residue K =
      2 * Real.pi * classNumber K / (Units.torsionOrder K * Real.sqrt |(discr K : ℝ)|) := by
  have h0 := nrRealPlaces_eq_zero hα hm0
  rw [dedekindZeta_residue_def, h0, nrComplexPlaces_eq_one hK h0,
    regulator_eq_one (card_infinitePlace_eq_one hK h0)]
  ring

/-- The torsion order is `2` when every unit is `±1`. -/
theorem torsionOrder_eq_two_of_units (h : ∀ ε : (𝓞 K)ˣ, (ε : 𝓞 K) = 1 ∨ (ε : 𝓞 K) = -1) :
    Units.torsionOrder K = 2 := by
  classical
  let := Fintype.ofFinite (Units.torsion K)
  rw [Units.torsionOrder, Nat.card_eq_fintype_card]
  refine (Finset.card_eq_two.2 ⟨1, ⟨-1, _root_.neg_one_mem_torsion⟩,
    by simp [← Subtype.coe_ne_coe], Finset.ext fun x ↦ ⟨fun _ ↦ ?_, fun _ ↦ Finset.mem_univ _⟩⟩)
  rw [Finset.mem_insert, Finset.mem_singleton, ← Subtype.val_inj, ← Subtype.val_inj]
  rcases h x with hx | hx
  · left; exact Units.ext hx
  · right; exact Units.ext (by rw [hx]; rfl)

/-- **`w = 2`** for `K = ℚ(√-m)`, `m ∉ {1, 3}`. -/
theorem torsionOrder_eq_two {m : ℕ} {α : K} (hα : α ^ 2 = -(m : K)) (hK : Module.finrank ℚ K = 2)
    (hm : Squarefree m) (hm1 : m ≠ 1) (hm3 : m ≠ 3) : Units.torsionOrder K = 2 :=
  torsionOrder_eq_two_of_units (coe_unit_eq_one_or_neg_one hα hK hm hm1 hm3)

/-- `|disc K| = d` as a natural number. -/
theorem natAbs_discr_eq {m : ℕ} {α : K} (hα : α ^ 2 = -(m : K)) (hK : Module.finrank ℚ K = 2)
    (hm : Squarefree m) : (discr K).natAbs = disc m := by
  rw [discr_eq hα hK hm]
  simp

/-- `|disc K| = d` as a real number. -/
theorem abs_discr_eq {m : ℕ} {α : K} (hα : α ^ 2 = -(m : K)) (hK : Module.finrank ℚ K = 2)
    (hm : Squarefree m) : |(discr K : ℝ)| = disc m := by
  rw [discr_eq hα hK hm]
  push_cast
  rw [abs_neg, Nat.abs_cast]

/-- `d ≥ 5` excludes `m = 1` (`d = 4`) and `m = 3` (`d = 3`). -/
theorem ne_one_and_ne_three_of_five_le {m : ℕ} (hd : 5 ≤ disc m) : m ≠ 1 ∧ m ≠ 3 := by
  constructor <;> rintro rfl <;> norm_num [disc] at hd

/-- `d ≥ 5` forces `d ≥ 7` (`d = m ≡ 3 (mod 4)` or `d = 4m`). -/
theorem seven_le_disc {m : ℕ} (hd : 5 ≤ disc m) : 7 ≤ disc m := by
  unfold disc at *
  split_ifs at * <;> omega

end BoundariesOfClass.ClassNumberFormula
