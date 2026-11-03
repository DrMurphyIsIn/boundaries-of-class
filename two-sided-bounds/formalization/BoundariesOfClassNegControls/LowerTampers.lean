import BoundariesOfClassNegControls.Fields
import CN1.Main
import HCN.Main
import HCN.Numerics.Threshold

/-!
# BoundariesOfClassNegControls.LowerTampers: field-level refutations of three tampered lower-bound statements

Pinned environment: Lean v4.34.1, Mathlib d13f23b. Never imported by the solution. Each tampered statement is the
challenge statement with its constants changed, stated as a `def` over fields in `Type` (the challenge's `Type*` form
implies it, so the negation refutes the tamper), and refuted at one real field `K_m = ℚ(√-m)` from the shared Fields
module, by an existing kernel-checked classification theorem:

* `PprimeTamper` ((P′) with `d ≥ 1000 → d ≥ 163` and `1/17 → 1/5`): at `m = 163`, `h = 1` but
  `163^{7/16}/5 > 1`, since `163⁷ > 5¹⁶` (COMPUTED value 1.857). `CN1.classNumber_eq_one_iff`.
* `BstarTamper` ((B*) with `max(1000, (17h)^{16/7}) → max(100, (5h)^{16/7})`): at `h = 1` and `m = 163`, the bound is at
  most `max(100, 5^{16/7}) = 100 < 163`, since `5¹⁶ ≤ 100⁷`. `CN1.classNumber_eq_one_iff`.
* `T4Tamper` ((T) with `X_4 = 427`, i.e. `h ≤ 4 ⇒ d < 427`): at `m = 427`, `h = 2`. `HCN.classNumber_eq_two_iff`.
-/

set_option autoImplicit false

open NumberField CN1.Finite

namespace BoundariesOfClassNegControls

lemma dOf_163 : dOf 163 = 163 := by decide

lemma dOf_427 : dOf 427 = 427 := by decide

lemma abs_discr_163 : |(discr (KField 163) : ℝ)| = 163 := by
  rw [abs_discr_KField 163 squarefree_163, dOf_163]; norm_num

lemma abs_discr_427 : |(discr (KField 427) : ℝ)| = 427 := by
  rw [abs_discr_KField 427 squarefree_427, dOf_427]; norm_num

lemma classNumber_163 : classNumber (KField 163) = 1 :=
  (CN1.classNumber_eq_one_iff (KField 163) (finrank_KField 163) 163 squarefree_163 (exists_sq_eq_neg 163)).2
    (by decide)

lemma classNumber_427 : classNumber (KField 427) = 2 :=
  (HCN.classNumber_eq_two_iff (KField 427) (finrank_KField 427) 427 squarefree_427 (exists_sq_eq_neg 427)).2
    (by decide)

/-- The tampered (P′). -/
def PprimeTamper : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (m : ℕ), Squarefree m →
    (∃ α : K, α ^ 2 = -(m : K)) → (163 : ℝ) ≤ |(discr K : ℝ)| →
    |(discr K : ℝ)| ^ ((7 : ℝ) / 16) / 5 ≤ (classNumber K : ℝ)

/-- **The tampered (P′) is false**, at `m = 163`. -/
theorem not_PprimeTamper : ¬ PprimeTamper := by
  intro h
  have h1 := h (KField 163) (finrank_KField 163) 163 squarefree_163 (exists_sq_eq_neg 163)
    (by rw [abs_discr_163])
  rw [abs_discr_163, classNumber_163] at h1
  push_cast at h1
  -- `163^{7/16} > 5`, from `163⁷ > 5¹⁶`
  have hpow : ((163 : ℝ) ^ ((7 : ℝ) / 16)) ^ 16 = (163 : ℝ) ^ 7 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  have h2 : (163 : ℝ) ^ ((7 : ℝ) / 16) ≤ 5 := by linarith
  have h3 := pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) _) h2 16
  rw [hpow] at h3
  norm_num at h3

/-- The tampered (B*). -/
def BstarTamper : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (m : ℕ), Squarefree m →
    (∃ α : K, α ^ 2 = -(m : K)) → ∀ (h : ℕ), 1 ≤ h → classNumber K ≤ h →
    |(discr K : ℝ)| ≤ min (max 100 (((5 : ℝ) * h) ^ ((16 : ℝ) / 7)))
      (max 2981 (((6 : ℝ) * h * (Real.log ((6 : ℝ) * h) + Real.log (2 * Real.log ((6 : ℝ) * h)))) ^ 2))

/-- **The tampered (B*) is false**, at `h = 1` and `m = 163`. -/
theorem not_BstarTamper : ¬ BstarTamper := by
  intro h
  have h1 := h (KField 163) (finrank_KField 163) 163 squarefree_163 (exists_sq_eq_neg 163) 1 le_rfl
    (by rw [classNumber_163])
  rw [abs_discr_163] at h1
  have h5 : ((5 : ℝ) * ((1 : ℕ) : ℝ)) ^ ((16 : ℝ) / 7) ≤ 100 := by
    rw [Nat.cast_one, mul_one]
    exact HCN.Numerics.rpow_le_of_pow_le (k := 16) (n := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  have h2 := h1.trans (min_le_left _ _)
  rw [max_eq_left h5] at h2
  norm_num at h2

/-- The tampered threshold `X_4 = 427`. -/
def T4Tamper : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (m : ℕ), Squarefree m →
    (∃ α : K, α ^ 2 = -(m : K)) → classNumber K ≤ 4 → |(discr K : ℝ)| < 427

/-- **The tampered threshold is false**, at `m = 427` (`h = 2`). -/
theorem not_T4Tamper : ¬ T4Tamper := by
  intro h
  have h1 := h (KField 427) (finrank_KField 427) 427 squarefree_427 (exists_sq_eq_neg 427)
    (by rw [classNumber_427]; norm_num)
  rw [abs_discr_427] at h1
  exact lt_irrefl _ h1

end BoundariesOfClassNegControls
