import BoundariesOfClassNegControls.LowerTampers

/-!
# BoundariesOfClassNegControls.LowerTampersRest: the other six lower-bound tampers, and the `K_2983` witness

Pinned environment: Lean v4.34.1, Mathlib d13f23b. Never imported by the solution. As in `LowerTampers`, each tampered
statement is a `def` over fields in `Type` and is refuted at one field of the shared Fields module by an existing
kernel-checked classification theorem:

* `LprimeTamper` ((L′) with `1/3 → 1/2` and `d ≥ 2981 → d ≥ 163`): at `m = 163`, `h = 1` but
  `(1/2)√163/log 163 > 1` (COMPUTED 1.2532), from `√163 > 12.7` and `log 163 < 5.2` (`163⁵ < e^26`).
  `CN1.classNumber_eq_one_iff`.
* `UprimeTamper` ((U′) with `1/π → 1/200` and `d ≥ 5 → d ≥ 2981`): at `m = 2983`, `h ≥ 3` (2983 is not among the 27
  fields of class number at most two) but `√2983 (log 2983 + 7/6)/200 < 3` (COMPUTED 2.503), from `√2983 < 55` and
  `log 2983 < 8.1` (`2983¹⁰ < e^81`). `HCN.classNumber_le_two_iff`.
* `BprimeTamper` ((B′) with the bound replaced by `150 h²`): at `h = 1` and `m = 163`, `163 > 150`.
  `CN1.classNumber_eq_one_iff`.
* `T1Tamper` (`X_1 = 163`, i.e. `h ≤ 1 ⇒ d < 163`): at `m = 163`. `CN1.classNumber_eq_one_iff`.
* `T2Tamper` (`X_2 = 427`, i.e. `h ≤ 2 ⇒ d < 427`): at `m = 427`, `h = 2`. `HCN.classNumber_eq_two_iff`.
* `PointTamper` (a point value `d ≥ 427 ⇒ h ≥ 3`): at `m = 427`, `h = 2`. `HCN.classNumber_eq_two_iff`.

`witness_2983` is the non-vacuity witness for (L′) and (U′): `K_2983` meets their hypotheses (finrank 2, a square root
of `-2983`, `2983` squarefree, `d = 2983 ≥ 2981`). Its class number (20, COMPUTED) is not part of the witness.
-/

set_option autoImplicit false

open NumberField CN1.Finite

namespace BoundariesOfClassNegControls

lemma dOf_2983 : dOf 2983 = 2983 := by decide

lemma abs_discr_2983 : |(discr (KField 2983) : ℝ)| = 2983 := by
  rw [abs_discr_KField 2983 squarefree_2983, dOf_2983]; norm_num

lemma three_le_classNumber_2983 : 3 ≤ classNumber (KField 2983) := by
  have h := HCN.classNumber_le_two_iff (KField 2983) (finrank_KField 2983) 2983 squarefree_2983
    (exists_sq_eq_neg 2983)
  have hn : ¬ classNumber (KField 2983) ≤ 2 := by rw [h]; decide
  omega

/-- **The non-vacuity witness for (L′) and (U′).** -/
theorem witness_2983 : Module.finrank ℚ (KField 2983) = 2 ∧ Squarefree (2983 : ℕ) ∧
    (∃ α : KField 2983, α ^ 2 = -((2983 : ℕ) : KField 2983)) ∧ (2981 : ℝ) ≤ |(discr (KField 2983) : ℝ)| :=
  ⟨finrank_KField 2983, squarefree_2983, exists_sq_eq_neg 2983, by rw [abs_discr_2983]; norm_num⟩

/-- The tampered (L′). -/
def LprimeTamper : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (m : ℕ), Squarefree m →
    (∃ α : K, α ^ 2 = -(m : K)) → (163 : ℝ) ≤ |(discr K : ℝ)| →
    (1 / 2 : ℝ) * Real.sqrt |(discr K : ℝ)| / Real.log |(discr K : ℝ)| ≤ (classNumber K : ℝ)

/-- **The tampered (L′) is false**, at `m = 163`. -/
theorem not_LprimeTamper : ¬ LprimeTamper := by
  intro h
  have h1 := h (KField 163) (finrank_KField 163) 163 squarefree_163 (exists_sq_eq_neg 163)
    (by rw [abs_discr_163])
  rw [abs_discr_163, classNumber_163] at h1
  push_cast at h1
  have he := Real.exp_one_gt_d9
  have hl5 : Real.log ((163 : ℝ) ^ 5) < 26 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num), show (26 : ℝ) = ((26 : ℕ) : ℝ) by norm_num, ← Real.exp_one_pow]
    calc ((163 : ℝ) ^ 5) < (2.7182818283 : ℝ) ^ 26 := by norm_num
      _ ≤ Real.exp 1 ^ 26 := pow_le_pow_left₀ (by norm_num) he.le 26
  rw [Real.log_pow] at hl5
  push_cast at hl5
  have hl0 : 0 < Real.log (163 : ℝ) := Real.log_pos (by norm_num)
  have hs : (127 / 10 : ℝ) < Real.sqrt 163 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  rw [div_le_iff₀ hl0] at h1
  linarith

/-- The tampered (U′). -/
def UprimeTamper : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (m : ℕ), Squarefree m →
    (∃ α : K, α ^ 2 = -(m : K)) → (2981 : ℝ) ≤ |(discr K : ℝ)| →
    (classNumber K : ℝ) ≤ Real.sqrt |(discr K : ℝ)| * (Real.log |(discr K : ℝ)| + 7 / 6) / 200

/-- **The tampered (U′) is false**, at `m = 2983`. -/
theorem not_UprimeTamper : ¬ UprimeTamper := by
  intro h
  have h1 := h (KField 2983) (finrank_KField 2983) 2983 squarefree_2983 (exists_sq_eq_neg 2983)
    (by rw [abs_discr_2983]; norm_num)
  rw [abs_discr_2983] at h1
  have h3 : (3 : ℝ) ≤ classNumber (KField 2983) := by exact_mod_cast three_le_classNumber_2983
  have he := Real.exp_one_gt_d9
  have hl10 : Real.log ((2983 : ℝ) ^ 10) < 81 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num), show (81 : ℝ) = ((81 : ℕ) : ℝ) by norm_num, ← Real.exp_one_pow]
    calc ((2983 : ℝ) ^ 10) < (2.7182818283 : ℝ) ^ 81 := by norm_num
      _ ≤ Real.exp 1 ^ 81 := pow_le_pow_left₀ (by norm_num) he.le 81
  rw [Real.log_pow] at hl10
  push_cast at hl10
  have hl0 : 0 < Real.log (2983 : ℝ) := Real.log_pos (by norm_num)
  have hs : Real.sqrt 2983 < 55 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hs0 := Real.sqrt_nonneg (2983 : ℝ)
  have hb : Real.sqrt 2983 * (Real.log 2983 + 7 / 6) < 55 * (81 / 10 + 7 / 6) :=
    mul_lt_mul'' hs (by linarith) hs0 (by linarith)
  have : Real.sqrt 2983 * (Real.log 2983 + 7 / 6) / 200 < 3 := by
    rw [div_lt_iff₀ (by norm_num)]; linarith
  linarith

/-- The tampered (B′). -/
def BprimeTamper : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (m : ℕ), Squarefree m →
    (∃ α : K, α ^ 2 = -(m : K)) → ∀ (h : ℕ), 1 ≤ h → classNumber K ≤ h →
    |(discr K : ℝ)| ≤ 150 * (h : ℝ) ^ 2

/-- **The tampered (B′) is false**, at `h = 1` and `m = 163`. -/
theorem not_BprimeTamper : ¬ BprimeTamper := by
  intro h
  have h1 := h (KField 163) (finrank_KField 163) 163 squarefree_163 (exists_sq_eq_neg 163) 1 le_rfl
    (by rw [classNumber_163])
  rw [abs_discr_163] at h1
  norm_num at h1

/-- The tampered threshold `X_1 = 163`. -/
def T1Tamper : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (m : ℕ), Squarefree m →
    (∃ α : K, α ^ 2 = -(m : K)) → classNumber K ≤ 1 → |(discr K : ℝ)| < 163

/-- **The tampered threshold `X_1 = 163` is false**, at `m = 163`. -/
theorem not_T1Tamper : ¬ T1Tamper := by
  intro h
  have h1 := h (KField 163) (finrank_KField 163) 163 squarefree_163 (exists_sq_eq_neg 163)
    (by rw [classNumber_163])
  rw [abs_discr_163] at h1
  exact lt_irrefl _ h1

/-- The tampered threshold `X_2 = 427`. -/
def T2Tamper : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (m : ℕ), Squarefree m →
    (∃ α : K, α ^ 2 = -(m : K)) → classNumber K ≤ 2 → |(discr K : ℝ)| < 427

/-- **The tampered threshold `X_2 = 427` is false**, at `m = 427`. -/
theorem not_T2Tamper : ¬ T2Tamper := by
  intro h
  have h1 := h (KField 427) (finrank_KField 427) 427 squarefree_427 (exists_sq_eq_neg 427)
    (by rw [classNumber_427])
  rw [abs_discr_427] at h1
  exact lt_irrefl _ h1

/-- The tampered point value `d ≥ 427 ⇒ h ≥ 3`. -/
def PointTamper : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (m : ℕ), Squarefree m →
    (∃ α : K, α ^ 2 = -(m : K)) → (427 : ℝ) ≤ |(discr K : ℝ)| → 3 ≤ classNumber K

/-- **The tampered point value is false**, at `m = 427`. -/
theorem not_PointTamper : ¬ PointTamper := by
  intro h
  have h1 := h (KField 427) (finrank_KField 427) 427 squarefree_427 (exists_sq_eq_neg 427)
    (by rw [abs_discr_427])
  rw [classNumber_427] at h1
  omega

end BoundariesOfClassNegControls
