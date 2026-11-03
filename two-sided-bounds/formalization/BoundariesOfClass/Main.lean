import BoundariesOfClass.Assembly.Version2
import BoundariesOfClass.ClassNumberFormula.Main
import BoundariesOfClass.PolyaVinogradov.ClassNumber
import BoundariesOfClass.PolyaVinogradov.HalfLog
import BoundariesOfClass.PolyaVinogradov.Main
import BoundariesOfClass.Primitivity.Field

/-!
# The solution's main module

This module states every theorem of `BoundariesOfClassChallenges.BoundaryV2` that is not already declared, under its
challenge name, by a solution module. It proves them from their `dOf m` forms through the bridge
`|disc K| = dOf m` (`abs_discr_eq_dOf`).

Ten of the 28 challenge names are declared, with the challenge statement, in the class number formula,
Pólya–Vinogradov and primitivity modules, which this module imports. The remaining eighteen are declared here:
- the two lower bounds;
- the existence and uniqueness of the factorisation (from the existence in ClassNumberFormula.Main and the uniqueness
  `Primitivity.eq_of_LFunction_eq`);
- the two cutoffs;
- the ten thresholds;
- the three lower thresholds.
-/

open NumberField CN1.Finite

namespace BoundariesOfClass

section Bridge

variable {K : Type*} [Field K] [NumberField K]

/-- `disc m = dOf m`: both are `if m % 4 = 3 then m else 4 m`. It is proved here by `rfl`, not taken from
`CN1.Finite.Bridge`, which the closure checks keep out of the lower-bound cone. -/
theorem disc_eq_dOf' (m : ℕ) : CN1.Foundations.disc m = dOf m := rfl

/-- **The bridge**: `|disc K| = dOf m` for `K = ℚ(√-m)`, `m` squarefree. -/
theorem abs_discr_eq_dOf (hK : Module.finrank ℚ K = 2) {m : ℕ} (hm : Squarefree m) {α : K}
    (hα : α ^ 2 = -(m : K)) : |(discr K : ℝ)| = (dOf m : ℝ) := by
  rw [← Int.cast_abs, ← Nat.cast_natAbs, ClassNumberFormula.natAbs_discr_eq hα hK hm, disc_eq_dOf']

/-- `dOf 1 = 4` and `dOf 3 = 3`: both small. -/
theorem dOf_le_four_of_eq_one_or_three {m : ℕ} (h : m = 1 ∨ m = 3) : (dOf m : ℝ) ≤ 4 := by
  rcases h with rfl | rfl <;> norm_num [dOf]

end Bridge

/-! ## The two lower bounds -/

theorem classNumber_lower (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hd : (2981 : ℝ) ≤ |(discr K : ℝ)|) :
    (1 / 3 : ℝ) * Real.sqrt |(discr K : ℝ)| / Real.log |(discr K : ℝ)| ≤ (classNumber K : ℝ) := by
  obtain ⟨α, hα⟩ := hsq
  rw [abs_discr_eq_dOf hK hm hα] at hd ⊢
  have h13 : m ≠ 1 ∧ m ≠ 3 := by
    refine ⟨fun h => ?_, fun h => ?_⟩ <;>
    · have := dOf_le_four_of_eq_one_or_three (by tauto : m = 1 ∨ m = 3); linarith
  exact Assembly.classNumber_ge_third hα hK hm h13.1 h13.2 hd

theorem classNumber_ge_rpow (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hd : (1000 : ℝ) ≤ |(discr K : ℝ)|) :
    |(discr K : ℝ)| ^ ((7 : ℝ) / 16) / 17 ≤ (classNumber K : ℝ) := by
  obtain ⟨α, hα⟩ := hsq
  rw [abs_discr_eq_dOf hK hm hα] at hd ⊢
  have h13 : m ≠ 1 ∧ m ≠ 3 := by
    refine ⟨fun h => ?_, fun h => ?_⟩ <;>
    · have := dOf_le_four_of_eq_one_or_three (by tauto : m = 1 ∨ m = 3); linarith
  exact Numerics.rpow_le_classNumber hα hK hm h13.1 h13.2 hd

/-! ## The factorisation is unique -/

theorem existsUnique_LFunction_factorisation (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    [NeZero (discr K).natAbs] :
    ∃! χ : DirichletCharacter ℂ (discr K).natAbs,
      ∀ s : ℂ, 1 < s.re → dedekindZeta K s = riemannZeta s * χ.LFunction s := by
  obtain ⟨χ, hχ⟩ := exists_LFunction_factorisation K hK m hm hsq
  refine ⟨χ, hχ, fun ψ hψ => Primitivity.eq_of_LFunction_eq fun s hs => ?_⟩
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  exact mul_left_cancel₀ hz ((hψ s hs).symm.trans (hχ s hs))

/-! ## The two cutoffs -/

theorem abs_discr_le_of_classNumber_le (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (h : ℕ) (hh : 1 ≤ h) (hcl : classNumber K ≤ h) :
    |(discr K : ℝ)| ≤ max 2981
      (((6 : ℝ) * h * (Real.log ((6 : ℝ) * h) + Real.log (2 * Real.log ((6 : ℝ) * h)))) ^ 2) := by
  obtain ⟨α, hα⟩ := hsq
  rw [abs_discr_eq_dOf hK hm hα]
  by_cases h13 : m = 1 ∨ m = 3
  · exact le_max_of_le_left (by have := dOf_le_four_of_eq_one_or_three h13; linarith)
  · obtain ⟨h1, h3⟩ := not_or.mp h13
    exact Assembly.dOf_le_cutoff_v2 hα hK hm h1 h3 h hh hcl

theorem abs_discr_le_of_classNumber_le' (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (h : ℕ) (hh : 1 ≤ h) (hcl : classNumber K ≤ h) :
    |(discr K : ℝ)| ≤ min (max 1000 (((17 : ℝ) * h) ^ ((16 : ℝ) / 7)))
      (max 2981
        (((6 : ℝ) * h * (Real.log ((6 : ℝ) * h) + Real.log (2 * Real.log ((6 : ℝ) * h)))) ^ 2)) := by
  obtain ⟨α, hα⟩ := hsq
  rw [abs_discr_eq_dOf hK hm hα]
  by_cases h13 : m = 1 ∨ m = 3
  · have := dOf_le_four_of_eq_one_or_three h13
    exact le_min (le_max_of_le_left (by linarith)) (le_max_of_le_left (by linarith))
  · obtain ⟨h1, h3⟩ := not_or.mp h13
    exact Assembly.dOf_le_cutoff_star hα hK hm h1 h3 h hh hcl

/-! ## The thresholds

Each is the contrapositive of its `dOf m` form `X ≤ dOf m → N < classNumber K`; `m ∈ {1, 3}` is below every `X`. -/

section Thresholds

variable {K : Type*} [Field K] [NumberField K]

/-- The common step. -/
theorem abs_discr_lt_of_threshold (hK : Module.finrank ℚ K = 2) {m : ℕ} (hm : Squarefree m)
    (hsq : ∃ α : K, α ^ 2 = -(m : K)) {N : ℕ} {X : ℝ} (hX : 4 < X)
    (hT : ∀ {α : K}, α ^ 2 = -(m : K) → m ≠ 1 → m ≠ 3 → X ≤ (dOf m : ℝ) → N < classNumber K)
    (hcl : classNumber K ≤ N) : |(discr K : ℝ)| < X := by
  obtain ⟨α, hα⟩ := hsq
  rw [abs_discr_eq_dOf hK hm hα]
  by_cases h13 : m = 1 ∨ m = 3
  · have := dOf_le_four_of_eq_one_or_three h13; linarith
  · obtain ⟨h1, h3⟩ := not_or.mp h13
    by_contra hlt
    exact absurd hcl (not_le.mpr (hT hα h1 h3 (not_lt.mp hlt)))

end Thresholds

theorem abs_discr_lt_of_classNumber_le_one (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hcl : classNumber K ≤ 1) : |(discr K : ℝ)| < 660 :=
  abs_discr_lt_of_threshold hK hm hsq (by norm_num)
    (fun hα h1 h3 hd => Numerics.lt_classNumber_of_le_dOf_le_one hα hK hm h1 h3 hd) hcl

theorem abs_discr_lt_of_classNumber_le_two (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hcl : classNumber K ≤ 2) : |(discr K : ℝ)| < 2210 :=
  abs_discr_lt_of_threshold hK hm hsq (by norm_num)
    (fun hα h1 h3 hd => Numerics.lt_classNumber_of_le_dOf_le_two hα hK hm h1 h3 hd) hcl

theorem abs_discr_lt_of_classNumber_le_three (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hcl : classNumber K ≤ 3) : |(discr K : ℝ)| < 4740 :=
  abs_discr_lt_of_threshold hK hm hsq (by norm_num)
    (fun hα h1 h3 hd => Numerics.lt_classNumber_of_le_dOf_le_three hα hK hm h1 h3 hd) hcl

theorem abs_discr_lt_of_classNumber_le_four (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hcl : classNumber K ≤ 4) : |(discr K : ℝ)| < 8310 :=
  abs_discr_lt_of_threshold hK hm hsq (by norm_num)
    (fun hα h1 h3 hd => Numerics.lt_classNumber_of_le_dOf_le_four hα hK hm h1 h3 hd) hcl

theorem abs_discr_lt_of_classNumber_le_five (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hcl : classNumber K ≤ 5) : |(discr K : ℝ)| < 13000 :=
  abs_discr_lt_of_threshold hK hm hsq (by norm_num)
    (fun hα h1 h3 hd => Numerics.lt_classNumber_of_le_dOf_le_five hα hK hm h1 h3 hd) hcl

theorem abs_discr_lt_of_classNumber_le_ten (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hcl : classNumber K ≤ 10) : |(discr K : ℝ)| < 54500 :=
  abs_discr_lt_of_threshold hK hm hsq (by norm_num)
    (fun hα h1 h3 hd => Numerics.lt_classNumber_of_le_dOf_le_ten hα hK hm h1 h3 hd) hcl

theorem abs_discr_lt_of_classNumber_le_hundred (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hcl : classNumber K ≤ 100) : |(discr K : ℝ)| < 8620000 :=
  abs_discr_lt_of_threshold hK hm hsq (by norm_num)
    (fun hα h1 h3 hd => Numerics.lt_classNumber_of_le_dOf_le_hundred hα hK hm h1 h3 hd) hcl

theorem abs_discr_lt_of_classNumber_le_thousand (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hcl : classNumber K ≤ 1000) : |(discr K : ℝ)| < 1605000000 :=
  abs_discr_lt_of_threshold hK hm hsq (by norm_num)
    (fun hα h1 h3 hd => Numerics.lt_classNumber_of_le_dOf_le_thousand hα hK hm h1 h3 hd) hcl

theorem abs_discr_lt_of_classNumber_le_two_thousand (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hcl : classNumber K ≤ 2000) : |(discr K : ℝ)| < 7800000000 :=
  abs_discr_lt_of_threshold hK hm hsq (by norm_num)
    (fun hα h1 h3 hd => Numerics.lt_classNumber_of_le_dOf_le_two_thousand hα hK hm h1 h3 hd) hcl

theorem abs_discr_lt_of_classNumber_le_five_thousand (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hcl : classNumber K ≤ 5000) : |(discr K : ℝ)| < 63200000000 :=
  abs_discr_lt_of_threshold hK hm hsq (by norm_num)
    (fun hα h1 h3 hd => Numerics.lt_classNumber_of_le_dOf_le_five_thousand hα hK hm h1 h3 hd) hcl

/-! ## The three lower thresholds -/

theorem classNumber_ge_of_two_e9_le (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hd : (2000000000 : ℝ) ≤ |(discr K : ℝ)|) : 1101 ≤ classNumber K := by
  obtain ⟨α, hα⟩ := hsq
  rw [abs_discr_eq_dOf hK hm hα] at hd
  have h13 : m ≠ 1 ∧ m ≠ 3 := by
    refine ⟨fun h => ?_, fun h => ?_⟩ <;>
    · have := dOf_le_four_of_eq_one_or_three (by tauto : m = 1 ∨ m = 3); linarith
  exact Numerics.lt_classNumber_of_le_dOf_two_e9 hα hK hm h13.1 h13.2 hd

theorem classNumber_ge_of_one_nine_eight_e10_le (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hd : (19800000000 : ℝ) ≤ |(discr K : ℝ)|) : 3007 ≤ classNumber K := by
  obtain ⟨α, hα⟩ := hsq
  rw [abs_discr_eq_dOf hK hm hα] at hd
  have h13 : m ≠ 1 ∧ m ≠ 3 := by
    refine ⟨fun h => ?_, fun h => ?_⟩ <;>
    · have := dOf_le_four_of_eq_one_or_three (by tauto : m = 1 ∨ m = 3); linarith
  exact Numerics.lt_classNumber_of_le_dOf_one_nine_eight_e10 hα hK hm h13.1 h13.2 hd

theorem classNumber_ge_of_two_pow_forty_le (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hd : (2 : ℝ) ^ 40 ≤ |(discr K : ℝ)|) : 17450 ≤ classNumber K := by
  obtain ⟨α, hα⟩ := hsq
  rw [abs_discr_eq_dOf hK hm hα] at hd
  have h40 : (2 : ℝ) ^ 40 = 1099511627776 := by norm_num
  have hd' : (1099511627776 : ℝ) ≤ (dOf m : ℝ) := h40 ▸ hd
  have h13 : m ≠ 1 ∧ m ≠ 3 := by
    refine ⟨fun h => ?_, fun h => ?_⟩ <;>
    · have := dOf_le_four_of_eq_one_or_three (by tauto : m = 1 ∨ m = 3); linarith
  exact Numerics.lt_classNumber_of_le_dOf_two_pow_forty hα hK hm h13.1 h13.2 hd'

end BoundariesOfClass
