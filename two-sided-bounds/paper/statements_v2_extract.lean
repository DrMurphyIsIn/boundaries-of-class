theorem classNumber_lower (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hd : (2981 : ℝ) ≤ |(discr K : ℝ)|) :
    (1 / 3 : ℝ) * Real.sqrt |(discr K : ℝ)| / Real.log |(discr K : ℝ)| ≤ (classNumber K : ℝ) := by
  sorry

theorem classNumber_ge_rpow (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hd : (1000 : ℝ) ≤ |(discr K : ℝ)|) :
    |(discr K : ℝ)| ^ ((7 : ℝ) / 16) / 17 ≤ (classNumber K : ℝ) := by
  sorry

theorem norm_LFunction_one_le {q : ℕ} [NeZero q] (hq : 7 ≤ q) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ‖χ.LFunction 1‖ ≤ Real.log q + 7 / 6 := by
  sorry

theorem LFunction_one_eq_general (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    [NeZero (discr K).natAbs] (χ : DirichletCharacter ℂ (discr K).natAbs)
    (hχ : ∀ s : ℂ, 1 < s.re → dedekindZeta K s = riemannZeta s * χ.LFunction s) :
    χ.LFunction 1 =
      2 * Real.pi * classNumber K / (Units.torsionOrder K * Real.sqrt |(discr K : ℝ)|) := by
  sorry

theorem LFunction_one_eq (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hd : (5 : ℝ) ≤ |(discr K : ℝ)|)
    [NeZero (discr K).natAbs] (χ : DirichletCharacter ℂ (discr K).natAbs)
    (hχ : ∀ s : ℂ, 1 < s.re → dedekindZeta K s = riemannZeta s * χ.LFunction s) :
    χ.LFunction 1 = Real.pi * classNumber K / Real.sqrt |(discr K : ℝ)| := by
  sorry

theorem existsUnique_LFunction_factorisation (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    [NeZero (discr K).natAbs] :
    ∃! χ : DirichletCharacter ℂ (discr K).natAbs,
      ∀ s : ℂ, 1 < s.re → dedekindZeta K s = riemannZeta s * χ.LFunction s := by
  sorry

theorem classNumber_le_sharp (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hd : (5 : ℝ) ≤ |(discr K : ℝ)|) :
    (classNumber K : ℝ) ≤
      Real.sqrt |(discr K : ℝ)| * (Real.log |(discr K : ℝ)| + 7 / 6) / Real.pi := by
  sorry

theorem norm_sum_le_of_isPrimitive {q : ℕ} [NeZero q] (hq : 1 < q) (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (M : ℤ) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, χ ((M + n : ℤ) : ZMod q)‖ ≤ Real.sqrt q * (Real.log q + 1 / 3) := by
  sorry

theorem norm_LFunction_one_le_of_isPrimitive {q : ℕ} [NeZero q] (hq : 7 ≤ q) (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) :
    ‖χ.LFunction 1‖ ≤ Real.log q / 2 + Real.log (Real.log q + 1 / 3) + 5 / 3 := by
  sorry

theorem norm_LFunction_one_le_loglog {q : ℕ} [NeZero q] (hq : 7 ≤ q) (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) :
    ‖χ.LFunction 1‖ ≤ Real.log q / 2 + Real.log (Real.log q) + 2 := by
  sorry

theorem classNumber_le_half_log (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hd : (5 : ℝ) ≤ |(discr K : ℝ)|) :
    (classNumber K : ℝ) ≤ Real.sqrt |(discr K : ℝ)| *
      (Real.log |(discr K : ℝ)| / 2 + Real.log (Real.log |(discr K : ℝ)| + 1 / 3) + 5 / 3) / Real.pi := by
  sorry

theorem classNumber_le_loglog (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hd : (5 : ℝ) ≤ |(discr K : ℝ)|) :
    (classNumber K : ℝ) ≤ Real.sqrt |(discr K : ℝ)| *
      (Real.log |(discr K : ℝ)| / 2 + Real.log (Real.log |(discr K : ℝ)|) + 2) / Real.pi := by
  sorry

theorem isPrimitive_of_factorisation (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    [NeZero (discr K).natAbs] (χ : DirichletCharacter ℂ (discr K).natAbs)
    (hχ : ∀ s : ℂ, 1 < s.re → dedekindZeta K s = riemannZeta s * χ.LFunction s) :
    χ.IsPrimitive := by
  sorry

theorem abs_discr_le_of_classNumber_le (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (h : ℕ) (hh : 1 ≤ h) (hcl : classNumber K ≤ h) :
    |(discr K : ℝ)| ≤ max 2981
      (((6 : ℝ) * h * (Real.log ((6 : ℝ) * h) + Real.log (2 * Real.log ((6 : ℝ) * h)))) ^ 2) := by
  sorry

theorem abs_discr_le_of_classNumber_le' (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (h : ℕ) (hh : 1 ≤ h) (hcl : classNumber K ≤ h) :
    |(discr K : ℝ)| ≤ min (max 1000 (((17 : ℝ) * h) ^ ((16 : ℝ) / 7)))
      (max 2981
        (((6 : ℝ) * h * (Real.log ((6 : ℝ) * h) + Real.log (2 * Real.log ((6 : ℝ) * h)))) ^ 2)) := by
  sorry

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
