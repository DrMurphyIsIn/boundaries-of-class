import Mathlib
import CN1.ChowlaSelberg.GammaIntegral

/-!
# BoundariesOfClass.CS.BesselHalf: the `K_{1/2}` integral, exactly

Pinned environment: Lean v4.34.1, Mathlib d13f23b.

* `integral_exp_neg_sq_sub_div`: for `a, b > 0`, `∫₀^∞ e^{-(a w - b/w)²} dw = √π/(2a)` (Cauchy–Schlömilch). The map
  `φ(w) = a w - b/w` is a bijection `(0, ∞) → ℝ` with `φ' = a + b/w²`, so `∫₀^∞ e^{-φ²}(a + b/w²) dw = ∫_ℝ e^{-u²} = √π`;
  and `w ↦ (b/a)/w` maps `(0, ∞)` to itself with `φ ↦ -φ`, so `∫ e^{-φ²} · b/w² = ∫ e^{-φ²} · a`.
* `integral_rpow_neg_half_exp`: for `A, B > 0`, `∫₀^∞ t^{-1/2} e^{-(A t + B/t)} dt = √(π/A) e^{-2√(AB)}`
  (substitute `t = w²`; `A w² + B/w² = (√A w - √B/w)² + 2√(AB)`).
* `integral_rpow_kernF_le`: for `0 < ν ≤ 1/2`, `∫₀^∞ t^{ν-1} e^{-(A t + B/t)} dt ≤ (B/A)^{(ν-1/2)/2} √(π/A) e^{-2√(AB)}`:
  symmetrize under `t ↦ (B/A)/t` and use `x^ν + x^{-ν} ≤ x^{1/2} + x^{-1/2}`.
-/

set_option autoImplicit false

open MeasureTheory Set Real

namespace BoundariesOfClass.CS

/-- `φ(w) = a w - b/w` maps `(0, ∞)` onto `ℝ`. -/
lemma image_sub_div_Ioi {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (fun w : ℝ => a * w - b / w) '' Ioi 0 = univ := by
  refine eq_univ_of_forall fun u => ?_
  have hd : 0 ≤ u ^ 2 + 4 * a * b := by positivity
  have hs : |u| < Real.sqrt (u ^ 2 + 4 * a * b) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg u) (by nlinarith [mul_pos ha hb])
  have hw : 0 < (u + Real.sqrt (u ^ 2 + 4 * a * b)) / (2 * a) := by
    apply div_pos _ (by linarith)
    linarith [neg_abs_le u]
  refine ⟨_, hw, ?_⟩
  have hsq := Real.sq_sqrt hd
  set r := Real.sqrt (u ^ 2 + 4 * a * b)
  have hne : u + r ≠ 0 := by linarith [neg_abs_le u]
  field_simp
  nlinarith [hsq]

lemma hasDerivWithinAt_sub_div {a b w : ℝ} (hw : w ∈ Ioi (0 : ℝ)) :
    HasDerivWithinAt (fun w : ℝ => a * w - b / w) (a + b / w ^ 2) (Ioi 0) w := by
  have hw0 : w ≠ 0 := (mem_Ioi.mp hw).ne'
  have h : HasDerivAt (fun w : ℝ => a * w - b / w) (a + b / w ^ 2) w := by
    have h0 := ((hasDerivAt_id w).const_mul a).sub ((hasDerivAt_inv hw0).const_mul b)
    convert h0 using 1
    · funext x; simp [div_eq_mul_inv]
    · field_simp; ring
  exact h.hasDerivWithinAt

lemma injOn_sub_div {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    InjOn (fun w : ℝ => a * w - b / w) (Ioi 0) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := hx
  have hy0 : 0 < y := hy
  simp only at hxy
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have : a * x - b / x < a * y - b / y := by
      have h1 : b / y < b / x := div_lt_div_of_pos_left hb hx0 h
      nlinarith
    linarith
  · have : a * y - b / y < a * x - b / x := by
      have h1 : b / x < b / y := div_lt_div_of_pos_left hb hy0 h
      nlinarith
    linarith

/-- `ψ(w) = c/w` maps `(0, ∞)` onto itself. -/
lemma image_div_Ioi {c : ℝ} (hc : 0 < c) : (fun w : ℝ => c / w) '' Ioi 0 = Ioi 0 := by
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩; exact div_pos hc hw
  · intro hx; exact ⟨c / x, div_pos hc hx, by field_simp⟩

lemma hasDerivWithinAt_div {c w : ℝ} (hw : w ∈ Ioi (0 : ℝ)) :
    HasDerivWithinAt (fun w : ℝ => c / w) (-(c / w ^ 2)) (Ioi 0) w := by
  have hw0 : w ≠ 0 := (mem_Ioi.mp hw).ne'
  have h : HasDerivAt (fun w : ℝ => c / w) (-(c / w ^ 2)) w := by
    have h0 := (hasDerivAt_inv hw0).const_mul c
    convert h0 using 1
    · funext x; simp [div_eq_mul_inv]
    · ring
  exact h.hasDerivWithinAt

lemma injOn_div {c : ℝ} (hc : 0 < c) : InjOn (fun w : ℝ => c / w) (Ioi 0) := by
  intro x hx y hy hxy
  simp only at hxy
  have hx0 : (x : ℝ) ≠ 0 := (mem_Ioi.mp hx).ne'
  have hy0 : (y : ℝ) ≠ 0 := (mem_Ioi.mp hy).ne'
  field_simp at hxy
  nlinarith [hxy, hc]

/-- **Cauchy–Schlömilch:** `∫₀^∞ e^{-(a w - b/w)²} dw = √π/(2a)`, and the integrand is integrable. -/
theorem integral_exp_neg_sq_sub_div {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun w : ℝ => Real.exp (-(a * w - b / w) ^ 2)) (Ioi 0) ∧
      ∫ w in Ioi 0, Real.exp (-(a * w - b / w) ^ 2) = Real.sqrt π / (2 * a) := by
  set φ : ℝ → ℝ := fun w => a * w - b / w with hφ
  set g : ℝ → ℝ := fun u => Real.exp (-u ^ 2) with hg
  have hgi : Integrable g := by
    have := integrable_exp_neg_mul_sq (b := 1) one_pos
    simpa [hg] using this
  have hgint : ∫ u, g u = Real.sqrt π := by
    have := integral_gaussian 1
    simpa [hg] using this
  -- the image formula for `φ`
  have hdφ : ∀ w ∈ Ioi (0 : ℝ), HasDerivWithinAt φ (a + b / w ^ 2) (Ioi 0) w := fun w hw =>
    hasDerivWithinAt_sub_div hw
  have hinj := injOn_sub_div ha hb
  have himg := image_sub_div_Ioi ha hb
  have hI1 := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hdφ hinj g
  have hI1i := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hdφ hinj g).mp
  rw [show (fun w : ℝ => a * w - b / w) = φ from rfl] at himg
  rw [himg, Measure.restrict_univ, hgint] at hI1
  have hint1 : IntegrableOn (fun w => |a + b / w ^ 2| • g (φ w)) (Ioi 0) := by
    apply hI1i; rw [himg]; exact hgi.integrableOn
  have habs : ∀ w ∈ Ioi (0 : ℝ), |a + b / w ^ 2| = a + b / w ^ 2 := fun w hw =>
    abs_of_pos (by have := mem_Ioi.mp hw; positivity)
  -- integrability of the two pieces
  have hgφ0 : ∀ w, 0 ≤ g (φ w) := fun w => (Real.exp_pos _).le
  have hint_a : IntegrableOn (fun w => a * g (φ w)) (Ioi 0) := by
    refine hint1.mono' (Measurable.aestronglyMeasurable (by simp only [hg, hφ]; fun_prop)) ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ha.le (hgφ0 w)), smul_eq_mul, habs w hw]
      have : 0 ≤ b / w ^ 2 := by have := mem_Ioi.mp hw; positivity
      nlinarith [hgφ0 w]
  have hint_b : IntegrableOn (fun w => b / w ^ 2 * g (φ w)) (Ioi 0) := by
    refine (hint1.sub hint_a).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
    simp only [Pi.sub_apply, smul_eq_mul, habs w hw]; ring
  -- the symmetry `w ↦ (b/a)/w`
  set c := b / a with hc
  have hc0 : 0 < c := div_pos hb ha
  have hdψ : ∀ w ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun w : ℝ => c / w) (-(c / w ^ 2)) (Ioi 0) w := fun w hw =>
    hasDerivWithinAt_div hw
  have hI2 := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hdψ (injOn_div hc0)
    (fun x => a * g (φ x))
  rw [image_div_Ioi hc0] at hI2
  have hsym : ∀ w ∈ Ioi (0 : ℝ), |-(c / w ^ 2)| • (a * g (φ (c / w))) = b / w ^ 2 * g (φ w) := by
    intro w hw
    have hw0 : 0 < w := hw
    rw [abs_neg, abs_of_pos (by positivity), smul_eq_mul]
    have hφs : φ (c / w) = -φ w := by
      simp only [hφ, hc]; field_simp; ring
    rw [hφs, show g (-φ w) = g (φ w) by simp [hg]]
    rw [hc]; field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hsym] at hI2
  -- assemble: `√π = ∫ (a + b/w²) g(φ) = 2 a ∫ g(φ)`
  have hsplit : ∫ w in Ioi 0, |a + b / w ^ 2| • g (φ w) =
      (∫ w in Ioi 0, a * g (φ w)) + ∫ w in Ioi 0, b / w ^ 2 * g (φ w) := by
    rw [← integral_add hint_a hint_b]
    refine setIntegral_congr_fun measurableSet_Ioi fun w hw => ?_
    simp only [smul_eq_mul, habs w hw]; ring
  rw [hsplit, ← hI2, integral_const_mul] at hI1
  have hint_g : IntegrableOn (fun w => g (φ w)) (Ioi 0) := by
    have h1 : IntegrableOn (fun w => a⁻¹ * (a * g (φ w))) (Ioi 0) := Integrable.const_mul hint_a a⁻¹
    refine IntegrableOn.congr_fun h1 (fun w _ => ?_) measurableSet_Ioi
    field_simp
  refine ⟨hint_g, ?_⟩
  have : ∫ w in Ioi 0, g (φ w) = Real.sqrt π / (2 * a) := by
    rw [eq_div_iff (by positivity)]; linarith
  simpa [hg, hφ] using this

/-- **The `K_{1/2}` integral:** for `A, B > 0`, `∫₀^∞ t^{-1/2} e^{-(A t + B/t)} dt = √(π/A) e^{-2√(AB)}`. -/
theorem integral_rpow_neg_half_exp {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    ∫ t in Ioi 0, t ^ (-(1 / 2 : ℝ)) * Real.exp (-(A * t + B / t)) =
      Real.sqrt (π / A) * Real.exp (-(2 * Real.sqrt (A * B))) := by
  have hsA := Real.sqrt_pos.mpr hA
  have hsB := Real.sqrt_pos.mpr hB
  obtain ⟨-, hgauss⟩ := integral_exp_neg_sq_sub_div hsA hsB
  -- substitute `t = w²`
  have hsub := integral_comp_rpow_Ioi (fun t : ℝ => t ^ (-(1 / 2 : ℝ)) * Real.exp (-(A * t + B / t)))
    (p := 2) (by norm_num)
  rw [← hsub]
  have hpt : ∀ w ∈ Ioi (0 : ℝ), (|(2 : ℝ)| * w ^ ((2 : ℝ) - 1)) •
      ((w ^ (2 : ℝ)) ^ (-(1 / 2 : ℝ)) * Real.exp (-(A * w ^ (2 : ℝ) + B / w ^ (2 : ℝ)))) =
      2 * Real.exp (-(2 * Real.sqrt (A * B))) * Real.exp (-(Real.sqrt A * w - Real.sqrt B / w) ^ 2) := by
    intro w hw
    have hw0 : 0 < w := hw
    rw [smul_eq_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one,
      ← Real.rpow_mul hw0.le, show (2 : ℝ) * (-(1 / 2)) = -1 by norm_num, Real.rpow_neg_one,
      Real.rpow_two]
    have hsAB : Real.sqrt (A * B) = Real.sqrt A * Real.sqrt B := Real.sqrt_mul hA.le B
    have e : -(A * w ^ 2 + B / w ^ 2) = -(2 * Real.sqrt (A * B)) + -(Real.sqrt A * w - Real.sqrt B / w) ^ 2 := by
      rw [hsAB]
      have h1 := Real.sq_sqrt hA.le
      have h2 := Real.sq_sqrt hB.le
      have key : (Real.sqrt A * w - Real.sqrt B / w) ^ 2 =
          Real.sqrt A ^ 2 * w ^ 2 - 2 * (Real.sqrt A * Real.sqrt B) + Real.sqrt B ^ 2 / w ^ 2 := by
        field_simp; ring
      rw [h1, h2] at key
      linarith [key]
    rw [e, Real.exp_add]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul, hgauss]
  rw [Real.sqrt_div' π hA.le]
  field_simp

/-! ### The `K_ν` bound for `0 < ν ≤ 1/2` -/

/-- `x^ν + x^{-ν} ≤ x^{1/2} + x^{-1/2}` for `x > 0`, `0 ≤ ν ≤ 1/2` (`cosh(ν y) ≤ cosh(y/2)`). -/
lemma rpow_add_rpow_neg_le {x ν : ℝ} (hx : 0 < x) (hν0 : 0 ≤ ν) (hν : ν ≤ 1 / 2) :
    x ^ ν + x ^ (-ν) ≤ x ^ (1 / 2 : ℝ) + x ^ (-(1 / 2 : ℝ)) := by
  have e : ∀ r : ℝ, x ^ r + x ^ (-r) = 2 * Real.cosh (r * Real.log x) := by
    intro r
    rw [Real.cosh_eq, Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hx]
    ring_nf
  rw [e, e]
  have : Real.cosh (ν * Real.log x) ≤ Real.cosh (1 / 2 * Real.log x) := by
    rw [Real.cosh_le_cosh, abs_mul, abs_mul, abs_of_nonneg hν0, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    exact mul_le_mul_of_nonneg_right hν (abs_nonneg _)
  linarith

/-- The kernel `F(t) = e^{-(A t + B/t)}`. -/
noncomputable def kernF (A B t : ℝ) : ℝ := Real.exp (-(A * t + B / t))

lemma kernF_symm {A B t : ℝ} (hA : 0 < A) (hB : 0 < B) (ht : 0 < t) : kernF A B (B / A / t) = kernF A B t := by
  unfold kernF
  congr 2
  field_simp
  ring

/-- **The symmetry `t ↦ (B/A)/t`:** if `t^{p-1} F` is integrable on `(0, ∞)`, so is `t^{-p-1} F`, and
`∫ t^{p-1} F = (B/A)^p ∫ t^{-p-1} F`. -/
theorem integral_rpow_kernF_symm {A B p : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hint : IntegrableOn (fun t => t ^ (p - 1) * kernF A B t) (Ioi 0)) :
    IntegrableOn (fun t => t ^ (-p - 1) * kernF A B t) (Ioi 0) ∧
      ∫ t in Ioi 0, t ^ (p - 1) * kernF A B t = (B / A) ^ p * ∫ t in Ioi 0, t ^ (-p - 1) * kernF A B t := by
  set c := B / A with hc
  have hc0 : 0 < c := div_pos hB hA
  have hdψ : ∀ w ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun w : ℝ => c / w) (-(c / w ^ 2)) (Ioi 0) w := fun w hw =>
    hasDerivWithinAt_div hw
  set g : ℝ → ℝ := fun t => t ^ (p - 1) * kernF A B t with hg
  have hI := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hdψ (injOn_div hc0) g
  have hIi := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hdψ (injOn_div hc0) g).mp
  rw [image_div_Ioi hc0] at hI hIi
  have hpt : ∀ w ∈ Ioi (0 : ℝ), |-(c / w ^ 2)| • g (c / w) = c ^ p * (w ^ (-p - 1) * kernF A B w) := by
    intro w hw
    have hw0 : 0 < w := hw
    rw [abs_neg, abs_of_pos (by positivity), smul_eq_mul, hg]
    simp only
    rw [hc, kernF_symm hA hB hw0, Real.div_rpow hc0.le hw0.le, ← hc]
    have h1 : w ^ (-p - 1) = (w ^ (p - 1))⁻¹ * (w ^ 2)⁻¹ := by
      rw [← Real.rpow_neg hw0.le, ← Real.rpow_natCast, ← Real.rpow_neg hw0.le, ← Real.rpow_add hw0]
      congr 1; push_cast; ring
    have h2 : c ^ (p - 1) = c ^ p * c⁻¹ := by
      rw [Real.rpow_sub hc0, Real.rpow_one, div_eq_mul_inv]
    rw [h1, h2]
    have : 0 < w ^ (p - 1) := Real.rpow_pos_of_pos hw0 _
    field_simp
  have hint2 : IntegrableOn (fun w => c ^ p * (w ^ (-p - 1) * kernF A B w)) (Ioi 0) :=
    (hIi hint).congr_fun (fun w hw => hpt w hw) measurableSet_Ioi
  have hcp : 0 < c ^ p := Real.rpow_pos_of_pos hc0 _
  refine ⟨?_, ?_⟩
  · have := hint2.const_mul (c ^ p)⁻¹
    refine IntegrableOn.congr_fun this (fun w _ => ?_) measurableSet_Ioi
    field_simp
  · rw [hI, setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul]

lemma integrableOn_rpow_kernF {A B ν : ℝ} (hA : 0 < A) (hB : 0 ≤ B) (hν : 0 < ν) :
    IntegrableOn (fun t => t ^ (ν - 1) * kernF A B t) (Ioi 0) := by
  have h := CN1.CS.integrableOn_rpow_mul_exp (σ := ν) hν hA
  refine h.mono' ?_ ?_
  · refine (ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi)
    refine ContinuousOn.mul (fun t ht => (Real.continuousAt_rpow_const _ _ (Or.inl (mem_Ioi.mp ht).ne')).continuousWithinAt) ?_
    unfold kernF
    refine Real.continuous_exp.comp_continuousOn ?_
    refine ContinuousOn.neg (ContinuousOn.add (by fun_prop) ?_)
    exact continuousOn_const.div continuousOn_id (fun t ht => ne_of_gt ht)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    unfold kernF
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg ht0.le _)
    apply Real.exp_le_exp.mpr
    have : 0 ≤ B / t := div_nonneg hB ht0.le
    linarith

/-- **The `K_ν` bound, `0 < ν ≤ 1/2`:** `∫₀^∞ t^{ν-1} e^{-(A t + B/t)} dt ≤ (√(B/A))^{ν-1/2} √(π/A) e^{-2√(AB)}`. -/
theorem integral_rpow_kernF_le {A B ν : ℝ} (hA : 0 < A) (hB : 0 < B) (hν0 : 0 < ν) (hν : ν ≤ 1 / 2) :
    ∫ t in Ioi 0, t ^ (ν - 1) * kernF A B t ≤
      Real.sqrt (B / A) ^ (ν - 1 / 2) * (Real.sqrt (π / A) * Real.exp (-(2 * Real.sqrt (A * B)))) := by
  set l := Real.sqrt (B / A) with hl
  have hl0 : 0 < l := Real.sqrt_pos.mpr (div_pos hB hA)
  have hl2 : l ^ (2 : ℝ) = B / A := by rw [Real.rpow_two, hl, Real.sq_sqrt (div_pos hB hA).le]
  have hJν := integrableOn_rpow_kernF hA hB.le hν0
  obtain ⟨hJmν, hsymν⟩ := integral_rpow_kernF_symm hA hB hJν
  have hJh := integrableOn_rpow_kernF (ν := 1 / 2) hA hB.le (by norm_num)
  obtain ⟨hJmh, hsymh⟩ := integral_rpow_kernF_symm hA hB hJh
  have hhalf : ∫ t in Ioi 0, t ^ ((1 / 2 : ℝ) - 1) * kernF A B t =
      Real.sqrt (π / A) * Real.exp (-(2 * Real.sqrt (A * B))) := by
    rw [show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num]
    exact integral_rpow_neg_half_exp hA hB
  -- `(B/A)^ν = l^{2ν}`, `(B/A)^{1/2} = l`
  have hBAν : (B / A) ^ ν = l ^ (2 * ν) := by rw [← hl2, ← Real.rpow_mul hl0.le]
  have hBAh : (B / A) ^ (1 / 2 : ℝ) = l := by rw [hl, Real.sqrt_eq_rpow]
  -- pointwise: `t^{ν-1} + l^{2ν} t^{-ν-1} ≤ l^{ν-1/2} (t^{-1/2} + l t^{-3/2})`
  have hpt : ∀ t ∈ Ioi (0 : ℝ), t ^ (ν - 1) * kernF A B t + l ^ (2 * ν) * (t ^ (-ν - 1) * kernF A B t) ≤
      l ^ (ν - 1 / 2) * (t ^ ((1 / 2 : ℝ) - 1) * kernF A B t + l * (t ^ (-(1 / 2 : ℝ) - 1) * kernF A B t)) := by
    intro t ht
    have ht0 : 0 < t := ht
    have hF : 0 ≤ kernF A B t := (Real.exp_pos _).le
    have hx : 0 < t / l := div_pos ht0 hl0
    have hc := rpow_add_rpow_neg_le hx hν0.le hν
    -- multiply by `l^ν t^{-1} F`
    have hk : 0 ≤ l ^ ν * t⁻¹ * kernF A B t := by positivity
    have := mul_le_mul_of_nonneg_left hc hk
    set a := t ^ ν with ha
    set b := l ^ ν with hb
    set r := t ^ (1 / 2 : ℝ) with hr
    set q := l ^ (1 / 2 : ℝ) with hq
    have ha0 : 0 < a := Real.rpow_pos_of_pos ht0 _
    have hb0 : 0 < b := Real.rpow_pos_of_pos hl0 _
    have hr0 : 0 < r := Real.rpow_pos_of_pos ht0 _
    have hq0 : 0 < q := Real.rpow_pos_of_pos hl0 _
    have f1 : t ^ (ν - 1) = a / t := Real.rpow_sub_one ht0.ne' ν
    have f2 : t ^ (-ν - 1) = a⁻¹ / t := by rw [Real.rpow_sub_one ht0.ne', Real.rpow_neg ht0.le]
    have f3 : l ^ (2 * ν) = b ^ 2 := by
      rw [hb, ← Real.rpow_natCast, ← Real.rpow_mul hl0.le]; congr 1; push_cast; ring
    have f4 : (t / l) ^ ν = a / b := Real.div_rpow ht0.le hl0.le ν
    have f5 : (t / l) ^ (-ν) = (a / b)⁻¹ := by rw [Real.rpow_neg hx.le, f4]
    have f6 : t ^ ((1 / 2 : ℝ) - 1) = r / t := Real.rpow_sub_one ht0.ne' _
    have f7 : t ^ (-(1 / 2 : ℝ) - 1) = r⁻¹ / t := by rw [Real.rpow_sub_one ht0.ne', Real.rpow_neg ht0.le]
    have f8 : l ^ (ν - 1 / 2) = b / q := Real.rpow_sub hl0 _ _
    have f9 : (t / l) ^ (1 / 2 : ℝ) = r / q := Real.div_rpow ht0.le hl0.le _
    have f10 : (t / l) ^ (-(1 / 2 : ℝ)) = (r / q)⁻¹ := by rw [Real.rpow_neg hx.le, f9]
    have f11 : l = q ^ 2 := by
      rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul hl0.le]; norm_num
    have e1 : l ^ ν * t⁻¹ * kernF A B t * ((t / l) ^ ν + (t / l) ^ (-ν)) =
        t ^ (ν - 1) * kernF A B t + l ^ (2 * ν) * (t ^ (-ν - 1) * kernF A B t) := by
      rw [f1, f2, f3, f4, f5, ← hb]
      field_simp
    have e2 : l ^ ν * t⁻¹ * kernF A B t * ((t / l) ^ (1 / 2 : ℝ) + (t / l) ^ (-(1 / 2 : ℝ))) =
        l ^ (ν - 1 / 2) * (t ^ ((1 / 2 : ℝ) - 1) * kernF A B t + l * (t ^ (-(1 / 2 : ℝ) - 1) * kernF A B t)) := by
      rw [f6, f7, f8, f9, f10, ← hb]
      conv_rhs => rw [f11]
      field_simp
    rw [e1, e2] at this
    exact this
  have hintL : IntegrableOn (fun t => t ^ (ν - 1) * kernF A B t + l ^ (2 * ν) * (t ^ (-ν - 1) * kernF A B t))
      (Ioi 0) := hJν.add (hJmν.const_mul _)
  have hintR : IntegrableOn (fun t => l ^ (ν - 1 / 2) * (t ^ ((1 / 2 : ℝ) - 1) * kernF A B t +
      l * (t ^ (-(1 / 2 : ℝ) - 1) * kernF A B t))) (Ioi 0) := (hJh.add (hJmh.const_mul _)).const_mul _
  have hmono := setIntegral_mono_on hintL hintR measurableSet_Ioi hpt
  rw [integral_add hJν (hJmν.const_mul _), integral_const_mul, integral_const_mul,
    integral_add hJh (hJmh.const_mul _), integral_const_mul] at hmono
  -- `l^{2ν} J(-ν) = J(ν)` and `l J(-1/2) = J(1/2)`
  rw [hBAν] at hsymν
  rw [hBAh] at hsymh
  rw [← hsymν, ← hsymh, hhalf] at hmono
  linarith

end BoundariesOfClass.CS
