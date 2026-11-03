import Mathlib

/-!
# BoundariesOfClass.Analytic.Floor: the exact minimum of one class's main term over its leading coefficient

Pinned environment: Lean v4.34.1, Mathlib d13f23b. Pure real analysis. At `σ = 1 - δ` the Chowla–Selberg main term of a
class with leading coefficient `a ≥ 1` is `g(a) = a^{-σ} Z - K a^{-δ}` (with `Z = ζ(2σ) > 0`, `K = C₁ |ζ(2σ - 1)| ≥ 0`).
Put `p = σ/δ > 1` and `u = a^{-δ}`, so `a^{-σ} = u^p`. The function `Z u^p - K u` has its minimum over `u > 0` at
`u* = (δK/(σZ))^{δ/(1-2δ)}`, where `Z u*^{p-1} = K/p`, and by Bernoulli's inequality `x^p ≥ 1 + p(x - 1)`
(Mathlib's `one_add_mul_self_le_rpow_one_add`) applied to `x = u/u*`:

* `rpow_neg_mul_kappa_mono`: `a ↦ a^{-δ} κ(C/a)` is increasing while `C/a ≥ δ` (the remainder's worst class is at
  the largest leading coefficient), generalizing HCN's `bg_core_mono`.
* `floor_le`: `-(1 - δ/σ) K u* ≤ a^{-σ} Z - K a^{-δ}` for every `a > 0`.

So every class is charged at least `-(1 - δ/σ) K u*`, which scales like `d^{-σ/2}`, instead of the principal form's
`-K ~ d^{1/2-σ}`.
-/

set_option autoImplicit false

namespace BoundariesOfClass.Analytic

/-- **The per-class floor.** For `1/2 < σ < 1`, `δ = 1 - σ`, `Z > 0`, `K ≥ 0`, `a > 0`:
`-(1 - δ/σ) K u* ≤ a^{-σ} Z - K a^{-δ}`, with `u* = (δK/(σZ))^{δ/(1-2δ)}`. -/
theorem floor_le {σ Z K a : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ < 1) (hZ : 0 < Z) (hK : 0 ≤ K) (ha : 0 < a) :
    -((1 - (1 - σ) / σ) * K * ((1 - σ) * K / (σ * Z)) ^ ((1 - σ) / (1 - 2 * (1 - σ)))) ≤
      a ^ (-σ) * Z - K * a ^ (-(1 - σ)) := by
  set δ : ℝ := 1 - σ with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hσ0 : 0 < σ := by linarith
  have h12 : 0 < 1 - 2 * δ := by rw [hδ]; linarith
  set p : ℝ := σ / δ with hp
  have hp1 : 1 < p := by rw [hp, lt_div_iff₀ hδ0]; linarith
  set u : ℝ := a ^ (-δ) with hu
  have hu0 : 0 < u := Real.rpow_pos_of_pos ha _
  have hup : u ^ p = a ^ (-σ) := by
    rw [hu, ← Real.rpow_mul ha.le, hp]; congr 1; field_simp
  rcases eq_or_lt_of_le hK with hK0 | hKpos
  · -- `K = 0`: the floor is `0` and `g(a) = a^{-σ} Z ≥ 0`
    rw [← hK0]
    have : 0 ≤ a ^ (-σ) * Z := mul_nonneg (Real.rpow_nonneg ha.le _) hZ.le
    simp only [mul_zero, zero_mul, neg_zero, sub_zero]
    exact this
  set e : ℝ := δ / (1 - 2 * δ) with he
  set q : ℝ := δ * K / (σ * Z) with hq
  have hq0 : 0 < q := by rw [hq]; positivity
  set us : ℝ := q ^ e with hus
  have hus0 : 0 < us := Real.rpow_pos_of_pos hq0 _
  -- `us^{p-1} = q`
  have hpe : e * (p - 1) = 1 := by
    have h1 : 1 - 2 * δ ≠ 0 := h12.ne'
    rw [he, hp, div_sub_one hδ0.ne', div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero h1 hδ0.ne')]
    rw [hδ]; ring
  have husp1 : us ^ (p - 1) = q := by
    rw [hus, ← Real.rpow_mul hq0.le, hpe, Real.rpow_one]
  have husp : us ^ p = us * q := by
    rw [show p = 1 + (p - 1) by ring, Real.rpow_add hus0, Real.rpow_one, husp1]
  -- Bernoulli at `x = u/us`
  set x : ℝ := u / us with hx
  have hx0 : 0 < x := div_pos hu0 hus0
  have hb := one_add_mul_self_le_rpow_one_add (s := x - 1) (by linarith) hp1.le
  rw [show 1 + (x - 1) = x by ring] at hb
  have hxp : x ^ p = u ^ p / us ^ p := Real.div_rpow hu0.le hus0.le p
  -- `Z u^p = Z us^p x^p ≥ Z us q (1 + p(x - 1))`, and `Z q = δK/σ = K/p`
  have hZq : Z * q = K / p := by
    rw [hq, hp]; field_simp
  have key : u ^ p = us ^ p * x ^ p := by rw [hxp]; field_simp
  have hmain : Z * u ^ p ≥ K / p * us * (1 + p * (x - 1)) := by
    rw [key, husp]
    have : Z * (us * q * x ^ p) = (Z * q) * us * x ^ p := by ring
    rw [this, hZq]
    have hK' : 0 ≤ K / p * us := by positivity
    exact mul_le_mul_of_nonneg_left hb hK'
  have hux : us * x = u := by rw [hx]; field_simp
  have hδσ : (1 - (1 - σ) / σ) = 1 - 1 / p := by rw [hp, hδ]; field_simp
  rw [hδσ, ← hup]
  have hp0 : 0 < p := by linarith
  have expand : K / p * us * (1 + p * (x - 1)) = K / p * us - K * us + K * (us * x) := by
    field_simp; ring
  rw [expand, hux] at hmain
  have : -((1 - 1 / p) * K * us) = K / p * us - K * us := by ring
  have hc : u ^ p * Z = Z * u ^ p := mul_comm _ _
  linarith [this, hmain, hc]

/-- `κ(x) = e^{-x}/(1 - e^{-x})²`. -/
noncomputable def kappa (x : ℝ) : ℝ := Real.exp (-x) / (1 - Real.exp (-x)) ^ 2

lemma kappa_nonneg (x : ℝ) : 0 ≤ kappa x := by unfold kappa; positivity

/-- **The remainder's `a`-dependence is increasing:** for `0 ≤ δ ≤ 1`, `C > 0`, `0 < a ≤ a'` and `δ ≤ C/a'`,
`a^{-δ} κ(C/a) ≤ a'^{-δ} κ(C/a')`. With `t = (a'/a)^δ ≥ 1`: `a'^{-δ} = a^{-δ}/t`, and `c = C/a = c' t^{1/δ}` with
`c - c' ≥ c'(t - 1)/δ ≥ t - 1` (Bernoulli), so `t e^{-c} ≤ e^{-c'}`; the denominator only helps. This generalizes HCN's
`bg_core_mono` (the case `δ = 1/8`). -/
theorem rpow_neg_mul_kappa_mono {δ C a a' : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hC : 0 < C) (ha : 0 < a)
    (haa : a ≤ a') (hc' : δ ≤ C / a') :
    a ^ (-δ) * kappa (C / a) ≤ a' ^ (-δ) * kappa (C / a') := by
  have ha' : 0 < a' := lt_of_lt_of_le ha haa
  set c := C / a with hcdef
  set c' := C / a' with hc'def
  have hc'0 : 0 < c' := by positivity
  have hcc : c' ≤ c := div_le_div_of_nonneg_left hC.le ha haa
  have hq' : 0 < 1 - Real.exp (-c') := by
    have := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hc'0); linarith
  have hqq : 1 - Real.exp (-c') ≤ 1 - Real.exp (-c) := by
    have := Real.exp_le_exp.mpr (neg_le_neg hcc); linarith
  have hden : (1 - Real.exp (-c')) ^ 2 ≤ (1 - Real.exp (-c)) ^ 2 := pow_le_pow_left₀ hq'.le hqq 2
  rcases eq_or_lt_of_le hδ0 with hδ | hδ
  · -- `δ = 0`: `κ` is decreasing
    rw [← hδ, neg_zero, Real.rpow_zero, Real.rpow_zero, one_mul, one_mul]
    unfold kappa
    calc Real.exp (-c) / (1 - Real.exp (-c)) ^ 2 ≤ Real.exp (-c') / (1 - Real.exp (-c)) ^ 2 :=
          div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hcc)) (by positivity)
      _ ≤ Real.exp (-c') / (1 - Real.exp (-c')) ^ 2 :=
          div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity) hden
  set t : ℝ := (a' / a) ^ δ with htdef
  have hr : 1 ≤ a' / a := (one_le_div ha).mpr haa
  have ht1 : 1 ≤ t := Real.one_le_rpow hr hδ.le
  have ht0 : 0 < t := by linarith
  -- `a'^{-δ} = a^{-δ} / t`
  have ha'δ : a' ^ (-δ) = a ^ (-δ) / t := by
    rw [htdef, Real.div_rpow ha'.le ha.le, Real.rpow_neg ha'.le, Real.rpow_neg ha.le]
    field_simp
  -- `c = c' · t^{1/δ}`
  have htp : t ^ (1 / δ) = a' / a := by
    rw [htdef, ← Real.rpow_mul (by positivity), mul_one_div_cancel hδ.ne', Real.rpow_one]
  have hcc' : c = c' * t ^ (1 / δ) := by
    rw [htp, hcdef, hc'def]; field_simp
  -- Bernoulli: `t^{1/δ} ≥ 1 + (1/δ)(t - 1)`
  have hb := one_add_mul_self_le_rpow_one_add (s := t - 1) (p := 1 / δ) (by linarith)
    (by rw [le_div_iff₀ hδ]; linarith)
  rw [show 1 + (t - 1) = t by ring] at hb
  have hdiff : t - 1 ≤ c - c' := by
    rw [hcc']
    have h1 : c' * (1 / δ * (t - 1)) ≥ t - 1 := by
      have : 1 ≤ c' * (1 / δ) := by rw [mul_one_div, le_div_iff₀ hδ]; linarith
      nlinarith
    nlinarith
  have hexp : t * Real.exp (-c) ≤ Real.exp (-c') := by
    have h1 : t ≤ Real.exp (c - c') := by linarith [Real.add_one_le_exp (c - c')]
    calc t * Real.exp (-c) ≤ Real.exp (c - c') * Real.exp (-c) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = Real.exp (-c') := by rw [← Real.exp_add]; ring_nf
  rw [ha'δ]
  unfold kappa
  have haδ : 0 < a ^ (-δ) := Real.rpow_pos_of_pos ha _
  rw [div_mul_eq_mul_div, le_div_iff₀ ht0]
  calc a ^ (-δ) * (Real.exp (-c) / (1 - Real.exp (-c)) ^ 2) * t
      = a ^ (-δ) * (t * Real.exp (-c) / (1 - Real.exp (-c)) ^ 2) := by ring
    _ ≤ a ^ (-δ) * (Real.exp (-c') / (1 - Real.exp (-c')) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ haδ.le
        calc t * Real.exp (-c) / (1 - Real.exp (-c)) ^ 2 ≤ Real.exp (-c') / (1 - Real.exp (-c)) ^ 2 :=
              div_le_div_of_nonneg_right hexp (by positivity)
          _ ≤ Real.exp (-c') / (1 - Real.exp (-c')) ^ 2 :=
              div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity) hden

end BoundariesOfClass.Analytic
