import Mathlib
import BoundariesOfClass.Sieve.Soundness

/-!
# The count bound from arithmetic hypotheses

`mu_le_classNumber`: for `K` with `𝓞 K = ℤ[θ]`, `θ² = t·θ - c`, `d = 4c - t² > 0`, and a list `L` of
distinct primes, each split (`p ∤ d`, and `X² - t·X + c` has a root mod `p`) or ramified (`p ∣ d`), every
`Y` with `4Y² < d` gives `mu L Y ≤ classNumber K`.

The ideals of `BoundariesOfClass.Sieve.Fam` are built here: a root gives an ideal `P` of norm `p`
(Kummer–Dedekind, `HCN.Finite.exists_absNorm_eq_of_root`), and `(p) = P·J` with `N(J) = p`
(`HCN.Finite.exists_mul_eq_span_of_absNorm_eq`). For a split `p`, `P ≠ J`: otherwise `P² = (p)`, and with
`θ - z ∈ P` the element `(θ - z)² = (t - 2z)·θ + (z² - c)` lies in `(p)`, so `p ∣ t - 2z`, and with
`p ∣ z² - t·z + c` this gives `p ∣ 4(z² - tz + c) - (t - 2z)² = d`. A ramified `p` always has a root:
`r = c` for `p = 2` (then `t` is even), and `r = t·(p + 1)/2` for odd `p`, where
`4(r² - tr + c) = (2r - t)² + d = t²p² + d`.
-/

namespace BoundariesOfClass.Sieve

open NumberField Ideal Polynomial
open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

section Field

variable {t c : ℕ} (D : CN1.Finite.QuadInt K (t : ℤ) (c : ℤ))
include D

/-- For a split prime the two ideals of norm `p` differ. -/
theorem ne_of_not_dvd (htc : t * t < 4 * c) {P J : Ideal (𝓞 K)} {p : ℕ} (hp : p.Prime) (hP : absNorm P = p)
    (hPJ : P * J = span {(p : 𝓞 K)}) (hpd : ¬ (p : ℤ) ∣ 4 * c - t * t) : P ≠ J := by
  rintro rfl
  obtain ⟨z, hz⟩ := HCN.Finite.exists_sub_mem D hp hP
  have hz2 : (D.θ - z) ^ 2 ∈ P * P := by rw [sq]; exact Ideal.mul_mem_mul hz hz
  rw [hPJ, Ideal.mem_span_singleton] at hz2
  obtain ⟨γ, hγ⟩ := hz2
  obtain ⟨a, b, rfl⟩ := D.exists_eq_add_mul γ
  have key : ((z ^ 2 - c : ℤ) : 𝓞 K) + ((t - 2 * z : ℤ) : 𝓞 K) * D.θ =
      ((p * a : ℤ) : 𝓞 K) + ((p * b : ℤ) : 𝓞 K) * D.θ := by
    push_cast at hγ ⊢
    linear_combination hγ - HCN.Finite.theta_sq D
  obtain ⟨-, hb⟩ := HCN.Finite.add_mul_theta_inj D htc key
  have h1 : (p : ℤ) ∣ t - 2 * z := ⟨b, hb⟩
  have h2 : (p : ℤ) ∣ z ^ 2 - t * z + c := HCN.Finite.dvd_root_of_sub_mem D hp hP hz
  apply hpd
  have : 4 * (c : ℤ) - t * t = 4 * (z ^ 2 - t * z + c) - (t - 2 * z) ^ 2 := by ring
  rw [this]
  exact dvd_sub (dvd_mul_of_dvd_right h2 4) (dvd_pow h1 two_ne_zero)

omit D in
/-- A ramified prime has a root of `X² - t·X + c`. -/
theorem exists_root_of_dvd {p : ℕ} (hp : p.Prime) (hpd : (p : ℤ) ∣ 4 * c - t * t) :
    ∃ r : ℤ, (p : ℤ) ∣ r ^ 2 - t * r + c := by
  rcases hp.eq_two_or_odd' with rfl | hodd
  · -- `t` is even
    have ht : (2 : ℤ) ∣ t := by
      have h : (2 : ℤ) ∣ (t : ℤ) * t := by
        have : (2 : ℤ) ∣ 4 * c := ⟨2 * c, by ring⟩
        have := dvd_sub this hpd
        simpa using this
      exact Int.prime_two.dvd_or_dvd h |>.elim id id
    obtain ⟨s, hs⟩ := ht
    refine ⟨c, ?_⟩
    have : (c : ℤ) ^ 2 - t * c + c = 2 * ((c * (c + 1)) / 2 - s * c) := by
      have hev : (2 : ℤ) ∣ c * (c + 1) := by
        rcases Int.even_or_odd (c : ℤ) with ⟨e, he⟩ | ⟨e, he⟩
        · exact ⟨e * (c + 1), by rw [he]; ring⟩
        · exact ⟨(c : ℤ) * (e + 1), by rw [he]; ring⟩
      obtain ⟨w, hw⟩ := hev
      rw [hw, hs]
      have : (2 * w) / 2 = w := by omega
      rw [this]; linear_combination hw
    rw [this]
    exact dvd_mul_right _ _
  · obtain ⟨k, hk⟩ := hodd
    refine ⟨(t : ℤ) * (k + 1), ?_⟩
    -- `4(r² - tr + c) = t²p² + d`, and `p` is odd
    have h4 : (4 : ℤ) * ((t * (k + 1)) ^ 2 - t * (t * (k + 1)) + c) = t ^ 2 * (p : ℤ) ^ 2 + (4 * c - t * t) := by
      rw [show (p : ℤ) = 2 * k + 1 by exact_mod_cast hk]; ring
    have hdvd : (p : ℤ) ∣ 4 * ((t * (k + 1)) ^ 2 - t * (t * (k + 1)) + c) := by
      rw [h4]; exact dvd_add (dvd_mul_of_dvd_right (dvd_pow_self _ two_ne_zero) _) hpd
    have hcop : IsCoprime (p : ℤ) 4 := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      have : Nat.Coprime p 4 := by
        rw [show (4 : ℕ) = 2 ^ 2 by rfl]
        exact Nat.Coprime.pow_right 2 ((Nat.coprime_primes hp Nat.prime_two).mpr (by omega))
      exact_mod_cast this
    exact hcop.dvd_of_dvd_mul_left hdvd

/-- The two ideals of norm `p` for a listed prime. -/
theorem exists_pair (htc : t * t < 4 * c) {p : ℕ} (hp : p.Prime) {b : Bool}
    (hs : b = true → ¬ (p : ℤ) ∣ 4 * c - t * t ∧ ∃ r : ℤ, (p : ℤ) ∣ r ^ 2 - t * r + c)
    (hr : b = false → (p : ℤ) ∣ 4 * c - t * t) :
    ∃ PJ : (Ideal (𝓞 K))⁰ × (Ideal (𝓞 K))⁰, absNorm (PJ.1 : Ideal (𝓞 K)) = p ∧
      absNorm (PJ.2 : Ideal (𝓞 K)) = p ∧ (PJ.1 : Ideal (𝓞 K)) * PJ.2 = span {(p : 𝓞 K)} ∧
      (b = true → PJ.1 ≠ PJ.2) := by
  obtain ⟨r, hroot⟩ : ∃ r : ℤ, (p : ℤ) ∣ r ^ 2 - t * r + c := by
    cases b
    · exact exists_root_of_dvd hp (hr rfl)
    · exact (hs rfl).2
  obtain ⟨P0, hP0⟩ := HCN.Finite.exists_absNorm_eq_of_root D hp r hroot
  obtain ⟨J0, hJ0, hPJ⟩ := HCN.Finite.exists_mul_eq_span_of_absNorm_eq D hp hP0
  refine ⟨(⟨P0, HCN.Finite.mem_nonZeroDivisors_of_absNorm_eq hp hP0⟩,
    ⟨J0, HCN.Finite.mem_nonZeroDivisors_of_absNorm_eq hp hJ0⟩), hP0, hJ0, hPJ, ?_⟩
  intro hb h
  exact ne_of_not_dvd D htc hp hP0 hPJ (hs hb).1 (congrArg Subtype.val h)

/-- **The count is at most the class number.** -/
theorem mu_le_classNumber (htc : t * t < 4 * c) (L : List (ℕ × Bool))
    (hL : ∀ pb ∈ L, pb.1.Prime ∧
      (pb.2 = true → ¬ (pb.1 : ℤ) ∣ 4 * c - t * t ∧ ∃ r : ℤ, (pb.1 : ℤ) ∣ r ^ 2 - t * r + c) ∧
      (pb.2 = false → (pb.1 : ℤ) ∣ 4 * c - t * t))
    (hnd : (L.map (·.1)).Nodup) {Y : ℕ} (hY : 4 * (Y * Y) < 4 * c - t * t) :
    mu L Y ≤ classNumber K := by
  classical
  have hex : ∀ p : ℕ, ∃ PJ : (Ideal (𝓞 K))⁰ × (Ideal (𝓞 K))⁰, ∀ b, (p, b) ∈ L →
      absNorm (PJ.1 : Ideal (𝓞 K)) = p ∧ absNorm (PJ.2 : Ideal (𝓞 K)) = p ∧
      (PJ.1 : Ideal (𝓞 K)) * PJ.2 = span {(p : 𝓞 K)} ∧ (b = true → PJ.1 ≠ PJ.2) := by
    intro p
    by_cases h : ∃ b, (p, b) ∈ L
    · obtain ⟨b, hb⟩ := h
      obtain ⟨hp, hs, hr⟩ := hL _ hb
      obtain ⟨PJ, h1, h2, h3, h4⟩ := exists_pair D htc hp hs hr
      refine ⟨PJ, fun b' hb' => ?_⟩
      have hpbeq : (p, b') = (p, b) := List.inj_on_of_nodup_map hnd hb' hb rfl
      cases hpbeq
      exact ⟨h1, h2, h3, h4⟩
    · exact ⟨(1, 1), fun b hb => (h ⟨b, hb⟩).elim⟩
  choose PJ hPJ using hex
  have hF : Fam (fun p => (PJ p).1) (fun p => (PJ p).2) L :=
    { prime := fun pb h => (hL pb h).1
      normP := fun pb h => (hPJ pb.1 pb.2 h).1
      normJ := fun pb h => (hPJ pb.1 pb.2 h).2.1
      mul := fun pb h => (hPJ pb.1 pb.2 h).2.2.1
      ne := fun pb h => (hPJ pb.1 pb.2 h).2.2.2 }
  exact mu_le_classNumber_of_fam D _ _ htc hF hnd hY

end Field

end BoundariesOfClass.Sieve
