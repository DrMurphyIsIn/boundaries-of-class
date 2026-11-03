import Mathlib

/-!
# BoundariesOfClass.Primitivity.Criterion: a criterion for primitivity of a Dirichlet character

Pinned environment: Lean v4.34.1, Mathlib d13f23b. Mathlib only.

* `isPrimitive_of_forall_prime`: a Dirichlet character `χ` of level `n ≠ 0` is primitive if, for every prime `p ∣ n`,
  some `a` coprime to `n` with `a ≡ 1 (mod n/p)` has `χ(a) ≠ 1`.

If the conductor `c` were a proper divisor of `n`, then `c ∣ n/p` for the least prime factor `p` of `n/c`. So `χ` would
factor through `n/p` (Mathlib's `mem_conductorSet_iff_conductor_dvd` and `FactorsThrough.mono`), and would be trivial on
every unit that is `1` modulo `n/p` (`factorsThrough_iff_ker_unitsMap`). The witness `a` is such a unit.
-/

set_option autoImplicit false

namespace BoundariesOfClass.Primitivity

open DirichletCharacter

/-- **A criterion for primitivity.** If for every prime `p ∣ n` some `a` coprime to `n`, with `a ≡ 1 (mod n/p)`, has
`χ(a) ≠ 1`, then `χ` is primitive. -/
theorem isPrimitive_of_forall_prime {R : Type*} [CommMonoidWithZero R] {n : ℕ} [NeZero n]
    (χ : DirichletCharacter R n)
    (h : ∀ p : ℕ, p.Prime → p ∣ n → ∃ a : ℕ, Nat.Coprime a n ∧ (a : ZMod (n / p)) = 1 ∧ χ a ≠ 1) :
    χ.IsPrimitive := by
  rw [isPrimitive_def]
  by_contra hc
  obtain ⟨k, hk⟩ := conductor_dvd_level χ
  have hk1 : k ≠ 1 := by
    rintro rfl
    exact hc (by rw [mul_one] at hk; exact hk.symm)
  have hp : k.minFac.Prime := Nat.minFac_prime hk1
  obtain ⟨k', hk'⟩ := Nat.minFac_dvd k
  set p := k.minFac with hpdef
  have hpn : p ∣ n := ⟨χ.conductor * k', hk.trans (by rw [hk']; ring)⟩
  -- `n / p = c k'`, so the conductor divides `n / p`
  have hnp : n / p = χ.conductor * k' :=
    Nat.div_eq_of_eq_mul_left hp.pos (hk.trans (by rw [hk']; ring))
  have hcp : χ.conductor ∣ n / p := ⟨k', hnp⟩
  have hdvd : n / p ∣ n := Nat.div_dvd_of_dvd hpn
  have hft : χ.FactorsThrough (n / p) := (factorsThrough_conductor χ).mono χ hcp hdvd
  rw [factorsThrough_iff_ker_unitsMap hdvd] at hft
  obtain ⟨a, ha, ha1, hχa⟩ := h p hp hpn
  set u := ZMod.unitOfCoprime a ha
  have hu : u ∈ (ZMod.unitsMap hdvd).ker := by
    rw [MonoidHom.mem_ker, Units.ext_iff, ZMod.unitsMap_val, ZMod.coe_unitOfCoprime, Units.val_one,
      ZMod.cast_natCast hdvd, ha1]
  have h1 := hft hu
  rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, ZMod.coe_unitOfCoprime, Units.val_one] at h1
  exact hχa h1

end BoundariesOfClass.Primitivity
