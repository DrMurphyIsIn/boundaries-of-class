import Mathlib
import BoundariesOfClass.Sieve.Mu
import HCN.Finite.ClassLower
import HCN.Finite.IdealLite

/-!
# Soundness of the smooth-number count: `mu L Y ≤ h` when `4Y² < d`

`K` is a number field with `𝓞 K = ℤ[θ]`, `θ² = t·θ - c`, given by `CN1.Finite.QuadInt K t c`, and
`d = 4c - t² > 0`. Let `L` list distinct primes, each tagged split (`p ∤ d` and `X² - t·X + c` has a root
mod `p`) or ramified (`p ∣ d`), and let `4Y² < d`. Then `mu L Y ≤ classNumber K` (`mu_le_classNumber`).

**The paper proof.** For each listed `p` choose an ideal `P_p` of norm `p` and the ideal `J_p` of norm `p`
with `P_p·J_p = (p)`, so `[J_p] = [P_p]⁻¹`; for a split `p` they differ. An exponent vector `v` gives the
ideal `I_v = ∏ Q_p^{|v_p|}` (`Q_p = P_p` if `v_p ≥ 0`, else `J_p`), of norm `n(v) = ∏ p^{|v_p|}` and class
`∏ [P_p]^{v_p}`. Let `v ≠ v'` be two of the vectors counted by `mu L Y`, so `n(v), n(v') ≤ Y`, and put
`w = v - v'`. If `[I_v] = [I_{v'}]`, then `I_w` is principal, and `w ≠ 0`, `n(w) ≤ n(v)·n(v') ≤ Y² < d/4`,
with ramified entries `±1` or `0`. Let `I_w = (β)`, `β = x + yθ`. Then `4·n(w) = (2x + ty)² + d·y²`, so
`y = 0` and `n(w) = x²`; as `w ≠ 0`, `n(w) ≥ 2`, so some prime `q` divides `x`, and `q` is a listed prime
with `w_q ≠ 0`.
* If `q` is ramified, `q` divides `n(w)` exactly once, but `q² ∣ x²`.
* If `q` splits, say `w_q > 0`, then `I_w = (x) ⊆ (q) ⊆ J_q`. The prime `J_q` then contains a factor of
  `I_w`: either `P_q`, so `P_q = J_q` (both are maximal), or some `Q_p` with `p ≠ q`, so `Q_p = J_q` and
  `p = N(Q_p) = q`. Both are impossible. The case `w_q < 0` is the same with `P_q` and `J_q` exchanged.

So the classes of the counted vectors are pairwise distinct, and there are `mu L Y` of them
(`BoundariesOfClass.Sieve.length_vecs`). This is the reduction-free form of the count of reduced forms
`(a, b, c)` with `4a² < d` in Watkins, *Class numbers of imaginary quadratic fields*, Math. Comp. 73 (2004),
§8 (eq. (2) and Lemma 3 there), restricted to the `a` built from the listed primes.
-/

namespace BoundariesOfClass.Sieve

open NumberField Ideal
open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

/-! ### Exponent vectors as ideals and classes -/

section Family

variable (P J : ℕ → (Ideal (𝓞 K))⁰)

/-- The factor `Q_p^{|k|}` of an entry `((p, b), k)`. -/
noncomputable def fac (z : (ℕ × Bool) × ℤ) : (Ideal (𝓞 K))⁰ :=
  (if 0 ≤ z.2 then P z.1.1 else J z.1.1) ^ z.2.natAbs

/-- The class `[P_p]^k` of an entry. -/
noncomputable def cls (z : (ℕ × Bool) × ℤ) : ClassGroup (𝓞 K) :=
  ClassGroup.mk0 (P z.1.1) ^ z.2

/-- The norm `p^{|k|}` of an entry. -/
def nrm (z : (ℕ × Bool) × ℤ) : ℕ := z.1.1 ^ z.2.natAbs

/-- **The family.** For each listed `(p, b)`: `p` prime, `N(P_p) = N(J_p) = p`, `P_p·J_p = (p)`, and
`P_p ≠ J_p` when `p` splits. -/
structure Fam (L : List (ℕ × Bool)) : Prop where
  prime : ∀ pb ∈ L, pb.1.Prime
  normP : ∀ pb ∈ L, absNorm (P pb.1 : Ideal (𝓞 K)) = pb.1
  normJ : ∀ pb ∈ L, absNorm (J pb.1 : Ideal (𝓞 K)) = pb.1
  mul : ∀ pb ∈ L, (P pb.1 : Ideal (𝓞 K)) * J pb.1 = span {((pb.1 : ℕ) : 𝓞 K)}
  ne : ∀ pb ∈ L, pb.2 = true → P pb.1 ≠ J pb.1

theorem mk0_J {L : List (ℕ × Bool)} (hF : Fam P J L) {pb : ℕ × Bool} (h : pb ∈ L) :
    ClassGroup.mk0 (J pb.1) = (ClassGroup.mk0 (P pb.1))⁻¹ :=
  ClassGroup.mk0_eq_mk0_inv_iff.mpr ⟨(pb.1 : 𝓞 K), by exact_mod_cast (hF.prime pb h).ne_zero, by
    rw [mul_comm]; exact hF.mul pb h⟩

theorem mk0_fac {L : List (ℕ × Bool)} (hF : Fam P J L) {z : (ℕ × Bool) × ℤ} (h : z.1 ∈ L) :
    ClassGroup.mk0 (fac P J z) = cls P z := by
  unfold fac cls
  split_ifs with hk
  · rw [map_pow, ← zpow_natCast, Int.natAbs_of_nonneg hk]
  · rw [map_pow, mk0_J P J hF h, inv_pow, ← zpow_natCast, ← zpow_neg]
    congr 1
    omega

theorem absNorm_fac {L : List (ℕ × Bool)} (hF : Fam P J L) {z : (ℕ × Bool) × ℤ} (h : z.1 ∈ L) :
    absNorm (fac P J z : Ideal (𝓞 K)) = nrm z := by
  unfold fac nrm
  rw [SubmonoidClass.coe_pow, map_pow]
  split_ifs
  · rw [hF.normP _ h]
  · rw [hF.normJ _ h]

theorem mk0_prod_fac {L : List (ℕ × Bool)} (hF : Fam P J L) :
    ∀ Z : List ((ℕ × Bool) × ℤ), (∀ z ∈ Z, z.1 ∈ L) →
      ClassGroup.mk0 (Z.map (fac P J)).prod = (Z.map (cls P)).prod
  | [], _ => by simp
  | z :: Z, h => by
    rw [List.map_cons, List.prod_cons, map_mul, mk0_fac P J hF (h z List.mem_cons_self),
      mk0_prod_fac hF Z (fun z' hz' => h z' (List.mem_cons_of_mem _ hz')), List.map_cons, List.prod_cons]

theorem absNorm_prod_fac {L : List (ℕ × Bool)} (hF : Fam P J L) :
    ∀ Z : List ((ℕ × Bool) × ℤ), (∀ z ∈ Z, z.1 ∈ L) →
      absNorm ((Z.map (fac P J)).prod : Ideal (𝓞 K)) = (Z.map nrm).prod
  | [], _ => by simp
  | z :: Z, h => by
    rw [List.map_cons, List.prod_cons, Submonoid.coe_mul, map_mul, absNorm_fac P J hF (h z List.mem_cons_self),
      absNorm_prod_fac hF Z (fun z' hz' => h z' (List.mem_cons_of_mem _ hz')), List.map_cons, List.prod_cons]

end Family

/-! ### Arithmetic of the norms -/

theorem one_le_prod_nrm : ∀ Z : List ((ℕ × Bool) × ℤ), (∀ z ∈ Z, 1 ≤ z.1.1) → 1 ≤ (Z.map nrm).prod
  | [], _ => by simp
  | z :: Z, h => by
    rw [List.map_cons, List.prod_cons]
    exact Nat.one_le_iff_ne_zero.mpr (mul_ne_zero
      (pow_ne_zero _ (by have := h z List.mem_cons_self; omega))
      (by have := one_le_prod_nrm Z (fun z' hz' => h z' (List.mem_cons_of_mem _ hz')); omega))

theorem two_le_prod_nrm : ∀ Z : List ((ℕ × Bool) × ℤ), (∀ z ∈ Z, 2 ≤ z.1.1) → (∃ z ∈ Z, z.2 ≠ 0) →
    2 ≤ (Z.map nrm).prod
  | [], _, ⟨z, hz, _⟩ => by simp at hz
  | z :: Z, h, ⟨z', hz', hne⟩ => by
    rw [List.map_cons, List.prod_cons]
    have h1 : 1 ≤ (Z.map nrm).prod :=
      one_le_prod_nrm Z (fun y hy => by have := h y (List.mem_cons_of_mem _ hy); omega)
    have h2 : 1 ≤ nrm z := Nat.one_le_pow _ _ (by have := h z List.mem_cons_self; omega)
    rcases List.mem_cons.mp hz' with rfl | hz'
    · have : 2 ≤ nrm z' := by
        unfold nrm
        calc 2 ≤ z'.1.1 := h z' List.mem_cons_self
          _ = z'.1.1 ^ 1 := (pow_one _).symm
          _ ≤ z'.1.1 ^ z'.2.natAbs :=
            Nat.pow_le_pow_right (by have := h z' List.mem_cons_self; omega) (by omega)
      nlinarith
    · have := two_le_prod_nrm Z (fun y hy => h y (List.mem_cons_of_mem _ hy)) ⟨z', hz', hne⟩
      nlinarith

/-- A prime dividing `∏ p^{|k|}` (primes `p`) is one of the `p` with `k ≠ 0`. -/
theorem exists_of_prime_dvd_prod_nrm {q : ℕ} (hq : q.Prime) :
    ∀ Z : List ((ℕ × Bool) × ℤ), (∀ z ∈ Z, z.1.1.Prime) → q ∣ (Z.map nrm).prod →
      ∃ z ∈ Z, z.1.1 = q ∧ z.2 ≠ 0 := by
  intro Z hZ hdvd
  obtain ⟨a, ha, hqa⟩ := (Prime.dvd_prod_iff hq.prime).mp hdvd
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp ha
  have hk : z.2.natAbs ≠ 0 := by
    intro h0
    simp [nrm, h0] at hqa
    exact hq.one_lt.ne' hqa
  have : q ∣ z.1.1 := hq.dvd_of_dvd_pow hqa
  refine ⟨z, hz, ((Nat.prime_dvd_prime_iff_eq hq (hZ z hz)).mp this).symm, ?_⟩
  omega

/-- The product over entries at primes other than `q` is prime to `q`. -/
theorem not_dvd_prod_nrm {q : ℕ} (hq : q.Prime) :
    ∀ Z : List ((ℕ × Bool) × ℤ), (∀ z ∈ Z, z.1.1.Prime) → (∀ z ∈ Z, z.1.1 ≠ q) →
      ¬ q ∣ (Z.map nrm).prod := by
  intro Z hZ hne hdvd
  obtain ⟨z, hz, hzq, -⟩ := exists_of_prime_dvd_prod_nrm hq Z hZ hdvd
  exact hne z hz hzq

/-! ### No factor of the other entries lies in a prime of norm `q` -/

section NotLe

variable (P J : ℕ → (Ideal (𝓞 K))⁰)

theorem not_prod_le {L : List (ℕ × Bool)} (hF : Fam P J L) {M : Ideal (𝓞 K)} [hM : M.IsPrime] {q : ℕ}
    (hMq : absNorm M = q) :
    ∀ Z : List ((ℕ × Bool) × ℤ), (∀ z ∈ Z, z.1 ∈ L) → (∀ z ∈ Z, z.1.1 ≠ q) →
      ¬ ((Z.map (fac P J)).prod : Ideal (𝓞 K)) ≤ M
  | [], _, _, h => by
    simp only [List.map_nil, List.prod_nil, OneMemClass.coe_one, Ideal.one_eq_top, top_le_iff] at h
    exact hM.ne_top h
  | z :: Z, hL, hq, h => by
    rw [List.map_cons, List.prod_cons, Submonoid.coe_mul, hM.mul_le] at h
    rcases h with h | h
    · have hzL := hL z List.mem_cons_self
      have hp := (hF.prime _ hzL)
      unfold fac at h
      rw [SubmonoidClass.coe_pow] at h
      by_cases hk : z.2.natAbs = 0
      · rw [hk, pow_zero, Ideal.one_eq_top, top_le_iff] at h
        exact hM.ne_top h
      · have hle := hM.le_of_pow_le h
        set G : Ideal (𝓞 K) := ((if 0 ≤ z.2 then P z.1.1 else J z.1.1 : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))
        have hGn : absNorm G = z.1.1 := by
          simp only [G]; split_ifs
          · exact hF.normP _ hzL
          · exact hF.normJ _ hzL
        have hGmax : G.IsMaximal := HCN.Finite.isMaximal_of_absNorm_eq hp hGn
        have hGM : G = M := hGmax.eq_of_le hM.ne_top hle
        apply hq z List.mem_cons_self
        rw [← hGn, hGM, hMq]
    · exact not_prod_le hF hMq Z (fun z' hz' => hL z' (List.mem_cons_of_mem _ hz'))
        (fun z' hz' => hq z' (List.mem_cons_of_mem _ hz')) h

end NotLe

/-! ### The key lemma: a nonzero admissible vector of small norm is not principal -/

section Key

variable {t c : ℕ} (D : CN1.Finite.QuadInt K (t : ℤ) (c : ℤ))
variable (P J : ℕ → (Ideal (𝓞 K))⁰)

/-- `Q(x, y) < d/4` forces `y = 0`. -/
theorem y_eq_zero_of_form_lt {x y : ℤ} {n : ℕ}
    (hxy : x ^ 2 + (t : ℤ) * x * y + (c : ℤ) * y ^ 2 = n) (hn : 4 * n < 4 * c - t * t) : y = 0 := by
  have h4 := CN1.Finite.four_mul_form (t : ℤ) c x y
  rw [hxy] at h4
  have hlt : (4 * n : ℤ) < 4 * c - (t : ℤ) ^ 2 := by
    have : ((4 * n : ℕ) : ℤ) < ((4 * c - t * t : ℕ) : ℤ) := by exact_mod_cast hn
    push_cast [Nat.cast_sub (by omega : t * t ≤ 4 * c)] at this
    nlinarith
  by_contra hy
  have hy2 : 1 ≤ y ^ 2 := by
    have := sq_pos_of_ne_zero hy
    omega
  nlinarith [sq_nonneg (2 * x + t * y)]

include D in
/-- **Key lemma.** Let the entries of `Z` lie in `L` (a valid family), at distinct primes, with ramified
entries in `{-1, 0, 1}` and some entry nonzero. If `4·∏ p^{|k|} < d`, then `∏ Q_p^{|k|}` is not
principal. -/
theorem not_isPrincipal (htc : t * t < 4 * c) {L : List (ℕ × Bool)} (hF : Fam P J L)
    (Z : List ((ℕ × Bool) × ℤ)) (hZL : ∀ z ∈ Z, z.1 ∈ L) (hnd : (Z.map (·.1.1)).Nodup)
    (hram : ∀ z ∈ Z, z.1.2 = false → z.2.natAbs ≤ 1) (hne : ∃ z ∈ Z, z.2 ≠ 0)
    (hsmall : 4 * (Z.map nrm).prod < 4 * c - t * t) :
    ¬ ((Z.map (fac P J)).prod : Ideal (𝓞 K)).IsPrincipal := by
  rintro ⟨β, hβ⟩
  have hprime : ∀ z ∈ Z, z.1.1.Prime := fun z hz => hF.prime _ (hZL z hz)
  set n := (Z.map nrm).prod with hn
  have hIn : absNorm ((Z.map (fac P J)).prod : Ideal (𝓞 K)) = n := absNorm_prod_fac P J hF Z hZL
  rw [hβ, Ideal.submodule_span_eq] at hIn
  obtain ⟨x, y, rfl, hxy⟩ := HCN.Finite.exists_form_eq_absNorm_span D htc.le β
  rw [hIn] at hxy
  have hy : y = 0 := y_eq_zero_of_form_lt hxy hsmall
  subst hy
  have hx2 : x ^ 2 = n := by simpa using hxy
  have hn2 : 2 ≤ n := two_le_prod_nrm Z (fun z hz => (hprime z hz).two_le) hne
  -- a prime `q ∣ x`
  have hxa : x.natAbs ^ 2 = n := by
    have : ((x.natAbs ^ 2 : ℕ) : ℤ) = (n : ℤ) := by rw [Nat.cast_pow, Int.natCast_natAbs, sq_abs]; exact hx2
    exact_mod_cast this
  have hx1 : x.natAbs ≠ 1 := by intro h; rw [h] at hxa; omega
  set q := x.natAbs.minFac with hqdef
  have hq : q.Prime := Nat.minFac_prime hx1
  have hqx : q ∣ x.natAbs := Nat.minFac_dvd _
  have hqn : q ∣ n := hxa ▸ dvd_pow hqx two_ne_zero
  obtain ⟨z, hz, hzq, hzk⟩ := exists_of_prime_dvd_prod_nrm hq Z hprime hqn
  -- split off the entry at `q`
  have hperm : Z.Perm (z :: Z.erase z) := List.perm_cons_erase hz
  have hrest : ∀ z' ∈ Z.erase z, z'.1.1 ≠ q := by
    intro z' hz' hz'q
    have hnd' := (hperm.map (·.1.1)).nodup_iff.mp hnd
    rw [List.map_cons, List.nodup_cons] at hnd'
    exact hnd'.1 (List.mem_map.mpr ⟨z', hz', by rw [hz'q, hzq]⟩)
  have hsubL : ∀ z' ∈ Z.erase z, z'.1 ∈ L := fun z' hz' => hZL z' (List.mem_of_mem_erase hz')
  have hsubP : ∀ z' ∈ Z.erase z, z'.1.1.Prime := fun z' hz' => hprime z' (List.mem_of_mem_erase hz')
  cases hb : z.1.2 with
  | false =>
    -- ramified: `q ∥ n`, but `q² ∣ x² = n`
    have hk1 : z.2.natAbs = 1 := by have := hram z hz hb; omega
    have hnsplit : n = q * ((Z.erase z).map nrm).prod := by
      rw [hn, (hperm.map nrm).prod_eq, List.map_cons, List.prod_cons]
      simp [nrm, hk1, hzq]
    have hq2 : q * q ∣ n := hxa ▸ by rw [sq]; exact Nat.mul_dvd_mul hqx hqx
    rw [hnsplit] at hq2
    have := Nat.dvd_of_mul_dvd_mul_left hq.pos hq2
    exact not_dvd_prod_nrm hq _ hsubP hrest this
  | true =>
    have hzL := hZL z hz
    have hqP : absNorm (P z.1.1 : Ideal (𝓞 K)) = q := by rw [hF.normP _ hzL, hzq]
    have hqJ : absNorm (J z.1.1 : Ideal (𝓞 K)) = q := by rw [hF.normJ _ hzL, hzq]
    have hPJ : (P z.1.1 : Ideal (𝓞 K)) ≠ J z.1.1 := by
      intro h; exact hF.ne _ hzL hb (Subtype.ext h)
    -- the "other" prime `M`: `J` if the exponent is `≥ 0`, else `P`
    set G : Ideal (𝓞 K) := ((if 0 ≤ z.2 then P z.1.1 else J z.1.1 : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))
    set M : Ideal (𝓞 K) := ((if 0 ≤ z.2 then J z.1.1 else P z.1.1 : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))
    have hMn : absNorm M = q := by simp only [M]; split_ifs <;> assumption
    have hGn : absNorm G = q := by simp only [G]; split_ifs <;> assumption
    have hGM : G ≠ M := by
      simp only [G, M]; split_ifs
      · exact hPJ
      · exact fun h => hPJ h.symm
    have hMprime : M.IsPrime := (HCN.Finite.isMaximal_of_absNorm_eq hq hMn).isPrime
    -- `(x) ⊆ (q) = P·J ⊆ M`
    have hxq : (x : 𝓞 K) ∈ span {((q : ℕ) : 𝓞 K)} := by
      rw [Ideal.mem_span_singleton]
      obtain ⟨e, he⟩ : (q : ℤ) ∣ x := Int.natCast_dvd.mpr hqx
      exact ⟨(e : 𝓞 K), by rw [he]; push_cast; ring⟩
    have hqM : span {((q : ℕ) : 𝓞 K)} ≤ M := by
      rw [← hzq, ← hF.mul _ hzL]
      simp only [M]; split_ifs
      · exact Ideal.mul_le_inf.trans inf_le_right
      · exact Ideal.mul_le_inf.trans inf_le_left
    have hle : ((Z.map (fac P J)).prod : Ideal (𝓞 K)) ≤ M := by
      rw [hβ, Ideal.submodule_span_eq, span_singleton_le_iff_mem]
      simpa using hqM hxq
    have hprod : ((Z.map (fac P J)).prod : Ideal (𝓞 K)) =
        G ^ z.2.natAbs * (((Z.erase z).map (fac P J)).prod : Ideal (𝓞 K)) := by
      rw [(hperm.map (fac P J)).prod_eq, List.map_cons, List.prod_cons, Submonoid.coe_mul]
      simp only [fac, SubmonoidClass.coe_pow, G]
    rw [hprod, hMprime.mul_le] at hle
    rcases hle with h | h
    · have hGle := hMprime.le_of_pow_le h
      exact hGM ((HCN.Finite.isMaximal_of_absNorm_eq hq hGn).eq_of_le hMprime.ne_top hGle)
    · exact not_prod_le P J hF hMn _ hsubL hrest h

end Key

/-! ### Differences of exponent vectors -/

/-- `L.zip (v - v')`, entrywise. -/
def zipSub (L : List (ℕ × Bool)) (v v' : List ℤ) : List ((ℕ × Bool) × ℤ) :=
  L.zip (List.zipWith (· - ·) v v')

theorem adm_length : ∀ {L : List (ℕ × Bool)} {v : List ℤ}, Adm L v → v.length = L.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp [adm_length h.2]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem normOf_eq_prod : ∀ (L : List (ℕ × Bool)) (v : List ℤ), normOf L v = ((L.zip v).map nrm).prod
  | [], _ => by simp [normOf]
  | _ :: _, [] => by simp [normOf]
  | (p, b) :: L, k :: v => by simp [normOf, nrm, normOf_eq_prod L v]

theorem one_le_normOf {L : List (ℕ × Bool)} (h : ∀ pb ∈ L, 1 ≤ pb.1) (v : List ℤ) : 1 ≤ normOf L v := by
  rw [normOf_eq_prod]
  exact one_le_prod_nrm _ (fun z hz => h z.1 (List.of_mem_zip hz).1)

theorem prod_nrm_zipSub_le : ∀ {L : List (ℕ × Bool)} {v v' : List ℤ}, (∀ pb ∈ L, 1 ≤ pb.1) →
    ((zipSub L v v').map nrm).prod ≤ normOf L v * normOf L v'
  | [], _, _, _ => by simp [zipSub, normOf]
  | _ :: _, [], _, h => by simpa [zipSub, normOf] using one_le_normOf h _
  | pb :: L, k :: v, [], h => by simpa [zipSub, normOf] using one_le_normOf h (k :: v)
  | (p, b) :: L, k :: v, k' :: v', h => by
    have ih := prod_nrm_zipSub_le (L := L) (v := v) (v' := v') (fun pb hpb => h pb (List.mem_cons_of_mem _ hpb))
    have hp : 1 ≤ p := h (p, b) List.mem_cons_self
    simp only [zipSub, List.zipWith_cons_cons, List.zip_cons_cons, List.map_cons, List.prod_cons, nrm, normOf] at ih ⊢
    have hpow : p ^ (k - k').natAbs ≤ p ^ k.natAbs * p ^ k'.natAbs := by
      rw [← pow_add]; exact Nat.pow_le_pow_right hp (by omega)
    calc p ^ (k - k').natAbs * (List.map nrm (L.zip (List.zipWith (· - ·) v v'))).prod
        ≤ (p ^ k.natAbs * p ^ k'.natAbs) * (normOf L v * normOf L v') := Nat.mul_le_mul hpow ih
      _ = p ^ k.natAbs * normOf L v * (p ^ k'.natAbs * normOf L v') := by ring

theorem cls_zipSub {P : ℕ → (Ideal (𝓞 K))⁰} : ∀ {L : List (ℕ × Bool)} {v v' : List ℤ},
    v.length = L.length → v'.length = L.length →
    ((zipSub L v v').map (cls P)).prod = ((L.zip v).map (cls P)).prod * (((L.zip v').map (cls P)).prod)⁻¹
  | [], [], [], _, _ => by simp [zipSub]
  | (p, b) :: L, k :: v, k' :: v', h, h' => by
    have ih := cls_zipSub (P := P) (L := L) (v := v) (v' := v') (by simpa using h) (by simpa using h')
    simp only [zipSub, List.zipWith_cons_cons, List.zip_cons_cons, List.map_cons, List.prod_cons, cls] at ih ⊢
    rw [ih, zpow_sub, mul_inv]
    ac_rfl
  | [], _ :: _, _, h, _ => by simp at h
  | _ :: _, [], _, h, _ => by simp at h
  | [], [], _ :: _, _, h' => by simp at h'
  | _ :: _, _ :: _, [], _, h' => by simp at h'

theorem zipSub_mem {L : List (ℕ × Bool)} {v v' : List ℤ} : ∀ z ∈ zipSub L v v', z.1 ∈ L := by
  intro z hz
  exact (List.of_mem_zip hz).1

theorem zipSub_map_fst : ∀ {L : List (ℕ × Bool)} {v v' : List ℤ},
    v.length = L.length → v'.length = L.length → (zipSub L v v').map (·.1.1) = L.map (·.1)
  | [], [], [], _, _ => by simp [zipSub]
  | (p, b) :: L, k :: v, k' :: v', h, h' => by
    have ih := zipSub_map_fst (L := L) (v := v) (v' := v') (by simpa using h) (by simpa using h')
    simp only [zipSub, List.zipWith_cons_cons, List.zip_cons_cons, List.map_cons] at ih ⊢
    rw [ih]
  | [], _ :: _, _, h, _ => by simp at h
  | _ :: _, [], _, h, _ => by simp at h
  | [], [], _ :: _, _, h' => by simp at h'
  | _ :: _, _ :: _, [], _, h' => by simp at h'

theorem zipSub_ram : ∀ {L : List (ℕ × Bool)} {v v' : List ℤ}, Adm L v → Adm L v' →
    ∀ z ∈ zipSub L v v', z.1.2 = false → z.2.natAbs ≤ 1
  | [], [], [], _, _, z, hz, _ => by simp [zipSub] at hz
  | (p, b) :: L, k :: v, k' :: v', ⟨hk, ha⟩, ⟨hk', ha'⟩, z, hz, hb => by
    simp only [zipSub, List.zipWith_cons_cons, List.zip_cons_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · simp only at hb ⊢
      rcases hk hb with rfl | rfl <;> rcases hk' hb with rfl | rfl <;> simp
    · exact zipSub_ram ha ha' z hz hb
  | [], _ :: _, _, h, _, _, _, _ => h.elim
  | _ :: _, [], _, h, _, _, _, _ => h.elim
  | [], [], _ :: _, _, h', _, _, _ => h'.elim
  | _ :: _, _ :: _, [], _, h', _, _, _ => h'.elim

theorem zipSub_ne : ∀ {L : List (ℕ × Bool)} {v v' : List ℤ},
    v.length = L.length → v'.length = L.length → v ≠ v' → ∃ z ∈ zipSub L v v', z.2 ≠ 0
  | [], [], [], _, _, hne => (hne rfl).elim
  | (p, b) :: L, k :: v, k' :: v', h, h', hne => by
    by_cases hk : k = k'
    · subst hk
      have hne' : v ≠ v' := fun h => hne (by rw [h])
      obtain ⟨z, hz, hz0⟩ := zipSub_ne (L := L) (by simpa using h) (by simpa using h') hne'
      exact ⟨z, by simp only [zipSub, List.zipWith_cons_cons, List.zip_cons_cons, List.mem_cons]; exact Or.inr hz, hz0⟩
    · exact ⟨((p, b), k - k'), by simp [zipSub], by simp only; omega⟩
  | [], _ :: _, _, h, _, _ => by simp at h
  | _ :: _, [], _, h, _, _ => by simp at h
  | [], [], _ :: _, _, h', _ => by simp at h'
  | _ :: _, _ :: _, [], _, h', _ => by simp at h'

/-! ### The count is at most the class number -/

section Count

variable {t c : ℕ} (D : CN1.Finite.QuadInt K (t : ℤ) (c : ℤ))
variable (P J : ℕ → (Ideal (𝓞 K))⁰)

include D in
/-- **Distinct counted vectors have distinct classes.** -/
theorem cls_injOn (htc : t * t < 4 * c) {L : List (ℕ × Bool)} (hF : Fam P J L) (hnd : (L.map (·.1)).Nodup)
    {Y : ℕ} (hY : 4 * (Y * Y) < 4 * c - t * t) (hY1 : 1 ≤ Y) {v v' : List ℤ}
    (hv : v ∈ vecs L Y) (hv' : v' ∈ vecs L Y)
    (h : ((L.zip v).map (cls P)).prod = ((L.zip v').map (cls P)).prod) : v = v' := by
  by_contra hne
  have ha := adm_vecs L Y v hv
  have ha' := adm_vecs L Y v' hv'
  have hl := adm_length ha
  have hl' := adm_length ha'
  set Z := zipSub L v v'
  have hZL : ∀ z ∈ Z, z.1 ∈ L := zipSub_mem
  have hcls : (Z.map (cls P)).prod = 1 := by
    rw [cls_zipSub hl hl', h, mul_inv_cancel]
  have hsmall : 4 * (Z.map nrm).prod < 4 * c - t * t := by
    have h1 : (Z.map nrm).prod ≤ normOf L v * normOf L v' :=
      prod_nrm_zipSub_le (fun pb hpb => (hF.prime pb hpb).one_lt.le)
    have h2 := norm_vecs L Y hY1 v hv
    have h3 := norm_vecs L Y hY1 v' hv'
    have : normOf L v * normOf L v' ≤ Y * Y := Nat.mul_le_mul h2 h3
    omega
  have hmem : ((Z.map (fac P J)).prod : Ideal (𝓞 K)) ∈ (Ideal (𝓞 K))⁰ := ((Z.map (fac P J)).prod).2
  apply not_isPrincipal D P J htc hF Z hZL (by rw [zipSub_map_fst hl hl']; exact hnd)
    (zipSub_ram ha ha') (zipSub_ne hl hl' hne) hsmall
  rw [← ClassGroup.mk0_eq_one_iff hmem]
  have : ClassGroup.mk0 (Z.map (fac P J)).prod = 1 := by rw [mk0_prod_fac P J hF Z hZL, hcls]
  have e : (⟨((Z.map (fac P J)).prod : Ideal (𝓞 K)), hmem⟩ : (Ideal (𝓞 K))⁰) = (Z.map (fac P J)).prod :=
    Subtype.coe_eta _ _
  rw [e]
  exact this

include D in
/-- **The count is at most the class number**, for a valid family. -/
theorem mu_le_classNumber_of_fam (htc : t * t < 4 * c) {L : List (ℕ × Bool)} (hF : Fam P J L)
    (hnd : (L.map (·.1)).Nodup) {Y : ℕ} (hY : 4 * (Y * Y) < 4 * c - t * t) :
    mu L Y ≤ classNumber K := by
  classical
  rcases Nat.eq_zero_or_pos Y with rfl | hY1
  · -- `mu L 0 = 1`
    have h0 : ∀ L : List (ℕ × Bool), (∀ pb ∈ L, 1 ≤ pb.1) → mu L 0 = 1 := by
      intro L
      induction L with
      | nil => intro _; rfl
      | cons pb L ih =>
        intro hL
        obtain ⟨p, b⟩ := pb
        have hp : 1 ≤ p := hL (p, b) List.mem_cons_self
        have ih' := ih (fun pb hpb => hL pb (List.mem_cons_of_mem _ hpb))
        cases b
        · simp [mu, ih']; omega
        · simp [mu, ih', powSum]; omega
    rw [h0 L (fun pb hpb => (hF.prime pb hpb).one_lt.le)]
    exact Nat.one_le_iff_ne_zero.mpr (Fintype.card_ne_zero)
  · rw [← length_vecs]
    have hnodup : ((vecs L Y).map (fun v => ((L.zip v).map (cls P)).prod)).Nodup :=
      (nodup_vecs L Y).map_on (fun v hv v' hv' h => cls_injOn D P J htc hF hnd hY hY1 hv hv' h)
    have := hnodup.length_le_card
    rw [List.length_map] at this
    exact this

end Count

end BoundariesOfClass.Sieve
