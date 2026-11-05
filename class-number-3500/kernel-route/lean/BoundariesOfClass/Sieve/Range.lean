import Mathlib
import BoundariesOfClass.Sieve.Check

/-!
# Kernel-checked ranges of radicands

`allRange f f lo n` checks `f m = true` for every `m` with `lo ≤ m < lo + n`, splitting the range in halves down to
blocks of at most `64`, with fuel `f` for the depth. Splitting keeps the loop variable a literal in the kernel: a
linear loop that passes `m + 1` along evaluates it lazily, and its cost grows faster than the length of the range.
`allRange_sound` is the soundness statement, proved once.

`rangeOK N YA YB A B P1 P E` is the per-radicand predicate of a range certificate: `m` is excluded (`m ∈ E`), or
`dOf m` lies outside `[A, B)`, or the sieve check passes, with bound `YA` when `m ≡ 3 (mod 4)` (`dOf m = m`) and `YB`
otherwise (`dOf m = 4m`). The check is tried first with a short list of small primes `P1`, which settles most
radicands cheaply, and then with the full list `P`. `lt_classNumber_of_rangeOK` turns it into `N < h`.
-/

namespace BoundariesOfClass.Sieve

/-- Linear check of `g m` for `n` consecutive values from `m`. -/
def allBlock (g : ℕ → Bool) : ℕ → ℕ → Bool
  | 0, _ => true
  | n + 1, m => g m && allBlock g n (m + 1)

/-- Binary-split check of `g m` for `lo ≤ m < lo + n`, with depth fuel. -/
def allRange (g : ℕ → Bool) : ℕ → ℕ → ℕ → Bool
  | 0, lo, n => allBlock g n lo
  | f + 1, lo, n =>
    cond (Nat.ble n 64) (allBlock g n lo)
      (allRange g f lo (Nat.div n 2) && allRange g f (Nat.add lo (Nat.div n 2)) (Nat.sub n (Nat.div n 2)))

theorem allBlock_sound {g : ℕ → Bool} : ∀ {n m : ℕ}, allBlock g n m = true → ∀ k, m ≤ k → k < m + n → g k = true
  | 0, _, _, k, h1, h2 => by omega
  | n + 1, m, h, k, h1, h2 => by
    simp only [allBlock, Bool.and_eq_true] at h
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · exact h.1
    · exact allBlock_sound h.2 k (by omega) (by omega)

theorem allRange_sound {g : ℕ → Bool} : ∀ {f lo n : ℕ}, allRange g f lo n = true →
    ∀ k, lo ≤ k → k < lo + n → g k = true
  | 0, lo, n, h => allBlock_sound h
  | f + 1, lo, n, h => by
    intro k h1 h2
    unfold allRange at h
    cases hb : Nat.ble n 64
    · rw [hb, cond_false, Bool.and_eq_true] at h
      have e1 : Nat.add lo (Nat.div n 2) = lo + n / 2 := rfl
      have e2 : Nat.sub n (Nat.div n 2) = n - n / 2 := rfl
      rw [e1, e2] at h
      by_cases hk : k < lo + n / 2
      · exact allRange_sound h.1 k h1 hk
      · exact allRange_sound h.2 k (by omega) (by omega)
    · rw [hb, cond_true] at h
      exact allBlock_sound h k h1 h2

/-- A square factor `k² ∣ m` with `k ≥ 2` refutes squarefreeness. -/
theorem not_squarefree_of_mod {m k : ℕ} (hk : 2 ≤ k) (h : m % (k * k) = 0) : ¬ Squarefree m := by
  intro hm
  have := hm k (Nat.dvd_of_mod_eq_zero h)
  rw [Nat.isUnit_iff] at this
  omega

/-- **The per-radicand predicate of a range certificate.** -/
def rangeOK (N YA YB A B : ℕ) (P1 P : List (ℕ × ℕ)) (E : List ℕ) (m : ℕ) : Bool :=
  E.elem m || Nat.blt (CN1.Finite.dOf m) A || Nat.ble B (CN1.Finite.dOf m) ||
    checkAt N (cond (Nat.beq (Nat.mod m 4) 3) YA YB) P1 m ||
    checkAt N (cond (Nat.beq (Nat.mod m 4) 3) YA YB) P m

/-- **Soundness of a range certificate.** -/
theorem lt_classNumber_of_rangeOK {K : Type*} [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
    {m : ℕ} (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K)) {N YA YB A B : ℕ} {P1 P : List (ℕ × ℕ)}
    {E : List ℕ} (hP1 : PrimesOK P1) (hP : PrimesOK P) (h : rangeOK N YA YB A B P1 P E m = true) (hE : m ∉ E)
    (hA : A ≤ CN1.Finite.dOf m) (hB : CN1.Finite.dOf m < B) : N < NumberField.classNumber K := by
  simp only [rangeOK, Bool.or_eq_true, List.elem_eq_mem, decide_eq_true_eq, Nat.blt_eq, Nat.ble_eq] at h
  rcases h with (((h | h) | h) | h) | h
  · exact absurd h hE
  · omega
  · omega
  · exact lt_classNumber_of_checkAt hK hm hsq hP1 h
  · exact lt_classNumber_of_checkAt hK hm hsq hP h

end BoundariesOfClass.Sieve
