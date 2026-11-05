import Mathlib

/-!
# The smooth-number count of the residue sieve

Let `L` be a list of primes, each tagged `true` (split) or `false` (ramified), and `Y` a bound. The count
`mu L Y` is the number of exponent vectors `v` (one integer per entry of `L`) with
`∏ p_i ^ |v_i| ≤ Y`, where a split entry takes any exponent in `ℤ` and a ramified entry takes `0` or `1`.
Grouping the vectors by `a = ∏ p_i ^ |v_i|`, it is `Σ_{a ≤ Y} 2^{ω_S(a)}` over the `a ≤ Y` built from the
listed primes, the ramified ones to the first power only, with `ω_S(a)` the number of split primes dividing
`a`. This is the lower bound for the class number in the sieve of Watkins, *Class numbers of imaginary
quadratic fields*, Math. Comp. 73 (2004), §8, in the form `μ_P(Y)` of Kimura (arXiv:2610.21511, §5.1) and
`W(Y)` of Jaswal (Zenodo 10.5281/zenodo.23251443, Lemma 3.3).

This file is pure combinatorics:
* `mu L Y`, computed by recursion on `L` (the kernel evaluates it);
* `vecs L Y`, the list of the exponent vectors, with `(vecs L Y).length = mu L Y` (`length_vecs`),
  `(vecs L Y).Nodup` (`nodup_vecs`), every member admissible (`adm_vecs`: one entry per prime, ramified
  entries in `{0, 1}`), and, for `1 ≤ Y`, every member of norm `normOf L v ≤ Y` (`norm_vecs`).

The number field enters in `BoundariesOfClass.Sieve.Soundness`, which maps `vecs L Y` injectively into the
class group when `4Y² < d`.

The exponent loop runs with fuel `64`. Fuel only cuts the count short, never adds to it, so every statement
here holds for any fuel; for `2 ≤ p` and `Y < 2^64` the fuel is never exhausted.
-/

namespace BoundariesOfClass.Sieve

/-- `powSum g p f q Y = Σ_{j ≥ 0, j < f, q·p^j ≤ Y} g (Y / (q·p^j))`, with fuel `f`. -/
def powSum (g : ℕ → ℕ) (p : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | f + 1, q, Y => if Y < q then 0 else g (Y / q) + powSum g p f (q * p) Y

/-- **The count.** `(p, true)` is a split prime (exponents `0, ±1, ±2, …`), `(p, false)` a ramified one
(exponents `0, 1`). -/
def mu : List (ℕ × Bool) → ℕ → ℕ
  | [], _ => 1
  | (p, b) :: L, Y =>
    mu L Y + if b then 2 * powSum (mu L) p 64 p Y else (if p ≤ Y then mu L (Y / p) else 0)

/-- The vectors with head `±j`, `j ≥ k`, `q = p^k`, fuel `f`, built from `g` on the remaining bound. -/
def powVecs (g : ℕ → List (List ℤ)) (p : ℕ) : ℕ → ℕ → ℕ → ℕ → List (List ℤ)
  | 0, _, _, _ => []
  | f + 1, k, q, Y =>
    if Y < q then []
    else ((g (Y / q)).map (((k : ℤ)) :: ·) ++ (g (Y / q)).map ((-(k : ℤ)) :: ·)) ++
      powVecs g p f (k + 1) (q * p) Y

/-- **The exponent vectors** counted by `mu`. -/
def vecs : List (ℕ × Bool) → ℕ → List (List ℤ)
  | [], _ => [[]]
  | (p, b) :: L, Y =>
    (vecs L Y).map ((0 : ℤ) :: ·) ++
      if b then powVecs (vecs L) p 64 1 p Y
      else (if p ≤ Y then (vecs L (Y / p)).map ((1 : ℤ) :: ·) else [])

/-- The norm `∏ p_i ^ |v_i|` of an exponent vector. -/
def normOf : List (ℕ × Bool) → List ℤ → ℕ
  | (p, _) :: L, k :: v => p ^ k.natAbs * normOf L v
  | _, _ => 1

/-- Admissible exponents: one per entry, ramified entries in `{0, 1}`. -/
def Adm : List (ℕ × Bool) → List ℤ → Prop
  | [], [] => True
  | (_, b) :: L, k :: v => (b = false → k = 0 ∨ k = 1) ∧ Adm L v
  | _, _ => False

/-! ### Length -/

theorem length_powVecs (g : ℕ → List (List ℤ)) (p : ℕ) :
    ∀ f k q Y, (powVecs g p f k q Y).length = 2 * powSum (fun y => (g y).length) p f q Y := by
  intro f
  induction f with
  | zero => intro k q Y; simp [powVecs, powSum]
  | succ f ih =>
    intro k q Y
    unfold powVecs powSum
    split_ifs
    · simp
    · simp only [List.length_append, List.length_map, ih]
      ring

theorem length_vecs : ∀ L Y, (vecs L Y).length = mu L Y
  | [], _ => by simp [vecs, mu]
  | (p, b) :: L, Y => by
    have ih : ∀ Y, (vecs L Y).length = mu L Y := fun Y => length_vecs L Y
    unfold vecs mu
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_map, ih]
      split_ifs <;> simp [ih]
    · simp only [↓reduceIte, List.length_append, List.length_map, ih, length_powVecs]

/-! ### Distinctness -/

theorem mem_powVecs {g : ℕ → List (List ℤ)} {p : ℕ} :
    ∀ {f k q Y v}, v ∈ powVecs g p f k q Y →
      ∃ j : ℕ, k ≤ j ∧ ∃ Y' ≤ Y, ∃ u ∈ g Y', (v = (j : ℤ) :: u ∨ v = (-(j : ℤ)) :: u) ∧
        q * p ^ (j - k) ≤ Y ∧ Y' = Y / (q * p ^ (j - k)) := by
  intro f
  induction f with
  | zero => intro k q Y v h; simp [powVecs] at h
  | succ f ih =>
    intro k q Y v h
    unfold powVecs at h
    split_ifs at h with hlt
    · simp at h
    · rcases List.mem_append.mp h with h | h
      · rcases List.mem_append.mp h with h | h
        · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp h
          exact ⟨k, le_rfl, Y / q, Nat.div_le_self _ _, u, hu, Or.inl rfl, by simpa using not_lt.mp hlt,
            by simp⟩
        · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp h
          exact ⟨k, le_rfl, Y / q, Nat.div_le_self _ _, u, hu, Or.inr rfl, by simpa using not_lt.mp hlt,
            by simp⟩
      · obtain ⟨j, hj, Y', hY', u, hu, hv, hq, hY'eq⟩ := ih h
        refine ⟨j, by omega, Y', hY', u, hu, hv, ?_, ?_⟩
        · have : q * p * p ^ (j - (k + 1)) = q * p ^ (j - k) := by
            rw [mul_assoc, ← pow_succ']
            congr 2
            omega
          rwa [this] at hq
        · have : q * p * p ^ (j - (k + 1)) = q * p ^ (j - k) := by
            rw [mul_assoc, ← pow_succ']
            congr 2
            omega
          rwa [this] at hY'eq

/-- The heads of the members of `powVecs … k …` are `±j` with `j ≥ k`. -/
theorem head_powVecs {g : ℕ → List (List ℤ)} {p f k q Y : ℕ} {v : List ℤ}
    (h : v ∈ powVecs g p f k q Y) : ∃ j : ℕ, k ≤ j ∧ ∃ u, v = (j : ℤ) :: u ∨ v = (-(j : ℤ)) :: u := by
  obtain ⟨j, hj, -, -, u, -, hv, -⟩ := mem_powVecs h
  exact ⟨j, hj, u, hv⟩

theorem nodup_map_cons {a : ℤ} {l : List (List ℤ)} (h : l.Nodup) : (l.map (a :: ·)).Nodup :=
  h.map (fun _ _ h => List.cons_injective h)

theorem nodup_powVecs {g : ℕ → List (List ℤ)} {p : ℕ} (hg : ∀ y, (g y).Nodup) :
    ∀ f k q Y, 1 ≤ k → (powVecs g p f k q Y).Nodup := by
  intro f
  induction f with
  | zero => intro k q Y _; simp [powVecs]
  | succ f ih =>
    intro k q Y hk
    unfold powVecs
    split_ifs
    · simp
    · rw [List.nodup_append]
      refine ⟨?_, ih _ _ _ (by omega), ?_⟩
      · rw [List.nodup_append]
        refine ⟨nodup_map_cons (hg _), nodup_map_cons (hg _), ?_⟩
        intro a ha b hb hab
        obtain ⟨u, -, rfl⟩ := List.mem_map.mp ha
        obtain ⟨u', -, rfl⟩ := List.mem_map.mp hb
        have := (List.cons_eq_cons.mp hab).1
        omega
      · intro a ha b hb hab
        obtain ⟨j, hj, u, hu⟩ := head_powVecs hb
        have hhead : ∃ u', a = (k : ℤ) :: u' ∨ a = (-(k : ℤ)) :: u' := by
          rcases List.mem_append.mp ha with ha | ha
          · obtain ⟨u', -, rfl⟩ := List.mem_map.mp ha; exact ⟨u', Or.inl rfl⟩
          · obtain ⟨u', -, rfl⟩ := List.mem_map.mp ha; exact ⟨u', Or.inr rfl⟩
        obtain ⟨u', hu'⟩ := hhead
        subst hab
        rcases hu' with rfl | rfl <;> rcases hu with h | h <;>
          · have := (List.cons_eq_cons.mp h).1; omega

theorem nodup_vecs : ∀ L Y, (vecs L Y).Nodup
  | [], _ => by simp [vecs]
  | (p, b) :: L, Y => by
    have ih : ∀ Y, (vecs L Y).Nodup := fun Y => nodup_vecs L Y
    unfold vecs
    rw [List.nodup_append]
    refine ⟨nodup_map_cons (ih Y), ?_, ?_⟩
    · cases b
      · simp only [Bool.false_eq_true, ↓reduceIte]
        split_ifs
        · exact nodup_map_cons (ih _)
        · simp
      · simpa using nodup_powVecs ih 64 1 p Y le_rfl
    · intro a ha c hc hac
      obtain ⟨u, -, rfl⟩ := List.mem_map.mp ha
      subst hac
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte] at hc
        split_ifs at hc
        · obtain ⟨u', -, hu'⟩ := List.mem_map.mp hc
          have := (List.cons_eq_cons.mp hu').1; omega
        · simp at hc
      · simp only [↓reduceIte] at hc
        obtain ⟨j, hj, u', hu'⟩ := head_powVecs hc
        rcases hu' with h | h <;>
          · have := (List.cons_eq_cons.mp h).1; omega

/-! ### Norm bound and admissibility -/

/-- **The members of `vecs L Y` are admissible.** -/
theorem adm_vecs : ∀ L Y, ∀ v ∈ vecs L Y, Adm L v
  | [], Y, v, hv => by
    simp only [vecs, List.mem_singleton] at hv
    subst hv
    trivial
  | (p, b) :: L, Y, v, hv => by
    have ih : ∀ Y, ∀ v ∈ vecs L Y, Adm L v := fun Y => adm_vecs L Y
    unfold vecs at hv
    rcases List.mem_append.mp hv with hv | hv
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
      exact ⟨fun _ => Or.inl rfl, ih Y u hu⟩
    · cases b
      · simp only [Bool.false_eq_true, ↓reduceIte] at hv
        split_ifs at hv with hpY
        · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
          exact ⟨fun _ => Or.inr rfl, ih _ u hu⟩
        · simp at hv
      · simp only [↓reduceIte] at hv
        obtain ⟨j, -, Y', -, u, hu, hvu, -, -⟩ := mem_powVecs hv
        rcases hvu with rfl | rfl
        · exact ⟨fun h => absurd h (by simp), ih Y' u hu⟩
        · exact ⟨fun h => absurd h (by simp), ih Y' u hu⟩

/-- `m * normOf L u ≤ Y` from `normOf L u ≤ Y / m` (or `m = 0`). -/
theorem mul_le_of_le_div {m n Y : ℕ} (h : n ≤ Y / m) : m * n ≤ Y :=
  (Nat.mul_le_mul_left m h).trans (Nat.mul_div_le Y m)

/-- **The members of `vecs L Y` have norm at most `Y`**, for `1 ≤ Y`. -/
theorem norm_vecs : ∀ L Y, 1 ≤ Y → ∀ v ∈ vecs L Y, normOf L v ≤ Y
  | [], Y, hY, v, hv => by
    simp only [vecs, List.mem_singleton] at hv
    subst hv
    simpa [normOf] using hY
  | (p, b) :: L, Y, hY, v, hv => by
    have ih : ∀ Y, 1 ≤ Y → ∀ v ∈ vecs L Y, normOf L v ≤ Y := fun Y => norm_vecs L Y
    unfold vecs at hv
    rcases List.mem_append.mp hv with hv | hv
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
      simpa [normOf] using ih Y hY u hu
    · cases b
      · simp only [Bool.false_eq_true, ↓reduceIte] at hv
        split_ifs at hv with hpY
        · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
          simp only [normOf, Int.natAbs_one, pow_one]
          rcases Nat.eq_zero_or_pos p with rfl | hp0
          · simp
          · exact mul_le_of_le_div (ih (Y / p) ((Nat.le_div_iff_mul_le hp0).mpr (by omega)) u hu)
        · simp at hv
      · simp only [↓reduceIte] at hv
        obtain ⟨j, hj, Y', -, u, hu, hvu, hq, rfl⟩ := mem_powVecs hv
        have hpj : p * p ^ (j - 1) = p ^ j := by
          rw [← pow_succ']; congr 1; omega
        rw [hpj] at hq
        have key : p ^ j * normOf L u ≤ Y := by
          rcases Nat.eq_zero_or_pos (p ^ j) with h0 | hpos
          · simp [h0]
          · rw [hpj] at hu
            exact mul_le_of_le_div (ih _ ((Nat.le_div_iff_mul_le hpos).mpr (by omega)) u hu)
        rcases hvu with rfl | rfl <;>
        · simpa only [normOf, Int.natAbs_neg, Int.natAbs_natCast] using key

/-! ### A capped count for the kernel

`muK cap L Y` is a lower bound for `mu L Y` (`muK_le_mu`) that the kernel evaluates cheaply: it answers `1` as soon as
`Y` is below the head prime, and stops adding once the count of the remaining list reaches `cap`. For a list of
increasing primes and `mu L Y < cap` the two agree, but only the inequality is used. It is written with `cond`,
`Nat.blt`, `Nat.ble`, `Nat.add`, `Nat.mul` and `Nat.div` so that the kernel does not unfold instances. -/

/-- `powSum` in kernel-friendly form. -/
def powSumR (g : ℕ → ℕ) (p : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | f + 1, q, Y => cond (Nat.blt Y q) 0 (Nat.add (g (Nat.div Y q)) (powSumR g p f (Nat.mul q p) Y))

/-- **The capped count.** -/
def muK (cap : ℕ) : List (ℕ × Bool) → ℕ → ℕ
  | [], _ => 1
  | (p, b) :: L, Y =>
    cond (Nat.blt Y p) 1
      (cond (Nat.ble cap (muK cap L Y)) (muK cap L Y)
        (Nat.add (muK cap L Y)
          (cond b (Nat.mul 2 (powSumR (muK cap L) p 64 p Y))
            (cond (Nat.ble p Y) (muK cap L (Nat.div Y p)) 0))))

theorem powSumR_le {g g' : ℕ → ℕ} (h : ∀ y, g y ≤ g' y) (p : ℕ) :
    ∀ f q Y, powSumR g p f q Y ≤ powSum g' p f q Y := by
  intro f
  induction f with
  | zero => intro q Y; simp [powSumR, powSum]
  | succ f ih =>
    intro q Y
    unfold powSumR powSum
    by_cases hY : Y < q
    · simp [Nat.blt_eq.mpr hY, hY]
    · have : Nat.blt Y q = false := Bool.eq_false_iff.mpr (fun h => hY (Nat.blt_eq.mp h))
      rw [this, Bool.cond_false, if_neg hY]
      exact Nat.add_le_add (h _) (ih _ _)

theorem one_le_mu : ∀ (L : List (ℕ × Bool)) (Y : ℕ), 1 ≤ mu L Y
  | [], _ => le_rfl
  | (_, _) :: L, Y => (one_le_mu L Y).trans (Nat.le_add_right _ _)

/-- **The capped count is a lower bound.** -/
theorem muK_le_mu (cap : ℕ) : ∀ (L : List (ℕ × Bool)) (Y : ℕ), muK cap L Y ≤ mu L Y
  | [], _ => le_rfl
  | (p, b) :: L, Y => by
    have ih : ∀ Y, muK cap L Y ≤ mu L Y := fun Y => muK_le_mu cap L Y
    unfold muK mu
    cases Nat.blt Y p
    · simp only [Bool.cond_false]
      cases Nat.ble cap (muK cap L Y)
      · simp only [Bool.cond_false]
        refine Nat.add_le_add (ih Y) ?_
        cases b
        · simp only [Bool.cond_false, Bool.false_eq_true, ↓reduceIte]
          by_cases hp : p ≤ Y
          · rw [show Nat.ble p Y = true from Nat.ble_eq.mpr hp, Bool.cond_true, if_pos hp]
            exact ih _
          · have : Nat.ble p Y = false := Bool.eq_false_iff.mpr (fun h => hp (Nat.ble_eq.mp h))
            simp [this, hp]
        · simp only [Bool.cond_true, ↓reduceIte]
          exact Nat.mul_le_mul_left 2 (powSumR_le ih p 64 p Y)
      · simp only [Bool.cond_true]
        exact (ih Y).trans (Nat.le_add_right _ _)
    · simp only [Bool.cond_true]
      exact (one_le_mu L Y).trans (Nat.le_add_right _ _)

end BoundariesOfClass.Sieve
