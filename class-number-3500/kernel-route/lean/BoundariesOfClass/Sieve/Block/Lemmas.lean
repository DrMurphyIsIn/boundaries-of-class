import BoundariesOfClass.Sieve.Block.Defs

namespace BoundariesOfClass.Sieve.Block

open BoundariesOfClass.Sieve

/-! ### Items 1 and 2 -/

theorem testBit_rot {q B t j : ℕ} (hB : B < 2 ^ q) (ht : t < q) (hj : j < q) :
    (rot q B t).testBit j = B.testBit ((j + t) % q) := by
  show (((B >>> t) ||| (B <<< (q - t))) &&& (2 ^ q - 1)).testBit j = _
  rw [Nat.testBit_land, Nat.testBit_lor, Nat.testBit_shiftRight, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  simp only [hj, decide_true, Bool.and_true]
  by_cases h : j + t < q
  · rw [Nat.mod_eq_of_lt h, Nat.add_comm t j]
    have : ¬ j ≥ q - t := by omega
    simp [this]
  · have hmod : (j + t) % q = j - (q - t) := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
    rw [hmod]
    have h1 : B.testBit (t + j) = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hB (Nat.pow_le_pow_right (by norm_num) (by omega)))
    have : j ≥ q - t := by omega
    simp [h1, this]


/-- The repunit `Σ_{i<k} 2^(q i)`. -/
def ru (q : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => 2 ^ (q * k) + ru q k

theorem ru_mul (q : ℕ) : ∀ k, (2 ^ q - 1) * ru q k = 2 ^ (q * k) - 1
  | 0 => by simp [ru]
  | k + 1 => by
    have ih := ru_mul q k
    have e : 2 ^ (q * (k + 1)) = 2 ^ q * 2 ^ (q * k) := by rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]
    show (2 ^ q - 1) * (2 ^ (q * k) + ru q k) = _
    rw [Nat.mul_add, ih, e, Nat.sub_mul, Nat.one_mul]
    have h1 : 1 ≤ 2 ^ (q * k) := Nat.one_le_two_pow
    have h3 : 2 ^ (q * k) ≤ 2 ^ q * 2 ^ (q * k) := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos q)
    generalize 2 ^ q * 2 ^ (q * k) = A at *
    omega

theorem mul_ru_lt {q P : ℕ} (hP : P < 2 ^ q) (k : ℕ) : P * ru q k < 2 ^ (q * k) := by
  have h := ru_mul q k
  have hle : P * ru q k ≤ (2 ^ q - 1) * ru q k := Nat.mul_le_mul_right _ (by omega)
  have : 1 ≤ 2 ^ (q * k) := Nat.one_le_two_pow
  omega

theorem testBit_mul_ru {q P : ℕ} (hq : 0 < q) (hP : P < 2 ^ q) :
    ∀ k n, n < q * k → (P * ru q k).testBit n = P.testBit (n % q)
  | 0, n, hn => by simp at hn
  | k + 1, n, hn => by
    have e : P * ru q (k + 1) = 2 ^ (q * k) * P + P * ru q k := by
      show P * (2 ^ (q * k) + ru q k) = _
      rw [Nat.mul_add, Nat.mul_comm P]
    rw [e, Nat.testBit_two_pow_mul_add _ (mul_ru_lt hP k)]
    by_cases h : n < q * k
    · rw [if_pos h]; exact testBit_mul_ru hq hP k n h
    · rw [if_neg h]
      have hlt : n - q * k < q := by rw [Nat.mul_succ] at hn; omega
      have hm : n % q = n - q * k := by
        conv_lhs => rw [show n = (n - q * k) + q * k by omega]
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
      rw [hm]

theorem testBit_rep {L q P i : ℕ} (hq : 0 < q) (hP : P < 2 ^ q) (hi : i < L) :
    (rep L q P).testBit i = P.testBit (i % q) := by
  have hpos : 0 < 2 ^ q - 1 := by
    have : 2 ≤ 2 ^ q := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) hq
    omega
  have hdiv : (2 ^ (q * ((L + q - 1) / q)) - 1) / (2 ^ q - 1) = ru q ((L + q - 1) / q) := by
    rw [← ru_mul q]; exact Nat.mul_div_cancel_left _ hpos
  show ((P * ((2 ^ (q * ((L + q - 1) / q)) - 1) / (2 ^ q - 1))) &&& (2 ^ L - 1)).testBit i = _
  rw [hdiv, Nat.testBit_land, Nat.testBit_two_pow_sub_one]
  have hL : L ≤ q * ((L + q - 1) / q) := by
    have h1 := Nat.div_add_mod (L + q - 1) q
    have h2 := Nat.mod_lt (L + q - 1) hq
    omega
  simp only [hi, decide_true, Bool.and_true]
  exact testBit_mul_ru hq hP _ i (by omega)


/-! ### Item 4: a mask bit gives a split prime -/

theorem rot_lt (q B t : ℕ) : rot q B t < 2 ^ q := by
  show ((B >>> t) ||| (B <<< (q - t))) &&& (2 ^ q - 1) < 2 ^ q
  rw [Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_lt _ (Nat.two_pow_pos q)

theorem four_mul_inv4 {q : ℕ} (hodd : q % 2 = 1) : (4 : ZMod q) * ((inv4 q : ℕ) : ZMod q) = 1 := by
  have h2 : 2 * ((q + 1) / 2) = q + 1 := by omega
  have h1 : (2 : ZMod q) * (((q + 1) / 2 : ℕ) : ZMod q) = 1 := by
    have : ((2 * ((q + 1) / 2) : ℕ) : ZMod q) = 1 := by rw [h2]; push_cast; rw [ZMod.natCast_self, zero_add]
    exact_mod_cast this
  unfold inv4
  rw [ZMod.natCast_mod, Nat.cast_mul]
  calc (4 : ZMod q) * ((((q + 1) / 2 : ℕ) : ZMod q) * (((q + 1) / 2 : ℕ) : ZMod q))
      = ((2 : ZMod q) * (((q + 1) / 2 : ℕ) : ZMod q)) ^ 2 := by ring
    _ = 1 := by rw [h1]; ring

theorem testBit_maskOf {L m0 q B i : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hB : BaseOK q B) (hi : i < L) :
    (maskOf L m0 q B).testBit i = true →
      (¬ q ∣ m0 + 4 * i ∧ ∃ s : ℕ, q ∣ s ^ 2 + (m0 + 4 * i)) := by
  intro h
  have hq0 : 0 < q := hq.pos
  unfold maskOf at h
  rw [testBit_rep hq0 (rot_lt _ _ _) hi, testBit_rot hB.1 (Nat.mod_lt _ hq0) (Nat.mod_lt _ hq0)] at h
  set j := (i % q + m0 * inv4 q % q) % q with hj
  have hjq : j < q := Nat.mod_lt _ hq0
  obtain ⟨hnd, y, -, hyy⟩ := hB.2 j hjq h
  have hodd : q % 2 = 1 := Nat.odd_iff.mp (hq.odd_of_ne_two hq2)
  have hkey : ((4 * j : ℕ) : ZMod q) = ((m0 + 4 * i : ℕ) : ZMod q) := by
    have hinv := four_mul_inv4 hodd
    rw [hj]
    push_cast [ZMod.natCast_mod]
    linear_combination (m0 : ZMod q) * hinv
  have hq3 : 3 ≤ q := by have := hq.two_le; omega
  have hle : 4 * j ≤ q * q := by nlinarith
  constructor
  · intro hd
    apply hnd
    rw [← ZMod.natCast_eq_zero_iff] at hd ⊢
    rw [hkey]; exact hd
  · refine ⟨y, ?_⟩
    rw [← ZMod.natCast_eq_zero_iff]
    have hyy' : ((y * y : ℕ) : ZMod q) = ((q * q - 4 * j : ℕ) : ZMod q) :=
      (ZMod.natCast_eq_natCast_iff' _ _ q).mpr (by rw [hyy, Nat.mod_mod])
    calc ((y ^ 2 + (m0 + 4 * i) : ℕ) : ZMod q) = ((y * y : ℕ) : ZMod q) + ((4 * j : ℕ) : ZMod q) := by
          rw [hkey]; push_cast; ring
      _ = ((q * q - 4 * j : ℕ) : ZMod q) + ((4 * j : ℕ) : ZMod q) := by rw [hyy']
      _ = ((q * q : ℕ) : ZMod q) := by rw [← Nat.cast_add, Nat.sub_add_cancel hle]
      _ = 0 := by rw [Nat.cast_mul, ZMod.natCast_self, zero_mul]

/-! ### The reference pattern -/

theorem testBit_basePatAux (q sq : ℕ) : ∀ (n acc s : ℕ), (basePatAux q sq n acc).testBit s = true →
    acc.testBit s = true ∨ (s < n ∧ 4 * s % q ≠ 0 ∧ (sq >>> ((q * q - 4 * s) % q)) % 2 = 1)
  | 0, acc, s, h => Or.inl h
  | n + 1, acc, s, h => by
    rcases testBit_basePatAux q sq n _ s h with h' | h'
    · simp only [cond_beq] at h'
      split_ifs at h' with h1 h2
      · exact Or.inl h'
      · have h'' : (acc ||| 1 <<< n).testBit s = true := h'
        rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq] at h''
        rcases h'' with h'' | rfl
        · exact Or.inl h''
        · exact Or.inr ⟨by omega, h1, h2⟩
      · exact Or.inl h'
    · exact Or.inr ⟨by omega, h'.2⟩

theorem basePatAux_lt (q sq : ℕ) : ∀ (n acc : ℕ), n ≤ q → acc < 2 ^ q → basePatAux q sq n acc < 2 ^ q
  | 0, acc, _, h => h
  | n + 1, acc, hn, h => by
    apply basePatAux_lt q sq n _ (by omega)
    simp only [cond_beq]
    split_ifs
    · exact h
    · show acc ||| 1 <<< n < 2 ^ q
      rw [Nat.one_shiftLeft]
      exact Nat.or_lt_two_pow h (Nat.pow_lt_pow_right (by norm_num) (by omega))
    · exact h

theorem baseOK_basePat {q : ℕ} (hq : 0 < q) : BaseOK q (basePat q) := by
  refine ⟨basePatAux_lt q _ q 0 le_rfl (Nat.two_pow_pos q), fun j _ h => ?_⟩
  rcases testBit_basePatAux q (sqMask q) q 0 j h with h0 | ⟨-, h1, h2⟩
  · simp at h0
  · exact ⟨fun hd => h1 (Nat.mod_eq_zero_of_dvd hd), maskOK_sqMask hq _ (Nat.mod_lt _ hq).le h2⟩

/-! ### √p-bounded trial division -/

theorem trialB_spec (p : ℕ) : ∀ (f k : ℕ), trialB p f k = true → ∀ m, k ≤ m → m * m ≤ p → p % m ≠ 0
  | 0, _, h => by simp [trialB] at h
  | f + 1, k, h => by
    intro m hkm hmm
    unfold trialB at h
    split_ifs at h with hk
    · exfalso
      have : k * k ≤ m * m := Nat.mul_le_mul hkm hkm
      omega
    · simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      rcases Nat.eq_or_lt_of_le hkm with rfl | hlt
      · exact h.1
      · exact trialB_spec p f (k + 1) h.2 m hlt hmm

theorem primeSqB_sound {p : ℕ} (h : primeSqB p = true) : p.Prime := by
  simp only [primeSqB, Bool.and_eq_true] at h
  refine Nat.prime_def_le_sqrt.mpr ⟨Nat.le_of_ble_eq_true h.1, fun m hm2 hms hd => ?_⟩
  exact trialB_spec p p 2 h.2 m hm2 (Nat.le_sqrt.mp hms) (Nat.mod_eq_zero_of_dvd hd)

/-! ### The shared table -/

theorem entries_of_chunkOKB {l : List (ℕ × ℕ)} (h : chunkOKB l = true) :
    ∀ qB ∈ l, qB.1.Prime ∧ qB.1 ≠ 2 ∧ BaseOK qB.1 qB.2 := by
  simp only [chunkOKB, Bool.and_eq_true, List.all_eq_true] at h
  intro qB hqB
  have h1 := h.1 qB hqB
  simp only [Bool.not_eq_true'] at h1
  obtain ⟨⟨hp, h2⟩, hB⟩ := h1
  have hp' := primeSqB_sound hp
  refine ⟨hp', fun he => by simp [he] at h2, ?_⟩
  rw [Nat.eq_of_beq_eq_true hB]
  exact baseOK_basePat hp'.pos

theorem pairwise_of_incr : ∀ {l : List ℕ}, incr l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | a :: l, h => by
    obtain ⟨ha, hl⟩ := incr_cons h
    exact List.pairwise_cons.mpr ⟨ha, pairwise_of_incr hl⟩

theorem patsOK_of_chunks {chunks : List (List (ℕ × ℕ))} (hc : ∀ l ∈ chunks, chunkOKB l = true)
    (hi : incr (chunks.flatten.map (·.1)) = true) : PatsOK chunks.flatten := by
  refine ⟨fun qB hqB => ?_, pairwise_of_incr hi⟩
  obtain ⟨l, hl, hqBl⟩ := List.mem_flatten.mp hqB
  exact entries_of_chunkOKB (hc l hl) qB hqBl

/-! ### Item 4a: splitting in family A -/

theorem two_mul_half {q : ℕ} (hodd : q % 2 = 1) : (2 : ZMod q) * (((q + 1) / 2 : ℕ) : ZMod q) = 1 := by
  have h2 : 2 * ((q + 1) / 2) = q + 1 := by omega
  have : ((2 * ((q + 1) / 2) : ℕ) : ZMod q) = 1 := by rw [h2]; push_cast; rw [ZMod.natCast_self, zero_add]
  exact_mod_cast this

theorem split_iff_root_A {q m : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hm : m % 4 = 3) :
    (∃ s : ℕ, q ∣ s ^ 2 + m) ↔ ∃ r : ℤ, (q : ℤ) ∣ r ^ 2 - 1 * r + ((m + 1) / 4 : ℕ) := by
  have := Fact.mk hq
  have hodd : q % 2 = 1 := Nat.odd_iff.mp (hq.odd_of_ne_two hq2)
  have hc4 : 4 * ((m + 1) / 4) = m + 1 := by omega
  generalize (m + 1) / 4 = c at hc4 ⊢
  have hc : (4 : ZMod q) * ((c : ℕ) : ZMod q) = (m : ZMod q) + 1 := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ZMod q)) hc4
  have h2ne : (2 : ZMod q) ≠ 0 := by
    intro h
    have : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).mp (by exact_mod_cast h)
    rcases (Nat.dvd_prime Nat.prime_two).mp this with h1 | h1
    · exact hq.one_lt.ne' h1
    · exact hq2 h1
  have h4ne : (4 : ZMod q) ≠ 0 := by
    have : (4 : ZMod q) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2ne h2ne
  constructor
  · rintro ⟨s, hs⟩
    have hs' : ((s : ZMod q)) ^ 2 + (m : ZMod q) = 0 := by
      have := (ZMod.natCast_eq_zero_iff _ q).mpr hs; push_cast at this; exact this
    have hh := two_mul_half hodd
    generalize (q + 1) / 2 = k at hh
    refine ⟨(1 + s) * (k : ℤ), ?_⟩
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    set h : ZMod q := ((k : ℕ) : ZMod q)
    have : (4 : ZMod q) * (((1 + s) * h) ^ 2 - 1 * ((1 + s) * h) + ((c : ℕ) : ZMod q)) = 0 := by
      linear_combination hs' + hc + ((1 + (s : ZMod q)) ^ 2 * (2 * h + 1) - 2 * (1 + (s : ZMod q))) * hh
    exact (mul_eq_zero.mp this).resolve_left h4ne
  · rintro ⟨r, hr⟩
    refine ⟨(2 * r - 1).natAbs, ?_⟩
    rw [← Int.natCast_dvd_natCast]
    push_cast
    rw [sq_abs, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hr' := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr hr
    push_cast at hr' ⊢
    linear_combination 4 * hr' - hc

theorem two_split_iff_A {m : ℕ} (hm : m % 4 = 3) :
    (m % 8 = 7) ↔ (¬ (2 : ℤ) ∣ 4 * ((m + 1) / 4 : ℕ) - 1 * 1 ∧
      ∃ r : ℤ, (2 : ℤ) ∣ r ^ 2 - 1 * r + ((m + 1) / 4 : ℕ)) := by
  constructor
  · intro h7
    refine ⟨by omega, 0, by simp; omega⟩
  · rintro ⟨-, r, hr⟩
    have he : (2 : ℤ) ∣ r ^ 2 - 1 * r := by
      have := even_iff_two_dvd.mp (Int.even_mul_succ_self (r - 1))
      have e : (r - 1) * (r - 1 + 1) = r ^ 2 - 1 * r := by ring
      rwa [e] at this
    have hc : (2 : ℤ) ∣ (((m + 1) / 4 : ℕ) : ℤ) := by
      have := dvd_sub hr he
      simpa using this
    omega

/-! ### Item 2b: NSQ -/

theorem testBit_foldl_lor (L m0 i : ℕ) : ∀ (sqps : List ℕ) (acc : ℕ),
    (sqps.foldl (fun acc p => Nat.lor acc (nsqOf L m0 p)) acc).testBit i = true →
      acc.testBit i = true ∨ ∃ p ∈ sqps, (nsqOf L m0 p).testBit i = true
  | [], acc, h => Or.inl h
  | p :: ps, acc, h => by
    rcases testBit_foldl_lor L m0 i ps _ h with h' | ⟨p', hp', h'⟩
    · have h'' : (acc ||| nsqOf L m0 p).testBit i = true := h'
      rw [Nat.testBit_or, Bool.or_eq_true] at h''
      rcases h'' with h'' | h''
      · exact Or.inl h''
      · exact Or.inr ⟨p, List.mem_cons_self .., h''⟩
    · exact Or.inr ⟨p', List.mem_cons_of_mem _ hp', h'⟩

theorem not_squarefree_of_NSQ {L m0 i : ℕ} {sqps : List ℕ} (h3 : ∀ p ∈ sqps, 3 ≤ p ∧ p % 2 = 1) (hi : i < L)
    (h : (NSQ L m0 sqps).testBit i = true) : ¬ Squarefree (m0 + 4 * i) := by
  rcases testBit_foldl_lor L m0 i sqps 0 h with h0 | ⟨p, hp, hb⟩
  · simp at h0
  obtain ⟨hp3, hpodd⟩ := h3 p hp
  have hpp : 0 < p * p := Nat.mul_pos (by omega) (by omega)
  have hodd : (p * p) % 2 = 1 := by rw [Nat.mul_mod, hpodd]
  have hj0 : j0Of m0 p < p * p := Nat.mod_lt _ hpp
  -- the lane is ≡ j0 (mod p²)
  have hij : ((i : ℕ) : ZMod (p * p)) = ((j0Of m0 p : ℕ) : ZMod (p * p)) := by
    unfold nsqOf at hb
    split_ifs at hb with h1 h2
    · rw [testBit_rep hpp (Nat.pow_lt_pow_right (by norm_num) hj0) hi, Nat.testBit_two_pow,
        decide_eq_true_eq] at hb
      rw [hb, ZMod.natCast_mod]
    · rw [Nat.testBit_two_pow, decide_eq_true_eq] at hb
      rw [hb]
    · simp at hb
  have hle : m0 % (p * p) ≤ p * p := (Nat.mod_lt _ hpp).le
  have hj : ((j0Of m0 p : ℕ) : ZMod (p * p)) = -(m0 : ZMod (p * p)) * ((inv4 (p * p) : ℕ) : ZMod (p * p)) := by
    show (((p * p - m0 % (p * p)) * inv4 (p * p) % (p * p) : ℕ) : ZMod (p * p)) = _
    rw [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_sub hle, ZMod.natCast_self, ZMod.natCast_mod, zero_sub]
  have hz : ((m0 + 4 * i : ℕ) : ZMod (p * p)) = 0 := by
    push_cast
    rw [hij, hj]
    linear_combination (-(m0 : ZMod (p * p))) * four_mul_inv4 hodd
  have hd : p * p ∣ m0 + 4 * i := (ZMod.natCast_eq_zero_iff _ _).mp hz
  intro hsq
  have := Nat.isUnit_iff.mp (hsq p hd)
  omega


/-! ### Items 5 and 6: the bit-sliced counter, one lane at a time -/

section Lane

variable (i : ℕ)

theorem tb_land (a b : ℕ) : (Nat.land a b).testBit i = (a.testBit i && b.testBit i) := Nat.testBit_and a b i
theorem tb_lor (a b : ℕ) : (Nat.lor a b).testBit i = (a.testBit i || b.testBit i) := Nat.testBit_or a b i
theorem tb_xor (a b : ℕ) : (Nat.xor a b).testBit i = (a.testBit i ^^ b.testBit i) := Nat.testBit_xor a b i

theorem addFrom_length : ∀ (ps : List ℕ) (k c : ℕ), (addFrom ps k c).1.length = ps.length
  | [], _, _ => rfl
  | _ :: ps, 0, c => by simp [addFrom, addFrom_length ps 0]
  | _ :: ps, k + 1, c => by simp [addFrom, addFrom_length ps k]

/-- Ripple-carry addition, lane `i`, at or below the top plane. -/
theorem addFrom_val : ∀ (ps : List ℕ) (k c : ℕ), k ≤ ps.length →
    planesVal (addFrom ps k c).1 i + 2 ^ ps.length * ((addFrom ps k c).2.testBit i).toNat =
      planesVal ps i + (c.testBit i).toNat * 2 ^ k
  | [], k, c, hk => by
    have : k = 0 := by simpa using hk
    subst this; simp [addFrom, planesVal]
  | p :: ps, 0, c, _ => by
    have ih := addFrom_val ps 0 (Nat.land p c) (Nat.zero_le _)
    simp only [addFrom, planesVal, List.length_cons, pow_succ]
    generalize addFrom ps 0 (Nat.land p c) = r at ih ⊢
    rw [tb_land] at ih
    rw [tb_xor]
    generalize 2 ^ ps.length = P at ih ⊢
    cases hp : p.testBit i <;> cases hc : c.testBit i <;> cases hr : r.2.testBit i <;>
      simp [hp, hc, hr] at ih ⊢ <;> omega
  | p :: ps, k + 1, c, hk => by
    have ih := addFrom_val ps k c (by simpa using hk)
    simp only [addFrom, planesVal, List.length_cons] at ih ⊢
    rw [pow_succ, pow_succ]
    cases hc : c.testBit i <;> simp [hc] at ih ⊢ <;> nlinarith [ih]

/-- Above the top plane, the mask goes straight to the carry. -/
theorem addFrom_above : ∀ (ps : List ℕ) (k c : ℕ), ps.length ≤ k →
    planesVal (addFrom ps k c).1 i = planesVal ps i ∧ (addFrom ps k c).2 = c
  | [], _, _, _ => ⟨rfl, rfl⟩
  | _ :: _, 0, _, h => by simp at h
  | p :: ps, k + 1, c, h => by
    have ih := addFrom_above ps k c (by simpa using h)
    simp only [addFrom, planesVal]
    exact ⟨by rw [ih.1], ih.2⟩

/-- The lane invariant: either the sticky bit is set and the lane has counted at least `2^NP`, or the planes hold
exactly the count `t`. -/
def R (s : St) (t : ℕ) : Prop :=
  s.planes.length = NP ∧ (s.sticky.testBit i = true → 2 ^ NP ≤ t) ∧
    (s.sticky.testBit i = false → planesVal s.planes i = t)

theorem R_addSt {s : St} {t : ℕ} (h : R i s t) (M k : ℕ) :
    R i (addSt s M k) (t + (M.testBit i).toNat * 2 ^ k) := by
  obtain ⟨hlen, hst, hpl⟩ := h
  refine ⟨by simp [addSt, addFrom_length, hlen], ?_, ?_⟩ <;>
  · simp only [addSt, tb_lor, Bool.or_eq_true, Bool.or_eq_false_iff]
    rcases Nat.le_total k NP with hk | hk
    · have hv := addFrom_val i s.planes k M (hlen ▸ hk)
      rw [hlen] at hv
      cases hs : s.sticky.testBit i <;> cases hc : (addFrom s.planes k M).2.testBit i <;>
        simp [hs, hc] at hv hst hpl ⊢ <;> omega
    · have hv := addFrom_above i s.planes k M (hlen ▸ hk)
      have h2 : 2 ^ NP ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      rw [hv.2]
      cases hs : s.sticky.testBit i <;> cases hc : M.testBit i <;>
        simp [hs, hv.1] at hst hpl ⊢ <;> omega

/-- The lane value of a most-significant-first plane list. -/
def valHi : List ℕ → ℕ
  | [] => 0
  | p :: ps => (p.testBit i).toNat * 2 ^ ps.length + valHi ps

theorem valHi_append (p : ℕ) : ∀ l : List ℕ, valHi i (l ++ [p]) = 2 * valHi i l + (p.testBit i).toNat
  | [] => by simp [valHi]
  | a :: l => by
    simp only [List.cons_append, valHi, valHi_append p l, List.length_append, List.length_singleton, pow_succ]
    ring

theorem valHi_reverse : ∀ ps : List ℕ, valHi i ps.reverse = planesVal ps i
  | [] => rfl
  | p :: ps => by
    rw [List.reverse_cons, valHi_append, valHi_reverse ps, planesVal]
    cases p.testBit i <;> simp <;> ring

/-- The comparator, lane `i`: a set output bit means `gt`, or `eq` and lane value ≥ the low bits of `T`. -/
theorem geqFrom_spec (ALL T : ℕ) (hA : ALL.testBit i = true) : ∀ (ps : List ℕ) (gt eq j : ℕ), j = ps.length - 1 →
    (geqFrom ALL ps T gt eq j).testBit i = true →
      gt.testBit i = true ∨ (eq.testBit i = true ∧ T % 2 ^ ps.length ≤ valHi i ps)
  | [], gt, eq, j, _, h => by
    simp only [geqFrom, tb_lor, Bool.or_eq_true] at h
    simp only [List.length_nil, pow_zero, Nat.mod_one, zero_le, and_true]
    exact h
  | p :: ps, gt, eq, j, hj, h => by
    simp only [List.length_cons, Nat.add_sub_cancel] at hj
    subst hj
    have hT : T % 2 ^ (ps.length + 1) = T % 2 ^ ps.length + 2 ^ ps.length * (T / 2 ^ ps.length % 2) := by
      rw [pow_succ]; exact Nat.mod_mul
    have hlt : T % 2 ^ ps.length < 2 ^ ps.length := Nat.mod_lt _ (Nat.two_pow_pos _)
    have h2 : T / 2 ^ ps.length % 2 < 2 := Nat.mod_lt _ (by norm_num)
    unfold geqFrom at h
    simp only [List.length_cons, valHi]
    split_ifs at h with hb
    · rcases geqFrom_spec ALL T hA ps _ _ _ rfl h with h1 | ⟨h1, h1'⟩
      · exact Or.inl h1
      · rw [tb_land, Bool.and_eq_true] at h1
        refine Or.inr ⟨h1.1, ?_⟩
        rw [hT, hb, h1.2]; simp; omega
    · rcases geqFrom_spec ALL T hA ps _ _ _ rfl h with h1 | ⟨h1, h1'⟩
      · rw [tb_lor, tb_land, Bool.or_eq_true, Bool.and_eq_true] at h1
        rcases h1 with h1 | ⟨h1, h1p⟩
        · exact Or.inl h1
        · refine Or.inr ⟨h1, ?_⟩
          have hb0 : T / 2 ^ ps.length % 2 = 0 := by omega
          rw [hT, h1p, hb0]; simp; omega
      · rw [tb_land, tb_xor, hA, Bool.and_eq_true] at h1
        have hp : p.testBit i = false := by simpa using h1.2
        refine Or.inr ⟨h1.1, ?_⟩
        have hb0 : T / 2 ^ ps.length % 2 = 0 := by omega
        rw [hT, hp, hb0]; simp; omega

/-! ### The depth-first count is at most `mu` -/

/-- The lane's split list: the entries whose mask bit `i` is set, as split primes (as in `laneList`). -/
def lf (l : List (ℕ × ℕ)) : List (ℕ × Bool) :=
  (l.filter (fun qS : ℕ × ℕ => qS.2.testBit i)).map (fun qS : ℕ × ℕ => (qS.1, true))

theorem one_le_mu : ∀ (L : List (ℕ × Bool)) (Y : ℕ), 1 ≤ mu L Y
  | [], _ => by simp [mu]
  | (p, b) :: L, Y => by simp only [mu]; have := one_le_mu L Y; omega

theorem lf_cons (q S : ℕ) (rest : List (ℕ × ℕ)) :
    lf i ((q, S) :: rest) = if S.testBit i then (q, true) :: lf i rest else lf i rest := by
  unfold lf
  rw [List.filter_cons]
  split_ifs with h <;> simp_all

theorem dfs_bound (Yb : ℕ) (hYb : Yb < 2 ^ 64) : ∀ f : ℕ,
    (∀ (l : List (ℕ × ℕ)) (prod M k : ℕ) (s : St) (t : ℕ), R i s t → 0 < prod → (∀ e ∈ l, 2 ≤ e.1) →
      ∃ t', R i (dfsY Yb f l prod M k s) t' ∧
        t' + (M.testBit i).toNat * 2 ^ k ≤ t + (M.testBit i).toNat * 2 ^ k * mu (lf i l) (Yb / prod)) ∧
    (∀ (q M2 : ℕ) (rest : List (ℕ × ℕ)) (prod qq F k : ℕ) (s : St) (t : ℕ), R i s t → 0 < prod → 0 < qq →
      2 ≤ q → (∀ e ∈ rest, 2 ≤ e.1) → Yb / prod < qq * q ^ F →
      ∃ t', R i (powsY Yb f q M2 rest (prod * qq) k s) t' ∧
        t' ≤ t + (M2.testBit i).toNat * 2 ^ k * powSum (mu (lf i rest)) q F qq (Yb / prod))
  | 0 => by
    refine ⟨fun l prod M k s t hR _ _ => ⟨t, by simpa [dfsY] using hR, ?_⟩,
      fun q M2 rest prod qq F k s t hR _ _ _ _ _ => ⟨t, by simpa [powsY] using hR, by simp⟩⟩
    have := one_le_mu (lf i l) (Yb / prod)
    have : (M.testBit i).toNat * 2 ^ k ≤ (M.testBit i).toNat * 2 ^ k * mu (lf i l) (Yb / prod) :=
      Nat.le_mul_of_pos_right _ this
    omega
  | f + 1 => by
    obtain ⟨ihD, ihP⟩ := dfs_bound Yb hYb f
    refine ⟨fun l prod M k s t hR hprod hl => ?_, fun q M2 rest prod qq F k s t hR hprod hqq hq hrest hF => ?_⟩
    · have hbase : (M.testBit i).toNat * 2 ^ k ≤ (M.testBit i).toNat * 2 ^ k * mu (lf i l) (Yb / prod) :=
        Nat.le_mul_of_pos_right _ (one_le_mu _ _)
      match l, hl with
      | [], _ => exact ⟨t, by simpa [dfsY] using hR, by omega⟩
      | (q, S) :: rest, hl =>
        have hq : 2 ≤ q := hl (q, S) List.mem_cons_self
        have hrest : ∀ e ∈ rest, 2 ≤ e.1 := fun e he => hl e (List.mem_cons_of_mem _ he)
        simp only [dfsY]
        split_ifs with hlt
        · exact ⟨t, hR, by omega⟩
        · have hY' : Yb / prod < q * q ^ 64 := by
            have h1 : Yb / prod ≤ Yb := Nat.div_le_self _ _
            have h2 : 2 ^ 64 ≤ q ^ 64 := Nat.pow_le_pow_left hq 64
            have h3 : q ^ 64 ≤ q * q ^ 64 := Nat.le_mul_of_pos_left _ (by omega)
            omega
          obtain ⟨t1, hR1, ht1⟩ := ihP q (Nat.land M S) rest prod q 64 (k + 1) s t hR hprod (by omega) hq hrest hY'
          obtain ⟨t2, hR2, ht2⟩ := ihD rest prod M k _ t1 hR1 hprod hrest
          refine ⟨t2, hR2, ?_⟩
          rw [lf_cons]
          rw [tb_land] at ht1
          cases hS : S.testBit i
          · simp only [hS, Bool.and_false, Bool.toNat_false, zero_mul, add_zero, Bool.false_eq_true, ↓reduceIte] at ht1 ⊢
            omega
          · simp only [hS, Bool.and_true, ↓reduceIte, mu] at ht1 ⊢
            rw [pow_succ] at ht1
            nlinarith [ht1, ht2]
    · simp only [powsY]
      split_ifs with hlt
      · exact ⟨t, hR, by omega⟩
      · obtain ⟨F, rfl⟩ : ∃ F', F = F' + 1 := by
          rcases F with _ | F
          · exfalso
            have : Yb < qq * prod := (Nat.div_lt_iff_lt_mul hprod).mp (by simpa using hF)
            rw [Nat.mul_comm] at this; exact hlt this
          · exact ⟨F, rfl⟩
        have hge : qq ≤ Yb / prod := by
          rw [Nat.le_div_iff_mul_le hprod, Nat.mul_comm]; omega
        have hR1 := R_addSt i hR M2 k
        obtain ⟨t2, hR2, ht2⟩ := ihD rest (prod * qq) M2 k _ _ hR1 (Nat.mul_pos hprod hqq) hrest
        have hF' : Yb / prod < qq * q * q ^ F := by rw [pow_succ] at hF; linarith [hF, show qq * (q ^ F * q) = qq * q * q ^ F by ring]
        obtain ⟨t3, hR3, ht3⟩ := ihP q M2 rest prod (qq * q) F k _ t2 hR2 hprod (Nat.mul_pos hqq (by omega)) hq hrest hF'
        refine ⟨t3, by rw [← Nat.mul_assoc] at hR3; exact hR3, ?_⟩
        have hps : powSum (mu (lf i rest)) q (F + 1) qq (Yb / prod) =
            mu (lf i rest) (Yb / (prod * qq)) + powSum (mu (lf i rest)) q F (qq * q) (Yb / prod) := by
          simp only [powSum, Nat.not_lt.mpr hge, ↓reduceIte, Nat.div_div_eq_div_mul]
        rw [hps]
        nlinarith [ht2, ht3]

theorem planesVal_replicate : ∀ n : ℕ, planesVal (List.replicate n 0) i = 0
  | 0 => rfl
  | n + 1 => by simp [List.replicate_succ, planesVal, planesVal_replicate n]

theorem R_init : R i ⟨List.replicate NP 0, 0⟩ 0 :=
  ⟨by simp, by simp, fun _ => planesVal_replicate i NP⟩

theorem count1_bound {L Yb : ℕ} {masks : List (ℕ × ℕ)} {s : St} {t : ℕ} (hR : R i s t) (hi : i < L)
    (hm : ∀ e ∈ masks, 2 ≤ e.1) (hYb : Yb < 2 ^ 64) :
    ∃ t', R i (count1 L masks Yb s) t' ∧ t' ≤ t + mu (lf i masks) Yb := by
  have hA : (2 ^ L - 1).testBit i = true := by rw [Nat.testBit_two_pow_sub_one]; simp [hi]
  have h1 := R_addSt i hR (2 ^ L - 1) 0
  rw [hA] at h1
  obtain ⟨t', hR', ht'⟩ := (dfs_bound i Yb hYb 4000).1 masks 1 (2 ^ L - 1) 0 _ _ h1 Nat.one_pos hm
  refine ⟨t', hR', ?_⟩
  rw [hA] at ht'
  simp only [Bool.toNat_true, pow_zero, Nat.mul_one, Nat.div_one, Nat.one_mul] at ht'
  omega

end Lane

/-! ### The block: from a clear `uncertified` bit to `N < mu` -/

theorem blockOK_parts {b : Blk} (hb : blockOK b = true) :
    uncertified b = b.E ∧ b.N + 1 < 2 ^ NP ∧ (∀ p ∈ b.oddPrimes, 3 ≤ p ∧ p % 2 = 1) ∧
      (b.fam = 0 → 4 * (b.Y * b.Y) < b.m0 ∧ b.m0 % 4 = 3) ∧
      (b.fam ≠ 0 → b.Y * b.Y < b.m0 ∧ (b.m0 % 4 = 1 ∨ b.m0 % 4 = 2)) ∧ 2 ≤ b.Y := by
  simp only [blockOK, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq, List.all_eq_true,
    Bool.or_eq_true] at hb
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hb
  refine ⟨h1, h2, fun p hp => by simpa using h3 p hp, fun h0 => ?_, fun h0 => ?_, h5⟩
  · simp only [h0, ↓reduceIte, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h4; exact h4
  · simp only [h0, ↓reduceIte, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, Bool.or_eq_true] at h4; exact h4

theorem masksOf_ge_two {b : Blk} (hP : ∀ qB ∈ b.pats, qB.1.Prime) : ∀ e ∈ masksOf b, 2 ≤ e.1 := by
  intro e he
  simp only [masksOf, List.mem_append, List.mem_map] at he
  rcases he with he | ⟨qB, hqB, rfl⟩
  · split_ifs at he <;> simp_all
  · exact (hP qB hqB).two_le

theorem laneList_eq (b : Blk) (i : ℕ) :
    laneList b i = (if b.fam = 0 then [] else [(2, false)]) ++ lf i (masksOf b) := rfl

theorem finalSt_bound {b : Blk} {i : ℕ} (hi : i < b.L) (hm : ∀ e ∈ masksOf b, 2 ≤ e.1) (hY : b.Y < 2 ^ 64)
    (hY2 : 2 ≤ b.Y) : ∃ t, R i (finalSt b) t ∧ t ≤ mu (laneList b i) b.Y := by
  rw [laneList_eq]
  unfold finalSt
  split_ifs with h0
  · obtain ⟨t, hR, ht⟩ := count1_bound i (R_init i) hi hm hY
    exact ⟨t, hR, by simpa using ht⟩
  · obtain ⟨t1, hR1, ht1⟩ := count1_bound i (R_init i) hi hm hY
    obtain ⟨t2, hR2, ht2⟩ := count1_bound i hR1 hi hm (lt_of_le_of_lt (Nat.div_le_self _ _) hY)
    refine ⟨t2, hR2, ?_⟩
    simp only [List.nil_append, List.cons_append, mu, Bool.false_eq_true, ↓reduceIte, hY2]
    omega


/-- Items 5 and 6 (with the exponent bound `b.Y < 2 ^ 64`, which `mu`'s fuel 64 needs). -/
theorem lt_mu_of_not_uncertified {b : Blk} (hP : PatsOK b.pats) (hb : blockOK b = true) (hY : b.Y < 2 ^ 64)
    {i : ℕ} (hi : i < b.L) (hsq : Squarefree (b.m0 + 4 * i)) (hE : (uncertified b).testBit i = false) :
    b.N < mu (laneList b i) b.Y := by
  obtain ⟨-, hN, hodd, -, -, hY2⟩ := blockOK_parts hb
  have hm := masksOf_ge_two (fun qB h => (hP.1 qB h).1)
  obtain ⟨t, hR, ht⟩ := finalSt_bound hi hm hY hY2
  have hA : (2 ^ b.L - 1).testBit i = true := by rw [Nat.testBit_two_pow_sub_one]; simp [hi]
  have hns : (NSQ b.L b.m0 (sqps b)).testBit i = false := by
    by_contra h
    rw [Bool.not_eq_false] at h
    exact not_squarefree_of_NSQ (fun p hp => hodd p (List.mem_filter.mp hp).1) hi h hsq
  unfold uncertified at hE
  simp only [tb_land, tb_xor, tb_lor, hA, hns] at hE
  have hG : (geqFrom (2 ^ b.L - 1) (finalSt b).planes.reverse (b.N + 1) 0 (2 ^ b.L - 1) (NP - 1)).testBit i = true ∨
      (finalSt b).sticky.testBit i = true := by
    revert hE
    cases (geqFrom (2 ^ b.L - 1) (finalSt b).planes.reverse (b.N + 1) 0 (2 ^ b.L - 1) (NP - 1)).testBit i <;>
      cases (finalSt b).sticky.testBit i <;> simp
  obtain ⟨hlen, hst, hpl⟩ := hR
  rcases hG with hG | hG
  · rcases geqFrom_spec i _ _ hA _ _ _ _ (by simp [hlen]) hG with h0 | ⟨-, h1⟩
    · simp at h0
    · rw [valHi_reverse, List.length_reverse, hlen, Nat.mod_eq_of_lt hN] at h1
      cases hs : (finalSt b).sticky.testBit i
      · have := hpl hs; omega
      · have := hst hs; omega
  · have := hst hG; omega


/-! ### Item 7: the block theorem -/

theorem mask2_spec {L m0 i : ℕ} (hm : m0 % 4 = 3) (hi : i < L) (h : (mask2 L m0).testBit i = true) :
    (m0 + 4 * i) % 8 = 7 := by
  unfold mask2 at h
  have hP : (if m0 % 8 = 7 then 1 else 2) < 2 ^ 2 := by split_ifs <;> norm_num
  rw [testBit_rep (by norm_num) hP hi] at h
  have h2 : i % 2 = 0 ∨ i % 2 = 1 := Nat.mod_two_eq_zero_or_one i
  split_ifs at h with h7 <;> rcases h2 with h2 | h2 <;> rw [h2] at h <;>
    first | omega | (rw [Nat.testBit_eq_decide_div_mod_eq] at h; norm_num at h)

open CN1.Finite in
/-- Each listed lane prime splits (in `mu_le_classNumber`'s form) for `m = m0 + 4 i`. -/
theorem entry_split {b : Blk} (hP : PatsOK b.pats) (hb : blockOK b = true) {i : ℕ} (hi : i < b.L)
    {qS : ℕ × ℕ} (hq : qS ∈ masksOf b) (hbit : qS.2.testBit i = true) :
    qS.1.Prime ∧ ¬ (qS.1 : ℤ) ∣ 4 * ((cOf (b.m0 + 4 * i) : ℕ) : ℤ) -
        ((tOf (b.m0 + 4 * i) : ℕ) : ℤ) * ((tOf (b.m0 + 4 * i) : ℕ) : ℤ) ∧
      ∃ r : ℤ, (qS.1 : ℤ) ∣ r ^ 2 - ((tOf (b.m0 + 4 * i) : ℕ) : ℤ) * r + ((cOf (b.m0 + 4 * i) : ℕ) : ℤ) := by
  obtain ⟨-, -, -, hA, hB, -⟩ := blockOK_parts hb
  simp only [masksOf, List.mem_append, List.mem_map] at hq
  rcases hq with hq | ⟨qB, hqB, rfl⟩
  · split_ifs at hq with h0
    · simp only [List.mem_singleton] at hq
      subst hq
      have h7 := mask2_spec (hA h0).2 hi hbit
      have hm3 : (b.m0 + 4 * i) % 4 = 3 := by omega
      simp only [tOf, cOf, hm3, ↓reduceIte, Nat.cast_one]
      obtain ⟨h1, h2⟩ := (two_split_iff_A hm3).mp h7
      exact ⟨Nat.prime_two, by exact_mod_cast h1, by exact_mod_cast h2⟩
    · simp at hq
  · obtain ⟨hpr, hq2, hBOK⟩ := hP.1 qB hqB
    obtain ⟨hnd, s, hs⟩ := testBit_maskOf hpr hq2 hBOK hi hbit
    refine ⟨hpr, ?_⟩
    by_cases h0 : b.fam = 0
    · have hm3 : (b.m0 + 4 * i) % 4 = 3 := by have := (hA h0).2; omega
      simp only [tOf, cOf, hm3, ↓reduceIte, Nat.cast_one]
      have h4 : 4 * ((b.m0 + 4 * i + 1) / 4) = b.m0 + 4 * i + 1 := by omega
      have h4z : 4 * (((b.m0 + 4 * i + 1) / 4 : ℕ) : ℤ) - 1 * 1 = ((b.m0 + 4 * i : ℕ) : ℤ) := by
        have := congrArg (fun n : ℕ => (n : ℤ)) h4; push_cast at this ⊢; linarith
      refine ⟨?_, (split_iff_root_A hpr hq2 hm3).mp ⟨s, hs⟩⟩
      rw [h4z, Int.natCast_dvd_natCast]; exact hnd
    · have hm3 : (b.m0 + 4 * i) % 4 ≠ 3 := by have := (hB h0).2; omega
      simp only [tOf, cOf, hm3, ↓reduceIte, Nat.cast_zero, mul_zero, sub_zero, zero_mul]
      refine ⟨fun hd => ?_, s, by exact_mod_cast hs⟩
      have hd' : qB.1 ∣ 4 * (b.m0 + 4 * i) := by exact_mod_cast hd
      rcases (Nat.Prime.dvd_mul hpr).mp hd' with h | h
      · have : qB.1 ∣ 2 := hpr.dvd_of_dvd_pow (n := 2) (by simpa using h)
        exact hq2 ((Nat.prime_dvd_prime_iff_eq hpr Nat.prime_two).mp this)
      · exact hnd h

/-- Item 7 (with `b.Y < 2 ^ 64`). -/
theorem lt_classNumber_of_blockOK {K : Type*} [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
    {m : ℕ} (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K)) {b : Blk} (hP : PatsOK b.pats)
    (hb : blockOK b = true) (hY : b.Y < 2 ^ 64) (hlo : b.m0 ≤ m) (hhi : m < b.m0 + 4 * b.L)
    (hmod : m % 4 = b.m0 % 4) (hE : b.E.testBit ((m - b.m0) / 4) = false) :
    b.N < NumberField.classNumber K := by
  obtain ⟨hU, -, -, hA, hB, -⟩ := blockOK_parts hb
  have hmi : m = b.m0 + 4 * ((m - b.m0) / 4) := by omega
  have hi : (m - b.m0) / 4 < b.L := by omega
  generalize (m - b.m0) / 4 = i at hmi hi hE
  subst hmi
  have hlt := lt_mu_of_not_uncertified hP hb hY hi hm (by rw [hU]; exact hE)
  obtain ⟨α, hα⟩ := hsq
  have D := CN1.Finite.quadIntOfFoundations hK hm hα
  have htc := HCN.Finite.tOf_mul_lt_four_mul_cOf hm.ne_zero
  have hd : CN1.Finite.dOf (b.m0 + 4 * i) =
      4 * CN1.Finite.cOf (b.m0 + 4 * i) - CN1.Finite.tOf (b.m0 + 4 * i) * CN1.Finite.tOf (b.m0 + 4 * i) := by
    have := CN1.Finite.four_mul_cOf (b.m0 + 4 * i); rw [sq] at this; omega
  have hYd : 4 * (b.Y * b.Y) < 4 * CN1.Finite.cOf (b.m0 + 4 * i) -
      CN1.Finite.tOf (b.m0 + 4 * i) * CN1.Finite.tOf (b.m0 + 4 * i) := by
    rw [← hd]
    unfold CN1.Finite.dOf
    by_cases h0 : b.fam = 0
    · have := hA h0; split_ifs <;> omega
    · have := hB h0; split_ifs <;> omega
  refine lt_of_lt_of_le hlt (mu_le_classNumber D htc _ ?_ ?_ hYd)
  · intro pb hpb
    rw [laneList_eq] at hpb
    rcases List.mem_append.mp hpb with h2 | hlf
    · split_ifs at h2 with h0
      · simp at h2
      · simp only [List.mem_singleton] at h2
        subst h2
        have hm3 : (b.m0 + 4 * i) % 4 ≠ 3 := by have := (hB h0).2; omega
        refine ⟨Nat.prime_two, by simp, fun _ => ?_⟩
        simp only [CN1.Finite.tOf, CN1.Finite.cOf, hm3, ↓reduceIte, Nat.cast_zero, mul_zero, sub_zero]
        exact ⟨2 * ((b.m0 + 4 * i : ℕ) : ℤ), by push_cast; ring⟩
    · unfold lf at hlf
      simp only [List.mem_map, List.mem_filter] at hlf
      obtain ⟨qS, ⟨hqS, hbit⟩, rfl⟩ := hlf
      obtain ⟨hpr, hns, hr⟩ := entry_split hP hb hi hqS hbit
      exact ⟨hpr, fun _ => ⟨hns, hr⟩, fun h => by simp at h⟩
  · have hl : ((lf i (masksOf b)).map (·.1)).Sublist ((masksOf b).map (·.1)) := by
      have := (List.filter_sublist (p := fun qS : ℕ × ℕ => qS.2.testBit i) (l := masksOf b)).map (fun qS : ℕ × ℕ => qS.1)
      simpa [lf, List.map_map, Function.comp_def] using this
    have hmm : (masksOf b).map (·.1) = (if b.fam = 0 then [2] else []) ++ b.pats.map (·.1) := by
      unfold masksOf; split_ifs <;> simp [List.map_map, Function.comp_def]
    rw [hmm] at hl
    have hsub : ((laneList b i).map (·.1)).Sublist (2 :: b.pats.map (·.1)) := by
      rw [laneList_eq]
      split_ifs at hl ⊢ with h0
      · simpa using hl
      · simpa using hl.cons_cons 2
    refine hsub.nodup (List.nodup_cons.mpr ⟨fun h2 => ?_, hP.2.imp (fun h => ne_of_lt h)⟩)
    obtain ⟨qB, hqB, he⟩ := List.mem_map.mp h2
    exact (hP.1 qB hqB).2.1 he


/-! ### Item 8: the range assembly -/

/-- Item 8, with the (T) instance above `X_1000` as the hypothesis `hT` (the sieve project does not import
`BoundariesOfClass.Numerics`; the solution's main module discharges `hT` by
`BoundariesOfClass.Numerics.lt_classNumber_of_le_dOf_le_thousand`). The exponent bound `b.Y < 2 ^ 64` of items
5–7 is derived here from the range. -/
theorem dOf_le_or_mem_W18_of_classNumber_le_thousand {K : Type*} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) {m : ℕ} (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hm1 : m ≠ 1) (hm3 : m ≠ 3) {Bs : List Blk} (hB : ∀ b ∈ Bs, PatsOK b.pats ∧ blockOK b = true ∧ b.N = 1000)
    (hC : Covers Bs 227932027 1605000000) (hX : ExceptionsOK Bs)
    (hT : 1605000000 ≤ CN1.Finite.dOf m → 1000 < NumberField.classNumber K)
    (hcl : NumberField.classNumber K ≤ 1000) :
    CN1.Finite.dOf m ≤ 227932027 ∨ m ∈ W18 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hF, hW⟩ := hcon
  have hcl' : ¬ 1000 < NumberField.classNumber K := not_lt.mpr hcl
  by_cases hXr : 1605000000 ≤ CN1.Finite.dOf m
  · exact hcl' (hT hXr)
  push Not at hXr
  obtain ⟨b, hbB, hlo, hhi, hmod⟩ := hC m hm hm1 hm3 hF hXr
  obtain ⟨hP, hb, hN⟩ := hB b hbB
  have hY : b.Y < 2 ^ 64 := by
    obtain ⟨-, -, -, hA, hB', -⟩ := blockOK_parts hb
    have hmd := CN1.Finite.le_dOf m
    have hYY : b.Y * b.Y < 1605000000 := by
      by_cases h0 : b.fam = 0
      · have := hA h0; omega
      · have := hB' h0; omega
    by_contra hc
    push Not at hc
    have := Nat.mul_le_mul hc hc
    omega
  cases hE : b.E.testBit ((m - b.m0) / 4)
  · have := lt_classNumber_of_blockOK hK hm hsq hP hb hY hlo hhi hmod hE
    rw [hN] at this
    exact hcl' this
  · have hmi : b.m0 + 4 * ((m - b.m0) / 4) = m := by omega
    rcases hX b hbB ((m - b.m0) / 4) (by omega) hE (by rw [hmi]; exact hm) with hw | ⟨Y, P, hPOK, hck⟩
    · rw [hmi] at hw; exact hW hw
    · rw [hmi] at hck; exact hcl' (lt_classNumber_of_checkAt hK hm hsq hPOK hck)

end BoundariesOfClass.Sieve.Block
