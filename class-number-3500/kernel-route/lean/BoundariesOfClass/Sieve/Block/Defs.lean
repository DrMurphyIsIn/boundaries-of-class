import BoundariesOfClass.Sieve.Range

/-!
# The block sieve: definitions (2026-10-25)

Solution-side. These are the block-sieve definitions (items 1–9 of DESIGN.md), in Lean, as reviewed by a separate
AI review session. Everything here is internal and is checked by the kernel and the closure audit.

Families: `fam = 0` is family A (d = m, m ≡ 3 mod 4, (t, c) = (1, (m + 1)/4)); `fam = 1` is family B (d = 4m,
m ≡ 1 or 2 mod 4, (t, c) = (0, m), 2 ramified).
-/

namespace BoundariesOfClass.Sieve.Block

/-! ## Definitions -/

/-- Rotate a `q`-bit pattern so that bit `j` becomes bit `(j + t) % q` of the input. -/
def rot (q B t : ℕ) : ℕ := Nat.land (Nat.lor (B >>> t) (B <<< (q - t))) (2 ^ q - 1)
/-- Replicate a `q`-bit pattern across `L` lanes. -/
def rep (L q P : ℕ) : ℕ := Nat.land (P * ((2 ^ (q * ((L + q - 1) / q)) - 1) / (2 ^ q - 1))) (2 ^ L - 1)
def inv4 (q : ℕ) : ℕ := ((q + 1) / 2) * ((q + 1) / 2) % q
/-- The split mask of the odd prime `q` over the lanes `m = m0 + 4 i`, `i < L`. -/
def maskOf (L m0 q B : ℕ) : ℕ := rep L q (rot q B (m0 * inv4 q % q))
/-- The base pattern of `q` (stride 4), in the SOUNDNESS direction only: a set
bit `j` means `q` splits when `m ≡ 4 j (mod q)`. A bit wrongly left clear only drops a split prime from `laneList`,
which undercounts and stays sound. -/
def BaseOK (q B : ℕ) : Prop :=
  B < 2 ^ q ∧ ∀ j < q, B.testBit j = true → (¬ q ∣ 4 * j ∧ IsSqMod q ((q * q - 4 * j) % q))

/-- The reference pattern, built linearly from Check.lean's `sqMask` (structural recursion, like `sqMaskAux`): bit
`n` is set iff `(4 n) % q ≠ 0` and `(q² − 4n) % q` is a square mod `q`. -/
def basePatAux (q sq : ℕ) : ℕ → ℕ → ℕ
  | 0, acc => acc
  | n + 1, acc =>
    basePatAux q sq n
      (cond (Nat.beq (4 * n % q) 0) acc
        (cond (Nat.beq ((sq >>> ((q * q - 4 * n) % q)) % 2) 1) (Nat.lor acc (1 <<< n)) acc))
def basePat (q : ℕ) : ℕ := basePatAux q (sqMask q) q 0

/-- Trial division by `k, k + 1, …` while `k * k ≤ p`, with fuel `f` (false when the fuel runs out). No `Nat.sqrt`
is evaluated. -/
def trialB (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, k => if p < k * k then true else (p % k != 0) && trialB p f (k + 1)

/-- √p-bounded primality: about √p steps instead of `primeB`'s p. -/
def primeSqB (p : ℕ) : Bool := Nat.ble 2 p && trialB p p 2

/-- One chunk of the shared table, checked linearly (in primesOKB's shape): every entry is a prime (by
`primeSqB`), not 2, with exactly the reference pattern; the primes increase. -/
def chunkOKB (l : List (ℕ × ℕ)) : Bool :=
  l.all (fun qB => primeSqB qB.1 && !(Nat.beq qB.1 2) && Nat.beq qB.2 (basePat qB.1)) &&
    incr (l.map (·.1))
/-- The shared pattern table: odd primes, increasing, each with its base pattern. Proved once per table, in the
Base modules (FORMAT.md); a block only refers to the table. -/
def PatsOK (pats : List (ℕ × ℕ)) : Prop :=
  (∀ qB ∈ pats, qB.1.Prime ∧ qB.1 ≠ 2 ∧ BaseOK qB.1 qB.2) ∧ (pats.map (·.1)).Pairwise (· < ·)

/-- Lanes `i` with `p² ∣ m0 + 4i` (the inverse of 4 mod p² is ((p²+1)/2)²; no exponent ≥ L is ever formed). -/
def j0Of (m0 p : ℕ) : ℕ := (p * p - m0 % (p * p)) * ((p * p + 1) / 2 * ((p * p + 1) / 2) % (p * p)) % (p * p)
def nsqOf (L m0 p : ℕ) : ℕ :=
  if p * p < L then rep L (p * p) (2 ^ j0Of m0 p) else if j0Of m0 p < L then 2 ^ j0Of m0 p else 0
def NSQ (L m0 : ℕ) (sqps : List ℕ) : ℕ := sqps.foldl (fun acc p => Nat.lor acc (nsqOf L m0 p)) 0

/-- Ripple-carry addition of a mask into bit-planes from plane `k`; returns (planes, carry out). -/
def addFrom : List ℕ → ℕ → ℕ → List ℕ × ℕ
  | [], _, c => ([], c)
  | p :: ps, 0, c => let r := addFrom ps 0 (Nat.land p c); (Nat.xor p c :: r.1, r.2)
  | p :: ps, k + 1, c => let r := addFrom ps k c; (p :: r.1, r.2)

structure St where
  planes : List ℕ
  sticky : ℕ

def addSt (s : St) (M k : ℕ) : St := let r := addFrom s.planes k M; ⟨r.1, Nat.lor s.sticky r.2⟩

mutual
def dfsY (Yb : ℕ) : ℕ → List (ℕ × ℕ) → ℕ → ℕ → ℕ → St → St
  | 0, _, _, _, _, s => s
  | _ + 1, [], _, _, _, s => s
  | f + 1, (q, S) :: rest, prod, M, k, s =>
    if Yb < prod * q then s
    else
      let M2 := Nat.land M S
      let s1 := powsY Yb f q M2 rest (prod * q) (k + 1) s
      dfsY Yb f rest prod M k s1
def powsY (Yb : ℕ) : ℕ → ℕ → ℕ → List (ℕ × ℕ) → ℕ → ℕ → St → St
  | 0, _, _, _, _, _, s => s
  | f + 1, q, M2, rest, pk, k, s =>
    if Yb < pk then s
    else
      let s1 := addSt s M2 k
      let s2 := dfsY Yb f rest pk M2 k s1
      powsY Yb f q M2 rest (pk * q) k s2
end

def NP : ℕ := 11

/-- The value of lane `i` in bit-planes (least significant plane first). -/
def planesVal : List ℕ → ℕ → ℕ
  | [], _ => 0
  | p :: ps, i => (if p.testBit i then 1 else 0) + 2 * planesVal ps i

def geqFrom (ALL : ℕ) : List ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  | [], _, gt, eq, _ => Nat.lor gt eq
  | p :: ps, T, gt, eq, j =>
    if T / 2 ^ j % 2 = 1 then geqFrom ALL ps T gt (Nat.land eq p) (j - 1)
    else geqFrom ALL ps T (Nat.lor gt (Nat.land eq p)) (Nat.land eq (Nat.xor ALL p)) (j - 1)

/-- One split-only count at bound `Yb` over finished lane MASKS (not base patterns), added onto `s` (the `n = 1`
term first). Taking masks, not patterns, is a 2026-10-25 fix: the previous draft applied `maskOf` to every
entry, including family A's already-built `mask2`, which double-rotated it (wrong parity for odd m0) and disagreed
with `laneList`. -/
def count1 (L : ℕ) (masks : List (ℕ × ℕ)) (Yb : ℕ) (s : St) : St :=
  dfsY Yb 4000 masks 1 (2 ^ L - 1) 0 (addSt s (2 ^ L - 1) 0)

/-- A block. Family A uses the prime 2 by the mask `m ≡ 7 (mod 8)`; family B adds the count at `Y / 2` (2 ramified).
`oddPrimes` is the shared list from which the square primes are SELECTED in the kernel. -/
structure Blk where
  fam : ℕ
  N : ℕ
  L : ℕ
  m0 : ℕ
  Y : ℕ
  pats : List (ℕ × ℕ)
  oddPrimes : List ℕ
  E : ℕ

def mask2 (L m0 : ℕ) : ℕ := rep L 2 (if m0 % 8 = 7 then 1 else 2)

/-- The finished lane masks of a block: 2 by the mod-8 mask in family A (none in family B, where 2 is ramified),
then every odd pattern prime by `maskOf`. `finalSt` and `laneList` both use exactly this list. -/
def masksOf (b : Blk) : List (ℕ × ℕ) :=
  (if b.fam = 0 then [(2, mask2 b.L b.m0)] else []) ++
    b.pats.map (fun qB : ℕ × ℕ => (qB.1, maskOf b.L b.m0 qB.1 qB.2))

def finalSt (b : Blk) : St :=
  let s0 : St := ⟨List.replicate NP 0, 0⟩
  if b.fam = 0 then count1 b.L (masksOf b) b.Y s0
  else count1 b.L (masksOf b) (b.Y / 2) (count1 b.L (masksOf b) b.Y s0)

def sqps (b : Blk) : List ℕ := b.oddPrimes.filter (fun p => p * p ≤ b.m0 + 4 * (b.L - 1))

def uncertified (b : Blk) : ℕ :=
  let ALL := 2 ^ b.L - 1
  let s := finalSt b
  Nat.land (Nat.xor ALL (Nat.land (Nat.lor (geqFrom ALL s.planes.reverse (b.N + 1) 0 ALL (NP - 1)) s.sticky) ALL))
    (Nat.xor ALL (NSQ b.L b.m0 (sqps b)))

/-- The kernel check of one block. The shared table's facts (`PatsOK`) are a separate hypothesis, proved once
in the Base modules. -/
def blockOK (b : Blk) : Bool :=
  Nat.beq (uncertified b) b.E &&
  Nat.blt (b.N + 1) (2 ^ NP) &&   -- strict: geqFrom reads only bits 0..NP-1 of T = N + 1
  (b.oddPrimes.all (fun p => Nat.ble 3 p && Nat.beq (p % 2) 1)) &&
  (if b.fam = 0 then Nat.blt (4 * (b.Y * b.Y)) b.m0 && Nat.beq (b.m0 % 4) 3
   else Nat.blt (b.Y * b.Y) b.m0 && (Nat.beq (b.m0 % 4) 1 || Nat.beq (b.m0 % 4) 2)) &&
  Nat.ble 2 b.Y

/-- The list `mu` is applied to for lane `i`: for family B the ramified 2 first, then the lane's split
primes, i.e. the primes whose mask bit `i` is set (2 by the mod-8 mask in family A). -/
def laneList (b : Blk) (i : ℕ) : List (ℕ × Bool) :=
  let split : List (ℕ × Bool) :=
    ((masksOf b).filter (fun qS : ℕ × ℕ => qS.2.testBit i)).map (fun qS : ℕ × ℕ => (qS.1, true))
  (if b.fam = 0 then [] else [(2, false)]) ++ split

/-! ## Item 8: the range assembly (pillar 1; the h ≤ 1000 instance) -/

/-- The 18 W radicands (= d, all ≡ 3 mod 4, family A): the fields above F(1000) = 227932027 with h between 1002
and 1052 that the split-prime count cannot certify at any Y. -/
def W18 : List ℕ := [228532627, 229119067, 229382707, 229591147, 231332467, 232380163, 233047963, 233333563, 233421043, 233875387, 234914947, 235714747, 237710467, 239630227, 243829987, 245007547, 249255043, 269497867]

/-- Every squarefree radicand with F < dOf m < X lies in a lane of some block of `Bs` of its own family. -/
def Covers (Bs : List Blk) (F X : ℕ) : Prop :=
  ∀ m : ℕ, Squarefree m → m ≠ 1 → m ≠ 3 → F < CN1.Finite.dOf m → CN1.Finite.dOf m < X →
    ∃ b ∈ Bs, b.m0 ≤ m ∧ m < b.m0 + 4 * b.L ∧ m % 4 = b.m0 % 4

/-- **The check that carries the weight (narrowed for pillar 1).** Every uncertified
squarefree lane is either in W18 or settled by the existing per-field `checkAt` at its own Y. -/
def ExceptionsOK (Bs : List Blk) : Prop :=
  ∀ b ∈ Bs, ∀ i < b.L, b.E.testBit i = true → Squarefree (b.m0 + 4 * i) →
    (b.m0 + 4 * i) ∈ W18 ∨ ∃ Y P, PrimesOK P ∧ checkAt 1000 Y P (b.m0 + 4 * i) = true

end BoundariesOfClass.Sieve.Block
