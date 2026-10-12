import FrcCore.Sum
import FrcCore.Instances
import FrcCore.Poly
import FrcCore.Meridian
import FrcCore.Keys.Frame

/-!
# FrcCore.Epi — the classical constants on the shell, with no axioms (13-epi)

The derangement numbers by their natural recurrence, their signed recurrence and antiperiodicity
`!(n + p) ≡ −!n` on every shell `p = 4κ + 1`, the fixed-shell tower of `e` exact at every grade, the
orientation transport of the quarter-turn under a change of drive (no third case), the wrap-free window
below `√p`; and the value rows decided by the kernel: the `p = 13` coincidence (`e_p = π_A = −1/2 = 6`),
the residue lines of `e` and `π` on `𝔽₁₃`, the terminal residue `−(!13)⁻¹ = 9`, the legibility window and
the first revival on `𝔽₁₃`, the 36 two-digit revivals, and the products `!p·A(p)` on the six wall shells; and the
censuses decided by the kernel (section `census`, each cut into chunks of about 45,000 fold steps): the opening stretch
of the blind-scale census (F5), the arcsin wall vanishing on all 428 odd primes below 3000 and to second order on the 60
primes below 300 (G6, G7), the frame invariants at `p = 13` and `1093` (I5), the tail bound of the arcsin chain and the
impossibility of exact calibration on the 500 shells `p ≤ 8009`, both against a certified rational bracket of `π`
(E3, H3), the binary64 readout and the step counts of the derangement chain in the integers (D4, D5), the shell data of
the best calibrated shell (H4), the height run over the 500 shells and the certification split (J3, J5).

Since the ledger migration (task LM17) `ofNat_self` and `ofNat_add_self` live in `Frame.lean`; the old names stay as aliases.
-/

namespace FRC.Epi

open FRC.Shell FRC.Shell.Frame

/-! ### The factorial, Kurepa's left factorial and the derangement numbers -/

/-- The factorial. -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- The derangement numbers `!n` by the natural recurrence `!(n+2) = (n+1)(!n + !(n+1))`. -/
def dr : Nat → Nat
  | 0 => 1
  | 1 => 0
  | n + 2 => (n + 1) * (dr n + dr (n + 1))

theorem dr_zero : dr 0 = 1 := rfl
theorem dr_one : dr 1 = 0 := rfl
theorem dr_add_two (n : Nat) : dr (n + 2) = (n + 1) * (dr n + dr (n + 1)) := rfl

/-- Kurepa's left factorial `!p = Σ_{k<p} k!`. -/
def kur : Nat → Nat
  | 0 => 0
  | n + 1 => kur n + fact n

/-- The central binomial coefficient `C(2n, n) = (2n)!/(n!·n!)`. -/
def cb (n : Nat) : Nat := fact (2 * n) / (fact n * fact n)

section shell

variable {p : Nat} [Pos p]

/-- The factorial reduced on the shell, `k! mod p`, computed one factor at a time. -/
def factS : Nat → Shell p
  | 0 => 1
  | n + 1 => factS n * ofNat (n + 1)

theorem factS_eq : ∀ n, (factS n : Shell p) = ofNat (fact n)
  | 0 => rfl
  | n + 1 => by
    show factS n * ofNat (n + 1) = ofNat ((n + 1) * fact n)
    rw [factS_eq n, ofNat_mul, Nat.mul_comm]

/-- `Σ_{k<n} k!` on the shell. -/
def kurS (n : Nat) : Shell p := sumRange (fun k => factS k) n

/-- `Σ_{k<n} (−1)^k k!` on the shell (the alternating factorial sum `A(n)`). -/
def altS (n : Nat) : Shell p := sumRange (fun k => (-1) ^ k * factS k) n

theorem kurS_eq : ∀ n, (kurS n : Shell p) = ofNat (kur n)
  | 0 => rfl
  | n + 1 => by
    show sumRange (fun k => factS k) n + factS n = ofNat (kur n + fact n)
    rw [← ofNat_add, ← factS_eq]; exact congrArg (· + factS n) (kurS_eq n)

/-- The inverse by bounded search: the `y < n` with `x·y = 1`, or `0` when there is none. -/
def invSearch (x : Shell p) : Nat → Shell p
  | 0 => 0
  | n + 1 => if x * ofNat n = 1 then ofNat n else invSearch x n

/-- The inverse on the shell (`0` for a non-unit). -/
def inv (x : Shell p) : Shell p := invSearch x p

/-- The reading of `ε_n = n!/!n` on the shell (`0` at a blind scale). -/
def readE (n : Nat) : Shell p := ofNat (fact n) * inv (ofNat (dr n))

/-- The reading of the Wallis member `w_n = 16^n/(n·C(2n,n)²)` on the shell. -/
def readW (n : Nat) : Shell p := ofNat (16 ^ n) * inv (ofNat n * ofNat (cb n) ^ 2)

/-- The reading of the Wallis member `v_n = 2·16^n/((2n+1)·C(2n,n)²)` on the shell. -/
def readV (n : Nat) : Shell p := ofNat (2 * 16 ^ n) * inv (ofNat (2 * n + 1) * ofNat (cb n) ^ 2)

/-! ### The signed recurrence and antiperiodicity -/

theorem neg_one_pow_succ (n : Nat) : (-1 : Shell p) ^ (n + 1) = -((-1) ^ n) := by
  rw [pow_succ, ← mul_neg, mul_one]

/-- 13:F3 — the signed recurrence on the shell: `!(n+1) = (n+1)·!n + (−1)^{n+1}`. -/
theorem dr_succ : ∀ n : Nat, (ofNat (dr (n + 1)) : Shell p) = ofNat (n + 1) * ofNat (dr n) + (-1) ^ (n + 1)
  | 0 => by
    show (ofNat 0 : Shell p) = ofNat 1 * ofNat 1 + (-1) ^ 1
    rw [pow_one, ofNat_mul, Nat.mul_one]
    show (0 : Shell p) = 1 + -1
    rw [add_neg]
  | n + 1 => by
    have ih := dr_succ n
    rw [dr_add_two, ← ofNat_mul, ← ofNat_add (dr n) (dr (n + 1)), left_distrib]
    have e1 : (ofNat (n + 1) : Shell p) * ofNat (dr n) = ofNat (dr (n + 1)) + -((-1) ^ (n + 1)) := by
      rw [ih, add_assoc, add_neg, add_zero]
    rw [e1, neg_one_pow_succ (n + 1), ofNat_succ (n + 1), right_distrib, one_mul,
      add_comm (ofNat (dr (n + 1)) + -(-1) ^ (n + 1)) (ofNat (n + 1) * ofNat (dr (n + 1))), ← add_assoc]

theorem four_kappa_add_one_mod_two (κ : Nat) : (4 * κ + 1) % 2 = 1 :=
  FRC.Nat.mod_unique (q := 2 * κ) (Nat.lt_succ_self 1) (by rw [← FRC.Nat.mul_assoc])

theorem neg_one_pow_p {κ : Nat} (hκ : p = 4 * κ + 1) : (-1 : Shell p) ^ p = -1 := by
  have h2 : p % 2 = 1 := by rw [hκ]; exact four_kappa_add_one_mod_two κ
  rw [neg_one_pow, h2]; rfl

/-- 13:F3, 13:I1 — antiperiodicity on every shell `p = 4κ + 1`: `!(n + p) ≡ −!n (mod p)` for every `n`, so
`!n mod p` depends on `n mod 2p`; and the blind set contains `n = 1` (`!1 = 0`). -/
theorem dr_antiperiodic {κ : Nat} (hκ : p = 4 * κ + 1) :
    (∀ n, (ofNat (dr (n + p)) : Shell p) = -(ofNat (dr n))) ∧ dr 1 = 0 := by
  refine ⟨?_, rfl⟩
  intro n
  induction n with
  | zero =>
    have h : (ofNat (dr (0 + p)) : Shell p) = ofNat p * ofNat (dr (p - 1)) + (-1) ^ p := by
      have e : 0 + p = (p - 1) + 1 := by rw [Nat.zero_add, hκ]; rfl
      rw [e, dr_succ, ← e, Nat.zero_add]
    rw [h, ofNat_self, zero_mul, zero_add, neg_one_pow_p hκ]
    rfl
  | succ n ih =>
    have e : n + 1 + p = (n + p) + 1 := Nat.add_right_comm n 1 p
    have e2 : n + p + 1 = (n + 1) + p := Nat.add_right_comm n p 1
    rw [e, dr_succ, ih, e2, ofNat_add_self (n + 1), pow_add, neg_one_pow_p hκ, ← mul_neg, ← mul_neg,
      mul_one, ← neg_add_rev, ← dr_succ]

/-- 13:F7 — the fixed-shell tower of `e`, exact at every grade: `(mp)! ≡ 0` and `!(mp) ≡ (−1)^m` for `m ≥ 1`,
so the member `q_m = ((mp)! + δ_m)/!(mp)` reads `e_p` — numerator `≡ !(mp)·e_p` — whenever `δ_m ≡ (−1)^m e_p`. -/
theorem tower_e_exact {κ : Nat} (hκ : p = 4 * κ + 1) (m : Nat) (e δ : Shell p) (hδ : δ = (-1) ^ (m + 1) * e) :
    (ofNat (fact ((m + 1) * p)) : Shell p) = 0 ∧ (ofNat (dr ((m + 1) * p)) : Shell p) = (-1) ^ (m + 1) ∧
    ofNat (fact ((m + 1) * p)) + δ = ofNat (dr ((m + 1) * p)) * e := by
  have hfact : ∀ k, (ofNat (fact (k + p)) : Shell p) = 0 := by
    intro k
    induction k with
    | zero =>
      have e : 0 + p = (p - 1) + 1 := by rw [Nat.zero_add, hκ]; rfl
      rw [e]
      show (ofNat ((p - 1 + 1) * fact (p - 1)) : Shell p) = 0
      rw [← e, Nat.zero_add, ← ofNat_mul, ofNat_self, zero_mul]
    | succ k ih =>
      rw [Nat.add_right_comm]
      show (ofNat ((k + p + 1) * fact (k + p)) : Shell p) = 0
      rw [← ofNat_mul, ih, mul_zero]
  have hdr : ∀ m, (ofNat (dr (m * p)) : Shell p) = (-1) ^ m := by
    intro m
    induction m with
    | zero => rw [Nat.zero_mul]; rfl
    | succ m ih => rw [Nat.succ_mul, (dr_antiperiodic hκ).1, ih, neg_one_pow_succ]
  have hf : (ofNat (fact ((m + 1) * p)) : Shell p) = 0 := by
    rw [Nat.succ_mul]; exact hfact _
  refine ⟨hf, hdr (m + 1), ?_⟩
  rw [hf, zero_add, hδ, hdr]

end shell

/-! ### Orientation transport (13:B2) -/
section transport

variable {p κ : Nat} [Pos p] {g : Shell p}

theorem odd_of_coprime_four (F : Frame p κ g) {u : Nat} (hu : Coprime u (p - 1)) : u % 2 = 1 := by
  match hu with
  | ⟨a, _, hau⟩ =>
    match FRC.Nat.mod_spec 2 (Nat.zero_lt_succ 1) u with
    | ⟨t, ht⟩ =>
      match FRC.Nat.mod_spec (p - 1) F.n_pos (a * u) with
      | ⟨q, hq⟩ =>
        rw [hau, F.n_eq] at hq
        -- a * u = 4κq + 1 is odd; if u % 2 = 0 then a * u = 2 * (a * t) is even
        match h2 : u % 2 with
        | 0 =>
          rw [h2, Nat.add_zero] at ht
          have hodd : (a * u) % 2 = 1 := by
            apply FRC.Nat.mod_unique (q := 2 * κ * q) (Nat.lt_succ_self 1)
            rw [hq]
            show 4 * κ * q + 1 = 2 * (2 * κ * q) + 1
            rw [← FRC.Nat.mul_assoc, ← FRC.Nat.mul_assoc]
          have heven : (a * u) % 2 = 0 := by
            apply FRC.Nat.mod_unique (q := a * t) (Nat.zero_lt_succ 1)
            rw [ht, Nat.add_zero, FRC.Nat.mul_left_comm]
          exact (Nat.succ_ne_zero 0 (hodd.symm.trans heven)).elim
        | 1 => rfl
        | r + 2 =>
          have := Nat.mod_lt u (Nat.zero_lt_succ 1)
          rw [h2] at this
          exact absurd (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ this)) (Nat.not_lt_zero r)

theorem mod_four_of_odd {u : Nat} (h : u % 2 = 1) : u % 4 = 1 ∨ u % 4 = 3 := by
  match FRC.Nat.mod_spec 4 (Nat.zero_lt_succ 3) u with
  | ⟨q, hq⟩ =>
    have hr := Nat.mod_lt u (Nat.zero_lt_succ 3)
    match hr4 : u % 4, hr with
    | 0, _ =>
      rw [hr4, Nat.add_zero] at hq
      have : u % 2 = 0 := FRC.Nat.mod_unique (q := 2 * q) (Nat.zero_lt_succ 1)
        (by rw [hq, Nat.add_zero, ← FRC.Nat.mul_assoc])
      exact (Nat.succ_ne_zero 0 (this.symm.trans h).symm).elim
    | 1, _ => exact Or.inl rfl
    | 2, _ =>
      rw [hr4] at hq
      have : u % 2 = 0 := FRC.Nat.mod_unique (q := 2 * q + 1) (Nat.zero_lt_succ 1)
        (by rw [hq, Nat.add_zero, Nat.mul_succ, ← FRC.Nat.mul_assoc])
      exact (Nat.succ_ne_zero 0 (this.symm.trans h).symm).elim
    | 3, _ => exact Or.inr rfl
    | r + 4, hlt =>
      exact absurd (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
        (Nat.lt_of_succ_lt_succ hlt)))) (Nat.not_lt_zero r)

/-- 13:B2 — orientation transport: under `g' = g^u` with `u` coprime to `p − 1`, `u` is odd, so either
`u ≡ 1 (mod 4)` and the re-derived quarter-turn `−g'^κ` is `−g^κ` (the same chirality), or `u ≡ 3 (mod 4)`
and it is `−(−g^κ)` (the conjugate chart); there is no third case. -/
theorem orientation_transport (F : Frame p κ g) {u : Nat} (hu : Coprime u (p - 1)) :
    (u % 4 = 1 ∨ u % 4 = 3) ∧
    (u % 4 = 1 → quarterTurn (g ^ u) κ = quarterTurn g κ) ∧
    (u % 4 = 3 → quarterTurn (g ^ u) κ = -(quarterTurn g κ)) :=
  ⟨mod_four_of_odd (odd_of_coprime_four F hu), (F.orientation_class u).1, (F.orientation_class u).2⟩

end transport

/-! ### The wrap-free window (13:J1) -/
section window

/-- 13:J1 — the wrap-free window: two counts below `√p` (`a·a < p`, `b·b < p`) have a product below `p`, and,
for `p ≥ 4`, a sum below `p`: the accessible smalls neither wrap under `+` nor under `×`. -/
theorem wrap_free {a b p : Nat} (ha : a * a < p) (hb : b * b < p) :
    a * b < p ∧ (4 ≤ p → a + b < p) := by
  have hprod : a * b < p := by
    match Nat.lt_or_ge a b with
    | Or.inl hab => exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right b (Nat.le_of_lt hab)) hb
    | Or.inr hba => exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_left a hba) ha
  refine ⟨hprod, fun h4 => ?_⟩
  -- with c = max: a + b ≤ c + c ≤ c·c < p when c ≥ 2; a + b ≤ 2 < 4 ≤ p when c ≤ 1
  have key : ∀ c, c * c < p → c + c < p := by
    intro c hc
    match c with
    | 0 => exact Nat.lt_of_lt_of_le (Nat.zero_lt_succ 3) h4
    | 1 => exact Nat.lt_of_lt_of_le (Nat.lt_succ_self 3 |> Nat.lt_of_succ_lt) h4
    | c + 2 =>
      have : (c + 2) + (c + 2) ≤ (c + 2) * (c + 2) := by
        rw [← Nat.two_mul]; exact Nat.mul_le_mul_right (c + 2) (Nat.le_add_left 2 c)
      exact Nat.lt_of_le_of_lt this hc
  match Nat.lt_or_ge a b with
  | Or.inl hab => exact Nat.lt_of_le_of_lt (Nat.add_le_add_right (Nat.le_of_lt hab) b) (key b hb)
  | Or.inr hba => exact Nat.lt_of_le_of_lt (Nat.add_le_add_left hba a) (key a ha)

end window

/-! ### The value rows, decided by the kernel -/
section values

/-- 13:B3 — the `p = 13` coincidence: with `g = 2`, `κ = 3`, the quarter-turn `i = −g^κ = 5`, the exponential
unit `e_p = g^{λ(i)} = 2^5 = 6`, the half-period `π_A = 2κ = 6`, and `6` is the reading of `−1/2` (`2·6 = −1`). -/
theorem coincidence13 :
    quarterTurn (2 : Shell 13) 3 = 5 ∧ (2 : Shell 13) ^ (quarterTurn (2 : Shell 13) 3).val = 6 ∧
    (ofNat (halfPeriod 3) : Shell 13) = 6 ∧ (2 : Shell 13) * 6 = -1 := by decide

/-- 13:F2, 13:F6, 13:I1, 13:I3, 13:J6 — the wall of `e` on `𝔽₁₃`: `!12 ≡ !13 ≡ 10`, the terminal residue `⟦ε₁₂⟧ = 9 = −(!13)⁻¹`, the
common reading of `6/5` and `11/7`. -/
theorem terminal13 :
    (ofNat (dr 12) : Shell 13) = ofNat (kur 13) ∧ (ofNat (kur 13) : Shell 13) = 10 ∧
    readE (p := 13) 12 = 9 ∧ (ofNat (kur 13) : Shell 13) * 9 = -1 ∧
    (6 : Shell 13) * inv 5 = 9 ∧ (11 : Shell 13) * inv 7 = 9 := by decide +kernel

/-- 13:F6 — the residue line of `e` on `𝔽₁₃`: `⟦ε_n⟧`, `n = 2, …, 12`, is `2, 3, 7, 11, 1, 6, blind, 2, 8, 10, 9`
(the blind scale `n = 8` reads `0` here: `!8 = 14833 = 13·1141`). -/
theorem residue_line_e13 :
    (List.range 11).map (fun k => readE (p := 13) (k + 2)) = [2, 3, 7, 11, 1, 6, 0, 2, 8, 10, 9] ∧
    dr 8 = 13 * 1141 ∧ (ofNat (dr 8) : Shell 13) = 0 := by decide +kernel

/-- 13:G8, 13:G1, 13:I2, 13:I3 — the residue line of `π` on `𝔽₁₃`: `⟦w_n⟧`, `n = 1, …, 6`, is `4, 5, 10, 9, 6, 11`, the
calibration face `⟦w₆⟧ = 11 = −2`, the quarter invariant `⟦w₃⟧ = 10 = −(3²)⁻¹`; the legibility window is exactly
`1 ≤ n ≤ 6` (`13 ∣ C(2n,n)` for `7 ≤ n ≤ 12`, not for `n ≤ 6`). -/
theorem residue_line_pi13 :
    (List.range 6).map (fun k => readW (p := 13) (k + 1)) = [4, 5, 10, 9, 6, 11] ∧
    (11 : Shell 13) = -2 ∧ (10 : Shell 13) * (3 * 3) = -1 ∧
    (List.range 13).map (fun n => decide (cb n % 13 = 0)) =
      [false, false, false, false, false, false, false, true, true, true, true, true, true] := by decide +kernel

/-- 13:G5, 13:I2 — the first revival on `𝔽₁₃`: `⟦v₁₃⟧ = 8`, and the two-digit revivals `13 ≤ n < 169` with
`13 ∤ C(2n,n)` and `13 ∤ n` number `36 = (2κ)²`. -/
theorem revivals13 :
    readV (p := 13) 13 = 8 ∧
    ((List.range 169).filter (fun n => decide (13 ≤ n) && decide (cb n % 13 ≠ 0) && decide (n % 13 ≠ 0))).length
      = 36 := by decide +kernel

/-- 13:F4, 13:I3 — the broken group law at the wall: `!p·A(p) ≡ 3, 0, 21, 28, 132, 258` at `p = 7, 13, 29, 101, 257,
1009`, with `A(13) ≡ 0` (the direct series residue vanishes on `𝔽₁₃`). -/
theorem kurepa_alt_values :
    kurS (p := 7) 7 * altS 7 = 3 ∧ kurS (p := 13) 13 * altS 13 = 0 ∧ altS (p := 13) 13 = 0 ∧
    kurS (p := 29) 29 * altS 29 = 21 ∧ kurS (p := 101) 101 * altS 101 = 28 ∧
    kurS (p := 257) 257 * altS 257 = 132 ∧ kurS (p := 1009) 1009 * altS 1009 = 258 := by decide +kernel

end values

/-! ### Censuses decided by the kernel: the blind sets, the arcsin wall, the frame invariants, the height run,
the readouts and the calibration

Every theorem of this section is a `decide +kernel` evaluation of a closed natural-number statement: the shells are
enumerated by trial division, the residues are folded by the recurrences, and the kernel's arithmetic (GMP for the
large naturals) decides the equalities. Nothing here is proved for every shell; each is a census over the shells its
statement names, the instance face of the rows it cites. A census is cut into chunks of about 45,000 fold steps, each
a declaration of its own, since the kernel keeps every intermediate term of one evaluation; the census theorem
composes the chunks and asserts the completeness of its enumeration. -/
section census

/-- Trial division from `d` with fuel: `true` when no `d ≤ d' ≤ √q` divides `q`. -/
def noDivisorFrom (q : Nat) : Nat → Nat → Bool
  | _, 0 => true
  | d, fuel + 1 => if q < d * d then true else if q % d == 0 then false else noDivisorFrom q (d + 1) fuel

/-- Primality by trial division, as a Boolean: `q ≥ 2` and no divisor `2 ≤ d ≤ √q`. -/
def isPrimeB (q : Nat) : Bool := 2 ≤ q && noDivisorFrom q 2 q

/-! #### Three list lemmas with no axioms

The core library's `all_append_nat`, `filter_append_nat` and `length_append_nat` rest on `propext`; the census
theorems compose their chunks through these, proved by induction. -/
/-- `(l₁ ++ l₂).all f = (l₁.all f && l₂.all f)`, by induction, with no axioms (the core library's `all_append_nat_nat`
rests on `propext`). -/
theorem all_append_nat (f : Nat → Bool) : ∀ l₁ l₂ : List Nat, (l₁ ++ l₂).all f = (l₁.all f && l₂.all f)
  | [], _ => rfl
  | a :: l₁, l₂ => by
    show (f a && (l₁ ++ l₂).all f) = ((f a && l₁.all f) && l₂.all f)
    rw [all_append_nat f l₁ l₂, Bool.and_assoc]

/-- `(a :: l).filter f = a :: l.filter f` when `f a = true`. -/
theorem filter_cons_true_nat (f : Nat → Bool) (a : Nat) (l : List Nat) (h : f a = true) :
    (a :: l).filter f = a :: l.filter f := by
  show (match f a with | true => a :: l.filter f | false => l.filter f) = a :: l.filter f
  rw [h]

/-- `(a :: l).filter f = l.filter f` when `f a = false`. -/
theorem filter_cons_false_nat (f : Nat → Bool) (a : Nat) (l : List Nat) (h : f a = false) :
    (a :: l).filter f = l.filter f := by
  show (match f a with | true => a :: l.filter f | false => l.filter f) = l.filter f
  rw [h]

/-- `(l₁ ++ l₂).filter f = l₁.filter f ++ l₂.filter f`, by induction, with no axioms. -/
theorem filter_append_nat (f : Nat → Bool) : ∀ l₁ l₂ : List Nat, (l₁ ++ l₂).filter f = l₁.filter f ++ l₂.filter f
  | [], _ => rfl
  | a :: l₁, l₂ => by
    show (a :: (l₁ ++ l₂)).filter f = (a :: l₁).filter f ++ l₂.filter f
    cases h : f a with
    | true => rw [filter_cons_true_nat f a _ h, filter_cons_true_nat f a _ h, filter_append_nat f l₁ l₂]; rfl
    | false => rw [filter_cons_false_nat f a _ h, filter_cons_false_nat f a _ h, filter_append_nat f l₁ l₂]

/-- `(l₁ ++ l₂).length = l₁.length + l₂.length`, by induction, with no axioms. -/
theorem length_append_nat : ∀ l₁ l₂ : List Nat, (l₁ ++ l₂).length = l₁.length + l₂.length
  | [], l₂ => (Nat.zero_add _).symm
  | a :: l₁, l₂ => by
    show (l₁ ++ l₂).length + 1 = l₁.length + 1 + l₂.length
    rw [length_append_nat l₁ l₂, Nat.add_right_comm]

/-! #### The blind sets (13:F5) -/

/-- The walk of the derangement residues modulo `q`: after `n` steps, `(!n mod q, !(n+1) mod q, #{1 ≤ k ≤ n : !k ≡ 0})`. -/
def blindFold (q : Nat) : Nat → Nat × Nat × Nat
  | 0 => (1 % q, 0, 0)
  | n + 1 =>
    match blindFold q n with
    | (a, b, c) => (b, ((n + 1) * (a + b)) % q, if b = 0 then c + 1 else c)

/-- `|Z₀(q)| = #{1 ≤ n ≤ q − 2 : !n ≡ 0 (mod q)}`, the blind set of the shell `q` counted below the wall. -/
def blindCount (q : Nat) : Nat := (blindFold q (q - 2)).2.2

/-- The 43 primes in `(1000, 1300)`, the opening stretch of the census of F5. -/
def primes1000to1300 : List Nat := (List.range 1300).filter (fun q => 1000 < q && isPrimeB q)

/-- 13:F5, 13:I1, 13:I3 — the blind-scale census, its opening stretch: on the `43` primes in `(1000, 1300)` the
sizes `|Z₀(p)|` are `1, 2, 2, 1, 2, 4, 1, 4, 2, 1, 2, 2, 1, 3, 3, 2, 3, 2, 1, 3, 1, 2, 5, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 3, 1, 2, 1, 1, 2, 2, 1, 2, 3` — forty-three exact
counts of the Poisson-read distribution (the full census of `501` primes is the package's check of F5). -/
theorem blind_census :
    primes1000to1300.length = 43 ∧ primes1000to1300.map blindCount =
      [1, 2, 2, 1, 2, 4, 1, 4, 2, 1, 2, 2, 1, 3, 3, 2, 3, 2, 1, 3, 1, 2, 5, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 3, 1,
      2, 1, 1, 2, 2, 1, 2, 3] := by decide +kernel

/-! #### The arcsin wall (13:G6, G7) -/

/-- The fold of `σ_p = Σ_{k<m} C(2k,k)/((2k+1)16^k)` modulo `q` by common denominators, no inverses: the state
`(A_k, B_k, N, D)` carries the term `A_k/B_k` (`A_{k+1} = A_k(2k+1)²`, `B_{k+1} = 8B_k(k+1)(2k+3)`, the ratio
`C(2k+2,k+1)(2k+1)/(C(2k,k)(2k+3)·16)`) and the partial sum `N/D` of the terms below `k`, all reduced modulo `q`. -/
def sigmaFold (q : Nat) : Nat → Nat × Nat × Nat × Nat
  | 0 => (1, 1, 0, 1)
  | k + 1 =>
    match sigmaFold q k with
    | (a, b, n, d) =>
      ((a * (2 * k + 1) * (2 * k + 1)) % q, (8 * b * (k + 1) * (2 * k + 3)) % q, (n * b + a * d) % q, (d * b) % q)

/-- `σ_p ≡ 0 (mod q)` read off the numerator of the fold at `m = (p−1)/2`: for `q = p` or `q = p²` the
denominators `B_k = 8^k k!(2k+1)!!`, `k < m`, are units modulo `q`, so the numerator vanishes exactly when `σ_p` does. -/
def sigmaZero (p q : Nat) : Bool := (sigmaFold q ((p - 1) / 2)).2.2.1 == 0
/-- The odd primes `5 ≤ p ≤ 1087`, chunk 1 of the census of G6. -/
def oddPrimesC1 : List Nat :=
  [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109,
  113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233,
  239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367,
  373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499,
  503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643,
  647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797,
  809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947,
  953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069,
  1087]
/-- The odd primes `1091 ≤ p ≤ 1571`, chunk 2 of the census of G6. -/
def oddPrimesC2 : List Nat :=
  [1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217,
  1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327,
  1361, 1367, 1373, 1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483,
  1487, 1489, 1493, 1499, 1511, 1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571]
/-- The odd primes `1579 ≤ p ≤ 1973`, chunk 3 of the census of G6. -/
def oddPrimesC3 : List Nat :=
  [1579, 1583, 1597, 1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699,
  1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847, 1861,
  1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973]
/-- The odd primes `1979 ≤ p ≤ 2287`, chunk 4 of the census of G6. -/
def oddPrimesC4 : List Nat :=
  [1979, 1987, 1993, 1997, 1999, 2003, 2011, 2017, 2027, 2029, 2039, 2053, 2063, 2069, 2081, 2083, 2087, 2089,
  2099, 2111, 2113, 2129, 2131, 2137, 2141, 2143, 2153, 2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243,
  2251, 2267, 2269, 2273, 2281, 2287]
/-- The odd primes `2293 ≤ p ≤ 2591`, chunk 5 of the census of G6. -/
def oddPrimesC5 : List Nat :=
  [2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371, 2377, 2381, 2383, 2389, 2393, 2399, 2411,
  2417, 2423, 2437, 2441, 2447, 2459, 2467, 2473, 2477, 2503, 2521, 2531, 2539, 2543, 2549, 2551, 2557, 2579,
  2591]
/-- The odd primes `2593 ≤ p ≤ 2819`, chunk 6 of the census of G6. -/
def oddPrimesC6 : List Nat :=
  [2593, 2609, 2617, 2621, 2633, 2647, 2657, 2659, 2663, 2671, 2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711,
  2713, 2719, 2729, 2731, 2741, 2749, 2753, 2767, 2777, 2789, 2791, 2797, 2801, 2803, 2819]
/-- The odd primes `2833 ≤ p ≤ 2999`, chunk 7 of the census of G6. -/
def oddPrimesC7 : List Nat :=
  [2833, 2837, 2843, 2851, 2857, 2861, 2879, 2887, 2897, 2903, 2909, 2917, 2927, 2939, 2953, 2957, 2963, 2969,
  2971, 2999]
/-- The 428 odd primes `5 ≤ p < 3000`, the seven chunks concatenated. -/
def oddPrimesBelow3000 : List Nat := oddPrimesC1 ++ oddPrimesC2 ++ oddPrimesC3 ++ oddPrimesC4 ++ oddPrimesC5 ++ oddPrimesC6 ++ oddPrimesC7
/-- The enumeration is complete: the seven chunks are exactly the odd primes `5 ≤ p < 3000` by trial division. -/
theorem oddPrimesBelow3000_complete :
    (List.range 3000).filter (fun q => 5 ≤ q && isPrimeB q) = oddPrimesBelow3000 := by decide +kernel
theorem sigma_vanishes_c1 : oddPrimesC1.all (fun p => sigmaZero p p) = true := by decide +kernel
theorem sigma_vanishes_c2 : oddPrimesC2.all (fun p => sigmaZero p p) = true := by decide +kernel
theorem sigma_vanishes_c3 : oddPrimesC3.all (fun p => sigmaZero p p) = true := by decide +kernel
theorem sigma_vanishes_c4 : oddPrimesC4.all (fun p => sigmaZero p p) = true := by decide +kernel
theorem sigma_vanishes_c5 : oddPrimesC5.all (fun p => sigmaZero p p) = true := by decide +kernel
theorem sigma_vanishes_c6 : oddPrimesC6.all (fun p => sigmaZero p p) = true := by decide +kernel
theorem sigma_vanishes_c7 : oddPrimesC7.all (fun p => sigmaZero p p) = true := by decide +kernel
/-- 13:G6, 13:I2 — first-order wall vanishing of the arcsin chain: `σ_p ≡ 0 (mod p)` on all `428` odd primes
`5 ≤ p < 3000` (the enumeration complete), and `σ_3 = 1`. -/
theorem sigma_vanishes_all :
    (List.range 3000).filter (fun q => 5 ≤ q && isPrimeB q) = oddPrimesBelow3000 ∧ oddPrimesBelow3000.length = 428 ∧
    oddPrimesBelow3000.all (fun p => sigmaZero p p) = true ∧ sigmaZero 3 3 = false := by
  refine ⟨oddPrimesBelow3000_complete, by decide +kernel, ?_, by decide +kernel⟩
  rw [oddPrimesBelow3000, all_append_nat, all_append_nat, all_append_nat, all_append_nat, all_append_nat,
    all_append_nat, sigma_vanishes_c1, sigma_vanishes_c2, sigma_vanishes_c3, sigma_vanishes_c4, sigma_vanishes_c5,
    sigma_vanishes_c6, sigma_vanishes_c7]
  rfl

/-- The 60 primes `5 ≤ p < 300`. -/
def primes5to300 : List Nat := (List.range 300).filter (fun q => 5 ≤ q && isPrimeB q)

/-- 13:G7, 13:I2 — second order at the arcsin wall: `σ_p ≡ 0 (mod p²)` (Sun's theorem) on all `60` primes
`5 ≤ p < 300`. -/
theorem sigma_vanishes_mod_sq :
    primes5to300.length = 60 ∧ primes5to300.all (fun p => sigmaZero p (p * p)) = true := by decide +kernel

/-! #### The frame invariants (13:I5) -/

/-- The Fermat quotient of `4` at `p`: `(4^{p−1} − 1)/p mod p`. -/
def fermatQuotient4 (p : Nat) : Nat := ((4 ^ (p - 1) % (p * p) + p * p - 1) / p) % p

/-- 13:I5, 13:J6 — the three frame invariants on their named shells: at `p = 13` the wall of `e` is `!13 ≡ 10`, the
Fermat quotient `q₁₃(4) = 6` and the two squares `13 = 3² + 2²`; at `p = 1093` the Fermat quotient vanishes (the
Wieferich prime), each an exact certificate of its shell. -/
theorem invariants_13_1093 :
    kur 13 % 13 = 10 ∧ fermatQuotient4 13 = 6 ∧ 3 * 3 + 2 * 2 = 13 ∧ isPrimeB 1093 = true ∧ fermatQuotient4 1093 = 0 := by
  decide +kernel

/-! #### The arcsin chain against a certified bracket of `π` (13:E3, H3) -/

/-- The arcsin chain `s_n = 3 Σ_{k ≤ n} C(2k,k)/((2k+1)16^k)` as an exact fraction `(num, den)`, with `C(2k,k)`
carried by the recurrence `C(2k+2,k+1) = C(2k,k)·2(2k+1)/(k+1)`: after step `k` the state is `(C(2k,k), num, den)`
of `s_k`. -/
def arcsinChain : Nat → Nat × Nat × Nat
  | 0 => (1, 3, 1)
  | k + 1 =>
    match arcsinChain k with
    | (c, num, den) =>
      let c' := c * (2 * (2 * k + 1)) / (k + 1)
      let d := (2 * (k + 1) + 1) * 16 ^ (k + 1)
      (c', num * d + 3 * c' * den, den * d)

/-- The lower end `L` of the rational bracket `L ≤ π ≤ U` of the Machin pairing at `m = 12`
(`FRC.Epi.pi_bracket_24` on Mathlib: `L = 4(4 S_{1/5}(25) − S_{1/239}(24))`), as `(numerator, denominator)`. -/
def piLo : Nat × Nat := (56982451095683495439374565467485478486061627198245408555021816811556209980957932490824931053425856737444302864615815079280095539452134822710663747992660383090256176690756, 18138077522740431478132504469278196026908888402936691374051205499784758924249616118578433027852823624088713136757082253607690672547607224629473421373404562473297119140625)

/-- The upper end `U` of the same bracket (`U = 4(4 S_{1/5}(24) − S_{1/239}(25))`), the width below `10⁻³⁶`. -/
def piHi : Nat × Nat := (130195783561461477719700582162729520693370052310728319298679169305810308737653928066126520396560009514814646871106941551053006194003594103465911391825667397563687081581706376, 41442605047058247458496271511585593410122504578565869919087156374128208580482492892372746919359245529262855323388051816332995956263674891122406052090809680521488189697265625)

/-- `|π − s_n| < 4⁻ⁿ/(2n+3)` decided on the bracket: `s_n − 4⁻ⁿ/(2n+3) < L` and `U < s_n + 4⁻ⁿ/(2n+3)`,
cross-multiplied in the naturals. -/
def tailWithin (n : Nat) : Bool :=
  match arcsinChain n, piLo, piHi with
  | (_, num, den), (a, b), (c, d) =>
    let q := 4 ^ n * (2 * n + 3)
    ((num * q - den) * b < a * den * q) && (c * den * q < (num * q + den) * d)

/-- 13:E3 — the tail bound of the arcsin chain, `|π − s_n| < 4⁻ⁿ/(2n+3)`, holds against the certified bracket of
`π` for every `1 ≤ n ≤ 40`. -/
theorem arcsin_tail_bound : (List.range 40).all (fun k => tailWithin (k + 1)) = true := by decide +kernel

/-- No integer `λ` satisfies `2πλ = p − 1` on the shell `p`: with `L = a/b ≤ π ≤ U = c/d`, the interval
`[(p−1)/(2U), (p−1)/(2L)] = [(p−1)d/(2c), (p−1)b/(2a)]` contains no integer, decided in the naturals as
`⌊(p−1)b/(2a)⌋ < ⌈(p−1)d/(2c)⌉`. -/
def noCalibration (p : Nat) : Bool :=
  match piLo, piHi with
  | (a, b), (c, d) =>
    let lo := ((p - 1) * d + 2 * c - 1) / (2 * c)
    let hi := ((p - 1) * b) / (2 * a)
    hi < lo
/-- The shells `p ≡ 1 (mod 4)`, `5 ≤ p ≤ 1657`, chunk 1 of the run of J3. -/
def shellsQ1 : List Nat :=
  [5, 13, 17, 29, 37, 41, 53, 61, 73, 89, 97, 101, 109, 113, 137, 149, 157, 173, 181, 193, 197, 229, 233, 241,
  257, 269, 277, 281, 293, 313, 317, 337, 349, 353, 373, 389, 397, 401, 409, 421, 433, 449, 457, 461, 509, 521,
  541, 557, 569, 577, 593, 601, 613, 617, 641, 653, 661, 673, 677, 701, 709, 733, 757, 761, 769, 773, 797, 809,
  821, 829, 853, 857, 877, 881, 929, 937, 941, 953, 977, 997, 1009, 1013, 1021, 1033, 1049, 1061, 1069, 1093,
  1097, 1109, 1117, 1129, 1153, 1181, 1193, 1201, 1213, 1217, 1229, 1237, 1249, 1277, 1289, 1297, 1301, 1321,
  1361, 1373, 1381, 1409, 1429, 1433, 1453, 1481, 1489, 1493, 1549, 1553, 1597, 1601, 1609, 1613, 1621, 1637,
  1657]
/-- The shells `p ≡ 1 (mod 4)`, `1669 ≤ p ≤ 3637`, chunk 2 of the run of J3. -/
def shellsQ2 : List Nat :=
  [1669, 1693, 1697, 1709, 1721, 1733, 1741, 1753, 1777, 1789, 1801, 1861, 1873, 1877, 1889, 1901, 1913, 1933,
  1949, 1973, 1993, 1997, 2017, 2029, 2053, 2069, 2081, 2089, 2113, 2129, 2137, 2141, 2153, 2161, 2213, 2221,
  2237, 2269, 2273, 2281, 2293, 2297, 2309, 2333, 2341, 2357, 2377, 2381, 2389, 2393, 2417, 2437, 2441, 2473,
  2477, 2521, 2549, 2557, 2593, 2609, 2617, 2621, 2633, 2657, 2677, 2689, 2693, 2713, 2729, 2741, 2749, 2753,
  2777, 2789, 2797, 2801, 2833, 2837, 2857, 2861, 2897, 2909, 2917, 2953, 2957, 2969, 3001, 3037, 3041, 3049,
  3061, 3089, 3109, 3121, 3137, 3169, 3181, 3209, 3217, 3221, 3229, 3253, 3257, 3301, 3313, 3329, 3361, 3373,
  3389, 3413, 3433, 3449, 3457, 3461, 3469, 3517, 3529, 3533, 3541, 3557, 3581, 3593, 3613, 3617, 3637]
/-- The shells `p ≡ 1 (mod 4)`, `3673 ≤ p ≤ 5821`, chunk 3 of the run of J3. -/
def shellsQ3 : List Nat :=
  [3673, 3677, 3697, 3701, 3709, 3733, 3761, 3769, 3793, 3797, 3821, 3833, 3853, 3877, 3881, 3889, 3917, 3929,
  3989, 4001, 4013, 4021, 4049, 4057, 4073, 4093, 4129, 4133, 4153, 4157, 4177, 4201, 4217, 4229, 4241, 4253,
  4261, 4273, 4289, 4297, 4337, 4349, 4357, 4373, 4397, 4409, 4421, 4441, 4457, 4481, 4493, 4513, 4517, 4549,
  4561, 4597, 4621, 4637, 4649, 4657, 4673, 4721, 4729, 4733, 4789, 4793, 4801, 4813, 4817, 4861, 4877, 4889,
  4909, 4933, 4937, 4957, 4969, 4973, 4993, 5009, 5021, 5077, 5081, 5101, 5113, 5153, 5189, 5197, 5209, 5233,
  5237, 5261, 5273, 5281, 5297, 5309, 5333, 5381, 5393, 5413, 5417, 5437, 5441, 5449, 5477, 5501, 5521, 5557,
  5569, 5573, 5581, 5641, 5653, 5657, 5669, 5689, 5693, 5701, 5717, 5737, 5741, 5749, 5801, 5813, 5821]
/-- The shells `p ≡ 1 (mod 4)`, `5849 ≤ p ≤ 8009`, chunk 4 of the run of J3. -/
def shellsQ4 : List Nat :=
  [5849, 5857, 5861, 5869, 5881, 5897, 5953, 5981, 6029, 6037, 6053, 6073, 6089, 6101, 6113, 6121, 6133, 6173,
  6197, 6217, 6221, 6229, 6257, 6269, 6277, 6301, 6317, 6329, 6337, 6353, 6361, 6373, 6389, 6397, 6421, 6449,
  6469, 6473, 6481, 6521, 6529, 6553, 6569, 6577, 6581, 6637, 6653, 6661, 6673, 6689, 6701, 6709, 6733, 6737,
  6761, 6781, 6793, 6829, 6833, 6841, 6857, 6869, 6917, 6949, 6961, 6977, 6997, 7001, 7013, 7057, 7069, 7109,
  7121, 7129, 7177, 7193, 7213, 7229, 7237, 7253, 7297, 7309, 7321, 7333, 7349, 7369, 7393, 7417, 7433, 7457,
  7477, 7481, 7489, 7517, 7529, 7537, 7541, 7549, 7561, 7573, 7577, 7589, 7621, 7649, 7669, 7673, 7681, 7717,
  7741, 7753, 7757, 7789, 7793, 7817, 7829, 7841, 7853, 7873, 7877, 7901, 7933, 7937, 7949, 7993, 8009]
/-- The 500 shells `p ≡ 1 (mod 4)`, `5 ≤ p ≤ 8009`, the four chunks concatenated. -/
def shells8009 : List Nat := shellsQ1 ++ shellsQ2 ++ shellsQ3 ++ shellsQ4
/-- The enumeration is complete: the four chunks are exactly the primes `p ≡ 1 (mod 4)` below `8010` by trial division. -/
theorem shells8009_complete :
    (List.range 8010).filter (fun q => 5 ≤ q && q % 4 == 1 && isPrimeB q) = shells8009 := by decide +kernel

/-- 13:H3, 13:I1, 13:I3 — exact calibration is impossible on every shell of the run: with `θ = 2πλ(i)/(p−1)`, no
integer `λ` makes `θ = 1` on any of the `500` shells `p ≡ 1 (mod 4)`, `p ≤ 8009`, decided on the certified bracket
of `π`. -/
theorem no_exact_calibration : shells8009.length = 500 ∧ shells8009.all noCalibration = true := by decide +kernel

/-! #### The readouts and the calibrated shell in the integers (13:D4, D5, H4) -/

/-- `|ε_n − d| < 2⁻⁵²` for `d = 6121026514868073/2⁵¹`, decided in the integers: `2·|n!·2⁵¹ − 6121026514868073·!n| < !n`. -/
def readoutWithin (n : Nat) : Bool :=
  2 * Int.natAbs ((fact n * 2 ^ 51 : Int) - 6121026514868073 * (dr n : Int)) < dr n

/-- 13:D4, 13:I1 — the binary64 readout of `e` in the integers: `ε₁₈ = 18!/!18` lies within the half-ulp of the
binary64 constant `6121026514868073/2⁵¹` and no `ε_n` with `2 ≤ n ≤ 17` does; `!18 = 2355301661033953`. -/
theorem readout_e_core :
    readoutWithin 18 = true ∧ (List.range 16).all (fun k => !readoutWithin (k + 2)) = true ∧
    dr 18 = 2355301661033953 ∧ fact 18 = 6402373705728000 := by decide +kernel

/-- 13:D5, 13:E5 — the step counts of the derangement chain: `n = 11, 18, 70` are the least `n` with
`8·2^k < (n+1)!` for `k = 24, 53, 333` (the enclosure bound `8/(n+1)!` below `2^{−k}`), decided in the integers. -/
theorem derangement_cost_core :
    (8 * 2 ^ 24 < fact 12 ∧ ¬ (8 * 2 ^ 24 < fact 11)) ∧ (8 * 2 ^ 53 < fact 19 ∧ ¬ (8 * 2 ^ 53 < fact 18)) ∧
    (8 * 2 ^ 333 < fact 71 ∧ ¬ (8 * 2 ^ 333 < fact 70)) := by decide +kernel

/-- 13:H4 — the shell data of the best calibrated shell below `10⁶`: `778933` is prime, `≡ 1 (mod 4)`, and
`123966` is a quarter-turn, `123966² ≡ −1 (mod 778933)` (the angle bound against `π` is the Mathlib witness). -/
theorem calibrated_shell_core :
    isPrimeB 778933 = true ∧ 778933 % 4 = 1 ∧ (123966 * 123966) % 778933 = 778932 := by decide +kernel

/-! #### The height run (13:J3, J5) -/

/-- The prime factors of `n` by trial division from `d` with fuel, each factor repeated with its multiplicity. -/
def primeFactorsFrom (n d : Nat) : Nat → List Nat
  | 0 => []
  | fuel + 1 =>
    if n < 2 then [] else if n < d * d then [n]
    else if n % d == 0 then d :: primeFactorsFrom (n / d) d fuel
    else primeFactorsFrom n (d + 1) fuel

/-- The prime factors of `n`. -/
def primeFactors (n : Nat) : List Nat := primeFactorsFrom n 2 n

/-- `g` is a primitive root modulo the prime `p`: `g^{(p−1)/q} ≠ 1` for every prime `q ∣ p − 1`. -/
def isPrimRoot (p g : Nat) : Bool := (primeFactors (p - 1)).all (fun q => g ^ ((p - 1) / q) % p != 1)

/-- The first primitive root at or above `g`, searched with fuel (`0` when the fuel runs out). -/
def primRootFrom (p g : Nat) : Nat → Nat
  | 0 => 0
  | fuel + 1 => if isPrimRoot p g then g else primRootFrom p (g + 1) fuel

/-- The smallest primitive root modulo `p`. -/
def smallestPrimRoot (p : Nat) : Nat := primRootFrom p 2 p

/-- The centred absolute value `|ctr x|` of a residue `x < p`. -/
def ctrAbs (p x : Nat) : Nat := if 2 * x ≤ p then x else p - x

/-- `H_B(x) = min_{1 ≤ a ≤ B} max(a, |ctr(a·x)|)`, the height searched up to `a = B` (`H_0 = p`). -/
def heightSearch (p x : Nat) : Nat → Nat
  | 0 => p
  | a + 1 => min (heightSearch p x a) (max (a + 1) (ctrAbs p ((a + 1) * x % p)))

/-- The height searched within the band `a ≤ 200`: on every shell of the run `H ≤ 2√p < 180` (the clause
`H² ≤ 4p` of `height_run`), so a multiplier `a > 200` gives `max(a, ·) > H`, and the minimum over all `a ≥ 1` is the
minimum over the band. -/
def height (p x : Nat) : Nat := heightSearch p x 200

/-- The exponential unit `e_p = g^{λ(i)}` with `i = g^{−κ} = g^{3κ}` the quarter-turn, in the frame of `g`. -/
def expUnit (p g : Nat) : Nat := g ^ (g ^ (3 * ((p - 1) / 4)) % p) % p

/-- The exponential unit of the conjugate chart, `g^{λ(−i)}`. -/
def expUnitConj (p g : Nat) : Nat := g ^ (p - g ^ (3 * ((p - 1) / 4)) % p) % p

/-- `H(e_p)` minimised over the two chiralities, in the smallest-primitive-root frame. -/
def heightE (p : Nat) : Nat :=
  let g := smallestPrimRoot p
  min (height p (expUnit p g)) (height p (expUnitConj p g))
theorem height_run_q1 :
    shellsQ1.all (fun p => heightE p * heightE p ≤ 4 * p) = true ∧
    (shellsQ1.filter (fun p => heightE p ≤ 10)).length = 48 ∧
    shellsQ1.filter (fun p => heightE p == 2) = [13] := by decide +kernel
theorem height_run_q2 :
    shellsQ2.all (fun p => heightE p * heightE p ≤ 4 * p) = true ∧
    (shellsQ2.filter (fun p => heightE p ≤ 10)).length = 10 ∧
    shellsQ2.filter (fun p => heightE p == 2) = [1933] := by decide +kernel
theorem height_run_q3 :
    shellsQ3.all (fun p => heightE p * heightE p ≤ 4 * p) = true ∧
    (shellsQ3.filter (fun p => heightE p ≤ 10)).length = 3 ∧
    shellsQ3.filter (fun p => heightE p == 2) = [4177] := by decide +kernel
theorem height_run_q4 :
    shellsQ4.all (fun p => heightE p * heightE p ≤ 4 * p) = true ∧
    (shellsQ4.filter (fun p => heightE p ≤ 10)).length = 7 ∧
    shellsQ4.filter (fun p => heightE p == 2) = [5857] := by decide +kernel
/-- 13:J3 — the height run: over the `500` shells `p ≡ 1 (mod 4)`, `p ≤ 8009` (the enumeration complete),
`H(e_p) ≤ 2√p` on every shell (the horizon band), exactly `68` shells have `H ≤ 10`, and the pin value `2` is reached
on exactly `{13, 1933, 4177, 5857}`. -/
theorem height_run :
    (List.range 8010).filter (fun q => 5 ≤ q && q % 4 == 1 && isPrimeB q) = shells8009 ∧ shells8009.length = 500 ∧
    shells8009.all (fun p => heightE p * heightE p ≤ 4 * p) = true ∧
    (shells8009.filter (fun p => heightE p ≤ 10)).length = 68 ∧
    shells8009.filter (fun p => heightE p == 2) = [13, 1933, 4177, 5857] := by
  refine ⟨shells8009_complete, by decide +kernel, ?_, ?_, ?_⟩
  · rw [shells8009, all_append_nat, all_append_nat, all_append_nat, height_run_q1.1, height_run_q2.1,
      height_run_q3.1, height_run_q4.1]
    rfl
  · rw [shells8009, filter_append_nat, filter_append_nat, filter_append_nat, length_append_nat,
      length_append_nat, length_append_nat, height_run_q1.2.1, height_run_q2.2.1, height_run_q3.2.1,
      height_run_q4.2.1]
  · rw [shells8009, filter_append_nat, filter_append_nat, filter_append_nat, height_run_q1.2.2,
      height_run_q2.2.2, height_run_q3.2.2, height_run_q4.2.2]
    rfl

/-- 13:J5 — the certification split: the half-period is pinned by the height-two relation `2π_A + 1 ≡ 0` on every
frame shell (J2), while `e_p` reaches the pin value `2` on exactly four of the `500` shells of the run and otherwise
sits in the horizon band `H(e_p) ≤ 2√p`: no pinned residue and no cross-shell certificate for `e_p`. -/
theorem pin_contrast :
    (∀ {p : Nat} [Pos p] {κ : Nat} {g : Shell p}, Frame p κ g → (ofNat (2 * halfPeriod κ) : Shell p) = -1) ∧
    shells8009.filter (fun p => heightE p == 2) = [13, 1933, 4177, 5857] ∧
    shells8009.all (fun p => heightE p * heightE p ≤ 4 * p) = true :=
  ⟨fun F => F.two_pi, height_run.2.2.2.2, height_run.2.2.1⟩

end census

/-! ## Old names (ledger migration, task LM17): the declarations moved to the themes, each under its old name -/
section aliases
variable {p : Nat} [Pos p] {κ : Nat} {g : Shell p}

/-- `p ≡ 0` on the shell. -/
theorem ofNat_self : (ofNat p : Shell p) = 0 :=
  FRC.Shell.Frame.ofNat_self

theorem ofNat_add_self (n : Nat) : (ofNat (n + p) : Shell p) = ofNat n :=
  FRC.Shell.Frame.ofNat_add_self n

end aliases

-- Ledger predicates of 13-epi (generated by make_predicates.py from docs/13-epi/13-epi-ledger.json; edit the ledger, not this section)
/-- 13:B2 (p13009) — Orientation transport: under $\gen'=\gen^{u}$, $\gcd(u,\p-1)=1$, the re-derived quarter-turn is $\im'=\im$ exactly when $u\equiv1\pmod4$ and $\im'=-\im$ (the conjugate chart) when $u\equiv3\pmod4$; there is no third case, and every chirality-sensitive statement holds for the other chirality under $\im\mapsto-\im$. -/
theorem p13009 : (∀ {p κ : Nat} [FRC.Pos p] {g : FRC.Shell p}, FRC.Shell.Frame p κ g → ∀ {u : Nat}, FRC.Shell.Coprime u (p - (1 : Nat)) → (u % (4 : Nat) = (1 : Nat) ∨ u % (4 : Nat) = (3 : Nat)) ∧ (u % (4 : Nat) = (1 : Nat) → FRC.Shell.Frame.quarterTurn (g ^ u) κ = FRC.Shell.Frame.quarterTurn g κ) ∧ (u % (4 : Nat) = (3 : Nat) → FRC.Shell.Frame.quarterTurn (g ^ u) κ = -FRC.Shell.Frame.quarterTurn g κ)) ∧ ∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → ∀ (u : Nat), (u % (4 : Nat) = (1 : Nat) → -(g ^ u) ^ κ = -g ^ κ) ∧ (u % (4 : Nat) = (3 : Nat) → -(g ^ u) ^ κ = - -g ^ κ) :=
  And.intro @FRC.Epi.orientation_transport (@FRC.Shell.Frame.orientation_class)
/-- 13:B3 (p13010) — The coincidence that forces the typing: at $\p=13$ the field element $6$ is at once $\eP$, $\piA$ and the reading of $-1/2$, while $\eR\ne\piR$; no map from a bare residue to a real number exists, and the external comparison takes the structural role as part of its input --- roles, not residues, carry external meaning. Witnessed by the two towers reading the same element $6$ as $\eP$ and as $\piA$. -/
theorem p13010 : FRC.Shell.Frame.quarterTurn (2 : FRC.Shell (13 : Nat)) (3 : Nat) = (5 : FRC.Shell (13 : Nat)) ∧ (2 : FRC.Shell (13 : Nat)) ^ (FRC.Shell.Frame.quarterTurn (2 : FRC.Shell (13 : Nat)) (3 : Nat)).val = (6 : FRC.Shell (13 : Nat)) ∧ FRC.Shell.ofNat (FRC.Shell.Frame.halfPeriod (3 : Nat)) = (6 : FRC.Shell (13 : Nat)) ∧ (2 : FRC.Shell (13 : Nat)) * (6 : FRC.Shell (13 : Nat)) = (-1 : FRC.Shell (13 : Nat)) :=
  @FRC.Epi.coincidence13
/-- 13:D4 (p13020) — Horizon determination of the readout: $\ro(\varepsilon_n)=\ro(\eR)$ for $n\ge n_0(k)=\Theta(k/\log k)$; the binary64 constant for $e$ is the readout of $\varepsilon_{18}=18!/\dr{18}=6402373705728000/2355301661033953$ and $n=18$ is minimal ($\varepsilon_{17}$ fails readout equality, $|\varepsilon_{17}-\eR|=1.10\times10^{-15}$ above the half-ulp); the first $100$ significant digits of $\eR$ are those of $\varepsilon_{70}$; every floating-point value of $e$ is a plateau readout. -/
theorem p13020 : FRC.Epi.readoutWithin (18 : Nat) = true ∧ ((List.range (16 : Nat)).all fun k => !FRC.Epi.readoutWithin (k + (2 : Nat))) = true ∧ FRC.Epi.dr (18 : Nat) = (2355301661033953 : Nat) ∧ FRC.Epi.fact (18 : Nat) = (6402373705728000 : Nat) :=
  @FRC.Epi.readout_e_core
/-- 13:D5 (p13021) — Feasibility selection: the compound chain $(1+1/n)^{n}$ costs $n\asymp2^{k}$ steps for $k$ bits against $n_0(k)=\Theta(k/\log k)$ for the derangement chain ($n=11,18,70$ at $k=24,53,333$); within a horizon $H$ the compound chain realises $O(\log H)$ bits and the factorial chain $\Theta(H\log H)$; under the feasibility principle the derangement representation is the canonical finite definition of $e$. -/
theorem p13021 : ((8 : Nat) * (2 : Nat) ^ (24 : Nat) < FRC.Epi.fact (12 : Nat) ∧ ¬(8 : Nat) * (2 : Nat) ^ (24 : Nat) < FRC.Epi.fact (11 : Nat)) ∧ ((8 : Nat) * (2 : Nat) ^ (53 : Nat) < FRC.Epi.fact (19 : Nat) ∧ ¬(8 : Nat) * (2 : Nat) ^ (53 : Nat) < FRC.Epi.fact (18 : Nat)) ∧ (8 : Nat) * (2 : Nat) ^ (333 : Nat) < FRC.Epi.fact (71 : Nat) ∧ ¬(8 : Nat) * (2 : Nat) ^ (333 : Nat) < FRC.Epi.fact (70 : Nat) :=
  @FRC.Epi.derangement_cost_core
/-- 13:E3 (p13024) — The arcsin chain $s_n=3\sum_{k\le n}\Cb{k}/((2k+1)16^{k})\in\fQ$ with external completion $\piR=6\arcsin\frac12$ \chart{} and tail bound $|\piR-s_n|<4^{-n}/(2n+3)$ for $n\ge1$: geometric rate from the same combinatorial atoms as the Wallis pair. -/
theorem p13024 : ((List.range (40 : Nat)).all fun k => FRC.Epi.tailWithin (k + (1 : Nat))) = true :=
  @FRC.Epi.arcsin_tail_bound
/-- 13:E5 (p13026) — The feasibility hierarchy: among $\fQ$-native constructors of $\pi$ the best known rate is geometric, $\Theta(k)$ steps (Machin, arcsin), against $\Theta(k/\log k)$ for the derangement chain of $e$; the circle count and the Leibniz/Wallis chains sit at $2^{k}$; the AGM is not $\fQ$-native. A factorial-rate chain exists for every real by rounding (and for $\pi$ by rounding the Machin chain), so the split is by kind of chain --- E-partial sums ($e$) against G-partial sums ($\pi$), master C26; whether $\piR$ is the value of an E-function with rational coefficients at a rational point is a question of the continuum (Fischler--Rivoal's conjecture $\operatorname{Frac}\mathcal E\cap\operatorname{Frac}\mathcal G=\overline{\Q}$ would answer it negatively), not a predicate of the frame. -/
theorem p13026 : ((8 : Nat) * (2 : Nat) ^ (24 : Nat) < FRC.Epi.fact (12 : Nat) ∧ ¬(8 : Nat) * (2 : Nat) ^ (24 : Nat) < FRC.Epi.fact (11 : Nat)) ∧ ((8 : Nat) * (2 : Nat) ^ (53 : Nat) < FRC.Epi.fact (19 : Nat) ∧ ¬(8 : Nat) * (2 : Nat) ^ (53 : Nat) < FRC.Epi.fact (18 : Nat)) ∧ (8 : Nat) * (2 : Nat) ^ (333 : Nat) < FRC.Epi.fact (71 : Nat) ∧ ¬(8 : Nat) * (2 : Nat) ^ (333 : Nat) < FRC.Epi.fact (70 : Nat) :=
  @FRC.Epi.derangement_cost_core
set_option linter.defProp false in
/-- 13:F2 (p13028) — The wall identity and the terminal residue of $e$: $\dr{(\p-1)}\equiv\Ku{\p}\pmod\p$ (the odd-prime case of the Mijajlovi\'c--\v Sami congruence, A4), hence $\rep{\varepsilon_{\p-1}}=-(\Ku{\p})^{-1}$ whenever $\p\nmid\Ku{\p}$; existence of the terminal link on a shell is equivalent to $\p\nmid\Ku{\p}$, universal existence over the shells of the totality to the vanishing of Kurepa's certificate (Z1); re-verified in the derangement form for all $121{,}126$ odd primes $\p<1.6\times10^{6}$ with zero failures of either condition. Beyond the wall $n!\equiv0$: $n=\p-1$ is the factorial horizon. -/
def p13028 := @FRC.Epi.terminal13
set_option linter.defProp false in
/-- 13:F3 (p13029) — Antiperiodicity: $\dr{(n+\p)}\equiv-\dr{n}\pmod\p$ for every odd prime $\p$ and every $n\ge0$ of the totality, so $\dr{n}\bmod\p$ depends on $n\bmod2\p$; the blind set $Z_0(\p)=\{n<\p:\dr{n}\equiv0\}$ always contains $1$, and Kurepa's hypothesis is $\p-1\notin Z_0(\p)$ for every odd prime $\p$ of the totality. -/
def p13029 := And.intro @FRC.Epi.dr_antiperiodic (@FRC.Epi.dr_succ)
/-- 13:F4 (p13030) — Series duals at the wall: $\sum_{k<\p}(-1)^{k}/k!\equiv-\Ku{\p}$ and $\sum_{k<\p}1/k!\equiv-A(\p)$, $A(\p)$ the alternating factorial sum; the group law $\exp(1)\exp(-1)=1$ does not survive, $\Ku{\p}A(\p)\equiv3,0,21,28,132,258$ at $\p=7,13,29,101,257,1009$; on $\p=13$ the direct series residue vanishes ($A(13)\equiv0$) while the derangement side survives ($\Ku{13}\equiv10$) --- a second ground for the canonicity of D5. -/
theorem p13030 : FRC.Epi.kurS (7 : Nat) * FRC.Epi.altS (7 : Nat) = (3 : FRC.Shell (7 : Nat)) ∧ FRC.Epi.kurS (13 : Nat) * FRC.Epi.altS (13 : Nat) = (0 : FRC.Shell (13 : Nat)) ∧ FRC.Epi.altS (13 : Nat) = (0 : FRC.Shell (13 : Nat)) ∧ FRC.Epi.kurS (29 : Nat) * FRC.Epi.altS (29 : Nat) = (21 : FRC.Shell (29 : Nat)) ∧ FRC.Epi.kurS (101 : Nat) * FRC.Epi.altS (101 : Nat) = (28 : FRC.Shell (101 : Nat)) ∧ FRC.Epi.kurS (257 : Nat) * FRC.Epi.altS (257 : Nat) = (132 : FRC.Shell (257 : Nat)) ∧ FRC.Epi.kurS (1009 : Nat) * FRC.Epi.altS (1009 : Nat) = (258 : FRC.Shell (1009 : Nat)) :=
  @FRC.Epi.kurepa_alt_values
/-- 13:F5 (p13031) — Blind-scale statistics: over the $501$ primes in $(1000,5000)$ the sizes $|Z_0(\p)|$ distribute as $1^{(169)},2^{(209)},3^{(92)},4^{(22)},5^{(6)},6^{(2)},7^{(1)}$, mean $1.996$, the excess over the forced $n=1$ matching Poisson$(1)$ \apx{} (the model: $\dr{n}\bmod\p$ uniform for $2\le n\le\p-2$, the wall excluded; extended to the $1593$ primes in $(5000,20000)$: $1^{(597)},2^{(569)},3^{(299)},4^{(108)},5^{(17)},6^{(3)}$, mean $1.988$); blind scales never obstruct the plateau of D4 (advance at most $|Z_0(\p)|$ steps past $n_0$). The counts are exact; the Poisson reading is the model they match. -/
theorem p13031 : FRC.Epi.primes1000to1300.length = (43 : Nat) ∧ List.map FRC.Epi.blindCount FRC.Epi.primes1000to1300 = have y := have y := have y := [(1 : Nat), (2 : Nat), (2 : Nat), (1 : Nat), (2 : Nat), (3 : Nat)]; (2 : Nat) :: (3 : Nat) :: (1 : Nat) :: (2 : Nat) :: (1 : Nat) :: y; have y := (2 : Nat) :: (2 : Nat) :: (2 : Nat) :: (4 : Nat) :: (1 : Nat) :: (2 : Nat) :: y; (2 : Nat) :: (5 : Nat) :: (2 : Nat) :: (1 : Nat) :: (1 : Nat) :: y; have y := have y := (2 : Nat) :: (3 : Nat) :: (2 : Nat) :: (1 : Nat) :: (3 : Nat) :: (1 : Nat) :: y; (2 : Nat) :: (2 : Nat) :: (1 : Nat) :: (3 : Nat) :: (3 : Nat) :: y; have y := (4 : Nat) :: (1 : Nat) :: (4 : Nat) :: (2 : Nat) :: (1 : Nat) :: y; (1 : Nat) :: (2 : Nat) :: (2 : Nat) :: (1 : Nat) :: (2 : Nat) :: y :=
  @FRC.Epi.blind_census
set_option linter.defProp false in
/-- 13:F6 (p13032) — The $\p=13$ picture: the residue line $\rep{\varepsilon_n}$, $n=2,\dots,12$, is $2,3,7,11,1,6,\text{blind},2,8,10,9$ --- blind at $n=8$ ($\dr{8}=14833=13\cdot1141$) and terminating on $\rep{\varepsilon_{12}}=-(\Ku{13})^{-1}=9$, the common reading of $6/5$ and $11/7$ --- while the metric row freezes onto $2.71828\ldots$ by $n\approx9$: the thesis in miniature. -/
def p13032 := And.intro @FRC.Epi.residue_line_e13 (@FRC.Epi.terminal13)
/-- 13:F7 (p13033) — The fixed-shell tower of $e$: with $\delta_m=\ctr{(-1)^{m}\eP}$ and $q_m=((m\p)!+\delta_m)/\dr{(m\p)}$, $\rep{q_m}=\eP$ exactly at every grade (since $(m\p)!\equiv0$ and $\dr{(m\p)}\equiv(-1)^{m}$ by F3) while $q_m\to\eR$ with the certificate $|q_m-\eR|<(m\p)!/(\dr{(m\p)}\dr{(m\p+1)})+2\kap/\dr{(m\p)}$; on $\p=13$, $q_2$ differs from $\eR$ by $3.98\times10^{-26}$ and every member reads $6$. Compatibility, not selection. -/
theorem p13033 : ∀ {p : Nat} [FRC.Pos p] {κ : Nat}, p = (4 : Nat) * κ + (1 : Nat) → ∀ (m : Nat) (e δ : FRC.Shell p), δ = (-1 : FRC.Shell p) ^ (m + (1 : Nat)) * e → FRC.Shell.ofNat (FRC.Epi.fact ((m + (1 : Nat)) * p)) = (0 : FRC.Shell p) ∧ FRC.Shell.ofNat (FRC.Epi.dr ((m + (1 : Nat)) * p)) = (-1 : FRC.Shell p) ^ (m + (1 : Nat)) ∧ FRC.Shell.ofNat (FRC.Epi.fact ((m + (1 : Nat)) * p)) + δ = FRC.Shell.ofNat (FRC.Epi.dr ((m + (1 : Nat)) * p)) * e :=
  @FRC.Epi.tower_e_exact
/-- 13:G1 (p13034) — The legibility window: with $m=(\p-1)/2$, $\p\nmid\Cb{n}$ for $1\le n\le m$ and $\p\mid\Cb{n}$ for $m<n<\p$ (Kummer, A3): the residue line of the Wallis chain is defined on exactly $[1,m]$, blind-free below the wall and totally blind on $(m,\p)$; on a frame shell the last legible scale $n=2\kap$ is the angular address of $-1$. -/
theorem p13034 : List.map (fun k => FRC.Epi.readW (k + (1 : Nat))) (List.range (6 : Nat)) = [(4 : FRC.Shell (13 : Nat)), (5 : FRC.Shell (13 : Nat)), (10 : FRC.Shell (13 : Nat)), (9 : FRC.Shell (13 : Nat)), (6 : FRC.Shell (13 : Nat)), (11 : FRC.Shell (13 : Nat))] ∧ (11 : FRC.Shell (13 : Nat)) = (-2 : FRC.Shell (13 : Nat)) ∧ (10 : FRC.Shell (13 : Nat)) * ((3 : FRC.Shell (13 : Nat)) * (3 : FRC.Shell (13 : Nat))) = (-1 : FRC.Shell (13 : Nat)) ∧ List.map (fun n => decide (FRC.Epi.cb n % (13 : Nat) = (0 : Nat))) (List.range (13 : Nat)) = [false, false, false, false, false, false, false, true, true, true, true, true, true] :=
  @FRC.Epi.residue_line_pi13
/-- 13:G5 (p13038) — Lucas revivals and self-similarity: beyond the wall $n\ge\p$ is legible for $w$ precisely when every base-$\p$ digit of $n$ is at most $m$ and $\p\nmid n$ (on $\p=13$ the two-digit revivals number $(2\kap)^{2}=36$); on revival scales $\Cb{n}$ factorises digitwise (Lucas, A3); at the first revival $\rep{v_\p}\equiv8$ universally and $v_\p\equiv8+16\p(2q_\p(2)-1)\pmod{\p^{2}}$ by Wolstenholme. -/
theorem p13038 : FRC.Epi.readV (13 : Nat) = (8 : FRC.Shell (13 : Nat)) ∧ (List.filter (fun n => decide ((13 : Nat) ≤ n) && decide (FRC.Epi.cb n % (13 : Nat) ≠ (0 : Nat)) && decide (n % (13 : Nat) ≠ (0 : Nat))) (List.range (169 : Nat))).length = (36 : Nat) :=
  @FRC.Epi.revivals13
/-- 13:G6 (p13039) — First-order wall vanishing of the arcsin chain: $\sigma_\p=\sum_{k<m}\Cb{k}/((2k+1)16^{k})\equiv0\pmod\p$ for every prime $\p\ge5$ of the totality, $\sigma_3=1$ the sole exception; proved entirely in finite arithmetic through the key identity $A+B=2L$ (coefficient bookkeeping of the formal antiderivative of $(1-s^{2})^{m}$), Wilson reflection, Lerch's congruence and the binomial transfer $\Cb{k}\equiv(-4)^{k}\binom mk$. Verified for all $428$ odd primes $5\le\p<3000$; the ingredients for $m\le60$, $\p<500$. -/
theorem p13039 : List.filter (fun q => decide ((5 : Nat) ≤ q) && FRC.Epi.isPrimeB q) (List.range (3000 : Nat)) = FRC.Epi.oddPrimesBelow3000 ∧ FRC.Epi.oddPrimesBelow3000.length = (428 : Nat) ∧ (FRC.Epi.oddPrimesBelow3000.all fun p => FRC.Epi.sigmaZero p p) = true ∧ FRC.Epi.sigmaZero (3 : Nat) (3 : Nat) = false :=
  @FRC.Epi.sigma_vanishes_all
/-- 13:G7 (p13040) — Second and third order at the arcsin wall: $\sigma_\p\equiv0\pmod{\p^{2}}$ is Sun's theorem (A5), re-verified for $5\le\p<300$; the blind-range sum $\sum_{m<k<\p}\Cb{k}/((2k+1)16^{k})\equiv\p E_{\p-3}/3\pmod{\p^{2}}$ (A5), re-verified for $5\le\p<80$; at third order $\sigma_\p/\p^{2}\equiv(-1)^{(\p+1)/2}B_{\p-3}/36\pmod\p$ for all sixty primes $5\le\p<300$, the mod-$\p^{3}$ reading of Sun's Conjecture 5.1 with the Wolstenholme refinement, a theorem for every prime $\p\ge5$ of the totality (A8): Wolstenholme-trivial at orders $\p,\p^{2}$, Bernoulli at $\p^{3}$, the Euler content beyond the wall. -/
theorem p13040 : FRC.Epi.primes5to300.length = (60 : Nat) ∧ (FRC.Epi.primes5to300.all fun p => FRC.Epi.sigmaZero p (p * p)) = true :=
  @FRC.Epi.sigma_vanishes_mod_sq
/-- 13:G8 (p13041) — The $\p=13$ picture for $\pi$: $\kap=3$, wall at $n=6$; the residue line $\rep{w_n}$, $n=1,\dots,6$, is $4,5,10,9,6,11$ with $\rep{w_6}=11\equiv-2$ the calibration face and $\rep{w_3}=10\equiv-(3^{2})^{-1}$ encoding $13=3^{2}+2^{2}$; empty blind set below the wall, total blindness for $n=7,\dots,12$, first revival $\rep{v_{13}}=8$. -/
theorem p13041 : List.map (fun k => FRC.Epi.readW (k + (1 : Nat))) (List.range (6 : Nat)) = [(4 : FRC.Shell (13 : Nat)), (5 : FRC.Shell (13 : Nat)), (10 : FRC.Shell (13 : Nat)), (9 : FRC.Shell (13 : Nat)), (6 : FRC.Shell (13 : Nat)), (11 : FRC.Shell (13 : Nat))] ∧ (11 : FRC.Shell (13 : Nat)) = (-2 : FRC.Shell (13 : Nat)) ∧ (10 : FRC.Shell (13 : Nat)) * ((3 : FRC.Shell (13 : Nat)) * (3 : FRC.Shell (13 : Nat))) = (-1 : FRC.Shell (13 : Nat)) ∧ List.map (fun n => decide (FRC.Epi.cb n % (13 : Nat) = (0 : Nat))) (List.range (13 : Nat)) = [false, false, false, false, false, false, false, true, true, true, true, true, true] :=
  @FRC.Epi.residue_line_pi13
/-- 13:H2 (p13044) — The exact angular carrier of $\pi$: $\chi(-1)=e^{\imR\piR}$ exactly in every shell, for every generator and either chirality, since $-1=\gen^{(\p-1)/2}$ sits at arc fraction one half --- Euler's identity as the half-turn tautology $\gen^{2\kap}=-1$ under the dictionary, with no calibration and no error term. -/
theorem p13044 : ∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → g ^ ((2 : Nat) * κ) = (-1 : FRC.Shell p) :=
  @FRC.Ledger.p13044
/-- 13:H3 (p13045) — Exact calibration of $e$ is impossible: with $\theta=2\piR\lambda(\im)/(\p-1)$ the frame angle of $\eP$, $\theta\ne1$ in every shell ($\theta=1$ would make $\piR$ rational, A2); $\chi(\eP)$ is a root of unity while $e^{\imR}$ is not, so the identification is intrinsically horizon-limited. -/
theorem p13045 : FRC.Epi.shells8009.length = (500 : Nat) ∧ FRC.Epi.shells8009.all FRC.Epi.noCalibration = true :=
  @FRC.Epi.no_exact_calibration
/-- 13:H4 (p13069) — Calibrated shells at every precision the totality resolves: the $\varepsilon$-calibrated shells are a fraction $2\varepsilon/\piR$ \apx{} of the shells $\p\equiv1\pmod4$ below any bound of the totality, for every $\varepsilon$ above the nearest-hit scale $\piR/(2N)$, and $\chi(\eP)$ approaches $e^{\imR}$ along them. Below $10^{6}$: $260$ shells within $0.01$ against $249$ predicted; the best, $\p=778933$, within $4\times10^{-5}$, decided exactly. -/
theorem p13069 : FRC.Epi.isPrimeB (778933 : Nat) = true ∧ (778933 : Nat) % (4 : Nat) = (1 : Nat) ∧ (123966 : Nat) * (123966 : Nat) % (778933 : Nat) = (778932 : Nat) :=
  @FRC.Epi.calibrated_shell_core
set_option linter.defProp false in
/-- 13:I1 (p13048) — Emergence of the classical $e$: (i) in every shell with $\p>n_0+|Z_0(\p)|+1$ a non-blind scale in $[n_0,n_0+|Z_0(\p)|]$ reads out $\ro(\eR)$, at binary64 exactly $18!/\dr{18}$; (ii) the frame-internal continuation is the antiperiodic residue line with blind set $Z_0(\p)$ and terminal invariant $-(\Ku{\p})^{-1}$, collapsed by the readout to one dyadic rational; (iii) $\chi(\eP)$ approaches $e^{\imR}$ along the calibrated shells of the totality, exact calibration impossible, no pointwise link between the carriers. Composed from D4, F2, F3, F5, H3--H5. -/
def p13048 := And.intro @FRC.Epi.readout_e_core (And.intro @FRC.Epi.terminal13 (And.intro @FRC.Epi.dr_antiperiodic (And.intro @FRC.Epi.blind_census (@FRC.Epi.no_exact_calibration))))
/-- 13:I2 (p13049) — Emergence of the classical $\pi$: (i) the plateau readout of $\fQ$-native chains, at binary64 exactly $M_{10}$, the Wallis pair certifying two-sided enclosures at every scale; (ii) the residue line on $[1,2\kap]$ with the quarter-wall invariant $-(a^{2})^{-1}$, the half-wall terminus $-2$, the second-order Fermat quotient with $\pi$-Wieferich set $\{5,45827\}$, Morley exactness at $\p^{3}$, total blindness beyond the address of $-1$, Lucas revivals, the arcsin wall vanishing to $\p^{2}$ with the Bernoulli third order and the Euler content displaced beyond the wall; (iii) $\chi(-1)=e^{\imR\piR}$ exactly. Composed from E2, E4, G1--G7, H2. -/
theorem p13049 : (List.map (fun k => FRC.Epi.readW (k + (1 : Nat))) (List.range (6 : Nat)) = [(4 : FRC.Shell (13 : Nat)), (5 : FRC.Shell (13 : Nat)), (10 : FRC.Shell (13 : Nat)), (9 : FRC.Shell (13 : Nat)), (6 : FRC.Shell (13 : Nat)), (11 : FRC.Shell (13 : Nat))] ∧ (11 : FRC.Shell (13 : Nat)) = (-2 : FRC.Shell (13 : Nat)) ∧ (10 : FRC.Shell (13 : Nat)) * ((3 : FRC.Shell (13 : Nat)) * (3 : FRC.Shell (13 : Nat))) = (-1 : FRC.Shell (13 : Nat)) ∧ List.map (fun n => decide (FRC.Epi.cb n % (13 : Nat) = (0 : Nat))) (List.range (13 : Nat)) = [false, false, false, false, false, false, false, true, true, true, true, true, true]) ∧ (FRC.Epi.readV (13 : Nat) = (8 : FRC.Shell (13 : Nat)) ∧ (List.filter (fun n => decide ((13 : Nat) ≤ n) && decide (FRC.Epi.cb n % (13 : Nat) ≠ (0 : Nat)) && decide (n % (13 : Nat) ≠ (0 : Nat))) (List.range (169 : Nat))).length = (36 : Nat)) ∧ (List.filter (fun q => decide ((5 : Nat) ≤ q) && FRC.Epi.isPrimeB q) (List.range (3000 : Nat)) = FRC.Epi.oddPrimesBelow3000 ∧ FRC.Epi.oddPrimesBelow3000.length = (428 : Nat) ∧ (FRC.Epi.oddPrimesBelow3000.all fun p => FRC.Epi.sigmaZero p p) = true ∧ FRC.Epi.sigmaZero (3 : Nat) (3 : Nat) = false) ∧ FRC.Epi.primes5to300.length = (60 : Nat) ∧ (FRC.Epi.primes5to300.all fun p => FRC.Epi.sigmaZero p (p * p)) = true :=
  And.intro @FRC.Epi.residue_line_pi13 (And.intro @FRC.Epi.revivals13 (And.intro @FRC.Epi.sigma_vanishes_all (@FRC.Epi.sigma_vanishes_mod_sq)))
set_option linter.defProp false in
/-- 13:I3 (p13050) — The duality: $\pi$ is angular-exact and wall-trivial (tautological carrier, terminus the calibration face $-2$, Fermat quotient one order down, two-squares quarter invariant, empty blind set below the wall, geometric $\fQ$-rate, the series law split Bernoulli/Euler across the wall) and $e$ angular-approximate and wall-wild (calibration impossible, terminus the open Kurepa quantity, no quarter invariant, Poisson blind set, factorial $\fQ$-rate, the group law broken at the wall); each constant exact on the axis where the other is approximate: $\pi$ a structural, $e$ a statistical constant of the finite frame. -/
def p13050 := And.intro @FRC.Epi.residue_line_pi13 (And.intro @FRC.Epi.terminal13 (And.intro @FRC.Epi.kurepa_alt_values (And.intro @FRC.Epi.blind_census (@FRC.Epi.no_exact_calibration))))
/-- 13:I4 (p13051) — CRT stability: under the composite lift to $q=\prod\p_i$ the half-wall invariant of $\pi$ glues to $-2$ modulo every $q$, since $2\piA\equiv-1$ holds in every fibre, while the terminal content of $e$, $(-(\Ku{\p_i})^{-1})_i$, varies fibrewise. The two selectors resolve the $\p=13$ coincidence: the same residue $6$ reaches $\piR$ through C4 and $\eR$ through C1. -/
theorem p13051 : ∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → FRC.Shell.ofNat ((2 : Nat) * FRC.Shell.Frame.halfPeriod κ) = (-1 : FRC.Shell p) :=
  @FRC.Ledger.p13051
/-- 13:I5 (p13068) — The three frame invariants across shells: on the $4783$ shells $\p\equiv1\pmod4$ below $10^{5}$, the triple $(\Ku{\p}/\p,\ q_\p(4)/\p,\ \varphi/\piR)$ --- the wall of $e$ (F2), the wall of $\pi$ at second order (G4), the angular address $\varphi=\arg(a+b\imR)$ of $\p=a^{2}+b^{2}$, $a\equiv1\pmod4$ (G3) --- is exact on each shell ($\p=13$: $10,6,-3+2\imR$; $1093$: $q_\p(4)=0$, the Wieferich prime); means $0.502,0.499,0.499$ and variances $0.0828,0.0831,0.0832$ (uniform: $1/2$, $1/12$), correlations $-0.016,-0.008,+0.010$ ($\sigma=0.0145$), $4\times4\times4$ chi-square $59.6$ on $63$ df, $a/\sqrt\p=\cos\varphi$ arcsine-distributed (mean $0.004$, variance $0.500$) \apx: consistent with independence on the examined range. -/
theorem p13068 : FRC.Epi.kur (13 : Nat) % (13 : Nat) = (10 : Nat) ∧ FRC.Epi.fermatQuotient4 (13 : Nat) = (6 : Nat) ∧ (3 : Nat) * (3 : Nat) + (2 : Nat) * (2 : Nat) = (13 : Nat) ∧ FRC.Epi.isPrimeB (1093 : Nat) = true ∧ FRC.Epi.fermatQuotient4 (1093 : Nat) = (0 : Nat) :=
  @FRC.Epi.invariants_13_1093
/-- 13:J1 (p13052) — The wrap-free window: an entity of the shell is $\p$-hard when it lies beyond the observer's horizon $\sqrt\p$; the accessible smalls are the natural counts below $\sqrt\p$, where sums and products of two accessible counts do not wrap, so primality, parity and order are wrap-invariant there and only there. -/
theorem p13052 : ∀ {a b p : Nat}, a * a < p → b * b < p → a * b < p ∧ ((4 : Nat) ≤ p → a + b < p) :=
  @FRC.Epi.wrap_free
/-- 13:J2 (p13053) — Calibration pinning: the half-period satisfies the height-two relation $2\piA+1\equiv0$, the shell calibration $\p=4\kap+1$ itself, so the observer holds an exact short certificate of an entity it never accesses as a tally; the same pinning covers the quarter-turn ($\im^{2}+1\equiv0$) and the residue web of G2; the pin holds on every one of the $500$ shells $\p\le8009$ with $H(\piA)=2$. -/
theorem p13053 : (∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → FRC.Shell.ofNat ((2 : Nat) * FRC.Shell.Frame.halfPeriod κ) = (-1 : FRC.Shell p)) ∧ ∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → FRC.Shell.Frame.quarterTurn g κ * FRC.Shell.Frame.quarterTurn g κ = (-1 : FRC.Shell p) :=
  @FRC.Ledger.p13053
/-- 13:J3 (p13054) — The height run: with $H(x)=\min_{a\ge1}\max(a,|\ctr{ax}|)$ in the smallest-primitive-root frame, minimised over the two chiralities, over the $500$ shells $\p\equiv1\pmod4$, $\p\le8009$: $H(\eP)\le2\sqrt\p$ on every shell (the horizon band), median $H(\eP)=0.525\sqrt\p$ \apx, exactly $68$ shells with $H\le10$, and the pin value $2$ on exactly $\{13,1933,4177,5857\}$; for $\eP$ a relation of height at most $h$ holds only on the shells with $H(\eP)\le h$ ($68$ of the $500$ for $h=10$), a share that falls as the shells grow, $H(\eP)$ sitting at the $\sqrt\p$ scale (the generic-growth reading, A7). -/
theorem p13054 : List.filter (fun q => decide ((5 : Nat) ≤ q) && q % (4 : Nat) == (1 : Nat) && FRC.Epi.isPrimeB q) (List.range (8010 : Nat)) = FRC.Epi.shells8009 ∧ FRC.Epi.shells8009.length = (500 : Nat) ∧ (FRC.Epi.shells8009.all fun p => decide (FRC.Epi.heightE p * FRC.Epi.heightE p ≤ (4 : Nat) * p)) = true ∧ (List.filter (fun p => decide (FRC.Epi.heightE p ≤ (10 : Nat))) FRC.Epi.shells8009).length = (68 : Nat) ∧ List.filter (fun p => FRC.Epi.heightE p == (2 : Nat)) FRC.Epi.shells8009 = [(13 : Nat), (1933 : Nat), (4177 : Nat), (5857 : Nat)] :=
  @FRC.Epi.height_run
/-- 13:J5 (p13056) — Universality and the duality as corollary: $\p$-hardness is self-similar, every shell finding its own half-period and drive name beyond its own horizon, so the chart shadows agree across all observers; $\pi$'s half-period is calibration-pinned with a height-two certificate (J2) and its arc role normalisation-fixed, $\eP$ has neither a pinned residue nor a cross-shell certificate and its role is generator-dependent --- structural against statistical is the certification split (I3). The sporadic small-height shells of J3 are the certificate-level face of I4. -/
theorem p13056 : (∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → FRC.Shell.ofNat ((2 : Nat) * FRC.Shell.Frame.halfPeriod κ) = (-1 : FRC.Shell p)) ∧ List.filter (fun p => FRC.Epi.heightE p == (2 : Nat)) FRC.Epi.shells8009 = [(13 : Nat), (1933 : Nat), (4177 : Nat), (5857 : Nat)] ∧ (FRC.Epi.shells8009.all fun p => decide (FRC.Epi.heightE p * FRC.Epi.heightE p ≤ (4 : Nat) * p)) = true :=
  @FRC.Epi.pin_contrast
set_option linter.defProp false in
/-- 13:J6 (p13057) — Two constants, two walls: both attach their full-resolution shell content to sparse-prime problems (Kurepa non-vanishing for $e$, a prescribed Fermat quotient of Wieferich type for $\pi$); for each shell the bounded observer holds an exact finite certificate and holds no uniform certificate across all shells --- per-instance decidability without a uniform bound, the characteristic shape of statements at the arithmetic horizon; Kurepa's hypothesis is not thereby decided; the frequency of the persistence shells is a range reading (G4), their totality not a predicate of the paper. -/
def p13057 := And.intro @FRC.Epi.terminal13 (@FRC.Epi.invariants_13_1093)
-- end ledger predicates

end FRC.Epi
