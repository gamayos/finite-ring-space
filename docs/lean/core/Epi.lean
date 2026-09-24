import FrcCore.Algebra
import FrcCore.Meridian

/-!
# FrcCore.Epi — the classical constants on the shell, with no axioms (13-epi)

The derangement numbers by their natural recurrence, their signed recurrence and antiperiodicity
`!(n + p) ≡ −!n` on every shell `p = 4κ + 1`, the fixed-shell tower of `e` exact at every grade, the
orientation transport of the quarter-turn under a change of drive (no third case), the wrap-free window
below `√p`; and the value rows decided by the kernel: the `p = 13` coincidence (`e_p = π_A = −1/2 = 6`),
the residue lines of `e` and `π` on `𝔽₁₃`, the terminal residue `−(!13)⁻¹ = 9`, the legibility window and
the first revival on `𝔽₁₃`, the 36 two-digit revivals, and the products `!p·A(p)` on the six wall shells.
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

/-- `p ≡ 0` on the shell. -/
theorem ofNat_self : (ofNat p : Shell p) = 0 := by
  apply ext; show p % p = 0; exact FRC.Nat.mod_self p Pos.pos

theorem ofNat_add_self (n : Nat) : (ofNat (n + p) : Shell p) = ofNat n := by
  rw [← ofNat_add, ofNat_self, add_zero]

theorem four_kappa_add_one_mod_two (κ : Nat) : (4 * κ + 1) % 2 = 1 :=
  FRC.Nat.mod_unique (q := 2 * κ) (Nat.lt_succ_self 1) (by rw [← FRC.Nat.mul_assoc])

theorem neg_one_pow_p {κ : Nat} (hκ : p = 4 * κ + 1) : (-1 : Shell p) ^ p = -1 := by
  have h2 : p % 2 = 1 := by rw [hκ]; exact four_kappa_add_one_mod_two κ
  rw [neg_one_pow, h2]; rfl

/-- 13:F3 — antiperiodicity on every shell `p = 4κ + 1`: `!(n + p) ≡ −!n (mod p)` for every `n`, so
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

/-- 13:F2, 13:F6 — the wall of `e` on `𝔽₁₃`: `!12 ≡ !13 ≡ 10`, the terminal residue `⟦ε₁₂⟧ = 9 = −(!13)⁻¹`, the
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

/-- 13:G8, 13:G1 — the residue line of `π` on `𝔽₁₃`: `⟦w_n⟧`, `n = 1, …, 6`, is `4, 5, 10, 9, 6, 11`, the
calibration face `⟦w₆⟧ = 11 = −2`, the quarter invariant `⟦w₃⟧ = 10 = −(3²)⁻¹`; the legibility window is exactly
`1 ≤ n ≤ 6` (`13 ∣ C(2n,n)` for `7 ≤ n ≤ 12`, not for `n ≤ 6`). -/
theorem residue_line_pi13 :
    (List.range 6).map (fun k => readW (p := 13) (k + 1)) = [4, 5, 10, 9, 6, 11] ∧
    (11 : Shell 13) = -2 ∧ (10 : Shell 13) * (3 * 3) = -1 ∧
    (List.range 13).map (fun n => decide (cb n % 13 = 0)) =
      [false, false, false, false, false, false, false, true, true, true, true, true, true] := by decide +kernel

/-- 13:G5 — the first revival on `𝔽₁₃`: `⟦v₁₃⟧ = 8`, and the two-digit revivals `13 ≤ n < 169` with
`13 ∤ C(2n,n)` and `13 ∤ n` number `36 = (2κ)²`. -/
theorem revivals13 :
    readV (p := 13) 13 = 8 ∧
    ((List.range 169).filter (fun n => decide (13 ≤ n) && decide (cb n % 13 ≠ 0) && decide (n % 13 ≠ 0))).length
      = 36 := by decide +kernel

/-- 13:F4 — the broken group law at the wall: `!p·A(p) ≡ 3, 0, 21, 28, 132, 258` at `p = 7, 13, 29, 101, 257,
1009`, with `A(13) ≡ 0` (the direct series residue vanishes on `𝔽₁₃`). -/
theorem kurepa_alt_values :
    kurS (p := 7) 7 * altS 7 = 3 ∧ kurS (p := 13) 13 * altS 13 = 0 ∧ altS (p := 13) 13 = 0 ∧
    kurS (p := 29) 29 * altS 29 = 21 ∧ kurS (p := 101) 101 * altS 101 = 28 ∧
    kurS (p := 257) 257 * altS 257 = 132 ∧ kurS (p := 1009) 1009 * altS 1009 = 258 := by decide +kernel

end values

-- Ledger predicates of 13-epi (generated by make_predicates.py from docs/13-epi/13-epi-ledger.json; edit the ledger, not this section)
/-- 13:B2 (p13009) — Orientation transport: under $\gen'=\gen^{u}$, $\gcd(u,\p-1)=1$, the re-derived quarter-turn is $\im'=\im$ exactly when $u\equiv1\pmod4$ and $\im'=-\im$ (the conjugate chart) when $u\equiv3\pmod4$; there is no third case, and every chirality-sensitive statement holds for the other chirality under $\im\mapsto-\im$. -/
theorem p13009 : (∀ {p κ : Nat} [FRC.Pos p] {g : FRC.Shell p}, FRC.Shell.Frame p κ g → ∀ {u : Nat}, FRC.Shell.Coprime u (p - (1 : Nat)) → (u % (4 : Nat) = (1 : Nat) ∨ u % (4 : Nat) = (3 : Nat)) ∧ (u % (4 : Nat) = (1 : Nat) → FRC.Shell.Frame.quarterTurn (g ^ u) κ = FRC.Shell.Frame.quarterTurn g κ) ∧ (u % (4 : Nat) = (3 : Nat) → FRC.Shell.Frame.quarterTurn (g ^ u) κ = -FRC.Shell.Frame.quarterTurn g κ)) ∧ ∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → ∀ (u : Nat), (u % (4 : Nat) = (1 : Nat) → -(g ^ u) ^ κ = -g ^ κ) ∧ (u % (4 : Nat) = (3 : Nat) → -(g ^ u) ^ κ = - -g ^ κ) :=
  And.intro @FRC.Epi.orientation_transport (@FRC.Shell.Frame.orientation_class)
/-- 13:B3 (p13010) — The coincidence that forces the typing: at $\p=13$ the field element $6$ is at once $\eP$, $\piA$ and the reading of $-1/2$, while $\eR\ne\piR$; no map from a bare residue to a real number exists, and the external comparison takes the structural role as part of its input --- roles, not residues, carry external meaning. Witnessed by the two towers reading the same element $6$ as $\eP$ and as $\piA$. -/
theorem p13010 : FRC.Shell.Frame.quarterTurn (2 : FRC.Shell (13 : Nat)) (3 : Nat) = (5 : FRC.Shell (13 : Nat)) ∧ (2 : FRC.Shell (13 : Nat)) ^ (FRC.Shell.Frame.quarterTurn (2 : FRC.Shell (13 : Nat)) (3 : Nat)).val = (6 : FRC.Shell (13 : Nat)) ∧ FRC.Shell.ofNat (FRC.Shell.Frame.halfPeriod (3 : Nat)) = (6 : FRC.Shell (13 : Nat)) ∧ (2 : FRC.Shell (13 : Nat)) * (6 : FRC.Shell (13 : Nat)) = (-1 : FRC.Shell (13 : Nat)) :=
  @FRC.Epi.coincidence13
set_option linter.defProp false in
/-- 13:F2 (p13028) — The wall identity and the terminal residue of $e$: $\dr{(\p-1)}\equiv\Ku{\p}\pmod\p$ (the odd-prime case of the Mijajlovi\'c--\v Sami congruence, A4), hence $\rep{\varepsilon_{\p-1}}=-(\Ku{\p})^{-1}$ whenever $\p\nmid\Ku{\p}$; existence of the terminal link on a shell is equivalent to $\p\nmid\Ku{\p}$, universal existence to Kurepa's hypothesis (Y1); re-verified in the derangement form for all $121{,}126$ odd primes $\p<1.6\times10^{6}$ with zero failures of either condition. Beyond the wall $n!\equiv0$: $n=\p-1$ is the factorial horizon. -/
def p13028 := @FRC.Epi.terminal13
set_option linter.defProp false in
/-- 13:F3 (p13029) — Antiperiodicity: $\dr{(n+\p)}\equiv-\dr{n}\pmod\p$ for every odd prime and every $n\ge0$, so $\dr{n}\bmod\p$ depends on $n\bmod2\p$; the blind set $Z_0(\p)=\{n<\p:\dr{n}\equiv0\}$ always contains $1$, and Kurepa's hypothesis is $\p-1\notin Z_0(\p)$ for every $\p$. -/
def p13029 := And.intro @FRC.Epi.dr_antiperiodic (@FRC.Epi.dr_succ)
/-- 13:F4 (p13030) — Series duals at the wall: $\sum_{k<\p}(-1)^{k}/k!\equiv-\Ku{\p}$ and $\sum_{k<\p}1/k!\equiv-A(\p)$, $A(\p)$ the alternating factorial sum; the group law $\exp(1)\exp(-1)=1$ does not survive, $\Ku{\p}A(\p)\equiv3,0,21,28,132,258$ at $\p=7,13,29,101,257,1009$; on $\p=13$ the direct series residue vanishes ($A(13)\equiv0$) while the derangement side survives ($\Ku{13}\equiv10$) --- a second ground for the canonicity of D5. -/
theorem p13030 : FRC.Epi.kurS (7 : Nat) * FRC.Epi.altS (7 : Nat) = (3 : FRC.Shell (7 : Nat)) ∧ FRC.Epi.kurS (13 : Nat) * FRC.Epi.altS (13 : Nat) = (0 : FRC.Shell (13 : Nat)) ∧ FRC.Epi.altS (13 : Nat) = (0 : FRC.Shell (13 : Nat)) ∧ FRC.Epi.kurS (29 : Nat) * FRC.Epi.altS (29 : Nat) = (21 : FRC.Shell (29 : Nat)) ∧ FRC.Epi.kurS (101 : Nat) * FRC.Epi.altS (101 : Nat) = (28 : FRC.Shell (101 : Nat)) ∧ FRC.Epi.kurS (257 : Nat) * FRC.Epi.altS (257 : Nat) = (132 : FRC.Shell (257 : Nat)) ∧ FRC.Epi.kurS (1009 : Nat) * FRC.Epi.altS (1009 : Nat) = (258 : FRC.Shell (1009 : Nat)) :=
  @FRC.Epi.kurepa_alt_values
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
/-- 13:G8 (p13041) — The $\p=13$ picture for $\pi$: $\kap=3$, wall at $n=6$; the residue line $\rep{w_n}$, $n=1,\dots,6$, is $4,5,10,9,6,11$ with $\rep{w_6}=11\equiv-2$ the calibration face and $\rep{w_3}=10\equiv-(3^{2})^{-1}$ encoding $13=3^{2}+2^{2}$; empty blind set below the wall, total blindness for $n=7,\dots,12$, first revival $\rep{v_{13}}=8$. -/
theorem p13041 : List.map (fun k => FRC.Epi.readW (k + (1 : Nat))) (List.range (6 : Nat)) = [(4 : FRC.Shell (13 : Nat)), (5 : FRC.Shell (13 : Nat)), (10 : FRC.Shell (13 : Nat)), (9 : FRC.Shell (13 : Nat)), (6 : FRC.Shell (13 : Nat)), (11 : FRC.Shell (13 : Nat))] ∧ (11 : FRC.Shell (13 : Nat)) = (-2 : FRC.Shell (13 : Nat)) ∧ (10 : FRC.Shell (13 : Nat)) * ((3 : FRC.Shell (13 : Nat)) * (3 : FRC.Shell (13 : Nat))) = (-1 : FRC.Shell (13 : Nat)) ∧ List.map (fun n => decide (FRC.Epi.cb n % (13 : Nat) = (0 : Nat))) (List.range (13 : Nat)) = [false, false, false, false, false, false, false, true, true, true, true, true, true] :=
  @FRC.Epi.residue_line_pi13
/-- 13:H2 (p13044) — The exact angular carrier of $\pi$: $\chi(-1)=e^{\imR\piR}$ exactly in every shell, for every generator and either chirality, since $-1=\gen^{(\p-1)/2}$ sits at arc fraction one half --- Euler's identity as the half-turn tautology $\gen^{2\kap}=-1$ under the dictionary, with no calibration and no error term. -/
theorem p13044 : ∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → g ^ ((2 : Nat) * κ) = (-1 : FRC.Shell p) :=
  @FRC.Shell.Frame.half_period
/-- 13:I4 (p13051) — CRT stability: under the composite lift to $q=\prod\p_i$ the half-wall invariant of $\pi$ glues to $-2$ modulo every $q$, since $2\piA\equiv-1$ holds in every fibre, while the terminal content of $e$, $(-(\Ku{\p_i})^{-1})_i$, varies fibrewise. The two selectors resolve the $\p=13$ coincidence: the same residue $6$ reaches $\piR$ through C4 and $\eR$ through C1. -/
theorem p13051 : ∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → FRC.Shell.ofNat ((2 : Nat) * FRC.Shell.Frame.halfPeriod κ) = (-1 : FRC.Shell p) :=
  @FRC.Shell.Frame.two_pi
/-- 13:J1 (p13052) — The wrap-free window: an entity of the shell is $\p$-hard when it lies beyond the observer's horizon $\sqrt\p$; the accessible smalls are the natural counts below $\sqrt\p$, where sums and products of two accessible counts do not wrap, so primality, parity and order are wrap-invariant there and only there. -/
theorem p13052 : ∀ {a b p : Nat}, a * a < p → b * b < p → a * b < p ∧ ((4 : Nat) ≤ p → a + b < p) :=
  @FRC.Epi.wrap_free
/-- 13:J2 (p13053) — Calibration pinning: the half-period satisfies the height-two relation $2\piA+1\equiv0$, the shell calibration $\p=4\kap+1$ itself, so the observer holds an exact short certificate of an entity it never accesses as a tally; the same pinning covers the quarter-turn ($\im^{2}+1\equiv0$) and the residue web of G2; the pin holds on every one of the $500$ shells $\p\le8009$ with $H(\piA)=2$. -/
theorem p13053 : (∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → FRC.Shell.ofNat ((2 : Nat) * FRC.Shell.Frame.halfPeriod κ) = (-1 : FRC.Shell p)) ∧ ∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → FRC.Shell.Frame.quarterTurn g κ * FRC.Shell.Frame.quarterTurn g κ = (-1 : FRC.Shell p) :=
  And.intro @FRC.Shell.Frame.two_pi (@FRC.Shell.Frame.quarter_turn_sq)
-- end ledger predicates

end FRC.Epi
