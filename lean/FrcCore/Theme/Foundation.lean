import FrcCore.Theme.Field
import FrcCore.Theme.Logic

/-!
# FrcCore.Theme.Foundation — the rows of master block A on the prime shell (the foundation theme, tasks LM22–LM24)

Completeness is primality in the ideal form (A11), counting closes by return (A6), and a bounded observer is a proper
part (A4), on the field of `Theme/Field.lean` (split from this file by task LM24 under the size budget, G10); the
quarter-turn criterion (A12), the order-divides-period lemma and primality as no zero divisors, moved here from
`Theme/Field.lean` by the Phase 4 repairs so that the Subject's closure keeps the budget (G10), names unchanged. The
Carrier's rows (`Theme/Carrier.lean`) rest on the field and on the chart `Ω = 4S + 1` alone. The three former pillars
as theorems (9 October 2026, with review): whatever a bounded agent determines is bounded by its records (A2, on
`Theme/Logic.lean`'s `records`), two totalities each registered whole within the other have one count (A3), a
complete reading needs the whole count and the Carrier is a translation torsor (A5). No axioms.
-/

namespace FRC

namespace Shell

variable {p : Nat} [Pos p]

namespace Prime

/-- Completeness is primality, in the ideal form (A11): for `p ≥ 2`, every ideal of the shell that holds a nonzero
residue holds every residue iff `p` is prime. An ideal `I` holds `0` and is closed under addition and under
multiplication by any residue. Forward, a nonzero `a ∈ I` has the inverse `a^{p−2}` (Fermat), so `1 ∈ I` and then
`x = x · 1 ∈ I`. Backward, the annihilator `{x : x b = 0}` of `b` is an ideal, so `a b = 0` with `a ≠ 0` puts `1` in
it and `b = 0`: no zero divisors, so `p` is prime. -/
theorem isPrime_iff_complete (h2 : 2 ≤ p) :
    FRC.Nat.isPrime p ↔ ∀ I : Shell p → Prop, I 0 → (∀ a b, I a → I b → I (a + b)) → (∀ r a, I a → I (r * a)) →
      (∃ a, I a ∧ a ≠ 0) → ∀ x, I x := by
  constructor
  · intro hp I _ _ hmul ⟨a, ha, ha0⟩ x
    have hpm : p - 1 = p - 2 + 1 := by
      match p, h2 with
      | k + 2, _ => rfl
    have h1 : a ^ (p - 2) * a = 1 := by rw [← pow_succ, ← hpm, fermat hp ha0]
    have hI1 : I 1 := by have := hmul (a ^ (p - 2)) a ha; rwa [h1] at this
    have := hmul x 1 hI1
    rwa [mul_one] at this
  · intro hc
    refine isPrime_of_no_zero_divisors h2 (fun {a b} hab => ?_)
    match decEq a 0 with
    | .isTrue e => exact .inl e
    | .isFalse ha =>
      have hall := hc (fun x => x * b = 0) (zero_mul b)
        (fun x y hx hy => by show (x + y) * b = 0; rw [right_distrib, hx, hy, add_zero])
        (fun r x hx => by show r * x * b = 0; rw [mul_assoc, hx, mul_zero]) ⟨a, hab, ha⟩ 1
      exact .inr (by rw [← one_mul b]; exact hall)

/-- The order divides the period: `z^d = 1` gives `z^{(p−1) mod d} = 1`. -/
theorem pow_mod_eq_one (hp : FRC.Nat.isPrime p) {z : Shell p} (hz : z ≠ 0) {d : Nat} (hd0 : 0 < d)
    (hd : z ^ d = 1) : z ^ ((p - 1) % d) = 1 := by
  obtain ⟨q, hq⟩ := FRC.Nat.mod_spec d hd0 (p - 1)
  have h := fermat hp hz
  rw [hq, pow_add, pow_mul, hd, one_pow, one_mul] at h
  exact h

/-! ## The quarter-turn criterion: `−1` is a square iff `p ≡ 1 (mod 4)` -/

/-- The quarter-turn criterion on a prime `p > 2`: `x² = −1` is solvable iff `p ≡ 1 (mod 4)`. Forward, `ħ⁴ = 1`
and `ħ^{(p−1) mod 4} = 1` leave only `(p − 1) mod 4 = 0`; backward, the chart. -/
theorem quarter_turn_iff (hp : FRC.Nat.isPrime p) (h2 : 2 < p) : (∃ h : Shell p, h * h = -1) ↔ p % 4 = 1 := by
  constructor
  · intro ⟨h, hh⟩
    have h0 : h ≠ 0 := ne_zero_of_mul_self (neg_one_ne_zero hp) hh
    have h4 : h ^ 4 = 1 := by
      rw [show (4 : Nat) = 2 + 2 from rfl, pow_add, pow_two, hh, neg_mul_neg, mul_one]
    have hcase : (p - 1) % 4 = 0 := by
      have hr := pow_mod_eq_one hp h0 (by decide : 0 < 4) h4
      have hlt := Nat.mod_lt (p - 1) (by decide : 0 < 4)
      generalize (p - 1) % 4 = r at hr hlt
      match r, hr, hlt with
      | 0, _, _ => rfl
      | 1, hr, _ => rw [pow_one] at hr; rw [hr, mul_one] at hh; exact absurd hh.symm (neg_one_ne_one h2)
      | 2, hr, _ => rw [pow_two, hh] at hr; exact absurd hr (neg_one_ne_one h2)
      | 3, hr, _ =>
        rw [show (4 : Nat) = 3 + 1 from rfl, pow_succ, hr, one_mul] at h4
        rw [h4, mul_one] at hh; exact absurd hh.symm (neg_one_ne_one h2)
      | k + 4, _, hlt => exact absurd hlt (Nat.not_lt_of_le (Nat.le_add_left 4 k))
    obtain ⟨q, hq⟩ := FRC.Nat.mod_spec 4 (by decide) (p - 1)
    rw [hcase, Nat.add_zero] at hq
    exact FRC.Nat.mod_unique (by decide)
      (by rw [← hq, FRC.Nat.sub_add_cancel (Nat.le_of_lt (Nat.lt_trans (Nat.lt_succ_self 1) h2))])
  · intro h4
    obtain ⟨S, hS⟩ := FRC.Nat.mod_spec 4 (by decide) p
    rw [h4] at hS
    exact exists_quarter_turn hp hS

/-- Completeness is primality: for `p ≥ 2`, the shell has no zero divisors iff `p` is prime. -/
theorem isPrime_iff_no_zero_divisors (h2 : 2 ≤ p) :
    FRC.Nat.isPrime p ↔ ∀ a b : Shell p, a * b = 0 → a = 0 ∨ b = 0 :=
  ⟨fun hp _ _ h => mul_eq_zero hp h, fun hz => isPrime_of_no_zero_divisors h2 (fun h => hz _ _ h)⟩

end Prime
end Shell

/-! ## Counting closes by return (A6), and a bounded observer is a proper part (A4) -/

namespace Foundation

open Shell

variable {q : Nat} [Pos q]

/-- The successor `C_q : x ↦ x + 1` on the `q` residues, iterated: `succIter x k = C_q^k x`. -/
def succIter (x : Shell q) : Nat → Shell q
  | 0 => x
  | k + 1 => succIter x k + 1

theorem ofNat_add (a b : Nat) : (ofNat a + ofNat b : Shell q) = ofNat (a + b) :=
  ext (by show (a % q + b % q) % q = (a + b) % q; rw [← FRC.Nat.add_mod _ _ _ Pos.pos])

theorem succIter_eq (x : Shell q) : ∀ k, succIter x k = x + ofNat k
  | 0 => (add_zero x).symm
  | k + 1 => by
    show succIter x k + ofNat 1 = x + ofNat (k + 1)
    rw [succIter_eq x k, add_assoc, ofNat_add]

theorem ofNat_eq_zero_iff (k : Nat) : (ofNat k : Shell q) = 0 ↔ k % q = 0 :=
  ⟨fun h => by have := val_injective h; rw [val_ofNat, val_zero] at this; exact this,
   fun h => ext (by rw [val_ofNat, val_zero]; exact h)⟩

theorem add_eq_self_iff (x a : Shell q) : x + a = x ↔ a = 0 :=
  ⟨fun h => add_right_cancel (by rw [add_comm, h, zero_add] : a + x = 0 + x), fun h => by rw [h, add_zero]⟩

/-- A6 — counting closes by return: on `q ≥ 2` points the successor `x ↦ x + 1` has no fixed point, returns to its
start after exactly the multiples of `q` steps, and reaches every point from every point within `q` steps. It is one
`q`-cycle, so iteration is bounded and cyclic. -/
theorem successor_cycle (h2 : 2 ≤ q) :
    (∀ x : Shell q, x + 1 ≠ x) ∧ (∀ (x : Shell q) (k : Nat), succIter x k = x ↔ k % q = 0) ∧
      ∀ x y : Shell q, ∃ k, k < q ∧ succIter x k = y := by
  have hret : ∀ (x : Shell q) (k : Nat), succIter x k = x ↔ k % q = 0 := fun x k => by
    rw [succIter_eq]; exact (add_eq_self_iff x _).trans (ofNat_eq_zero_iff k)
  refine ⟨fun x h => ?_, hret, fun x y => ⟨(y + -x).val, (y + -x).lt, ?_⟩⟩
  · have h1 : 1 % q = 0 := (hret x 1).1 h
    rw [FRC.Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self 1) h2)] at h1
    exact absurd h1 (by decide)
  · rw [succIter_eq, ofNat_val, add_comm y, ← add_assoc, add_neg, zero_add]

/-- A4 — a bounded observer is a proper part: an observer with `o < Ω` states holds no injective
encoding of the Carrier's `Ω` points, and every reading `ρ` into its states identifies two distinct points (the
pigeonhole, `FRC.Logic.no_mirror`; 25:D1, 5:C2). The two points are found by search. -/
theorem observer_part {Ω o : Nat} [Pos Ω] (ho : o < Ω) (ρ : Shell Ω → Nat) (hρ : ∀ x, ρ x < o) :
    ∃ x y : Shell Ω, x ≠ y ∧ ρ x = ρ y :=
  match @decExistsLT (fun j => ∃ i, i < j ∧ ρ (ofNat i) = ρ (ofNat j))
      (fun j => decExistsLT (fun i => ρ (ofNat i) = ρ (ofNat j)) j) Ω with
  | .isTrue ⟨j, hj, i, hij, e⟩ =>
    ⟨ofNat i, ofNat j, fun h => Nat.lt_irrefl j (Poly.Frame.ofNat_inj_lt (Nat.lt_trans hij hj) hj h ▸ hij), e⟩
  | .isFalse hno => (FRC.Logic.no_mirror ho (fun i => ρ (ofNat i)) (fun _ _ => hρ _) (fun i j hi hj e =>
      match Nat.lt_or_ge i j with
      | .inl hlt => absurd ⟨j, hj, i, hlt, e⟩ hno
      | .inr hge => match Nat.lt_or_ge j i with
        | .inl hlt => absurd ⟨i, hi, j, hlt, e.symm⟩ hno
        | .inr hge' => Nat.le_antisymm hge' hge)).elim

/-! ## The three former pillars as theorems (A2, A3, A5; 9 October 2026) -/

/-- A5 — a complete reading needs the whole count: a reading of the `Ω` points into `o` records that identifies no two
points has `Ω ≤ o` (the contrapositive of `observer_part`). A reader that is not the whole reads incompletely. -/
theorem complete_needs_whole {Ω o : Nat} [Pos Ω] (ρ : Shell Ω → Nat) (hρ : ∀ x, ρ x < o)
    (hinj : ∀ x y, ρ x = ρ y → x = y) : Ω ≤ o :=
  match Nat.lt_or_ge o Ω with
  | .inl hlt => match observer_part hlt ρ hρ with
    | ⟨x, y, hxy, e⟩ => (hxy (hinj x y e)).elim
  | .inr hge => hge

/-- A2 — the agent's bound: a shell read whole — injectively — into the records of an agent of capacity `K` over
`s ≥ 2` symbols has at most `records s K` members, fewer than `s^(K+1)` (5:C2, 29:C1: `records_lt`). The finitude of
the Universe is the identification's (A7, A14, read by A9); what the row proves is that whatever a bounded agent
determines is bounded by its records. That an unlimited supply is determined by no registration is 29:C2 and 29:C4,
consumed by the row, not proved here. -/
theorem agent_bound (s K : Nat) (hs : 2 ≤ s) {N : Nat} [Pos N] (ρ : Shell N → Nat)
    (hρ : ∀ x, ρ x < FRC.Logic.records s K) (hinj : ∀ x y, ρ x = ρ y → x = y) :
    N ≤ FRC.Logic.records s K ∧ FRC.Logic.records s K < s ^ (K + 1) :=
  ⟨complete_needs_whole ρ hρ hinj, FRC.Logic.records_lt s hs K⟩

/-- A3 — two totalities each registered whole within the other have one count: injections both ways between shells
force `m = n` (the pigeonhole `FRC.Logic.no_mirror`, 5:C2, both ways). With A7, one count is one Carrier. Silent
on a host: a shell with more points registers a shell with fewer. -/
theorem mutual_registration_count (m n : Nat) [Pos m] [Pos n]
    (f : Shell m → Shell n) (hf : ∀ x y, f x = f y → x = y)
    (g : Shell n → Shell m) (hg : ∀ x y, g x = g y → x = y) : m = n :=
  have h1 : ∀ {a b : Nat} [Pos a] [Pos b] (f : Shell a → Shell b), (∀ x y, f x = f y → x = y) → a ≤ b :=
    fun {a b} _ _ f hf => match Nat.lt_or_ge b a with
      | .inl hlt => (FRC.Logic.no_mirror hlt (fun i => (f (ofNat i)).val) (fun _ _ => (f _).lt)
          (fun _ _ hi hj e => Poly.Frame.ofNat_inj_lt hi hj (hf _ _ (ext e)))).elim
      | .inr hge => hge
  Nat.le_antisymm (h1 f hf) (h1 g hg)

/-- A5 — the Carrier is a translation torsor (A7): exactly one translation carries each member to each. The origin
is frame data: the shell's `0` is the chart's, and the translation carrying `0` to `x` makes `x` an origin as good;
the affine frames are a torsor under the frame group (1:C2, `simply_transitive`). -/
theorem translation_torsor {Ω : Nat} [Pos Ω] (x y : Shell Ω) :
    ∃ t : Shell Ω, x + t = y ∧ ∀ t', x + t' = y → t' = t :=
  ⟨y + -x, by rw [add_comm y, ← add_assoc, add_neg, zero_add],
    fun t' h => add_right_cancel (c := x) (by rw [add_comm t', h, add_assoc, neg_add, add_zero])⟩

end Foundation
end FRC
