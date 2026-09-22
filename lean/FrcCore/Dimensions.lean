import FrcCore.Frame
import FrcCore.Meridian
import FrcCore.Epi

/-!
# 10-dimensions — the domain lattice, the unit flag and the Carrier residues, no axioms

The modular unit-domain labels `U_{r,s} = [L]^r [T]^s` of *Dimensional Analysis over Finite Holographic
Substrate* as pairs of residues `(r mod p, s mod 4κ)`, `p = 4κ + 1`: the group law, inverses and powers
(10:C2, the monomial half of C3); the chart duality `δ_S` and the crossed duality `δ_C` as involutions (D1);
the unit flag `I_q = (0, κ)` — `I_q⁴ = 1`, `I_q² = [T]^π`, `I_q, I_q², I_q³ ≠ 1`, no flag of space on a
framed shell (`4r = 0 ⇒ r = 0`), the half-period as the one element of order two, meridian transport
`([L][T]^κ)^p = I_q` (D2, C6); the record `s ↦ I_q^s` with its values (D3); the flagged readings `[E]`, `[p]`,
`[S]`, the phase counts neutral, the horizon inaccessibility of the flag on `𝔽₁₃` (D6); the Carrier face —
the linear pin `2G + 1 = 0 ⇒ G = 2S`, the root pairs, the linkage `(k_B c)² = −1 ⇒ k_B c = ±ħ` and the pair
consequences on every framed Carrier (E4, E5); the two Carriers `233` and `2 408 561` decided by the kernel
(E4, E5); the minimality scan certifying `(13, 233)` with its counterfactuals (E9); the derived domains
realized on `𝔽₁₃` and the energy–momentum relation among them (F2–F4, G3); the window ladder by integer squares
(G2). Every declaration is checked to depend on no axiom (`check_core_axioms.py`).
-/

namespace FRC.Dimensions

open FRC.Shell

/-! ## The domain lattice as pairs of residues (10:C1, C2, C3) -/

/-- 10:C1 — a modular unit-domain label `U_{r,s}`: the space exponent `r` in `C_p`, the time exponent `s`
in `C_n` (`n = p − 1 = 4κ`). -/
structure Dom (p n : Nat) where
  r : Shell p
  s : Shell n

namespace Dom

variable {p n : Nat}

theorem ext {a b : Dom p n} (hr : a.r = b.r) (hs : a.s = b.s) : a = b := by
  cases a; cases b; cases hr; cases hs; rfl

theorem r_congr {a b : Dom p n} (h : a = b) : a.r = b.r := by cases h; rfl
theorem s_congr {a b : Dom p n} (h : a = b) : a.s = b.s := by cases h; rfl

instance : DecidableEq (Dom p n) := fun a b =>
  if h : a.r = b.r ∧ a.s = b.s then isTrue (ext h.1 h.2)
  else isFalse (fun e => h ⟨r_congr e, s_congr e⟩)

variable [Pos p] [Pos n]

/-- 10:C2 — the product of labels adds the exponents: `U_{r,s} U_{r',s'} = U_{r+r', s+s'}`. -/
def mul (a b : Dom p n) : Dom p n := ⟨a.r + b.r, a.s + b.s⟩
instance : Mul (Dom p n) := ⟨mul⟩

/-- 10:C2 — the neutral label `U_{0,0} = 1`. -/
def one : Dom p n := ⟨0, 0⟩
instance : One (Dom p n) := ⟨one⟩

/-- 10:C2, 10:D1 — the inverse label `U_{r,s}⁻¹ = U_{−r,−s}`, the chart duality `δ_S`. -/
def inv (a : Dom p n) : Dom p n := ⟨-a.r, -a.s⟩
instance : Inv (Dom p n) := ⟨inv⟩

/-- Powers by structural recursion. -/
def pow (a : Dom p n) : Nat → Dom p n
  | 0 => 1
  | k + 1 => pow a k * a
instance : Pow (Dom p n) Nat := ⟨pow⟩

theorem mul_def (a b : Dom p n) : a * b = ⟨a.r + b.r, a.s + b.s⟩ := rfl
theorem one_def : (1 : Dom p n) = ⟨0, 0⟩ := rfl
theorem inv_def (a : Dom p n) : a⁻¹ = ⟨-a.r, -a.s⟩ := rfl
theorem pow_zero (a : Dom p n) : a ^ 0 = 1 := rfl
theorem pow_succ (a : Dom p n) (k : Nat) : a ^ (k + 1) = a ^ k * a := rfl

/-- 10:C2 — the label group is abelian: commutativity. -/
theorem mul_comm (a b : Dom p n) : a * b = b * a :=
  ext (Shell.add_comm _ _) (Shell.add_comm _ _)

/-- 10:C2 — associativity. -/
theorem mul_assoc (a b c : Dom p n) : a * b * c = a * (b * c) :=
  ext (Shell.add_assoc _ _ _) (Shell.add_assoc _ _ _)

/-- 10:C2 — the unit. -/
theorem one_mul (a : Dom p n) : 1 * a = a := ext (Shell.zero_add _) (Shell.zero_add _)
theorem mul_one (a : Dom p n) : a * 1 = a := ext (Shell.add_zero _) (Shell.add_zero _)

/-- 10:C2 — the inverse: `U_{r,s} U_{−r,−s} = 1`. -/
theorem mul_inv (a : Dom p n) : a * a⁻¹ = 1 := ext (Shell.add_neg _) (Shell.add_neg _)
theorem inv_mul (a : Dom p n) : a⁻¹ * a = 1 := ext (Shell.neg_add _) (Shell.neg_add _)

/-- 10:D1 — the chart duality `δ_S : D ↦ D⁻¹` is an involution. -/
theorem inv_inv (a : Dom p n) : a⁻¹⁻¹ = a := ext (Shell.neg_neg _) (Shell.neg_neg _)

/-- 10:C2, 10:C3 — the grading: `U_a^{k+l} = U_a^k U_a^l`. -/
theorem pow_add (a : Dom p n) (k l : Nat) : a ^ (k + l) = a ^ k * a ^ l := by
  induction l with
  | zero => rw [Nat.add_zero, pow_zero, mul_one]
  | succ l ih => rw [Nat.add_succ, pow_succ, ih, pow_succ, mul_assoc]

/-- 10:C3 — the domain of a power is the multiple of the label: `U_{r,s}^k = U_{kr, ks}`; so the domain
of a monomial `∏ U_{a_j}^{k_j}` is `Σ k_j a_j`, and the monomial is neutral iff that sum is `(0, 0)`. -/
theorem pow_eq (a : Dom p n) (k : Nat) : a ^ k = ⟨ofNat k * a.r, ofNat k * a.s⟩ := by
  induction k with
  | zero =>
    refine ext ?_ ?_
    · show (0 : Shell p) = ofNat 0 * a.r
      rw [show (ofNat 0 : Shell p) = 0 from rfl, Shell.zero_mul]
    · show (0 : Shell n) = ofNat 0 * a.s
      rw [show (ofNat 0 : Shell n) = 0 from rfl, Shell.zero_mul]
  | succ k ih =>
    rw [pow_succ, ih, mul_def, ofNat_succ, ofNat_succ, Shell.right_distrib, Shell.right_distrib,
      Shell.one_mul, Shell.one_mul]

/-- 10:C3 — the product of powers: `(U_a U_b)^k = U_a^k U_b^k`. -/
theorem mul_pow (a b : Dom p n) (k : Nat) : (a * b) ^ k = a ^ k * b ^ k := by
  rw [pow_eq, pow_eq, pow_eq, mul_def]
  exact ext (Shell.left_distrib _ _ _) (Shell.left_distrib _ _ _)

end Dom

/-! ## Bounded universal quantifiers, decided by search (no axioms) -/

/-- `∀ m < n, P m`, decided by recursion on `n` — Lean's own instance carries `propext`; this one nothing. -/
def decForallLT (P : Nat → Prop) [DecidablePred P] : (n : Nat) → Decidable (∀ m, m < n → P m)
  | 0 => isTrue (fun m hm => absurd hm (Nat.not_lt_zero m))
  | n + 1 =>
    match decForallLT P n with
    | isFalse h => isFalse (fun hall => h (fun m hm => hall m (Nat.lt_succ_of_lt hm)))
    | isTrue h =>
      if hn : P n then
        isTrue (fun m hm =>
          match Nat.lt_or_ge m n with
          | .inl hlt => h m hlt
          | .inr hge => (Nat.le_antisymm (Nat.le_of_lt_succ hm) hge) ▸ hn)
      else isFalse (fun hall => hn (hall n (Nat.lt_succ_self n)))

instance instDecForallLT (P : Nat → Prop) [DecidablePred P] (n : Nat) : Decidable (∀ m, m < n → P m) :=
  decForallLT P n

/-- `∀ x : Shell p, P x`, decided through the representatives. -/
instance instDecForallShell {p : Nat} [Pos p] (P : Shell p → Prop) [DecidablePred P] :
    Decidable (∀ x, P x) :=
  match decForallLT (fun v => P (ofNat v)) p with
  | isTrue h => isTrue (fun x => ofNat_val x ▸ h x.val x.lt)
  | isFalse h => isFalse (fun hall => h (fun v _ => hall (ofNat v)))

/-- `∀ x : Dom p n, P x`, decided componentwise. -/
instance instDecForallDom {p n : Nat} [Pos p] [Pos n] (P : Dom p n → Prop) [DecidablePred P] :
    Decidable (∀ x, P x) :=
  match (inferInstance : Decidable (∀ r : Shell p, ∀ s : Shell n, P ⟨r, s⟩)) with
  | isTrue h => isTrue (fun x => match x with | ⟨r, s⟩ => h r s)
  | isFalse h => isFalse (fun hall => h (fun r s => hall ⟨r, s⟩))

/-! ## The generators and the flag on the shell of capacity `κ` (10:D2, C6, D3, D6) -/
section shell

variable (κ : Nat) [Pos κ]

instance instPosFour : Pos (4 * κ) := ⟨Nat.mul_pos (Nat.zero_lt_succ 3) Pos.pos⟩

/-- The lattice of the shell of capacity `κ`: `D_p = C_{4κ+1} × C_{4κ}`. -/
abbrev DomK := Dom (4 * κ + 1) (4 * κ)

/-- 10:C1 — the space generator `[L] = (1, 0)`. -/
def L : DomK κ := ⟨1, 0⟩
/-- 10:C1 — the time generator `[T] = (0, 1)`. -/
def T : DomK κ := ⟨0, 1⟩
/-- 10:D2 — the unit flag `I_q = [T]^κ = (0, κ)`. -/
def flag : DomK κ := ⟨0, ofNat κ⟩
/-- 10:D6 — the energy domain `[E] = I_q [T]⁻¹`. -/
def energy : DomK κ := flag κ * (T κ)⁻¹
/-- 10:D6 — the momentum domain `[p] = I_q [L]⁻¹`. -/
def mom : DomK κ := flag κ * (L κ)⁻¹
/-- 10:D1 — the crossed duality `δ_C = I_q δ_S : D ↦ I_q D⁻¹`. -/
def deltaC (a : DomK κ) : DomK κ := flag κ * a⁻¹

/-- 10:D2 — `I_q = [T]^κ`. -/
theorem flag_eq_pow : T κ ^ κ = flag κ := by
  rw [Dom.pow_eq]
  exact Dom.ext (by show ofNat κ * 0 = 0; exact Shell.mul_zero _)
    (by show ofNat κ * 1 = ofNat κ; exact Shell.mul_one _)

/-- `ofNat (m·κ)` in `C_{4κ}` has representative `m·κ` for `m < 4`. -/
theorem val_ofNat_mul_kappa (m : Nat) (hm : m < 4) : (ofNat (m * κ) : Shell (4 * κ)).val = m * κ :=
  FRC.Nat.mod_eq_of_lt (FRC.Nat.mul_lt_mul_of_lt_of_pos hm Pos.pos)

theorem ofNat_kappa_ne_zero : (ofNat κ : Shell (4 * κ)) ≠ 0 := fun h => by
  have hv := val_injective h
  rw [show ofNat κ = (ofNat (1 * κ) : Shell (4 * κ)) by rw [Nat.one_mul],
    val_ofNat_mul_kappa κ 1 (by decide), Nat.one_mul, val_zero] at hv
  exact Nat.ne_of_gt Pos.pos hv

theorem ofNat_two_kappa_ne_zero : (ofNat (2 * κ) : Shell (4 * κ)) ≠ 0 := fun h => by
  have hv := val_injective h
  rw [val_ofNat_mul_kappa κ 2 (by decide), val_zero] at hv
  exact Nat.ne_of_gt (Nat.mul_pos (Nat.zero_lt_succ 1) Pos.pos) hv

theorem ofNat_three_kappa_ne_zero : (ofNat (3 * κ) : Shell (4 * κ)) ≠ 0 := fun h => by
  have hv := val_injective h
  rw [val_ofNat_mul_kappa κ 3 (by decide), val_zero] at hv
  exact Nat.ne_of_gt (Nat.mul_pos (Nat.zero_lt_succ 2) Pos.pos) hv

/-- `4κ ≡ 0` in `C_{4κ}`. -/
theorem ofNat_four_kappa : (ofNat (4 * κ) : Shell (4 * κ)) = 0 := Epi.ofNat_self

theorem flag_pow (m : Nat) : flag κ ^ m = ⟨0, ofNat (m * κ)⟩ := by
  rw [Dom.pow_eq]
  exact Dom.ext (by show ofNat m * 0 = 0; exact Shell.mul_zero _)
    (by show ofNat m * ofNat κ = ofNat (m * κ); rw [Frame.ofNat_mul])

/-- 10:D2 — `I_q⁴ = 1`. -/
theorem flag_pow_four : flag κ ^ 4 = 1 := by
  rw [flag_pow, ofNat_four_kappa]; rfl

/-- 10:D2 — `I_q² = [T]^π`, the half-period `π = 2κ`, and `I_q, I_q², I_q³ ≠ 1`: the flag has order four. -/
theorem flag_order_four :
    flag κ ^ 2 = T κ ^ (2 * κ) ∧ flag κ ^ 1 ≠ 1 ∧ flag κ ^ 2 ≠ 1 ∧ flag κ ^ 3 ≠ 1 := by
  refine ⟨?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [flag_pow, Dom.pow_eq]
    exact Dom.ext (by show (0 : Shell (4 * κ + 1)) = ofNat (2 * κ) * 0; rw [Shell.mul_zero])
      (by show ofNat (2 * κ) = ofNat (2 * κ) * 1; rw [Shell.mul_one])
  · rw [flag_pow, Nat.one_mul] at h; exact ofNat_kappa_ne_zero κ (Dom.s_congr h)
  · rw [flag_pow] at h; exact ofNat_two_kappa_ne_zero κ (Dom.s_congr h)
  · rw [flag_pow] at h; exact ofNat_three_kappa_ne_zero κ (Dom.s_congr h)

/-- 10:D2 — the conjugate generator `I_q⁻¹ = I_q³ = (0, 3κ)`. -/
theorem flag_inv : (flag κ)⁻¹ = flag κ ^ 3 := by
  rw [flag_pow, Dom.inv_def]
  refine Dom.ext (Shell.neg_zero) ?_
  show -(ofNat κ) = ofNat (3 * κ)
  apply Shell.neg_eq_of_add_eq_zero
  have h4 : 4 * κ = 3 * κ + κ := Nat.succ_mul 3 κ
  rw [Frame.ofNat_add, Nat.add_comm, ← h4, ofNat_four_kappa]

omit [Pos κ] in
/-- 10:D2 — no flag of space on a framed shell: `4r = 0` forces `r = 0` (`2 ≠ 0` and no zero divisors), so
the meridian factor contributes no element of order four; and `2r = 0` forces `r = 0`. -/
theorem no_flag_of_space {g : Shell (4 * κ + 1)} (F : Frame (4 * κ + 1) κ g) (r : Shell (4 * κ + 1))
    (h : (2 * 2 : Shell (4 * κ + 1)) * r = 0) : r = 0 := by
  rw [Shell.mul_assoc] at h
  exact F.no_south_pole _ (F.no_south_pole _ h)

/-- 10:D2 — the order-two element: `2s = 0` in `C_{4κ}` iff `s ∈ {0, 2κ}` — decided on `κ = 3` for every
residue; the general law is `two_smul_flag` of the Mathlib module. -/
theorem order_two_13 :
    ∀ s : Shell 12, (2 : Shell 12) * s = 0 ↔ (s = 0 ∨ s = 6) := by decide +kernel

/-- 10:D2 — the elements of order four of `D_13 = C_13 × C_12` are exactly `(0, 3)` and `(0, 9)`: the flag
and its conjugate, both in the time factor (exhaustive over the `156` labels). -/
theorem order_four_13 :
    ∀ x : DomK 3, (x ^ 4 = 1 ∧ x ^ 2 ≠ 1) ↔ (x = flag 3 ∨ x = (flag 3)⁻¹) := by decide +kernel

/-- 10:D2, 10:C6 — meridian transport onto the flag: `([L][T]^κ)^p = I_q` — the meridian component wraps,
`p ≡ 0 (mod p)`, and the phase component advances by `pκ = κ + κ·4κ ≡ κ (mod 4κ)`; for every capacity. -/
theorem meridian_transport : (L κ * T κ ^ κ) ^ (4 * κ + 1) = flag κ := by
  rw [flag_eq_pow, Dom.pow_eq]
  refine Dom.ext ?_ ?_
  · show ofNat (4 * κ + 1) * (1 + 0) = 0
    rw [Shell.add_zero, Shell.mul_one]; exact Epi.ofNat_self
  · show ofNat (4 * κ + 1) * (0 + ofNat κ) = ofNat κ
    rw [Shell.zero_add, Frame.ofNat_mul, FRC.Nat.add_mul (4 * κ) 1 κ, Nat.one_mul,
      Nat.mul_comm (4 * κ) κ, Nat.add_comm]
    exact ofNat_add_mul_self κ κ
  where
  ofNat_add_mul_self (a : Nat) : ∀ m : Nat, (ofNat (a + m * (4 * κ)) : Shell (4 * κ)) = ofNat a
    | 0 => by rw [Nat.zero_mul, Nat.add_zero]
    | m + 1 => by
      rw [FRC.Nat.add_mul m 1 (4 * κ), Nat.one_mul, ← Nat.add_assoc, Epi.ofNat_add_self,
        ofNat_add_mul_self a m]

/-- 10:D1 — the crossed duality is an involution, `δ_C(δ_C D) = D`, and carries `[L] ↦ [p]`, `[T] ↦ [E]`. -/
theorem deltaC_involutive (a : DomK κ) :
    deltaC κ (deltaC κ a) = a ∧ deltaC κ (L κ) = mom κ ∧ deltaC κ (T κ) = energy κ := by
  refine ⟨?_, rfl, rfl⟩
  unfold deltaC
  refine Dom.ext ?_ ?_
  · show (0 : Shell (4 * κ + 1)) + -(0 + -a.r) = a.r
    rw [Shell.zero_add, Shell.zero_add, Shell.neg_neg]
  · show ofNat κ + -(ofNat κ + -a.s) = a.s
    rw [Shell.neg_add_rev, Shell.neg_neg, ← Shell.add_assoc, Shell.add_neg, Shell.zero_add]

/-- 10:D3 — the record `s ↦ I_q^s` on `s = 0, 1, 2, 3` takes the four values `1, (0, κ), (0, 2κ), (0, 3κ)`
of the flag subgroup, and returns to `1` at `s = 4`; its values at `0` and `2` are the parity subgroup, the
chart shadow of the four-cycle. -/
theorem record_values :
    flag κ ^ 0 = 1 ∧ flag κ ^ 1 = ⟨0, ofNat κ⟩ ∧ flag κ ^ 2 = ⟨0, ofNat (2 * κ)⟩ ∧
    flag κ ^ 3 = ⟨0, ofNat (3 * κ)⟩ ∧ flag κ ^ 4 = 1 ∧ flag κ ^ 2 * flag κ ^ 2 = 1 := by
  refine ⟨rfl, by rw [flag_pow, Nat.one_mul], flag_pow κ 2, flag_pow κ 3, flag_pow_four κ, ?_⟩
  rw [← Dom.pow_add]; exact flag_pow_four κ

/-- 10:D6 — the flagged readings: `[E] = (0, κ − 1)` one capacity step above the count, `[p] = (−1, κ)`,
the action `[S] = [E][T] = I_q`, and the phase counts neutral, `[E][T] I_q⁻¹ = 1`, `[p][L] I_q⁻¹ = 1`. -/
theorem flagged_readings :
    energy κ = ⟨0, ofNat κ + -1⟩ ∧ mom κ = ⟨-1, ofNat κ⟩ ∧ energy κ * T κ = flag κ ∧
    energy κ * T κ * (flag κ)⁻¹ = 1 ∧ mom κ * L κ * (flag κ)⁻¹ = 1 := by
  have h3 : energy κ * T κ = flag κ := by
    unfold energy; rw [Dom.mul_assoc, Dom.inv_mul, Dom.mul_one]
  have h5 : mom κ * L κ = flag κ := by
    unfold mom; rw [Dom.mul_assoc, Dom.inv_mul, Dom.mul_one]
  refine ⟨?_, ?_, h3, ?_, ?_⟩
  · exact Dom.ext (by show (0 : Shell (4 * κ + 1)) + -0 = 0; rw [Shell.neg_zero, Shell.add_zero]) rfl
  · refine Dom.ext (by show (0 : Shell (4 * κ + 1)) + -1 = -1; rw [Shell.zero_add]) ?_
    show ofNat κ + -0 = ofNat κ
    rw [Shell.neg_zero, Shell.add_zero]
  · rw [h3, Dom.mul_inv]
  · rw [h5, Dom.mul_inv]

end shell

/-! ## The Carrier face: the defining congruences at pair level (10:E4, 10:E5) -/
section carrier

variable {Ω : Nat} [Pos Ω] {S : Nat} {g : Shell Ω}

/-- 10:E4 — the linear pin: on a framed Carrier `Ω = 4S + 1`, `2G + 1 = 0` has the unique solution
`G = 2S`, the half-cycle. -/
theorem G_unique (F : Frame Ω S g) (x : Shell Ω) : 2 * x + 1 = 0 ↔ x = ofNat (2 * S) := by
  have hΩ : (ofNat (4 * S + 1) : Shell Ω) = 0 := by rw [← F.cap]; exact Epi.ofNat_self
  have h2S : (2 : Shell Ω) * ofNat (2 * S) + 1 = 0 := by
    rw [Frame.two_mul', Frame.ofNat_add, show (1 : Shell Ω) = ofNat 1 from rfl, Frame.ofNat_add,
      ← Nat.two_mul, ← FRC.Nat.mul_assoc]
    exact hΩ
  constructor
  · intro h
    apply F.mul_left_cancel F.two_ne_zero
    apply Shell.add_right_cancel (c := 1)
    rw [h, h2S]
  · intro h; rw [h]; exact h2S

/-- 10:E4 — the root pair: if `x² = a` with `x ≠ 0` then `y² = a` iff `y = x` or `y = −x`, and `−x ≠ x`;
each quadratic defining congruence has exactly two roots on a framed Carrier. -/
theorem root_pair (F : Frame Ω S g) (a x : Shell Ω) (hx : x * x = a) (hx0 : x ≠ 0) :
    (∀ y : Shell Ω, y * y = a ↔ (y = x ∨ y = -x)) ∧ -x ≠ x := by
  refine ⟨fun y => ⟨fun hy => ?_, fun hy => ?_⟩, fun h => hx0 (F.eq_zero_of_eq_neg h.symm)⟩
  · have h0 : (y + -x) * (y + x) = 0 := by
      rw [Shell.right_distrib, Shell.left_distrib, Shell.left_distrib, ← Shell.neg_mul, ← Shell.neg_mul,
        Shell.mul_comm y x, Shell.add_assoc, ← Shell.add_assoc (x * y), Shell.add_neg, Shell.zero_add,
        hy, hx, Shell.add_neg]
    rcases F.mul_eq_zero h0 with h | h
    · left; exact (Shell.eq_neg_of_add_eq_zero h).trans (Shell.neg_neg x)
    · right; exact Shell.eq_neg_of_add_eq_zero h
  · rcases hy with rfl | rfl
    · exact hx
    · rw [Shell.neg_mul_neg]; exact hx

/-- 10:E4, 10:E5 — the linkage at pair level and the pair consequences, on a framed Carrier: from
`2G + 1 = 0`, `2c² = 1`, `ħ² = −1`, `k_B² = −2`: `(k_B c)² = −1`, so `k_B c = ħ` or `k_B c = −ħ`
(`{±k_B}{±c} = {±ħ}`); `G = −c²`; `(2G)² = 1`; `ħ⁴ = 1`; and `(ħ c)² = −2 G²`, the monomial face. -/
theorem linkage (F : Frame Ω S g) (G c h k : Shell Ω) (hG : 2 * G + 1 = 0) (hc : 2 * (c * c) = 1)
    (hh : h * h = -1) (hk : k * k = -2) :
    (k * c) * (k * c) = -1 ∧ (k * c = h ∨ k * c = -h) ∧ G = -(c * c) ∧ (2 * G) * (2 * G) = 1 ∧
    (h * h) * (h * h) = 1 ∧ (h * c) * (h * c) = -2 * (G * G) := by
  have hkc : (k * c) * (k * c) = -1 := by
    rw [Shell.mul_assoc, Shell.mul_left_comm c, ← Shell.mul_assoc, hk, ← Shell.neg_mul, hc]
  have hh0 : h ≠ 0 := fun h0 => by
    rw [h0, Shell.zero_mul] at hh
    have := congrArg Neg.neg hh
    rw [Shell.neg_zero, Shell.neg_neg] at this
    exact F.one_ne_zero this.symm
  have hlink : k * c = h ∨ k * c = -h := ((root_pair F (-1) h hh hh0).1 (k * c)).1 hkc
  have h2G : 2 * G = -1 := Shell.eq_neg_of_add_eq_zero hG
  refine ⟨hkc, hlink, ?_, ?_, ?_, ?_⟩
  · apply F.mul_left_cancel F.two_ne_zero
    rw [h2G, ← Shell.mul_neg, hc]
  · rw [h2G, Shell.neg_mul_neg, Shell.mul_one]
  · rw [hh, Shell.neg_mul_neg, Shell.mul_one]
  · have h4 : (2 * 2 : Shell Ω) * (G * G) = 1 := by
      rw [Shell.mul_assoc, ← Shell.mul_left_comm G 2 G, ← Shell.mul_assoc, h2G, Shell.neg_mul_neg,
        Shell.mul_one]
    have hcc : c * c = 2 * (G * G) := by
      apply F.mul_left_cancel F.two_ne_zero
      rw [hc, ← Shell.mul_assoc, h4]
    rw [Shell.mul_assoc, Shell.mul_left_comm c, ← Shell.mul_assoc, hh, Shell.neg_one_mul, hcc,
      Shell.neg_mul]

end carrier

/-! ## The values decided by the kernel (10:E4, E5, E9, F2–F4, G2, G3) -/
section values

/-- 10:E4, 10:E5 — the Carrier `Ω = 233` (`S = 58`): `G = 116 = 2S`, `ħ = 89`, `k_B = 124`, `c = 159`,
`h = 144 = −ħ` satisfy the defining congruences, the linkage `k_B c = −ħ`, `G = −c²`, `ħ c = k_B G`
(the monomial on the `k_B` residue), and the partner `109 = −124` fails the linkage. -/
theorem carrier233 :
    2 * (116 : Shell 233) + 1 = 0 ∧ (89 : Shell 233) * 89 = -1 ∧ (124 : Shell 233) * 124 = -2 ∧
    2 * ((159 : Shell 233) * 159) = 1 ∧ (124 : Shell 233) * 159 = -89 ∧ (144 : Shell 233) = -89 ∧
    (116 : Shell 233) = -(159 * 159) ∧ (89 : Shell 233) * 159 = 124 * 116 ∧
    (109 : Shell 233) = -124 ∧ (109 : Shell 233) * 159 ≠ -89 := by decide +kernel

/-- 10:E4, 10:E5, 21:C5 — the laboratory Carrier `Ω = 2 408 561` (`S = 602 140`): `G = 1 204 280`,
`ħ = 18 688`, `k_B = 1 880 160`, `c = 171 106`, `h = 2 389 873 = −ħ` satisfy the defining congruences, the
linkage, `G = −c²` and `ħ c = k_B G`. -/
theorem carrierLab :
    2 * (1204280 : Shell 2408561) + 1 = 0 ∧ (18688 : Shell 2408561) * 18688 = -1 ∧
    (1880160 : Shell 2408561) * 1880160 = -2 ∧ 2 * ((171106 : Shell 2408561) * 171106) = 1 ∧
    (1880160 : Shell 2408561) * 171106 = -18688 ∧ (2389873 : Shell 2408561) = -18688 ∧
    (1204280 : Shell 2408561) = -(171106 * 171106) ∧
    (18688 : Shell 2408561) * 171106 = 1880160 * 1204280 := by decide +kernel

/-- Primality by trial division, decidable. -/
def isPrime (n : Nat) : Prop := 2 ≤ n ∧ ∀ d, d < n → 2 ≤ d → n % d ≠ 0
instance (n : Nat) : Decidable (isPrime n) := by unfold isPrime; exact inferInstance

/-- 10:E9 — the admissibility predicate of the programme on `(p, Ω) = (4κ + 1, 4S + 1)`: `p` prime,
`κ > 1`; `Ω` prime, `S` even, `S ≡ 1 (mod 3)`; `p² < Ω`. -/
def admissible (κ S : Nat) : Prop :=
  isPrime (4 * κ + 1) ∧ 1 < κ ∧ isPrime (4 * S + 1) ∧ S % 2 = 0 ∧ S % 3 = 1 ∧
  (4 * κ + 1) * (4 * κ + 1) < 4 * S + 1
instance (κ S : Nat) : Decidable (admissible κ S) := by unfold admissible; exact inferInstance

/-- 10:E9 — the minimal admissible pair is `(13, 233)`: `(κ, S) = (3, 58)` is admissible, no pair with
`S < 58` is (for `S < 58`, `p² < Ω` forces `κ ≤ 3`), and the counterfactuals — dropping the mod-3 clause
admits `(13, 193)` (`S = 48`), dropping `κ > 1` admits `(5, 41)` (`S = 10`), and `κ = 2` gives the
composite `9`. -/
theorem minimality :
    admissible 3 58 ∧ (∀ κ, κ < 4 → ∀ S, S < 58 → ¬ admissible κ S) ∧
    (∀ κ, 4 ≤ κ → ∀ S, S < 58 → ¬ ((4 * κ + 1) * (4 * κ + 1) < 4 * S + 1)) ∧
    (isPrime 193 ∧ 48 % 2 = 0 ∧ 48 % 3 = 0 ∧ 13 * 13 < 193) ∧
    (isPrime 5 ∧ isPrime 41 ∧ 10 % 2 = 0 ∧ 10 % 3 = 1 ∧ 25 < 41) ∧ ¬ isPrime 9 := by
  refine ⟨by decide +kernel, by decide +kernel, fun κ hκ S hS h => ?_, by decide +kernel,
    by decide +kernel, by decide +kernel⟩
  have h1 : 17 * 17 ≤ (4 * κ + 1) * (4 * κ + 1) :=
    Nat.mul_le_mul (Nat.succ_le_succ (Nat.mul_le_mul_left 4 hκ)) (Nat.succ_le_succ (Nat.mul_le_mul_left 4 hκ))
  have h2 : 4 * S + 1 ≤ 229 := Nat.succ_le_succ (Nat.mul_le_mul_left 4 (Nat.le_of_lt_succ hS))
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt h1 h) (Nat.le_trans h2 (by decide)))

/-- 10:F2, 10:F3, 10:F4, 10:G3 — the derived domains realized on `𝔽₁₃` (`κ = 3`, the flag `(0, 3)`):
`[m] = [E][v]⁻² = (11, 4)`, `[a] = (1, 10)`, `[F] = [m][a] = (12, 2)`, `[p] = [m][v] = (12, 3) = I_q [L]⁻¹`,
`[S] = [E][T] = I_q`, `[P] = (0, 1)`, `[G] = [F][L]²[m]⁻² = (5, 6)`; the geometric conversions `[Għ/c³] = [L]²`,
`[Gm/c²] = [L]`, `[Gm/c³] = [T]`, `[Gm/r³] = [T]⁻²`; `[Θ] = [E][k_B]⁻¹ = [a]` and the Unruh closure;
the phase exponent `[E][T][ħ]⁻¹ = 1`; kinetic energy `[m][v]² = [E]`; `Q + Q²` inhomogeneous, `[L] ≠ [L]²`;
`F/a = [m]`, flagged. -/
theorem realized13 :
    let E := energy 3; let v := L 3 * (T 3)⁻¹; let m := E * (v ^ 2)⁻¹; let a := v * (T 3)⁻¹
    let f := m * a; let pm := m * v; let G := f * L 3 ^ 2 * (m ^ 2)⁻¹; let kB := flag 3 * (L 3)⁻¹ * T 3
    m = ⟨11, 4⟩ ∧ a = ⟨1, 10⟩ ∧ f = ⟨12, 2⟩ ∧ pm = ⟨12, 3⟩ ∧ pm = mom 3 ∧ E * T 3 = flag 3 ∧
    E * (T 3)⁻¹ = ⟨0, 1⟩ ∧ G = ⟨5, 6⟩ ∧
    G * flag 3 * (v ^ 3)⁻¹ = L 3 ^ 2 ∧ G * m * (v ^ 2)⁻¹ = L 3 ∧ G * m * (v ^ 3)⁻¹ = T 3 ∧
    G * m * (L 3 ^ 3)⁻¹ = (T 3 ^ 2)⁻¹ ∧ E * kB⁻¹ = a ∧ flag 3 * a * v⁻¹ * kB⁻¹ = a ∧
    E * T 3 * (flag 3)⁻¹ = 1 ∧ m * v ^ 2 = E ∧ L 3 ≠ L 3 ^ 2 ∧ f * a⁻¹ = m := by
  decide

/-- 10:D6 — the flag is horizon-inaccessible on `𝔽₁₃`: no label with `|r|, |s| ≤ 2 < κ = 3` (the
representatives `r ∈ {11, 12, 0, 1, 2}`, `s ∈ {10, 11, 0, 1, 2}`) is `I_q = (0, 3)`, while at `H = 3` the
label `(0, 3)` itself is the flag. -/
theorem flag_inaccessible13 :
    (∀ x : DomK 3, (x.r.val ≤ 2 ∨ 11 ≤ x.r.val) → (x.s.val ≤ 2 ∨ 10 ≤ x.s.val) → x ≠ flag 3) ∧
    (⟨0, 3⟩ : DomK 3) = flag 3 := by decide +kernel

/-- 10:G2 — the window ladder by integer squares: `(2√κ)² = 4κ < (κ/2)² = κ²/4`, i.e. `16κ < κ²`, holds for
`κ = 17, 387, 602 140` and fails for `κ = 3`; the coherence identity `(2√κ)² = 4κ = p − 1` and the
totality closure `4S = Ω − 1` on the laboratory Carrier. -/
theorem window_ladder :
    16 * 17 < 17 * 17 ∧ 16 * 387 < 387 * 387 ∧ 16 * 602140 < 602140 * 602140 ∧ ¬ (16 * 3 < 3 * 3) ∧
    (∀ κ, 2 * 2 * κ = 4 * κ ∧ 4 * κ = (4 * κ + 1) - 1) ∧ 4 * 602140 = 2408561 - 1 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, fun κ => ⟨rfl, rfl⟩, by decide +kernel⟩

/-- 10:G1, 10:G3 — local recovery on `𝔽₁₃` at `H = 5`: the `121` conventional pairs `|r|, |s| ≤ 5` have
distinct modular labels, `12 > 10`. -/
theorem recovery13 :
    12 > 2 * 5 ∧
    ∀ r, r < 11 → ∀ s, s < 11 → ∀ r', r' < 11 → ∀ s', s' < 11 →
      ((ofNat (r + 8) : Shell 13) = ofNat (r' + 8) ∧ (ofNat (s + 7) : Shell 12) = ofNat (s' + 7)) →
      r = r' ∧ s = s' := by
  refine ⟨by decide +kernel, by decide +kernel⟩

/-- 10:G3 — the energy–momentum relation realized on `𝔽₁₃`: with `[v] = [L][T]⁻¹`, `[p] = I_q[L]⁻¹` and
`[m] = (11, 4)`, the three labels `[E]²`, `([p][c])²`, `([m][c]²)²` coincide, `(0, 4) = I_q²[T]⁻²`, the
fibre of `[E]²`, so `E² = p²c² + m²c⁴` is homogeneous; its massless case `[E] = [p][c]`, and `[E] = [m][c]²`
on the energy fibre, `[m] = [E][v]⁻²`. -/
theorem energy_momentum13 :
    let E := energy 3; let v := L 3 * (T 3)⁻¹
    E ^ 2 = (mom 3 * v) ^ 2 ∧ E ^ 2 = ((⟨11, 4⟩ : DomK 3) * v ^ 2) ^ 2 ∧ E ^ 2 = ⟨0, 4⟩ ∧
    E ^ 2 = flag 3 ^ 2 * (T 3 ^ 2)⁻¹ ∧ E = mom 3 * v ∧ E = ⟨11, 4⟩ * v ^ 2 ∧ E * (v ^ 2)⁻¹ = ⟨11, 4⟩ := by
  decide

end values

-- Ledger rows of 10-dimensions (generated by make_rows.py from docs/10-dimensions/10-dimensions-ledger.json; edit the ledger, not this section)
/-- 10:C2 — The modular unit-domain group and the grading: $\{U_{r,s}\}$ is a finite abelian group isomorphic to $\Dp$ under $U_{r,s}U_{r',s'}=U_{r+r',s+s'}$, and $\Ap$ is $\Dp$-graded, $\Ap^{(r,s)}\Ap^{(r',s')}\subseteq\Ap^{(r+r',s+s')}$. -/
theorem row_C2 : ∀ {p n : Nat} [FRC.Pos p] [FRC.Pos n] (a : FRC.Dimensions.Dom p n), a * a⁻¹ = (1 : FRC.Dimensions.Dom p n) :=
  @FRC.Dimensions.Dom.mul_inv
/-- 10:C3 — Fibrewise addition and the neutral-domain criterion: a sum of homogeneous quantities is homogeneous exactly when its nonzero summands share a domain, the fibre components adding separately; a monomial $\prod Q_j^{k_j}$ has domain $\sum k_j(r_j,s_j)$ and is a neutral-domain invariant iff that sum is $(0,0)$ in $\Dp$. -/
theorem row_C3 : ∀ {p n : Nat} [FRC.Pos p] [FRC.Pos n] (a : FRC.Dimensions.Dom p n) (k : Nat), a ^ k = { r := FRC.Shell.ofNat k * a.r, s := FRC.Shell.ofNat k * a.s } :=
  @FRC.Dimensions.Dom.pow_eq
/-- 10:C6 — What the action forces and what is declared: the time-exponent period $\p-1$ is forced by the pushforward action of $\Zp^{\times}$, the space-exponent refinement to period $\p$ is declared and carried by the transport theorem (D2); classical temporal unit change is nominal re-assignment within a fixed presentation, the chronon atomic. -/
theorem row_C6 : ∀ (κ : Nat) [FRC.Pos κ], (FRC.Dimensions.L κ * FRC.Dimensions.T κ ^ κ) ^ ((4 : Nat) * κ + (1 : Nat)) = FRC.Dimensions.flag κ :=
  @FRC.Dimensions.meridian_transport
/-- 10:D1 — Chart duality: $[f]=\unitT^{-1}$; $\delta_S:D\mapsto D^{-1}$ is an involution of the domain group whose orbit on the generators is the four-domain structure (space, momentum, time, energy); $\delta_C$ the second involution, carrying $\unitL\mapsto[p]$, $\unitT\mapsto\unitE$. -/
theorem row_D1 : (∀ {p n : Nat} [FRC.Pos p] [FRC.Pos n] (a : FRC.Dimensions.Dom p n), a⁻¹⁻¹ = a) ∧ ∀ (κ : Nat) [FRC.Pos κ] (a : FRC.Dimensions.DomK κ), FRC.Dimensions.deltaC κ (FRC.Dimensions.deltaC κ a) = a ∧ FRC.Dimensions.deltaC κ (FRC.Dimensions.L κ) = FRC.Dimensions.mom κ ∧ FRC.Dimensions.deltaC κ (FRC.Dimensions.T κ) = FRC.Dimensions.energy κ :=
  And.intro @FRC.Dimensions.Dom.inv_inv (@FRC.Dimensions.deltaC_involutive)
/-- 10:D2 — The internal flag: $\Dp$ contains exactly one subgroup of order four, $\langle\unitT^{\kap}\rangle$, entirely in the time-exponent factor; $\Iq:=\unitT^{\kap}$, $\Iq^{4}=1$, $\Iq^{2}=\unitT^{\pi}$; no flag of space ($\Z_\p$ has no element of order four); the two periods interfere, $(\unitL\unitT^{\kap})^{\p}=\Iq$, on three shells. -/
theorem row_D2 : (∀ (κ : Nat) [FRC.Pos κ], FRC.Dimensions.flag κ ^ (2 : Nat) = FRC.Dimensions.T κ ^ ((2 : Nat) * κ) ∧ FRC.Dimensions.flag κ ^ (1 : Nat) ≠ (1 : FRC.Dimensions.DomK κ) ∧ FRC.Dimensions.flag κ ^ (2 : Nat) ≠ (1 : FRC.Dimensions.DomK κ) ∧ FRC.Dimensions.flag κ ^ (3 : Nat) ≠ (1 : FRC.Dimensions.DomK κ)) ∧ (∀ (κ : Nat) {g : FRC.Shell ((4 : Nat) * κ + (1 : Nat))}, FRC.Shell.Frame ((4 : Nat) * κ + (1 : Nat)) κ g → ∀ (r : FRC.Shell ((4 : Nat) * κ + (1 : Nat))), (2 : FRC.Shell ((4 : Nat) * κ + (1 : Nat))) * (2 : FRC.Shell ((4 : Nat) * κ + (1 : Nat))) * r = (0 : FRC.Shell ((4 : Nat) * κ + (1 : Nat))) → r = (0 : FRC.Shell ((4 : Nat) * κ + (1 : Nat)))) ∧ ∀ (x : FRC.Dimensions.DomK (3 : Nat)), x ^ (4 : Nat) = (1 : FRC.Dimensions.DomK (3 : Nat)) ∧ x ^ (2 : Nat) ≠ (1 : FRC.Dimensions.DomK (3 : Nat)) ↔ x = FRC.Dimensions.flag (3 : Nat) ∨ x = (FRC.Dimensions.flag (3 : Nat))⁻¹ :=
  And.intro @FRC.Dimensions.flag_order_four (And.intro @FRC.Dimensions.no_flag_of_space (@FRC.Dimensions.order_four_13))
/-- 10:D3 — The lift: the flag records the quarter the chart duality forgets --- on charts the cardinal skeleton acts as $s\bmod2$ ($F$ exchanges the conjugate charts, $J$ fixes them), on labels $s\mapsto\Iq^{s}$ is an isomorphism $\Z_4\to\langle\Iq\rangle$ whose quotient by $\{0,2\kap\}$ returns the chart action; on the Carrier $\hbar^{2}=-1$, $\hbar^{4}=1$, $\hbar^{2}\ne1$, the crossing quantum of order four, never two. Shells $(13,2)$, $(173,3)$; Carriers $233$, $2\,408\,561$. -/
theorem row_D3 : ∀ (κ : Nat) [FRC.Pos κ], FRC.Dimensions.flag κ ^ (0 : Nat) = (1 : FRC.Dimensions.DomK κ) ∧ FRC.Dimensions.flag κ ^ (1 : Nat) = { r := (0 : FRC.Shell ((4 : Nat) * κ + (1 : Nat))), s := FRC.Shell.ofNat κ } ∧ FRC.Dimensions.flag κ ^ (2 : Nat) = { r := (0 : FRC.Shell ((4 : Nat) * κ + (1 : Nat))), s := FRC.Shell.ofNat ((2 : Nat) * κ) } ∧ FRC.Dimensions.flag κ ^ (3 : Nat) = { r := (0 : FRC.Shell ((4 : Nat) * κ + (1 : Nat))), s := FRC.Shell.ofNat ((3 : Nat) * κ) } ∧ FRC.Dimensions.flag κ ^ (4 : Nat) = (1 : FRC.Dimensions.DomK κ) ∧ FRC.Dimensions.flag κ ^ (2 : Nat) * FRC.Dimensions.flag κ ^ (2 : Nat) = (1 : FRC.Dimensions.DomK κ) :=
  @FRC.Dimensions.record_values
/-- 10:D6 — The flagged readings over the counts: $\unitE=[h][f]=\Iq\unitT^{-1}$, $[p]=\unithbar[k]=\Iq\unitL^{-1}$, one quantity per pair, the flagged reading one capacity step above its count; $[S]=\unitE\unitT=\Iq$ and every phase count neutral, $\unitE\unitT\unithbar^{-1}=1$; the absolute unit is horizon-inaccessible (no monomial of a window $H\ll\kap$ expresses the flag) and becomes visible at $\kap\le H<2\kap$. -/
theorem row_D6 : (∀ (κ : Nat) [FRC.Pos κ], FRC.Dimensions.energy κ = { r := (0 : FRC.Shell ((4 : Nat) * κ + (1 : Nat))), s := FRC.Shell.ofNat κ + (-1 : FRC.Shell ((4 : Nat) * κ)) } ∧ FRC.Dimensions.mom κ = { r := (-1 : FRC.Shell ((4 : Nat) * κ + (1 : Nat))), s := FRC.Shell.ofNat κ } ∧ FRC.Dimensions.energy κ * FRC.Dimensions.T κ = FRC.Dimensions.flag κ ∧ FRC.Dimensions.energy κ * FRC.Dimensions.T κ * (FRC.Dimensions.flag κ)⁻¹ = (1 : FRC.Dimensions.DomK κ) ∧ FRC.Dimensions.mom κ * FRC.Dimensions.L κ * (FRC.Dimensions.flag κ)⁻¹ = (1 : FRC.Dimensions.DomK κ)) ∧ (∀ (x : FRC.Dimensions.DomK (3 : Nat)), x.r.val ≤ (2 : Nat) ∨ (11 : Nat) ≤ x.r.val → x.s.val ≤ (2 : Nat) ∨ (10 : Nat) ≤ x.s.val → x ≠ FRC.Dimensions.flag (3 : Nat)) ∧ { r := (0 : FRC.Shell ((4 : Nat) * (3 : Nat) + (1 : Nat))), s := (3 : FRC.Shell ((4 : Nat) * (3 : Nat))) } = FRC.Dimensions.flag (3 : Nat) :=
  And.intro @FRC.Dimensions.flagged_readings (@FRC.Dimensions.flag_inaccessible13)
/-- 10:E4 — The defining congruences, pair form: on the Carrier chart $2G+1\equiv0$, $2c^{2}\equiv1$, $\hbar^{2}\equiv-1$, $k_B^{2}\equiv-2\pmod\Om$ determine the constants uniquely at pair level --- $G=2\dS$ exact, the quadratics each with exactly two roots $\{x,-x\}$ (admissibility guarantees the residues: $\Om\equiv1\bmod4$, $\dS$ even for $2$, hence $-2$) --- and the linkage $\{\pm k_B\}\{\pm c\}=\{\pm\hbar\}$ is derived at pair level; the root pair of $-1$ is $\{\hbar,h\}$ with $h=2\pi\hbar\equiv-\hbar$. Exhaustive on both Carriers. -/
theorem row_E4 : (∀ {Ω : Nat} [FRC.Pos Ω] {S : Nat} {g : FRC.Shell Ω}, FRC.Shell.Frame Ω S g → ∀ (x : FRC.Shell Ω), (2 : FRC.Shell Ω) * x + (1 : FRC.Shell Ω) = (0 : FRC.Shell Ω) ↔ x = FRC.Shell.ofNat ((2 : Nat) * S)) ∧ (∀ {Ω : Nat} [FRC.Pos Ω] {S : Nat} {g : FRC.Shell Ω}, FRC.Shell.Frame Ω S g → ∀ (a x : FRC.Shell Ω), x * x = a → x ≠ (0 : FRC.Shell Ω) → (∀ (y : FRC.Shell Ω), y * y = a ↔ y = x ∨ y = -x) ∧ -x ≠ x) ∧ (∀ {Ω : Nat} [FRC.Pos Ω] {S : Nat} {g : FRC.Shell Ω}, FRC.Shell.Frame Ω S g → ∀ (G c h k : FRC.Shell Ω), (2 : FRC.Shell Ω) * G + (1 : FRC.Shell Ω) = (0 : FRC.Shell Ω) → (2 : FRC.Shell Ω) * (c * c) = (1 : FRC.Shell Ω) → h * h = (-1 : FRC.Shell Ω) → k * k = (-2 : FRC.Shell Ω) → k * c * (k * c) = (-1 : FRC.Shell Ω) ∧ (k * c = h ∨ k * c = -h) ∧ G = -(c * c) ∧ (2 : FRC.Shell Ω) * G * ((2 : FRC.Shell Ω) * G) = (1 : FRC.Shell Ω) ∧ h * h * (h * h) = (1 : FRC.Shell Ω) ∧ h * c * (h * c) = (-2 : FRC.Shell Ω) * (G * G)) ∧ ((2 : FRC.Shell (233 : Nat)) * (116 : FRC.Shell (233 : Nat)) + (1 : FRC.Shell (233 : Nat)) = (0 : FRC.Shell (233 : Nat)) ∧ (89 : FRC.Shell (233 : Nat)) * (89 : FRC.Shell (233 : Nat)) = (-1 : FRC.Shell (233 : Nat)) ∧ (124 : FRC.Shell (233 : Nat)) * (124 : FRC.Shell (233 : Nat)) = (-2 : FRC.Shell (233 : Nat)) ∧ (2 : FRC.Shell (233 : Nat)) * ((159 : FRC.Shell (233 : Nat)) * (159 : FRC.Shell (233 : Nat))) = (1 : FRC.Shell (233 : Nat)) ∧ (124 : FRC.Shell (233 : Nat)) * (159 : FRC.Shell (233 : Nat)) = (-89 : FRC.Shell (233 : Nat)) ∧ (144 : FRC.Shell (233 : Nat)) = (-89 : FRC.Shell (233 : Nat)) ∧ (116 : FRC.Shell (233 : Nat)) = -((159 : FRC.Shell (233 : Nat)) * (159 : FRC.Shell (233 : Nat))) ∧ (89 : FRC.Shell (233 : Nat)) * (159 : FRC.Shell (233 : Nat)) = (124 : FRC.Shell (233 : Nat)) * (116 : FRC.Shell (233 : Nat)) ∧ (109 : FRC.Shell (233 : Nat)) = (-124 : FRC.Shell (233 : Nat)) ∧ (109 : FRC.Shell (233 : Nat)) * (159 : FRC.Shell (233 : Nat)) ≠ (-89 : FRC.Shell (233 : Nat))) ∧ (2 : FRC.Shell (2408561 : Nat)) * (1204280 : FRC.Shell (2408561 : Nat)) + (1 : FRC.Shell (2408561 : Nat)) = (0 : FRC.Shell (2408561 : Nat)) ∧ (18688 : FRC.Shell (2408561 : Nat)) * (18688 : FRC.Shell (2408561 : Nat)) = (-1 : FRC.Shell (2408561 : Nat)) ∧ (1880160 : FRC.Shell (2408561 : Nat)) * (1880160 : FRC.Shell (2408561 : Nat)) = (-2 : FRC.Shell (2408561 : Nat)) ∧ (2 : FRC.Shell (2408561 : Nat)) * ((171106 : FRC.Shell (2408561 : Nat)) * (171106 : FRC.Shell (2408561 : Nat))) = (1 : FRC.Shell (2408561 : Nat)) ∧ (1880160 : FRC.Shell (2408561 : Nat)) * (171106 : FRC.Shell (2408561 : Nat)) = (-18688 : FRC.Shell (2408561 : Nat)) ∧ (2389873 : FRC.Shell (2408561 : Nat)) = (-18688 : FRC.Shell (2408561 : Nat)) ∧ (1204280 : FRC.Shell (2408561 : Nat)) = -((171106 : FRC.Shell (2408561 : Nat)) * (171106 : FRC.Shell (2408561 : Nat))) ∧ (18688 : FRC.Shell (2408561 : Nat)) * (171106 : FRC.Shell (2408561 : Nat)) = (1880160 : FRC.Shell (2408561 : Nat)) * (1204280 : FRC.Shell (2408561 : Nat)) :=
  And.intro @FRC.Dimensions.G_unique (And.intro @FRC.Dimensions.root_pair (And.intro @FRC.Dimensions.linkage (And.intro @FRC.Dimensions.carrier233 (@FRC.Dimensions.carrierLab))))
/-- 10:E5 — Pair consequences and representative inertness: $G=-c^{2}$, $G^{2}\equiv4^{-1}$, $\hbar^{4}\equiv1$, $(k_Bc)^{2}\equiv-1$, and $\hbar cG^{-1}$ lands in $\{\pm k_B\}$; of the eight sign assignments exactly the four with $\sigma_\hbar=\sigma_c\sigma_k$ are admissible, a $(\Z/2)^{2}$, every identity holding on each and the $\hbar$-flip relabelling within $\{\hbar,h\}$; what a bounded observer registers is exactly the pair-inert content. -/
theorem row_E5 : (∀ {Ω : Nat} [FRC.Pos Ω] {S : Nat} {g : FRC.Shell Ω}, FRC.Shell.Frame Ω S g → ∀ (G c h k : FRC.Shell Ω), (2 : FRC.Shell Ω) * G + (1 : FRC.Shell Ω) = (0 : FRC.Shell Ω) → (2 : FRC.Shell Ω) * (c * c) = (1 : FRC.Shell Ω) → h * h = (-1 : FRC.Shell Ω) → k * k = (-2 : FRC.Shell Ω) → k * c * (k * c) = (-1 : FRC.Shell Ω) ∧ (k * c = h ∨ k * c = -h) ∧ G = -(c * c) ∧ (2 : FRC.Shell Ω) * G * ((2 : FRC.Shell Ω) * G) = (1 : FRC.Shell Ω) ∧ h * h * (h * h) = (1 : FRC.Shell Ω) ∧ h * c * (h * c) = (-2 : FRC.Shell Ω) * (G * G)) ∧ ((2 : FRC.Shell (233 : Nat)) * (116 : FRC.Shell (233 : Nat)) + (1 : FRC.Shell (233 : Nat)) = (0 : FRC.Shell (233 : Nat)) ∧ (89 : FRC.Shell (233 : Nat)) * (89 : FRC.Shell (233 : Nat)) = (-1 : FRC.Shell (233 : Nat)) ∧ (124 : FRC.Shell (233 : Nat)) * (124 : FRC.Shell (233 : Nat)) = (-2 : FRC.Shell (233 : Nat)) ∧ (2 : FRC.Shell (233 : Nat)) * ((159 : FRC.Shell (233 : Nat)) * (159 : FRC.Shell (233 : Nat))) = (1 : FRC.Shell (233 : Nat)) ∧ (124 : FRC.Shell (233 : Nat)) * (159 : FRC.Shell (233 : Nat)) = (-89 : FRC.Shell (233 : Nat)) ∧ (144 : FRC.Shell (233 : Nat)) = (-89 : FRC.Shell (233 : Nat)) ∧ (116 : FRC.Shell (233 : Nat)) = -((159 : FRC.Shell (233 : Nat)) * (159 : FRC.Shell (233 : Nat))) ∧ (89 : FRC.Shell (233 : Nat)) * (159 : FRC.Shell (233 : Nat)) = (124 : FRC.Shell (233 : Nat)) * (116 : FRC.Shell (233 : Nat)) ∧ (109 : FRC.Shell (233 : Nat)) = (-124 : FRC.Shell (233 : Nat)) ∧ (109 : FRC.Shell (233 : Nat)) * (159 : FRC.Shell (233 : Nat)) ≠ (-89 : FRC.Shell (233 : Nat))) ∧ (2 : FRC.Shell (2408561 : Nat)) * (1204280 : FRC.Shell (2408561 : Nat)) + (1 : FRC.Shell (2408561 : Nat)) = (0 : FRC.Shell (2408561 : Nat)) ∧ (18688 : FRC.Shell (2408561 : Nat)) * (18688 : FRC.Shell (2408561 : Nat)) = (-1 : FRC.Shell (2408561 : Nat)) ∧ (1880160 : FRC.Shell (2408561 : Nat)) * (1880160 : FRC.Shell (2408561 : Nat)) = (-2 : FRC.Shell (2408561 : Nat)) ∧ (2 : FRC.Shell (2408561 : Nat)) * ((171106 : FRC.Shell (2408561 : Nat)) * (171106 : FRC.Shell (2408561 : Nat))) = (1 : FRC.Shell (2408561 : Nat)) ∧ (1880160 : FRC.Shell (2408561 : Nat)) * (171106 : FRC.Shell (2408561 : Nat)) = (-18688 : FRC.Shell (2408561 : Nat)) ∧ (2389873 : FRC.Shell (2408561 : Nat)) = (-18688 : FRC.Shell (2408561 : Nat)) ∧ (1204280 : FRC.Shell (2408561 : Nat)) = -((171106 : FRC.Shell (2408561 : Nat)) * (171106 : FRC.Shell (2408561 : Nat))) ∧ (18688 : FRC.Shell (2408561 : Nat)) * (171106 : FRC.Shell (2408561 : Nat)) = (1880160 : FRC.Shell (2408561 : Nat)) * (1204280 : FRC.Shell (2408561 : Nat)) :=
  And.intro @FRC.Dimensions.linkage (And.intro @FRC.Dimensions.carrier233 (@FRC.Dimensions.carrierLab))
/-- 10:E9 — The minimal admissible pair: under the programme's admissibility predicate ($\p=4\kap+1$ prime, $\kap>1$; $\Om=4\dS+1$ prime, $\dS$ even, $\dS\equiv1\bmod3$; $\p^{2}<\Om$) the smallest instance is $(\p,\Om)=(13,233)$, by exhaustive scan, with the counterfactuals: dropping the mod-$3$ clause admits $(13,193)$, dropping $\kap>1$ admits $(5,41)$, $\kap=2$ gives the composite $9$. -/
theorem row_E9 : FRC.Dimensions.admissible (3 : Nat) (58 : Nat) ∧ (∀ (κ : Nat), κ < (4 : Nat) → ∀ (S : Nat), S < (58 : Nat) → ¬FRC.Dimensions.admissible κ S) ∧ (∀ (κ : Nat), (4 : Nat) ≤ κ → ∀ (S : Nat), S < (58 : Nat) → ¬((4 : Nat) * κ + (1 : Nat)) * ((4 : Nat) * κ + (1 : Nat)) < (4 : Nat) * S + (1 : Nat)) ∧ (FRC.Dimensions.isPrime (193 : Nat) ∧ (48 : Nat) % (2 : Nat) = (0 : Nat) ∧ (48 : Nat) % (3 : Nat) = (0 : Nat) ∧ (13 : Nat) * (13 : Nat) < (193 : Nat)) ∧ (FRC.Dimensions.isPrime (5 : Nat) ∧ FRC.Dimensions.isPrime (41 : Nat) ∧ (10 : Nat) % (2 : Nat) = (0 : Nat) ∧ (10 : Nat) % (3 : Nat) = (1 : Nat) ∧ (25 : Nat) < (41 : Nat)) ∧ ¬FRC.Dimensions.isPrime (9 : Nat) :=
  @FRC.Dimensions.minimality
/-- 10:F2 — The mechanical and gravitational domains: $[m]=\Iq\unitL^{-2}\unitT$; $[a]=\unitL\unitT^{-2}$, $[F]=\Iq\unitL^{-1}\unitT^{-1}$, $[p]=\Iq\unitL^{-1}$, $[S]=\Iq$, $[P]=\Iq\unitT^{-2}$, $[\text{pressure}]=\Iq\unitL^{-3}\unitT^{-1}$; $[G]=\Iq^{-1}\unitL^{5}\unitT^{-3}$; the geometric conversions $[G\hbar/c^{3}]=\unitL^{2}$, $[Gm/c^{2}]=\unitL$, $[Gm/c^{3}]=\unitT$, $[G\rho_m]=\unitT^{-2}$; mass derived, not primitive. -/
theorem row_F2 : have E := FRC.Dimensions.energy (3 : Nat); have v := FRC.Dimensions.L (3 : Nat) * (FRC.Dimensions.T (3 : Nat))⁻¹; have m := E * (v ^ (2 : Nat))⁻¹; have a := v * (FRC.Dimensions.T (3 : Nat))⁻¹; have f := m * a; have pm := m * v; have G := f * FRC.Dimensions.L (3 : Nat) ^ (2 : Nat) * (m ^ (2 : Nat))⁻¹; have kB := FRC.Dimensions.flag (3 : Nat) * (FRC.Dimensions.L (3 : Nat))⁻¹ * FRC.Dimensions.T (3 : Nat); m = { r := (11 : FRC.Shell ((4 : Nat) * (3 : Nat) + (1 : Nat))), s := (4 : FRC.Shell ((4 : Nat) * (3 : Nat))) } ∧ a = { r := (1 : FRC.Shell ((4 : Nat) * (3 : Nat) + (1 : Nat))), s := (10 : FRC.Shell ((4 : Nat) * (3 : Nat))) } ∧ f = { r := (12 : FRC.Shell ((4 : Nat) * (3 : Nat) + (1 : Nat))), s := (2 : FRC.Shell ((4 : Nat) * (3 : Nat))) } ∧ pm = { r := (12 : FRC.Shell ((4 : Nat) * (3 : Nat) + (1 : Nat))), s := (3 : FRC.Shell ((4 : Nat) * (3 : Nat))) } ∧ pm = FRC.Dimensions.mom (3 : Nat) ∧ E * FRC.Dimensions.T (3 : Nat) = FRC.Dimensions.flag (3 : Nat) ∧ E * (FRC.Dimensions.T (3 : Nat))⁻¹ = { r := (0 : FRC.Shell ((4 : Nat) * (3 : Nat) + (1 : Nat))), s := (1 : FRC.Shell ((4 : Nat) * (3 : Nat))) } ∧ G = { r := (5 : FRC.Shell ((4 : Nat) * (3 : Nat) + (1 : Nat))), s := (6 : FRC.Shell ((4 : Nat) * (3 : Nat))) } ∧ G * FRC.Dimensions.flag (3 : Nat) * (v ^ (3 : Nat))⁻¹ = FRC.Dimensions.L (3 : Nat) ^ (2 : Nat) ∧ G * m * (v ^ (2 : Nat))⁻¹ = FRC.Dimensions.L (3 : Nat) ∧ G * m * (v ^ (3 : Nat))⁻¹ = FRC.Dimensions.T (3 : Nat) ∧ G * m * (FRC.Dimensions.L (3 : Nat) ^ (3 : Nat))⁻¹ = (FRC.Dimensions.T (3 : Nat) ^ (2 : Nat))⁻¹ ∧ E * kB⁻¹ = a ∧ FRC.Dimensions.flag (3 : Nat) * a * v⁻¹ * kB⁻¹ = a ∧ E * FRC.Dimensions.T (3 : Nat) * (FRC.Dimensions.flag (3 : Nat))⁻¹ = (1 : FRC.Dimensions.DomK (3 : Nat)) ∧ m * v ^ (2 : Nat) = E ∧ FRC.Dimensions.L (3 : Nat) ≠ FRC.Dimensions.L (3 : Nat) ^ (2 : Nat) ∧ f * a⁻¹ = m :=
  @FRC.Dimensions.realized13
/-- 10:F3 — Temperature carries the acceleration domain: $[\Theta]=\unitE[k_B]^{-1}=\unitL\unitT^{-2}=[a]$, flag-free; the Unruh combination $\hbar a/c\,k_B$ closes flag-free in the algebra; neither mass nor temperature is primitive, the classical $M$-$L$-$T$-plus-thermal system the torsion-free shadow of two generators plus the flag. -/
theorem row_F3 : have E := FRC.Dimensions.energy (3 : Nat); have v := FRC.Dimensions.L (3 : Nat) * (FRC.Dimensions.T (3 : Nat))⁻¹; have m := E * (v ^ (2 : Nat))⁻¹; have a := v * (FRC.Dimensions.T (3 : Nat))⁻¹; have f := m * a; have pm := m * v; have G := f * FRC.Dimensions.L (3 : Nat) ^ (2 : Nat) * (m ^ (2 : Nat))⁻¹; have kB := FRC.Dimensions.flag (3 : Nat) * (FRC.Dimensions.L (3 : Nat))⁻¹ * FRC.Dimensions.T (3 : Nat); m = { r := (11 : FRC.Shell ((4 : Nat) * (3 : Nat) + (1 : Nat))), s := (4 : FRC.Shell ((4 : Nat) * (3 : Nat))) } ∧ a = { r := (1 : FRC.Shell ((4 : Nat) * (3 : Nat) + (1 : Nat))), s := (10 : FRC.Shell ((4 : Nat) * (3 : Nat))) } ∧ f = { r := (12 : FRC.Shell ((4 : Nat) * (3 : Nat) + (1 : Nat))), s := (2 : FRC.Shell ((4 : Nat) * (3 : Nat))) } ∧ pm = { r := (12 : FRC.Shell ((4 : Nat) * (3 : Nat) + (1 : Nat))), s := (3 : FRC.Shell ((4 : Nat) * (3 : Nat))) } ∧ pm = FRC.Dimensions.mom (3 : Nat) ∧ E * FRC.Dimensions.T (3 : Nat) = FRC.Dimensions.flag (3 : Nat) ∧ E * (FRC.Dimensions.T (3 : Nat))⁻¹ = { r := (0 : FRC.Shell ((4 : Nat) * (3 : Nat) + (1 : Nat))), s := (1 : FRC.Shell ((4 : Nat) * (3 : Nat))) } ∧ G = { r := (5 : FRC.Shell ((4 : Nat) * (3 : Nat) + (1 : Nat))), s := (6 : FRC.Shell ((4 : Nat) * (3 : Nat))) } ∧ G * FRC.Dimensions.flag (3 : Nat) * (v ^ (3 : Nat))⁻¹ = FRC.Dimensions.L (3 : Nat) ^ (2 : Nat) ∧ G * m * (v ^ (2 : Nat))⁻¹ = FRC.Dimensions.L (3 : Nat) ∧ G * m * (v ^ (3 : Nat))⁻¹ = FRC.Dimensions.T (3 : Nat) ∧ G * m * (FRC.Dimensions.L (3 : Nat) ^ (3 : Nat))⁻¹ = (FRC.Dimensions.T (3 : Nat) ^ (2 : Nat))⁻¹ ∧ E * kB⁻¹ = a ∧ FRC.Dimensions.flag (3 : Nat) * a * v⁻¹ * kB⁻¹ = a ∧ E * FRC.Dimensions.T (3 : Nat) * (FRC.Dimensions.flag (3 : Nat))⁻¹ = (1 : FRC.Dimensions.DomK (3 : Nat)) ∧ m * v ^ (2 : Nat) = E ∧ FRC.Dimensions.L (3 : Nat) ≠ FRC.Dimensions.L (3 : Nat) ^ (2 : Nat) ∧ f * a⁻¹ = m :=
  @FRC.Dimensions.realized13
/-- 10:F4 — Count-valued comparisons are flag-free: every ratio of two quantities of equal crossing degree ($Gm/r^{3}$, the phase exponent $[E][T]/[\hbar]$) is a neutral or flag-free label, the flag entering unitful measures only; $F/a=[m]$, crossing degrees $1$ and $0$, is the flagged boundary case. -/
theorem row_F4 : have E := FRC.Dimensions.energy (3 : Nat); have v := FRC.Dimensions.L (3 : Nat) * (FRC.Dimensions.T (3 : Nat))⁻¹; have m := E * (v ^ (2 : Nat))⁻¹; have a := v * (FRC.Dimensions.T (3 : Nat))⁻¹; have f := m * a; have pm := m * v; have G := f * FRC.Dimensions.L (3 : Nat) ^ (2 : Nat) * (m ^ (2 : Nat))⁻¹; have kB := FRC.Dimensions.flag (3 : Nat) * (FRC.Dimensions.L (3 : Nat))⁻¹ * FRC.Dimensions.T (3 : Nat); m = { r := (11 : FRC.Shell ((4 : Nat) * (3 : Nat) + (1 : Nat))), s := (4 : FRC.Shell ((4 : Nat) * (3 : Nat))) } ∧ a = { r := (1 : FRC.Shell ((4 : Nat) * (3 : Nat) + (1 : Nat))), s := (10 : FRC.Shell ((4 : Nat) * (3 : Nat))) } ∧ f = { r := (12 : FRC.Shell ((4 : Nat) * (3 : Nat) + (1 : Nat))), s := (2 : FRC.Shell ((4 : Nat) * (3 : Nat))) } ∧ pm = { r := (12 : FRC.Shell ((4 : Nat) * (3 : Nat) + (1 : Nat))), s := (3 : FRC.Shell ((4 : Nat) * (3 : Nat))) } ∧ pm = FRC.Dimensions.mom (3 : Nat) ∧ E * FRC.Dimensions.T (3 : Nat) = FRC.Dimensions.flag (3 : Nat) ∧ E * (FRC.Dimensions.T (3 : Nat))⁻¹ = { r := (0 : FRC.Shell ((4 : Nat) * (3 : Nat) + (1 : Nat))), s := (1 : FRC.Shell ((4 : Nat) * (3 : Nat))) } ∧ G = { r := (5 : FRC.Shell ((4 : Nat) * (3 : Nat) + (1 : Nat))), s := (6 : FRC.Shell ((4 : Nat) * (3 : Nat))) } ∧ G * FRC.Dimensions.flag (3 : Nat) * (v ^ (3 : Nat))⁻¹ = FRC.Dimensions.L (3 : Nat) ^ (2 : Nat) ∧ G * m * (v ^ (2 : Nat))⁻¹ = FRC.Dimensions.L (3 : Nat) ∧ G * m * (v ^ (3 : Nat))⁻¹ = FRC.Dimensions.T (3 : Nat) ∧ G * m * (FRC.Dimensions.L (3 : Nat) ^ (3 : Nat))⁻¹ = (FRC.Dimensions.T (3 : Nat) ^ (2 : Nat))⁻¹ ∧ E * kB⁻¹ = a ∧ FRC.Dimensions.flag (3 : Nat) * a * v⁻¹ * kB⁻¹ = a ∧ E * FRC.Dimensions.T (3 : Nat) * (FRC.Dimensions.flag (3 : Nat))⁻¹ = (1 : FRC.Dimensions.DomK (3 : Nat)) ∧ m * v ^ (2 : Nat) = E ∧ FRC.Dimensions.L (3 : Nat) ≠ FRC.Dimensions.L (3 : Nat) ^ (2 : Nat) ∧ f * a⁻¹ = m :=
  @FRC.Dimensions.realized13
set_option linter.defProp false in
/-- 10:G1 — Local recovery: for an exponent horizon $H$ with $4\kap>2H$ the modular labels distinguish every conventional pair $|r|,|s|\le H$; the flagged sector is recovered through the crossing degree, $M^{u}L^{a}T^{b}\mapsto(a-2u,\,b+u;\,u)$ injective and windowed-faithful. -/
def row_G1 := @FRC.Dimensions.recovery13
/-- 10:G2 — The window ladder: coherence $2\sqrt\kap$ below recovery $\kap/2$ below flag inaccessibility $\kap$ below covariance $2\kap$, nested strictly for every $\kap\ge17$ and failing for the toy $\kap=3$, all orderings by integer squares; the coherence identity $(2\sqrt\kap)^{2}=\p-1$ and the totality closure $(2\sqrt\dS)^{2}=\Om-1$. -/
theorem row_G2 : (16 : Nat) * (17 : Nat) < (17 : Nat) * (17 : Nat) ∧ (16 : Nat) * (387 : Nat) < (387 : Nat) * (387 : Nat) ∧ (16 : Nat) * (602140 : Nat) < (602140 : Nat) * (602140 : Nat) ∧ ¬(16 : Nat) * (3 : Nat) < (3 : Nat) * (3 : Nat) ∧ (∀ (κ : Nat), (2 : Nat) * (2 : Nat) * κ = (4 : Nat) * κ ∧ (4 : Nat) * κ = (4 : Nat) * κ + (1 : Nat) - (1 : Nat)) ∧ (4 : Nat) * (602140 : Nat) = (2408561 : Nat) - (1 : Nat) :=
  @FRC.Dimensions.window_ladder
set_option linter.defProp false in
/-- 10:G3 — The worked examples: $\kap=3$, $H=5$, $12>10$ so every pair in $[-5,5]^{2}$ is distinguished; kinetic energy $[m][v]^{2}=[E]$; $Q+Q^{2}$ inhomogeneous; the phase exponent neutral; flag arithmetic ($G\hbar/c^{3}$ flag-free, $\Iq^{2}=\unitT^{\pi}$); the Schwarzschild length $[Gm/c^{2}]=\unitL$; the gravitational frequency $[Gm/r^{3}]=\unitT^{-2}$; the energy--momentum relation $E^{2}=p^{2}c^{2}+m^{2}c^{4}$ homogeneous at crossing degree two, its massless case $E=pc$ at crossing degree one. -/
def row_G3 := And.intro @FRC.Dimensions.realized13 (And.intro @FRC.Dimensions.recovery13 (@FRC.Dimensions.energy_momentum13))
-- end ledger rows

end FRC.Dimensions
