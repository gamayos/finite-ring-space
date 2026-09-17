import FrcCore.Shell
import FrcCore.Pigeonhole

/-!
# FrcCore.Frame — the frame `(τ; 0, 1, g)` and the Euclidean datum, from first principles

The shell of capacity `κ` has modulus `p = 4κ + 1`; its frame carries the drive `g` (00:A8, 00:C1).
One decidable predicate states what the frame's generator is: `IsPrimitive g n` (`g^n = 1`, no positive
power below `n` is `1`). That `g` then *generates* — every nonzero residue is a power of `g`
(`Generates g n`, also decidable) — is proved by the pigeonhole (`FrcCore.Pigeonhole`): the `n` powers are
distinct nonzero residues and there are `n` of those. Primality of `p` is neither assumed nor used; the
classical equivalence ("a primitive root of order `p − 1` exists iff `p` is prime") is a theorem for later.

From primitivity alone: inverses (`exists_inv`), no zero divisors (`mul_eq_zero`), the square roots
of one (`sq_eq_one`), the half-period `g^{2κ} = −1` (2:D1, 00:C1), the quarter-turn `i = −g^κ` with
`i² = −1` (1:B3, 2:D2), its orientation classes under `g ↦ g^u` (2:D5), and the Euler identity
`(g^i)^{i·2κ} = (−1)^i` (2:D6, 00:C14). No axioms.
-/

namespace FRC
namespace Shell

variable {p : Nat} [Pos p]

/-- 00:A8 — the drive generator is primitive of order `n`: `g^n = 1` and `g^l ≠ 1` for `0 < l < n`. -/
def IsPrimitive (g : Shell p) (n : Nat) : Prop :=
  g ^ n = 1 ∧ ∀ l, l < n → 0 < l → g ^ l ≠ 1

instance (g : Shell p) (n : Nat) : Decidable (IsPrimitive g n) := by
  unfold IsPrimitive; exact inferInstance

/-- 00:A8 — the drive generates the shell: every nonzero residue `v < p` is `g^m` for some `m < n`. -/
def Generates (g : Shell p) (n : Nat) : Prop :=
  ∀ v, v < p → 0 < v → ∃ m, m < n ∧ (g ^ m).val = v

/-- Bounded existence `∃ m < n, P m`, decided by search — Lean's own `Nat.decidableExistsLT` carries
`propext` and `Quot.sound`; this one carries nothing. -/
def decExistsLT (P : Nat → Prop) [DecidablePred P] : (n : Nat) → Decidable (∃ m, m < n ∧ P m)
  | 0 => isFalse (fun ⟨m, hm, _⟩ => Nat.not_lt_zero m hm)
  | n + 1 =>
    match decExistsLT P n with
    | isTrue h => isTrue (match h with | ⟨m, hm, hp⟩ => ⟨m, Nat.lt_succ_of_lt hm, hp⟩)
    | isFalse hno =>
      if h : P n then isTrue ⟨n, Nat.lt_succ_self n, h⟩
      else isFalse (fun ⟨m, hm, hp⟩ =>
        match Nat.lt_or_ge m n with
        | .inl hlt => hno ⟨m, hlt, hp⟩
        | .inr hge => h ((Nat.le_antisymm (Nat.le_of_lt_succ hm) hge) ▸ hp))

instance (g : Shell p) (n : Nat) : Decidable (Generates g n) := by
  unfold Generates
  have : ∀ v, Decidable (∃ m, m < n ∧ (g ^ m).val = v) := fun v => decExistsLT (fun m => (g ^ m).val = v) n
  exact inferInstance

/-- 00:C1 — the frame `(τ; 0, 1, g)` on the shell of capacity `κ`: `p = 4κ + 1`, `κ` positive, and the
drive `g` a primitive generator of the `p − 1` nonzero residues. -/
structure Frame (p : Nat) [Pos p] (κ : Nat) (g : Shell p) : Prop where
  cap : p = 4 * κ + 1
  cap_pos : 0 < κ
  prim : IsPrimitive g (p - 1)

namespace Frame
variable {κ : Nat} {g : Shell p}

theorem n_eq (F : Frame p κ g) : p - 1 = 4 * κ := by rw [F.cap]; rfl

theorem n_pos (F : Frame p κ g) : 0 < p - 1 := by
  rw [F.n_eq]; exact Nat.mul_pos (Nat.zero_lt_succ 3) F.cap_pos

theorem one_lt_p (F : Frame p κ g) : 1 < p := by
  rw [F.cap]; exact Nat.succ_lt_succ (Nat.mul_pos (Nat.zero_lt_succ 3) F.cap_pos)

theorem one_ne_zero (F : Frame p κ g) : (1 : Shell p) ≠ 0 := fun h => by
  have := val_injective h
  rw [val_one, val_zero, FRC.Nat.mod_eq_of_lt F.one_lt_p] at this
  exact Nat.noConfusion this

theorem pow_n (F : Frame p κ g) : g ^ (p - 1) = 1 := F.prim.1

/-- Powers of the drive are periodic with period `p − 1`. -/
theorem pow_mod (F : Frame p κ g) (l : Nat) : g ^ l = g ^ (l % (p - 1)) := by
  match FRC.Nat.mod_spec (p - 1) F.n_pos l with
  | ⟨q, hq⟩ =>
    calc g ^ l = g ^ ((p - 1) * q + l % (p - 1)) := by rw [← hq]
      _ = (g ^ (p - 1)) ^ q * g ^ (l % (p - 1)) := by rw [pow_add, pow_mul]
      _ = g ^ (l % (p - 1)) := by rw [F.pow_n, one_pow, one_mul]

theorem pow_eq_one_of_mod (F : Frame p κ g) {l : Nat} (h : l % (p - 1) = 0) : g ^ l = 1 := by
  rw [F.pow_mod, h, pow_zero]

theorem mod_eq_zero_of_pow_eq_one (F : Frame p κ g) {l : Nat} (h : g ^ l = 1) : l % (p - 1) = 0 := by
  rw [F.pow_mod] at h
  exact match Nat.decEq (l % (p - 1)) 0 with
    | .isTrue h0 => h0
    | .isFalse h0 => absurd h (F.prim.2 _ (Nat.mod_lt l F.n_pos) (Nat.pos_of_ne_zero h0))

theorem pow_inj (F : Frame p κ g) {i j : Nat} (hi : i < p - 1) (hj : j < p - 1) (h : g ^ i = g ^ j) :
    i = j := by
  have key : ∀ {i j : Nat}, i ≤ j → j < p - 1 → g ^ i = g ^ j → i = j := by
    intro i j hij hj h
    have hji : j - i < p - 1 := Nat.lt_of_le_of_lt (Nat.sub_le j i) hj
    have e : g ^ j = g ^ i * g ^ (j - i) := by rw [← pow_add, FRC.Nat.add_sub_of_le hij]
    have hinv : g ^ i * g ^ (p - 1 - i) = 1 := by
      rw [← pow_add, FRC.Nat.add_sub_of_le (Nat.le_of_lt (Nat.lt_of_le_of_lt hij hj)), F.pow_n]
    have h1 : g ^ (j - i) = 1 := by
      calc g ^ (j - i) = 1 * g ^ (j - i) := (one_mul _).symm
        _ = g ^ (p - 1 - i) * g ^ i * g ^ (j - i) := by rw [mul_comm (g ^ (p - 1 - i)), hinv]
        _ = g ^ (p - 1 - i) * g ^ j := by rw [mul_assoc, ← e]
        _ = g ^ (p - 1 - i) * g ^ i := by rw [h]
        _ = 1 := by rw [mul_comm, hinv]
    have h2 := F.mod_eq_zero_of_pow_eq_one h1
    rw [FRC.Nat.mod_eq_of_lt hji] at h2
    have : j = i + (j - i) := (FRC.Nat.add_sub_of_le hij).symm
    rw [h2, Nat.add_zero] at this
    exact this.symm
  exact match Nat.lt_or_ge i j with
    | .inl hlt => key (Nat.le_of_lt hlt) hj h
    | .inr hge => (key hge hi h.symm).symm

theorem g_ne_zero (F : Frame p κ g) : g ≠ 0 := fun h0 => by
  have hn := F.pow_n
  have : p - 1 = (p - 2) + 1 := by
    have := F.one_lt_p
    match p, this with
    | k + 2, _ => rfl
  rw [this, pow_succ, h0, mul_zero] at hn
  exact F.one_ne_zero hn.symm

/-- No power of the drive is zero: `g^m · g^{(n−1)m} = g^{nm} = 1`. -/
theorem pow_ne_zero (F : Frame p κ g) (m : Nat) : g ^ m ≠ 0 := fun h0 => by
  have hn := F.n_pos
  have e : m + (p - 1 - 1) * m = (p - 1) * m := by
    calc m + (p - 1 - 1) * m = 1 * m + (p - 1 - 1) * m := by rw [Nat.one_mul]
      _ = (1 + (p - 1 - 1)) * m := (FRC.Nat.add_mul _ _ _).symm
      _ = (p - 1) * m := by rw [FRC.Nat.add_sub_of_le hn]
  have : g ^ m * g ^ ((p - 1 - 1) * m) = 1 := by
    rw [← pow_add, e, pow_mul, F.pow_n, one_pow]
  rw [h0, zero_mul] at this
  exact F.one_ne_zero this.symm

/-- The representatives of `g^0, …, g^{n−1}`, as a list (latest first). -/
def powList (g : Shell p) : Nat → List Nat
  | 0 => []
  | m + 1 => (g ^ m).val :: powList g m

theorem powList_length (g : Shell p) (n : Nat) : (powList g n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => show (powList g n).length + 1 = n + 1; rw [ih]

theorem mem_powList {g : Shell p} {v : Nat} : ∀ {n : Nat}, Pigeonhole.mem v (powList g n) → ∃ m, m < n ∧ (g ^ m).val = v
  | 0, h => absurd h id
  | n + 1, h => match h with
    | Or.inl e => ⟨n, Nat.lt_succ_self n, e.symm⟩
    | Or.inr h' => match mem_powList h' with
      | ⟨m, hm, e⟩ => ⟨m, Nat.lt_succ_of_lt hm, e⟩

theorem powList_nodup (F : Frame p κ g) : ∀ {n : Nat}, n ≤ p - 1 → Pigeonhole.NoDup (powList g n)
  | 0, _ => trivial
  | n + 1, hn => ⟨fun h => match mem_powList h with
      | ⟨m, hm, e⟩ =>
        have : m = n := F.pow_inj (Nat.lt_trans hm hn) hn (ext e)
        Nat.lt_irrefl n (this ▸ hm),
    powList_nodup F (Nat.le_of_lt hn)⟩

/-- 00:A8 — the drive generates: every nonzero residue is a power `g^m`, `m < p − 1` (the pigeonhole). -/
theorem generates (F : Frame p κ g) : Generates g (p - 1) := by
  intro v hv hv0
  have hb : ∀ e, Pigeonhole.mem e (powList g (p - 1)) → 1 ≤ e ∧ e ≤ p - 1 := fun e he =>
    match mem_powList he with
    | ⟨m, _, hm⟩ =>
      ⟨Nat.pos_of_ne_zero (fun h0 => F.pow_ne_zero m (ext (by rw [hm, h0]; rfl))),
       by rw [← hm]; exact Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (g ^ m).lt (Nat.le_of_eq (FRC.Nat.sub_add_cancel Pos.pos).symm))⟩
  exact mem_powList (Pigeonhole.mem_of_nodup_of_length (p - 1) (powList g (p - 1)) (F.powList_nodup (Nat.le_refl _))
    hb (powList_length g (p - 1)) v hv0 (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hv (Nat.le_of_eq (FRC.Nat.sub_add_cancel Pos.pos).symm))))

/-- Every nonzero residue is a power of the drive, on residues. -/
theorem eq_pow_of_ne_zero (F : Frame p κ g) {x : Shell p} (hx : x ≠ 0) :
    ∃ m, m < p - 1 ∧ g ^ m = x := by
  have hv : 0 < x.val := Nat.pos_of_ne_zero (fun h => hx (ext h))
  match F.generates x.val x.lt hv with
  | ⟨m, hm, e⟩ => exact ⟨m, hm, ext e⟩

theorem exists_inv (F : Frame p κ g) {x : Shell p} (hx : x ≠ 0) : ∃ y, x * y = 1 := by
  match F.eq_pow_of_ne_zero hx with
  | ⟨m, hm, e⟩ =>
    refine ⟨g ^ (p - 1 - m), ?_⟩
    rw [← e, ← pow_add, FRC.Nat.add_sub_of_le (Nat.le_of_lt hm), F.pow_n]

theorem mul_eq_zero (F : Frame p κ g) {a b : Shell p} (h : a * b = 0) : a = 0 ∨ b = 0 :=
  match Shell.instDecidableEq a 0 with
  | .isTrue ha => .inl ha
  | .isFalse ha => .inr (by
      match F.exists_inv ha with
      | ⟨y, hy⟩ =>
        calc b = 1 * b := (one_mul b).symm
          _ = y * a * b := by rw [mul_comm y a, hy]
          _ = y * (a * b) := mul_assoc _ _ _
          _ = 0 := by rw [h, mul_zero])

theorem mul_ne_zero (F : Frame p κ g) {a b : Shell p} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 :=
  fun h => match F.mul_eq_zero h with
    | .inl e => ha e
    | .inr e => hb e

/-- Cancellation: `a * b = a * c` with `a ≠ 0` gives `b = c`. -/
theorem mul_left_cancel (F : Frame p κ g) {a b c : Shell p} (ha : a ≠ 0) (h : a * b = a * c) : b = c := by
  have : a * (b + -c) = 0 := by rw [left_distrib, ← mul_neg, h, add_neg]
  match F.mul_eq_zero this with
  | .inl e => exact absurd e ha
  | .inr e =>
    calc b = b + 0 := (add_zero b).symm
      _ = b + (-c + c) := by rw [neg_add]
      _ = (b + -c) + c := (add_assoc _ _ _).symm
      _ = c := by rw [e, zero_add]

/-- The square roots of one are `±1`. -/
theorem sq_eq_one (F : Frame p κ g) {x : Shell p} (h : x * x = 1) : x = 1 ∨ x = -1 := by
  have e : (x + -1) * (x + 1) = 0 := by
    rw [right_distrib, left_distrib, left_distrib, h, mul_one, neg_one_mul, neg_one_mul]
    rw [add_assoc, ← add_assoc x (-x), add_neg, zero_add, add_neg]
  match F.mul_eq_zero e with
  | .inl e1 => exact .inl (by
      calc x = x + 0 := (add_zero x).symm
        _ = x + (-1 + 1) := by rw [neg_add]
        _ = (x + -1) + 1 := (add_assoc _ _ _).symm
        _ = 1 := by rw [e1, zero_add])
  | .inr e2 => exact .inr (eq_neg_of_add_eq_zero e2)

/-! ### The Euclidean datum (00:C1) -/

/-- The half-period `π = 2κ`. -/
def halfPeriod (κ : Nat) : Nat := 2 * κ

/-- The oriented quarter-turn `i = −g^κ` (00:C7). -/
def quarterTurn (g : Shell p) (κ : Nat) : Shell p := -(g ^ κ)

theorem two_kappa_lt (F : Frame p κ g) : 2 * κ < p - 1 := by
  rw [F.n_eq]; exact FRC.Nat.mul_lt_mul_of_lt_of_pos (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ 1))) F.cap_pos

theorem two_kappa_pos (F : Frame p κ g) : 0 < 2 * κ := Nat.mul_pos (Nat.zero_lt_succ 1) F.cap_pos

theorem four_kappa (F : Frame p κ g) : 2 * κ + 2 * κ = p - 1 := by
  rw [F.n_eq]
  show 2 * κ + 2 * κ = 2 * 2 * κ
  rw [FRC.Nat.mul_assoc, ← Nat.two_mul (2 * κ)]

/-- 2:D1, 00:C1 — the half-period: `g^{2κ} = −1` for the drive of every frame. -/
theorem half_period (F : Frame p κ g) : g ^ (2 * κ) = -1 := by
  have hsq : g ^ (2 * κ) * g ^ (2 * κ) = 1 := by rw [← pow_add, F.four_kappa, F.pow_n]
  match F.sq_eq_one hsq with
  | .inr e => exact e
  | .inl e => exact absurd e (F.prim.2 (2 * κ) F.two_kappa_lt F.two_kappa_pos)

/-- 1:B3, 2:D2 — the quarter-turn `i = −g^κ` squares to `−1`. -/
theorem quarter_turn_sq (F : Frame p κ g) : quarterTurn g κ * quarterTurn g κ = -1 := by
  unfold quarterTurn
  rw [neg_mul_neg, ← pow_add, ← Nat.two_mul, F.half_period]

/-- 2:D2 — `g^κ` has order four: `(g^κ)^2 = −1` and `(g^κ)^4 = 1`. -/
theorem quarter_turn_order (F : Frame p κ g) : (g ^ κ) ^ 2 = -1 ∧ (g ^ κ) ^ 4 = 1 := by
  have h2 : (g ^ κ) ^ 2 = -1 := by rw [← pow_mul, Nat.mul_comm, F.half_period]
  refine ⟨h2, ?_⟩
  show (g ^ κ) ^ (2 * 2) = 1
  rw [pow_mul, h2, neg_pow_two, one_pow]

/-- 2:D5, 6:B3 — the orientation classes: for `g' = g^u`, the quarter-turn `−g'^κ` is `−g^κ` when
`u ≡ 1 (mod 4)` and `−(−g^κ)` when `u ≡ 3 (mod 4)`. -/
theorem orientation_class (F : Frame p κ g) (u : Nat) :
    (u % 4 = 1 → -((g ^ u) ^ κ) = -(g ^ κ)) ∧ (u % 4 = 3 → -((g ^ u) ^ κ) = -(-(g ^ κ))) := by
  have h4 : (g ^ κ) ^ 4 = 1 := (F.quarter_turn_order).2
  have h2 : (g ^ κ) ^ 2 = -1 := (F.quarter_turn_order).1
  have key : (g ^ u) ^ κ = (g ^ κ) ^ u := pow_mul_comm g u κ
  have hu : (g ^ κ) ^ u = (g ^ κ) ^ (u % 4) := by
    match FRC.Nat.mod_spec 4 (Nat.zero_lt_succ 3) u with
    | ⟨q, hq⟩ =>
      calc (g ^ κ) ^ u = (g ^ κ) ^ (4 * q + u % 4) := by rw [← hq]
        _ = ((g ^ κ) ^ 4) ^ q * (g ^ κ) ^ (u % 4) := by rw [pow_add, pow_mul]
        _ = (g ^ κ) ^ (u % 4) := by rw [h4, one_pow, one_mul]
  constructor
  · intro h1; rw [key, hu, h1, pow_one]
  · intro h3
    rw [key, hu, h3]
    show -((g ^ κ) ^ (2 + 1)) = -(-(g ^ κ))
    rw [pow_add, h2, pow_one, neg_one_mul]

theorem sq_mod_two (i : Nat) : (i * i) % 2 = i % 2 := by
  rw [FRC.Nat.mul_mod i i 2 (Nat.zero_lt_succ 1)]
  have := Nat.mod_lt i (Nat.zero_lt_succ 1)
  match i % 2, this with
  | 0, _ => rfl
  | 1, _ => rfl
  | k + 2, hk => exact absurd hk (Nat.not_lt_of_le (Nat.le_add_left 2 k))

/-- 2:D6, 6:B2, 00:C14 — the Euler identity on the shell: with `e = g^i` and `π = 2κ`,
`(g^i)^{i·2κ} = (−1)^i` for every natural reading `i` of the quarter-turn — `−1` exactly when `i` is odd. -/
theorem euler_identity (F : Frame p κ g) (i : Nat) :
    (g ^ i) ^ (i * (2 * κ)) = if i % 2 = 0 then 1 else -1 := by
  have e1 : (g ^ i) ^ (i * (2 * κ)) = (g ^ (2 * κ)) ^ (i * i) := by
    rw [← pow_mul, ← pow_mul]
    show g ^ (i * (i * (2 * κ))) = g ^ (2 * κ * (i * i))
    rw [← FRC.Nat.mul_assoc, Nat.mul_comm (i * i)]
  rw [e1, F.half_period, neg_one_pow, sq_mod_two]

/-- 00:C1 — the web closes: `2π ≡ −1` on every shell (`4κ = p − 1`). -/
theorem two_pi (F : Frame p κ g) : (ofNat (2 * halfPeriod κ) : Shell p) = -1 := by
  apply ext
  rw [val_ofNat, val_neg, val_one, FRC.Nat.mod_eq_of_lt F.one_lt_p]
  unfold halfPeriod
  rw [← FRC.Nat.mul_assoc]
  show (4 * κ) % p = (p - 1) % p
  rw [F.n_eq]

/-! ### Two is invertible on every shell -/

theorem two_lt_p (F : Frame p κ g) : 2 < p := by
  rw [F.cap]
  have h : 4 * 1 ≤ 4 * κ := Nat.mul_le_mul_left 4 F.cap_pos
  exact Nat.lt_of_lt_of_le (by decide : 2 < 4 * 1 + 1) (Nat.succ_le_succ h)

theorem two_ne_zero (F : Frame p κ g) : (2 : Shell p) ≠ 0 := fun h => by
  have := val_injective h
  rw [val_lit, val_zero, FRC.Nat.mod_eq_of_lt F.two_lt_p] at this
  exact Nat.noConfusion this

theorem two_eq_one_add_one : (2 : Shell p) = 1 + 1 :=
  ext (by rw [val_add, val_one, val_lit, FRC.Nat.mod_add_mod _ _ _ hp, FRC.Nat.add_mod_mod _ _ _ hp])

theorem two_mul' (x : Shell p) : (2 : Shell p) * x = x + x := by
  rw [two_eq_one_add_one, right_distrib, one_mul]

theorem eq_zero_of_eq_neg (F : Frame p κ g) {x : Shell p} (h : x = -x) : x = 0 := by
  have h2 : (2 : Shell p) * x = 0 := by
    rw [two_mul']
    calc x + x = x + -x := by rw [← h]
      _ = 0 := add_neg x
  match F.mul_eq_zero h2 with
  | .inl e => exact absurd e F.two_ne_zero
  | .inr e => exact e

/-- 1:F1 (Theorem 3) — `2s = 0 ⇒ s = 0`: the additive cycle has no element of order two; the antipode of
the origin is not a residue. -/
theorem no_south_pole (F : Frame p κ g) (s : Shell p) (h : (2 : Shell p) * s = 0) : s = 0 :=
  match F.mul_eq_zero h with
  | .inl e => absurd e F.two_ne_zero
  | .inr e => e

end Frame
end Shell
end FRC
