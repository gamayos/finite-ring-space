import FrcCore.Shell
import FrcCore.Pigeonhole
import FrcCore.Series

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

Since the ledger migration (task LM17) it also holds the frame's arithmetic from 1-algebra (scale periodicity, the affine
frame, the window law and its read-backs, `ofNat_add`, `ofNat_mul`, the quarter-turn and the fourth roots, the meridian
involution, the complex chart, Theorem approx, `natCount`), `ofNat_self` and `ofNat_add_self` (from 13-epi), the root pair
(from 10-dimensions), the bounded quantifiers' deciders (from 10-dimensions and 20-rh; in `Series.lean` since task LM22)
and the counting lemmas of 20-rh, all under their old names in `FRC.Shell` and `FRC.Shell.Frame`.
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

instance instDecForallLT (P : Nat → Prop) [DecidablePred P] (n : Nat) : Decidable (∀ m, m < n → P m) :=
  decForallLT P n

/-- `∀ x : Shell p, P x`, decided through the representatives. -/
instance instDecForallShell {p : Nat} [Pos p] (P : Shell p → Prop) [DecidablePred P] :
    Decidable (∀ x, P x) :=
  match decForallLT (fun v => P (ofNat v)) p with
  | isTrue h => isTrue (fun x => ofNat_val x ▸ h x.val x.lt)
  | isFalse h => isFalse (fun hall => h (fun v _ => hall (ofNat v)))

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

/-- 2:D1, 13:H2, 00:C1 — the half-period: `g^{2κ} = −1` for the drive of every frame (the half-turn tautology
behind `χ(−1) = e^{iπ}`). -/
theorem half_period (F : Frame p κ g) : g ^ (2 * κ) = -1 := by
  have hsq : g ^ (2 * κ) * g ^ (2 * κ) = 1 := by rw [← pow_add, F.four_kappa, F.pow_n]
  match F.sq_eq_one hsq with
  | .inr e => exact e
  | .inl e => exact absurd e (F.prim.2 (2 * κ) F.two_kappa_lt F.two_kappa_pos)

/-- 1:B3, 2:D2, 13:J2 — the quarter-turn `i = −g^κ` squares to `−1` (the pinning relation `i² + 1 ≡ 0`). -/
theorem quarter_turn_sq (F : Frame p κ g) : quarterTurn g κ * quarterTurn g κ = -1 := by
  unfold quarterTurn
  rw [neg_mul_neg, ← pow_add, ← Nat.two_mul, F.half_period]

/-- 2:D2 — `g^κ` has order four: `(g^κ)^2 = −1` and `(g^κ)^4 = 1`. -/
theorem quarter_turn_order (F : Frame p κ g) : (g ^ κ) ^ 2 = -1 ∧ (g ^ κ) ^ 4 = 1 := by
  have h2 : (g ^ κ) ^ 2 = -1 := by rw [← pow_mul, Nat.mul_comm, F.half_period]
  refine ⟨h2, ?_⟩
  show (g ^ κ) ^ (2 * 2) = 1
  rw [pow_mul, h2, neg_pow_two, one_pow]

/-- 2:D5, 6:B3, 13:B2 — the orientation classes: for `g' = g^u`, the quarter-turn `−g'^κ` is `−g^κ` when
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

/-- 00:C1, 13:J2, 13:I4 — the web closes: `2π ≡ −1` on every shell (`4κ = p − 1`): the height-two pinning
`2π_A + 1 ≡ 0`, which holds in every fibre of a composite lift. -/
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

/-- 1:Z1 (Theorem 3) — `2s = 0 ⇒ s = 0`: the additive cycle has no element of order two; the antipode of
the origin is not a residue. -/
theorem no_south_pole (F : Frame p κ g) (s : Shell p) (h : (2 : Shell p) * s = 0) : s = 0 :=
  match F.mul_eq_zero h with
  | .inl e => absurd e F.two_ne_zero
  | .inr e => e

/-! ## The frame's arithmetic (moved from 1-algebra by the ledger migration, task LM17) -/

/-- 1:D4 (Lemma 2 of 1-algebra, scale periodicity) — the residue grid repeats with the period `p − 1`
of the drive: `g^{n + (p−1)} = g^n`, hence `x·g^{n + (p−1)} = x·g^n` for every `x`. -/
theorem scale_periodic (F : Frame p κ g) (x : Shell p) (n : Nat) :
    x * g ^ (n + (p - 1)) = x * g ^ n := by
  rw [pow_add, F.pow_n, mul_one]

/-- The affine frame `(a, b)` of 1-algebra (Definition 2): the transported product
`x ⊗ z := a + b·((x − a)/b)·((z − a)/b)`, written with `y` the inverse of `b`. -/
def affineMul (a b y x z : Shell p) : Shell p := a + b * ((x + -a) * y) * ((z + -a) * y)

/-- 1:B4 (Definition 2 of 1-algebra) — in the affine frame `(a, b)` the multiplicative unit
is `a + b`, not `b`: `(a + b) ⊗ z = z` for every `z`. -/
theorem affine_frame_unit {a b y : Shell p} (hby : b * y = 1) (z : Shell p) :
    affineMul a b y (a + b) z = z := by
  unfold affineMul
  have e1 : a + b + -a = b := by rw [add_comm a b, add_assoc, add_neg, add_zero]
  rw [e1, hby, mul_one, mul_left_comm b, hby, mul_one, add_comm z (-a), ← add_assoc, add_neg, zero_add]

/-- 1:D2 (the window law, injectivity) — two window integers `x, y ≤ H` with `2H < p` that read as the same
residue are equal: `ofNat x = ofNat y → x = y`. (Both are below `p`, so the residues are the integers.) -/
theorem window_injective {H x y : Nat} (hH : 2 * H < p) (hx : x ≤ H) (hy : y ≤ H)
    (h : (ofNat x : Shell p) = ofNat y) : x = y := by
  have hxp : x < p := Nat.lt_of_le_of_lt hx (Nat.lt_of_le_of_lt (Nat.le_add_left H H) (Nat.two_mul H ▸ hH))
  have hyp : y < p := Nat.lt_of_le_of_lt hy (Nat.lt_of_le_of_lt (Nat.le_add_left H H) (Nat.two_mul H ▸ hH))
  have := val_injective h
  rw [val_ofNat, val_ofNat, FRC.Nat.mod_eq_of_lt hxp, FRC.Nat.mod_eq_of_lt hyp] at this
  exact this

theorem ofNat_add (x y : Nat) : (ofNat x : Shell p) + ofNat y = ofNat (x + y) :=
  ext (by rw [val_add, val_ofNat, val_ofNat, val_ofNat, FRC.Nat.mod_add_mod _ _ _ hp, FRC.Nat.add_mod_mod _ _ _ hp])

theorem ofNat_mul (x y : Nat) : (ofNat x : Shell p) * ofNat y = ofNat (x * y) :=
  ext (by rw [val_mul, val_ofNat, val_ofNat, val_ofNat, FRC.Nat.mod_mul_mod _ _ _ hp, FRC.Nat.mul_mod_mod _ _ _ hp])

/-- `p ≡ 0` on the shell. -/
theorem ofNat_self : (ofNat p : Shell p) = 0 := by
  apply ext; show p % p = 0; exact FRC.Nat.mod_self p Pos.pos

theorem ofNat_add_self (n : Nat) : (ofNat (n + p) : Shell p) = ofNat n := by
  rw [← ofNat_add, ofNat_self, add_zero]

/-- 1:D2, the read-back of sums: for `x, y ≤ H` and `4H < p`, the residue of `x + y` determines the integer
`x + y` among the integers `z ≤ 2H`. -/
theorem window_add_readback {H x y z : Nat} (hH : 2 * (2 * H) < p) (hx : x ≤ H) (hy : y ≤ H) (hz : z ≤ 2 * H)
    (h : (ofNat x : Shell p) + ofNat y = ofNat z) : x + y = z := by
  rw [ofNat_add] at h
  exact window_injective hH (by rw [Nat.two_mul]; exact Nat.add_le_add hx hy) hz h

/-- 1:D2, the read-back of products: for `x, y ≤ H` and `2H² < p`, the residue of `x·y` determines the integer
`x·y` among the integers `z ≤ H²`. -/
theorem window_mul_readback {H x y z : Nat} (hH : 2 * (H * H) < p) (hx : x ≤ H) (hy : y ≤ H) (hz : z ≤ H * H)
    (h : (ofNat x : Shell p) * ofNat y = ofNat z) : x * y = z := by
  rw [ofNat_mul] at h
  exact window_injective hH (Nat.mul_le_mul hx hy) hz h

/-- 1:D2, the signed window: `x` and `−y` (`x, y ≤ H`, `2H < p`) read as the same residue only when both
are zero — the window's positive and negative halves do not overlap. -/
theorem window_signed {H x y : Nat} (hH : 2 * H < p) (hx : x ≤ H) (hy : y ≤ H)
    (h : (ofNat x : Shell p) = -(ofNat y)) : x = 0 ∧ y = 0 := by
  have hxp : x < p := Nat.lt_of_le_of_lt hx (Nat.lt_of_le_of_lt (Nat.le_add_left H H) (Nat.two_mul H ▸ hH))
  have hyp : y < p := Nat.lt_of_le_of_lt hy (Nat.lt_of_le_of_lt (Nat.le_add_left H H) (Nat.two_mul H ▸ hH))
  have hv := val_injective h
  rw [val_ofNat, val_neg, val_ofNat, FRC.Nat.mod_eq_of_lt hxp, FRC.Nat.mod_eq_of_lt hyp] at hv
  -- hv : x = (p - y) % p
  match Nat.decEq y 0 with
  | .isTrue hy0 =>
    rw [hy0, Nat.sub_zero, FRC.Nat.mod_self p hp] at hv
    exact ⟨hv, hy0⟩
  | .isFalse hy0 =>
    have hpy : p - y < p := Nat.sub_lt hp (Nat.pos_of_ne_zero hy0)
    rw [FRC.Nat.mod_eq_of_lt hpy] at hv
    -- x = p − y with x ≤ H, y ≤ H gives p = x + y ≤ 2H < p
    have : p = x + y := by rw [hv, FRC.Nat.sub_add_cancel (Nat.le_of_lt hyp)]
    have hle : x + y ≤ 2 * H := by rw [Nat.two_mul]; exact Nat.add_le_add hx hy
    exact absurd (Nat.lt_of_le_of_lt (this ▸ hle) hH) (Nat.lt_irrefl p)

/-- 1:B2 (Theorem 1, existence clause) — a quarter-turn `u` with `u² = −1` exists on every shell. -/
theorem quarter_turn_exists (F : Frame p κ g) : ∃ u : Shell p, u * u = -1 :=
  ⟨quarterTurn g κ, F.quarter_turn_sq⟩

/-- 1:B2 (Theorem 1, the structural set) — the fourth roots of unity are exactly `1, −1, i, −i`. -/
theorem fourth_roots (F : Frame p κ g) (x : Shell p) :
    x ^ 4 = 1 ↔ x = 1 ∨ x = -1 ∨ x = quarterTurn g κ ∨ x = -(quarterTurn g κ) := by
  have h4 : x ^ 4 = (x * x) * (x * x) := by
    rw [show (4 : Nat) = 2 * 2 from rfl, pow_mul, pow_two, pow_two]
  have hi := F.quarter_turn_sq
  constructor
  · intro h
    rw [h4] at h
    match F.sq_eq_one h with
    | .inl e => match F.sq_eq_one e with
      | .inl e1 => exact .inl e1
      | .inr e1 => exact .inr (.inl e1)
    | .inr e =>
      -- x² = −1 = i²: (x + −i)(x + i) = 0
      have e2 : (x + -(quarterTurn g κ)) * (x + quarterTurn g κ) = 0 := by
        rw [right_distrib, left_distrib, left_distrib, e, ← neg_mul, ← neg_mul, hi, neg_neg, mul_comm (quarterTurn g κ) x]
        rw [add_assoc, ← add_assoc (x * quarterTurn g κ), add_neg, zero_add, neg_add]
      match F.mul_eq_zero e2 with
      | .inl e3 => exact .inr (.inr (.inl (by
          calc x = x + 0 := (add_zero x).symm
            _ = x + (-(quarterTurn g κ) + quarterTurn g κ) := by rw [neg_add]
            _ = (x + -(quarterTurn g κ)) + quarterTurn g κ := (add_assoc _ _ _).symm
            _ = quarterTurn g κ := by rw [e3, zero_add])))
      | .inr e3 => exact .inr (.inr (.inr (eq_neg_of_add_eq_zero e3)))
  · intro h
    match h with
    | .inl e => rw [e, one_pow]
    | .inr (.inl e) => rw [h4, e, neg_mul_neg, one_mul, one_mul]
    | .inr (.inr (.inl e)) => rw [h4, e, hi, neg_mul_neg, one_mul]
    | .inr (.inr (.inr e)) => rw [h4, e, neg_mul_neg, hi, neg_mul_neg, one_mul]

/-- 1:C4 (Definition 5 (a)) — the meridian involution: `(−a)·g^{n + 2κ} = a·g^n`. -/
theorem meridian_involution (F : Frame p κ g) (a : Shell p) (n : Nat) :
    -a * g ^ (n + 2 * κ) = a * g ^ n := by
  rw [pow_add, F.half_period, mul_comm (g ^ n), ← mul_assoc, neg_mul_neg, mul_one]

/-- The complex chart: pairs `(a, b)` read as `a + b·X` with `X² = −1`, multiplied as
`(a, b)(c, d) = (ac − bd, ad + bc)`. -/
def cmul (x y : Shell p × Shell p) : Shell p × Shell p :=
  (x.1 * y.1 + -(x.2 * y.2), x.1 * y.2 + x.2 * y.1)

/-- 1:E2 (Proposition 5 reversed) — on a shell that already has a square root of `−1` the complex chart is
not a field: `(i, 1)·(−i, 1) = (0, 0)` with both factors nonzero (`X + i` and `X − i` are zero divisors). -/
theorem complex_chart_zero_divisor (F : Frame p κ g) :
    cmul (quarterTurn g κ, (1 : Shell p)) (-(quarterTurn g κ), 1) = (0, 0) ∧
    (quarterTurn g κ, (1 : Shell p)) ≠ (0, 0) ∧ (-(quarterTurn g κ), (1 : Shell p)) ≠ (0, 0) := by
  refine ⟨?_, fun h => F.one_ne_zero (congrArg Prod.snd h), fun h => F.one_ne_zero (congrArg Prod.snd h)⟩
  unfold cmul
  show (quarterTurn g κ * -(quarterTurn g κ) + -(1 * 1), quarterTurn g κ * 1 + 1 * -(quarterTurn g κ)) = (0, 0)
  rw [← mul_neg, F.quarter_turn_sq, neg_neg, one_mul, add_neg, mul_one, one_mul, add_neg]

/-- 1:D6 (Theorem approx, the range at `p = 13`, `g = 2`): every grid point
`x / 2^n` with `x < 13` and `n ≥ 3` is at most `3/2` — as the integer statement `2x ≤ 3·2^n`. -/
theorem approx_obstruction (n x : Nat) (hn : 3 ≤ n) (hx : x < 13) : 2 * x ≤ 3 * 2 ^ n := by
  have h8 : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (Nat.zero_lt_succ 1) hn
  have h1 : 2 * x ≤ 2 * 12 := Nat.mul_le_mul_left 2 (Nat.le_of_lt_succ hx)
  have h2 : 3 * 2 ^ 3 ≤ 3 * 2 ^ n := Nat.mul_le_mul_left 3 h8
  exact Nat.le_trans h1 h2

/-- The number of `x < n` with `P x`, as a sum of `0`s and `1`s. -/
def natCount (P : Nat → Prop) [DecidablePred P] : Nat → Nat
  | 0 => 0
  | n + 1 => natCount P n + if P n then 1 else 0

theorem natCount_ne_zero (n : Nat) : natCount (fun x => x ≠ 0) (n + 1) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show natCount (fun x => x ≠ 0) (n + 1) + (if n + 1 ≠ 0 then 1 else 0) = n + 1
    rw [ih, ite_eq_left (Nat.succ_ne_zero n)]

/-- 10:E4, 10:P2 — the root pair: if `x² = a` with `x ≠ 0` then `y² = a` iff `y = x` or `y = −x`, and `−x ≠ x`;
each quadratic defining congruence has exactly two roots on a framed Carrier. -/
theorem root_pair (F : Frame p κ g) (a x : Shell p) (hx : x * x = a) (hx0 : x ≠ 0) :
    (∀ y : Shell p, y * y = a ↔ (y = x ∨ y = -x)) ∧ -x ≠ x := by
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

/-- Counting where nothing satisfies the predicate. -/
theorem natCount_eq_zero (P : Nat → Prop) [DecidablePred P] : ∀ n, (∀ x, x < n → ¬ P x) → natCount P n = 0
  | 0, _ => rfl
  | n + 1, h => by
    show natCount P n + (if P n then 1 else 0) = 0
    rw [natCount_eq_zero P n (fun x hx => h x (Nat.lt_succ_of_lt hx)), ite_eq_right (h n (Nat.lt_succ_self n))]

/-- Counting through an equivalent predicate. -/
theorem natCount_congr (P Q : Nat → Prop) [DecidablePred P] [DecidablePred Q] :
    ∀ n, (∀ x, x < n → (P x ↔ Q x)) → natCount P n = natCount Q n
  | 0, _ => rfl
  | n + 1, h => by
    show natCount P n + (if P n then 1 else 0) = natCount Q n + (if Q n then 1 else 0)
    rw [natCount_congr P Q n (fun x hx => h x (Nat.lt_succ_of_lt hx))]
    have e := h n (Nat.lt_succ_self n)
    match (inferInstance : Decidable (Q n)) with
    | isTrue hq => rw [ite_eq_left hq, ite_eq_left (e.2 hq)]
    | isFalse hq => rw [ite_eq_right hq, ite_eq_right (fun hp => hq (e.1 hp))]

end Frame
end Shell
end FRC
