import FrcCore.Theme.Field
import FrcCore.Theme.Logic

/-!
# FrcCore.Theme.Quantum — the quantum theme: the unequal-cycle composite (ledger migration, task LM28)

The master's block F where its rows are exact. A composite of `m` parts, part `j` of registration period `n j > 0`,
driven jointly one step per chronon (00:F2, 22:C26, 37-sim's composite gate):

* the joint recurrence: the chronons at which every part returns are exactly the multiples of one period `T > 0`, the
  least common multiple of the parts' periods (`joint_recurrence`, `joint_least`);
* each pair's conserved offset lives on the gcd cycle: for two parts of periods `a`, `b` with joint period `T`, the
  number `g` with `g T = a b` divides both, and two joint states lie on one orbit of the drive exactly when their
  offsets agree modulo `g` (`pair_offset`): the orbits are the quotient `A/⟨v⟩ ≅ ℤ/g`;
* dephasing over the product period is exact: on every prime shell, a character of the composite that the drive moves
  (`Π ζ_j ≠ 1`) sums to zero over every joint recurrence, the product of the periods among them (`dephasing`).

No axioms.
-/

namespace FRC.Quantum

open FRC.Shell

/-! ## Arithmetic of remainders -/

theorem mod_zero_of_eq_mul {t a q : Nat} (ha : 0 < a) (h : t = a * q) : t % a = 0 :=
  FRC.Nat.mod_unique ha (by rw [h, Nat.add_zero])

theorem eq_mul_of_mod_zero {t a : Nat} (ha : 0 < a) (h : t % a = 0) : ∃ q, t = a * q :=
  match FRC.Nat.mod_spec a ha t with
  | ⟨q, hq⟩ => ⟨q, by rw [hq, h, Nat.add_zero]⟩

theorem mul_mod_zero {t a : Nat} (ha : 0 < a) (h : t % a = 0) (k : Nat) : (t * k) % a = 0 :=
  match eq_mul_of_mod_zero ha h with
  | ⟨q, hq⟩ => mod_zero_of_eq_mul ha (by rw [hq, FRC.Nat.mul_assoc])

/-- A summand that keeps the remainder is a multiple: `(u + v) % b = u % b → v % b = 0`. -/
theorem mod_of_add_mod {u v b : Nat} (hb : 0 < b) (h : (u + v) % b = u % b) : v % b = 0 := by
  have hr := Nat.mod_lt u hb
  have hs := Nat.mod_lt v hb
  rw [FRC.Nat.add_mod u v b hb] at h
  match Nat.lt_or_ge (u % b + v % b) b with
  | .inl hlt =>
    rw [FRC.Nat.mod_eq_of_lt hlt] at h
    exact FRC.Nat.add_left_cancel (h.trans (Nat.add_zero _).symm)
  | .inr hge =>
    rw [FRC.Nat.mod_eq_sub_mod hb hge, FRC.Nat.mod_eq_of_lt (FRC.Nat.sub_lt_of_lt_add (Nat.add_lt_add hr hs) hge)] at h
    have e : u % b + v % b = u % b + b := by
      calc u % b + v % b = (u % b + v % b - b) + b := (FRC.Nat.sub_add_cancel hge).symm
        _ = u % b + b := by rw [h]
    exact absurd hs (by rw [FRC.Nat.add_left_cancel e]; exact Nat.lt_irrefl b)

/-- Remainders modulo a divisor: `g ∣ a` gives `(n % a) % g = n % g`. -/
theorem mod_mod_of_dvd {n a g : Nat} (hg : 0 < g) (ha : 0 < a) (h : a % g = 0) : n % a % g = n % g := by
  match FRC.Nat.mod_spec a ha n, eq_mul_of_mod_zero hg h with
  | ⟨q, hq⟩, ⟨u, hu⟩ =>
    calc n % a % g = (g * (u * q) + n % a) % g := (FRC.Nat.add_mul_mod_self_left _ _ _ hg).symm
      _ = n % g := by rw [← FRC.Nat.mul_assoc, ← hu, ← hq]

/-- Cancelling a common summand under a remainder. -/
theorem mod_add_left_cancel {x u v g : Nat} (hg : 0 < g) (h : (x + u) % g = (x + v) % g) : u % g = v % g := by
  have e1 : (x + u) % g = (x % g + u % g) % g := FRC.Nat.add_mod _ _ _ hg
  have e2 : (x + v) % g = (x % g + v % g) % g := FRC.Nat.add_mod _ _ _ hg
  have key : ∀ w, ((g - x % g) + (x + w)) % g = w % g := fun w => by
    have hx := Nat.mod_lt x hg
    match FRC.Nat.mod_spec g hg x with
    | ⟨q, hq⟩ =>
      calc ((g - x % g) + (x + w)) % g = (g * (q + 1) + w) % g := by
            congr 1
            calc (g - x % g) + (x + w) = (g - x % g) + (g * q + x % g + w) := by rw [← hq]
              _ = g * q + ((g - x % g) + x % g) + w := by
                rw [← Nat.add_assoc, Nat.add_comm (g - x % g) (g * q + x % g), Nat.add_assoc (g * q),
                  Nat.add_comm (x % g) (g - x % g), ← Nat.add_assoc (g * q)]
              _ = g * (q + 1) + w := by rw [FRC.Nat.sub_add_cancel (Nat.le_of_lt hx), Nat.mul_succ]
        _ = w % g := FRC.Nat.add_mul_mod_self_left _ _ _ hg
  rw [← key u, ← key v, FRC.Nat.add_mod (g - x % g) (x + u) g hg, FRC.Nat.add_mod (g - x % g) (x + v) g hg, h]

theorem lt_of_mul_lt_mul {g a b : Nat} (h : g * a < g * b) : a < b :=
  match Nat.lt_or_ge a b with
  | .inl hlt => hlt
  | .inr hge => absurd (Nat.lt_of_lt_of_le h (Nat.mul_le_mul_left g hge)) (Nat.lt_irrefl _)

theorem sub_pos {a b : Nat} (h : a < b) : 0 < b - a :=
  Nat.pos_of_ne_zero (fun e => by
    have := FRC.Nat.sub_add_cancel (Nat.le_of_lt h)
    rw [e, Nat.zero_add] at this
    exact Nat.lt_irrefl a (this ▸ h))

/-! ## The joint recurrence (00:F2) -/

/-- All `m` parts, of periods `n j`, are back at chronon `t`. -/
def Joint (n : Nat → Nat) (m t : Nat) : Prop := ∀ j, j < m → t % n j = 0

instance (n : Nat → Nat) (m t : Nat) : Decidable (Joint n m t) := FRC.Shell.decForallLT _ m

/-- The product of the periods. -/
def prodN (n : Nat → Nat) : Nat → Nat
  | 0 => 1
  | m + 1 => prodN n m * n m

theorem prodN_pos (n : Nat → Nat) (hn : ∀ j, 0 < n j) : ∀ m, 0 < prodN n m
  | 0 => Nat.zero_lt_succ 0
  | m + 1 => Nat.mul_pos (prodN_pos n hn m) (hn m)

theorem prodN_joint (n : Nat → Nat) (hn : ∀ j, 0 < n j) : ∀ m, Joint n m (prodN n m)
  | 0 => fun _ h => absurd h (Nat.not_lt_zero _)
  | m + 1 => fun j hj => match Nat.lt_or_ge j m with
    | .inl hlt => by
      show (prodN n m * n m) % n j = 0
      exact mul_mod_zero (hn j) (prodN_joint n hn m j hlt) _
    | .inr hge => by
      have e : j = m := Nat.le_antisymm (Nat.le_of_lt_succ hj) hge
      rw [e]
      exact mod_zero_of_eq_mul (hn m) (Nat.mul_comm _ _)

/-- 00:F2, 22:C26 — the joint recurrence of an unequal-cycle composite, found below a common multiple `L > 0` of the
periods (on a shell, a joint return below `Ω`): the chronons at which all `m` parts return are exactly the multiples of
one period `T`, `0 < T ≤ L`, which divides `L`. The search never passes `L` (Q20). -/
theorem joint_recurrence (n : Nat → Nat) (hn : ∀ j, 0 < n j) (m L : Nat) (hL : 0 < L) (hLj : Joint n m L) :
    ∃ T, T ≤ L ∧ 0 < T ∧ Joint n m T ∧ (∀ t, Joint n m t ↔ t % T = 0) ∧ L % T = 0 := by
  let P : Nat → Bool := fun t => decide (0 < t ∧ Joint n m t)
  have hP : P L = true := decide_eq_true ⟨hL, hLj⟩
  match FRC.Logic.leastBelow_some P (L + 1) L (Nat.lt_succ_self _) hP with
  | ⟨T, hT⟩ =>
    have hs := FRC.Logic.leastBelow_spec P _ T hT
    have hT' : 0 < T ∧ Joint n m T := of_decide_eq_true hs.2.1
    have hiff : ∀ t, Joint n m t ↔ t % T = 0 := fun t => by
      constructor
      · intro ht
        match FRC.Nat.mod_spec T hT'.1 t with
        | ⟨q, hq⟩ =>
          have hr : Joint n m (t % T) := fun j hj => by
            have h1 : (T * q + t % T) % n j = (T * q) % n j := by
              rw [← hq, ht j hj]
              exact (mul_mod_zero (hn j) (hT'.2 j hj) q).symm
            exact mod_of_add_mod (hn j) h1
          exact match Nat.decEq (t % T) 0 with
            | isTrue e => e
            | isFalse e =>
              have ht' : P (t % T) = true := decide_eq_true ⟨Nat.pos_of_ne_zero e, hr⟩
              Bool.noConfusion (ht'.symm.trans (hs.2.2 (t % T) (Nat.mod_lt t hT'.1)))
      · intro ht j hj
        match eq_mul_of_mod_zero hT'.1 ht with
        | ⟨q, hq⟩ => rw [hq]; exact mul_mod_zero (hn j) (hT'.2 j hj) q
    exact ⟨T, Nat.le_of_lt_succ hs.1, hT'.1, hT'.2, hiff, (hiff _).1 hLj⟩

/-- The joint period is the least common multiple: no positive joint return comes earlier. -/
theorem joint_least {n : Nat → Nat} {m T : Nat} (hiff : ∀ t, Joint n m t ↔ t % T = 0) (hT : 0 < T) :
    ∀ t, 0 < t → Joint n m t → T ≤ t := fun t ht hj =>
  match eq_mul_of_mod_zero hT ((hiff t).1 hj) with
  | ⟨q, hq⟩ => by
    rw [hq]
    match q with
    | 0 => rw [Nat.mul_zero] at hq; exact absurd (hq ▸ ht) (Nat.lt_irrefl 0)
    | q + 1 => rw [Nat.mul_succ]; exact Nat.le_add_left T _

/-! ## The conserved offset on the gcd cycle (00:F2) -/

/-- The last `j < N` with `g j = w` (the index of a multiple of `g`). -/
def mulIdx (g w : Nat) : Nat → Nat
  | 0 => 0
  | N + 1 => if g * N = w then N else mulIdx g w N

theorem mulIdx_spec (g w j₀ : Nat) (h : g * j₀ = w) : ∀ N, j₀ < N → g * mulIdx g w N = w ∧ mulIdx g w N < N
  | 0, hj => absurd hj (Nat.not_lt_zero _)
  | N + 1, hj => by
    show g * (if g * N = w then N else mulIdx g w N) = w ∧ (if g * N = w then N else mulIdx g w N) < N + 1
    match (inferInstance : Decidable (g * N = w)) with
    | isTrue e => rw [ite_eq_left e]; exact ⟨e, Nat.lt_succ_self N⟩
    | isFalse e =>
      rw [ite_eq_right e]
      have hlt : j₀ < N := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hj) (fun e' => e (e' ▸ h))
      have ih := mulIdx_spec g w j₀ h N hlt
      exact ⟨ih.1, Nat.lt_succ_of_lt ih.2⟩

/-- 00:F2, 22:C26 — two parts of periods `a`, `b` with joint period `T` (a common multiple, and no positive common
multiple below it): the number `g` with `g T = a b` divides both periods, and every common divisor divides it (`g` is
the gcd); the joint drive carries `(x, y)` to `(x', y')` within one joint period exactly when the offsets agree modulo
`g` — the conserved offset on the gcd cycle, the orbits the quotient `A/⟨v⟩ ≅ ℤ/g`. -/
theorem pair_offset {a b T : Nat} (ha : 0 < a) (hb : 0 < b) (hT : 0 < T) (hTa : T % a = 0) (hTb : T % b = 0)
    (hleast : ∀ t, 0 < t → t < T → ¬ (t % a = 0 ∧ t % b = 0)) :
    ∃ g, g ≤ a ∧ 0 < g ∧ g * T = a * b ∧ a % g = 0 ∧ b % g = 0 ∧ (∀ e, 0 < e → a % e = 0 → b % e = 0 → g % e = 0) ∧
      ∀ x y x' y', x < a → y < b → x' < a → y' < b →
        ((∃ t, t < T ∧ (x + t) % a = x' ∧ (y + t) % b = y') ↔ (x + y') % g = (x' + y) % g) := by
  -- every common multiple is a multiple of `T`
  have hcm : ∀ t, t % a = 0 → t % b = 0 → t % T = 0 := fun t hta htb => by
    obtain ⟨q, hq⟩ := FRC.Nat.mod_spec T hT t
    have hr : ∀ c, 0 < c → T % c = 0 → t % c = 0 → (t % T) % c = 0 := fun c hc hTc htc =>
      mod_of_add_mod hc (by rw [← hq, htc]; exact (mul_mod_zero hc hTc q).symm)
    match Nat.decEq (t % T) 0 with
    | isTrue e => exact e
    | isFalse e => exact absurd ⟨hr a ha hTa hta, hr b hb hTb htb⟩ (hleast _ (Nat.pos_of_ne_zero e) (Nat.mod_lt t hT))
  obtain ⟨ua, hua⟩ := eq_mul_of_mod_zero ha hTa
  obtain ⟨ub, hub⟩ := eq_mul_of_mod_zero hb hTb
  have hab : (a * b) % T = 0 := hcm (a * b) (mod_zero_of_eq_mul ha rfl) (mod_zero_of_eq_mul hb (Nat.mul_comm a b))
  obtain ⟨g, hg⟩ := eq_mul_of_mod_zero hT hab
  have hgT : g * T = a * b := by rw [Nat.mul_comm, ← hg]
  have hg0 : 0 < g := Nat.pos_of_ne_zero (fun e => by
    rw [e, Nat.mul_zero] at hg; exact Nat.ne_of_gt (Nat.mul_pos ha hb) hg)
  -- `g ua = b` and `g ub = a`
  have hgb : b = g * ua := Nat.eq_of_mul_eq_mul_left ha (by
    calc a * b = g * T := hgT.symm
      _ = a * (g * ua) := by rw [hua, Nat.mul_left_comm])
  have hga : a = g * ub := Nat.eq_of_mul_eq_mul_left hb (by
    calc b * a = g * T := by rw [Nat.mul_comm, hgT]
      _ = b * (g * ub) := by rw [hub, Nat.mul_left_comm])
  have hag : a % g = 0 := mod_zero_of_eq_mul hg0 hga
  have hbg : b % g = 0 := mod_zero_of_eq_mul hg0 hgb
  have hgle : g ≤ a := by
    match ub, hga with
    | 0, e => rw [Nat.mul_zero] at e; rw [e] at ha; exact absurd ha (Nat.lt_irrefl 0)
    | u + 1, e => rw [e, Nat.mul_succ]; exact Nat.le_add_left g (g * u)
  -- `g` is the greatest common divisor: a common divisor `e` gives the common multiple `e a' b'`
  have hgcd : ∀ e, 0 < e → a % e = 0 → b % e = 0 → g % e = 0 := fun e he hae hbe => by
    obtain ⟨a', ha'⟩ := eq_mul_of_mod_zero he hae
    obtain ⟨b', hb'⟩ := eq_mul_of_mod_zero he hbe
    have hMa : (e * a' * b') % a = 0 := mod_zero_of_eq_mul ha (by rw [ha'])
    have hMb : (e * a' * b') % b = 0 :=
      mod_zero_of_eq_mul hb (by rw [hb', FRC.Nat.mul_assoc, Nat.mul_comm a' b', ← FRC.Nat.mul_assoc])
    obtain ⟨c, hc⟩ := eq_mul_of_mod_zero hT (hcm _ hMa hMb)
    have e1 : g * T = (e * c) * T :=
      calc g * T = a * b := hgT
        _ = e * (e * a' * b') := by
          rw [ha', hb', FRC.Nat.mul_assoc e a' (e * b'), FRC.Nat.mul_left_comm a' e b', FRC.Nat.mul_assoc e a' b']
        _ = e * (T * c) := by rw [hc]
        _ = (e * c) * T := by rw [Nat.mul_comm T c, ← FRC.Nat.mul_assoc]
    exact mod_zero_of_eq_mul he (Nat.eq_of_mul_eq_mul_right hT e1)
  refine ⟨g, hgle, hg0, hgT, hag, hbg, hgcd, fun x y x' y' hx hy hx' hy' => ⟨?_, ?_⟩⟩
  · -- the offset is conserved
    rintro ⟨t, _, ht1, ht2⟩
    calc (x + y') % g = (x + (y + t) % b) % g := by rw [ht2]
      _ = (x + (y + t) % b % g) % g := (FRC.Nat.add_mod_mod _ _ _ hg0).symm
      _ = (x + (y + t)) % g := by rw [mod_mod_of_dvd hg0 hb hbg, FRC.Nat.add_mod_mod _ _ _ hg0]
      _ = ((x + t) + y) % g := by rw [← Nat.add_assoc, Nat.add_right_comm]
      _ = ((x + t) % a % g + y) % g := by rw [mod_mod_of_dvd hg0 ha hag, FRC.Nat.mod_add_mod _ _ _ hg0]
      _ = (x' + y) % g := by rw [FRC.Nat.mod_add_mod _ _ _ hg0, ht1]
  · -- the offset is complete: the pigeonhole over one cycle of the second part
    intro hoff
    let d := (x' + (a - x)) % a
    have hxd : (x + d) % a = x' := by
      show (x + (x' + (a - x)) % a) % a = x'
      rw [FRC.Nat.add_mod_mod _ _ _ ha]
      calc (x + (x' + (a - x))) % a = (a * 1 + x') % a := by
            congr 1
            rw [Nat.add_left_comm, FRC.Nat.add_sub_of_le (Nat.le_of_lt hx), Nat.mul_one, Nat.add_comm]
        _ = x' := by rw [FRC.Nat.add_mul_mod_self_left _ _ _ ha, FRC.Nat.mod_eq_of_lt hx']
    -- `y' ≡ y + d (mod g)`
    have hyd : y' % g = (y + d) % g := by
      have h1 : (x + y') % g = (x + (d + y)) % g := by
        calc (x + y') % g = (x' + y) % g := hoff
          _ = ((x + d) % a % g + y) % g := by rw [hxd, FRC.Nat.mod_add_mod _ _ _ hg0]
          _ = (x + (d + y)) % g := by rw [mod_mod_of_dvd hg0 ha hag, FRC.Nat.mod_add_mod _ _ _ hg0, Nat.add_assoc]
      rw [mod_add_left_cancel hg0 h1, Nat.add_comm]
    -- the residues `w k = (y + d + a k) % b` all lie in the class of `y'` modulo `g`
    let w : Nat → Nat := fun k => (y + d + a * k) % b
    let r₀ := y' % g
    have hwg : ∀ k, w k % g = r₀ := fun k => by
      show (y + d + a * k) % b % g = y' % g
      rw [mod_mod_of_dvd hg0 hb hbg, FRC.Nat.add_mod _ _ _ hg0, mul_mod_zero hg0 hag k, Nat.add_zero,
        FRC.Nat.mod_mod _ _ hg0, hyd]
    -- the index of a residue `v < b` of that class: `v = g j + r₀`, `j < ua`
    have hidx : ∀ v, v < b → v % g = r₀ → g * mulIdx g (v - r₀) ua = v - r₀ ∧ mulIdx g (v - r₀) ua < ua ∧ r₀ ≤ v := by
      intro v hv hvg
      obtain ⟨q, hq⟩ := FRC.Nat.mod_spec g hg0 v
      rw [hvg] at hq
      have hsub : v - r₀ = g * q := by rw [hq, FRC.Nat.add_sub_cancel]
      have hqlt : q < ua := lt_of_mul_lt_mul (Nat.lt_of_le_of_lt (hq ▸ Nat.le_add_right (g * q) r₀ : g * q ≤ v)
        (hgb ▸ hv))
      have := mulIdx_spec g (v - r₀) q hsub.symm ua hqlt
      exact ⟨this.1, this.2, hq ▸ Nat.le_add_left r₀ (g * q)⟩
    let S : Nat → Nat := fun k => mulIdx g (w k - r₀) ua
    have hS : ∀ k, g * S k = w k - r₀ ∧ S k < ua ∧ r₀ ≤ w k := fun k => hidx (w k) (Nat.mod_lt _ hb) (hwg k)
    -- the residues are distinct over one cycle of length `ua`
    have key : ∀ k₁ k₂, k₁ < k₂ → k₂ < ua → w k₁ ≠ w k₂ := fun k₁ k₂ hlt hk e => by
      have h1 : (y + d + a * k₁ + a * (k₂ - k₁)) % b = (y + d + a * k₁) % b := by
        rw [Nat.add_assoc, ← Nat.mul_add, FRC.Nat.add_sub_of_le (Nat.le_of_lt hlt)]; exact e.symm
      have h2 : (a * (k₂ - k₁)) % b = 0 := mod_of_add_mod hb h1
      have h3 : (a * (k₂ - k₁)) % T = 0 := hcm _ (mod_zero_of_eq_mul ha rfl) h2
      obtain ⟨q, hq⟩ := eq_mul_of_mod_zero hT h3
      rw [hua, FRC.Nat.mul_assoc] at hq
      have h4 : k₂ - k₁ = ua * q := Nat.eq_of_mul_eq_mul_left ha hq
      have h5 : 0 < k₂ - k₁ := sub_pos hlt
      have h6 : k₂ - k₁ < ua := Nat.lt_of_le_of_lt (Nat.sub_le k₂ k₁) hk
      match q with
      | 0 => rw [h4, Nat.mul_zero] at h5; exact Nat.lt_irrefl 0 h5
      | q + 1 => rw [h4, Nat.mul_succ] at h6; exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt (Nat.le_add_left ua _) h6)
    have hw_inj : ∀ k₁ k₂, k₁ < ua → k₂ < ua → w k₁ = w k₂ → k₁ = k₂ := fun k₁ k₂ h1 h2 ew =>
      match Nat.lt_or_ge k₁ k₂ with
      | .inl hlt => absurd ew (key k₁ k₂ hlt h2)
      | .inr hge => match Nat.lt_or_ge k₂ k₁ with
        | .inl hlt => absurd ew.symm (key k₂ k₁ hlt h1)
        | .inr hge' => Nat.le_antisymm hge' hge
    have hinj : ∀ k₁ k₂, k₁ < ua → k₂ < ua → S k₁ = S k₂ → k₁ = k₂ := fun k₁ k₂ h1 h2 e =>
      hw_inj k₁ k₂ h1 h2 (by
        rw [← FRC.Nat.sub_add_cancel (hS k₁).2.2, ← FRC.Nat.sub_add_cancel (hS k₂).2.2, ← (hS k₁).1, ← (hS k₂).1, e])
    have hy'g := hidx y' hy' rfl
    obtain ⟨k, hku, hk⟩ := FRC.Logic.inj_onto ua S (fun k _ => (hS k).2.1) hinj (mulIdx g (y' - r₀) ua) hy'g.2.1
    have hwk : w k = y' := by
      rw [← FRC.Nat.sub_add_cancel (hS k).2.2, ← FRC.Nat.sub_add_cancel hy'g.2.2, ← (hS k).1, ← hy'g.1, hk]
    have hdT : d + a * k < T := by
      rw [hua]
      calc d + a * k < a + a * k := Nat.add_lt_add_right (Nat.mod_lt _ ha) (a * k)
        _ = a * (k + 1) := by rw [Nat.add_comm, Nat.mul_succ]
        _ ≤ a * ua := Nat.mul_le_mul_left a hku
    refine ⟨d + a * k, hdT, ?_, ?_⟩
    · rw [← Nat.add_assoc, Nat.add_comm (x + d), FRC.Nat.add_mul_mod_self_left _ _ _ ha, hxd]
    · rw [← Nat.add_assoc]; exact hwk

/-! ## Dephasing over the product period (00:F2) -/

section dephasing
variable {q : Nat} [Pos q]

/-- Powers of a product: `(Π_j ζ_j)^t = Π_j ζ_j^t`. -/
theorem prodRange_pow (ζ : Nat → Shell q) (t : Nat) : ∀ m, prodRange (fun j => ζ j ^ t) m = (prodRange ζ m) ^ t
  | 0 => (one_pow t).symm
  | m + 1 => by
    show prodRange (fun j => ζ j ^ t) m * ζ m ^ t = (prodRange ζ m * ζ m) ^ t
    rw [prodRange_pow ζ t m, mul_pow]

theorem prodRange_one : ∀ m, prodRange (fun _ => (1 : Shell q)) m = 1
  | 0 => rfl
  | m + 1 => by show prodRange (fun _ => (1 : Shell q)) m * 1 = 1; rw [prodRange_one m, mul_one]

/-- 00:F2, 22:C26 — dephasing is exact: on a prime shell `q`, a character `χ(x) = Π_j ζ_j^{x_j}` of the composite
(`ζ_j^{n_j} = 1`) that the drive moves (`χ(v) = Π_j ζ_j ≠ 1`) sums to zero along the drive, `Σ_{t<M} χ(t v) = 0`, over
every joint recurrence `M`, the product of the periods among them. -/
theorem dephasing (hq : FRC.Nat.isPrime q) (n : Nat → Nat) (hn : ∀ j, 0 < n j) (m : Nat) (ζ : Nat → Shell q)
    (hζ : ∀ j, j < m → ζ j ^ n j = 1) (hχ : prodRange ζ m ≠ 1) (M : Nat) (hM : Joint n m M) :
    sumRange (fun t => prodRange (fun j => ζ j ^ t) m) M = 0 := by
  have e : ∀ t, t < M → prodRange (fun j => ζ j ^ t) m = (prodRange ζ m) ^ t := fun t _ => prodRange_pow ζ t m
  rw [sum_congr M e]
  have hz : (prodRange ζ m) ^ M = 1 := by
    rw [← prodRange_pow, prodRange_congr m (fun j hj => by
      obtain ⟨u, hu⟩ := eq_mul_of_mod_zero (hn j) (hM j hj)
      show ζ j ^ M = 1
      rw [hu, pow_mul, hζ j hj, one_pow]), prodRange_one]
  have hg := geom_sum_mul (prodRange ζ m) M
  rw [hz, add_neg] at hg
  match Prime.mul_eq_zero hq hg with
  | .inl h => exact h
  | .inr h => exact absurd (Prime.eq_of_sub_eq_zero h) hχ

end dephasing


end FRC.Quantum
