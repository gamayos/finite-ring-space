import FrcCore.Theme.Field
import FrcCore.Theme.Logic
import FrcCore.Theme.Drive

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


/-! ## The graded registration law (00:F5; 39-s173, rows B1–B5)

An Object component of order `n` (a prime power `ℓᵃ` of the Object's faces `C_{q−1}`, `C_{q+1}`) registers in the
Subject `𝔽_p` at the depth `d = ord_n(p)`: `d = 1` absorbed into the register `C_{p−1}`, its image the unique `C_n`;
`d = 2` observable on the boost torus `C_{p+1}`, its home unique since `gcd(p − 1, p + 1) = 2`; deeper, beyond the
quadratic frame. The sign `−1` registers on both faces. A component is visible while `p^d < Ω`; on a tower with
`p² < Ω` and `Ω / p² < p` the cap is `2`, read without forming `p³` (Q20). The instances are decided by the kernel. -/

section registration
variable {p : Nat} [Pos p]

/-- 00:F5, absorbed (`d = 1`): a component `n ∣ p − 1` registers in `C_{p−1}` with its unique image `C_n`: some `x` has
order `n`, and every `y` with `yⁿ = 1` is a power `x^k`, `k < n` (the root bound of `Xⁿ − 1`). -/
theorem absorbed (hp : FRC.Nat.isPrime p) {n : Nat} (hn : 0 < n) (hd : n ∣ p - 1) :
    ∃ x : Shell p, x ≠ 0 ∧ Prime.HasOrder x n ∧ ∀ y : Shell p, y ^ n = 1 → ∃ k, k < n ∧ y = x ^ k := by
  have hp1 : 0 < p - 1 := by
    match p, hp.1 with
    | k + 2, _ => exact Nat.zero_lt_succ k
  obtain ⟨x, hx0, hx⟩ := Prime.exists_order_of_dvd hp n n (Nat.le_refl n) hn hd
  refine ⟨x, hx0, hx, fun y hy => ?_⟩
  match decExistsLT (fun k => y = x ^ k) n with
  | .isTrue h => exact h
  | .isFalse h =>
    exfalso
    have hdist : ∀ i j, i < n → j < n → x ^ i = x ^ j → i = j := fun i j hi hj e => by
      have key : ∀ {a b : Nat}, a ≤ b → b < n → x ^ a = x ^ b → a = b := fun {a b} hab hb e => by
        have e1 : x ^ a * x ^ (b - a) = x ^ a * 1 := by rw [← pow_add, FRC.Nat.add_sub_of_le hab, mul_one, e]
        have h1 := Prime.mul_left_cancel hp (Prime.pow_ne_zero hp hx0 a) e1
        match Nat.decEq (b - a) 0 with
        | .isTrue h0 => exact Nat.le_antisymm hab (Nat.le_of_sub_eq_zero h0)
        | .isFalse h0 => exact absurd h1 (hx.2.2 _ (Nat.lt_of_le_of_lt (Nat.sub_le b a) hb) (Nat.pos_of_ne_zero h0))
      match Nat.lt_or_ge i j with
      | .inl hlt => exact key (Nat.le_of_lt hlt) hj e
      | .inr hge => exact (key hge hi e.symm).symm
    let r : Nat → Shell p := fun i => if i < n then x ^ i else y
    have hr : ∀ i j, i ≤ n → j ≤ n → r i = r j → i = j := fun i j hi hj e => by
      change (if i < n then x ^ i else y) = (if j < n then x ^ j else y) at e
      match Nat.decLt i n, Nat.decLt j n with
      | .isTrue hi', .isTrue hj' =>
        have e' : x ^ i = x ^ j := by
          have := e; rw [ite_eq_left hi', ite_eq_left hj'] at this; exact this
        exact hdist i j hi' hj' e'
      | .isTrue hi', .isFalse hj' =>
        have e' : x ^ i = y := by
          have := e; rw [ite_eq_left hi', ite_eq_right hj'] at this; exact this
        exact absurd ⟨i, hi', e'.symm⟩ h
      | .isFalse hi', .isTrue hj' =>
        have e' : y = x ^ j := by
          have := e; rw [ite_eq_right hi', ite_eq_left hj'] at this; exact this
        exact absurd ⟨j, hj', e'⟩ h
      | .isFalse hi', .isFalse hj' =>
        exact (Nat.le_antisymm hi (Nat.not_lt.1 hi')).trans (Nat.le_antisymm hj (Nat.not_lt.1 hj')).symm
    have hroot : ∀ i, i ≤ n → Poly.eval (Poly.xn1 n : Poly p) n (r i) = 0 := fun i _ => by
      rw [Poly.eval_xn1 hn]
      match Nat.decLt i n with
      | .isTrue hi' =>
        show (if i < n then x ^ i else y) ^ n + -1 = 0
        rw [ite_eq_left hi', ← pow_mul, Nat.mul_comm, pow_mul, hx.2.1, one_pow, add_neg]
      | .isFalse hi' => show (if i < n then x ^ i else y) ^ n + -1 = 0; rw [ite_eq_right hi', hy, add_neg]
    have hz := Poly.root_bound_of (fun h => Prime.mul_eq_zero hp h) n (Poly.xn1 n) (Poly.xn1_bound n) r hr hroot n
    rw [Poly.xn1_top] at hz
    exact Prime.one_ne_zero hp hz

/-- A prime power that divides `x y`, with the prime not dividing `y`, divides `x` (Euclid, by induction on the power). -/
theorem pow_mod_of_not_mod {l : Nat} (hl : FRC.Nat.isPrime l) {y : Nat} (hy : y % l ≠ 0) :
    ∀ a x : Nat, (x * y) % l ^ a = 0 → x % l ^ a = 0
  | 0, x, _ => FRC.Nat.mod_unique (Nat.zero_lt_succ 0) (by rw [Nat.pow_zero, Nat.one_mul, Nat.add_zero])
  | a + 1, x, h => by
    have hl0 : 0 < l := Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) hl.1
    have hpa : 0 < l ^ a := FRC.Nat.pos_pow_of_pos a hl0
    obtain ⟨c, hc⟩ := eq_mul_of_mod_zero (FRC.Nat.pos_pow_of_pos (a + 1) hl0) h
    have e1 : x * y = l * (l ^ a * c) := by rw [hc, Nat.pow_succ, Nat.mul_comm (l ^ a) l, FRC.Nat.mul_assoc]
    have hlx : x % l = 0 := (FRC.Nat.prime_mul_mod hl (mod_zero_of_eq_mul hl0 e1)).resolve_right hy
    obtain ⟨x', hx'⟩ := eq_mul_of_mod_zero hl0 hlx
    have e2 : x' * y = l ^ a * c := Nat.eq_of_mul_eq_mul_left hl0 (by rw [← FRC.Nat.mul_assoc, ← hx', e1])
    obtain ⟨d, hd⟩ := eq_mul_of_mod_zero hpa (pow_mod_of_not_mod hl hy a x' (mod_zero_of_eq_mul hpa e2))
    exact mod_zero_of_eq_mul (FRC.Nat.pos_pow_of_pos (a + 1) hl0)
      (by rw [hx', hd, Nat.pow_succ, Nat.mul_comm (l ^ a) l, FRC.Nat.mul_assoc])

/-- 00:F5, the unique home (`d = 2`): on an odd shell every common divisor of `p − 1` and `p + 1` divides `2`
(`gcd(p − 1, p + 1) = 2`), so an odd prime power `ℓᵃ` dividing `(p − 1)(p + 1)` and not `p − 1` lies on the boost
torus: `ℓᵃ ∣ p + 1`. -/
theorem unique_home {p : Nat} (hp0 : 0 < p) :
    (∀ e : Nat, 0 < e → (p - 1) % e = 0 → (p + 1) % e = 0 → 2 % e = 0) ∧
    (∀ l a : Nat, FRC.Nat.isPrime l → l ≠ 2 → ((p - 1) * (p + 1)) % l ^ a = 0 → (p - 1) % l ^ a ≠ 0 →
      (p + 1) % l ^ a = 0) := by
  have hsum : p + 1 = (p - 1) + 2 := by
    rw [show (2 : Nat) = 1 + 1 from rfl, ← Nat.add_assoc, FRC.Nat.sub_add_cancel hp0]
  have common : ∀ e : Nat, 0 < e → (p - 1) % e = 0 → (p + 1) % e = 0 → 2 % e = 0 := fun e he h1 h2 => by
    rw [hsum] at h2
    exact mod_of_add_mod he (by rw [h2, h1])
  refine ⟨common, fun l a hl hl2 hprod hnot => ?_⟩
  have hl0 : 0 < l := Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) hl.1
  match Nat.decEq ((p - 1) % l) 0 with
  | .isFalse h1 => exact pow_mod_of_not_mod hl h1 a (p + 1) (by rw [Nat.mul_comm]; exact hprod)
  | .isTrue h1 =>
    -- `l ∣ p − 1`, so `l ∤ p + 1` (else `l ∣ 2`, `l = 2`), and then `ℓᵃ ∣ p − 1`, against the hypothesis
    have h2 : (p + 1) % l ≠ 0 := fun h2 => by
      have h := common l hl0 h1 h2
      obtain ⟨c, hc⟩ := eq_mul_of_mod_zero hl0 h
      have hle : l ≤ 2 := FRC.Nat.le_of_dvd' (Nat.zero_lt_succ 1) ⟨c, hc⟩
      exact hl2 (Nat.le_antisymm hle hl.1)
    exact absurd (pow_mod_of_not_mod hl h2 a (p - 1) hprod) hnot

/-- 00:F5, the sign: `−1` registers on both faces, `(−1)^{p−1} = (−1)^{p+1} = 1`, of order two (`−1 ≠ 1` on an odd
shell). -/
theorem sign_both {p : Nat} [Pos p] (h2 : 2 < p) (hp2 : p % 2 = 1) :
    (-1 : Shell p) ^ (p - 1) = 1 ∧ (-1 : Shell p) ^ (p + 1) = 1 ∧ (-1 : Shell p) * -1 = 1 ∧ (-1 : Shell p) ≠ 1 := by
  obtain ⟨m, hm⟩ := FRC.Nat.mod_spec 2 (Nat.zero_lt_succ 1) p
  rw [hp2] at hm
  have e1 : p - 1 = 2 * m := by rw [hm, FRC.Nat.add_sub_cancel]
  have e2 : p + 1 = 2 * (m + 1) := by rw [hm, Nat.mul_succ, Nat.add_assoc]
  have sq : (-1 : Shell p) * -1 = 1 := by rw [neg_mul_neg, mul_one]
  refine ⟨by rw [e1, pow_mul, pow_two, sq, one_pow], by rw [e2, pow_mul, pow_two, sq, one_pow], sq,
    Prime.neg_one_ne_one h2⟩

/-- 00:F5, the visibility cap: on a tower with `p² < Ω < p³` the cap `K = max{k : pᵏ < Ω}` is `2` (`p < Ω`,
`p² < Ω`, and `p³` beyond the totality); every saturating tower `p² < Ω ≤ (p + 1)²`, `p ≥ 3`, has `Ω < p³`; and the
minimal tower `(173, 30 089)` is saturating; the laboratory tower `(1 373, 2 408 561)` has `p² < Ω < p³`. -/
theorem visibility_cap :
    (∀ p Ω : Nat, 1 < p → p * p < Ω → p < Ω) ∧
    (∀ p Ω : Nat, 3 ≤ p → Ω ≤ (p + 1) * (p + 1) → Ω < p * p * p) ∧
    (173 * 173 < 30089 ∧ 30089 ≤ 174 * 174) ∧ (1373 * 1373 < 2408561 ∧ 2408561 < 1373 * 1373 * 1373) := by
  refine ⟨fun p Ω hp h2 => Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left p (Nat.lt_trans (Nat.zero_lt_succ 0) hp)) h2,
    fun p Ω hp hs => Nat.lt_of_le_of_lt hs ?_, by decide, by decide⟩
  -- (p + 1)² = p² + 2p + 1 < 3p² ≤ p³ for p ≥ 3
  have e : (p + 1) * (p + 1) = p * p + (p + (p + 1)) := by rw [Nat.mul_succ, Nat.succ_mul, Nat.add_assoc]
  have h1 : p + (p + 1) < p * p + p * p := by
    have h3 : 3 * p ≤ p * p := Nat.mul_le_mul_right p hp
    have hpp : p + (p + 1) < 3 * p := by
      rw [show 3 * p = p + (p + p) by rw [Nat.succ_mul, Nat.succ_mul, Nat.one_mul, Nat.add_assoc]]
      exact Nat.add_lt_add_left (Nat.add_lt_add_left (Nat.lt_of_lt_of_le (by decide : 1 < 3) hp) _) _
    exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hpp h3) (Nat.le_add_right _ _)
  have h4 : p * p + p * p + p * p ≤ p * p * p := by
    rw [show p * p + p * p + p * p = p * p * 3 by rw [Nat.mul_succ, Nat.mul_succ, Nat.mul_one]]
    exact Nat.mul_le_mul_left _ hp
  rw [e]
  exact Nat.lt_of_lt_of_le (by rw [Nat.add_assoc (p * p) (p * p) (p * p)]; exact Nat.add_lt_add_left h1 _) h4

/-- 00:F5, the 2-components on a Subject with `κ` odd (`p − 1 = 4κ`, `p + 1 = 4κ + 2`): the quarter absorbs (`4 ∣ p − 1`)
and the sign is on both faces (`2 ∣ p + 1`), while `8 ∤ p − 1` and `4 ∤ p + 1`, so a 2-component `2ᵃ`, `a ≥ 3`, lies on
neither torus: at depth `2` it registers in `𝔽_{p²}` off both, not on the boost torus. -/
theorem two_part_homes {κ : Nat} (hκ : κ % 2 = 1) :
    (4 * κ) % 4 = 0 ∧ (4 * κ) % 8 ≠ 0 ∧ (4 * κ + 2) % 2 = 0 ∧ (4 * κ + 2) % 4 ≠ 0 ∧
    ∀ a, 3 ≤ a → (4 * κ) % 2 ^ a ≠ 0 ∧ (4 * κ + 2) % 2 ^ a ≠ 0 := by
  obtain ⟨m, hm⟩ := FRC.Nat.mod_spec 2 (Nat.zero_lt_succ 1) κ
  rw [hκ] at hm
  have e1 : 4 * κ = 8 * m + 4 := by rw [hm, Nat.left_distrib, ← FRC.Nat.mul_assoc]
  have e2 : 4 * κ + 2 = 4 * (2 * m + 1) + 2 := by rw [hm]
  have h8 : (4 * κ) % 8 ≠ 0 := by rw [e1, FRC.Nat.add_mul_mod_self_left _ _ _ (by decide)]; decide
  have h4 : (4 * κ + 2) % 4 ≠ 0 := by rw [e2, FRC.Nat.add_mul_mod_self_left _ _ _ (by decide)]; decide
  have hpow : ∀ a, 3 ≤ a → ∃ c, 2 ^ a = 8 * c := fun a ha =>
    ⟨2 ^ (a - 3), by rw [show (8 : Nat) = 2 ^ 3 from rfl, ← FRC.Nat.pow_add, FRC.Nat.add_sub_of_le ha]⟩
  refine ⟨mod_zero_of_eq_mul (by decide) rfl, h8, mod_zero_of_eq_mul (by decide) (by rw [e2, show 4 * (2 * m + 1) + 2 = 2 * (2 * (2 * m + 1) + 1) by rw [Nat.mul_succ 2, ← FRC.Nat.mul_assoc]]), h4,
    fun a ha => ⟨fun h => h8 ?_, fun h => h4 ?_⟩⟩
  · obtain ⟨c, hc⟩ := hpow a ha
    obtain ⟨d, hd⟩ := eq_mul_of_mod_zero (FRC.Nat.pos_pow_of_pos a (by decide)) h
    exact mod_zero_of_eq_mul (by decide) (by rw [hd, hc, FRC.Nat.mul_assoc])
  · obtain ⟨c, hc⟩ := hpow a ha
    obtain ⟨d, hd⟩ := eq_mul_of_mod_zero (FRC.Nat.pos_pow_of_pos a (by decide)) h
    exact mod_zero_of_eq_mul (by decide) (by rw [hd, hc, show (8 : Nat) = 4 * 2 from rfl, FRC.Nat.mul_assoc, FRC.Nat.mul_assoc])

/-- 00:F5, the instances (39:B2, B3, B5), decided by the kernel: the depth of `7` (hydrogen's interior) is `6` at
`173`, `2` at `181` and `1` at `197`, each the least `d` with `pᵈ ≡ 1 (mod 7)`; hydrogen's quarter is absorbed at `173`
with the images `{1, 80, 93, 172}`, exactly the roots of `x⁴ = 1`, and its triality is observable there (`3 ∤ 172`,
`3 ∣ 174`); the proton (`q = 5`) registers whole, `4 ∣ 172` and `6 ∣ 174`; `(5, 13)` is refused, `5² > 13`. -/
theorem registration_instances :
    ((173 ^ 6) % 7 = 1 ∧ ∀ d, 0 < d → d < 6 → (173 ^ d) % 7 ≠ 1) ∧
    ((181 ^ 2) % 7 = 1 ∧ 181 % 7 ≠ 1) ∧ 197 % 7 = 1 ∧
    (∀ v, v < 173 → ((ofNat v : Shell 173) ^ 4 = 1 ↔ v = 1 ∨ v = 80 ∨ v = 93 ∨ v = 172)) ∧
    (172 % 3 ≠ 0 ∧ 174 % 3 = 0) ∧ (172 % 4 = 0 ∧ 174 % 6 = 0) ∧ 13 < 5 * 5 := by
  refine ⟨⟨by decide, fun d h0 h6 => ?_⟩, by decide, by decide, by decide +kernel, by decide, by decide, by decide⟩
  · match d, h0, h6 with
    | 1, _, _ => decide
    | 2, _, _ => decide
    | 3, _, _ => decide
    | 4, _, _ => decide
    | 5, _, _ => decide
    | k + 6, _, h => exact absurd h (Nat.not_lt_of_le (Nat.le_add_left 6 k))
end registration

end FRC.Quantum
