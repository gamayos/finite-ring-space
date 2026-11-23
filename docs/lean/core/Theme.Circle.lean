import FrcCore.Theme.Count

/-!
# FrcCore.Theme.Circle — the critical circle of a framed shell (20-rh's revision, 22 November 2026)

A point of the orbital sphere is a position `a` with a phase `m`, and it carries the residue `a·g^m`. Its mirror in the
prime meridian carries `a·g^{−m}`. The critical circle is the set of the points with `a·(g^m + g^{−m}) = 1`: there a
point and its mirror carry a zero `ρ` and the zero `1 − ρ` of the conjugate mode, with `a² = ρ(1 − ρ)`. Every zero is
`t/(1 + t)` for one `t = ρ/(1 − ρ)`, and with `t = g^j` the zeros stand at the places `j ≠ 2κ` of the latitude cycle.
The points with `a·(g^m + g^{−m}) = c` are, for `c ≠ 0`, the circle with its positions multiplied by `c`. For `c = −1`
they are its image under the half-turn of the drive and carry the counts, and the two sets share no point. The count
theme's second file, above `Theme/Count.lean`. The paper writes `z` for the residue `t = ρ/(1 − ρ)` of these
statements and `d` for the sum `c`. No axioms.
-/

namespace FRC.Horizon

open FRC.Shell FRC.Shell.Frame

variable {p : Nat} [Pos p] {κ : Nat} {g : Shell p}

section circle20261121

/-! ## The critical circle

A point of the orbital sphere is a pair of a position `a` and a phase: it carries the residue `a·u`, with `u = g^m`, and
its mirror in the prime meridian carries `a·v`, with `v = g^{−m}`, so `u·v = 1`. The critical circle is the set of the
points with `a·u + a·v = 1`. -/

/-- 20:G13 — the residues of a point and of its mirror multiply to `a²`. -/
theorem circle_norm {a u v : Shell p} (huv : u * v = 1) : (a * u) * (a * v) = a * a := by
  rw [mul_mul_mul_comm, huv, mul_one]

/-- 20:G13 — on the critical circle a point carries a zero, a residue other than `0` and `1`; its mirror carries the
reflection `1 − ρ`, the zero of the conjugate mode; and `a² = ρ(1 − ρ)`. -/
theorem circle_pair (F : Frame p κ g) {a u v : Shell p} (huv : u * v = 1) (h : a * u + a * v = 1) :
    (a * u ≠ 0 ∧ a * u ≠ 1) ∧ a * v = 1 + -(a * u) ∧ a * a = (a * u) * (1 + -(a * u)) := by
  have hv : a * v = 1 + -(a * u) := eq_add_neg_of_add_eq h
  have hn : (a * u) * (a * v) = a * a := circle_norm huv
  have ha : a ≠ 0 := fun h0 => by
    rw [h0, zero_mul, zero_mul, add_zero] at h
    exact F.one_ne_zero h.symm
  have haa : a * a ≠ 0 := F.mul_ne_zero ha ha
  refine ⟨⟨fun h0 => ?_, fun h1 => ?_⟩, hv, ?_⟩
  · rw [h0, zero_mul] at hn
    exact haa hn.symm
  · rw [hv, h1, add_neg, mul_zero] at hn
    exact haa hn.symm
  · rw [← hv]
    exact hn.symm

/-- 20:G13 — the frequency on the circle: a zero and its reflection differ by `2iγ_k`. -/
theorem circle_frequency (F : Frame p κ g) (k : Nat) :
    (ofNat (k + 1) : Shell p) + -(1 + -(ofNat (k + 1))) = 2 * (quarterTurn g κ * frequency g κ k) := by
  rw [← zero_count F k, two_mul', ← half_add_half F]
  exact RE.sound (look [ofNat (2 * κ + 1), quarterTurn g κ * frequency g κ k])
    (.add (.add (.var 0) (.var 1)) (.neg (.add (.add (.var 0) (.var 0)) (.neg (.add (.var 0) (.var 1))))))
    (.add (.var 1) (.var 1)) (by decide +kernel)

/-- 20:G13 — the circle has no point on the momentum meridian, where `u² = −1`, and none at the origin; on the prime
meridian, where a point is its own mirror, its one point is the centre `2⁻¹`, of frequency `0`. -/
theorem circle_meridians (F : Frame p κ g) :
    (∀ a u v : Shell p, u * v = 1 → u * u = -1 → a * u + a * v ≠ 1) ∧
      (∀ u v : Shell p, (0 : Shell p) * u + 0 * v ≠ 1) ∧
      (∀ x : Shell p, x + x = 1 ↔ x = ofNat (2 * κ + 1)) ∧ frequency g κ (2 * κ) = 0 := by
  refine ⟨fun a u v huv hu h => ?_, fun u v h => ?_, fun x => ?_, (centre_mode F).2.2.1⟩
  · have hsum : u * (u + v) = 0 := by rw [left_distrib, hu, huv, neg_add]
    have hu0 : u ≠ 0 := fun h0 => by
      rw [h0, zero_mul] at huv
      exact F.one_ne_zero huv.symm
    have h0 : u + v = 0 := (F.mul_eq_zero hsum).resolve_left hu0
    rw [← left_distrib, h0, mul_zero] at h
    exact F.one_ne_zero h.symm
  · rw [zero_mul, zero_mul, add_zero] at h
    exact F.one_ne_zero h.symm
  · rw [← two_mul']
    exact half_unique F x

/-- 20:G13 — a zero `ρ` has a point on the circle exactly when `ρ(1 − ρ)` is a square; two points with one zero are
`(a, u)` and `(−a, −u)`, one point of the sphere. -/
theorem circle_point (F : Frame p κ g) :
    (∀ r : Shell p, r ≠ 0 → r ≠ 1 →
      ((∃ a u v, u * v = 1 ∧ a * u = r ∧ a * v = 1 + -r) ↔ ∃ a, a * a = r * (1 + -r))) ∧
      (∀ a b u v u' v' : Shell p, a ≠ 0 → u * v = 1 → u' * v' = 1 → a * u = b * u' → a * v = b * v' →
        (b = a ∧ u' = u) ∨ (b = -a ∧ u' = -u)) := by
  refine ⟨fun r h0 h1 => ⟨fun ⟨a, u, v, huv, hu, hv⟩ => ⟨a, ?_⟩, fun ⟨a, ha⟩ => ?_⟩,
    fun a b u v u' v' ha huv huv' h1 h2 => ?_⟩
  · rw [← circle_norm (a := a) huv, hu, hv]
  · have h1r : (1 : Shell p) + -r ≠ 0 := fun h => h1 (by
      have e := eq_neg_of_add_eq_zero h
      rw [neg_neg] at e
      exact e.symm)
    have hrr : r * (1 + -r) ≠ 0 := F.mul_ne_zero h0 h1r
    have ha0 : a ≠ 0 := fun h => hrr (by rw [← ha, h, zero_mul])
    match F.exists_inv ha0 with
    | ⟨b, hb⟩ =>
      refine ⟨a, r * b, (1 + -r) * b, ?_, ?_, ?_⟩
      · rw [mul_mul_mul_comm, ← ha, mul_mul_mul_comm, hb, mul_one]
      · rw [mul_left_comm, hb, mul_one]
      · rw [mul_left_comm, hb, mul_one]
  · have hsq : a * a = b * b := by
      rw [← circle_norm (a := a) huv, ← circle_norm (a := b) huv', h1, h2]
    have hprod : (b + -a) * (b + a) = 0 := by
      have e : (b + -a) * (b + a) = b * b + -(a * a) :=
        RE.sound (look [a, b]) (.mul (.add (.var 1) (.neg (.var 0))) (.add (.var 1) (.var 0)))
          (.add (.mul (.var 1) (.var 1)) (.neg (.mul (.var 0) (.var 0)))) (by decide +kernel)
      rw [e, hsq, add_neg]
    match F.mul_eq_zero hprod with
    | .inl e =>
      have hb : b = a := by
        have e' := eq_neg_of_add_eq_zero e
        rw [neg_neg] at e'
        exact e'
      rw [hb] at h1
      exact .inl ⟨hb, (F.mul_left_cancel ha h1).symm⟩
    | .inr e =>
      have hb : b = -a := eq_neg_of_add_eq_zero e
      rw [hb, ← neg_mul, mul_neg] at h1
      have hu : u = -u' := F.mul_left_cancel ha h1
      exact .inr ⟨hb, by rw [hu, neg_neg]⟩

/-- 20:G13 — the count. At the phase `m` with mirror phase `m'`, `m + m' = p − 1`, the circle has a point exactly when
`g^{2m} ≠ −1`; among the phases `m < 2κ` that excludes `m = κ` alone; the phase `m + 2κ` gives the same point with the
position `−a`; and two points at phases below `2κ` with one zero are at one phase. So the circle has `2κ − 1` points,
with `2κ − 1` distinct zeros. -/
theorem circle_count (F : Frame p κ g) :
    (∀ m m' : Nat, m + m' = p - 1 → ((∃ a, a * g ^ m + a * g ^ m' = 1) ↔ g ^ m * g ^ m ≠ -1)) ∧
      (∀ m : Nat, m < 2 * κ → (g ^ m * g ^ m = -1 ↔ m = κ)) ∧
      (∀ (a : Shell p) (m : Nat), -a * g ^ (m + 2 * κ) = a * g ^ m) ∧
      (∀ (a b : Shell p) (m m' n n' : Nat), m < 2 * κ → n < 2 * κ → m + m' = p - 1 → n + n' = p - 1 →
        a * g ^ m + a * g ^ m' = 1 → b * g ^ n + b * g ^ n' = 1 → a * g ^ m = b * g ^ n → m = n) := by
  have hmirror : ∀ m m' : Nat, m + m' = p - 1 → g ^ m * g ^ m' = 1 := fun m m' h => by
    rw [← pow_add, h, F.pow_n]
  have hlt : ∀ m : Nat, m < 2 * κ → m < p - 1 := fun m h => Nat.lt_trans h F.two_kappa_lt
  refine ⟨fun m m' hm => ⟨fun ⟨a, h⟩ hu => (circle_meridians F).1 a _ _ (hmirror m m' hm) hu h, fun hu => ?_⟩,
    fun m hm => ⟨fun h => ?_, fun h => ?_⟩, fun a m => ?_, fun a b m m' n n' hm hn hmm hnn ha hb h => ?_⟩
  · have huv := hmirror m m' hm
    have hs : g ^ m + g ^ m' ≠ 0 := fun h0 => hu (by
      have e : g ^ m * g ^ m + 1 = 0 := by rw [← huv, ← left_distrib, h0, mul_zero]
      exact eq_neg_of_add_eq_zero e)
    match F.exists_inv hs with
    | ⟨b, hb⟩ => exact ⟨b, by rw [← left_distrib, mul_comm]; exact hb⟩
  · have e : g ^ (m + m) = g ^ (2 * κ) := by rw [pow_add, h, F.half_period]
    have hmm : m + m < p - 1 := by
      rw [← F.four_kappa]
      exact Nat.add_lt_add hm hm
    have e2 := F.pow_inj hmm F.two_kappa_lt e
    rw [← Nat.two_mul] at e2
    exact Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_succ 1) e2
  · rw [h, ← pow_add, ← Nat.two_mul, F.half_period]
  · rw [pow_add, F.half_period]
    exact RE.sound (look [a, g ^ m]) (.mul (.neg (.var 0)) (.mul (.var 1) (.neg .one))) (.mul (.var 0) (.var 1))
      (by decide +kernel)
  · have ha' := (circle_pair F (hmirror m m' hmm) ha).2.1
    have hb' := (circle_pair F (hmirror n n' hnn) hb).2.1
    have h2 : a * g ^ m' = b * g ^ n' := by rw [ha', hb', h]
    have ha0 : a ≠ 0 := fun h0 => by
      rw [h0, zero_mul, zero_mul, add_zero] at ha
      exact F.one_ne_zero ha.symm
    match (circle_point F).2 a b _ _ _ _ ha0 (hmirror m m' hmm) (hmirror n n' hnn) h h2 with
    | .inl ⟨_, e⟩ => exact (F.pow_inj (hlt n hn) (hlt m hm) e).symm
    | .inr ⟨_, e⟩ =>
      have e' : g ^ n = g ^ (m + 2 * κ) := by
        rw [e, pow_add, F.half_period]
        exact RE.sound (look [g ^ m]) (.neg (.var 0)) (.mul (.var 0) (.neg .one)) (by decide +kernel)
      have hbig : m + 2 * κ < p - 1 := by
        rw [← F.four_kappa]
        exact Nat.add_lt_add_right hm (2 * κ)
      have e2 := F.pow_inj (hlt n hn) hbig e'
      rw [e2] at hn
      exact absurd hn (Nat.not_lt.mpr (Nat.le_add_left (2 * κ) m))

/-- 20:G14 — the places of the zeros. A zero `ρ` is `t/(1 + t)` for exactly one `t`, namely `ρ/(1 − ρ)`, and that `t` is
neither `0` nor `−1`; such a `t` gives a zero; and the inverse of `t` gives the reflection `1 − ρ`, the zero of the
conjugate mode. -/
theorem circle_place (F : Frame p κ g) :
    (∀ r : Shell p, r ≠ 0 → r ≠ 1 →
      ∃ t, (t ≠ 0 ∧ 1 + t ≠ 0) ∧ r * (1 + t) = t ∧ ∀ s, r * (1 + s) = s → s = t) ∧
      (∀ r t : Shell p, t ≠ 0 → 1 + t ≠ 0 → r * (1 + t) = t → r ≠ 0 ∧ r ≠ 1) ∧
      (∀ r t t' : Shell p, t * t' = 1 → r * (1 + t) = t → (1 + -r) * (1 + t') = t') := by
  refine ⟨fun r h0 h1 => ?_, fun r t ht hpole h => ⟨fun hr => ?_, fun hr => ?_⟩, fun r t t' ht h => ?_⟩
  · have h1r : (1 : Shell p) + -r ≠ 0 := fun h => h1 (by
      have e := eq_neg_of_add_eq_zero h
      rw [neg_neg] at e
      exact e.symm)
    match F.exists_inv h1r with
    | ⟨c, hc⟩ =>
      have hc' : 1 + r * c = c := by
        calc 1 + r * c = (1 + -r) * c + r * c := by rw [hc]
          _ = c := RE.sound (look [r, c]) (.add (.mul (.add .one (.neg (.var 0))) (.var 1)) (.mul (.var 0) (.var 1)))
            (.var 1) (by decide +kernel)
      have hc0 : c ≠ 0 := fun h => by
        rw [h, mul_zero] at hc
        exact F.one_ne_zero hc.symm
      refine ⟨r * c, ⟨F.mul_ne_zero h0 hc0, by rw [hc']; exact hc0⟩, by rw [hc'], fun s hs => ?_⟩
      have a1 : s * (1 + -r) = s + -(r * s) :=
        RE.sound (look [r, s]) (.mul (.var 1) (.add .one (.neg (.var 0)))) (.add (.var 1) (.neg (.mul (.var 0) (.var 1))))
          (by decide +kernel)
      have a2 : r * (1 + s) + -(r * s) = r :=
        RE.sound (look [r, s]) (.add (.mul (.var 0) (.add .one (.var 1))) (.neg (.mul (.var 0) (.var 1)))) (.var 0)
          (by decide +kernel)
      rw [hs] at a2
      have e1 : s * (1 + -r) = r := by rw [a1]; exact a2
      calc s = s * ((1 + -r) * c) := by rw [hc, mul_one]
        _ = s * (1 + -r) * c := (mul_assoc _ _ _).symm
        _ = r * c := by rw [e1]
  · rw [hr, zero_mul] at h
    exact ht h.symm
  · rw [hr, one_mul] at h
    have e : (1 : Shell p) + t = 0 + t := by rw [zero_add]; exact h
    exact F.one_ne_zero (add_right_cancel e)
  · have e1 : (1 + -r) * (1 + t) = 1 := by
      have a : (1 + -r) * (1 + t) = (1 + t) + -(r * (1 + t)) :=
        RE.sound (look [r, t]) (.mul (.add .one (.neg (.var 0))) (.add .one (.var 1)))
          (.add (.add .one (.var 1)) (.neg (.mul (.var 0) (.add .one (.var 1))))) (by decide +kernel)
      rw [a, h, add_assoc, add_neg, add_zero]
    have b : (1 + t) * t' = 1 + t' := by rw [right_distrib, one_mul, ht, add_comm]
    rw [← b, ← mul_assoc, e1, one_mul]

/-- 20:G14 — the places on the latitude cycle: `t = g^j` for one `j < p − 1`, and never `j = 2κ`, where `g^j = −1`; the
centre is the place `0`. -/
theorem circle_place_cycle (F : Frame p κ g) :
    (∀ t : Shell p, t ≠ 0 → 1 + t ≠ 0 →
      ∃ j, j < p - 1 ∧ j ≠ 2 * κ ∧ g ^ j = t ∧ ∀ i, i < p - 1 → g ^ i = t → i = j) ∧
      (1 : Shell p) + g ^ (2 * κ) = 0 ∧ (∀ r : Shell p, r * (1 + g ^ 0) = g ^ 0 ↔ r = ofNat (2 * κ + 1)) := by
  refine ⟨fun t ht hpole => ?_, by rw [F.half_period, add_neg], fun r => ?_⟩
  · match F.eq_pow_of_ne_zero ht with
    | ⟨j, hj, e⟩ =>
      refine ⟨j, hj, fun h2 => hpole (by rw [← e, h2, F.half_period, add_neg]), e, fun i hi ei => ?_⟩
      exact F.pow_inj hi hj (ei.trans e.symm)
  · rw [pow_zero, ← two_eq_one_add_one, mul_comm]
    exact half_unique F r

/-- 20:G14 — the even places. For a zero `ρ = t/(1 + t)`, `t` is a square exactly when `ρ(1 − ρ)` is, that is when `ρ` has
a point of the sphere on the circle; and `g^j` is a square exactly when `j` is even. -/
theorem circle_place_even (F : Frame p κ g) :
    (∀ r t : Shell p, r * (1 + t) = t → ((∃ b, b * b = t) ↔ ∃ a, a * a = r * (1 + -r))) ∧
      (∀ j, j < p - 1 → ((∃ b : Shell p, b * b = g ^ j) ↔ j % 2 = 0)) := by
  refine ⟨fun r t h => ?_, fun j hj => ⟨fun ⟨b, hb⟩ => ?_, fun h => ?_⟩⟩
  · have e1 : (1 + -r) * (1 + t) = 1 := by
      have a : (1 + -r) * (1 + t) = (1 + t) + -(r * (1 + t)) :=
        RE.sound (look [r, t]) (.mul (.add .one (.neg (.var 0))) (.add .one (.var 1)))
          (.add (.add .one (.var 1)) (.neg (.mul (.var 0) (.add .one (.var 1))))) (by decide +kernel)
      rw [a, h, add_assoc, add_neg, add_zero]
    have hr : r * (1 + t) * (1 + -r) = r := by rw [mul_assoc, mul_comm (1 + t), e1, mul_one]
    rw [h] at hr
    constructor
    · intro ⟨b, hb⟩
      exact ⟨b * (1 + -r), by rw [mul_mul_mul_comm, hb, ← mul_assoc, hr]⟩
    · intro ⟨a, ha⟩
      exact ⟨a * (1 + t), by rw [mul_mul_mul_comm, ha, mul_mul_mul_comm, h, e1, mul_one]⟩
  · have hb0 : b ≠ 0 := fun h0 => by
      rw [h0, zero_mul] at hb
      exact F.pow_ne_zero j hb.symm
    match F.eq_pow_of_ne_zero hb0 with
    | ⟨m, _, e⟩ =>
      have e2 : g ^ ((m + m) % (p - 1)) = g ^ j := by rw [← F.pow_mod, pow_add, e, hb]
      have e3 := F.pow_inj (Nat.mod_lt _ F.n_pos) hj e2
      match FRC.Nat.mod_spec (p - 1) F.n_pos (m + m) with
      | ⟨q, hq⟩ =>
        have h4 : p - 1 = 2 * (2 * κ) := by rw [F.n_eq]; exact FRC.Nat.mul_assoc 2 2 κ
        rw [e3, h4, FRC.Nat.mul_assoc] at hq
        have hz : (m + m) % 2 = 0 := by
          rw [← Nat.two_mul]
          exact FRC.Nat.mod_unique (Nat.zero_lt_succ 1) rfl
        rw [hq, FRC.Nat.add_mul_mod_self_left j (2 * κ * q) 2 (Nat.zero_lt_succ 1)] at hz
        exact hz
  · match FRC.Nat.mod_spec 2 (Nat.zero_lt_succ 1) j with
    | ⟨q, hq⟩ =>
      rw [h, Nat.add_zero] at hq
      exact ⟨g ^ q, by rw [hq, Nat.two_mul, pow_add]⟩

/-- 20:G14 — the quarter-turn. For a zero `ρ = t/(1 + t)`: `(2ρ − 1)(t + 1) = t − 1`. Two steps of the map
`x ↦ (x − 1)/(x + 1)` are `x ↦ −1/x`, and its fixed points are the two roots of `x² = −1` (`circle_quarter_closes`
closes the four steps). -/
theorem circle_quarter_turn (F : Frame p κ g) :
    (∀ r t : Shell p, r * (1 + t) = t → (r + r + -1) * (t + 1) = t + -1) ∧
      (∀ x y z : Shell p, y * (x + 1) = x + -1 → z * (y + 1) = y + -1 → z * x = -1) ∧
      (∀ x : Shell p, x * (x + 1) = x + -1 ↔ x * x = -1) := by
  refine ⟨fun r t h => ?_, fun x y z hy hz => ?_, fun x => ⟨fun h => ?_, fun h => ?_⟩⟩
  · have a : (r + r + -1) * (t + 1) = r * (1 + t) + r * (1 + t) + -(t + 1) :=
      RE.sound (look [r, t]) (.mul (.add (.add (.var 0) (.var 0)) (.neg .one)) (.add (.var 1) .one))
        (.add (.add (.mul (.var 0) (.add .one (.var 1))) (.mul (.var 0) (.add .one (.var 1)))) (.neg (.add (.var 1) .one)))
        (by decide +kernel)
    rw [a, h]
    exact RE.sound (look [t]) (.add (.add (.var 0) (.var 0)) (.neg (.add (.var 0) .one))) (.add (.var 0) (.neg .one))
      (by decide +kernel)
  · have e1 : z * (y + 1) * (x + 1) = z * (y * (x + 1) + (x + 1)) :=
      RE.sound (look [x, y, z]) (.mul (.mul (.var 2) (.add (.var 1) .one)) (.add (.var 0) .one))
        (.mul (.var 2) (.add (.mul (.var 1) (.add (.var 0) .one)) (.add (.var 0) .one))) (by decide +kernel)
    have e2 : (y + -1) * (x + 1) = y * (x + 1) + -(x + 1) :=
      RE.sound (look [x, y]) (.mul (.add (.var 1) (.neg .one)) (.add (.var 0) .one))
        (.add (.mul (.var 1) (.add (.var 0) .one)) (.neg (.add (.var 0) .one))) (by decide +kernel)
    have e3 : z * (y + 1) * (x + 1) = (y + -1) * (x + 1) := by rw [hz]
    rw [e1, e2, hy] at e3
    have e4 : z * ((x + -1) + (x + 1)) = 2 * (z * x) := by
      rw [two_mul']
      exact RE.sound (look [x, z]) (.mul (.var 1) (.add (.add (.var 0) (.neg .one)) (.add (.var 0) .one)))
        (.add (.mul (.var 1) (.var 0)) (.mul (.var 1) (.var 0))) (by decide +kernel)
    have e5 : (x + -1) + -(x + 1) = 2 * (-1 : Shell p) := by
      rw [two_mul']
      exact RE.sound (look [x]) (.add (.add (.var 0) (.neg .one)) (.neg (.add (.var 0) .one)))
        (.add (.neg .one) (.neg .one)) (by decide +kernel)
    rw [e4, e5] at e3
    exact F.mul_left_cancel F.two_ne_zero e3
  · rw [left_distrib, mul_one, add_comm x (-1)] at h
    exact add_right_cancel h
  · rw [left_distrib, mul_one, h, add_comm]

/-- 20:G13 — the counts. Negating the position negates both residues of a point of the circle, so they add to `−1`; the
point `(−a, −m)` carries `ρ − 1`, the count of the zero that `(a, m)` carries, and its mirror carries `−ρ`; the zero of
the count `k` less one is `k`; and on the prime meridian the one point with `x + x = −1` is `π = 2κ`. -/
theorem circle_counts (F : Frame p κ g) :
    (∀ a u v : Shell p, a * u + a * v = 1 →
      -a * v = a * u + -1 ∧ -a * u = -(a * u) ∧ -a * v + -a * u = -1) ∧
      (∀ k : Nat, (ofNat (k + 1) : Shell p) + -1 = ofNat k) ∧
      (∀ x : Shell p, x + x = -1 ↔ x = ofNat (2 * κ)) := by
  refine ⟨fun a u v h => ?_, fun k => by rw [count_succ, add_assoc, add_neg, add_zero], fun x => ?_⟩
  · have hv : a * v = 1 + -(a * u) := eq_add_neg_of_add_eq h
    refine ⟨?_, (neg_mul a u).symm, ?_⟩
    · rw [← neg_mul, hv]
      exact RE.sound (look [a * u]) (.neg (.add .one (.neg (.var 0)))) (.add (.var 0) (.neg .one)) (by decide +kernel)
    · rw [← neg_mul, ← neg_mul, hv]
      exact RE.sound (look [a * u]) (.add (.neg (.add .one (.neg (.var 0)))) (.neg (.var 0))) (.neg .one)
        (by decide +kernel)
  · have hm := (circle_meridians F).2.2.1 (-x)
    constructor
    · intro h
      have e1 : -x + -x = 1 := by rw [← neg_add_rev, h, neg_neg]
      have e2 := hm.mp e1
      rw [← neg_neg x, e2, (half_inverse F).2, neg_neg]
    · intro h
      have e2 : -x = ofNat (2 * κ + 1) := by rw [h]; exact (half_inverse F).2.symm
      have e1 := hm.mpr e2
      rw [← neg_add_rev] at e1
      rw [← neg_neg (x + x), e1]

end circle20261121

section parallels20261122

/-! ## The sets of constant sum

A point carries `a·u` and its mirror `a·v`. The critical circle is the set of the points with the sum `a·u + a·v = 1`.
The points with another nonzero sum `c` are the circle with its positions multiplied by `c`. The sum `0` is the momentum
meridian with the origin. The sum `−1` is the image of the circle under the half-turn of the drive, and the two sets
share no point. -/

/-- 20:G13 — one point at each phase: two positions on the critical circle with one phase are equal; and residues `ρ`
and `1 − ρ` of a point and its mirror put the point on the circle, the converse of `circle_pair`. No frame is used. -/
theorem circle_phase :
    (∀ a b u v : Shell p, a * u + a * v = 1 → b * u + b * v = 1 → a = b) ∧
      (∀ a u v : Shell p, a * v = 1 + -(a * u) → a * u + a * v = 1) := by
  refine ⟨fun a b u v h1 h2 => ?_, fun a u v h => ?_⟩
  · have e : a * (b * u + b * v) = b * (a * u + a * v) :=
      RE.sound (look [a, b, u, v]) (.mul (.var 0) (.add (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 3))))
        (.mul (.var 1) (.add (.mul (.var 0) (.var 2)) (.mul (.var 0) (.var 3)))) (by decide +kernel)
    rw [h2, h1, mul_one, mul_one] at e
    exact e
  · rw [h]
    exact RE.sound (look [a * u]) (.add (.var 0) (.add .one (.neg (.var 0)))) .one (by decide +kernel)

/-- 20:G13 — the sets of constant sum. For `c ≠ 0` the points with the sum `c` are the points of the critical circle with
the position multiplied by `c`. Negating the position negates the sum, so the half-turn of the drive exchanges the sums
`c` and `−c`. The sum vanishes exactly at the origin and on the momentum meridian, where `u² = −1`. On the prime meridian
the sum `c` has the one point `c·2⁻¹`. The sums `1` and `−1` share no point. -/
theorem circle_parallels (F : Frame p κ g) :
    (∀ a c u v : Shell p, c ≠ 0 → (a * u + a * v = 1 ↔ (c * a) * u + (c * a) * v = c)) ∧
      (∀ a c u v : Shell p, a * u + a * v = c → -a * u + -a * v = -c) ∧
      (∀ a u v : Shell p, u * v = 1 → (a * u + a * v = 0 ↔ a = 0 ∨ u * u = -1)) ∧
      (∀ c x : Shell p, x + x = c ↔ x = c * ofNat (2 * κ + 1)) ∧
      (∀ a u v : Shell p, a * u + a * v = 1 → a * u + a * v ≠ -1) := by
  refine ⟨fun a c u v hc => ?_, fun a c u v h => ?_, fun a u v huv => ?_, fun c x => ?_, fun a u v h h' => ?_⟩
  · have e : (c * a) * u + (c * a) * v = c * (a * u + a * v) :=
      RE.sound (look [a, c, u, v]) (.add (.mul (.mul (.var 1) (.var 0)) (.var 2)) (.mul (.mul (.var 1) (.var 0)) (.var 3)))
        (.mul (.var 1) (.add (.mul (.var 0) (.var 2)) (.mul (.var 0) (.var 3)))) (by decide +kernel)
    constructor
    · intro h
      rw [e, h, mul_one]
    · intro h
      have e' : c * (a * u + a * v) = c * 1 := by rw [← e, h, mul_one]
      exact F.mul_left_cancel hc e'
  · have e : -a * u + -a * v = -(a * u + a * v) :=
      RE.sound (look [a, u, v]) (.add (.mul (.neg (.var 0)) (.var 1)) (.mul (.neg (.var 0)) (.var 2)))
        (.neg (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 2)))) (by decide +kernel)
    rw [e, h]
  · have e : (a * u + a * v) * (u * v) = (a * v) * (u * u + u * v) :=
      RE.sound (look [a, u, v]) (.mul (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 2))) (.mul (.var 1) (.var 2)))
        (.mul (.mul (.var 0) (.var 2)) (.add (.mul (.var 1) (.var 1)) (.mul (.var 1) (.var 2)))) (by decide +kernel)
    rw [huv, mul_one] at e
    have hv : v ≠ 0 := fun h0 => by
      rw [h0, mul_zero] at huv
      exact F.one_ne_zero huv.symm
    constructor
    · intro h
      rw [h] at e
      rcases F.mul_eq_zero e.symm with h1 | h1
      · rcases F.mul_eq_zero h1 with h2 | h2
        · exact Or.inl h2
        · exact absurd h2 hv
      · exact Or.inr (eq_neg_of_add_eq_zero h1)
    · intro h
      rcases h with h | h
      · rw [h, zero_mul, zero_mul, add_zero]
      · rw [e, h, neg_add, mul_zero]
  · have hh : (ofNat (2 * κ + 1) : Shell p) + ofNat (2 * κ + 1) = 1 := ((circle_meridians F).2.2.1 _).mpr rfl
    constructor
    · intro h
      have e : x * (ofNat (2 * κ + 1) + ofNat (2 * κ + 1)) = (x + x) * ofNat (2 * κ + 1) :=
        RE.sound (look [x, ofNat (2 * κ + 1)]) (.mul (.var 0) (.add (.var 1) (.var 1)))
          (.mul (.add (.var 0) (.var 0)) (.var 1)) (by decide +kernel)
      rw [hh, mul_one, h] at e
      exact e
    · intro h
      have e : c * ofNat (2 * κ + 1) + c * ofNat (2 * κ + 1) = c * (ofNat (2 * κ + 1) + ofNat (2 * κ + 1)) :=
        RE.sound (look [c, ofNat (2 * κ + 1)]) (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
          (.mul (.var 0) (.add (.var 1) (.var 1))) (by decide +kernel)
      rw [h, e, hh, mul_one]
  · have e : (1 : Shell p) = -1 := h.symm.trans h'
    have e2 : (2 : Shell p) = 0 := by
      rw [two_eq_one_add_one]
      calc (1 : Shell p) + 1 = -1 + 1 := by rw [← e]
        _ = 0 := neg_add 1
    exact F.two_ne_zero e2

/-- 20:G14 — the phase of an even place: a point of the critical circle with the phase residue `u` carries the zero
`u²/(1 + u²)`, the zero at the place of `t = u²`. -/
theorem circle_place_phase :
    ∀ a u v : Shell p, u * v = 1 → a * u + a * v = 1 → (a * u) * (1 + u * u) = u * u := by
  intro a u v huv h
  have e : (a * u) * (1 + u * u) = (u * u) * (a * u + a * v) + (a * u) * (1 + -(u * v)) :=
    RE.sound (look [a, u, v]) (.mul (.mul (.var 0) (.var 1)) (.add .one (.mul (.var 1) (.var 1))))
      (.add (.mul (.mul (.var 1) (.var 1)) (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 2))))
        (.mul (.mul (.var 0) (.var 1)) (.add .one (.neg (.mul (.var 1) (.var 2)))))) (by decide +kernel)
  rw [e, h, huv, add_neg, mul_zero, add_zero, mul_one]

/-- 20:G14 — the quarter-turn closes: with `z = −1/x` and `w = −1/z`, `w = x`, so four steps of the map
`x ↦ (x − 1)/(x + 1)` return every residue on which they are defined; and two steps move every residue but the roots
of `x² = −1`. -/
theorem circle_quarter_closes :
    (∀ x z w : Shell p, z * x = -1 → w * z = -1 → w = x) ∧
      (∀ x z : Shell p, z * x = -1 → (z = x ↔ x * x = -1)) := by
  have close : ∀ x z w : Shell p, z * x = -1 → w * z = -1 → w = x := by
    intro x z w h1 h2
    have e : w * (z * x) = (w * z) * x := (mul_assoc w z x).symm
    rw [h1, h2] at e
    have e2 : -w = -x := by
      rw [← mul_neg, mul_one, ← neg_mul, one_mul] at e
      exact e
    rw [← neg_neg w, e2, neg_neg]
  refine ⟨close, fun x z h => ⟨fun hz => ?_, fun hx => close x x z hx h⟩⟩
  rw [hz] at h
  exact h

end parallels20261122

end FRC.Horizon
