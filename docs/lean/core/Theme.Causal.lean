import FrcCore.Parity
import FrcCore.Theme.Extension
import FrcCore.Theme.Gravity

/-!
# FrcCore.Theme.Causal — the counts of the Lorentzian form on every shell (3-causality, 7 November 2026)

The gravity theme's counting (`count`, `nsum`, their invariance under a bijection of the residues, and the plane conic
`y² + z² = c` with `p − 1` points for `c ≠ 0` and `2p − 1` for `c = 0`) applied to the diagonal form
`Q_ν = −ν t² + x² + y² + z²` of 3-causality, on every frame `(τ; 0, 1, g)` with `p = 4κ + 1`:

* the plane form `x² − ν t²` takes the value `0` once when `ν` is a nonsquare (`plane_zero_aniso`) and `2p − 1` times
  when `ν = w²` (`plane_zero_split`); over all values it takes `p²` points (`plane_total`);
* the count of `Q_ν = a` is `p²(p − 1) + p` times the plane's count at `a` (`form_count`), so the null cone has
  `p³ − p² + p` points for a nonsquare `ν` and `p³ + p² − p` for a square (`null_elliptic`, `null_hyperbolic`);
* for the drive `ν = g` the plane takes every nonzero value equally often, by the scaling `(t, x) ↦ (wt, wx)` and the
  swap `(t, x) ↦ (x, gt)`, which multiplies the form by `−g`: hence `p + 1` times (`plane_nonzero`), the norm-one
  cycle has `p + 1` elements, and every nonzero value of `Q_g` — the time sphere `Q_g = −g` among them — is taken
  `p³ + p` times (`sphere_drive`).

The counts are natural numbers and no numeral is formed. No axioms.
-/

namespace FRC.Causal

open FRC.Shell FRC.Shell.Frame FRC.Grav

variable {p : Nat} [Pos p]

/-! ## Sums over the residues -/

/-- A sum over the residues is invariant under a bijection of the residues. -/
theorem nsum_bij (F : Shell p → Nat) (f h : Shell p → Shell p) (hhf : ∀ x, h (f x) = x) :
    nsum (fun t => F (f (ofNat t))) p = nsum (fun t => F (ofNat t)) p := by
  have e : ∀ t, t < p → (fun t => F (f (ofNat t))) t = (fun y => F (ofNat y)) ((f (ofNat t)).val) := fun t _ => by
    show F (f (ofNat t)) = F (ofNat (f (ofNat t)).val)
    rw [ofNat_val]
  rw [nsum_congr p e]
  exact nsum_perm (fun y => F (ofNat y)) (fun t => (f (ofNat t)).val) p (fun t _ => (f (ofNat t)).lt)
    (fun i j hi hj hij => ofNat_inj hi hj (by rw [← hhf (ofNat i), ← hhf (ofNat j), ext hij]))

/-- An indicator summed over the residues is a count. -/
theorem nsum_ind (P : Shell p → Prop) [DecidablePred P] :
    nsum (fun x => if P (ofNat x) then 1 else 0) p = count P :=
  (natCount_eq_nsum (fun x => P (ofNat x)) p).symm

/-- A sum over the residues splits into the term at `0` and the terms at the nonzero residues. -/
theorem nsum_split (F : Shell p → Nat) :
    nsum (fun t => F (ofNat t)) p = F 0 + nsum (fun l => F (ofNat (l + 1))) (p - 1) := by
  have hp : (p - 1) + 1 = p := FRC.Nat.sub_add_cancel Pos.pos
  calc nsum (fun t => F (ofNat t)) p = nsum (fun t => F (ofNat t)) ((p - 1) + 1) := by rw [hp]
    _ = F (ofNat 0) + nsum (fun l => F (ofNat (l + 1))) (p - 1) := nsum_succ' _ _
    _ = F 0 + nsum (fun l => F (ofNat (l + 1))) (p - 1) := rfl

/-- The nonzero residues `l + 1`, `l < p − 1`, are nonzero. -/
theorem succ_ne_zero' {l : Nat} (hl : l < p - 1) : (ofNat (l + 1) : Shell p) ≠ 0 := fun h => by
  have hlt : l + 1 < p := by
    have h1 : l + 1 < (p - 1) + 1 := Nat.succ_lt_succ hl
    rw [FRC.Nat.sub_add_cancel Pos.pos] at h1
    exact h1
  exact Nat.succ_ne_zero l (ofNat_inj hlt Pos.pos h)

/-! ## The plane form `x² − ν t²` -/

/-- `#{(t, x) : x² − ν t² = c}`. -/
def planeCount (ν c : Shell p) : Nat :=
  nsum (fun t => nsum (fun x => if Q2 ν (ofNat t) (ofNat x) = c then 1 else 0) p) p

/-- The plane takes `p²` points over all its values. -/
theorem plane_total (ν : Shell p) : nsum (fun c => planeCount ν (ofNat c)) p = p * p := by
  have h1 : ∀ t, t < p →
      nsum (fun c => nsum (fun x => if Q2 ν (ofNat t) (ofNat x) = (ofNat c : Shell p) then 1 else 0) p) p = p := by
    intro t _
    have h2 : ∀ x, x < p →
        nsum (fun c => if Q2 ν (ofNat t) (ofNat x) = (ofNat c : Shell p) then 1 else 0) p = 1 := by
      intro x _
      exact (nsum_congr p (fun c _ => ite_iff ⟨Eq.symm, Eq.symm⟩ 1 0)).trans
        ((nsum_ind (fun c => c = Q2 ν (ofNat t) (ofNat x))).trans (count_eq _))
    calc nsum (fun c => nsum (fun x => if Q2 ν (ofNat t) (ofNat x) = (ofNat c : Shell p) then 1 else 0) p) p
        = nsum (fun x => nsum (fun c => if Q2 ν (ofNat t) (ofNat x) = (ofNat c : Shell p) then 1 else 0) p) p :=
          nsum_comm (fun c x => if Q2 ν (ofNat t) (ofNat x) = (ofNat c : Shell p) then 1 else 0) p p
      _ = nsum (fun _ => 1) p := nsum_congr p h2
      _ = p := by rw [nsum_const, Nat.mul_one]
  calc nsum (fun c => planeCount ν (ofNat c)) p
      = nsum (fun t => nsum (fun c => nsum (fun x => if Q2 ν (ofNat t) (ofNat x) = (ofNat c : Shell p) then 1 else 0) p) p) p :=
        nsum_comm (fun c t => nsum (fun x => if Q2 ν (ofNat t) (ofNat x) = (ofNat c : Shell p) then 1 else 0) p) p p
    _ = nsum (fun _ => p) p := nsum_congr p h1
    _ = p * p := nsum_const p p

section frame
variable {κ : Nat} {g : Shell p}

/-- `x² = 0` only at `x = 0`. -/
theorem sq_eq_zero (F : Frame p κ g) {x : Shell p} : x * x = 0 ↔ x = 0 :=
  ⟨fun h => match F.mul_eq_zero h with | .inl h' => h' | .inr h' => h', fun h => by rw [h, mul_zero]⟩

/-- The row `t = 0` of the plane at `0`: one point, `x = 0`. -/
theorem row_zero (F : Frame p κ g) (ν : Shell p) :
    nsum (fun x => if Q2 ν 0 (ofNat x) = 0 then 1 else 0) p = 1 := by
  have e : ∀ x : Shell p, Q2 ν 0 x = 0 ↔ x = 0 := fun x => by
    unfold Q2
    rw [mul_zero, mul_zero, neg_zero, add_zero]
    exact sq_eq_zero F
  exact (nsum_congr p (fun x _ => ite_iff (e (ofNat x)) 1 0)).trans
    ((nsum_ind (fun x : Shell p => x = 0)).trans (count_eq _))

/-- 3:B4 — for a nonsquare `ν` the plane `x² − ν t²` vanishes only at the origin: one point. -/
theorem plane_zero_aniso (F : Frame p κ g) {ν : Shell p} (hν : ¬IsSquare ν) : planeCount ν 0 = 1 := by
  unfold planeCount
  rw [nsum_split (fun t => nsum (fun x => if Q2 ν t (ofNat x) = 0 then 1 else 0) p)]
  have hrow : ∀ l, l < p - 1 → nsum (fun x => if Q2 ν (ofNat (l + 1)) (ofNat x) = 0 then 1 else 0) p = 0 := by
    intro l hl
    have e : ∀ x, x < p → (if Q2 ν (ofNat (l + 1)) (ofNat x) = (0 : Shell p) then 1 else 0) = 0 := fun x _ =>
      ite_eq_right (fun h => by
        have h' : (ofNat x : Shell p) * ofNat x = ν * (ofNat (l + 1) * ofNat (l + 1)) := by
          unfold Q2 at h
          calc (ofNat x : Shell p) * ofNat x
              = ofNat x * ofNat x + -(ν * (ofNat (l + 1) * ofNat (l + 1))) + ν * (ofNat (l + 1) * ofNat (l + 1)) := by
                rw [add_assoc, neg_add, add_zero]
            _ = ν * (ofNat (l + 1) * ofNat (l + 1)) := by rw [h, zero_add]
        exact succ_ne_zero' hl (aniso_tx F hν h').1)
    rw [nsum_congr p e, nsum_zero]
  show nsum (fun x => if Q2 ν 0 (ofNat x) = 0 then 1 else 0) p + _ = 1
  rw [row_zero F ν, nsum_congr (p - 1) hrow, nsum_zero]

/-- 3:B4 — for a square `ν = w²`, `w ≠ 0`, the plane `x² − w² t²` vanishes on `2p − 1` points: the two lines
`x = ±wt`. -/
theorem plane_zero_split (F : Frame p κ g) {w : Shell p} (hw : w ≠ 0) : planeCount (w * w) 0 + 1 = 2 * p := by
  unfold planeCount
  rw [nsum_split (fun t => nsum (fun x => if Q2 (w * w) t (ofNat x) = 0 then 1 else 0) p)]
  have hrow : ∀ l, l < p - 1 → nsum (fun x => if Q2 (w * w) (ofNat (l + 1)) (ofNat x) = 0 then 1 else 0) p = 2 := by
    intro l hl
    have hb : w * ofNat (l + 1) ≠ 0 := F.mul_ne_zero hw (succ_ne_zero' hl)
    have e : ∀ x : Shell p, Q2 (w * w) (ofNat (l + 1)) x = 0 ↔ x * x = (w * ofNat (l + 1)) * (w * ofNat (l + 1)) :=
      fun x => by
        unfold Q2
        rw [sq_mul w (ofNat (l + 1)), mul_assoc]
        exact ⟨fun h => by
            calc x * x = x * x + -(w * (w * (ofNat (l + 1) * ofNat (l + 1)))) + w * (w * (ofNat (l + 1) * ofNat (l + 1))) := by
                  rw [add_assoc, neg_add, add_zero]
              _ = w * (w * (ofNat (l + 1) * ofNat (l + 1))) := by rw [h, zero_add],
          fun h => by rw [h, add_neg]⟩
    exact (nsum_congr p (fun x _ => ite_iff (e (ofNat x)) 1 0)).trans
      ((nsum_ind (fun x : Shell p => x * x = (w * ofNat (l + 1)) * (w * ofNat (l + 1)))).trans (count_sq F hb))
  show nsum (fun x => if Q2 (w * w) 0 (ofNat x) = 0 then 1 else 0) p + _ + 1 = 2 * p
  rw [row_zero F (w * w), nsum_congr (p - 1) hrow, nsum_const]
  have hp : (p - 1) + 1 = p := FRC.Nat.sub_add_cancel Pos.pos
  calc 1 + (p - 1) * 2 + 1 = ((p - 1) + 1) * 2 := by rw [Nat.succ_mul, Nat.add_comm 1, Nat.add_assoc]
    _ = 2 * p := by rw [hp, Nat.mul_comm]

/-! ## The four-dimensional form -/

/-- `#{(t, x, y, z) : x² − ν t² + y² + z² = a}`. -/
def formCount (ν a : Shell p) : Nat :=
  nsum (fun t => nsum (fun x => nsum (fun y => count (fun z =>
    ofNat y * ofNat y + z * z = a + -(Q2 ν (ofNat t) (ofNat x)))) p) p) p

/-- The count of `Q_ν = a` is `p²(p − 1) + p` times the plane's count at `a`. -/
theorem form_count (F : Frame p κ g) (ν a : Shell p) : formCount ν a = p * p * (p - 1) + p * planeCount ν a := by
  unfold formCount planeCount
  have hx : ∀ t x, nsum (fun y => count (fun z => ofNat y * ofNat y + z * z = a + -(Q2 ν (ofNat t) (ofNat x)))) p
      = (p - 1) + p * (if Q2 ν (ofNat t) (ofNat x) = a then 1 else 0) := fun t x => by
    rw [conic_count F]
    congr 1
    have hiff : a + -(Q2 ν (ofNat t) (ofNat x)) = 0 ↔ Q2 ν (ofNat t) (ofNat x) = a := ⟨fun h => by
        calc Q2 ν (ofNat t) (ofNat x) = Q2 ν (ofNat t) (ofNat x) + (a + -(Q2 ν (ofNat t) (ofNat x))) := by rw [h, add_zero]
          _ = a := by rw [add_left_comm, add_neg, add_zero],
      fun h => by rw [h, add_neg]⟩
    match (inferInstance : Decidable (Q2 ν (ofNat t) (ofNat x) = a)) with
    | isTrue h => rw [ite_eq_left (hiff.2 h), ite_eq_left h, Nat.mul_one]
    | isFalse h => rw [ite_eq_right (fun h' => h (hiff.1 h')), ite_eq_right h, Nat.mul_zero]
  have ht : ∀ t, t < p → nsum (fun x => nsum (fun y => count (fun z =>
      ofNat y * ofNat y + z * z = a + -(Q2 ν (ofNat t) (ofNat x)))) p) p
      = p * (p - 1) + p * nsum (fun x => if Q2 ν (ofNat t) (ofNat x) = a then 1 else 0) p := fun t _ => by
    rw [nsum_congr p (fun x _ => hx t x), nsum_add, nsum_const, nsum_mul_left]
  rw [nsum_congr p ht, nsum_add, nsum_const, nsum_mul_left, Nat.mul_assoc]

/-- 3:B4, 3:B7, 3:E1 — the null cone of `Q_ν` for a nonsquare `ν`: `p³ − p² + p` points, the elliptic count (written
`N + p² = p³ + p`). -/
theorem null_elliptic (F : Frame p κ g) {ν : Shell p} (hν : ¬IsSquare ν) : formCount ν 0 + p * p = p * p * p + p := by
  rw [form_count F, plane_zero_aniso F hν, Nat.mul_one, Nat.add_right_comm, ← Nat.mul_succ]
  show p * p * ((p - 1) + 1) + p = p * p * p + p
  rw [FRC.Nat.sub_add_cancel Pos.pos]

/-- 3:B4, 3:B2 — the null cone of `Q_ν` for a square `ν = w²`, `w ≠ 0`: `p³ + p² − p` points, the hyperbolic count
(written `N + p = p³ + p²`). -/
theorem null_hyperbolic (F : Frame p κ g) {w : Shell p} (hw : w ≠ 0) :
    formCount (w * w) 0 + p = p * p * p + p * p := by
  rw [form_count F]
  have h := plane_zero_split F hw
  have hp : (p - 1) + 1 = p := FRC.Nat.sub_add_cancel Pos.pos
  calc p * p * (p - 1) + p * planeCount (w * w) 0 + p = p * p * (p - 1) + p * (planeCount (w * w) 0 + 1) := by
        rw [Nat.mul_add, Nat.mul_one, Nat.add_assoc]
    _ = p * p * (p - 1) + p * p + p * p := by rw [h, Nat.mul_comm 2 p, ← Nat.mul_assoc, Nat.mul_two, Nat.add_assoc]
    _ = p * p * ((p - 1) + 1) + p * p := by rw [← Nat.mul_succ]
    _ = p * p * p + p * p := by rw [hp]

end frame

/-! ## The plane takes every nonzero value equally often (the drive) -/

/-- The plane form under the scaling `(t, x) ↦ (wt, wx)`: `Q₂(wt, wx) = w² Q₂(t, x)`. -/
theorem q2_scale (ν w t x : Shell p) : Q2 ν (w * t) (w * x) = w * w * Q2 ν t x := by
  unfold Q2
  exact Shell.Frame.RE.sound (Shell.Frame.look [w, x, ν, t])
    (.add (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1))) (.neg (.mul (.var 2) (.mul (.mul (.var 0) (.var 3)) (.mul (.var 0) (.var 3))))))
    (.mul (.mul (.var 0) (.var 0)) (.add (.mul (.var 1) (.var 1)) (.neg (.mul (.var 2) (.mul (.var 3) (.var 3))))))
    (by decide +kernel)

/-- The plane form under the swap `(t, x) ↦ (x, νt)`: `Q₂(x, νt) = −ν Q₂(t, x)`. -/
theorem q2_swap (ν t x : Shell p) : Q2 ν x (ν * t) = -(ν * Q2 ν t x) := by
  unfold Q2
  exact Shell.Frame.RE.sound (Shell.Frame.look [ν, t, x])
    (.add (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1))) (.neg (.mul (.var 0) (.mul (.var 2) (.var 2)))))
    (.neg (.mul (.var 0) (.add (.mul (.var 2) (.var 2)) (.neg (.mul (.var 0) (.mul (.var 1) (.var 1)))))))
    (by decide +kernel)

/-- Cancelling a positive factor in the naturals. -/
theorem nat_mul_left_cancel {a b c : Nat} (ha : 0 < a) (h : a * b = a * c) : b = c :=
  match Nat.lt_or_ge b c with
  | .inl hlt => absurd h (fun e => Nat.lt_irrefl (a * c) (by
      have := FRC.Nat.mul_lt_mul_of_lt_of_pos hlt ha
      rw [Nat.mul_comm b a, Nat.mul_comm c a, e] at this
      exact this))
  | .inr hge => match Nat.lt_or_ge c b with
    | .inl hlt => absurd h (fun e => Nat.lt_irrefl (a * b) (by
        have := FRC.Nat.mul_lt_mul_of_lt_of_pos hlt ha
        rw [Nat.mul_comm c a, Nat.mul_comm b a, ← e] at this
        exact this))
    | .inr hle => Nat.le_antisymm hle hge

section frame
variable {κ : Nat} {g : Shell p}

/-- `a·u = a·v` iff `u = v` for `a ≠ 0`. -/
theorem mul_cancel_iff (F : Frame p κ g) {a : Shell p} (ha : a ≠ 0) (u v : Shell p) : a * u = a * v ↔ u = v :=
  ⟨F.mul_left_cancel ha, fun h => by rw [h]⟩

/-- The scaling: the plane takes `w² c` as often as `c`, for `w ≠ 0`. -/
theorem plane_scale (F : Frame p κ g) {w : Shell p} (hw : w ≠ 0) (ν c : Shell p) :
    planeCount ν (w * w * c) = planeCount ν c := by
  obtain ⟨u, hu⟩ := F.exists_inv hw
  have hinv : ∀ y : Shell p, u * (w * y) = y := fun y => by rw [← mul_assoc, mul_comm u w, hu, one_mul]
  have hww : w * w ≠ 0 := F.mul_ne_zero hw hw
  unfold planeCount
  have step1 : ∀ t, t < p → nsum (fun x => if Q2 ν (ofNat t) (ofNat x) = c then 1 else 0) p
      = nsum (fun x => if Q2 ν (w * ofNat t) (w * ofNat x) = w * w * c then 1 else 0) p := fun t _ =>
    nsum_congr p (fun x _ => by
      rw [q2_scale]
      exact (ite_iff (mul_cancel_iff F hww _ _) 1 0).symm)
  have step2 : ∀ t, t < p → nsum (fun x => if Q2 ν (w * ofNat t) (w * ofNat x) = w * w * c then 1 else 0) p
      = nsum (fun x => if Q2 ν (w * ofNat t) (ofNat x) = w * w * c then 1 else 0) p := fun t _ =>
    nsum_bij (fun y => if Q2 ν (w * ofNat t) y = w * w * c then 1 else 0) (fun y => w * y) (fun y => u * y) hinv
  calc nsum (fun t => nsum (fun x => if Q2 ν (ofNat t) (ofNat x) = w * w * c then 1 else 0) p) p
      = nsum (fun t => (fun s : Shell p => nsum (fun x => if Q2 ν s (ofNat x) = w * w * c then 1 else 0) p) ((fun y => w * y) (ofNat t))) p :=
        (nsum_bij (fun s : Shell p => nsum (fun x => if Q2 ν s (ofNat x) = w * w * c then 1 else 0) p) (fun y => w * y) (fun y => u * y) hinv).symm
    _ = nsum (fun t => nsum (fun x => if Q2 ν (ofNat t) (ofNat x) = c then 1 else 0) p) p :=
        nsum_congr p (fun t ht => ((step1 t ht).trans (step2 t ht)).symm)

/-- The swap: the plane takes `−ν c` as often as `c`, for `ν ≠ 0`. -/
theorem plane_swap (F : Frame p κ g) {ν : Shell p} (hν : ν ≠ 0) (c : Shell p) :
    planeCount ν (-(ν * c)) = planeCount ν c := by
  obtain ⟨u, hu⟩ := F.exists_inv hν
  have hinv : ∀ y : Shell p, u * (ν * y) = y := fun y => by rw [← mul_assoc, mul_comm u ν, hu, one_mul]
  have hneg : -ν ≠ 0 := fun h => hν (by rw [← neg_neg ν, h, neg_zero])
  have hiff : ∀ q : Shell p, -(ν * q) = -(ν * c) ↔ q = c := fun q => by
    rw [neg_mul, neg_mul]; exact mul_cancel_iff F hneg q c
  unfold planeCount
  have step1 : ∀ t, t < p → nsum (fun x => if Q2 ν (ofNat t) (ofNat x) = c then 1 else 0) p
      = nsum (fun x => if Q2 ν (ofNat x) (ν * ofNat t) = -(ν * c) then 1 else 0) p := fun t _ =>
    nsum_congr p (fun x _ => by rw [q2_swap]; exact (ite_iff (hiff _) 1 0).symm)
  have step2 : ∀ x, x < p → nsum (fun t => if Q2 ν (ofNat x) (ν * ofNat t) = -(ν * c) then 1 else 0) p
      = nsum (fun t => if Q2 ν (ofNat x) (ofNat t) = -(ν * c) then 1 else 0) p := fun x _ =>
    nsum_bij (fun y => if Q2 ν (ofNat x) y = -(ν * c) then 1 else 0) (fun y => ν * y) (fun y => u * y) hinv
  calc nsum (fun t => nsum (fun x => if Q2 ν (ofNat t) (ofNat x) = -(ν * c) then 1 else 0) p) p
      = nsum (fun x => nsum (fun t => if Q2 ν (ofNat x) (ν * ofNat t) = -(ν * c) then 1 else 0) p) p :=
        (nsum_congr p step2).symm
    _ = nsum (fun t => nsum (fun x => if Q2 ν (ofNat x) (ν * ofNat t) = -(ν * c) then 1 else 0) p) p :=
        nsum_comm (fun x t => if Q2 ν (ofNat x) (ν * ofNat t) = -(ν * c) then 1 else 0) p p
    _ = nsum (fun t => nsum (fun x => if Q2 ν (ofNat t) (ofNat x) = c then 1 else 0) p) p :=
        nsum_congr p (fun t ht => (step1 t ht).symm)

/-- For the drive `g`, the plane takes every nonzero value as often as `1`. -/
theorem plane_const (F : Frame p κ g) {c : Shell p} (hc : c ≠ 0) : planeCount g c = planeCount g 1 := by
  have hg : g ≠ 0 := by have := F.pow_ne_zero 1; rw [Shell.pow_one] at this; exact this
  have hi : quarterTurn g κ ≠ 0 := fun h => F.one_ne_zero (by
    have := F.quarter_turn_sq
    rw [h, mul_zero] at this
    rw [← neg_neg (1 : Shell p), ← this, neg_zero])
  obtain ⟨k, _, hk⟩ := F.eq_pow_of_ne_zero hc
  obtain ⟨q, hq⟩ := FRC.Nat.mod_spec 2 (Nat.zero_lt_succ 1) k
  have hsq : ∀ j, g ^ (2 * j) = g ^ j * g ^ j := fun j => by rw [Nat.mul_comm, Shell.pow_mul, Shell.pow_two]
  have hwq : g ^ q ≠ 0 := F.pow_ne_zero q
  have h1 : planeCount g (-1) = planeCount g 1 := by
    rw [← F.quarter_turn_sq, ← mul_one (quarterTurn g κ * quarterTurn g κ)]
    exact plane_scale F hi g 1
  match mod_two_cases k with
  | .inl h0 =>
    rw [h0, Nat.add_zero] at hq
    rw [← hk, hq, hsq, ← mul_one (g ^ q * g ^ q)]
    exact plane_scale F hwq g 1
  | .inr h1' =>
    rw [h1'] at hq
    have e : c = g ^ q * g ^ q * g := by rw [← hk, hq, Shell.pow_add, hsq, Shell.pow_one]
    have eg : -(g * -1) = g := by rw [← mul_neg, neg_neg, mul_one]
    rw [e, plane_scale F hwq g g]
    calc planeCount g g = planeCount g (-(g * -1)) := by rw [eg]
      _ = planeCount g (-1) := plane_swap F hg (-1)
      _ = planeCount g 1 := h1

/-- 3:C2, 3:B6, 3:E1 — for the drive `g` the plane `x² − g t²` takes every nonzero value `p + 1` times: the norm-one cycle of
`𝔽_p(√g)` (the boosts, `γ² − g b² = 1`) has `p + 1` elements. -/
theorem plane_nonzero (F : Frame p κ g) {c : Shell p} (hc : c ≠ 0) : planeCount g c = p + 1 := by
  rw [plane_const F hc]
  have hgns : ¬IsSquare g := drive_nonsquare F
  have htot := plane_total g
  rw [nsum_split (fun c => planeCount g c), plane_zero_aniso F hgns,
    nsum_congr (p - 1) (fun l hl => plane_const F (succ_ne_zero' hl)), nsum_const] at htot
  have hp : (p - 1) + 1 = p := FRC.Nat.sub_add_cancel Pos.pos
  have e : 1 + (p - 1) * (p - 1 + 1 + 1) = p * p := by
    calc 1 + (p - 1) * (p - 1 + 1 + 1) = (p - 1) * (p - 1) + (p - 1) + ((p - 1) + 1) := by
          rw [Nat.mul_succ, Nat.mul_succ, Nat.add_comm 1, Nat.add_assoc ((p - 1) * (p - 1) + (p - 1))]
      _ = ((p - 1) + 1) * ((p - 1) + 1) := by rw [Nat.succ_mul, Nat.mul_succ]
      _ = p * p := by rw [hp]
  have h2 : (p - 1) * planeCount g 1 = (p - 1) * (p - 1 + 1 + 1) :=
    FRC.Nat.add_left_cancel (htot.trans e.symm)
  rw [nat_mul_left_cancel F.n_pos h2, hp]

/-- 3:B6 — for the drive `g` every nonzero value of `Q_g = −g t² + x² + y² + z²` is taken `p³ + p` times; at `a = −g`
this is the time sphere, whose `p³ + p` points times `|O(3, 𝔽_p)| = 2p(p² − 1)` give `|O₄⁻(p)| = 2p²(p⁴ − 1)`. -/
theorem sphere_drive (F : Frame p κ g) {a : Shell p} (ha : a ≠ 0) : formCount g a = p * p * p + p := by
  rw [form_count F, plane_nonzero F ha, Nat.mul_succ, ← Nat.add_assoc, ← Nat.mul_succ]
  show p * p * ((p - 1) + 1) + p = p * p * p + p
  rw [FRC.Nat.sub_add_cancel Pos.pos]

end frame

/-! ## The causal classes, the pair algebra, the boost in dimension `1 + 3` -/

section frame
variable {κ : Nat} {g : Shell p}

/-- 3:B7, 3:E1 — the similitude `(t, x, y, z) ↦ (cz, ax − by, bx + ay, cνt)` with `a² + b² = ν` and `c² = −1` multiplies
`Q_ν = −ν t² + x² + y² + z²` by `ν`. -/
theorem similitude (ν a b c t x y z : Shell p) (hab : a * a + b * b = ν) (hc : c * c = -1) :
    -(ν * ((c * z) * (c * z))) + (a * x + -(b * y)) * (a * x + -(b * y)) + (b * x + a * y) * (b * x + a * y)
      + (c * (ν * t)) * (c * (ν * t))
      = ν * (-(ν * (t * t)) + x * x + y * y + z * z) := by
  have e : -(ν * ((c * z) * (c * z))) + (a * x + -(b * y)) * (a * x + -(b * y)) + (b * x + a * y) * (b * x + a * y)
      + (c * (ν * t)) * (c * (ν * t))
      = ν * (-(ν * (t * t)) + x * x + y * y + z * z) + (c * c + 1) * (ν * ν * (t * t) + -(ν * (z * z)))
        + (a * a + b * b + -ν) * (x * x + y * y) :=
    Shell.Frame.RE.sound (Shell.Frame.look [ν, a, b, c, t, x, y, z])
      (.add (.add (.add (.neg (.mul (.var 0) (.mul (.mul (.var 3) (.var 7)) (.mul (.var 3) (.var 7)))))
        (.mul (.add (.mul (.var 1) (.var 5)) (.neg (.mul (.var 2) (.var 6)))) (.add (.mul (.var 1) (.var 5)) (.neg (.mul (.var 2) (.var 6))))))
        (.mul (.add (.mul (.var 2) (.var 5)) (.mul (.var 1) (.var 6))) (.add (.mul (.var 2) (.var 5)) (.mul (.var 1) (.var 6)))))
        (.mul (.mul (.var 3) (.mul (.var 0) (.var 4))) (.mul (.var 3) (.mul (.var 0) (.var 4)))))
      (.add (.add (.mul (.var 0) (.add (.add (.add (.neg (.mul (.var 0) (.mul (.var 4) (.var 4)))) (.mul (.var 5) (.var 5))) (.mul (.var 6) (.var 6))) (.mul (.var 7) (.var 7))))
        (.mul (.add (.mul (.var 3) (.var 3)) .one) (.add (.mul (.mul (.var 0) (.var 0)) (.mul (.var 4) (.var 4))) (.neg (.mul (.var 0) (.mul (.var 7) (.var 7)))))))
        (.mul (.add (.add (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.neg (.var 0))) (.add (.mul (.var 5) (.var 5)) (.mul (.var 6) (.var 6)))))
      (by decide +kernel)
  have h1 : c * c + 1 = 0 := by rw [hc, neg_add]
  have h2 : a * a + b * b + -ν = 0 := by rw [hab, add_neg]
  rw [e, h1, h2, zero_mul, zero_mul, add_zero, add_zero]

/-- 3:B7, 3:E1 — multiplication by the drive exchanges the two square classes of the nonzero residues. -/
theorem class_flip (F : Frame p κ g) {s : Shell p} (hs : s ≠ 0) : IsSquare s ↔ ¬IsSquare (g * s) := by
  obtain ⟨k, _, hk⟩ := F.eq_pow_of_ne_zero hs
  have hgs : g * s = g ^ (k + 1) := by rw [← hk, Shell.pow_succ, mul_comm]
  constructor
  · intro hsq hgsq
    have h0 : k % 2 = 0 := (parity_iff F k).1 (match hsq with | ⟨y, hy⟩ => ⟨y, hy.trans hk.symm⟩)
    have h1 : (k + 1) % 2 = 0 := (parity_iff F (k + 1)).1 (match hgsq with | ⟨y, hy⟩ => ⟨y, hy.trans hgs⟩)
    have h2 := (succ_mod_two_eq_zero_iff k).1 h1
    rw [h0] at h2
    exact Nat.noConfusion h2
  · intro hn
    match mod_two_cases k with
    | .inl h0 => exact match (parity_iff F k).2 h0 with | ⟨y, hy⟩ => ⟨y, hy.trans hk⟩
    | .inr h1 => exact absurd (match (parity_iff F (k + 1)).2 ((succ_mod_two_eq_zero_iff k).2 h1) with
        | ⟨y, hy⟩ => ⟨y, hy.trans hgs.symm⟩) hn

/-- 3:B8 — the drive cycle `𝔽_p^×` meets the norm-one cycle of `𝔽_p(√ν)` in `±1`: `γ² − ν·0² = 1` forces `γ = ±1`. -/
theorem drive_meets_norm_one (F : Frame p κ g) {ν γ : Shell p} (h : γ * γ + -(ν * (0 * 0)) = 1) : γ = 1 ∨ γ = -1 := by
  rw [mul_zero, mul_zero, neg_zero, add_zero] at h
  exact ((root_pair F 1 1 (mul_one 1) F.one_ne_zero).1 γ).1 h

/-- 3:C4 — the `x`-boost `Λ ⊕ I₂` lies in `O(Q_ν, 𝔽_p)` on every shell: it preserves `x² − ν t² + y² + z²`. -/
theorem xboost_preserves {ν γ b : Shell p} (h : γ * γ + -(ν * (b * b)) = 1) (t x y z : Shell p) :
    Q2 ν (boostT ν γ b t x) (boostX ν γ b t x) + (y * y + z * z) = Q2 ν t x + (y * y + z * z) := by
  rw [boost_preserves h]

end frame

/-! ## The generation of the Lorentz group of the shell: the reduction to a spatial vector -/

section frame
variable {κ : Nat} {g : Shell p}

/-- 3:C4 — the square shift: for `t ≠ 0` the residue `x = (1 + g t²)/2` makes `x² − g t²` the nonzero square `y²`,
`y = (g t² − 1)/2`; `y ≠ 0` since `g t² = 1` would make the drive a square. -/
theorem square_shift (F : Frame p κ g) {t : Shell p} (ht : t ≠ 0) :
    ∃ x y : Shell p, y ≠ 0 ∧ x * x + -(g * (t * t)) = y * y := by
  obtain ⟨h, hh⟩ := F.exists_inv F.two_ne_zero
  have h2 : h + h = 1 := by rw [← two_mul', hh]
  let u := g * (t * t)
  have e : ((1 + u) * h) * ((1 + u) * h) + -u = ((u + -1) * h) * ((u + -1) * h) + u * ((h + h) * (h + h) + -1) :=
    Shell.Frame.RE.sound (Shell.Frame.look [u, h])
      (.add (.mul (.mul (.add .one (.var 0)) (.var 1)) (.mul (.add .one (.var 0)) (.var 1))) (.neg (.var 0)))
      (.add (.mul (.mul (.add (.var 0) (.neg .one)) (.var 1)) (.mul (.add (.var 0) (.neg .one)) (.var 1)))
        (.mul (.var 0) (.add (.mul (.add (.var 1) (.var 1)) (.add (.var 1) (.var 1))) (.neg .one))))
      (by decide +kernel)
  refine ⟨(1 + u) * h, (u + -1) * h, fun hy => ?_, ?_⟩
  · have hh0 : h ≠ 0 := fun h0 => F.one_ne_zero (by rw [← hh, h0, mul_zero])
    have hu : u + -1 = 0 := match F.mul_eq_zero hy with
      | .inl e1 => e1
      | .inr e2 => absurd e2 hh0
    have hu1 : g * (t * t) = 1 := by
      calc g * (t * t) = u + -1 + 1 := by rw [add_assoc, neg_add, add_zero]
        _ = 1 := by rw [hu, zero_add]
    obtain ⟨s, hs⟩ := F.exists_inv ht
    exact drive_nonsquare F ⟨s, by
      calc s * s = g * (t * t) * (s * s) := by rw [hu1, one_mul]
        _ = g * ((t * s) * (t * s)) := by rw [mul_assoc, sq_mul t s]
        _ = g := by rw [hs, mul_one, mul_one]⟩
  · rw [e, h2, mul_one, add_neg, mul_zero, add_zero]

/-- 3:C4 — the boosts act transitively on each level set of the plane `x² − g t² = m`, `m ≠ 0`: the boost
`γ = (x₂x₁ − g t₂t₁)/m`, `b = (t₂x₁ − x₂t₁)/m` (the quotient of the two points in `𝔽_p(√g)`) carries `(t₁, x₁)` to
`(t₂, x₂)`. -/
theorem boost_transitive (F : Frame p κ g) {t₁ x₁ t₂ x₂ : Shell p}
    (hm : Q2 g t₁ x₁ ≠ 0) (h12 : Q2 g t₁ x₁ = Q2 g t₂ x₂) :
    ∃ γ b : Shell p, γ * γ + -(g * (b * b)) = 1 ∧ boostT g γ b t₁ x₁ = t₂ ∧ boostX g γ b t₁ x₁ = x₂ := by
  obtain ⟨n, hn⟩ := F.exists_inv hm
  let m := Q2 g t₁ x₁
  have hm1 : m = x₁ * x₁ + -(g * (t₁ * t₁)) := rfl
  have hm2 : m = x₂ * x₂ + -(g * (t₂ * t₂)) := h12
  refine ⟨(x₂ * x₁ + -(g * (t₂ * t₁))) * n, (t₂ * x₁ + -(x₂ * t₁)) * n, ?_, ?_, ?_⟩
  · -- Brahmagupta: (x₂x₁ − g t₂t₁)² − g (t₂x₁ − x₂t₁)² = (x₂² − g t₂²)(x₁² − g t₁²)
    have e : ((x₂ * x₁ + -(g * (t₂ * t₁))) * n) * ((x₂ * x₁ + -(g * (t₂ * t₁))) * n)
        + -(g * (((t₂ * x₁ + -(x₂ * t₁)) * n) * ((t₂ * x₁ + -(x₂ * t₁)) * n)))
        = ((x₂ * x₂ + -(g * (t₂ * t₂))) * n) * ((x₁ * x₁ + -(g * (t₁ * t₁))) * n) :=
      Shell.Frame.RE.sound (Shell.Frame.look [x₁, t₁, x₂, t₂, g, n])
        (.add (.mul (.mul (.add (.mul (.var 2) (.var 0)) (.neg (.mul (.var 4) (.mul (.var 3) (.var 1))))) (.var 5))
                    (.mul (.add (.mul (.var 2) (.var 0)) (.neg (.mul (.var 4) (.mul (.var 3) (.var 1))))) (.var 5)))
              (.neg (.mul (.var 4) (.mul (.mul (.add (.mul (.var 3) (.var 0)) (.neg (.mul (.var 2) (.var 1)))) (.var 5))
                    (.mul (.add (.mul (.var 3) (.var 0)) (.neg (.mul (.var 2) (.var 1)))) (.var 5))))))
        (.mul (.mul (.add (.mul (.var 2) (.var 2)) (.neg (.mul (.var 4) (.mul (.var 3) (.var 3))))) (.var 5))
              (.mul (.add (.mul (.var 0) (.var 0)) (.neg (.mul (.var 4) (.mul (.var 1) (.var 1))))) (.var 5)))
        (by decide +kernel)
    rw [e, ← hm2, ← hm1]
    show Q2 g t₁ x₁ * n * (Q2 g t₁ x₁ * n) = 1
    rw [hn, mul_one]
  · -- γ t₁ + b x₁ = t₂ (x₁² − g t₁²) / m
    unfold boostT
    have e : ((x₂ * x₁ + -(g * (t₂ * t₁))) * n) * t₁ + ((t₂ * x₁ + -(x₂ * t₁)) * n) * x₁
        = t₂ * ((x₁ * x₁ + -(g * (t₁ * t₁))) * n) :=
      Shell.Frame.RE.sound (Shell.Frame.look [x₁, t₁, x₂, t₂, g, n])
        (.add (.mul (.mul (.add (.mul (.var 2) (.var 0)) (.neg (.mul (.var 4) (.mul (.var 3) (.var 1))))) (.var 5)) (.var 1))
              (.mul (.mul (.add (.mul (.var 3) (.var 0)) (.neg (.mul (.var 2) (.var 1)))) (.var 5)) (.var 0)))
        (.mul (.var 3) (.mul (.add (.mul (.var 0) (.var 0)) (.neg (.mul (.var 4) (.mul (.var 1) (.var 1))))) (.var 5)))
        (by decide +kernel)
    rw [e, ← hm1]
    show _ * (Q2 g t₁ x₁ * n) = _
    rw [hn, mul_one]
  · -- γ x₁ + g b t₁ = x₂ (x₁² − g t₁²) / m
    unfold boostX
    have e : ((x₂ * x₁ + -(g * (t₂ * t₁))) * n) * x₁ + g * (((t₂ * x₁ + -(x₂ * t₁)) * n) * t₁)
        = x₂ * ((x₁ * x₁ + -(g * (t₁ * t₁))) * n) :=
      Shell.Frame.RE.sound (Shell.Frame.look [x₁, t₁, x₂, t₂, g, n])
        (.add (.mul (.mul (.add (.mul (.var 2) (.var 0)) (.neg (.mul (.var 4) (.mul (.var 3) (.var 1))))) (.var 5)) (.var 0))
              (.mul (.var 4) (.mul (.mul (.add (.mul (.var 3) (.var 0)) (.neg (.mul (.var 2) (.var 1)))) (.var 5)) (.var 1))))
        (.mul (.var 2) (.mul (.add (.mul (.var 0) (.var 0)) (.neg (.mul (.var 4) (.mul (.var 1) (.var 1))))) (.var 5)))
        (by decide +kernel)
    rw [e, ← hm1]
    show _ * (Q2 g t₁ x₁ * n) = _
    rw [hn, mul_one]

/-- 3:C4 — time to space: for `t ≠ 0` there are a residue `x` and a boost carrying `(t, x)` to `(0, y)` with `y ≠ 0`.
With the spatial rotations, which give the spatial part any `x`-component (Witt), every non-null vector of `Q_g` is
carried to a spatial one; the conjugates of the spatial reflections are then all the reflections, which generate
`O(Q_g, 𝔽_p)` (Cartan–Dieudonné). -/
theorem time_to_space (F : Frame p κ g) {t : Shell p} (ht : t ≠ 0) :
    ∃ x y γ b : Shell p, y ≠ 0 ∧ γ * γ + -(g * (b * b)) = 1 ∧ boostT g γ b t x = 0 ∧ boostX g γ b t x = y := by
  obtain ⟨x, y, hy, hxy⟩ := square_shift F ht
  have hq : Q2 g t x = Q2 g 0 y := by
    show x * x + -(g * (t * t)) = y * y + -(g * (0 * 0))
    rw [hxy, mul_zero, mul_zero, neg_zero, add_zero]
  have hm : Q2 g t x ≠ 0 := by
    rw [hq]; show y * y + -(g * (0 * 0)) ≠ 0
    rw [mul_zero, mul_zero, neg_zero, add_zero]
    exact fun h => hy ((sq_eq_zero F).1 h)
  obtain ⟨γ, b, hγ, h1, h2⟩ := boost_transitive F hm hq
  exact ⟨x, y, γ, b, hy, hγ, h1, h2⟩

end frame

/-! ## The window and the temporal fibres -/

/-- 3:E3 — no point off the real cone inside the window. Read an integer point `(t, x, y, z)` through the absolute
values of its coordinates, each at most `R`, with `3R² < p` and `νR² < p`. If `x² + y² + z² ≡ ν t² (mod p)`, that is
`Q_ν ≡ 0`, then `x² + y² + z² = ν t²`: the point lies on the real cone of the integral form. -/
theorem window_exact {p ν R x y z t : Nat} (hx : x ≤ R) (hy : y ≤ R) (hz : z ≤ R) (ht : t ≤ R)
    (h3 : R * R + R * R + R * R < p) (hν : ν * (R * R) < p)
    (h : (x * x + y * y + z * z) % p = (ν * (t * t)) % p) : x * x + y * y + z * z = ν * (t * t) := by
  have hs : x * x + y * y + z * z < p :=
    Nat.lt_of_le_of_lt (Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul hx hx) (Nat.mul_le_mul hy hy))
      (Nat.mul_le_mul hz hz)) h3
  have hu : ν * (t * t) < p := Nat.lt_of_le_of_lt (Nat.mul_le_mul_left ν (Nat.mul_le_mul ht ht)) hν
  rw [Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hu] at h
  exact h

/-- 3:E3 — the window is sharp below `√p`. When `p = a² + b²` with `a > 0`, the point `(t, x, y, z) = (0, a, b, 0)`
satisfies `x² + y² + z² ≡ ν t² (mod p)` but not `x² + y² + z² = ν t²`: a null point of the shell off the real cone,
with coordinates at most `b` and `b² < p`. -/
theorem window_ghost {p ν a b : Nat} (ha : 0 < a) (hp : a * a + b * b = p) :
    (a * a + b * b + 0 * 0) % p = (ν * (0 * 0)) % p ∧ a * a + b * b + 0 * 0 ≠ ν * (0 * 0) ∧ b * b < p := by
  have haa : 0 < a * a := Nat.mul_pos ha ha
  have hp0 : 0 < p := hp ▸ Nat.lt_of_lt_of_le haa (Nat.le_add_right (a * a) (b * b))
  have e1 : a * a + b * b + 0 * 0 = p := by rw [Nat.mul_zero, Nat.add_zero, hp]
  have e2 : ν * (0 * 0) = 0 := Nat.mul_zero ν
  rw [e1, e2]
  refine ⟨?_, ?_, ?_⟩
  · rw [Nat.mod_self, Nat.zero_mod]
    exact hp0
  · exact fun h => Nat.lt_irrefl 0 (h ▸ hp0)
  · exact hp ▸ Nat.lt_add_of_pos_left haa

/-- 3:E4 — the null cone over the temporal plane: above each pair `(t, x)` lie `p − 1` null points of `Q_g`, and
`2p − 1` above the origin, since the plane `x² − g t²` vanishes only at the origin. -/
theorem temporal_fiber (F : Frame p κ g) (t x : Shell p) :
    nsum (fun y => count (fun z => ofNat y * ofNat y + z * z = 0 + -(Q2 g t x))) p
      = (p - 1) + (if t = 0 ∧ x = 0 then p else 0) := by
  rw [conic_count F]
  have hiff : (0 : Shell p) + -(Q2 g t x) = 0 ↔ (t = 0 ∧ x = 0) := ⟨fun h => by
      have hq : Q2 g t x = 0 := by
        calc Q2 g t x = Q2 g t x + (0 + -(Q2 g t x)) := by rw [h, add_zero]
          _ = 0 := by rw [zero_add, add_neg]
      have h' : x * x = g * (t * t) := by
        unfold Q2 at hq
        calc x * x = x * x + -(g * (t * t)) + g * (t * t) := by rw [add_assoc, neg_add, add_zero]
          _ = g * (t * t) := by rw [hq, zero_add]
      exact aniso_tx F (drive_nonsquare F) h',
    fun h => by
      have hq : Q2 g (0 : Shell p) 0 = 0 := by
        unfold Q2
        rw [mul_zero, mul_zero, neg_zero, add_zero]
      rw [h.1, h.2, hq, neg_zero, add_zero]⟩
  match (inferInstance : Decidable (t = 0 ∧ x = 0)) with
  | isTrue h => rw [ite_eq_left (hiff.2 h), ite_eq_left h]
  | isFalse h => rw [ite_eq_right (fun h' => h (hiff.1 h')), ite_eq_right h]

/-! ## The worked shells -/

/-- The frame of the laboratory Subject `𝔽₁₇₃`, drive `2`. -/
theorem frame173 : Frame 173 43 (2 : Shell 173) := ⟨rfl, Nat.zero_lt_succ 42, by decide +kernel⟩

/-- 3:D1 [value] — `𝔽₁₃`: `14` boosts, decided by the kernel. -/
theorem normOne13 : normOneCount 13 2 = 14 := by decide +kernel

/-- 3:D1 [value] — `𝔽₁₇₃`, drive `2`: the null cone of `Q_2` has `173³ − 173² + 173 = 5 147 961` points and the
boosts number `174`, from the general counts on the frame `(τ; 0, 1, 2)`. -/
theorem shell173 : formCount (2 : Shell 173) 0 + 173 * 173 = 173 * 173 * 173 + 173 ∧ planeCount (2 : Shell 173) 1 = 174 :=
  ⟨null_elliptic frame173 (drive_nonsquare frame173), plane_nonzero frame173 (by decide)⟩

end FRC.Causal
