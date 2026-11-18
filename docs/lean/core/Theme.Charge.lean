import FrcCore.Theme.Torus

/-!
# FrcCore.Theme.Charge — the units of the extension and the one charge system (27:C15, 27:C16)

`Theme/Torus.lean` states the split cycle and the unitary cycle of the extension `K = 𝔽_p[η]`, `η² = ν`, by their points
and periods. This file states how the two lie in the units of `K`, and the cycles of the hypercharge and of the charge
in the frame of rank five.

* **The square of a unit (27:C15).** For a unit `x = a + b η` with norm `N = a² − ν b²` and `k = 1/N`, the quotient
  `ratio ν a b k = x/σ(x) = x²/N` is a unitary point, `x² = N · ratio`, and `σ(x) x = N` lies in the shell
  (`unit_square`). The quotient is `1` exactly when `b = 0`, that is when `x` is a split point (`ratio_kernel`). The
  Cayley point of `s` is the quotient of `1 + s η` (`ratio_cay`), and `−1` is the quotient of `η` (`ratio_eta`); with
  `cycle_orders` every unitary point is such a quotient.
* **The two readings of a weight (27:C15).** With `p − 1 = 2m` and `p + 1 = 2m + 2`: readings `a < p − 1` and
  `b < p + 1` of equal parity are the readings of one exponent below `p² − 1` (`weights_lift_ge`, `weights_lift_lt`,
  `lift_below`), and the two
  readings of one exponent have equal parity (`weights_parity`). The Frobenius fixes a split point and inverts a
  unitary point, so `σ(x)ⁿ` is `xⁿ` on the split cycle and the inverse of `xⁿ` on the unitary cycle (`frobenius_readings`).
* **The rotations (27:C15).** With `i² = −1` in the shell and `a a' = 1`, the matrix of rows `(c, s)`, `(−s, c)` with
  `c = (a + a')/2`, `s = i (a' − a)/2` has `c² + s² = 1`, `c + i s = a`, `c − i s = a'`, and it carries `(1, i)` to
  `a (1, i)` and `(1, −i)` to `a' (1, −i)` (`rotation_cycle`); the matrices multiply as their parameters do (`rotation_mul`).
* **The hypercharge cycle and the charge cycle (27:C16).** For a unitary `w` the point
  `diag(σ(w)², σ(w)², σ(w)², w³, w³)` has determinant one, and it is the identity only for `w = 1`
  (`hypercharge_cycle`). The point `diag(u, u, u, σ(u)³, 1)` has determinant one, and its entry `σ(u)³` on the doublet
  is `1` exactly when `u³ = 1` (`charge_cycle`). On the sixteen states the weights of the two cycles are `6Y` and
  `−3Q`, the second `|S ∩ C| − 3 [3 ∈ S]` (`charge_weights`).
* **Powers (27:C16).** For `d ∣ p + 1`, `d > 1`, some unitary point is no `d`-th power of a unitary point
  (`not_all_powers`), by the generator of `Theme/Torus.lean`. Where `p + 2 = 3 j` every unitary point is a cube
  (`all_cubes`).
* **The classes of the unitary cycle (27:C16).** Every unitary point is a power of a generator (`generator_powers`).
  For `p + 1 = d m` the classes modulo the `d`-th powers are those of `u^0, …, u^(d−1)`, and they number `d`
  (`power_classes`). The sixth powers are the `d`-th powers for `d = gcd(6, p + 1)` (`sixth_powers`).
* **Determinants and squares (27:C16).** A scalar `s` multiplies a determinant of rank three by `s³` and of rank two
  by `s²` (`det_scale`). A point of the charge cycle whose determinant on the doublet is a sixth power is a square,
  and conversely (`charge_squares`).
* **The kernel of the product (27:C16).** The product of a hypercharge point with a pair of scalar matrices is the
  identity exactly on the triples `(w, w² I₃, σ(w)³ I₂)`, of determinants one exactly when `w⁶ = 1` (`product_kernel`).
  These `w` are the `d = gcd(6, p + 1)` powers `u^(m r)` of a generator (`sixth_roots`).
* **The centre of the colour frame (27:P10).** For a cube root of unity `x ≠ 1`, `x ^ n = 1` exactly when three
  divides `n` (`centre_weight`). A state of fewer than `p + 1` indices that the diagonal frame moves fix has equal net
  numbers of indices in the three colour directions (`colourless_indices`).
* **The Frobenius parity of a tally (27:C17).** An expression with integer coefficients commutes with the Frobenius
  (`tally_even`). The odd term of a plaquette and the determinant of an anti-Hermitian matrix are negated by it
  (`orientation_odd`, `antihermitian_det`), and the product of two such elements is fixed (`odd_product`).
* **The lift of one chronon (27:C15, 27:C4).** The entries of `diag(η, η⁻¹)`, their squares and their norms
  (`drive_lift`), and the rays that one chronon keeps (`fixed_rays`).
* **The commutant (27:C16).** A matrix of rank three that commutes with a diagonal matrix of three entries with
  invertible differences and with the two permutation matrices of adjacent directions is a scalar
  (`commutant_scalar`).

`unit_cycle` conjoins the clauses of row C15. Row C16 cites `one_charge_system` and the seven theorems above. No axioms.
-/

namespace FRC.Unitary

open FRC.Shell FRC.Shell.Frame FRC.Extension

variable {p : Nat} [Pos p] {ν : Shell p}

/-- The point `a + b η` of the extension. -/
def pt (ν a b : Shell p) : Ext p ν := ⟨a, b⟩

/-- The quotient `x/σ(x)` of the unit `x = a + b η`, with `k` the inverse of its norm `a² − ν b²`: `(a + b η)² · k`. -/
def ratio (ν a b k : Shell p) : Ext p ν := ⟨(a * a + ν * (b * b)) * k, (a * b + b * a) * k⟩

/-! ## The square of a unit -/

/-- 27:C15 — the square of a unit: the quotient `x/σ(x)` is unitary, the square of the unit is its norm times that
quotient, and its norm `σ(x) x` lies in the shell. -/
theorem unit_square {a b k : Shell p} (hk : (a * a + -(ν * (b * b))) * k = 1) :
    Ext.conj (ratio ν a b k) * ratio ν a b k = 1 ∧
    pt ν a b * pt ν a b = pt ν (a * a + -(ν * (b * b))) 0 * ratio ν a b k ∧
    Ext.conj (pt ν a b) * pt ν a b = pt ν (a * a + -(ν * (b * b))) 0 := by
  refine ⟨Ext.ext ?_ ?_, Ext.ext ?_ ?_, Ext.ext ?_ ?_⟩
  · have e : (((((a * a) + (ν * (b * b))) * k) * (((a * a) + (ν * (b * b))) * k)) + (ν * (-(((a * b) + (b * a)) * k) * (((a * b) + (b * a)) * k)))) = ((((a * a) + -(ν * (b * b))) * k) * (((a * a) + -(ν * (b * b))) * k)) := Shell.Frame.RE.sound (Shell.Frame.look [ν, a, b, k]) (.add (.mul (.mul (.add (.mul (.var 1) (.var 1)) (.mul (.var 0) (.mul (.var 2) (.var 2)))) (.var 3)) (.mul (.add (.mul (.var 1) (.var 1)) (.mul (.var 0) (.mul (.var 2) (.var 2)))) (.var 3))) (.mul (.var 0) (.mul (.neg (.mul (.add (.mul (.var 1) (.var 2)) (.mul (.var 2) (.var 1))) (.var 3))) (.mul (.add (.mul (.var 1) (.var 2)) (.mul (.var 2) (.var 1))) (.var 3))))) (.mul (.mul (.add (.mul (.var 1) (.var 1)) (.neg (.mul (.var 0) (.mul (.var 2) (.var 2))))) (.var 3)) (.mul (.add (.mul (.var 1) (.var 1)) (.neg (.mul (.var 0) (.mul (.var 2) (.var 2))))) (.var 3))) (by decide +kernel)
    rw [hk, Shell.mul_one] at e
    exact e
  · exact Shell.Frame.RE.sound (Shell.Frame.look [ν, a, b, k]) (.add (.mul (.mul (.add (.mul (.var 1) (.var 1)) (.mul (.var 0) (.mul (.var 2) (.var 2)))) (.var 3)) (.mul (.add (.mul (.var 1) (.var 2)) (.mul (.var 2) (.var 1))) (.var 3))) (.mul (.neg (.mul (.add (.mul (.var 1) (.var 2)) (.mul (.var 2) (.var 1))) (.var 3))) (.mul (.add (.mul (.var 1) (.var 1)) (.mul (.var 0) (.mul (.var 2) (.var 2)))) (.var 3)))) .zero (by decide +kernel)
  · have e : ((((a * a) + -(ν * (b * b))) * (((a * a) + (ν * (b * b))) * k)) + (ν * (0 * (((a * b) + (b * a)) * k)))) = ((((a * a) + -(ν * (b * b))) * k) * ((a * a) + (ν * (b * b)))) := Shell.Frame.RE.sound (Shell.Frame.look [ν, a, b, k]) (.add (.mul (.add (.mul (.var 1) (.var 1)) (.neg (.mul (.var 0) (.mul (.var 2) (.var 2))))) (.mul (.add (.mul (.var 1) (.var 1)) (.mul (.var 0) (.mul (.var 2) (.var 2)))) (.var 3))) (.mul (.var 0) (.mul .zero (.mul (.add (.mul (.var 1) (.var 2)) (.mul (.var 2) (.var 1))) (.var 3))))) (.mul (.mul (.add (.mul (.var 1) (.var 1)) (.neg (.mul (.var 0) (.mul (.var 2) (.var 2))))) (.var 3)) (.add (.mul (.var 1) (.var 1)) (.mul (.var 0) (.mul (.var 2) (.var 2))))) (by decide +kernel)
    rw [hk, Shell.one_mul] at e
    exact e.symm
  · have e : ((((a * a) + -(ν * (b * b))) * (((a * b) + (b * a)) * k)) + (0 * (((a * a) + (ν * (b * b))) * k))) = ((((a * a) + -(ν * (b * b))) * k) * ((a * b) + (b * a))) := Shell.Frame.RE.sound (Shell.Frame.look [ν, a, b, k]) (.add (.mul (.add (.mul (.var 1) (.var 1)) (.neg (.mul (.var 0) (.mul (.var 2) (.var 2))))) (.mul (.add (.mul (.var 1) (.var 2)) (.mul (.var 2) (.var 1))) (.var 3))) (.mul .zero (.mul (.add (.mul (.var 1) (.var 1)) (.mul (.var 0) (.mul (.var 2) (.var 2)))) (.var 3)))) (.mul (.mul (.add (.mul (.var 1) (.var 1)) (.neg (.mul (.var 0) (.mul (.var 2) (.var 2))))) (.var 3)) (.add (.mul (.var 1) (.var 2)) (.mul (.var 2) (.var 1)))) (by decide +kernel)
    rw [hk, Shell.one_mul] at e
    exact e.symm
  · exact Shell.Frame.RE.sound (Shell.Frame.look [ν, a, b, k]) (.add (.mul (.var 1) (.var 1)) (.mul (.var 0) (.mul (.neg (.var 2)) (.var 2)))) (.add (.mul (.var 1) (.var 1)) (.neg (.mul (.var 0) (.mul (.var 2) (.var 2))))) (by decide +kernel)
  · exact Shell.Frame.RE.sound (Shell.Frame.look [ν, a, b, k]) (.add (.mul (.var 1) (.var 2)) (.mul (.neg (.var 2)) (.var 1))) .zero (by decide +kernel)

/-- 27:C15 — the quotient `x/σ(x)` of a unit is `1` exactly when the unit is a split point, `b = 0`. -/
theorem ratio_kernel (hp : FRC.Nat.isPrime p) (hν : ¬ ∃ y : Shell p, y * y = ν) (h2 : (1 : Shell p) + 1 ≠ 0)
    {a b k : Shell p} (hk : (a * a + -(ν * (b * b))) * k = 1) : ratio ν a b k = 1 ↔ b = 0 := by
  constructor
  · intro h
    have hre : (a * a + ν * (b * b)) * k = 1 := Ext.re_congr h
    have e : (((1 + 1) * ν) * ((b * b) * k)) = ((((a * a) + (ν * (b * b))) * k) + -(((a * a) + -(ν * (b * b))) * k)) := Shell.Frame.RE.sound (Shell.Frame.look [ν, a, b, k]) (.mul (.mul (.add .one .one) (.var 0)) (.mul (.mul (.var 2) (.var 2)) (.var 3))) (.add (.mul (.add (.mul (.var 1) (.var 1)) (.mul (.var 0) (.mul (.var 2) (.var 2)))) (.var 3)) (.neg (.mul (.add (.mul (.var 1) (.var 1)) (.neg (.mul (.var 0) (.mul (.var 2) (.var 2))))) (.var 3)))) (by decide +kernel)
    have e0 : (1 : Shell p) + -1 = 0 := Shell.Frame.RE.sound (Shell.Frame.look [ν]) (.add .one (.neg .one)) .zero (by decide +kernel)
    rw [hre, hk, e0] at e
    match Prime.mul_eq_zero hp e with
    | .inl h1 =>
      match Prime.mul_eq_zero hp h1 with
      | .inl h => exact absurd h h2
      | .inr h => exact absurd ⟨0, (Shell.zero_mul 0).trans h.symm⟩ hν
    | .inr h1 =>
      match Prime.mul_eq_zero hp h1 with
      | .inl hbb =>
        match Prime.mul_eq_zero hp hbb with
        | .inl h => exact h
        | .inr h => exact h
      | .inr hk0 => exact absurd (by rw [← hk, hk0, Shell.mul_zero]) (Prime.one_ne_zero hp)
  · intro hb
    subst hb
    refine Ext.ext ?_ ?_
    · have e : (((a * a) + (ν * (0 * 0))) * k) = (((a * a) + -(ν * (0 * 0))) * k) := Shell.Frame.RE.sound (Shell.Frame.look [ν, a, k]) (.mul (.add (.mul (.var 1) (.var 1)) (.mul (.var 0) (.mul .zero .zero))) (.var 2)) (.mul (.add (.mul (.var 1) (.var 1)) (.neg (.mul (.var 0) (.mul .zero .zero)))) (.var 2)) (by decide +kernel)
      exact e.trans hk
    · exact Shell.Frame.RE.sound (Shell.Frame.look [ν, a, k]) (.mul (.add (.mul (.var 1) .zero) (.mul .zero (.var 1))) (.var 2)) .zero (by decide +kernel)

/-- 27:C15 — the Cayley point of `s` is the quotient `x/σ(x)` of `x = 1 + s η`. -/
theorem ratio_cay (s : Shell p) : ratio ν 1 s ((1 + -(ν * (s * s))) ^ (p - 2)) = cay ν s := by
  refine Ext.ext ?_ ?_
  · show (1 * 1 + ν * (s * s)) * (1 + -(ν * (s * s))) ^ (p - 2) = (1 + ν * (s * s)) * (1 + -(ν * (s * s))) ^ (p - 2)
    rw [Shell.one_mul]
  · show (1 * s + s * 1) * (1 + -(ν * (s * s))) ^ (p - 2) = (s + s) * (1 + -(ν * (s * s))) ^ (p - 2)
    rw [Shell.one_mul, Shell.mul_one]

/-- 27:C15 — `−1` is the quotient `η/σ(η)`. -/
theorem ratio_eta (hp : FRC.Nat.isPrime p) (hν : ¬ ∃ y : Shell p, y * y = ν) :
    ratio ν 0 1 ((-ν) ^ (p - 2)) = -1 := by
  have hν0 : -ν ≠ 0 := fun h => by
    have e : (ν + -ν) = 0 := Shell.Frame.RE.sound (Shell.Frame.look [ν]) (.add (.var 0) (.neg (.var 0))) .zero (by decide +kernel)
    rw [h, Shell.add_zero] at e
    exact hν ⟨0, (Shell.zero_mul 0).trans e.symm⟩
  have hk := mul_pow_pred hp hν0
  refine Ext.ext ?_ ?_
  · have e : (((0 * 0) + (ν * (1 * 1))) * (-ν) ^ (p - 2)) = -(-ν * (-ν) ^ (p - 2)) := Shell.Frame.RE.sound (Shell.Frame.look [ν, (-ν) ^ (p - 2)]) (.mul (.add (.mul .zero .zero) (.mul (.var 0) (.mul .one .one))) (.var 1)) (.neg (.mul (.neg (.var 0)) (.var 1))) (by decide +kernel)
    rw [hk] at e
    exact e
  · exact Shell.Frame.RE.sound (Shell.Frame.look [ν, (-ν) ^ (p - 2)]) (.mul (.add (.mul .zero .one) (.mul .one .zero)) (.var 1)) (.neg .zero) (by decide +kernel)

/-! ## The two readings of a weight -/

/-- 27:C15 — an exponent `x + c y` with `x < c` and `y ≤ c + 1` is below `(c + 1)² − 1`; with `c = p − 1` the bound
is `p² − 1`, the number of the units of the extension. -/
theorem lift_below {x y c : Nat} (hx : x < c) (hy : y ≤ c + 1) : x + c * y + 1 < (c + 1) * (c + 1) := by
  have h1 : c * y ≤ c * (c + 1) := Nat.mul_le_mul_left c hy
  have h2 : x + 1 + c * y ≤ c + c * (c + 1) := Nat.add_le_add hx h1
  have h3 : c + c * (c + 1) < (c + 1) * (c + 1) := by
    rw [Nat.succ_mul c (c + 1), Nat.add_comm c]
    exact Nat.add_lt_add_left (Nat.lt_succ_self c) _
  rw [Nat.add_right_comm]
  exact Nat.lt_of_le_of_lt h2 h3

/-- 27:C15 — readings `a = b + 2t < p − 1 = 2m` on the split cycle and `b` on the unitary cycle, of order `2m + 2`, are
the readings of the exponent `a + 2m t = b + (2m + 2) t`, which is below `p² − 1 = (2m + 1)² − 1`. -/
theorem weights_lift_ge (m b t : Nat) (ha : b + 2 * t < 2 * m) :
    (b + 2 * t + (2 * m) * t) % (2 * m) = b + 2 * t ∧ (b + 2 * t + (2 * m) * t) % (2 * m + 2) = b ∧
    b + 2 * t + (2 * m) * t + 1 < (2 * m + 1) * (2 * m + 1) := by
  have ht : t ≤ 2 * m + 1 := by
    have h : t ≤ b + 2 * t := by
      rw [Nat.two_mul]
      exact Nat.le_trans (Nat.le_add_right t t) (Nat.le_add_left _ b)
    exact Nat.le_trans h (Nat.le_trans (Nat.le_of_lt ha) (Nat.le_succ _))
  have hb : b < 2 * m + 2 :=
    Nat.lt_of_le_of_lt (Nat.le_add_right b (2 * t)) (Nat.lt_of_lt_of_le ha (Nat.le_add_right (2 * m) 2))
  have e : (b + 2 * t) + (2 * m) * t = b + (2 * m + 2) * t := by
    rw [FRC.Nat.add_mul, Nat.add_assoc, Nat.add_comm (2 * t)]
  refine ⟨?_, ?_, ?_⟩
  · rw [Nat.add_comm, FRC.Nat.add_mul_mod_self_left _ _ _ (FRC.Nat.pos_of_lt ha)]
    exact FRC.Nat.mod_eq_of_lt ha
  · rw [e, Nat.add_comm, FRC.Nat.add_mul_mod_self_left _ _ _ (Nat.succ_pos _)]
    exact FRC.Nat.mod_eq_of_lt hb
  · exact lift_below ha ht

/-- 27:C15 — readings `a < p − 1 = 2(t + r)` on the split cycle and `b = a + 2t < p + 1` on the unitary cycle are the
readings of the exponent `a + (p − 1)(r + 1) = b + (p + 1) r`, which is below `p² − 1`. -/
theorem weights_lift_lt (a t r : Nat) (ha : a < 2 * (t + r)) (hb : a + 2 * t < 2 * (t + r) + 2) :
    (a + (2 * (t + r)) * (r + 1)) % (2 * (t + r)) = a ∧ (a + (2 * (t + r)) * (r + 1)) % (2 * (t + r) + 2) = a + 2 * t ∧
    a + (2 * (t + r)) * (r + 1) + 1 < (2 * (t + r) + 1) * (2 * (t + r) + 1) := by
  have hr : r + 1 ≤ 2 * (t + r) + 1 := by
    rw [Nat.two_mul]
    exact Nat.succ_le_succ (Nat.le_trans (Nat.le_add_left r t) (Nat.le_add_right _ _))
  have e : a + (2 * (t + r)) * (r + 1) = (a + 2 * t) + (2 * (t + r) + 2) * r := by
    rw [Nat.mul_succ, FRC.Nat.add_mul (2 * (t + r)) 2 r, Nat.mul_add 2 t r, Nat.add_assoc a (2 * t)]
    rw [Nat.add_left_comm (2 * t) ((2 * t + 2 * r) * r) (2 * r), Nat.add_comm (2 * t) (2 * r)]
  refine ⟨?_, ?_, ?_⟩
  · rw [Nat.add_comm, FRC.Nat.add_mul_mod_self_left _ _ _ (FRC.Nat.pos_of_lt ha)]
    exact FRC.Nat.mod_eq_of_lt ha
  · rw [e, Nat.add_comm, FRC.Nat.add_mul_mod_self_left _ _ _ (Nat.succ_pos _)]
    exact FRC.Nat.mod_eq_of_lt hb
  · exact lift_below ha hr

/-- 27:C15 — the two readings of one exponent, `a` modulo `2m` and `b` modulo `2m + 2`, have equal parity. -/
theorem weights_parity (m a b k j : Nat) (h : a + (2 * m) * k = b + (2 * m + 2) * j) : a % 2 = b % 2 := by
  have e1 : (a + (2 * m) * k) % 2 = a % 2 := by
    rw [FRC.Nat.mul_assoc, Nat.add_comm, FRC.Nat.add_mul_mod_self_left _ _ 2 (by decide)]
  have e2 : (b + (2 * m + 2) * j) % 2 = b % 2 := by
    rw [show 2 * m + 2 = 2 * (m + 1) from (Nat.mul_succ 2 m).symm, FRC.Nat.mul_assoc, Nat.add_comm,
      FRC.Nat.add_mul_mod_self_left _ _ 2 (by decide)]
  rw [← e1, h, e2]

/-- 27:C15 — the Frobenius fixes a split point and inverts a unitary point: `σ(a)ⁿ = aⁿ` for `a` in the shell, and
`σ(w)ⁿ wⁿ = 1` for a unitary `w`. -/
theorem frobenius_readings :
    (∀ (a : Shell p) (n : Nat), Ext.conj (pt ν a 0) ^ n = pt ν a 0 ^ n) ∧
    (∀ w : Ext p ν, Ext.conj w * w = 1 → ∀ n : Nat, Ext.conj w ^ n * w ^ n = 1) := by
  refine ⟨fun a n => ?_, fun w hw n => ?_⟩
  · have e : Ext.conj (pt ν a 0) = pt ν a 0 := Ext.ext rfl Shell.neg_zero
    rw [e]
  · rw [← conj_pow]
    exact unitary_pow hw n

/-! ## The rotations with entries of the shell -/

/-- 27:C15 — the rotation of the split point `a`, `a a' = 1`, with `i² = −1` and `t = 1/2` in the shell: its entries
`c = (a + a') t` and `s = i (a' − a) t` have `c² + s² = 1`, `c + i s = a`, `c − i s = a'`, `−s + c i = a i` and `−s − c i = −a' i`. -/
theorem rotation_cycle {i t a a' : Shell p} (hi : i * i + 1 = 0) (ht : (1 + 1) * t = 1) (ha : a * a' = 1) :
    ((a + a') * t) * ((a + a') * t) + (i * ((a' + -a) * t)) * (i * ((a' + -a) * t)) = 1 ∧
    (a + a') * t + i * (i * ((a' + -a) * t)) = a ∧
    (a + a') * t + -(i * (i * ((a' + -a) * t))) = a' ∧
    -(i * ((a' + -a) * t)) + ((a + a') * t) * i = a * i ∧
    -(i * ((a' + -a) * t)) + ((a + a') * t) * -i = a' * -i := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have e : ((((a + a') * t) * ((a + a') * t)) + ((i * ((a' + -a) * t)) * (i * ((a' + -a) * t)))) = (((((1 + 1) * t) * ((1 + 1) * t)) * (a * a')) + (((i * i) + 1) * (((a' + -a) * t) * ((a' + -a) * t)))) := Shell.Frame.RE.sound (Shell.Frame.look [i, t, a, a']) (.add (.mul (.mul (.add (.var 2) (.var 3)) (.var 1)) (.mul (.add (.var 2) (.var 3)) (.var 1))) (.mul (.mul (.var 0) (.mul (.add (.var 3) (.neg (.var 2))) (.var 1))) (.mul (.var 0) (.mul (.add (.var 3) (.neg (.var 2))) (.var 1))))) (.add (.mul (.mul (.mul (.add .one .one) (.var 1)) (.mul (.add .one .one) (.var 1))) (.mul (.var 2) (.var 3))) (.mul (.add (.mul (.var 0) (.var 0)) .one) (.mul (.mul (.add (.var 3) (.neg (.var 2))) (.var 1)) (.mul (.add (.var 3) (.neg (.var 2))) (.var 1))))) (by decide +kernel)
    rw [ht, ha, hi, Shell.mul_one, Shell.mul_one, Shell.zero_mul, Shell.add_zero] at e
    exact e
  · have e : (((a + a') * t) + (i * (i * ((a' + -a) * t)))) = ((((1 + 1) * t) * a) + (((i * i) + 1) * ((a' + -a) * t))) := Shell.Frame.RE.sound (Shell.Frame.look [i, t, a, a']) (.add (.mul (.add (.var 2) (.var 3)) (.var 1)) (.mul (.var 0) (.mul (.var 0) (.mul (.add (.var 3) (.neg (.var 2))) (.var 1))))) (.add (.mul (.mul (.add .one .one) (.var 1)) (.var 2)) (.mul (.add (.mul (.var 0) (.var 0)) .one) (.mul (.add (.var 3) (.neg (.var 2))) (.var 1)))) (by decide +kernel)
    rw [ht, hi, Shell.one_mul, Shell.zero_mul, Shell.add_zero] at e
    exact e
  · have e : (((a + a') * t) + -(i * (i * ((a' + -a) * t)))) = ((((1 + 1) * t) * a') + -(((i * i) + 1) * ((a' + -a) * t))) := Shell.Frame.RE.sound (Shell.Frame.look [i, t, a, a']) (.add (.mul (.add (.var 2) (.var 3)) (.var 1)) (.neg (.mul (.var 0) (.mul (.var 0) (.mul (.add (.var 3) (.neg (.var 2))) (.var 1)))))) (.add (.mul (.mul (.add .one .one) (.var 1)) (.var 3)) (.neg (.mul (.add (.mul (.var 0) (.var 0)) .one) (.mul (.add (.var 3) (.neg (.var 2))) (.var 1))))) (by decide +kernel)
    rw [ht, hi, Shell.one_mul, Shell.zero_mul, Shell.neg_zero, Shell.add_zero] at e
    exact e
  · have e : (-(i * ((a' + -a) * t)) + (((a + a') * t) * i)) = ((((1 + 1) * t) * a) * i) := Shell.Frame.RE.sound (Shell.Frame.look [i, t, a, a']) (.add (.neg (.mul (.var 0) (.mul (.add (.var 3) (.neg (.var 2))) (.var 1)))) (.mul (.mul (.add (.var 2) (.var 3)) (.var 1)) (.var 0))) (.mul (.mul (.mul (.add .one .one) (.var 1)) (.var 2)) (.var 0)) (by decide +kernel)
    rw [ht, Shell.one_mul] at e
    exact e
  · have e : (-(i * ((a' + -a) * t)) + (((a + a') * t) * -i)) = ((((1 + 1) * t) * a') * -i) := Shell.Frame.RE.sound (Shell.Frame.look [i, t, a, a']) (.add (.neg (.mul (.var 0) (.mul (.add (.var 3) (.neg (.var 2))) (.var 1)))) (.mul (.mul (.add (.var 2) (.var 3)) (.var 1)) (.neg (.var 0)))) (.mul (.mul (.mul (.add .one .one) (.var 1)) (.var 3)) (.neg (.var 0))) (by decide +kernel)
    rw [ht, Shell.one_mul] at e
    exact e

/-- 27:C15 — the rotations multiply as their split points do. -/
theorem rotation_mul {i t a a' b b' : Shell p} (hi : i * i + 1 = 0) (ht : (1 + 1) * t = 1) :
    ((a + a') * t) * ((b + b') * t) + -((i * ((a' + -a) * t)) * (i * ((b' + -b) * t))) = (a * b + a' * b') * t ∧
    (i * ((a' + -a) * t)) * ((b + b') * t) + ((a + a') * t) * (i * ((b' + -b) * t)) = i * ((a' * b' + -(a * b)) * t) := by
  refine ⟨?_, ?_⟩
  · have e : ((((a + a') * t) * ((b + b') * t)) + -((i * ((a' + -a) * t)) * (i * ((b' + -b) * t)))) = ((((1 + 1) * t) * (((a * b) + (a' * b')) * t)) + -(((i * i) + 1) * (((a' + -a) * t) * ((b' + -b) * t)))) := Shell.Frame.RE.sound (Shell.Frame.look [i, t, a, a', b, b']) (.add (.mul (.mul (.add (.var 2) (.var 3)) (.var 1)) (.mul (.add (.var 4) (.var 5)) (.var 1))) (.neg (.mul (.mul (.var 0) (.mul (.add (.var 3) (.neg (.var 2))) (.var 1))) (.mul (.var 0) (.mul (.add (.var 5) (.neg (.var 4))) (.var 1)))))) (.add (.mul (.mul (.add .one .one) (.var 1)) (.mul (.add (.mul (.var 2) (.var 4)) (.mul (.var 3) (.var 5))) (.var 1))) (.neg (.mul (.add (.mul (.var 0) (.var 0)) .one) (.mul (.mul (.add (.var 3) (.neg (.var 2))) (.var 1)) (.mul (.add (.var 5) (.neg (.var 4))) (.var 1)))))) (by decide +kernel)
    rw [ht, hi, Shell.one_mul, Shell.zero_mul, Shell.neg_zero, Shell.add_zero] at e
    exact e
  · have e : (((i * ((a' + -a) * t)) * ((b + b') * t)) + (((a + a') * t) * (i * ((b' + -b) * t)))) = (((1 + 1) * t) * (i * (((a' * b') + -(a * b)) * t))) := Shell.Frame.RE.sound (Shell.Frame.look [i, t, a, a', b, b']) (.add (.mul (.mul (.var 0) (.mul (.add (.var 3) (.neg (.var 2))) (.var 1))) (.mul (.add (.var 4) (.var 5)) (.var 1))) (.mul (.mul (.add (.var 2) (.var 3)) (.var 1)) (.mul (.var 0) (.mul (.add (.var 5) (.neg (.var 4))) (.var 1))))) (.mul (.mul (.add .one .one) (.var 1)) (.mul (.var 0) (.mul (.add (.mul (.var 3) (.var 5)) (.neg (.mul (.var 2) (.var 4)))) (.var 1)))) (by decide +kernel)
    rw [ht, Shell.one_mul] at e
    exact e

/-- 27:C15 — the units of the extension: the square of a unit with the kernel of the quotient `x/σ(x)`, the unitary points as such
quotients, the two readings of a weight, and the split cycle of the unitary frame as rotations with entries of the shell. -/
theorem unit_cycle (hp : FRC.Nat.isPrime p) (hν : ¬ ∃ y : Shell p, y * y = ν) (h2 : (1 : Shell p) + 1 ≠ 0) :
    (∀ a b k : Shell p, (a * a + -(ν * (b * b))) * k = 1 →
      Ext.conj (ratio ν a b k) * ratio ν a b k = 1 ∧
      pt ν a b * pt ν a b = pt ν (a * a + -(ν * (b * b))) 0 * ratio ν a b k ∧
      Ext.conj (pt ν a b) * pt ν a b = pt ν (a * a + -(ν * (b * b))) 0 ∧
      (ratio ν a b k = 1 ↔ b = 0)) ∧
    (∀ s : Shell p, ratio ν 1 s ((1 + -(ν * (s * s))) ^ (p - 2)) = cay ν s) ∧
    ratio ν 0 1 ((-ν) ^ (p - 2)) = -1 ∧
    (∀ m b t : Nat, b + 2 * t < 2 * m →
      (b + 2 * t + (2 * m) * t) % (2 * m) = b + 2 * t ∧ (b + 2 * t + (2 * m) * t) % (2 * m + 2) = b ∧
      b + 2 * t + (2 * m) * t + 1 < (2 * m + 1) * (2 * m + 1)) ∧
    (∀ a t r : Nat, a < 2 * (t + r) → a + 2 * t < 2 * (t + r) + 2 →
      (a + (2 * (t + r)) * (r + 1)) % (2 * (t + r)) = a ∧ (a + (2 * (t + r)) * (r + 1)) % (2 * (t + r) + 2) = a + 2 * t ∧
      a + (2 * (t + r)) * (r + 1) + 1 < (2 * (t + r) + 1) * (2 * (t + r) + 1)) ∧
    (∀ m a b k j : Nat, a + (2 * m) * k = b + (2 * m + 2) * j → a % 2 = b % 2) ∧
    ((∀ (a : Shell p) (n : Nat), Ext.conj (pt ν a 0) ^ n = pt ν a 0 ^ n) ∧
      (∀ w : Ext p ν, Ext.conj w * w = 1 → ∀ n : Nat, Ext.conj w ^ n * w ^ n = 1)) ∧
    (∀ i t a a' : Shell p, i * i + 1 = 0 → (1 + 1) * t = 1 → a * a' = 1 →
      ((a + a') * t) * ((a + a') * t) + (i * ((a' + -a) * t)) * (i * ((a' + -a) * t)) = 1 ∧
      (a + a') * t + i * (i * ((a' + -a) * t)) = a ∧
      (a + a') * t + -(i * (i * ((a' + -a) * t))) = a' ∧
      -(i * ((a' + -a) * t)) + ((a + a') * t) * i = a * i ∧
      -(i * ((a' + -a) * t)) + ((a + a') * t) * -i = a' * -i) ∧
    (∀ i t a a' b b' : Shell p, i * i + 1 = 0 → (1 + 1) * t = 1 →
      ((a + a') * t) * ((b + b') * t) + -((i * ((a' + -a) * t)) * (i * ((b' + -b) * t))) = (a * b + a' * b') * t ∧
      (i * ((a' + -a) * t)) * ((b + b') * t) + ((a + a') * t) * (i * ((b' + -b) * t)) = i * ((a' * b' + -(a * b)) * t)) :=
  ⟨fun _ _ _ hk => ⟨(unit_square hk).1, (unit_square hk).2.1, (unit_square hk).2.2, ratio_kernel hp hν h2 hk⟩,
   ratio_cay, ratio_eta hp hν, weights_lift_ge, weights_lift_lt, weights_parity, frobenius_readings,
   fun _ _ _ _ hi ht ha => rotation_cycle hi ht ha, fun _ _ _ _ _ _ hi ht => rotation_mul hi ht⟩

/-! ## The hypercharge cycle and the charge cycle of the frame of rank five -/

/-- 27:C16 — the hypercharge point `diag(σ(w)², σ(w)², σ(w)², w³, w³)` of a unitary `w` has determinant one, and it is
the identity only for `w = 1`. -/
theorem hypercharge_cycle {w : Ext p ν} (hw : Ext.conj w * w = 1) :
    (Ext.conj w * Ext.conj w) * (Ext.conj w * Ext.conj w) * (Ext.conj w * Ext.conj w) * (w * w * w) * (w * w * w) = 1 ∧
    (Ext.conj w * Ext.conj w = 1 → w * w * w = 1 → w = 1) := by
  refine ⟨?_, fun hv h3 => ?_⟩
  · have e : (((((Ext.conj w * Ext.conj w) * (Ext.conj w * Ext.conj w)) * (Ext.conj w * Ext.conj w)) * ((w * w) * w)) * ((w * w) * w)) = ((((Ext.conj w * w) * (Ext.conj w * w)) * (Ext.conj w * w)) * (((Ext.conj w * w) * (Ext.conj w * w)) * (Ext.conj w * w))) := xsound (xlook [w, Ext.conj w]) (.mul (.mul (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 1) (.var 1))) (.mul (.var 1) (.var 1))) (.mul (.mul (.var 0) (.var 0)) (.var 0))) (.mul (.mul (.var 0) (.var 0)) (.var 0))) (.mul (.mul (.mul (.mul (.var 1) (.var 0)) (.mul (.var 1) (.var 0))) (.mul (.var 1) (.var 0))) (.mul (.mul (.mul (.var 1) (.var 0)) (.mul (.var 1) (.var 0))) (.mul (.var 1) (.var 0)))) (by decide +kernel)
    have e1 : ((1 : Ext p ν) * 1 * 1) * (1 * 1 * 1) = 1 := xsound (xlook [w]) (.mul (.mul (.mul .one .one) .one) (.mul (.mul .one .one) .one)) .one (by decide +kernel)
    rw [hw] at e
    exact e.trans e1
  · have e : (w * ((Ext.conj w * w) * (Ext.conj w * w))) = (((w * w) * w) * (Ext.conj w * Ext.conj w)) := xsound (xlook [w, Ext.conj w]) (.mul (.var 0) (.mul (.mul (.var 1) (.var 0)) (.mul (.var 1) (.var 0)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.var 0)) (.mul (.var 1) (.var 1))) (by decide +kernel)
    have e1 : w * ((1 : Ext p ν) * 1) = w := xsound (xlook [w]) (.mul (.var 0) (.mul .one .one)) (.var 0) (by decide +kernel)
    have e2 : (1 : Ext p ν) * 1 = 1 := xsound (xlook [w]) (.mul .one .one) .one (by decide +kernel)
    rw [hw, h3, hv] at e
    exact e1.symm.trans (e.trans e2)

/-- 27:C16 — the charge point `diag(u, u, u, σ(u)³, 1)` of a unitary `u` has determinant one, and its entry `σ(u)³`
on the doublet is `1` exactly when `u³ = 1`. -/
theorem charge_cycle {w : Ext p ν} (hw : Ext.conj w * w = 1) :
    w * w * w * (Ext.conj w * Ext.conj w * Ext.conj w) = 1 ∧
    (Ext.conj w * Ext.conj w * Ext.conj w = 1 ↔ w * w * w = 1) := by
  have d : w * w * w * (Ext.conj w * Ext.conj w * Ext.conj w) = 1 := by
    have e : (((w * w) * w) * ((Ext.conj w * Ext.conj w) * Ext.conj w)) = (((Ext.conj w * w) * (Ext.conj w * w)) * (Ext.conj w * w)) := xsound (xlook [w, Ext.conj w]) (.mul (.mul (.mul (.var 0) (.var 0)) (.var 0)) (.mul (.mul (.var 1) (.var 1)) (.var 1))) (.mul (.mul (.mul (.var 1) (.var 0)) (.mul (.var 1) (.var 0))) (.mul (.var 1) (.var 0))) (by decide +kernel)
    have e1 : (1 : Ext p ν) * 1 * 1 = 1 := xsound (xlook [w]) (.mul (.mul .one .one) .one) .one (by decide +kernel)
    rw [hw] at e
    exact e.trans e1
  refine ⟨d, fun h => ?_, fun h => ?_⟩
  · have d' := d
    rw [h, Ext.mul_one] at d'
    exact d'
  · have d' := d
    rw [h, Ext.one_mul] at d'
    exact d'

/-- 27:C16, 27:P10 — on the sixteen states the weight of the hypercharge cycle, `−2 |S ∩ C| + 3 |S ∩ W|`, is `6Y`, and the
weight of the charge cycle, `|S ∩ C| − 3 [3 ∈ S]`, is `−3Q`, so `6Q + 2 |S ∩ C|`
is a multiple of `6`: a cube root of unity of the charge cycle acts as the centre of the colour frame. The first clause
holds by the definition of `y6`, which `one_generation` ties to `6Y`. -/
theorem charge_weights :
    (Interactions.gen16.all (fun S => -2 * (Interactions.col S : Int) + 3 * (Interactions.wk S : Int) == Interactions.y6 S)) = true ∧
    (Interactions.gen16.all (fun S => 2 * (Interactions.col S : Int) + -(6 * (Interactions.cnt S 3 4 : Int)) == -(Interactions.q6 S))) = true ∧
    (Interactions.gen16.all (fun S => (Interactions.q6 S + 2 * (Interactions.col S : Int)) % 6 == 0)) = true := by
  decide +kernel

/-- 27:C16 — for `d ∣ p + 1` with `d > 1` some unitary point is no `d`-th power of a unitary point. -/
theorem not_all_powers (hp : FRC.Nat.isPrime p) (hν : ¬ ∃ y : Shell p, y * y = ν) (h2 : (1 : Shell p) + 1 ≠ 0)
    {d m : Nat} (hdm : p + 1 = d * m) (hd : 1 < d) :
    ¬∀ w : Ext p ν, Ext.conj w * w = 1 → ¬∀ v : Ext p ν, Ext.conj v * v = 1 → v ^ d ≠ w := fun hall => by
  obtain ⟨w, hw, _, hmin⟩ := unitary_generator hp hν h2
  have hm : 0 < m := Nat.pos_of_ne_zero (fun h0 => by rw [h0, Nat.mul_zero] at hdm; exact FRC.Nat.succ_ne_zero p hdm)
  have hlt : m < p + 1 := by
    have h := FRC.Nat.mul_lt_mul_of_lt_of_pos hd hm
    rw [Nat.one_mul] at h
    rw [hdm]
    exact h
  refine hall w hw (fun v hv e => hmin m hlt hm ?_)
  rw [← e, ← ext_pow_mul, ← hdm]
  exact unitary_period hp hν h2 hv

/-- 27:C16 — where `p + 2 = 3 j`, that is where `3` does not divide `p + 1`, every unitary point is the cube of the
unitary point `w^j`. -/
theorem all_cubes (hp : FRC.Nat.isPrime p) (hν : ¬ ∃ y : Shell p, y * y = ν) (h2 : (1 : Shell p) + 1 ≠ 0)
    {j : Nat} (hj : p + 2 = 3 * j) {w : Ext p ν} (hw : Ext.conj w * w = 1) :
    Ext.conj (w ^ j) * w ^ j = 1 ∧ (w ^ j) ^ 3 = w := by
  refine ⟨unitary_pow hw j, ?_⟩
  rw [← ext_pow_mul, Nat.mul_comm, ← hj, show p + 2 = (p + 1) + 1 from rfl, Ext.pow_add,
    unitary_period hp hν h2 hw, ext_pow_one, Ext.one_mul]

/-! ## The powers of a generator and the classes of the unitary cycle -/

/-- A generator of the unitary cycle has no repeated power below `p + 1`: `u^(i+l) = u^i` with `i + l < p + 1` gives
`l = 0`. -/
theorem generator_pow_cancel {u : Ext p ν} (hu : Ext.conj u * u = 1) (hmin : ∀ l, l < p + 1 → 0 < l → u ^ l ≠ 1)
    {i l : Nat} (hil : i + l < p + 1) (e : u ^ (i + l) = u ^ i) : l = 0 :=
  match Nat.decEq l 0 with
  | .isTrue h => h
  | .isFalse h => by
    have e1 : Ext.conj (u ^ i) * (u ^ i * u ^ l) = (Ext.conj (u ^ i) * u ^ i) * u ^ l := (Ext.mul_assoc _ _ _).symm
    rw [Ext.pow_add] at e
    rw [e, unitary_pow hu i] at e1
    exact absurd ((Ext.one_mul _).symm.trans e1.symm)
      (hmin l (Nat.lt_of_le_of_lt (Nat.le_add_left l i) hil) (Nat.pos_of_ne_zero h))

/-- The powers `u^j`, `j < p + 1`, of a generator of the unitary cycle are pairwise distinct. -/
theorem generator_pow_inj {u : Ext p ν} (hu : Ext.conj u * u = 1) (hmin : ∀ l, l < p + 1 → 0 < l → u ^ l ≠ 1)
    {i j : Nat} (hi : i < p + 1) (hj : j < p + 1) (e : u ^ i = u ^ j) : i = j :=
  match Nat.le_total i j with
  | .inl h => by
    obtain ⟨l, hl⟩ := Nat.le.dest h
    subst hl
    have h0 := generator_pow_cancel hu hmin hj e.symm
    rw [h0, Nat.add_zero]
  | .inr h => by
    obtain ⟨l, hl⟩ := Nat.le.dest h
    subst hl
    have h0 := generator_pow_cancel hu hmin hi e
    rw [h0, Nat.add_zero]

/-- 27:C16 — every unitary point is a power `u^j`, `j < p + 1`, of a generator `u` of the unitary cycle: the `p + 1`
powers are distinct unitary points, and the unitary points number `p + 1`. -/
theorem generator_powers (hp : FRC.Nat.isPrime p) (hν : ¬ ∃ y : Shell p, y * y = ν)
    {u : Ext p ν} (hu : Ext.conj u * u = 1) (hmin : ∀ l, l < p + 1 → 0 < l → u ^ l ≠ 1)
    {w : Ext p ν} (hw : Ext.conj w * w = 1) : ∃ j, j < p + 1 ∧ u ^ j = w := by
  have hσ : ∀ j, upt ν (uidx (u ^ j)) = u ^ j ∧ uidx (u ^ j) < p + 1 := fun j => upt_uidx hp hν (unitary_pow hu j)
  have hinj : ∀ i j, i < p + 1 → j < p + 1 → uidx (u ^ i) = uidx (u ^ j) → i = j := fun i j hi hj e =>
    generator_pow_inj hu hmin hi hj (((hσ i).1.symm.trans (congrArg (upt ν) e)).trans (hσ j).1)
  have hmem := Pigeonhole.mem_of_nodup_of_length_lt (p + 1) (imageList (fun j => uidx (u ^ j)) (p + 1))
    (imageList_nodup hinj (Nat.le_refl _))
    (fun e he => match mem_imageList he with | ⟨j, _, e'⟩ => e' ▸ (hσ j).2)
    (imageList_length _ _) (uidx w) (upt_uidx hp hν hw).2
  obtain ⟨j, hj, e⟩ := mem_imageList hmem
  exact ⟨j, hj, ((hσ j).1.symm.trans (congrArg (upt ν) e)).trans (upt_uidx hp hν hw).1⟩

/-- 27:C16 — the classes of the unitary cycle modulo its `d`-th powers, for `p + 1 = d m` and a generator `u`: every
unitary point is `v^d · u^r` with `v` unitary and `r < d`, and `u^s` is no `d`-th power of a unitary point for
`0 < s < d`. So the classes are those of `u^0, …, u^(d−1)`, and they number `d`. -/
theorem power_classes (hp : FRC.Nat.isPrime p) (hν : ¬ ∃ y : Shell p, y * y = ν) (h2 : (1 : Shell p) + 1 ≠ 0)
    {d m : Nat} (hdm : p + 1 = d * m) {u : Ext p ν} (hu : Ext.conj u * u = 1)
    (hmin : ∀ l, l < p + 1 → 0 < l → u ^ l ≠ 1) :
    (∀ w : Ext p ν, Ext.conj w * w = 1 → ∃ r, r < d ∧ ∃ v : Ext p ν, Ext.conj v * v = 1 ∧ w = v ^ d * u ^ r) ∧
    (∀ s, 0 < s → s < d → ∀ v : Ext p ν, Ext.conj v * v = 1 → v ^ d ≠ u ^ s) := by
  have hd : 0 < d := Nat.pos_of_ne_zero (fun h0 => by rw [h0, Nat.zero_mul] at hdm; exact FRC.Nat.succ_ne_zero p hdm)
  have hm : 0 < m := Nat.pos_of_ne_zero (fun h0 => by rw [h0, Nat.mul_zero] at hdm; exact FRC.Nat.succ_ne_zero p hdm)
  refine ⟨fun w hw => ?_, fun s hs hsd v hv e => ?_⟩
  · obtain ⟨k, _, hk⟩ := generator_powers hp hν hu hmin hw
    obtain ⟨q, hq⟩ := FRC.Nat.mod_spec d hd k
    have e : u ^ (d * q + k % d) = u ^ k := by rw [← hq]
    refine ⟨k % d, Nat.mod_lt k hd, u ^ q, unitary_pow hu q, ?_⟩
    rw [← hk, ← e, Ext.pow_add, ext_pow_mul, ext_pow_mul_comm]
  · have hlt : s * m < p + 1 := by rw [hdm]; exact FRC.Nat.mul_lt_mul_of_lt_of_pos hsd hm
    have hpos : 0 < s * m := by
      have h := FRC.Nat.mul_lt_mul_of_lt_of_pos hs hm
      rw [Nat.zero_mul] at h
      exact h
    refine hmin (s * m) hlt hpos ?_
    rw [ext_pow_mul, ← e, ← ext_pow_mul, ← hdm]
    exact unitary_period hp hν h2 hv

/-- 27:C16 — the sixth powers of the unitary cycle are its `d`-th powers for `d = gcd(6, p + 1)`. The numbers
`6 = d a`, `p + 1 = d m` and `a x = 1 + m t` certify the greatest common divisor: `d` divides both, and `a` is prime to
`m`. Then `w⁶ = (w^a)^d`, and `v^d = (v^x)⁶` for a unitary `v`. -/
theorem sixth_powers (hp : FRC.Nat.isPrime p) (hν : ¬ ∃ y : Shell p, y * y = ν) (h2 : (1 : Shell p) + 1 ≠ 0)
    {d a m x t : Nat} (h6 : 6 = d * a) (hdm : p + 1 = d * m) (hax : a * x = 1 + m * t) :
    (∀ w : Ext p ν, w ^ 6 = (w ^ a) ^ d) ∧
    (∀ v : Ext p ν, Ext.conj v * v = 1 → Ext.conj (v ^ x) * v ^ x = 1 ∧ (v ^ x) ^ 6 = v ^ d) := by
  refine ⟨fun w => ?_, fun v hv => ⟨unitary_pow hv x, ?_⟩⟩
  · rw [← ext_pow_mul, Nat.mul_comm a d, ← h6]
  · have e : x * 6 = d + (p + 1) * t := by
      rw [h6, FRC.Nat.mul_left_comm x d a, Nat.mul_comm x a, hax, Nat.mul_add, Nat.mul_one, hdm, FRC.Nat.mul_assoc]
    rw [← ext_pow_mul, e, Ext.pow_add, ext_pow_mul, unitary_period hp hν h2 hv, ext_one_pow]
    exact Ext.mul_one _

/-! ## Determinants under a scalar, and the squares of the charge cycle -/

/-- 27:C16 — a scalar `s` multiplies the determinant of rank three by `s³` and that of rank two by `s²`. With
`s = σ(w)²` on the colour block and `s = w³` on the doublet, the product of a hypercharge point with a pair of
determinants one has the determinant `w⁶` on the doublet. -/
theorem det_scale (s : Ext p ν) (A : M3 p ν) (B : M2 p ν) :
    det (smul s A) = (s * s * s) * det A ∧
    det2 (⟨s * B.a00, s * B.a01, s * B.a10, s * B.a11⟩ : M2 p ν) = (s * s) * det2 B := by
  cases A with
  | mk a00 a01 a02 a10 a11 a12 a20 a21 a22 =>
    cases B with
    | mk b00 b01 b10 b11 =>
      exact ⟨xsound (xlook [s, a00, a01, a02, a10, a11, a12, a20, a21, a22]) (.add (.add (.mul (.mul (.var 0) (.var 1)) (.add (.mul (.mul (.var 0) (.var 5)) (.mul (.var 0) (.var 9))) (.neg (.mul (.mul (.var 0) (.var 6)) (.mul (.var 0) (.var 8)))))) (.neg (.mul (.mul (.var 0) (.var 2)) (.add (.mul (.mul (.var 0) (.var 4)) (.mul (.var 0) (.var 9))) (.neg (.mul (.mul (.var 0) (.var 6)) (.mul (.var 0) (.var 7)))))))) (.mul (.mul (.var 0) (.var 3)) (.add (.mul (.mul (.var 0) (.var 4)) (.mul (.var 0) (.var 8))) (.neg (.mul (.mul (.var 0) (.var 5)) (.mul (.var 0) (.var 7))))))) (.mul (.mul (.mul (.var 0) (.var 0)) (.var 0)) (.add (.add (.mul (.var 1) (.add (.mul (.var 5) (.var 9)) (.neg (.mul (.var 6) (.var 8))))) (.neg (.mul (.var 2) (.add (.mul (.var 4) (.var 9)) (.neg (.mul (.var 6) (.var 7))))))) (.mul (.var 3) (.add (.mul (.var 4) (.var 8)) (.neg (.mul (.var 5) (.var 7))))))) (by decide +kernel), xsound (xlook [s, b00, b01, b10, b11]) (.add (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 4))) (.neg (.mul (.mul (.var 0) (.var 2)) (.mul (.var 0) (.var 3))))) (.mul (.mul (.var 0) (.var 0)) (.add (.mul (.var 1) (.var 4)) (.neg (.mul (.var 2) (.var 3))))) (by decide +kernel)⟩

/-- 27:C16 — a point of the charge cycle that is a product of a hypercharge point with a pair of determinants one is a
square, and every square is such a product. The point `diag(u, u, u, σ(u)³, 1)` has the determinant `σ(u)³` on the
doublet and the product has `w⁶`: from `σ(u)³ = w⁶` the unitary `z = (u w²)² w^p` has `z² = u`. Conversely, for a
unitary `z` and `w = σ(z)`, `σ(z²)³ = w⁶`, and the block `diag(w³, z³)` has determinant one. -/
theorem charge_squares (hp : FRC.Nat.isPrime p) (hν : ¬ ∃ y : Shell p, y * y = ν) (h2 : (1 : Shell p) + 1 ≠ 0) :
    (∀ u w : Ext p ν, Ext.conj u * u = 1 → Ext.conj w * w = 1 →
      Ext.conj u * Ext.conj u * Ext.conj u = w * w * w * (w * w * w) →
      ∃ z : Ext p ν, Ext.conj z * z = 1 ∧ z * z = u) ∧
    (∀ z : Ext p ν, Ext.conj z * z = 1 →
      Ext.conj (z * z) * Ext.conj (z * z) * Ext.conj (z * z)
        = Ext.conj z * Ext.conj z * Ext.conj z * (Ext.conj z * Ext.conj z * Ext.conj z) ∧
      Ext.conj z * Ext.conj z * Ext.conj z * (z * z * z) = 1) := by
  refine ⟨fun u w hu hw h => ?_, fun z hz => ⟨?_, ?_⟩⟩
  · have hP : w ^ p * w = 1 := unitary_period hp hν h2 hw
    have hx : Ext.conj (u * (w * w)) * (u * (w * w)) = 1 := unitary_mul hu (unitary_mul hw hw)
    refine ⟨u * (w * w) * (u * (w * w)) * w ^ p, unitary_mul (unitary_mul hx hx) (unitary_pow hw p), ?_⟩
    have e : ((((u * (w * w)) * (u * (w * w))) * w ^ p) * (((u * (w * w)) * (u * (w * w))) * w ^ p)) = (((((u * u) * u) * (((w * w) * w) * ((w * w) * w))) * u) * ((w ^ p * w) * (w ^ p * w))) := xsound (xlook [u, w, w ^ p]) (.mul (.mul (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.mul (.var 0) (.mul (.var 1) (.var 1)))) (.var 2)) (.mul (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.mul (.var 0) (.mul (.var 1) (.var 1)))) (.var 2))) (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 0)) (.var 0)) (.mul (.mul (.mul (.var 1) (.var 1)) (.var 1)) (.mul (.mul (.var 1) (.var 1)) (.var 1)))) (.var 0)) (.mul (.mul (.var 2) (.var 1)) (.mul (.var 2) (.var 1)))) (by decide +kernel)
    have e2 : (((((u * u) * u) * ((Ext.conj u * Ext.conj u) * Ext.conj u)) * u) * (1 * 1)) = ((((Ext.conj u * u) * (Ext.conj u * u)) * (Ext.conj u * u)) * u) := xsound (xlook [u, Ext.conj u]) (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 0)) (.var 0)) (.mul (.mul (.var 1) (.var 1)) (.var 1))) (.var 0)) (.mul .one .one)) (.mul (.mul (.mul (.mul (.var 1) (.var 0)) (.mul (.var 1) (.var 0))) (.mul (.var 1) (.var 0))) (.var 0)) (by decide +kernel)
    have e3 : (((1 * 1) * 1) * u) = u := xsound (xlook [u]) (.mul (.mul (.mul .one .one) .one) (.var 0)) (.var 0) (by decide +kernel)
    rw [← h, hP] at e
    rw [hu] at e2
    exact e.trans (e2.trans e3)
  · rw [Ext.conj_mul]
    exact xsound (xlook [z, Ext.conj z]) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 1) (.var 1))) (.mul (.var 1) (.var 1))) (.mul (.mul (.mul (.var 1) (.var 1)) (.var 1)) (.mul (.mul (.var 1) (.var 1)) (.var 1))) (by decide +kernel)
  · have e : (((Ext.conj z * Ext.conj z) * Ext.conj z) * ((z * z) * z)) = (((Ext.conj z * z) * (Ext.conj z * z)) * (Ext.conj z * z)) := xsound (xlook [z, Ext.conj z]) (.mul (.mul (.mul (.var 1) (.var 1)) (.var 1)) (.mul (.mul (.var 0) (.var 0)) (.var 0))) (.mul (.mul (.mul (.var 1) (.var 0)) (.mul (.var 1) (.var 0))) (.mul (.var 1) (.var 0))) (by decide +kernel)
    have e1 : (1 : Ext p ν) * 1 * 1 = 1 := xsound (xlook [z]) (.mul (.mul .one .one) .one) .one (by decide +kernel)
    rw [hz] at e
    exact e.trans e1

/-! ## The commutant of a diagonal matrix and two transpositions -/

/-- The diagonal matrix of three entries. -/
def mdiag (x y z : Ext p ν) : M3 p ν := ⟨x, 0, 0, 0, y, 0, 0, 0, z⟩

/-- The permutation matrix that exchanges the first two directions. -/
def swap01 : M3 p ν := ⟨0, 1, 0, 1, 0, 0, 0, 0, 1⟩

/-- The permutation matrix that exchanges the last two directions. -/
def swap12 : M3 p ν := ⟨1, 0, 0, 0, 0, 1, 0, 1, 0⟩

/-- 27:C16 — a matrix of rank three over the extension that commutes with a diagonal matrix whose three entries have
invertible differences, and with the two permutation matrices of adjacent directions, is a scalar. The three are
unitary when the entries are unitary points, so a frame move of the colour block that commutes with every frame move
of the block is a scalar: the centre of the vacuum's stabiliser is the charge cycle. -/
theorem commutant_scalar {A : M3 p ν} {d0 d1 d2 k01 k02 k12 : Ext p ν}
    (h01 : (d0 + -d1) * k01 = 1) (h02 : (d0 + -d2) * k02 = 1) (h12 : (d1 + -d2) * k12 = 1)
    (hD : mmul A (mdiag d0 d1 d2) = mmul (mdiag d0 d1 d2) A)
    (hS : mmul A swap01 = mmul swap01 A) (hT : mmul A swap12 = mmul swap12 A) : A = scal A.a00 := by
  cases A with
  | mk a00 a01 a02 a10 a11 a12 a20 a21 a22 =>
    have e01 : a01 = 0 := by
      have h : (((a00 * 0) + (a01 * d1)) + (a02 * 0)) = (((d0 * a01) + (0 * a11)) + (0 * a21)) := congrArg M3.a01 hD
      have e : (a01 * ((d0 + -d1) * k01)) = (((((d0 * a01) + (0 * a11)) + (0 * a21)) + -(((a00 * 0) + (a01 * d1)) + (a02 * 0))) * k01) := xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, d0, d1, d2, k01]) (.mul (.var 1) (.mul (.add (.var 9) (.neg (.var 10))) (.var 12))) (.mul (.add (.add (.add (.mul (.var 9) (.var 1)) (.mul .zero (.var 4))) (.mul .zero (.var 7))) (.neg (.add (.add (.mul (.var 0) .zero) (.mul (.var 1) (.var 10))) (.mul (.var 2) .zero)))) (.var 12)) (by decide +kernel)
      have z : (((((d0 * a01) + (0 * a11)) + (0 * a21)) + -(((d0 * a01) + (0 * a11)) + (0 * a21))) * k01) = 0 := xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, d0, d1, d2, k01]) (.mul (.add (.add (.add (.mul (.var 9) (.var 1)) (.mul .zero (.var 4))) (.mul .zero (.var 7))) (.neg (.add (.add (.mul (.var 9) (.var 1)) (.mul .zero (.var 4))) (.mul .zero (.var 7))))) (.var 12)) .zero (by decide +kernel)
      have o : (a01 * 1) = a01 := xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, d0, d1, d2, k01]) (.mul (.var 1) .one) (.var 1) (by decide +kernel)
      rw [h, h01] at e
      exact o.symm.trans (e.trans z)
    have e02 : a02 = 0 := by
      have h : (((a00 * 0) + (a01 * 0)) + (a02 * d2)) = (((d0 * a02) + (0 * a12)) + (0 * a22)) := congrArg M3.a02 hD
      have e : (a02 * ((d0 + -d2) * k02)) = (((((d0 * a02) + (0 * a12)) + (0 * a22)) + -(((a00 * 0) + (a01 * 0)) + (a02 * d2))) * k02) := xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, d0, d1, d2, k02]) (.mul (.var 2) (.mul (.add (.var 9) (.neg (.var 11))) (.var 12))) (.mul (.add (.add (.add (.mul (.var 9) (.var 2)) (.mul .zero (.var 5))) (.mul .zero (.var 8))) (.neg (.add (.add (.mul (.var 0) .zero) (.mul (.var 1) .zero)) (.mul (.var 2) (.var 11))))) (.var 12)) (by decide +kernel)
      have z : (((((d0 * a02) + (0 * a12)) + (0 * a22)) + -(((d0 * a02) + (0 * a12)) + (0 * a22))) * k02) = 0 := xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, d0, d1, d2, k02]) (.mul (.add (.add (.add (.mul (.var 9) (.var 2)) (.mul .zero (.var 5))) (.mul .zero (.var 8))) (.neg (.add (.add (.mul (.var 9) (.var 2)) (.mul .zero (.var 5))) (.mul .zero (.var 8))))) (.var 12)) .zero (by decide +kernel)
      have o : (a02 * 1) = a02 := xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, d0, d1, d2, k02]) (.mul (.var 2) .one) (.var 2) (by decide +kernel)
      rw [h, h02] at e
      exact o.symm.trans (e.trans z)
    have e10 : a10 = 0 := by
      have h : (((a10 * d0) + (a11 * 0)) + (a12 * 0)) = (((0 * a00) + (d1 * a10)) + (0 * a20)) := congrArg M3.a10 hD
      have e : (a10 * ((d0 + -d1) * k01)) = (((((a10 * d0) + (a11 * 0)) + (a12 * 0)) + -(((0 * a00) + (d1 * a10)) + (0 * a20))) * k01) := xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, d0, d1, d2, k01]) (.mul (.var 3) (.mul (.add (.var 9) (.neg (.var 10))) (.var 12))) (.mul (.add (.add (.add (.mul (.var 3) (.var 9)) (.mul (.var 4) .zero)) (.mul (.var 5) .zero)) (.neg (.add (.add (.mul .zero (.var 0)) (.mul (.var 10) (.var 3))) (.mul .zero (.var 6))))) (.var 12)) (by decide +kernel)
      have z : (((((0 * a00) + (d1 * a10)) + (0 * a20)) + -(((0 * a00) + (d1 * a10)) + (0 * a20))) * k01) = 0 := xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, d0, d1, d2, k01]) (.mul (.add (.add (.add (.mul .zero (.var 0)) (.mul (.var 10) (.var 3))) (.mul .zero (.var 6))) (.neg (.add (.add (.mul .zero (.var 0)) (.mul (.var 10) (.var 3))) (.mul .zero (.var 6))))) (.var 12)) .zero (by decide +kernel)
      have o : (a10 * 1) = a10 := xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, d0, d1, d2, k01]) (.mul (.var 3) .one) (.var 3) (by decide +kernel)
      rw [h, h01] at e
      exact o.symm.trans (e.trans z)
    have e12 : a12 = 0 := by
      have h : (((a10 * 0) + (a11 * 0)) + (a12 * d2)) = (((0 * a02) + (d1 * a12)) + (0 * a22)) := congrArg M3.a12 hD
      have e : (a12 * ((d1 + -d2) * k12)) = (((((0 * a02) + (d1 * a12)) + (0 * a22)) + -(((a10 * 0) + (a11 * 0)) + (a12 * d2))) * k12) := xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, d0, d1, d2, k12]) (.mul (.var 5) (.mul (.add (.var 10) (.neg (.var 11))) (.var 12))) (.mul (.add (.add (.add (.mul .zero (.var 2)) (.mul (.var 10) (.var 5))) (.mul .zero (.var 8))) (.neg (.add (.add (.mul (.var 3) .zero) (.mul (.var 4) .zero)) (.mul (.var 5) (.var 11))))) (.var 12)) (by decide +kernel)
      have z : (((((0 * a02) + (d1 * a12)) + (0 * a22)) + -(((0 * a02) + (d1 * a12)) + (0 * a22))) * k12) = 0 := xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, d0, d1, d2, k12]) (.mul (.add (.add (.add (.mul .zero (.var 2)) (.mul (.var 10) (.var 5))) (.mul .zero (.var 8))) (.neg (.add (.add (.mul .zero (.var 2)) (.mul (.var 10) (.var 5))) (.mul .zero (.var 8))))) (.var 12)) .zero (by decide +kernel)
      have o : (a12 * 1) = a12 := xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, d0, d1, d2, k12]) (.mul (.var 5) .one) (.var 5) (by decide +kernel)
      rw [h, h12] at e
      exact o.symm.trans (e.trans z)
    have e20 : a20 = 0 := by
      have h : (((a20 * d0) + (a21 * 0)) + (a22 * 0)) = (((0 * a00) + (0 * a10)) + (d2 * a20)) := congrArg M3.a20 hD
      have e : (a20 * ((d0 + -d2) * k02)) = (((((a20 * d0) + (a21 * 0)) + (a22 * 0)) + -(((0 * a00) + (0 * a10)) + (d2 * a20))) * k02) := xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, d0, d1, d2, k02]) (.mul (.var 6) (.mul (.add (.var 9) (.neg (.var 11))) (.var 12))) (.mul (.add (.add (.add (.mul (.var 6) (.var 9)) (.mul (.var 7) .zero)) (.mul (.var 8) .zero)) (.neg (.add (.add (.mul .zero (.var 0)) (.mul .zero (.var 3))) (.mul (.var 11) (.var 6))))) (.var 12)) (by decide +kernel)
      have z : (((((0 * a00) + (0 * a10)) + (d2 * a20)) + -(((0 * a00) + (0 * a10)) + (d2 * a20))) * k02) = 0 := xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, d0, d1, d2, k02]) (.mul (.add (.add (.add (.mul .zero (.var 0)) (.mul .zero (.var 3))) (.mul (.var 11) (.var 6))) (.neg (.add (.add (.mul .zero (.var 0)) (.mul .zero (.var 3))) (.mul (.var 11) (.var 6))))) (.var 12)) .zero (by decide +kernel)
      have o : (a20 * 1) = a20 := xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, d0, d1, d2, k02]) (.mul (.var 6) .one) (.var 6) (by decide +kernel)
      rw [h, h02] at e
      exact o.symm.trans (e.trans z)
    have e21 : a21 = 0 := by
      have h : (((a20 * 0) + (a21 * d1)) + (a22 * 0)) = (((0 * a01) + (0 * a11)) + (d2 * a21)) := congrArg M3.a21 hD
      have e : (a21 * ((d1 + -d2) * k12)) = (((((a20 * 0) + (a21 * d1)) + (a22 * 0)) + -(((0 * a01) + (0 * a11)) + (d2 * a21))) * k12) := xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, d0, d1, d2, k12]) (.mul (.var 7) (.mul (.add (.var 10) (.neg (.var 11))) (.var 12))) (.mul (.add (.add (.add (.mul (.var 6) .zero) (.mul (.var 7) (.var 10))) (.mul (.var 8) .zero)) (.neg (.add (.add (.mul .zero (.var 1)) (.mul .zero (.var 4))) (.mul (.var 11) (.var 7))))) (.var 12)) (by decide +kernel)
      have z : (((((0 * a01) + (0 * a11)) + (d2 * a21)) + -(((0 * a01) + (0 * a11)) + (d2 * a21))) * k12) = 0 := xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, d0, d1, d2, k12]) (.mul (.add (.add (.add (.mul .zero (.var 1)) (.mul .zero (.var 4))) (.mul (.var 11) (.var 7))) (.neg (.add (.add (.mul .zero (.var 1)) (.mul .zero (.var 4))) (.mul (.var 11) (.var 7))))) (.var 12)) .zero (by decide +kernel)
      have o : (a21 * 1) = a21 := xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22, d0, d1, d2, k12]) (.mul (.var 7) .one) (.var 7) (by decide +kernel)
      rw [h, h12] at e
      exact o.symm.trans (e.trans z)
    have e0011 : a00 = a11 := by
      have h : (((a00 * 1) + (a01 * 0)) + (a02 * 0)) = (((0 * a01) + (1 * a11)) + (0 * a21)) := congrArg M3.a01 hS
      have i1 : a00 = (((a00 * 1) + (a01 * 0)) + (a02 * 0)) := xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22]) (.var 0) (.add (.add (.mul (.var 0) .one) (.mul (.var 1) .zero)) (.mul (.var 2) .zero)) (by decide +kernel)
      have i2 : (((0 * a01) + (1 * a11)) + (0 * a21)) = a11 := xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22]) (.add (.add (.mul .zero (.var 1)) (.mul .one (.var 4))) (.mul .zero (.var 7))) (.var 4) (by decide +kernel)
      exact i1.trans (h.trans i2)
    have e1122 : a11 = a22 := by
      have h : (((a10 * 0) + (a11 * 1)) + (a12 * 0)) = (((0 * a02) + (0 * a12)) + (1 * a22)) := congrArg M3.a12 hT
      have i1 : a11 = (((a10 * 0) + (a11 * 1)) + (a12 * 0)) := xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22]) (.var 4) (.add (.add (.mul (.var 3) .zero) (.mul (.var 4) .one)) (.mul (.var 5) .zero)) (by decide +kernel)
      have i2 : (((0 * a02) + (0 * a12)) + (1 * a22)) = a22 := xsound (xlook [a00, a01, a02, a10, a11, a12, a20, a21, a22]) (.add (.add (.mul .zero (.var 2)) (.mul .zero (.var 5))) (.mul .one (.var 8))) (.var 8) (by decide +kernel)
      exact i1.trans (h.trans i2)
    show M3.mk a00 a01 a02 a10 a11 a12 a20 a21 a22 = M3.mk a00 0 0 0 a00 0 0 0 a00
    rw [e01, e02, e10, e12, e20, e21, ← e1122, ← e0011]

/-! ## The kernel of the product of the hypercharge cycle with the two frames -/

/-- A scalar matrix `s I₃` times `A` is the identity only for `A = t I₃`, where `t s = 1`. -/
theorem scal_inverse {s t : Ext p ν} (hst : t * s = 1) {A : M3 p ν} (h : mmul (scal s) A = mone) : A = scal t := by
  have e : smul t (mmul (scal s) A) = smul t mone := congrArg (smul t) h
  rw [scal_mul, smul_smul, hst, one_smul] at e
  rw [e]
  exact mext (xsound (xlook [t]) (.mul (.var 0) .one) (.var 0) (by decide +kernel)) (xsound (xlook [t]) (.mul (.var 0) .zero) .zero (by decide +kernel)) (xsound (xlook [t]) (.mul (.var 0) .zero) .zero (by decide +kernel)) (xsound (xlook [t]) (.mul (.var 0) .zero) .zero (by decide +kernel)) (xsound (xlook [t]) (.mul (.var 0) .one) (.var 0) (by decide +kernel)) (xsound (xlook [t]) (.mul (.var 0) .zero) .zero (by decide +kernel)) (xsound (xlook [t]) (.mul (.var 0) .zero) .zero (by decide +kernel)) (xsound (xlook [t]) (.mul (.var 0) .zero) .zero (by decide +kernel)) (xsound (xlook [t]) (.mul (.var 0) .one) (.var 0) (by decide +kernel))

/-- 27:C16, 27:P10 — the kernel of the product of the hypercharge cycle with the two frames of determinant one. A hypercharge
point of a unitary `w` is `σ(w)² I₃` on the colour block and `w³ I₂` on the doublet. Its product with a pair `(A, B)` is
the identity only for `A = w² I₃`, of determinant `w⁶`, and for `B = σ(w)³ I₂`, since `w³ σ(w)³ = 1`. The two
determinants are one together, `w⁶ = 1` exactly when `σ(w)⁶ = 1`. So the kernel is the set of the triples with `w⁶ = 1`. -/
theorem product_kernel {w : Ext p ν} (hw : Ext.conj w * w = 1) :
    (∀ A : M3 p ν, mmul (scal (Ext.conj w * Ext.conj w)) A = mone → A = scal (w * w)) ∧
    det (scal (w * w)) = (w * w) ^ 3 ∧
    w * w * w * (Ext.conj w * Ext.conj w * Ext.conj w) = 1 ∧
    ((w * w) * (w * w) * (w * w) = 1 ↔
      (Ext.conj w * Ext.conj w * Ext.conj w) * (Ext.conj w * Ext.conj w * Ext.conj w) = 1) := by
  have hi : (w * w) * (Ext.conj w * Ext.conj w) = 1 := by
    have e : ((w * w) * (Ext.conj w * Ext.conj w)) = ((Ext.conj w * w) * (Ext.conj w * w)) := xsound (xlook [w, Ext.conj w]) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.mul (.var 1) (.var 0)) (.mul (.var 1) (.var 0))) (by decide +kernel)
    have e2 : (1 : Ext p ν) * 1 = 1 := xsound (xlook [w]) (.mul .one .one) .one (by decide +kernel)
    rw [hw] at e
    exact e.trans e2
  have d6 : ((w * w) * (w * w) * (w * w)) *
      ((Ext.conj w * Ext.conj w * Ext.conj w) * (Ext.conj w * Ext.conj w * Ext.conj w)) = 1 := by
    have e : ((((w * w) * (w * w)) * (w * w)) * (((Ext.conj w * Ext.conj w) * Ext.conj w) * ((Ext.conj w * Ext.conj w) * Ext.conj w))) = ((((Ext.conj w * w) * (Ext.conj w * w)) * (Ext.conj w * w)) * (((Ext.conj w * w) * (Ext.conj w * w)) * (Ext.conj w * w))) := xsound (xlook [w, Ext.conj w]) (.mul (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 0) (.var 0))) (.mul (.var 0) (.var 0))) (.mul (.mul (.mul (.var 1) (.var 1)) (.var 1)) (.mul (.mul (.var 1) (.var 1)) (.var 1)))) (.mul (.mul (.mul (.mul (.var 1) (.var 0)) (.mul (.var 1) (.var 0))) (.mul (.var 1) (.var 0))) (.mul (.mul (.mul (.var 1) (.var 0)) (.mul (.var 1) (.var 0))) (.mul (.var 1) (.var 0)))) (by decide +kernel)
    have e1 : ((1 : Ext p ν) * 1 * 1) * (1 * 1 * 1) = 1 := xsound (xlook [w]) (.mul (.mul (.mul .one .one) .one) (.mul (.mul .one .one) .one)) .one (by decide +kernel)
    rw [hw] at e
    exact e.trans e1
  refine ⟨fun A h => scal_inverse hi h, det_scal _, (charge_cycle hw).1, fun h => ?_, fun h => ?_⟩
  · have d' := d6
    rw [h, Ext.one_mul] at d'
    exact d'
  · have d' := d6
    rw [h, Ext.mul_one] at d'
    exact d'

/-- 27:C16, 27:P10 — the solutions of `w⁶ = 1` on the unitary cycle, the kernel of the product map. With `6 = d a`,
`p + 1 = d m`, `a x = 1 + m t` and a generator `u`: a unitary point has `w⁶ = 1` exactly when `w^d = 1`, and the unitary
points with `w^d = 1` are the `d` distinct powers `u^(m r)`, `r < d`. The kernel is a cycle of order `d = gcd(6, p + 1)`. -/
theorem sixth_roots (hp : FRC.Nat.isPrime p) (hν : ¬ ∃ y : Shell p, y * y = ν) (h2 : (1 : Shell p) + 1 ≠ 0)
    {d a m x t : Nat} (h6 : 6 = d * a) (hdm : p + 1 = d * m) (hax : a * x = 1 + m * t)
    {u : Ext p ν} (hu : Ext.conj u * u = 1) (hmin : ∀ l, l < p + 1 → 0 < l → u ^ l ≠ 1) :
    (∀ w : Ext p ν, Ext.conj w * w = 1 → (w ^ 6 = 1 ↔ w ^ d = 1)) ∧
    (∀ r : Nat, (u ^ (m * r)) ^ d = 1) ∧
    (∀ w : Ext p ν, Ext.conj w * w = 1 → w ^ d = 1 → ∃ r, r < d ∧ w = u ^ (m * r)) ∧
    (∀ r s : Nat, r < d → s < d → u ^ (m * r) = u ^ (m * s) → r = s) := by
  have hd : 0 < d := Nat.pos_of_ne_zero (fun h0 => by rw [h0, Nat.zero_mul] at hdm; exact FRC.Nat.succ_ne_zero p hdm)
  have hm : 0 < m := Nat.pos_of_ne_zero (fun h0 => by rw [h0, Nat.mul_zero] at hdm; exact FRC.Nat.succ_ne_zero p hdm)
  have sp := sixth_powers (ν := ν) hp hν h2 h6 hdm hax
  have hlt : ∀ r, r < d → m * r < p + 1 := fun r hr => by
    rw [hdm, Nat.mul_comm m r]
    exact FRC.Nat.mul_lt_mul_of_lt_of_pos hr hm
  refine ⟨fun w hw => ⟨fun h => ?_, fun h => ?_⟩, fun r => ?_, fun w hw hwd => ?_, fun r s hr hs e => ?_⟩
  · rw [← (sp.2 w hw).2, ext_pow_mul_comm, h, ext_one_pow]
  · rw [sp.1 w, ext_pow_mul_comm, h, ext_one_pow]
  · rw [← ext_pow_mul, FRC.Nat.mul_assoc, Nat.mul_comm r d, ← FRC.Nat.mul_assoc, Nat.mul_comm m d, ← hdm, ext_pow_mul,
      unitary_period hp hν h2 hu, ext_one_pow]
  · obtain ⟨k, hk, e⟩ := generator_powers hp hν hu hmin hw
    have hkd : u ^ (k * d) = 1 := by rw [ext_pow_mul, e, hwd]
    obtain ⟨c, hc⟩ := uorder_dvd ⟨Nat.succ_pos p, unitary_period hp hν h2 hu, hmin⟩ hkd
    have hc' : d * k = d * (m * c) := by
      have h1 : k * d = (p + 1) * c := hc
      rw [Nat.mul_comm d k, h1, hdm, FRC.Nat.mul_assoc]
    have hkc : k = m * c := FRC.Nat.quot_unique (p := d) (r := 0) (r' := 0) hd hd hc'
    match Nat.lt_or_ge c d with
    | .inl h => exact ⟨c, h, by rw [← e, hkc]⟩
    | .inr h =>
      have hle : p + 1 ≤ k := by
        rw [hkc, hdm, Nat.mul_comm d m]
        exact Nat.mul_le_mul_left m h
      exact absurd (Nat.lt_of_lt_of_le hk hle) (Nat.lt_irrefl k)
  · exact FRC.Nat.quot_unique (p := m) (r := 0) (r' := 0) hm hm (generator_pow_inj hu hmin (hlt r hr) (hlt s hs) e)

/-- 27:P10 — the weight of a point of the centre of the colour frame. For a cube root of unity `x ≠ 1` the power `x ^ n`
is one exactly when three divides `n`: a state of `n` net colour indices that the point fixes has `n` a multiple of
three. -/
theorem centre_weight {x : Ext p ν} (h3 : x ^ 3 = 1) (h1 : x ≠ 1) (n : Nat) : x ^ n = 1 ↔ n % 3 = 0 := by
  obtain ⟨q, hq⟩ := FRC.Nat.mod_spec 3 (by decide) n
  have hx : x ^ n = x ^ (n % 3) := by
    have e : x ^ (3 * q + n % 3) = x ^ (n % 3) := by
      rw [Ext.pow_add, ext_pow_mul, h3, ext_one_pow, Ext.one_mul]
    rw [← hq] at e
    exact e
  rw [hx]
  match n % 3, Nat.mod_lt n (by decide : 0 < 3) with
  | 0, _ => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | 1, _ =>
    refine ⟨fun h => absurd ?_ h1, fun h => absurd h (by decide)⟩
    rw [ext_pow_one] at h
    exact h
  | 2, _ =>
    refine ⟨fun h => absurd ?_ h1, fun h => absurd h (by decide)⟩
    have e : x ^ (2 + 1) = x := by rw [Ext.pow_add, h, ext_pow_one, Ext.one_mul]
    rw [← e]
    exact h3
  | k + 3, h => exact absurd h (Nat.not_lt_of_le (Nat.le_add_left 3 k))

/-- 27:P10 — a state that the diagonal frame moves of the colour frame fix. With `aᵢ` indices and `bᵢ` conjugate indices
in the colour direction `i`, fewer than `p + 1` in each sum, the equal weights `u^(a₁+b₃) = u^(a₃+b₁)` and
`u^(a₂+b₃) = u^(a₃+b₂)` on a generator `u` of the unitary cycle give equal net numbers of indices in the three
directions. -/
theorem colourless_indices {u : Ext p ν} (hu : Ext.conj u * u = 1) (hmin : ∀ l, l < p + 1 → 0 < l → u ^ l ≠ 1)
    {a1 a2 a3 b1 b2 b3 : Nat} (h1 : a1 + b3 < p + 1) (h1' : a3 + b1 < p + 1) (h2 : a2 + b3 < p + 1)
    (h2' : a3 + b2 < p + 1) (e1 : u ^ (a1 + b3) = u ^ (a3 + b1)) (e2 : u ^ (a2 + b3) = u ^ (a3 + b2)) :
    a1 + b3 = a3 + b1 ∧ a2 + b3 = a3 + b2 :=
  ⟨generator_pow_inj hu hmin h1 h1' e1, generator_pow_inj hu hmin h2 h2' e2⟩

/-! ## The Frobenius parity of a tally (27:C17) -/

/-- 27:C17 — an expression formed from the entries with integer coefficients commutes with the Frobenius: its value on
the conjugate entries is the conjugate of its value. A value of the shell is its own conjugate, so a tally takes equal
values on a configuration and on its Frobenius conjugate. -/
theorem tally_even (env : Nat → Ext p ν) (e : RE) :
    Ext.conj (xeval env e) = xeval (fun i => Ext.conj (env i)) e := conj_xeval env e

/-- An element that the Frobenius negates has a real part of `2`-torsion: on an odd shell it lies in `η F_p`. -/
theorem re_of_conj_neg {z : Ext p ν} (h : Ext.conj z = -z) : z.re + z.re = 0 := by
  have e : z.re = -z.re := Ext.re_congr h
  have t := Shell.neg_add z.re
  rw [← e] at t
  exact t

/-- 27:C17 — the orientation-odd term of a plaquette. For a frame move `U` of determinant one the difference of the
traces of `U` and of its inverse is negated by the Frobenius, and its real part is `2`-torsion. -/
theorem orientation_odd (U : M3 p ν) (hU : SU mone U) :
    Ext.conj (tr U + -(tr (adj U))) = -(tr U + -(tr (adj U))) ∧
    (tr U + -(tr (adj U))).re + (tr U + -(tr (adj U))).re = 0 := by
  have e := (wilson_orientation_even U hU).1
  have h : Ext.conj (tr U + -(tr (adj U))) = -(tr U + -(tr (adj U))) := by
    rw [e, conj_add, conj_neg, Ext.conj_conj]
    exact xsound (xlook [tr U, Ext.conj (tr U)]) (.add (.var 1) (.neg (.var 0))) (.neg (.add (.var 0) (.neg (.var 1))))
      (by decide +kernel)
  exact ⟨h, re_of_conj_neg h⟩

/-- The conjugate of a determinant is the determinant of the conjugate transpose. -/
theorem conj_det (A : M3 p ν) : Ext.conj (det A) = det (dag A) := by
  have e1 : Ext.conj (det A) = xeval (fun i => Ext.conj (xlook (ents A) i)) detRE := by
    rw [← conj_xeval]; rfl
  have e2 : xeval (fun i => Ext.conj (xlook (ents A) i)) detRE = xeval (fun i => Ext.conj (xlook (ents A) i)) detRE' :=
    xsound _ detRE detRE' (by decide +kernel)
  have e3 : xeval (fun i => Ext.conj (xlook (ents A) i)) detRE' = det (dag A) := rfl
  rw [e1, e2, e3]

/-- 27:C17 — the determinant of an anti-Hermitian matrix of three rows, such as the commutator of two Hermitian
matrices, is negated by the Frobenius, and its real part is `2`-torsion. -/
theorem antihermitian_det (C : M3 p ν) (h : dag C = smul (-1) C) :
    Ext.conj (det C) = -(det C) ∧ (det C).re + (det C).re = 0 := by
  have e : Ext.conj (det C) = -(det C) := by
    rw [conj_det, h, (det_scale (-1) C (⟨0, 0, 0, 0⟩ : M2 p ν)).1]
    exact xsound (xlook [det C]) (.mul (.mul (.mul (.neg .one) (.neg .one)) (.neg .one)) (.var 0)) (.neg (.var 0))
      (by decide +kernel)
  exact ⟨e, re_of_conj_neg e⟩

/-- 27:C17 — the product of two elements that the Frobenius negates is fixed by it, and its imaginary part is
`2`-torsion: on an odd shell the product lies in the shell. -/
theorem odd_product {a b : Ext p ν} (ha : Ext.conj a = -a) (hb : Ext.conj b = -b) :
    Ext.conj (a * b) = a * b ∧ (a * b).im + (a * b).im = 0 := by
  have e : Ext.conj (a * b) = a * b := by
    rw [Ext.conj_mul, ha, hb]
    exact xsound (xlook [a, b]) (.mul (.neg (.var 0)) (.neg (.var 1))) (.mul (.var 0) (.var 1)) (by decide +kernel)
  exact ⟨e, im_of_conj_fixed e⟩

/-! ## The lift of one chronon to the doublet (27:C15, 27:C4) -/

/-- 27:C15, 27:C4 — the entries `η = pt ν 0 1` and `η⁻¹ = pt ν 0 k`, `ν k = 1`, of the lift `diag(η, η⁻¹)` of one
chronon. They are inverse, their squares are `ν` and `k`, the entries of the transport of two chronons, and their norms
are `−ν` and `−k`. So one chronon multiplies the two charged directions by `η · η = ν` and `η⁻¹ · η⁻¹ = k`, and the
Hermitian pairings of the two components by `−ν` and `−k`. -/
theorem drive_lift {k : Shell p} (hk : ν * k = 1) :
    pt ν 0 1 * pt ν 0 k = 1 ∧ pt ν 0 1 * pt ν 0 1 = pt ν ν 0 ∧ pt ν 0 k * pt ν 0 k = pt ν k 0 ∧
    Ext.conj (pt ν 0 1) * pt ν 0 1 = pt ν (-ν) 0 ∧ Ext.conj (pt ν 0 k) * pt ν 0 k = pt ν (-k) 0 := by
  refine ⟨Ext.ext ?_ ?_, Ext.ext ?_ ?_, Ext.ext ?_ ?_, Ext.ext ?_ ?_, Ext.ext ?_ ?_⟩
  · have e : ((0 * 0) + (ν * (1 * k))) = (ν * k) := Shell.Frame.RE.sound (Shell.Frame.look [ν, k]) (.add (.mul .zero .zero) (.mul (.var 0) (.mul .one (.var 1)))) (.mul (.var 0) (.var 1)) (by decide +kernel)
    rw [hk] at e
    exact e
  · exact Shell.Frame.RE.sound (Shell.Frame.look [ν, k]) (.add (.mul .zero (.var 1)) (.mul .one .zero)) .zero (by decide +kernel)
  · exact Shell.Frame.RE.sound (Shell.Frame.look [ν, k]) (.add (.mul .zero .zero) (.mul (.var 0) (.mul .one .one))) (.var 0) (by decide +kernel)
  · exact Shell.Frame.RE.sound (Shell.Frame.look [ν, k]) (.add (.mul .zero .one) (.mul .one .zero)) .zero (by decide +kernel)
  · have e : ((0 * 0) + (ν * (k * k))) = ((ν * k) * k) := Shell.Frame.RE.sound (Shell.Frame.look [ν, k]) (.add (.mul .zero .zero) (.mul (.var 0) (.mul (.var 1) (.var 1)))) (.mul (.mul (.var 0) (.var 1)) (.var 1)) (by decide +kernel)
    rw [hk, Shell.one_mul] at e
    exact e
  · exact Shell.Frame.RE.sound (Shell.Frame.look [ν, k]) (.add (.mul .zero (.var 1)) (.mul (.var 1) .zero)) .zero (by decide +kernel)
  · exact Shell.Frame.RE.sound (Shell.Frame.look [ν, k]) (.add (.mul .zero .zero) (.mul (.var 0) (.mul (.neg .one) .one))) (.neg (.var 0)) (by decide +kernel)
  · exact Shell.Frame.RE.sound (Shell.Frame.look [ν, k]) (.add (.mul .zero .one) (.mul (.neg .one) .zero)) .zero (by decide +kernel)
  · have e : ((0 * 0) + (ν * (-k * k))) = -((ν * k) * k) := Shell.Frame.RE.sound (Shell.Frame.look [ν, k]) (.add (.mul .zero .zero) (.mul (.var 0) (.mul (.neg (.var 1)) (.var 1)))) (.neg (.mul (.mul (.var 0) (.var 1)) (.var 1))) (by decide +kernel)
    rw [hk, Shell.one_mul] at e
    exact e
  · exact Shell.Frame.RE.sound (Shell.Frame.look [ν, k]) (.add (.mul .zero (.var 1)) (.mul (.neg (.var 1)) .zero)) .zero (by decide +kernel)

/-- 27:C15 — the rays that one chronon keeps. If `diag(g, 1)` multiplies the vector `(x, y)` by a scalar `c`, with
`g − 1` invertible, then `x y = 0`: the ray is the origin or the antipode. -/
theorem fixed_rays {gE kE x y c : Ext p ν} (hk : kE * (gE + -1) = 1) (h1 : gE * x = c * x) (h2 : y = c * y) :
    x * y = 0 := by
  have e : ((gE + -1) * (x * y)) = (((gE * x) * y) + -(x * y)) := xsound (xlook [gE, x, y]) (.mul (.add (.var 0) (.neg .one)) (.mul (.var 1) (.var 2))) (.add (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.neg (.mul (.var 1) (.var 2)))) (by decide +kernel)
  rw [h1] at e
  have e2 : ((c * x) * y) = (x * (c * y)) := xsound (xlook [c, x, y]) (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide +kernel)
  rw [e2, ← h2] at e
  have e3 : ((x * y) + -(x * y)) = 0 := xsound (xlook [x, y]) (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 0) (.var 1)))) .zero (by decide +kernel)
  rw [e3] at e
  have e4 : x * y = kE * ((gE + -1) * (x * y)) := by
    have t : (kE * (gE + -1)) * (x * y) = kE * ((gE + -1) * (x * y)) := Ext.mul_assoc _ _ _
    rw [hk, Ext.one_mul] at t
    exact t
  rw [e] at e4
  have z : kE * (0 : Ext p ν) = 0 := xsound (xlook [kE]) (.mul (.var 0) .zero) .zero (by decide +kernel)
  rw [z] at e4
  exact e4

/-- 27:C16 — one charge system in the frame of rank five: the hypercharge cycle and the charge cycle have determinant
one, the first is faithful, the second is trivial on the doublet exactly at the cube roots of unity, the weights on the
sixteen states are `6Y` and `−3Q`, for `d ∣ p + 1`, `d > 1`, some unitary point is no `d`-th power, and where
`p + 2 = 3 j` every unitary point is a cube. -/
theorem one_charge_system (hp : FRC.Nat.isPrime p) (hν : ¬ ∃ y : Shell p, y * y = ν) (h2 : (1 : Shell p) + 1 ≠ 0) :
    (∀ w : Ext p ν, Ext.conj w * w = 1 →
      (Ext.conj w * Ext.conj w) * (Ext.conj w * Ext.conj w) * (Ext.conj w * Ext.conj w) * (w * w * w) * (w * w * w) = 1 ∧
      (Ext.conj w * Ext.conj w = 1 → w * w * w = 1 → w = 1) ∧
      w * w * w * (Ext.conj w * Ext.conj w * Ext.conj w) = 1 ∧
      (Ext.conj w * Ext.conj w * Ext.conj w = 1 ↔ w * w * w = 1)) ∧
    ((Interactions.gen16.all (fun S => -2 * (Interactions.col S : Int) + 3 * (Interactions.wk S : Int) == Interactions.y6 S)) = true ∧
      (Interactions.gen16.all (fun S => 2 * (Interactions.col S : Int) + -(6 * (Interactions.cnt S 3 4 : Int)) == -(Interactions.q6 S))) = true ∧
      (Interactions.gen16.all (fun S => (Interactions.q6 S + 2 * (Interactions.col S : Int)) % 6 == 0)) = true) ∧
    (∀ d m : Nat, p + 1 = d * m → 1 < d →
      ¬∀ w : Ext p ν, Ext.conj w * w = 1 → ¬∀ v : Ext p ν, Ext.conj v * v = 1 → v ^ d ≠ w) ∧
    (∀ j : Nat, p + 2 = 3 * j → ∀ w : Ext p ν, Ext.conj w * w = 1 → Ext.conj (w ^ j) * w ^ j = 1 ∧ (w ^ j) ^ 3 = w) :=
  ⟨fun _ hw => ⟨(hypercharge_cycle hw).1, (hypercharge_cycle hw).2, (charge_cycle hw).1, (charge_cycle hw).2⟩,
   charge_weights, fun _ _ hdm hd => not_all_powers hp hν h2 hdm hd, fun _ hj _ hw => all_cubes hp hν h2 hj hw⟩

end FRC.Unitary
