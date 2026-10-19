import FrcCore.Theme.Hadrons
import FrcCore.Ring

/-!
# FrcCore.Theme.Super — the super theme (superconductivity on the split torus, 19 October 2026)

The exact content of the master's rows G19 (superconductivity, structure) and G20 (superconductivity, duality), developed
in the master without a paper ledger (34-super is unpublished; its theorems C1, C3–C5, C9, C10 and its prediction D1 are
the content), as `frc/super.py` and `frc/ledgers/master/super.py` compute it: the phase-neutral pairs of a cycle are the
inverse pairs `(k, −k)` (`winding_pairs`, G19), the charge-`2` condensate leaves the residual `ℤ₂` on every cycle of length
`4m` (`residual_two`, G19), the self-dual point `β* = ½ ln(1 + √2)` as a ring identity in `√2` (`self_dual_point`, G19),
the symplectic quarter-turn on the charge–flux lattice (`symplectic_quarter_turn`, G20), the metrology closure
`K_J R_K Q = 4` (`metrology_closure`, G20) and the even and odd Airy ladders of the vortex core by Sturm's count
(`airy_ladder_sturm`, G20). Kernel-decided or ring-normalised throughout; no axioms (`check_core_axioms.py`).
-/

namespace FRC.Super

open FRC.Shell FRC.Shell.Frame

/-! ## The phase-neutral pairs and the residual `ℤ₂` (00:G19; 34-super C3, C4) -/

/-- The two-body neutral composites of a cycle of length `q`: the pairs `(a, b)` with `a + b ≡ 0 (mod q)`, as a list. -/
def neutralPairs (q : Nat) : List (Nat × Nat) :=
  (List.range q).flatMap fun a => ((List.range q).filter fun b => (a + b) % q == 0).map fun b => (a, b)

/-- The three-body neutral composites of a cycle of length `q`. -/
def neutralTriples (q : Nat) : List (Nat × Nat × Nat) :=
  (List.range q).flatMap fun a => (List.range q).flatMap fun b =>
    ((List.range q).filter fun c => (a + b + c) % q == 0).map fun c => (a, b, c)

/-- 00:G19 — the phase-neutral pair is the inverse pair: on every shell, `a + b = 0` forces `b = −a` (the zero-total-winding
Cooper pair `(k, −k)`); on the substrates `q = 16, 28, 40, 52, 88, 100` the two-body neutral set has exactly `q` members, each
`(a, (q − a) mod q)`, and on `q = 16, 28` the three-body neutral set has `q²` members. -/
theorem winding_pairs :
    (∀ {q : Nat} [Pos q] (a b : Shell q), a + b = 0 → b = -a) ∧
    ([16, 28, 40, 52, 88, 100].all fun q =>
      (neutralPairs q).length == q && (neutralPairs q).all fun ab => ab.2 == (q - ab.1) % q) = true ∧
    ([16, 28].all fun q => (neutralTriples q).length == q * q) = true :=
  ⟨fun a b h => (neg_eq_of_add_eq_zero h).symm, by decide +kernel, by decide +kernel⟩

/-- The vorticities `b < q` with `2b ≡ 0 (mod q)`: the subgroup the charge-`2` condensate leaves deconfined. -/
def residual (q : Nat) : List Nat := (List.range q).filter fun b => (2 * b) % q == 0

/-- 00:G19 — the charge-`2` condensate leaves the residual `ℤ₂`: on every cycle of length `4m`, the solutions `b < 4m` of
`2b ≡ 0 (mod 4m)` are exactly `0` and `2m` — two of them, the flux quantum `h/2e` the half of the cycle; on the substrates
`q = 16, 28, 40, 52, 88, 100` the residual list is `[0, q/2]`. -/
theorem residual_two :
    (∀ m b : Nat, 0 < m → b < 4 * m → (2 * b) % (4 * m) = 0 → b = 0 ∨ b = 2 * m) ∧
    (∀ m : Nat, 0 < m → (2 * 0) % (4 * m) = 0 ∧ (2 * (2 * m)) % (4 * m) = 0) ∧
    ([16, 28, 40, 52, 88, 100].all fun q => residual q == [0, q / 2]) = true := by
  refine ⟨?_, ?_, by decide +kernel⟩
  · intro m b hm hb h
    have h4 : 0 < 4 * m := Nat.mul_pos (by decide) hm
    obtain ⟨t, ht⟩ := FRC.Nat.mod_spec (4 * m) h4 (2 * b)
    rw [h, Nat.add_zero] at ht
    have hb' : b = 2 * m * t := by
      apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 by decide)
      rw [ht, ← FRC.Nat.mul_assoc, ← FRC.Nat.mul_assoc]
    have hb4 : b < 2 * m * 2 := by
      rw [FRC.Nat.mul_assoc, Nat.mul_comm m 2, ← FRC.Nat.mul_assoc]
      exact hb
    have ht2 : t < 2 := by                                   -- without the classical `Nat.lt_of_mul_lt_mul_left`
      match Nat.lt_or_ge t 2 with
      | Or.inl h => exact h
      | Or.inr h =>
        have : 2 * m * 2 ≤ b := by rw [hb']; exact Nat.mul_le_mul_left (2 * m) h
        exact absurd (Nat.lt_of_lt_of_le hb4 this) (Nat.lt_irrefl _)
    cases t with                                             -- `cases`, not `match`: the latter's impossible case uses propext
    | zero => exact Or.inl (by rw [hb', Nat.mul_zero])
    | succ t => cases t with
      | zero => exact Or.inr (by rw [hb', Nat.mul_one])
      | succ t => exact absurd ht2 (Nat.not_lt_of_le (Nat.le_add_left 2 t))
  · intro m hm
    exact ⟨rfl, by rw [← FRC.Nat.mul_assoc]; exact FRC.Nat.mod_self (4 * m) (Nat.mul_pos (by decide) hm)⟩

/-! ## The self-dual point as a ring identity in `√2` (00:G19; 34-super C5) -/

/-- 00:G19 — with `w² = 2` (every shell carrying `√2`, and `ℤ[√2]`) and `x = e^{2β*} = 1 + w`: `(1 + w)(w − 1) = 1`, so
`x − x⁻¹ = (1 + w) − (w − 1) = 2` and `sinh 2β* = 1`; `(2 + w)(w − 1) = w`, so `tanh β* = (x − 1)/(x + 1) = w/(2 + w) = w − 1 =
√2 − 1`; the vortex line tension `τ(β*) = 2β* + ln tanh β* = ln[(1 + w)(w − 1)] = ln 1 = 0`; and `x² − 2x − 1 = 0`, the
fixed point of the duality `sinh 2β sinh 2β̃ = 1`: `β* = ½ ln(1 + √2)` is the self-dual point, where the vortex deconfines. -/
theorem self_dual_point {p : Nat} [Pos p] (w : Shell p) (hw : w * w = 1 + 1) :
    (1 + w) * (w + -1) = 1 ∧ 1 + w + -(w + -1) = 1 + 1 ∧ (1 + 1 + w) * (w + -1) = w ∧
    (1 + w) * (1 + w) + -((1 + 1) * (1 + w)) + -1 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e : (1 + w) * (w + -1) = w * w + -1 := RE.sound (look [w]) (.mul (.add .one (.var 0)) (.add (.var 0) (.neg .one))) (.add (.mul (.var 0) (.var 0)) (.neg .one)) (by decide +kernel)
    rw [e, hw]
    exact RE.sound (look []) (.add (.add .one .one) (.neg .one)) .one (by decide +kernel)
  · exact RE.sound (look [w]) (.add (.add .one (.var 0)) (.neg (.add (.var 0) (.neg .one)))) (.add .one .one) (by decide +kernel)
  · have e : (1 + 1 + w) * (w + -1) = w * w + -(1 + 1) + w := RE.sound (look [w]) (.mul (.add (.add .one .one) (.var 0)) (.add (.var 0) (.neg .one))) (.add (.add (.mul (.var 0) (.var 0)) (.neg (.add .one .one))) (.var 0)) (by decide +kernel)
    rw [e, hw]
    exact RE.sound (look [w]) (.add (.add (.add .one .one) (.neg (.add .one .one))) (.var 0)) (.var 0) (by decide +kernel)
  · have e : (1 + w) * (1 + w) + -((1 + 1) * (1 + w)) + -1 = w * w + -(1 + 1) := RE.sound (look [w]) (.add (.add (.mul (.add .one (.var 0)) (.add .one (.var 0))) (.neg (.mul (.add .one .one) (.add .one (.var 0))))) (.neg .one)) (.add (.mul (.var 0) (.var 0)) (.neg (.add .one .one))) (by decide +kernel)
    rw [e, hw]
    exact RE.sound (look []) (.add (.add .one .one) (.neg (.add .one .one))) .zero (by decide +kernel)

/-! ## The symplectic quarter-turn on the charge–flux lattice (00:G20; 34-super C9) -/

/-- The electric–magnetic dual `S(a, b) = (b, −a)` on the charge–flux lattice. -/
def S {p : Nat} [Pos p] (v : Shell p × Shell p) : Shell p × Shell p := (v.2, -v.1)

/-- The Dirac pairing `ω((a, b), (a', b')) = ab' − a'b`. -/
def pairing {p : Nat} [Pos p] (u v : Shell p × Shell p) : Shell p := u.1 * v.2 + -(v.1 * u.2)

/-- 00:G20 — the duality is a symplectic quarter-turn: `S² = −I` (charge conjugation), `S⁴ = I`, the pairing `ab' − a'b` is
`S`-invariant, the condensate `(2, 0)` goes to the double vortex `(0, −2)` and the unit vortex `(0, 1)` to the unit charge
`(1, 0)` — charge and flux exchanged, Wilson and 't Hooft loops exchanged, on every shell. -/
theorem symplectic_quarter_turn {p : Nat} [Pos p] (a b a' b' : Shell p) :
    S (S (a, b)) = (-a, -b) ∧ S (S (S (S (a, b)))) = (a, b) ∧
    pairing (S (a, b)) (S (a', b')) = pairing (a, b) (a', b') ∧
    S ((1 : Shell p) + 1, 0) = (0, -(1 + 1)) ∧ S ((0 : Shell p), 1) = (1, 0) := by
  refine ⟨rfl, ?_, ?_, rfl, ?_⟩
  · show (- -a, - -b) = (a, b)
    rw [neg_neg a, neg_neg b]
  · show b * -a' + -(b' * -a) = a * b' + -(a' * b)
    exact RE.sound (look [a, b, a', b']) (.add (.mul (.var 1) (.neg (.var 2))) (.neg (.mul (.var 3) (.neg (.var 0))))) (.add (.mul (.var 0) (.var 3)) (.neg (.mul (.var 2) (.var 1)))) (by decide +kernel)
  · show ((1 : Shell p), -(0 : Shell p)) = (1, 0)
    rw [neg_zero]

/-! ## The metrology closure (00:G20; 34-super C10) -/

/-- 00:G20 — the charge–flux duality of the quantised relations, with the inverses `E = e⁻¹`, `Hi = h⁻¹` and the half `t`
(`2t = 1`) as shell elements: the Josephson constant `K_J = 2e/h`, the von Klitzing resistance `R_K = h/e²` and the current
quantum `Q` close the metrology triangle on an integer, `K_J R_K Q = 4 = q_c²` for the pair quantum `Q = 2e` and `2` for the
single-electron quantum `Q = e`; the condensate charge `2e` and the flux quantum `h/2e` multiply to the action quantum `h`.
Each is a ring identity in `e, h, E, Hi, t` with the hypotheses `eE = 1`, `hHi = 1`, `2t = 1` applied. -/
theorem metrology_closure {p : Nat} [Pos p] (e h E Hi t : Shell p) (he : e * E = 1) (hh : h * Hi = 1) (ht : (1 + 1) * t = 1) :
    (1 + 1) * e * Hi * (h * E * E) * ((1 + 1) * e) = 1 + 1 + 1 + 1 ∧
    (1 + 1) * e * Hi * (h * E * E) * e = 1 + 1 ∧
    (1 + 1) * e * (h * E * t) = h := by
  refine ⟨?_, ?_, ?_⟩
  · have i : (1 + 1) * e * Hi * (h * E * E) * ((1 + 1) * e) = (1 + 1 + 1 + 1) * (e * E) * (e * E) * (h * Hi) := RE.sound (look [e, h, E, Hi, t]) (.mul (.mul (.mul (.mul (.add .one .one) (.var 0)) (.var 3)) (.mul (.mul (.var 1) (.var 2)) (.var 2))) (.mul (.add .one .one) (.var 0))) (.mul (.mul (.mul (.add (.add (.add .one .one) .one) .one) (.mul (.var 0) (.var 2))) (.mul (.var 0) (.var 2))) (.mul (.var 1) (.var 3))) (by decide +kernel)
    rw [i, he, hh]
    exact RE.sound (look []) (.mul (.mul (.mul (.add (.add (.add .one .one) .one) .one) .one) .one) .one) (.add (.add (.add .one .one) .one) .one) (by decide +kernel)
  · have i : (1 + 1) * e * Hi * (h * E * E) * e = (1 + 1) * (e * E) * (e * E) * (h * Hi) := RE.sound (look [e, h, E, Hi, t]) (.mul (.mul (.mul (.mul (.add .one .one) (.var 0)) (.var 3)) (.mul (.mul (.var 1) (.var 2)) (.var 2))) (.var 0)) (.mul (.mul (.mul (.add .one .one) (.mul (.var 0) (.var 2))) (.mul (.var 0) (.var 2))) (.mul (.var 1) (.var 3))) (by decide +kernel)
    rw [i, he, hh]
    exact RE.sound (look []) (.mul (.mul (.mul (.add .one .one) .one) .one) .one) (.add .one .one) (by decide +kernel)
  · have i : (1 + 1) * e * (h * E * t) = h * (e * E) * ((1 + 1) * t) := RE.sound (look [e, h, E, Hi, t]) (.mul (.mul (.add .one .one) (.var 0)) (.mul (.mul (.var 1) (.var 2)) (.var 4))) (.mul (.mul (.var 1) (.mul (.var 0) (.var 2))) (.mul (.add .one .one) (.var 4))) (by decide +kernel)
    rw [i, he, ht]
    exact RE.sound (look [h]) (.mul (.mul (.var 0) .one) .one) (.var 0) (by decide +kernel)

/-! ## The even and odd Airy ladders of the vortex core by Sturm's count (00:G20; 34-super D1) -/

/-- The leading principal minors of the even (Neumann) operator's integer tridiagonal on the sites `k = 0 … N`: the diagonal
`2c + L³ k` with `c = (N + 1)³`, the squared off-diagonal `2c²` on the first link (the origin's symmetrising rescaling,
`u(−h) = u(h)`) and `c²` on the others; `(p_k, p_{k−1}, sign changes)`, as `FRC.Hadrons.sturmAux` for the odd (Dirichlet)
operator. -/
def sturmEvenAux (N L : Nat) (μ : Int) : Nat → Int × Int × Nat
  | 0 => (1, 1, 0)
  | k + 1 =>
    let (pm, pmm, acc) := sturmEvenAux N L μ k
    let c : Int := ((N + 1) ^ 3 : Nat)
    let d : Int := 2 * c + (L ^ 3 : Nat) * (k : Nat)
    let cc : Int := if k = 1 then 2 * c * c else c * c
    let cur := (d - μ) * pm - (if k = 0 then 0 else cc * pmm)
    (cur, pm, if (decide (cur < 0)) != (decide (pm < 0)) then acc + 1 else acc)

/-- Sturm's count of the even operator's eigenvalues below `μ = (N + 1) L² ε`, over its `N + 1` sites. -/
def sturmEven (N L : Nat) (μ : Int) : Nat := (sturmEvenAux N L μ (N + 1)).2.2

/-- 00:G20 — the vortex-core ladder is the Airy ladder, by Sturm's count on `N = 200` sites of `[0, 16]`: the even operator
has exactly one eigenvalue in `(1.018, 1.019)` (`E₁`, the first zero of `Ai'`) and one in `(3.246, 3.247)` (`E₃`, the
second), the odd operator (`FRC.Hadrons.sturm`) exactly one in `(2.337, 2.338)` (`E₂`, the first zero of `Ai`); so the
successive-spacing ratio `ρ = (E₃ − E₂)/(E₂ − E₁)` lies in `(0.687, 0.691)` — the Airy value `0.690`, below the
equally-spaced ladder's `1`. The bracket ends enter as the integer `μ = ⌊201 · 256 · ε⌋`, within `2 × 10⁻⁵` below the
decimal `ε` (the convention of `FRC.Hadrons.airy_sturm`); the python witness `frc.super.airy_ladder` counts at the exact
decimals in `Fraction`s. -/
theorem airy_ladder_sturm :
    sturmEven 200 16 (201 * 256 * 1018 / 1000) = 0 ∧ sturmEven 200 16 (201 * 256 * 1019 / 1000) = 1 ∧
    sturmEven 200 16 (201 * 256 * 3246 / 1000) = 1 ∧ sturmEven 200 16 (201 * 256 * 3247 / 1000) = 2 ∧
    FRC.Hadrons.sturm 200 16 (201 * 256 * 2337 / 1000) = 0 ∧ FRC.Hadrons.sturm 200 16 (201 * 256 * 2338 / 1000) = 1 ∧
    687 * (2338 - 1018) < (3246 - 2338) * 1000 ∧ (3247 - 2337) * 1000 < 691 * (2337 - 1019) ∧
    (3247 - 2337) * 1000 < 1000 * (2337 - 1019) := by
  decide +kernel

end FRC.Super
