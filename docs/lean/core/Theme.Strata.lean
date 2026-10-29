import FrcCore.Nat

/-!
# FrcCore.Theme.Strata — the fixed-setting Bell weight is no tally (22:C28), and the framed readout on the sweep (22:C29)
(the quantum theme; 22-quantum, the Y1 and Y2 pushes of 29 October 2026, landed the same day)

The Tsirelson weights of the `C₈` Bell configuration are `W± = 2 ± √2`, elements of `ℤ[√2]` written on the basis
`(1, √2)` as integer pairs. For `B` copies read at one fixed Tsirelson setting the structural weight of a registration
string with `a` agreeing and `b` disagreeing pairs is `W₊^a W₋^b`. The file decides:

* `pow_Wp_eq`, `B_pos`, `pow_Wp_irrational`: the coordinates of `(2 + √2)^m` are the naturals `(A_m, B_m)` of the
  recursion `A_{m+1} = 2A_m + 2B_m`, `B_{m+1} = A_m + 2B_m` from `(1, 0)`, with `B_m ≥ 1` for every `m ≥ 1`, so no
  power `(2 + √2)^m`, `m ≥ 1`, is a rational integer — unbounded, by induction;
* `Wp_mul_Wm`: `W₊ W₋ = 2`, so `W₊^a W₋^b = 2^{min(a,b)} W_±^{|a−b|}` and the string weight is rational exactly on the
  balanced strings `a = b`; the identity on the strings themselves is exhausted on the box `a, b < 13`
  (`string_rational_iff_box`, `string_succ_box`), the Galois trace recurrence `t_{m+2} = 4t_{m+1} − 2t_m` on `m < 12`
  (`trace_rec_box`), as the paper's witness exhausts them;
* `trace_rational`: the Galois trace `x + x̄`, the sum of a string's weight with its conjugate-setting weight, has
  zero `√2`-coordinate for every `x`.

Together with the conservation of the relative offset under the diagonal drive (`Theme/Composite.lean`, 22:C15) this
is 22:C28, the obstruction to a counting theorem for the stratum-sampling realisation 22:B9 (the former hypothesis Y1):
the drive never presents a second setting, and no fixed-setting string weight is a tally unless the string is balanced.

The second part (22:C29, the former hypothesis Y2) is the framed readout at every setting of the sweep, on counts alone
(`Readout`), and the bounded-discrepancy law of the largest-remainder rule, one outcome at a time: with the
readout `a/D` of an outcome and `B` runs, `B a = D f + r`, `r < D`, and a residual unit `δ ≤ 1`, the count `N = f + δ`
satisfies `|D N − B a| ≤ D`, that is `|N − B a/D| ≤ 1` (`hamilton_component`, `hamilton_count`). The rule's existence
(the residual is below the number of outcomes, so each outcome receives at most one unit) is the sum of the fractional
parts, an integer below the number of outcomes, decided by the ledger file on the configuration. No axioms.
-/

namespace FRC.Strata

/-- An element `a + b √2` of `ℤ[√2]` on the basis `(1, √2)`. -/
structure Q2 where
  a : Int
  b : Int
deriving DecidableEq

namespace Q2

/-- The product `(a + b√2)(c + d√2) = (ac + 2bd) + (ad + bc)√2`. -/
def mul (x y : Q2) : Q2 := ⟨x.a * y.a + 2 * (x.b * y.b), x.a * y.b + x.b * y.a⟩

/-- The Galois conjugation `√2 ↦ −√2`, realised in the Bell configuration by the setting shift `Δ ↦ 40 − Δ`. -/
def conj (x : Q2) : Q2 := ⟨x.a, -x.b⟩

/-- Powers. -/
def pow (x : Q2) : Nat → Q2
  | 0 => ⟨1, 0⟩
  | n + 1 => mul (pow x n) x

/-- An element is a rational integer when its `√2`-coordinate vanishes. -/
def rational (x : Q2) : Prop := x.b = 0

instance (x : Q2) : Decidable (rational x) := inferInstanceAs (Decidable (x.b = 0))

/-- The trace `x + x̄ = 2a`. -/
def trace (x : Q2) : Int := 2 * x.a

/-- `W₊ = 2 + √2`, the agreeing Tsirelson weight. -/
def Wp : Q2 := ⟨2, 1⟩

/-- `W₋ = 2 − √2`, the disagreeing Tsirelson weight, the conjugate of `W₊`. -/
def Wm : Q2 := ⟨2, -1⟩

theorem Wm_eq_conj : Wm = conj Wp := rfl

/-- 22:C28 — `W₊ W₋ = (2 + √2)(2 − √2) = 2`: an agreeing and a disagreeing pair cancel to the tally `2`. -/
theorem Wp_mul_Wm : mul Wp Wm = ⟨2, 0⟩ := by decide

/-- The natural coordinates `(A_m, B_m)` of `(2 + √2)^m`: `A_{m+1} = 2A_m + 2B_m`, `B_{m+1} = A_m + 2B_m`. -/
def AB : Nat → Nat × Nat
  | 0 => (1, 0)
  | m + 1 => ((AB m).1 * 2 + 2 * ((AB m).2 * 1), (AB m).1 * 1 + (AB m).2 * 2)

/-- `(2 + √2)^m` has the coordinates `(A_m, B_m)`. -/
theorem pow_Wp_eq : ∀ m, pow Wp m = ⟨Int.ofNat (AB m).1, Int.ofNat (AB m).2⟩
  | 0 => rfl
  | m + 1 => by
    show mul (pow Wp m) Wp = _
    rw [pow_Wp_eq m]
    rfl

/-- `A_m ≥ 1` for every `m`. -/
theorem A_pos : ∀ m, 0 < (AB m).1
  | 0 => Nat.zero_lt_one
  | m + 1 => Nat.add_pos_left (Nat.mul_pos (A_pos m) (Nat.zero_lt_succ 1)) _

/-- `B_{m+1} ≥ 1` for every `m`: no power `(2 + √2)^{m+1}` lies in `ℤ`. -/
theorem B_pos (m : Nat) : 0 < (AB (m + 1)).2 :=
  Nat.add_pos_left (Nat.mul_pos (A_pos m) Nat.zero_lt_one) _

/-- 22:C28 — `(2 + √2)^{m+1}` is irrational for every `m`: the agreeing Tsirelson weight
raised to any positive power is no realised tally. -/
theorem pow_Wp_irrational (m : Nat) : ¬ rational (pow Wp (m + 1)) := by
  rw [pow_Wp_eq]
  show Int.ofNat (AB (m + 1)).2 ≠ 0
  intro h
  exact Nat.ne_of_gt (B_pos m) (Int.ofNat_eq_zero.mp h)

/-- The structural weight of a fixed-setting registration string with `a` agreeing and `b` disagreeing pairs. -/
def string (a b : Nat) : Q2 := mul (pow Wp a) (pow Wm b)

/-- 22:C28 — on the box `a, b < 13` the string weight `W₊^a W₋^b` is a rational integer exactly when
the string is balanced, `a = b`; the unbounded statement follows from `pow_Wp_irrational` and `W₊ W₋ = 2`. -/
theorem string_rational_iff_box : ∀ a, a < 13 → ∀ b, b < 13 → (rational (string a b) ↔ a = b) := by
  decide +kernel

/-- One agreeing and one disagreeing pair cancel to the tally `2`, on the box. -/
theorem string_succ_box : ∀ a, a < 12 → ∀ b, b < 12 →
    string (a + 1) (b + 1) = ⟨2 * (string a b).a, 2 * (string a b).b⟩ := by
  decide +kernel

/-- On a balanced string the weight is the tally `2^a`, on the box. -/
theorem string_balanced_box : ∀ a, a < 13 → string a a = ⟨Int.ofNat (2 ^ a), 0⟩ := by
  decide +kernel

/-- `z + −z = 0` on the integers, by cases, without `propext`. -/
theorem add_neg_self : ∀ z : Int, z + -z = 0
  | Int.ofNat 0 => rfl
  | Int.ofNat (k + 1) => Int.subNatNat_self (k + 1)
  | Int.negSucc k => Int.subNatNat_self (k + 1)

/-- 22:C28 — the Galois trace `x + x̄` is rational for every `x`: a string summed with its conjugate-setting string is a tally. -/
theorem trace_rational (x : Q2) : rational ⟨x.a + (conj x).a, x.b + (conj x).b⟩ :=
  add_neg_self x.b

/-- The traces `t_m = tr (2 + √2)^m` obey `t_{m+2} = 4 t_{m+1} − 2 t_m` from `t₀ = 2`, `t₁ = 4`, on the box. -/
theorem trace_rec_box : ∀ m, m < 12 →
    trace (pow Wp (m + 2)) = 4 * trace (pow Wp (m + 1)) - 2 * trace (pow Wp m) := by
  decide +kernel

theorem trace_zero : trace (pow Wp 0) = 2 := by decide
theorem trace_one : trace (pow Wp 1) = 4 := by decide

end Q2

/-! ## The bounded-discrepancy law of the largest-remainder rule (22:Y2) -/

/-- One outcome of the largest-remainder rule: with `B a = D f + r`, `r < D`, and a residual unit `δ ≤ 1`, the count
`N = f + δ` satisfies `D N ≤ B a + D` and `B a < D N + D`, that is `|N − B a/D| ≤ 1`. -/
theorem hamilton_component {B a D f r δ : Nat} (hdiv : B * a = D * f + r) (hr : r < D) (hδ : δ ≤ 1) :
    D * (f + δ) ≤ B * a + D ∧ B * a < D * (f + δ) + D := by
  rw [hdiv, Nat.mul_add]
  constructor
  · have h1 : D * δ ≤ D := by
      have := Nat.mul_le_mul_left D hδ
      rwa [Nat.mul_one] at this
    rw [Nat.add_assoc]
    exact Nat.add_le_add_left (Nat.le_trans h1 (Nat.le_add_left D r)) _
  · rw [Nat.add_assoc]
    exact Nat.add_lt_add_left (Nat.lt_of_lt_of_le hr (Nat.le_add_left D (D * δ))) _

/-- 22:C29 — the bounded-discrepancy law: for a readout `a/D` and `B` runs the provisional count `f = ⌊B a / D⌋` exists
with `B a = D f + (B a mod D)`, and with any residual unit `δ ≤ 1` the registered count `f + δ` lies within one of
`B a/D`. -/
theorem hamilton_count (B a D δ : Nat) (hD : 0 < D) (hδ : δ ≤ 1) :
    ∃ f, B * a = D * f + B * a % D ∧ D * (f + δ) ≤ B * a + D ∧ B * a < D * (f + δ) + D := by
  obtain ⟨f, hf⟩ := FRC.Nat.mod_spec D hD (B * a)
  exact ⟨f, hf, hamilton_component hf (Nat.mod_lt _ hD) hδ⟩

/-! ## The framed readout at every setting (22:Y2), on counts alone

A framed rational is a numerator over a denominator, both counts. The readout of a weight `(u + v c)/b` at scale `G = gⁿ`
is `(uG + v s)/(bG)`, where `s` is the integer part of `G c`: for `c = √m` the two-sided bound `s² ≤ mG² < (s + 1)²`
(`IsSqrt` of `Theme/Window.lean`, restated here as the two-sided bound); for a general totally real `c` the grid cell of the root of its isolating
integer polynomial `Q`, that is `Q(s/G) = 0` or a sign change of `Q` between `s/G` and `(s + 1)/G`, both read on the
homogenised integer `Gᵈ Q(s/G)`. The irrational `c` never appears: only its cell on the Subject's grid. -/

namespace Readout

/-- The homogenised evaluation `Gᵈ Q(s/G)` of an integer polynomial `Q` (coefficients low degree first): an integer. -/
def hom : List Int → Int → Int → Int
  | [], _, _ => 0
  | q :: qs, s, G => q * G ^ qs.length + s * hom qs s G

/-- The grid cell of a root: `Q` vanishes at `s/G`, or changes sign between `s/G` and `(s + 1)/G`. This is the
integer-part certificate; for `Q = X² − m` it is the two-sided bound of the integer square root. -/
def IsCell (Q : List Int) (G s : Int) : Prop := hom Q s G = 0 ∨ hom Q s G * hom Q (s + 1) G < 0

instance (Q : List Int) (G s : Int) : Decidable (IsCell Q G s) := inferInstanceAs (Decidable (_ ∨ _))

/-- 22:C29 — the readout pair of a setting, numerators over the denominator `bG`: the two weights `(u ± c)/b` share the integer
part `s` of `Gc`, so their readouts sum to `2u/b` exactly, on counts: `(uG + s) + (uG − s) = uG + uG`. -/
theorem pair_sum {uG s : Nat} (h : s ≤ uG) : (uG + s) + (uG - s) = uG + uG := by
  rw [Nat.add_assoc, FRC.Nat.add_sub_of_le h]

/-- The Chebyshev-type polynomials `P₂₀`, `P₁₀`, `P₅` (`P₀ = 2`, `P₁ = X`, `P_{k+1} = X P_k − P_{k−1}`), whose roots
are the trace elements `c_Δ = ζ₈₀^Δ + ζ₈₀^{−Δ}` of the odd settings, the settings `≡ 2 (mod 4)` and `≡ 4 (mod 8)`. -/
def P20 : List Int := [2, 0, -100, 0, 825, 0, -2640, 0, 4290, 0, -4004, 0, 2275, 0, -800, 0, 170, 0, -20, 0, 1]
def P10 : List Int := [-2, 0, 25, 0, -50, 0, 35, 0, -10, 0, 1]
def P5 : List Int := [0, 5, 0, -5, 0, 1]

/-- The isolating polynomial of the setting `Δ` (`c_Δ = c_{80−Δ}`): `P₂₀`, `P₁₀`, `P₅`, the golden quadratics
`X² ∓ X − 1`, or `X ∓ 2`. -/
def polyOf (D : Nat) : List Int :=
  let d := D % 80
  let m := if d ≤ 40 then d else 80 - d
  if m % 2 = 1 then P20
  else if m % 4 = 2 then P10
  else if m % 8 = 4 then P5
  else if m = 8 ∨ m = 24 then [-1, -1, 1]
  else if m = 16 ∨ m = 32 then [-1, 1, 1]
  else if m = 0 then [-2, 1] else [2, 1]

/-- The `n`-th entry of a list of integers (`0` past the end), structurally, so that the kernel evaluates it. -/
def nth : List Int → Nat → Int
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, n + 1 => nth xs n

/-- Membership in a list of integers as a Boolean, structurally. -/
def mem : List Int → Int → Bool
  | [], _ => false
  | x :: xs, y => if x = y then true else mem xs y

/-- The integer parts `s₄(Δ) = ⌊81 c_Δ⌋` at the paper's worked scale `n = 4` (`g = 3`), all 80 settings. -/
def s4 : List Int := [162, 161, 160, 157, 154, 149, 144, 138, 131, 123, 114, 105, 95, 84, 73, 61, 50, 37, 25, 12, 0,
  -13, -26, -38, -51, -62, -74, -85, -96, -106, -115, -124, -132, -139, -145, -150, -155, -158, -161, -162, -162,
  -162, -161, -158, -155, -150, -145, -139, -132, -124, -115, -106, -96, -85, -74, -62, -51, -38, -26, -13, 0, 12,
  25, 37, 50, 61, 73, 84, 95, 105, 114, 123, 131, 138, 144, 149, 154, 157, 160, 161]

/-- 22:C29 — at scale `n = 4` every setting's integer part is certified by its isolating polynomial: `s₄(Δ)` is the
grid cell of the root `c_Δ` for all 80 settings, decided by the kernel on the homogenised integers. -/
theorem cells_all_settings : ∀ D, D < 80 → IsCell (polyOf D) 81 (nth s4 D) := by decide +kernel

/-- 22:C29 — the cells of `P₂₀` on the grid of scale `81` over `[−2, 2]`: exactly the twenty integer parts of the odd settings,
one cell per root and no cell holding two — the finite isolation of all twenty roots. -/
theorem cells_P20 : ∀ k : Nat, k < 325 → (IsCell P20 81 ((k : Int) - 162) ↔
    mem [-162, -158, -150, -139, -124, -106, -85, -62, -38, -13, 12, 37, 61, 84, 105, 123, 138, 149, 157, 161] ((k : Int) - 162) = true) := by
  decide +kernel

/-- The cells of `P₁₀` and `P₅` at scale `81`: ten and five, the integer parts of the settings `≡ 2 (mod 4)` and
`≡ 4 (mod 8)`. -/
theorem cells_P10 : ∀ k : Nat, k < 325 → (IsCell P10 81 ((k : Int) - 162) ↔
    mem [-161, -145, -115, -74, -26, 25, 73, 114, 144, 160] ((k : Int) - 162) = true) := by
  decide +kernel

theorem cells_P5 : ∀ k : Nat, k < 325 → (IsCell P5 81 ((k : Int) - 162) ↔ mem [-155, -96, 0, 95, 154] ((k : Int) - 162) = true) := by
  decide +kernel

/-- 22:C29 — restriction: at the Tsirelson setting the cell certificate of `X² − 2` is the two-sided bound of the integer
square root of `2 · 81²`, `114² ≤ 2 · 81² < 115²` (`s₄ = 114`), and the readout numerators are `2 · 81 ± 114 = 276, 48`
over `8 · 81 = 648`: the paper's `23/54` and `2/27`. -/
theorem tsirelson_restriction : IsCell [-2, 0, 1] 81 114 ∧ (114 * 114 ≤ 2 * 81 * 81 ∧ 2 * 81 * 81 < 115 * 115) ∧
    2 * 81 + 114 = 276 ∧ 2 * 81 - 114 = 48 ∧ 8 * 81 = 648 := by decide

/-- 22:C29 — the four classical settings read exactly: the cell is the exact point `Gc` (`hom = 0`), the readout is the weight. -/
theorem classical_exact : hom (polyOf 0) 162 81 = 0 ∧ hom (polyOf 20) 0 81 = 0 ∧ hom (polyOf 40) (-162) 81 = 0 ∧
    hom (polyOf 60) 0 81 = 0 := by decide

end Readout

end FRC.Strata
