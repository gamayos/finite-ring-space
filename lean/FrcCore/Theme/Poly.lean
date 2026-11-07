import FrcCore.Theme.Hermitian
/-!
# FrcCore.Theme.Poly — polynomials over `K` (the operator theme)

A polynomial over `K = 𝔽_p[w]/(w² − ν)` is its list of coefficients, the constant term first; trailing zeros are allowed, so
two lists may name one polynomial, and the statements below are about the evaluation map and the coefficients, never about
the lists as such. The operations: sum, negative, scalar multiple, product (the convolution, by recursion on the first
factor), the constants, `X`. The evaluation `eval f x` by Horner's scheme is a ring homomorphism (`eval_padd`, `eval_pneg`,
`eval_psmul`, `eval_pmul`, `eval_C`, `eval_X`), the facts the characteristic polynomial of `Theme/CharPoly` rests on. The
coefficients: `coeff f k` is the `k`-th entry (`0` beyond the list), `DegLE f d` says every coefficient above `d` is zero,
and the coefficient lemmas of the sum and the product (`coeff_padd`, `coeff_pmul_top`) give the leading term of a product.
No axioms.
-/

namespace FRC.Dirac.Poly

open FRC FRC.Extension FRC.Dirac FRC.Dirac.Hermitian
open FRC.Dirac.Mat (nth)

variable {p : Nat} [Pos p] {ν : Shell p}

/-- A polynomial over `K`: its coefficients, the constant term first. -/
abbrev Poly (p : Nat) [Pos p] (ν : Shell p) := List (Ext p ν)

/-! ## The operations -/

def padd : Poly p ν → Poly p ν → Poly p ν
  | [], g => g
  | f, [] => f
  | a :: f, b :: g => (a + b) :: padd f g

def pneg (f : Poly p ν) : Poly p ν := f.map (- ·)

def psmul (c : Ext p ν) (f : Poly p ν) : Poly p ν := f.map (c * ·)

/-- The product by recursion on the first factor: `(a + X f) g = a g + X (f g)`. -/
def pmul : Poly p ν → Poly p ν → Poly p ν
  | [], _ => []
  | a :: f, g => padd (psmul a g) (0 :: pmul f g)

/-- The constant polynomial. -/
def C (a : Ext p ν) : Poly p ν := [a]

/-- The indeterminate. -/
def X : Poly p ν := [0, 1]

/-- Horner's scheme: `eval (a :: f) x = a + x · eval f x`. -/
def eval : Poly p ν → Ext p ν → Ext p ν
  | [], _ => 0
  | a :: f, x => a + x * eval f x

/-- The `k`-th coefficient (`0` beyond the list). -/
def coeff (f : Poly p ν) (k : Nat) : Ext p ν := nth 0 f k

/-- Every coefficient above `d` vanishes. -/
def DegLE (f : Poly p ν) (d : Nat) : Prop := ∀ k, d < k → coeff f k = 0

/-! ## Evaluation is a ring homomorphism -/

theorem eval_nil (x : Ext p ν) : eval ([] : Poly p ν) x = 0 := rfl

theorem eval_cons (a : Ext p ν) (f : Poly p ν) (x : Ext p ν) : eval (a :: f) x = a + x * eval f x := rfl

theorem eval_padd : ∀ (f g : Poly p ν) (x : Ext p ν), eval (padd f g) x = eval f x + eval g x
  | [], g, x => (zero_add _).symm
  | _ :: _, [], x => (add_zero _).symm
  | a :: f, b :: g, x => by
    show a + b + x * eval (padd f g) x = (a + x * eval f x) + (b + x * eval g x)
    rw [eval_padd f g x, mul_add, add_assoc, add_assoc, ← add_assoc b, add_comm b, add_assoc]

theorem eval_pneg : ∀ (f : Poly p ν) (x : Ext p ν), eval (pneg f) x = -(eval f x)
  | [], _ => (neg_zero_ext).symm
  | a :: f, x => by
    show -a + x * eval (pneg f) x = -(a + x * eval f x)
    rw [eval_pneg f x, ← mul_neg, neg_add_eq]
where
  neg_zero_ext : (-0 : Ext p ν) = 0 := Ext.ext Shell.neg_zero Shell.neg_zero
  neg_add_eq (a b : Ext p ν) : -a + -b = -(a + b) := by
    have h : (a + b) + (-a + -b) = 0 := by
      rw [add_assoc, ← add_assoc b, add_comm b, add_assoc, add_neg, add_zero, add_neg]
    have h2 := congrArg (fun z => -(a + b) + z) h
    show -a + -b = -(a + b)
    have : -(a + b) + ((a + b) + (-a + -b)) = -a + -b := by rw [← add_assoc, neg_add, zero_add]
    rw [← this, h, add_zero]

theorem eval_psmul (c : Ext p ν) : ∀ (f : Poly p ν) (x : Ext p ν), eval (psmul c f) x = c * eval f x
  | [], _ => (mul_zero c).symm
  | a :: f, x => by
    show c * a + x * eval (psmul c f) x = c * (a + x * eval f x)
    rw [eval_psmul c f x, mul_add, ← Ext.mul_assoc, Ext.mul_comm x c, Ext.mul_assoc]

theorem eval_pmul : ∀ (f g : Poly p ν) (x : Ext p ν), eval (pmul f g) x = eval f x * eval g x
  | [], g, x => (zero_mul _).symm
  | a :: f, g, x => by
    show eval (padd (psmul a g) (0 :: pmul f g)) x = (a + x * eval f x) * eval g x
    rw [eval_padd, eval_psmul, eval_cons, zero_add, eval_pmul f g x, add_mul, Ext.mul_assoc]

theorem eval_C (a x : Ext p ν) : eval (C a) x = a := by show a + x * 0 = a; rw [mul_zero, add_zero]

theorem eval_X (x : Ext p ν) : eval (X : Poly p ν) x = x := by
  show 0 + x * (1 + x * 0) = x; rw [mul_zero, add_zero, Ext.mul_one, zero_add]

/-! ## Coefficients -/

theorem coeff_nil (k : Nat) : coeff ([] : Poly p ν) k = 0 := rfl

theorem coeff_cons_zero (a : Ext p ν) (f : Poly p ν) : coeff (a :: f) 0 = a := rfl

theorem coeff_cons_succ (a : Ext p ν) (f : Poly p ν) (k : Nat) : coeff (a :: f) (k + 1) = coeff f k := rfl

theorem coeff_padd : ∀ (f g : Poly p ν) (k : Nat), coeff (padd f g) k = coeff f k + coeff g k
  | [], g, k => by show coeff g k = coeff [] k + coeff g k; rw [coeff_nil, zero_add]
  | a :: f, [], k => by show coeff (a :: f) k = coeff (a :: f) k + coeff [] k; rw [coeff_nil, add_zero]
  | _ :: _, _ :: _, 0 => rfl
  | _ :: f, _ :: g, k + 1 => coeff_padd f g k

theorem coeff_psmul (c : Ext p ν) : ∀ (f : Poly p ν) (k : Nat), coeff (psmul c f) k = c * coeff f k
  | [], k => by show coeff [] k = c * coeff [] k; rw [coeff_nil, mul_zero]
  | _ :: _, 0 => rfl
  | _ :: f, k + 1 => coeff_psmul c f k

theorem coeff_pneg : ∀ (f : Poly p ν) (k : Nat), coeff (pneg f) k = -(coeff f k)
  | [], k => by show coeff [] k = -(coeff [] k); rw [coeff_nil]; exact (Ext.ext Shell.neg_zero Shell.neg_zero).symm
  | _ :: _, 0 => rfl
  | _ :: f, k + 1 => coeff_pneg f k

theorem coeff_pmul_zero : ∀ (f g : Poly p ν), coeff (pmul f g) 0 = coeff f 0 * coeff g 0
  | [], g => by show coeff [] 0 = coeff [] 0 * coeff g 0; rw [coeff_nil, zero_mul]
  | a :: f, g => by
    show coeff (padd (psmul a g) (0 :: pmul f g)) 0 = a * coeff g 0
    rw [coeff_padd, coeff_psmul, coeff_cons_zero, add_zero]

theorem coeff_pmul_succ : ∀ (f g : Poly p ν) (k : Nat), coeff (pmul f g) (k + 1) = coeff f 0 * coeff g (k + 1) + coeff (pmul f.tail g) k
  | [], g, k => by show coeff [] (k + 1) = coeff [] 0 * coeff g (k + 1) + coeff (pmul [] g) k; rw [coeff_nil, coeff_nil, zero_mul, zero_add]; rfl
  | a :: f, g, k => by
    show coeff (padd (psmul a g) (0 :: pmul f g)) (k + 1) = a * coeff g (k + 1) + coeff (pmul f g) k
    rw [coeff_padd, coeff_psmul, coeff_cons_succ]

theorem degLE_of_length (f : Poly p ν) (d : Nat) (h : f.length ≤ d + 1) : DegLE f d := fun k hk => by
  show nth 0 f k = 0
  exact nth_beyond' f k (Nat.le_trans h hk)
where
  nth_beyond' : ∀ (l : Poly p ν) (i : Nat), l.length ≤ i → nth 0 l i = 0
    | [], _, _ => rfl
    | _ :: _, 0, h => absurd h (Nat.not_succ_le_zero _)
    | _ :: l, i + 1, h => nth_beyond' l i (Nat.le_of_succ_le_succ h)

theorem degLE_padd (f g : Poly p ν) (d : Nat) (hf : DegLE f d) (hg : DegLE g d) : DegLE (padd f g) d := fun k hk => by
  rw [coeff_padd, hf k hk, hg k hk, add_zero]

theorem degLE_psmul (c : Ext p ν) (f : Poly p ν) (d : Nat) (hf : DegLE f d) : DegLE (psmul c f) d := fun k hk => by
  rw [coeff_psmul, hf k hk, mul_zero]

theorem degLE_pneg (f : Poly p ν) (d : Nat) (hf : DegLE f d) : DegLE (pneg f) d := fun k hk => by
  rw [coeff_pneg, hf k hk]; exact Ext.ext Shell.neg_zero Shell.neg_zero

theorem degLE_mono (f : Poly p ν) {d e : Nat} (hde : d ≤ e) (hf : DegLE f d) : DegLE f e := fun k hk => hf k (Nat.lt_of_le_of_lt hde hk)

theorem degLE_cons (a : Ext p ν) (f : Poly p ν) (d : Nat) (hf : DegLE f d) : DegLE (a :: f) (d + 1) := fun k hk =>
  match k, hk with
  | k + 1, hk => hf k (Nat.lt_of_succ_lt_succ hk)

theorem degLE_tail : ∀ (f : Poly p ν) (d : Nat), DegLE f (d + 1) → DegLE f.tail d
  | [], _, _ => fun _ _ => rfl
  | _ :: _, _, hf => fun k hk => hf (k + 1) (Nat.succ_lt_succ hk)

/-- The degree of a product: `DegLE f d`, `DegLE g e` give `DegLE (f g) (d + e)`. -/
theorem degLE_pmul : ∀ (f g : Poly p ν) (d e : Nat), DegLE f d → DegLE g e → DegLE (pmul f g) (d + e)
  | [], _, _, _, _, _ => fun k _ => rfl
  | a :: f, g, d, e, hf, hg => by
    show DegLE (padd (psmul a g) (0 :: pmul f g)) (d + e)
    match d with
    | 0 =>
      -- `f` is zero beyond its constant term: every coefficient of `f` vanishes, and so does `f · g`
      have hf0 : ∀ k, coeff f k = 0 := fun k => hf (k + 1) (Nat.succ_pos k)
      intro k hk
      rw [coeff_padd, coeff_psmul, hg k (Nat.zero_add e ▸ hk), mul_zero, zero_add]
      match k with
      | 0 => rfl
      | k + 1 => exact coeff_pmul_zero_poly f g hf0 k
    | d + 1 =>
      refine degLE_padd _ _ _ (degLE_mono _ (Nat.le_add_left e (d + 1)) (degLE_psmul a g e hg)) ?_
      have := degLE_pmul f g d e (degLE_tail (a :: f) d hf) hg
      rw [Nat.succ_add]; exact degLE_cons 0 _ _ this
where
  coeff_pmul_zero_poly : ∀ (f g : Poly p ν), (∀ k, coeff f k = 0) → ∀ k, coeff (pmul f g) k = 0
    | [], _, _, _ => rfl
    | a :: f, g, h, k => by
      show coeff (padd (psmul a g) (0 :: pmul f g)) k = 0
      rw [coeff_padd, coeff_psmul, show a = 0 from h 0, zero_mul, zero_add]
      match k with
      | 0 => rfl
      | k + 1 => exact coeff_pmul_zero_poly f g (fun k => h (k + 1)) k

/-- The top coefficient of a product: with `DegLE f d`, `DegLE g e`, `coeff (f g) (d + e) = coeff f d · coeff g e`. -/
theorem coeff_pmul_top : ∀ (f g : Poly p ν) (d e : Nat), DegLE f d → DegLE g e → coeff (pmul f g) (d + e) = coeff f d * coeff g e
  | [], g, d, e, _, _ => by show coeff [] (d + e) = coeff [] d * coeff g e; rw [coeff_nil, coeff_nil, zero_mul]
  | a :: f, g, d, e, hf, hg => by
    show coeff (padd (psmul a g) (0 :: pmul f g)) (d + e) = coeff (a :: f) d * coeff g e
    rw [coeff_padd, coeff_psmul]
    match d with
    | 0 =>
      rw [Nat.zero_add]
      have hf0 : ∀ k, coeff f k = 0 := fun k => hf (k + 1) (Nat.succ_pos k)
      match e with
      | 0 => show a * coeff g 0 + 0 = a * coeff g 0; rw [add_zero]
      | e + 1 =>
        rw [coeff_cons_succ, degLE_pmul.coeff_pmul_zero_poly f g hf0 e, add_zero]; rfl
    | d + 1 =>
      rw [Nat.succ_add, coeff_cons_succ, hg (d + e + 1) (Nat.succ_le_succ (Nat.le_add_left e d)), mul_zero, zero_add,
        coeff_pmul_top f g d e (degLE_tail (a :: f) d hf) hg]
      rfl

end FRC.Dirac.Poly
