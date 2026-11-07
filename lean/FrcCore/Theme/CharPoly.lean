import FrcCore.Theme.Poly
import FrcCore.Theme.Product
/-!
# FrcCore.Theme.CharPoly — the characteristic polynomial over `K` (the operator theme)

The determinant of a matrix with polynomial entries, by the Laplace expansion of `Theme/Det` written over `Theme/Poly`
(`pdet`), evaluates to the determinant of the evaluated matrix (`eval_pdet`). The characteristic polynomial of a square
matrix `H` over `K` is `χ_H = pdet (X·I − H)` (`charPoly`), so that `χ_H(a) = det (aI − H)` (`eval_charPoly`); it is monic
of degree `n` (`degLE_charPoly`, `coeff_charPoly_top`). The Cayley denominator of 8-dirac is `I − αH = α (α⁻¹I − H)`, so
`det (I − αH) = αⁿ χ_H(α⁻¹)` (`det_cayleyDen_charPoly`) and a nonzero `α` is admissible exactly when `χ_H(α⁻¹) ≠ 0`
(`cayleyDen_singular_iff_charPoly`): the classification of 8:C17 reads the excluded parameters off the roots of `χ_H` in
`K⁻`. No axioms.
-/

namespace FRC.Dirac.Det

open FRC FRC.Extension FRC.Dirac FRC.Dirac.Hermitian FRC.Dirac.Poly
open FRC.Dirac.Mat (nth)
open FRC.Shell (Frame)
open FRC.Shell.Frame (IsSquare)

variable {p : Nat} [Pos p] {ν : Shell p}

/-! ## The determinant with polynomial entries -/

/-- A matrix with polynomial entries: its rows. -/
abbrev PMat (p : Nat) [Pos p] (ν : Shell p) := List (List (Poly p ν))

def prow (M : PMat p ν) (i : Nat) : List (Poly p ν) := nth [] M i
def phead (r : List (Poly p ν)) : Poly p ν := nth [] r 0
def pminor (M : PMat p ν) (i : Nat) : PMat p ν := (removeAt M i).map List.tail

def psgn : Nat → Poly p ν
  | 0 => [1]
  | i + 1 => pneg (psgn i)

def psumFrom (f : Nat → Poly p ν) : Nat → Nat → Poly p ν
  | 0, _ => []
  | k + 1, i => padd (f i) (psumFrom f k (i + 1))

def pterm (d : PMat p ν → Poly p ν) (M : PMat p ν) (i : Nat) : Poly p ν := pmul (pmul (psgn i) (phead (prow M i))) (d (pminor M i))

/-- The expansion along the first column, the number of rows as fuel (the shape of `Theme/Det`'s `detF`). -/
def pdetF : Nat → PMat p ν → Poly p ν
  | 0, _ => [1]
  | _ + 1, [] => [1]
  | n + 1, M@(_ :: _) => psumFrom (pterm (pdetF n) M) M.length 0

def pdet (M : PMat p ν) : Poly p ν := pdetF M.length M

/-- The matrix evaluated at `x`. -/
def evalM (M : PMat p ν) (x : Ext p ν) : Mat p ν := M.map fun r => r.map fun f => eval f x

theorem eval_psgn (x : Ext p ν) : ∀ i : Nat, eval (psgn i) x = sgn i
  | 0 => by show (1 : Ext p ν) + x * 0 = 1; rw [mul_zero, add_zero]
  | i + 1 => by show eval (pneg (psgn i)) x = -(sgn i); rw [eval_pneg, eval_psgn x i]

theorem eval_psumFrom (f : Nat → Poly p ν) (x : Ext p ν) : ∀ k i, eval (psumFrom f k i) x = sumFrom (fun j => eval (f j) x) k i
  | 0, _ => rfl
  | k + 1, i => by
    show eval (padd (f i) (psumFrom f k (i + 1))) x = eval (f i) x + sumFrom (fun j => eval (f j) x) k (i + 1)
    rw [eval_padd, eval_psumFrom f x k (i + 1)]

theorem length_evalM (M : PMat p ν) (x : Ext p ν) : (evalM M x).length = M.length := length_map _ M

theorem row_evalM (M : PMat p ν) (x : Ext p ν) (i : Nat) : row (evalM M x) i = (prow M i).map fun f => eval f x :=
  nth_map (fun r : List (Poly p ν) => r.map fun f => eval f x) [] M i

theorem head_evalM (M : PMat p ν) (x : Ext p ν) (i : Nat) : head (row (evalM M x) i) = eval (phead (prow M i)) x := by
  rw [row_evalM]; exact nth_map (fun f : Poly p ν => eval f x) [] (prow M i) 0

theorem map_tail' {α β : Type} (f : α → β) : ∀ l : List α, (l.map f).tail = l.tail.map f
  | [] => rfl
  | _ :: _ => rfl

theorem evalM_pminor (M : PMat p ν) (x : Ext p ν) (i : Nat) : evalM (pminor M i) x = minor (evalM M x) i := by
  show ((removeAt M i).map List.tail).map (fun r => r.map fun f => eval f x) = (removeAt (M.map fun r => r.map fun f => eval f x) i).map List.tail
  rw [← map_removeAt, map_map', map_map']
  exact map_congr' (fun r => (map_tail' _ r).symm) _

theorem sumFrom_congr' {f g : Nat → Ext p ν} (h : ∀ j, f j = g j) : ∀ (k i : Nat), sumFrom f k i = sumFrom g k i
  | 0, _ => rfl
  | k + 1, i => by show f i + sumFrom f k (i + 1) = g i + sumFrom g k (i + 1); rw [h i, sumFrom_congr' h k (i + 1)]

/-- The evaluation of the polynomial determinant is the determinant of the evaluated matrix. -/
theorem eval_pdetF : ∀ (n : Nat) (M : PMat p ν) (x : Ext p ν), eval (pdetF n M) x = detF n (evalM M x)
  | 0, _, x => by show (1 : Ext p ν) + x * 0 = 1; rw [mul_zero, add_zero]
  | _ + 1, [], x => by show (1 : Ext p ν) + x * 0 = 1; rw [mul_zero, add_zero]
  | n + 1, r :: rest, x => by
    show eval (psumFrom (pterm (pdetF n) (r :: rest)) (r :: rest).length 0) x =
      sumFrom (term (detF n) (evalM (r :: rest) x)) (evalM (r :: rest) x).length 0
    rw [eval_psumFrom, length_evalM]
    refine sumFrom_congr' (fun i => ?_) _ _
    show eval (pmul (pmul (psgn i) (phead (prow (r :: rest) i))) (pdetF n (pminor (r :: rest) i))) x =
      sgn i * head (row (evalM (r :: rest) x) i) * detF n (minor (evalM (r :: rest) x) i)
    rw [eval_pmul, eval_pmul, eval_psgn, head_evalM, eval_pdetF n _ x, evalM_pminor]

theorem eval_pdet (M : PMat p ν) (x : Ext p ν) : eval (pdet M) x = det (evalM M x) := by
  show eval (pdetF M.length M) x = detF (evalM M x).length (evalM M x)
  rw [length_evalM, eval_pdetF]

/-! ## The characteristic polynomial -/

/-- `X·I − H` as a polynomial matrix: the entry `(i, j)` is `−H[i][j] + δ_ij X`. -/
def charMatP (H : Mat p ν) : PMat p ν :=
  (List.range H.length).map fun i => (List.range H.length).map fun j => [-(E H i j), if i = j then 1 else 0]

/-- The characteristic polynomial `χ_H = det (X·I − H)`. -/
def charPoly (H : Mat p ν) : Poly p ν := pdet (charMatP H)

/-- `aI − H`. -/
def charMat (a : Ext p ν) (H : Mat p ν) : Mat p ν := Mat.add (Mat.smul a (Mat.ident H.length)) (Mat.neg H)

theorem nth_range_map {β : Type} (d : β) (f : Nat → β) (n j : Nat) (hj : j < n) : nth d ((List.range n).map f) j = f j := by
  rw [range_eq_rangeS, nth_map_lt f 0 d _ j (by rw [length_rangeS]; exact hj), nth_rangeS n j hj]

theorem length_range_map {β : Type} (f : Nat → β) (n : Nat) : ((List.range n).map f).length = n := by
  rw [length_map, range_eq_rangeS, length_rangeS]

theorem row_charMat (a : Ext p ν) (H : Mat p ν) (i : Nat) (hi : i < H.length) :
    row (charMat a H) i = radd (rsmul a (unitRow H.length i)) ((row H i).map (- ·)) := by
  show nth [] (List.zipWith (fun r s => List.zipWith (· + ·) r s) (Mat.smul a (Mat.ident H.length)) (Mat.neg H)) i = _
  have h1 : i < (Mat.smul a (Mat.ident H.length)).length := by show i < ((Mat.ident _).map _).length; rw [length_map, length_ident]; exact hi
  have h2 : i < (Mat.neg H).length := by show i < (H.map _).length; rw [length_map]; exact hi
  rw [nth_zipWith (fun r s => List.zipWith (· + ·) r s) [] [] [] _ _ i h1 h2, zipWith_add_eq_radd]
  show radd (nth [] ((Mat.ident H.length).map fun r => r.map (a * ·)) i) (nth [] (H.map fun r => r.map (- ·)) i) = _
  rw [nth_map_lt (fun r : List (Ext p ν) => r.map (a * ·)) [] [] _ i (by rw [length_ident]; exact hi),
    nth_map_lt (fun r : List (Ext p ν) => r.map (- ·)) [] [] _ i hi]
  show radd ((row (Mat.ident H.length) i).map (a * ·)) ((row H i).map (- ·)) = _
  rw [row_ident _ _ hi]; rfl

theorem length_charMat (a : Ext p ν) (H : Mat p ν) : (charMat a H).length = H.length := by
  show (List.zipWith _ (Mat.smul a (Mat.ident H.length)) (Mat.neg H)).length = H.length
  rw [length_zipWith']
  · show ((Mat.ident _).map _).length = _; rw [length_map, length_ident]
  · show ((Mat.ident _).map _).length = (H.map _).length; rw [length_map, length_ident, length_map]

theorem square_charMat (a : Ext p ν) (H : Mat p ν) (hS : Square H) : Square (charMat a H) := fun i hi => by
  rw [length_charMat] at hi ⊢
  rw [row_charMat a H i hi, length_radd _ _ (by rw [length_rsmul, length_unitRow, length_map, hS i hi]), length_rsmul, length_unitRow]

theorem length_charMatP (H : Mat p ν) : (charMatP H).length = H.length := length_range_map _ _

theorem nth_map_neg (r : List (Ext p ν)) (j : Nat) : nth 0 (r.map (- ·)) j = -(nth 0 r j) := by
  have h := nth_map (- ·) (0 : Ext p ν) r j
  rw [show (-0 : Ext p ν) = 0 from Ext.ext Shell.neg_zero Shell.neg_zero] at h
  exact h


/-- The evaluation of `X·I − H` at `a` is `aI − H`. -/
theorem evalM_charMatP (H : Mat p ν) (hS : Square H) (a : Ext p ν) : evalM (charMatP H) a = charMat a H := by
  refine rows_ext _ _ (by rw [length_evalM, length_charMatP, length_charMat]) fun i hi => ?_
  rw [length_evalM, length_charMatP] at hi
  rw [row_evalM, row_charMat a H i hi]
  show ((prow (charMatP H) i).map fun f => eval f a) = _
  have hrow : prow (charMatP H) i = (List.range H.length).map fun j => [-(E H i j), if i = j then (1 : Ext p ν) else 0] :=
    nth_range_map [] _ _ i hi
  rw [hrow, map_map']
  refine ext_nth 0 _ _ (by rw [length_range_map, length_radd _ _ (by rw [length_rsmul, length_unitRow, length_map, hS i hi]), length_rsmul, length_unitRow]) fun j hj => ?_
  rw [length_range_map] at hj
  rw [nth_range_map 0 _ _ j hj, nth_radd _ _ _ (by rw [length_rsmul, length_unitRow, length_map, hS i hi]), nth_rsmul, nth_unitRow _ _ _ hj]
  show -(E H i j) + a * ((if i = j then (1 : Ext p ν) else 0) + a * 0) = a * (if i = j then 1 else 0) + nth 0 ((row H i).map (- ·)) j
  rw [mul_zero, add_zero, add_comm, nth_map_neg]
  rfl

/-- `χ_H(a) = det (aI − H)`. -/
theorem eval_charPoly (H : Mat p ν) (hS : Square H) (a : Ext p ν) : eval (charPoly H) a = det (charMat a H) := by
  show eval (pdet (charMatP H)) a = _; rw [eval_pdet, evalM_charMatP H hS a]

/-! ## The Cayley denominator and the characteristic polynomial -/

theorem row_smul (c : Ext p ν) (M : Mat p ν) (i : Nat) (hi : i < M.length) : row (Mat.smul c M) i = rsmul c (row M i) :=
  nth_map_lt (fun r : List (Ext p ν) => r.map (c * ·)) [] [] M i hi

theorem length_smul (c : Ext p ν) (M : Mat p ν) : (Mat.smul c M).length = M.length := length_map _ M

theorem prodUpto_const (c : Ext p ν) : ∀ n : Nat, prodUpto (fun _ => c) n = c ^ n
  | 0 => rfl
  | n + 1 => by show prodUpto (fun _ => c) n * c = c ^ n * c; rw [prodUpto_const c n]

/-- `det (c · M) = cⁿ · det M`. -/
theorem det_smul (c : Ext p ν) (M : Mat p ν) : det (Mat.smul c M) = c ^ M.length * det M := by
  have e : Mat.smul c M = scaleRows (fun _ => c) M M.length := by
    refine rows_ext _ _ (by rw [length_smul, length_scaleRows]) fun i hi => ?_
    rw [length_smul] at hi
    rw [row_smul c M i hi, row_scaleRows_lt _ _ _ i hi hi]
  rw [e, det_scaleRows _ _ _ (Nat.le_refl _), prodUpto_const]

/-- `I − αH = α (α⁻¹ I − H)` for `α ≠ 0`. -/
theorem cayleyDen_eq_smul {κ : Nat} {g : Shell p} (F : Frame p κ g) (hν : ¬IsSquare ν) {α : Ext p ν} (hα : α ≠ 0) (H : Mat p ν) (hS : Square H) :
    cayleyDen α H = Mat.smul α (charMat (inv α) H) := by
  refine rows_ext _ _ (by rw [length_cayleyDen, length_smul, length_charMat]) fun i hi => ?_
  rw [length_cayleyDen] at hi
  rw [row_cayleyDen α H i hi, row_smul _ _ i (by rw [length_charMat]; exact hi), row_charMat _ H i hi]
  have hl : (unitRow (ν := ν) H.length i).length = (rsmul (-α) (row H i)).length := by rw [length_unitRow, length_rsmul, hS i hi]
  have hl2 : (rsmul (inv α) (unitRow (ν := ν) H.length i)).length = ((row H i).map (- ·)).length := by rw [length_rsmul, length_unitRow, length_map, hS i hi]
  refine ext_nth 0 _ _ (by rw [length_radd _ _ hl, length_unitRow, length_rsmul, length_radd _ _ hl2, length_rsmul, length_unitRow]) fun j _ => ?_
  rw [nth_radd _ _ _ hl, nth_rsmul, nth_rsmul, nth_radd _ _ _ hl2, nth_rsmul, mul_add, ← Ext.mul_assoc, mul_inv F hν hα, Ext.one_mul,
    ← neg_mul, nth_map_neg, ← mul_neg]

/-- `det (I − αH) = αⁿ · χ_H(α⁻¹)` for `α ≠ 0`. -/
theorem det_cayleyDen_charPoly {κ : Nat} {g : Shell p} (F : Frame p κ g) (hν : ¬IsSquare ν) {α : Ext p ν} (hα : α ≠ 0) (H : Mat p ν) (hS : Square H) :
    det (cayleyDen α H) = α ^ H.length * eval (charPoly H) (inv α) := by
  rw [cayleyDen_eq_smul F hν hα H hS, det_smul, length_charMat, eval_charPoly H hS]

theorem pow_ne_zero {κ : Nat} {g : Shell p} (F : Frame p κ g) (hν : ¬IsSquare ν) {α : Ext p ν} (hα : α ≠ 0) : ∀ n : Nat, α ^ n ≠ 0
  | 0 => ext_one_ne_zero F
  | n + 1 => fun h => pow_ne_zero F hν hα n (by
      have : α * α ^ n = 0 := by rw [Ext.mul_comm]; exact h
      exact mul_left_cancel_zero F hν hα this)

/-- 8:C17's step (ii) in polynomial form: a nonzero `α` is excluded exactly when `α⁻¹` is a root of `χ_H`. -/
theorem cayleyDen_singular_iff_charPoly {κ : Nat} {g : Shell p} (F : Frame p κ g) (hν : ¬IsSquare ν) {α : Ext p ν} (hα : α ≠ 0)
    (H : Mat p ν) (hS : Square H) : det (cayleyDen α H) = 0 ↔ eval (charPoly H) (inv α) = 0 := by
  rw [det_cayleyDen_charPoly F hν hα H hS]
  exact ⟨fun h => mul_left_cancel_zero F hν (pow_ne_zero F hν hα _) h, fun h => by rw [h, mul_zero]⟩


/-! ## The degree and the leading coefficient -/

/-- The entry `(i, j)` of a polynomial matrix (`[]`, the zero polynomial, beyond the rows and the columns). -/
def pentry (M : PMat p ν) (i j : Nat) : Poly p ν := nth [] (prow M i) j

theorem pentry_pminor (M : PMat p ν) (i i' j : Nat) :
    pentry (pminor M i) i' j = pentry M (if i' < i then i' else i' + 1) (j + 1) := by
  show nth [] (nth [] ((removeAt M i).map List.tail) i') j = nth [] (nth [] M _) (j + 1)
  have hm : nth [] ((removeAt M i).map List.tail) i' = (nth [] (removeAt M i) i').tail := nth_map List.tail [] (removeAt M i) i'
  rw [hm]
  have tail_nth : ∀ (r : List (Poly p ν)) (j : Nat), nth [] r.tail j = nth [] r (j + 1) := fun r j =>
    match r with | [] => rfl | _ :: _ => rfl
  rw [tail_nth]
  match Nat.decLt i' i with
  | .isTrue h => rw [ite_eq_left h, nth_removeAt_lt [] M i i' h]
  | .isFalse h => rw [ite_eq_right h, nth_removeAt_ge [] M i i' (Nat.le_of_not_lt h)]

/-- Every entry has degree at most one. -/
def DegLE1 (M : PMat p ν) : Prop := ∀ i j, DegLE (pentry M i j) 1

theorem degLE1_pminor (M : PMat p ν) (hM : DegLE1 M) (i : Nat) : DegLE1 (pminor M i) := fun i' j => by
  rw [pentry_pminor]; exact hM _ _

theorem degLE_psgn : ∀ i : Nat, DegLE (psgn (p := p) (ν := ν) i) 0
  | 0 => fun k hk => match k, hk with | _ + 1, _ => rfl
  | i + 1 => degLE_pneg _ _ (degLE_psgn i)

theorem degLE_psumFrom (f : Nat → Poly p ν) (d : Nat) : ∀ k i, (∀ j, DegLE (f j) d) → DegLE (psumFrom f k i) d
  | 0, _, _ => fun _ _ => rfl
  | k + 1, i, h => degLE_padd _ _ _ (h i) (degLE_psumFrom f d k (i + 1) h)

theorem degLE_nil (d : Nat) : DegLE ([] : Poly p ν) d := fun _ _ => rfl

/-- The expansion of a matrix with entries of degree at most one has degree at most the row count. -/
theorem degLE_pdetF : ∀ (n : Nat) (M : PMat p ν), DegLE1 M → DegLE (pdetF n M) n
  | 0, _, _ => fun k hk => match k, hk with | _ + 1, _ => rfl
  | _ + 1, [], _ => fun k hk => match k, hk with | _ + 1, _ => rfl
  | n + 1, r :: rest, hM => by
    show DegLE (psumFrom (pterm (pdetF n) (r :: rest)) (r :: rest).length 0) (n + 1)
    refine degLE_psumFrom _ _ _ _ fun i => ?_
    show DegLE (pmul (pmul (psgn i) (phead (prow (r :: rest) i))) (pdetF n (pminor (r :: rest) i))) (n + 1)
    have h1 : DegLE (pmul (psgn i) (phead (prow (r :: rest) i))) 1 := degLE_pmul _ _ 0 1 (degLE_psgn i) (hM i 0)
    have h2 := degLE_pdetF n (pminor (r :: rest) i) (degLE1_pminor _ hM i)
    rw [Nat.add_comm]; exact degLE_pmul _ _ 1 n h1 h2

theorem coeff_psumFrom (f : Nat → Poly p ν) (c : Nat) : ∀ k i, coeff (psumFrom f k i) c = sumFrom (fun j => coeff (f j) c) k i
  | 0, _ => rfl
  | k + 1, i => by
    show coeff (padd (f i) (psumFrom f k (i + 1))) c = coeff (f i) c + sumFrom (fun j => coeff (f j) c) k (i + 1)
    rw [coeff_padd, coeff_psumFrom f c k (i + 1)]

theorem sumFrom_eq_zero (f : Nat → Ext p ν) : ∀ k i, (∀ j, i ≤ j → j < i + k → f j = 0) → sumFrom f k i = 0
  | 0, _, _ => rfl
  | k + 1, i, h => by
    show f i + sumFrom f k (i + 1) = 0
    rw [h i (Nat.le_refl i) (Nat.lt_add_of_pos_right (Nat.succ_pos k)), zero_add]
    exact sumFrom_eq_zero f k (i + 1) fun j hj hj' => h j (Nat.le_of_succ_le hj) (Nat.add_right_comm i 1 k ▸ hj')

/-- `X·I − H` and its first minors: the entries have degree at most one, and the coefficient of `X` is the Kronecker delta. -/
def XDiag (n : Nat) (M : PMat p ν) : Prop :=
  M.length = n ∧ DegLE1 M ∧ ∀ i j, i < n → j < n → coeff (pentry M i j) 1 = if i = j then 1 else 0

theorem xdiag_pminor_zero (n : Nat) (M : PMat p ν) (h : XDiag (n + 1) M) : XDiag n (pminor M 0) := by
  obtain ⟨hl, h1, hd⟩ := h
  refine ⟨?_, degLE1_pminor M h1 0, fun i j hi hj => ?_⟩
  · show ((removeAt M 0).map List.tail).length = n
    rw [length_map]; exact Nat.succ.inj ((length_removeAt M 0 (hl ▸ Nat.succ_pos n)).trans hl)
  · rw [pentry_pminor, ite_eq_right (Nat.not_lt_zero i), hd (i + 1) (j + 1) (Nat.succ_lt_succ hi) (Nat.succ_lt_succ hj)]
    exact ite_succ' i j
where
  ite_succ' (i j : Nat) : (if i + 1 = j + 1 then (1 : Ext p ν) else 0) = if i = j then 1 else 0 :=
    match Nat.decEq i j with
    | isTrue h => by rw [h, ite_eq_left rfl, ite_eq_left rfl]
    | isFalse h => by rw [ite_eq_right h, ite_eq_right (fun e => h (Nat.succ.inj e))]

theorem degLE_zero_of_coeff_one (f : Poly p ν) (h1 : DegLE f 1) (h0 : coeff f 1 = 0) : DegLE f 0 := fun k hk =>
  match k, hk with
  | 1, _ => h0
  | k + 2, _ => h1 (k + 2) (Nat.succ_lt_succ (Nat.succ_pos k))

/-- The leading coefficient of the expansion of an `X`-diagonal matrix is `1`. -/
theorem coeff_pdetF_top : ∀ (n : Nat) (M : PMat p ν), XDiag n M → coeff (pdetF n M) n = 1
  | 0, _, _ => rfl
  | n + 1, [], ⟨hl, _, _⟩ => absurd hl (Nat.ne_of_lt (Nat.succ_pos n))
  | n + 1, r :: rest, h => by
    obtain ⟨hl, h1, hd⟩ := h
    show coeff (psumFrom (pterm (pdetF n) (r :: rest)) (r :: rest).length 0) (n + 1) = 1
    rw [coeff_psumFrom, hl]
    show coeff (pterm (pdetF n) (r :: rest) 0) (n + 1) + sumFrom (fun j => coeff (pterm (pdetF n) (r :: rest) j) (n + 1)) n 1 = 1
    -- the first term: `(X − H[0][0]) · pdet (minor)`, monic of degree `n + 1`
    have hminor := coeff_pdetF_top n (pminor (r :: rest) 0) (xdiag_pminor_zero n _ ⟨hl, h1, hd⟩)
    have hminorD := degLE_pdetF n (pminor (r :: rest) 0) (degLE1_pminor _ h1 0)
    have hhead : DegLE (phead (prow (r :: rest) 0)) 1 := h1 0 0
    have hhead1 : coeff (phead (prow (r :: rest) 0)) 1 = 1 := by
      have := hd 0 0 (Nat.succ_pos n) (Nat.succ_pos n); rw [ite_eq_left rfl] at this; exact this
    have hsgn : coeff (psgn (p := p) (ν := ν) 0) 0 = 1 := rfl
    have hfirst : coeff (pterm (pdetF n) (r :: rest) 0) (n + 1) = 1 := by
      show coeff (pmul (pmul (psgn 0) (phead (prow (r :: rest) 0))) (pdetF n (pminor (r :: rest) 0))) (n + 1) = 1
      have hA : DegLE (pmul (psgn 0) (phead (prow (r :: rest) 0))) 1 := degLE_pmul _ _ 0 1 (degLE_psgn 0) hhead
      have hA1 : coeff (pmul (psgn 0) (phead (prow (r :: rest) 0))) 1 = 1 := by
        have := coeff_pmul_top (psgn 0) (phead (prow (r :: rest) 0)) 0 1 (degLE_psgn 0) hhead
        rw [Nat.zero_add] at this; rw [this, hsgn, hhead1, Ext.one_mul]
      rw [Nat.add_comm, coeff_pmul_top _ _ 1 n hA hminorD, hA1, hminor, Ext.one_mul]
    -- the other terms have degree at most `n`
    have hrest : ∀ i, 1 ≤ i → i < 1 + n → coeff (pterm (pdetF n) (r :: rest) i) (n + 1) = 0 := fun i hi hin => by
      show coeff (pmul (pmul (psgn i) (phead (prow (r :: rest) i))) (pdetF n (pminor (r :: rest) i))) (n + 1) = 0
      have hi0 : coeff (pentry (r :: rest) i 0) 1 = 0 := by
        have := hd i 0 (Nat.add_comm 1 n ▸ hin) (Nat.succ_pos n); rw [ite_eq_right (Nat.ne_of_gt hi)] at this; exact this
      have hA : DegLE (pmul (psgn i) (phead (prow (r :: rest) i))) 0 :=
        degLE_pmul _ _ 0 0 (degLE_psgn i) (degLE_zero_of_coeff_one _ (h1 i 0) hi0)
      have hB := degLE_pdetF n (pminor (r :: rest) i) (degLE1_pminor _ h1 i)
      have := degLE_pmul _ _ 0 n hA hB
      rw [Nat.zero_add] at this
      exact this (n + 1) (Nat.lt_succ_self n)
    rw [hfirst, sumFrom_eq_zero _ n 1 hrest, add_zero]

theorem xdiag_charMatP (H : Mat p ν) : XDiag H.length (charMatP H) := by
  refine ⟨length_charMatP H, fun i j => ?_, fun i j hi hj => ?_⟩
  · match Nat.decLt i H.length with
    | .isFalse hi =>
      show DegLE (nth [] (nth [] (charMatP H) i) j) 1
      rw [nth_beyond [] _ i (by rw [length_charMatP]; exact Nat.le_of_not_lt hi)]; exact degLE_nil 1
    | .isTrue hi =>
      show DegLE (nth [] (prow (charMatP H) i) j) 1
      rw [show prow (charMatP H) i = (List.range H.length).map fun j => [-(E H i j), if i = j then (1 : Ext p ν) else 0] from
        nth_range_map [] _ _ i hi]
      match Nat.decLt j H.length with
      | .isTrue hj => rw [nth_range_map [] _ _ j hj]; exact degLE_of_length _ 1 (Nat.le_refl 2)
      | .isFalse hj => rw [nth_beyond [] _ j (by rw [length_range_map]; exact Nat.le_of_not_lt hj)]; exact degLE_nil 1
  · show coeff (nth [] (prow (charMatP H) i) j) 1 = _
    rw [show prow (charMatP H) i = (List.range H.length).map fun j => [-(E H i j), if i = j then (1 : Ext p ν) else 0] from
      nth_range_map [] _ _ i hi, nth_range_map [] _ _ j hj]
    rfl

/-- `χ_H` has degree at most `n`. -/
theorem degLE_charPoly (H : Mat p ν) : DegLE (charPoly H) H.length := by
  show DegLE (pdetF (charMatP H).length (charMatP H)) H.length
  rw [length_charMatP]; exact degLE_pdetF _ _ (xdiag_charMatP H).2.1

/-- `χ_H` is monic: its coefficient of `Xⁿ` is `1`. -/
theorem coeff_charPoly_top (H : Mat p ν) : coeff (charPoly H) H.length = 1 := by
  show coeff (pdetF (charMatP H).length (charMatP H)) H.length = 1
  rw [length_charMatP]; exact coeff_pdetF_top _ _ (xdiag_charMatP H)

end FRC.Dirac.Det
