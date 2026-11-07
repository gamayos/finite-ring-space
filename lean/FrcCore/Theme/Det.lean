import FrcCore.Theme.Hermitian
/-!
# FrcCore.Theme.Det — the determinant over the coefficient field (the operator theme)

The determinant of a square matrix over `K = 𝔽_p(√ν)` (the list matrices `Mat p ν` of `Theme/Dirac`), by Laplace
expansion along the first column: `det (r₀ :: …) = Σ_i (−1)^i · (row i)₀ · det (minor i)`, the minor the rows other
than `i` without their heads. The expansion along the first column makes the row lemmas inductions on the matrix:
linearity in each row, the sign change under an adjacent swap, the vanishing on two equal rows, the invariance under
adding a multiple of one row to another. `Theme/Elim.lean` continues with Gaussian elimination, which computes the
determinant with `n³` operations and is proved equal to `det`. Written for 8:T1 (the admissible set of Cayley
parameters, 7 November 2026). No axioms.
-/
namespace FRC.Dirac.Det

open FRC FRC.Extension FRC.Dirac FRC.Dirac.Hermitian
open FRC.Dirac.Mat (nth)

variable {p : Nat} [Pos p] {ν : Shell p}

/-! ## Lists: rows, removal, length -/

/-- The row `i` of a matrix (the empty row beyond the end) and the head of a row (`0` for the empty row). -/
def row (M : Mat p ν) (i : Nat) : List (Ext p ν) := nth [] M i
def head (r : List (Ext p ν)) : Ext p ν := nth 0 r 0

/-- The list without its `i`-th entry. -/
def removeAt {α : Type} : List α → Nat → List α
  | [], _ => []
  | _ :: l, 0 => l
  | a :: l, i + 1 => a :: removeAt l i

/-- The list with its `i`-th entry replaced. -/
def setAt {α : Type} : List α → Nat → α → List α
  | [], _, _ => []
  | _ :: l, 0, x => x :: l
  | a :: l, i + 1, x => a :: setAt l i x

theorem length_map {α β : Type} (f : α → β) : ∀ l : List α, (l.map f).length = l.length
  | [] => rfl
  | _ :: l => congrArg (· + 1) (length_map f l)

theorem eq_zero_of_lt_one {n : Nat} (h : n < 1) : n = 0 := Nat.le_antisymm (Nat.le_of_lt_succ h) (Nat.zero_le _)
theorem sub_pos_of_lt' {m n : Nat} (h : m < n) : 0 < n - m := FRC.Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact h)

theorem length_removeAt {α : Type} : ∀ (l : List α) (i : Nat), i < l.length → (removeAt l i).length + 1 = l.length
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _ => rfl
  | _ :: l, i + 1, h => congrArg (· + 1) (length_removeAt l i (Nat.lt_of_succ_lt_succ h))

theorem length_setAt {α : Type} : ∀ (l : List α) (i : Nat) (x : α), (setAt l i x).length = l.length
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | _ :: l, i + 1, x => congrArg (· + 1) (length_setAt l i x)

theorem nth_setAt_eq {α : Type} (d : α) : ∀ (l : List α) (i : Nat) (x : α), i < l.length → nth d (setAt l i x) i = x
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _, _ => rfl
  | _ :: l, i + 1, x, h => nth_setAt_eq d l i x (Nat.lt_of_succ_lt_succ h)

theorem nth_setAt_ne {α : Type} (d : α) : ∀ (l : List α) (i j : Nat) (x : α), i ≠ j → nth d (setAt l i x) j = nth d l j
  | [], _, _, _, _ => rfl
  | _ :: _, 0, 0, _, h => absurd rfl h
  | _ :: _, 0, _ + 1, _, _ => rfl
  | _ :: _, _ + 1, 0, _, _ => rfl
  | _ :: l, i + 1, j + 1, x, h => nth_setAt_ne d l i j x (fun e => h (congrArg (· + 1) e))

/-- Removing entry `j` of `setAt l i x`: the entry `i` survives at `i` (`j > i`) or at `i − 1` (`j < i`). -/
theorem removeAt_setAt_gt {α : Type} : ∀ (l : List α) (i j : Nat) (x : α), i < j →
    removeAt (setAt l i x) j = setAt (removeAt l j) i x
  | [], _, _, _, _ => rfl
  | _ :: _, 0, 0, _, h => absurd h (Nat.lt_irrefl 0)
  | _ :: _, 0, _ + 1, _, _ => rfl
  | _ :: _, _ + 1, 0, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: l, i + 1, j + 1, x, h => congrArg (_ :: ·) (removeAt_setAt_gt l i j x (Nat.lt_of_succ_lt_succ h))

theorem removeAt_setAt_lt {α : Type} : ∀ (l : List α) (i j : Nat) (x : α), j < i →
    removeAt (setAt l i x) j = setAt (removeAt l j) (i - 1) x
  | [], _, _, _, _ => rfl
  | _ :: _, 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, _ + 1, 0, _, _ => rfl
  | a :: l, i + 1, j + 1, x, h =>
    match i, Nat.lt_of_succ_lt_succ h with
    | 0, h' => absurd h' (Nat.not_lt_zero _)
    | i' + 1, h' => congrArg (a :: ·) (removeAt_setAt_lt l (i' + 1) j x h')

theorem removeAt_setAt_eq {α : Type} : ∀ (l : List α) (i : Nat) (x : α), removeAt (setAt l i x) i = removeAt l i
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | _ :: l, i + 1, x => congrArg (_ :: ·) (removeAt_setAt_eq l i x)

theorem map_removeAt {α β : Type} (f : α → β) : ∀ (l : List α) (i : Nat), (removeAt l i).map f = removeAt (l.map f) i
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => congrArg (_ :: ·) (map_removeAt f l i)

theorem map_setAt {α β : Type} (f : α → β) : ∀ (l : List α) (i : Nat) (x : α), (setAt l i x).map f = setAt (l.map f) i (f x)
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | _ :: l, i + 1, x => congrArg (_ :: ·) (map_setAt f l i x)

theorem nth_map {α β : Type} (f : α → β) (d : α) : ∀ (l : List α) (i : Nat), nth (f d) (l.map f) i = f (nth d l i)
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => nth_map f d l i

-- appending, mapping and zipping (the core's `List.length_append`, `List.append_assoc`, `List.map_append`,
-- `List.length_zipWith` carry `propext`)
-- lists (the core's `List.length_append`, `List.append_assoc`, `List.map_append` carry `propext`)
theorem length_append' {α : Type} : ∀ (l m : List α), (l ++ m).length = l.length + m.length
  | [], m => (Nat.zero_add _).symm
  | _ :: l, m => by
    show (l ++ m).length + 1 = l.length + 1 + m.length
    rw [length_append' l m, Nat.add_right_comm]

theorem append_assoc' {α : Type} : ∀ (l m k : List α), l ++ m ++ k = l ++ (m ++ k)
  | [], _, _ => rfl
  | _ :: l, m, k => congrArg (_ :: ·) (append_assoc' l m k)

theorem map_append' {α β : Type} (f : α → β) : ∀ (l m : List α), (l ++ m).map f = l.map f ++ m.map f
  | [], _ => rfl
  | _ :: l, m => congrArg (_ :: ·) (map_append' f l m)

theorem map_append_single {α β : Type} (f : α → β) (l : List α) (a : α) : (l ++ [a]).map f = l.map f ++ [f a] := map_append' f l [a]

theorem nth_map_lt {α β : Type} (f : α → β) (d : α) (e : β) : ∀ (l : List α) (i : Nat), i < l.length → nth e (l.map f) i = f (nth d l i)
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _ => rfl
  | _ :: l, i + 1, h => nth_map_lt f d e l i (Nat.lt_of_succ_lt_succ h)

theorem nth_append_lt {α : Type} (d : α) : ∀ (l m : List α) (i : Nat), i < l.length → nth d (l ++ m) i = nth d l i
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, _, 0, _ => rfl
  | _ :: l, m, i + 1, h => nth_append_lt d l m i (Nat.lt_of_succ_lt_succ h)

theorem nth_append_len {α : Type} (d : α) : ∀ (l : List α) (a : α), nth d (l ++ [a]) l.length = a
  | [], _ => rfl
  | _ :: l, a => nth_append_len d l a

theorem length_zipWith' {α β γ : Type} (f : α → β → γ) : ∀ (l : List α) (m : List β), l.length = m.length →
    (List.zipWith f l m).length = l.length
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h (Nat.ne_of_lt (Nat.succ_pos _))
  | _ :: _, [], h => absurd h (Nat.ne_of_gt (Nat.succ_pos _))
  | _ :: l, _ :: m, h => congrArg (· + 1) (length_zipWith' f l m (Nat.succ.inj h))

theorem nth_zipWith {α β γ : Type} (f : α → β → γ) (d : α) (e : β) (c : γ) : ∀ (l : List α) (m : List β) (i : Nat),
    i < l.length → i < m.length → nth c (List.zipWith f l m) i = f (nth d l i) (nth e m i)
  | [], _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | _ :: _, [], _, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, _ :: _, 0, _, _ => rfl
  | _ :: l, _ :: m, i + 1, h, h' => nth_zipWith f d e c l m i (Nat.lt_of_succ_lt_succ h) (Nat.lt_of_succ_lt_succ h')

theorem ext_nth {α : Type} (d : α) : ∀ (l m : List α), l.length = m.length → (∀ i, i < l.length → nth d l i = nth d m i) → l = m
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => absurd h (Nat.ne_of_lt (Nat.succ_pos _))
  | _ :: _, [], h, _ => absurd h (Nat.ne_of_gt (Nat.succ_pos _))
  | a :: l, b :: m, h, e => by
    have hab : a = b := e 0 (Nat.succ_pos _)
    rw [hab, ext_nth d l m (Nat.succ.inj h) (fun i hi => e (i + 1) (Nat.succ_lt_succ hi))]

theorem map_map' {α β γ : Type} (f : α → β) (g : β → γ) : ∀ l : List α, (l.map f).map g = l.map (fun x => g (f x))
  | [] => rfl
  | _ :: l => congrArg (_ :: ·) (map_map' f g l)

theorem map_congr' {α β : Type} {f g : α → β} (h : ∀ x, f x = g x) : ∀ l : List α, l.map f = l.map g
  | [] => rfl
  | x :: l => by show f x :: _ = g x :: _; rw [h x, map_congr' h l]

/-! ## The sign and the sums -/

/-- `(−1)^i` in `K`. -/
def sgn : Nat → Ext p ν
  | 0 => 1
  | i + 1 => -(sgn i)

theorem sgn_succ (i : Nat) : (sgn (i + 1) : Ext p ν) = -(sgn i) := rfl
theorem sgn_add_two (i : Nat) : (sgn (i + 2) : Ext p ν) = sgn i := Hermitian.neg_neg _
theorem sgn_add (i : Nat) : ∀ j : Nat, (sgn (i + j) : Ext p ν) = sgn i * sgn j
  | 0 => (Ext.mul_one _).symm
  | j + 1 => by
    show -(sgn (i + j)) = sgn i * -(sgn j)
    rw [sgn_add i j, Hermitian.mul_neg]
theorem sgn_mul_sgn (i : Nat) : (sgn i : Ext p ν) * sgn i = 1 := by
  induction i with
  | zero => exact Ext.one_mul (1 : Ext p ν)
  | succ i ih => show -(sgn i) * -(sgn i) = 1; rw [← Hermitian.neg_mul, ← Hermitian.mul_neg, Hermitian.neg_neg, ih]

/-- `Σ_{j = i}^{i + k − 1} f j`. -/
def sumFrom (f : Nat → Ext p ν) : Nat → Nat → Ext p ν
  | 0, _ => 0
  | k + 1, i => f i + sumFrom f k (i + 1)

theorem sumFrom_congr {f g : Nat → Ext p ν} : ∀ (k i : Nat), (∀ j, i ≤ j → j < i + k → f j = g j) →
    sumFrom f k i = sumFrom g k i
  | 0, _, _ => rfl
  | k + 1, i, h => by
    show f i + sumFrom f k (i + 1) = g i + sumFrom g k (i + 1)
    rw [h i (Nat.le_refl i) (Nat.lt_add_of_pos_right (Nat.succ_pos k)),
      sumFrom_congr k (i + 1) fun j hj hj' => h j (Nat.le_of_succ_le hj) (Nat.add_right_comm i 1 k ▸ hj')]

theorem sumFrom_add (f g : Nat → Ext p ν) : ∀ (k i : Nat), sumFrom (fun j => f j + g j) k i = sumFrom f k i + sumFrom g k i
  | 0, _ => (add_zero _).symm
  | k + 1, i => by
    show f i + g i + sumFrom (fun j => f j + g j) k (i + 1) = f i + sumFrom f k (i + 1) + (g i + sumFrom g k (i + 1))
    rw [sumFrom_add f g k, add_add_add_comm]

theorem sumFrom_smul (c : Ext p ν) (f : Nat → Ext p ν) : ∀ (k i : Nat), sumFrom (fun j => c * f j) k i = c * sumFrom f k i
  | 0, _ => (mul_zero c).symm
  | k + 1, i => by
    show c * f i + sumFrom (fun j => c * f j) k (i + 1) = c * (f i + sumFrom f k (i + 1))
    rw [sumFrom_smul c f k, mul_add]

theorem sumFrom_neg (f : Nat → Ext p ν) : ∀ (k i : Nat), sumFrom (fun j => -(f j)) k i = -(sumFrom f k i)
  | 0, _ => Ext.ext Shell.neg_zero.symm Shell.neg_zero.symm
  | k + 1, i => by
    show -(f i) + sumFrom (fun j => -(f j)) k (i + 1) = -(f i + sumFrom f k (i + 1))
    rw [sumFrom_neg f k, neg_add_rev]

theorem sumFrom_zero_fn : ∀ (k i : Nat), sumFrom (fun _ => (0 : Ext p ν)) k i = 0
  | 0, _ => rfl
  | k + 1, i => by show 0 + sumFrom (fun _ => (0 : Ext p ν)) k (i + 1) = 0; rw [sumFrom_zero_fn k, add_zero]

/-- Splitting a sum after its first `m` terms. -/
theorem sumFrom_split (f : Nat → Ext p ν) : ∀ (m k i : Nat), sumFrom f m i + sumFrom f k (i + m) = sumFrom f (m + k) i
  | 0, k, i => by rw [Nat.zero_add]; exact Hermitian.zero_add _
  | m + 1, k, i => by
    rw [Nat.succ_add]
    show f i + sumFrom f m (i + 1) + sumFrom f k (i + (m + 1)) = f i + sumFrom f (m + k) (i + 1)
    rw [← sumFrom_split f m k (i + 1), Hermitian.add_assoc, Nat.add_right_comm]; rfl

/-! ## The determinant by expansion along the first column -/

/-- The minor at row `i`: the rows other than `i`, each without its head. -/
def minor (M : Mat p ν) (i : Nat) : Mat p ν := (removeAt M i).map List.tail

/-- The term of row `i` in the expansion along the first column, `d` standing for the determinant of the minors. -/
def term (d : Mat p ν → Ext p ν) (M : Mat p ν) (i : Nat) : Ext p ν := sgn i * head (row M i) * d (minor M i)

/-- The expansion with the number of rows as fuel. -/
def detF : Nat → Mat p ν → Ext p ν
  | 0, _ => 1
  | _ + 1, [] => 1
  | n + 1, M@(_ :: _) => sumFrom (term (detF n) M) M.length 0

/-- The determinant of a square matrix (`1` for the empty matrix). -/
def det (M : Mat p ν) : Ext p ν := detF M.length M

theorem length_minor (M : Mat p ν) (i : Nat) (h : i < M.length) : (minor M i).length + 1 = M.length := by
  unfold minor; rw [length_map]; exact length_removeAt M i h

theorem length_minor_le {M : Mat p ν} {i n : Nat} (hM : M.length ≤ n + 1) (h : i < M.length) : (minor M i).length ≤ n :=
  Nat.le_of_succ_le_succ (show (minor M i).length + 1 ≤ n + 1 by rw [length_minor M i h]; exact hM)

/-- The fuel does not matter once it covers the rows. -/
theorem detF_fuel_eq : ∀ (n m : Nat) (M : Mat p ν), M.length ≤ n → M.length ≤ m → detF n M = detF m M
  | 0, 0, _, _, _ => rfl
  | 0, _ + 1, [], _, _ => rfl
  | 0, _ + 1, _ :: _, h, _ => absurd h (Nat.not_succ_le_zero _)
  | _ + 1, 0, [], _, _ => rfl
  | _ + 1, 0, _ :: _, _, h => absurd h (Nat.not_succ_le_zero _)
  | _ + 1, _ + 1, [], _, _ => rfl
  | n + 1, m + 1, r :: rest, h, h' =>
    sumFrom_congr _ _ fun j _ hj => by
      have hj' : j < (r :: rest).length := Nat.lt_of_lt_of_eq hj (Nat.zero_add _)
      unfold term
      rw [detF_fuel_eq n m (minor (r :: rest) j) (length_minor_le h hj') (length_minor_le h' hj')]

theorem detF_fuel (n : Nat) (M : Mat p ν) (h : M.length ≤ n) : detF n M = det M :=
  detF_fuel_eq n M.length M h (Nat.le_refl _)

/-- The expansion along the first column. -/
theorem det_expand (M : Mat p ν) (h : 0 < M.length) : det M = sumFrom (term det M) M.length 0 := by
  match M, h with
  | r :: rest, _ =>
    show sumFrom (term (detF rest.length) (r :: rest)) (rest.length + 1) 0 = _
    exact sumFrom_congr _ _ fun j _ hj => by
      unfold term
      rw [detF_fuel rest.length (minor (r :: rest) j) (length_minor_le (Nat.le_refl _) (Nat.lt_of_lt_of_eq hj (Nat.zero_add _)))]

theorem det_nil : det ([] : Mat p ν) = 1 := rfl

theorem det_single (a : Ext p ν) : det [[a]] = a := by
  show 1 * a * 1 + 0 = a
  rw [Ext.one_mul, Ext.mul_one, add_zero]

/-! ## Rows: replacement, addition, scaling -/

/-- The sum and the scaling of rows. -/
def radd : List (Ext p ν) → List (Ext p ν) → List (Ext p ν)
  | [], _ => []
  | _ :: _, [] => []
  | a :: r, b :: s => (a + b) :: radd r s
def rsmul (c : Ext p ν) (r : List (Ext p ν)) : List (Ext p ν) := r.map (c * ·)

theorem head_radd : ∀ (r s : List (Ext p ν)), r.length = s.length → head (radd r s) = head r + head s
  | [], [], _ => (add_zero _).symm
  | [], _ :: _, h => absurd h (Nat.ne_of_lt (Nat.succ_pos _))
  | _ :: _, [], h => absurd h (Nat.ne_of_gt (Nat.succ_pos _))
  | _ :: _, _ :: _, _ => rfl

theorem tail_radd : ∀ (r s : List (Ext p ν)), (radd r s).tail = radd r.tail s.tail
  | [], _ => rfl
  | _ :: [], [] => rfl
  | _ :: _ :: _, [] => rfl
  | _ :: _, _ :: _ => rfl

theorem length_radd : ∀ (r s : List (Ext p ν)), r.length = s.length → (radd r s).length = r.length
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h (Nat.ne_of_lt (Nat.succ_pos _))
  | _ :: _, [], h => absurd h (Nat.ne_of_gt (Nat.succ_pos _))
  | _ :: r, _ :: s, h => congrArg (· + 1) (length_radd r s (Nat.succ.inj h))

theorem length_tail {α : Type} : ∀ (l : List α), l.tail.length + 1 = l.length ∨ l = []
  | [] => Or.inr rfl
  | _ :: _ => Or.inl rfl

theorem head_rsmul (c : Ext p ν) : ∀ r : List (Ext p ν), head (rsmul c r) = c * head r
  | [] => (mul_zero c).symm
  | _ :: _ => rfl

theorem tail_rsmul (c : Ext p ν) : ∀ r : List (Ext p ν), (rsmul c r).tail = rsmul c r.tail
  | [] => rfl
  | _ :: _ => rfl

theorem row_setAt_eq (M : Mat p ν) (i : Nat) (r : List (Ext p ν)) (h : i < M.length) : row (setAt M i r) i = r :=
  nth_setAt_eq [] M i r h
theorem row_setAt_ne (M : Mat p ν) (i j : Nat) (r : List (Ext p ν)) (h : i ≠ j) : row (setAt M i r) j = row M j :=
  nth_setAt_ne [] M i j r h

theorem minor_setAt_gt (M : Mat p ν) (i j : Nat) (r : List (Ext p ν)) (h : i < j) :
    minor (setAt M i r) j = setAt (minor M j) i r.tail := by
  unfold minor; rw [removeAt_setAt_gt M i j r h, map_setAt]
theorem minor_setAt_lt (M : Mat p ν) (i j : Nat) (r : List (Ext p ν)) (h : j < i) :
    minor (setAt M i r) j = setAt (minor M j) (i - 1) r.tail := by
  unfold minor; rw [removeAt_setAt_lt M i j r h, map_setAt]
theorem minor_setAt_eq (M : Mat p ν) (i : Nat) (r : List (Ext p ν)) : minor (setAt M i r) i = minor M i := by
  unfold minor; rw [removeAt_setAt_eq]

/-- The index of row `i` inside the minor at row `j`. -/
def shift (i j : Nat) : Nat := if j < i then i - 1 else i

theorem minor_setAt (M : Mat p ν) (i j : Nat) (r : List (Ext p ν)) (h : i ≠ j) :
    minor (setAt M i r) j = setAt (minor M j) (shift i j) r.tail := by
  unfold shift
  match Nat.decLt j i with
  | .isTrue hji => rw [ite_eq_left hji]; exact minor_setAt_lt M i j r hji
  | .isFalse hji =>
    rw [ite_eq_right hji]
    exact minor_setAt_gt M i j r (Nat.lt_of_le_of_ne (Nat.le_of_not_lt hji) h)

theorem shift_lt {i j n : Nat} (hi : i < n + 1) (hj : j < n + 1) (h : i ≠ j) : shift i j < n := by
  unfold shift
  match Nat.decLt j i with
  | .isTrue hji =>
    rw [ite_eq_left hji]
    exact Nat.lt_of_lt_of_le (Nat.sub_lt (Nat.lt_of_le_of_lt (Nat.zero_le j) hji) Nat.one_pos) (Nat.le_of_lt_succ hi)
  | .isFalse hji =>
    rw [ite_eq_right hji]
    exact Nat.lt_of_lt_of_le (Nat.lt_of_le_of_ne (Nat.le_of_not_lt hji) h) (Nat.le_of_lt_succ hj)

/-- Linearity in a row: the sum. -/
theorem det_setAt_add : ∀ (n : Nat) (M : Mat p ν) (i : Nat) (r s : List (Ext p ν)), M.length = n + 1 → i < n + 1 →
    r.length = s.length → det (setAt M i (radd r s)) = det (setAt M i r) + det (setAt M i s)
  | n, M, i, r, s, hM, hi, hl => by
    have hlen : ∀ t, (setAt M i t).length = n + 1 := fun t => (length_setAt M i t).trans hM
    rw [det_expand _ (hlen _ ▸ Nat.succ_pos n), det_expand _ (hlen _ ▸ Nat.succ_pos n),
      det_expand _ (hlen _ ▸ Nat.succ_pos n), hlen, hlen, hlen, ← sumFrom_add]
    exact sumFrom_congr _ _ fun j _ hj => by
      have hj' : j < n + 1 := Nat.lt_of_lt_of_eq hj (Nat.zero_add _)
      unfold term
      match Nat.decEq i j with
      | .isTrue e =>
        subst e
        rw [row_setAt_eq _ _ _ (hM ▸ hi), row_setAt_eq _ _ _ (hM ▸ hi), row_setAt_eq _ _ _ (hM ▸ hi),
          minor_setAt_eq, minor_setAt_eq, minor_setAt_eq, head_radd r s hl, mul_add, add_mul]
      | .isFalse e =>
        rw [row_setAt_ne _ _ _ _ e, row_setAt_ne _ _ _ _ e, row_setAt_ne _ _ _ _ e,
          minor_setAt _ _ _ _ e, minor_setAt _ _ _ _ e, minor_setAt _ _ _ _ e, tail_radd]
        match n with
        | 0 => exact absurd (eq_zero_of_lt_one hi ▸ eq_zero_of_lt_one hj' ▸ e) (fun h => h rfl)
        | n + 1 =>
          have hjM : j < M.length := by rw [hM]; exact hj'
          rw [det_setAt_add n (minor M j) (shift i j) r.tail s.tail
            (Nat.succ.inj (show (minor M j).length + 1 = n + 1 + 1 by rw [length_minor M j hjM]; exact hM))
            (shift_lt hi hj' e) ?_, mul_add]
          match r, s, hl with
          | [], [], _ => rfl
          | _ :: _, _ :: _, h => exact Nat.succ.inj h

theorem mul_left_comm (a b c : Ext p ν) : a * (b * c) = b * (a * c) := by
  rw [← Ext.mul_assoc, Ext.mul_comm a b, Ext.mul_assoc]
theorem add_left_comm (a b c : Ext p ν) : a + (b + c) = b + (a + c) := by
  rw [← Hermitian.add_assoc, Hermitian.add_comm a b, Hermitian.add_assoc]

/-- Linearity in a row: the scaling. -/
theorem det_setAt_smul : ∀ (n : Nat) (M : Mat p ν) (i : Nat) (c : Ext p ν) (r : List (Ext p ν)), M.length = n + 1 →
    i < n + 1 → det (setAt M i (rsmul c r)) = c * det (setAt M i r)
  | n, M, i, c, r, hM, hi => by
    have hlen : ∀ t, (setAt M i t).length = n + 1 := fun t => (length_setAt M i t).trans hM
    rw [det_expand _ (hlen _ ▸ Nat.succ_pos n), det_expand _ (hlen _ ▸ Nat.succ_pos n), hlen, hlen, ← sumFrom_smul]
    exact sumFrom_congr _ _ fun j _ hj => by
      have hj' : j < n + 1 := Nat.lt_of_lt_of_eq hj (Nat.zero_add _)
      unfold term
      match Nat.decEq i j with
      | .isTrue e =>
        subst e
        rw [row_setAt_eq _ _ _ (hM ▸ hi), row_setAt_eq _ _ _ (hM ▸ hi), minor_setAt_eq, minor_setAt_eq, head_rsmul,
          mul_left_comm (sgn i) c, Ext.mul_assoc c]
      | .isFalse e =>
        rw [row_setAt_ne _ _ _ _ e, row_setAt_ne _ _ _ _ e, minor_setAt _ _ _ _ e, minor_setAt _ _ _ _ e, tail_rsmul]
        match n with
        | 0 => exact absurd (eq_zero_of_lt_one hi ▸ eq_zero_of_lt_one hj' ▸ e) (fun h => h rfl)
        | n + 1 =>
          have hjM : j < M.length := by rw [hM]; exact hj'
          rw [det_setAt_smul n (minor M j) (shift i j) c r.tail
            (Nat.succ.inj (show (minor M j).length + 1 = n + 1 + 1 by rw [length_minor M j hjM]; exact hM))
            (shift_lt hi hj' e), mul_left_comm _ c]

/-! ## The adjacent swap and the vanishing on equal rows -/

/-- The matrix with rows `i` and `i + 1` exchanged. -/
def swapAdj (M : Mat p ν) (i : Nat) : Mat p ν := setAt (setAt M i (row M (i + 1))) (i + 1) (row M i)

theorem length_swapAdj (M : Mat p ν) (i : Nat) : (swapAdj M i).length = M.length := by
  unfold swapAdj; rw [length_setAt, length_setAt]

theorem row_swapAdj_fst (M : Mat p ν) (i : Nat) (h : i + 1 < M.length) : row (swapAdj M i) i = row M (i + 1) := by
  unfold swapAdj
  rw [row_setAt_ne _ _ _ _ (Nat.ne_of_gt (Nat.lt_succ_self i)), row_setAt_eq _ _ _ (Nat.lt_of_succ_lt h)]
theorem row_swapAdj_snd (M : Mat p ν) (i : Nat) (h : i + 1 < M.length) : row (swapAdj M i) (i + 1) = row M i := by
  unfold swapAdj; rw [row_setAt_eq _ _ _ (by rw [length_setAt]; exact h)]
theorem row_swapAdj_other (M : Mat p ν) (i j : Nat) (h1 : j ≠ i) (h2 : j ≠ i + 1) : row (swapAdj M i) j = row M j := by
  unfold swapAdj; rw [row_setAt_ne _ _ _ _ (Ne.symm h2), row_setAt_ne _ _ _ _ (Ne.symm h1)]

theorem nth_removeAt_lt {α : Type} (d : α) : ∀ (l : List α) (j k : Nat), k < j → nth d (removeAt l j) k = nth d l k
  | [], _, _, _ => rfl
  | _ :: _, 0, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, _ + 1, 0, _ => rfl
  | _ :: l, j + 1, k + 1, h => nth_removeAt_lt d l j k (Nat.lt_of_succ_lt_succ h)
theorem nth_removeAt_ge {α : Type} (d : α) : ∀ (l : List α) (j k : Nat), j ≤ k → nth d (removeAt l j) k = nth d l (k + 1)
  | [], _, _, _ => rfl
  | _ :: _, 0, _, _ => rfl
  | _ :: _, _ + 1, 0, h => absurd h (Nat.not_succ_le_zero _)
  | _ :: l, j + 1, k + 1, h => nth_removeAt_ge d l j k (Nat.le_of_succ_le_succ h)

theorem row_minor_lt (M : Mat p ν) (j k : Nat) (h : k < j) : row (minor M j) k = (row M k).tail := by
  show nth [] ((removeAt M j).map List.tail) k = (nth [] M k).tail
  rw [show nth [] ((removeAt M j).map List.tail) k = (nth [] (removeAt M j) k).tail from
    nth_map List.tail [] (removeAt M j) k, nth_removeAt_lt _ _ _ _ h]
theorem row_minor_ge (M : Mat p ν) (j k : Nat) (h : j ≤ k) : row (minor M j) k = (row M (k + 1)).tail := by
  show nth [] ((removeAt M j).map List.tail) k = (nth [] M (k + 1)).tail
  rw [show nth [] ((removeAt M j).map List.tail) k = (nth [] (removeAt M j) k).tail from
    nth_map List.tail [] (removeAt M j) k, nth_removeAt_ge _ _ _ _ h]

/-- Removing entry `i` and writing it back at `i` removes entry `i + 1`. -/
theorem removeAt_succ_eq {α : Type} (d : α) : ∀ (l : List α) (i : Nat), i + 1 < l.length →
    setAt (removeAt l i) i (nth d l i) = removeAt l (i + 1)
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | _ :: [], 0, h => absurd (Nat.lt_of_succ_lt_succ h) (Nat.not_lt_zero _)
  | _ :: _ :: _, 0, _ => rfl
  | _ :: l, i + 1, h => congrArg (_ :: ·) (removeAt_succ_eq d l i (Nat.lt_of_succ_lt_succ h))

/-- The minor at `i` of the swap at `i` is the minor at `i + 1`, and conversely. -/
theorem minor_swapAdj_fst (M : Mat p ν) (i : Nat) (h : i + 1 < M.length) : minor (swapAdj M i) i = minor M (i + 1) := by
  unfold swapAdj
  rw [minor_setAt_lt _ _ _ _ (Nat.lt_succ_self i), minor_setAt_eq]
  show setAt (minor M i) i (row M i).tail = minor M (i + 1)
  unfold minor
  rw [← map_setAt]
  exact congrArg (List.map List.tail) (removeAt_succ_eq [] M i h)

theorem setAt_removeAt_succ {α : Type} (d : α) : ∀ (l : List α) (i : Nat), i + 1 < l.length →
    setAt (removeAt l (i + 1)) i (nth d l (i + 1)) = removeAt l i
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | _ :: [], 0, h => absurd (Nat.lt_of_succ_lt_succ h) (Nat.not_lt_zero _)
  | _ :: _ :: _, 0, _ => rfl
  | _ :: l, i + 1, h => congrArg (_ :: ·) (setAt_removeAt_succ d l i (Nat.lt_of_succ_lt_succ h))

theorem minor_swapAdj_snd (M : Mat p ν) (i : Nat) (h : i + 1 < M.length) : minor (swapAdj M i) (i + 1) = minor M i := by
  unfold swapAdj
  rw [minor_setAt_eq, minor_setAt_gt _ _ _ _ (Nat.lt_succ_self i)]
  show setAt (minor M (i + 1)) i (row M (i + 1)).tail = minor M i
  unfold minor
  rw [← map_setAt]
  exact congrArg (List.map List.tail) (setAt_removeAt_succ [] M i h)

theorem shift_succ (i j : Nat) (h1 : j ≠ i) (h2 : j ≠ i + 1) : shift (i + 1) j = shift i j + 1 := by
  unfold shift
  match Nat.decLt j i with
  | .isTrue hji =>
    rw [ite_eq_left (Nat.lt_succ_of_lt hji), ite_eq_left hji]
    match i, hji with
    | i' + 1, _ => rfl
  | .isFalse hji =>
    rw [ite_eq_right hji, ite_eq_right]
    intro hj; exact h1 (Nat.le_antisymm (Nat.le_of_lt_succ hj) (Nat.le_of_not_lt hji))

theorem minor_swapAdj_other (M : Mat p ν) (i j : Nat) (h1 : j ≠ i) (h2 : j ≠ i + 1) :
    minor (swapAdj M i) j = swapAdj (minor M j) (shift i j) := by
  unfold swapAdj
  rw [minor_setAt _ _ _ _ (Ne.symm h2), minor_setAt _ _ _ _ (Ne.symm h1), shift_succ i j h1 h2]
  unfold shift
  match Nat.decLt j i with
  | .isTrue hji =>
    rw [ite_eq_left hji]
    match i, hji with
    | i' + 1, hji' =>
      show setAt (setAt (minor M j) i' (row M (i' + 1 + 1)).tail) (i' + 1) (row M (i' + 1)).tail =
        setAt (setAt (minor M j) i' (row (minor M j) (i' + 1))) (i' + 1) (row (minor M j) i')
      rw [← row_minor_ge M j (i' + 1) (Nat.le_of_lt hji'), ← row_minor_ge M j i' (Nat.le_of_lt_succ hji')]
  | .isFalse hji =>
    rw [ite_eq_right hji]
    have hij : i + 1 < j := Nat.lt_of_le_of_ne (Nat.lt_of_le_of_ne (Nat.le_of_not_lt hji) (Ne.symm h1)) (Ne.symm h2)
    rw [← row_minor_lt M j (i + 1) hij, ← row_minor_lt M j i (Nat.lt_of_succ_lt hij)]

/-- The transposition of `i` and `i + 1`. -/
def tr (i j : Nat) : Nat := if j = i then i + 1 else if j = i + 1 then i else j

theorem tr_fst (i : Nat) : tr i i = i + 1 := by unfold tr; rw [ite_eq_left rfl]
theorem tr_snd (i : Nat) : tr i (i + 1) = i := by
  unfold tr; rw [ite_eq_right (Nat.ne_of_gt (Nat.lt_succ_self i)), ite_eq_left rfl]
theorem tr_other (i j : Nat) (h1 : j ≠ i) (h2 : j ≠ i + 1) : tr i j = j := by
  unfold tr; rw [ite_eq_right h1, ite_eq_right h2]

/-- A sum is unchanged by exchanging two adjacent summands. -/
theorem sumFrom_tr (f : Nat → Ext p ν) (i m : Nat) :
    sumFrom (fun j => f (tr i j)) (i + (m + 2)) 0 = sumFrom f (i + (m + 2)) 0 := by
    rw [← sumFrom_split _ i (m + 2) 0, ← sumFrom_split f i (m + 2) 0, Nat.zero_add]
    rw [sumFrom_congr i 0 (fun j _ hj => by
      rw [tr_other i j (Nat.ne_of_lt (Nat.lt_of_lt_of_eq hj (Nat.zero_add i)))
        (Nat.ne_of_lt (Nat.lt_succ_of_lt (Nat.lt_of_lt_of_eq hj (Nat.zero_add i))))])]
    show sumFrom f i 0 + (f (tr i i) + (f (tr i (i + 1)) + sumFrom (fun j => f (tr i j)) m (i + 2))) =
      sumFrom f i 0 + (f i + (f (i + 1) + sumFrom f m (i + 2)))
    rw [tr_fst, tr_snd, sumFrom_congr m (i + 2) (fun j hj _ => by
      rw [tr_other i j (Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.lt_succ_of_lt (Nat.lt_succ_self i)) hj))
        (Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.lt_succ_self (i + 1)) hj))]), add_left_comm (f (i + 1)) (f i)]

/-- The adjacent swap negates the determinant. -/
theorem det_swapAdj : ∀ (n : Nat) (M : Mat p ν) (i : Nat), M.length = n + 2 → i + 1 < n + 2 → det (swapAdj M i) = -(det M)
  | n, M, i, hM, hi => by
    have hlen : (swapAdj M i).length = n + 2 := (length_swapAdj M i).trans hM
    have hiM : i + 1 < M.length := hM ▸ hi
    rw [det_expand _ (hlen ▸ Nat.succ_pos _), det_expand _ (hM ▸ Nat.succ_pos _), hlen, hM, ← sumFrom_neg]
    have hk : n + 2 = i + (n - i + 2) := by
      rw [← Nat.add_assoc, FRC.Nat.add_sub_of_le (Nat.le_of_lt_succ (Nat.lt_of_succ_lt_succ hi))]
    rw [hk, ← sumFrom_tr (fun j => -(term det M j)) i (n - i)]
    exact sumFrom_congr _ _ fun j _ hj => by
      have hj' : j < n + 2 := Nat.lt_of_lt_of_eq hj (by rw [Nat.zero_add]; exact hk.symm)
      unfold term
      match Nat.decEq j i with
      | .isTrue e =>
        subst e
        rw [tr_fst, row_swapAdj_fst M j hiM, minor_swapAdj_fst M j hiM, sgn_succ, ← Hermitian.neg_mul, ← Hermitian.neg_mul,
          Hermitian.neg_neg]
      | .isFalse e1 =>
        match Nat.decEq j (i + 1) with
        | .isTrue e =>
          subst e
          rw [tr_snd, row_swapAdj_snd M i hiM, minor_swapAdj_snd M i hiM, sgn_succ, ← Hermitian.neg_mul, ← Hermitian.neg_mul]
        | .isFalse e2 =>
          rw [tr_other i j e1 e2, row_swapAdj_other M i j e1 e2, minor_swapAdj_other M i j e1 e2]
          match n with
          | 0 =>
            match i, j, hi, hj' with
            | 0, 0, _, _ => exact absurd rfl e1
            | 0, 1, _, _ => exact absurd rfl e2
            | 0, _ + 2, _, hj => exact absurd (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hj)) (Nat.not_lt_zero _)
            | _ + 1, _, hi, _ => exact absurd (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hi)) (Nat.not_lt_zero _)
          | n + 1 =>
            have hjM : j < M.length := by rw [hM]; exact hj'
            rw [det_swapAdj n (minor M j) (shift i j)
              (Nat.succ.inj (show (minor M j).length + 1 = n + 2 + 1 by rw [length_minor M j hjM]; exact hM))
              (shift_succ i j e1 e2 ▸ shift_lt hi hj' (Ne.symm e2)), Hermitian.mul_neg]

/-! ## Two equal rows -/

theorem removeAt_eq_of_eq {α : Type} (d : α) : ∀ (l : List α) (i : Nat), i + 1 < l.length → nth d l i = nth d l (i + 1) →
    removeAt l i = removeAt l (i + 1)
  | [], _, h, _ => absurd h (Nat.not_lt_zero _)
  | _ :: [], 0, h, _ => absurd (Nat.lt_of_succ_lt_succ h) (Nat.not_lt_zero _)
  | a :: b :: l, 0, _, e => by
    show b :: l = a :: l
    exact congrArg (· :: l) (show a = b from e).symm
  | _ :: l, i + 1, h, e => congrArg (_ :: ·) (removeAt_eq_of_eq d l i (Nat.lt_of_succ_lt_succ h) e)

theorem minor_eq_of_adj_eq (M : Mat p ν) (i : Nat) (h : i + 1 < M.length) (e : row M i = row M (i + 1)) :
    minor M i = minor M (i + 1) := by
  unfold minor; rw [removeAt_eq_of_eq [] M i h e]

theorem term_eq_zero_of_minor {d : Mat p ν → Ext p ν} {M : Mat p ν} {j : Nat} (h : d (minor M j) = 0) : term d M j = 0 := by
  unfold term; rw [h, mul_zero]

theorem neg_eq_zero {x : Ext p ν} (h : -x = 0) : x = 0 := by
  rw [← Hermitian.neg_neg x, h]; exact Ext.ext Shell.neg_zero Shell.neg_zero

/-- Two equal adjacent rows: the determinant vanishes. -/
theorem det_adj_eq_zero : ∀ (n : Nat) (M : Mat p ν) (i : Nat), M.length = n + 2 → i + 1 < n + 2 → row M i = row M (i + 1) →
    det M = 0
  | n, M, i, hM, hi, e => by
    have hiM : i + 1 < M.length := hM ▸ hi
    rw [det_expand _ (hM ▸ Nat.succ_pos _), hM]
    have hk : n + 2 = i + (n - i + 2) := by
      rw [← Nat.add_assoc, FRC.Nat.add_sub_of_le (Nat.le_of_lt_succ (Nat.lt_of_succ_lt_succ hi))]
    rw [hk, ← sumFrom_split _ i (n - i + 2) 0, Nat.zero_add]
    show sumFrom (term det M) i 0 + (term det M i + (term det M (i + 1) + sumFrom (term det M) (n - i) (i + 2))) = 0
    -- the two terms of the equal rows cancel
    have h2 : term det M i + term det M (i + 1) = 0 := by
      unfold term
      rw [minor_eq_of_adj_eq M i hiM e, ← e, sgn_succ, ← Hermitian.neg_mul, ← Hermitian.neg_mul, add_neg]
    -- the other terms vanish by induction
    have hlow : sumFrom (term det M) i 0 = 0 := by
      rw [← sumFrom_zero_fn i 0]
      exact sumFrom_congr _ _ fun j _ hj => by
        have hji : j < i := Nat.lt_of_lt_of_eq hj (Nat.zero_add i)
        apply term_eq_zero_of_minor
        match n, hi with
        | 0, hi => exact absurd (Nat.lt_of_lt_of_le hji (Nat.le_of_lt_succ (Nat.lt_of_succ_lt_succ hi))) (Nat.not_lt_zero _)
        | n + 1, hi =>
          have hjM : j < M.length := by rw [hM]; exact Nat.lt_of_lt_of_le hji (Nat.le_of_lt (Nat.lt_of_succ_lt hi))
          refine det_adj_eq_zero n (minor M j) (i - 1)
            (Nat.succ.inj (show (minor M j).length + 1 = n + 2 + 1 by rw [length_minor M j hjM]; exact hM)) ?_ ?_
          · match i, hji, hi with
            | i' + 1, _, hi => exact Nat.lt_of_succ_lt_succ hi
          · match i, hji with
            | i' + 1, hji =>
              show row (minor M j) i' = row (minor M j) (i' + 1)
              rw [row_minor_ge M j i' (Nat.le_of_lt_succ hji), row_minor_ge M j (i' + 1) (Nat.le_of_lt hji), e]
    have hhigh : sumFrom (term det M) (n - i) (i + 2) = 0 := by
      rw [← sumFrom_zero_fn (n - i) (i + 2)]
      exact sumFrom_congr _ _ fun j hj hj' => by
        apply term_eq_zero_of_minor
        have hjn : j < n + 2 := by
          have := FRC.Nat.add_sub_of_le (Nat.le_of_lt_succ (Nat.lt_of_succ_lt_succ hi))
          rw [Nat.add_right_comm] at hj'; rw [this] at hj'; exact hj'
        match n, i, hi, hj, hj' with
        | 0, 0, _, hj, hj' => exact absurd (Nat.lt_of_le_of_lt hj hj') (Nat.lt_irrefl _)
        | 0, _ + 1, hi, _, _ => exact absurd (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hi)) (Nat.not_lt_zero _)
        | n + 1, i, hi, hj, _ =>
          have hjM : j < M.length := by rw [hM]; exact hjn
          refine det_adj_eq_zero n (minor M j) i
            (Nat.succ.inj (show (minor M j).length + 1 = n + 2 + 1 by rw [length_minor M j hjM]; exact hM))
            (Nat.lt_of_succ_lt_succ (Nat.lt_of_le_of_lt hj hjn)) ?_
          rw [row_minor_lt M j i (Nat.lt_of_succ_lt (Nat.lt_of_succ_le hj)),
            row_minor_lt M j (i + 1) (Nat.lt_of_succ_le hj), e]
    rw [hlow, hhigh, add_zero, zero_add, h2]

theorem length_form_two {α : Type} {l : List α} (h : 2 ≤ l.length) : l.length = l.length - 2 + 2 := (FRC.Nat.sub_add_cancel h).symm
theorem length_form_one {α : Type} {l : List α} (h : 1 ≤ l.length) : l.length = l.length - 1 + 1 := (FRC.Nat.sub_add_cancel h).symm

/-- Two equal rows at `i` and `i + d + 1`: the determinant vanishes (the lower row brought up by adjacent swaps). -/
theorem det_rows_eq_zero : ∀ (d : Nat) (M : Mat p ν) (i : Nat), i + d + 1 < M.length → row M i = row M (i + d + 1) → det M = 0
  | 0, M, i, h, e =>
    have h2 : 2 ≤ M.length := Nat.le_trans (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le i))) h
    det_adj_eq_zero (M.length - 2) M i (length_form_two h2) (length_form_two h2 ▸ h) e
  | d + 1, M, i, h, e => by
    have h2 : 2 ≤ M.length := Nat.le_trans (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _))) h
    have hne1 : i ≠ i + d + 1 := Nat.ne_of_lt (Nat.lt_succ_of_le (Nat.le_add_right i d))
    have hne2 : i ≠ i + d + 1 + 1 := Nat.ne_of_lt (Nat.lt_succ_of_lt (Nat.lt_succ_of_le (Nat.le_add_right i d)))
    have hrec := det_rows_eq_zero d (swapAdj M (i + d + 1)) i
      (by rw [length_swapAdj]; exact Nat.lt_of_succ_lt h)
      (by rw [row_swapAdj_other M (i + d + 1) i hne1 hne2, row_swapAdj_fst M (i + d + 1) h]; exact e)
    rw [det_swapAdj (M.length - 2) M (i + d + 1) (length_form_two h2) (length_form_two h2 ▸ h)] at hrec
    exact neg_eq_zero hrec

/-- Two equal rows at any two positions. -/
theorem det_rows_eq_zero' (M : Mat p ν) (i k : Nat) (hik : i ≠ k) (hi : i < M.length) (hk : k < M.length)
    (e : row M i = row M k) : det M = 0 := by
  match Nat.lt_or_ge i k with
  | .inl hlt =>
    have hd : i + (k - i - 1) + 1 = k := by
      rw [Nat.add_assoc, FRC.Nat.sub_add_cancel (sub_pos_of_lt' hlt), FRC.Nat.add_sub_of_le (Nat.le_of_lt hlt)]
    exact det_rows_eq_zero (k - i - 1) M i (by rw [hd]; exact hk) (by rw [hd]; exact e)
  | .inr hge =>
    have hlt : k < i := Nat.lt_of_le_of_ne hge (Ne.symm hik)
    have hd : k + (i - k - 1) + 1 = i := by
      rw [Nat.add_assoc, FRC.Nat.sub_add_cancel (sub_pos_of_lt' hlt), FRC.Nat.add_sub_of_le (Nat.le_of_lt hlt)]
    exact det_rows_eq_zero (i - k - 1) M k (by rw [hd]; exact hi) (by rw [hd]; exact e.symm)

/-! ## Row operations and square matrices -/

/-- A square matrix: every row as long as the list of rows. -/
def Square (M : Mat p ν) : Prop := ∀ i, i < M.length → (row M i).length = M.length

theorem setAt_self {α : Type} (d : α) : ∀ (l : List α) (i : Nat), i < l.length → setAt l i (nth d l i) = l
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _ => rfl
  | _ :: l, i + 1, h => congrArg (_ :: ·) (setAt_self d l i (Nat.lt_of_succ_lt_succ h))

theorem length_rsmul (c : Ext p ν) (r : List (Ext p ν)) : (rsmul c r).length = r.length := length_map _ r
theorem setAt_row_self (M : Mat p ν) (i : Nat) (h : i < M.length) : setAt M i (row M i) = M := setAt_self [] M i h

/-- Adding a multiple of row `k` to row `i` leaves the determinant unchanged. -/
theorem det_addRow (M : Mat p ν) (hS : Square M) (i k : Nat) (hik : i ≠ k) (hi : i < M.length) (hk : k < M.length)
    (c : Ext p ν) : det (setAt M i (radd (row M i) (rsmul c (row M k)))) = det M := by
  have hn : M.length = M.length - 1 + 1 := length_form_one (Nat.lt_of_le_of_lt (Nat.zero_le i) hi)
  have hi' : i < M.length - 1 + 1 := by rw [← hn]; exact hi
  rw [det_setAt_add (M.length - 1) M i _ _ hn hi' (by rw [length_rsmul]; exact (hS i hi).trans (hS k hk).symm),
    det_setAt_smul (M.length - 1) M i c _ hn hi', setAt_row_self M i hi,
    det_rows_eq_zero' (setAt M i (row M k)) i k hik (by rw [length_setAt]; exact hi) (by rw [length_setAt]; exact hk)
      (by rw [row_setAt_eq _ _ _ hi, row_setAt_ne _ _ _ _ hik]), mul_zero, add_zero]

end FRC.Dirac.Det
