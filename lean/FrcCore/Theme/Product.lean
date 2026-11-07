import FrcCore.Theme.Cayley
/-!
# FrcCore.Theme.Product — the determinant of a product (the operator theme)

`det (A · B) = det A · det B` for square matrices over `K`, by elementary row operations. An operation — the addition of
a multiple of one row to another — is a datum, `Op`; a list of them applies to a matrix, `apply`, leaves the determinant
unchanged (`det_apply`, from `Theme/Det`'s `det_addRow`) and commutes with the right multiplication by any matrix
(`apply_mul`: the rows of `M · B` are the rows of `M` times `B`, a linear map of the row). Gauss–Jordan elimination
(`gj`) reads its operations off `A` — no swaps: a pivot below the current row is added to it — and ends either in a
diagonal matrix with nonzero diagonal or in a matrix with a zero row (`gj_spec`); applied to `A · B` the same operations
give `D · B`, whose rows are the scaled rows of `B`, or a matrix with a zero row. The two cases give the theorem
(`det_mul`). The identities rest on `Theme/Dirac`'s `Mat.mul` (`dot`, a left fold, is `Theme/Elim`'s `dotL`). No axioms.
-/

namespace FRC.Dirac.Det

open FRC FRC.Extension FRC.Dirac FRC.Dirac.Hermitian
open FRC.Dirac.Mat (nth)
open FRC.Shell (Frame)
open FRC.Shell.Frame (IsSquare)

variable {p : Nat} [Pos p] {ν : Shell p}

/-! ## The product, row by row -/

/-- The row vector times the matrix: the `i`-th row of `M · B` is `rowMul (row M i) B`. -/
def rowMul (r : List (Ext p ν)) (B : Mat p ν) : List (Ext p ν) := (Mat.transpose B).map fun c => Mat.dot r c

theorem mul_eq_map (M B : Mat p ν) : M * B = M.map fun r => rowMul r B := rfl

theorem length_mul (M B : Mat p ν) : (M * B).length = M.length := length_map _ M

theorem row_mul (M B : Mat p ν) (i : Nat) (hi : i < M.length) : row (M * B) i = rowMul (row M i) B :=
  nth_map_lt (fun r => rowMul r B) [] [] M i hi

theorem foldl_add_eq (l : List (Ext p ν)) : ∀ a : Ext p ν, l.foldl (· + ·) a = a + l.foldl (· + ·) 0 := by
  induction l with
  | nil => intro a; exact (add_zero a).symm
  | cons x l ih =>
    intro a
    show l.foldl (· + ·) (a + x) = a + l.foldl (· + ·) (0 + x)
    rw [ih (a + x), ih (0 + x), zero_add, add_assoc]

theorem dot_eq_dotL : ∀ r c : List (Ext p ν), Mat.dot r c = dotL r c
  | [], _ => rfl
  | _ :: _, [] => rfl
  | a :: r, x :: c => by
    show (List.zipWith (· * ·) r c).foldl (· + ·) (0 + a * x) = a * x + dotL r c
    rw [foldl_add_eq, zero_add]; exact congrArg (a * x + ·) (dot_eq_dotL r c)

theorem zipWith_map_same {α β : Type} (f g : α → β) (h : β → β → β) : ∀ l : List α,
    List.zipWith h (l.map f) (l.map g) = l.map fun x => h (f x) (g x)
  | [] => rfl
  | _ :: l => congrArg (_ :: ·) (zipWith_map_same f g h l)

theorem rowMul_radd (r s : List (Ext p ν)) (B : Mat p ν) (h : r.length = s.length) :
    rowMul (radd r s) B = radd (rowMul r B) (rowMul s B) := by
  show (Mat.transpose B).map (fun c => Mat.dot (radd r s) c) =
    radd ((Mat.transpose B).map fun c => Mat.dot r c) ((Mat.transpose B).map fun c => Mat.dot s c)
  rw [← zipWith_add_eq_radd ((Mat.transpose B).map fun c => Mat.dot r c), zipWith_map_same]
  exact map_congr' (fun c => by rw [dot_eq_dotL, dot_eq_dotL, dot_eq_dotL, dotL_radd r s c h]) _

theorem rowMul_rsmul (k : Ext p ν) (r : List (Ext p ν)) (B : Mat p ν) : rowMul (rsmul k r) B = rsmul k (rowMul r B) := by
  show (Mat.transpose B).map (fun c => Mat.dot (rsmul k r) c) = ((Mat.transpose B).map _).map (k * ·)
  rw [map_map']
  exact map_congr' (fun c => by rw [dot_eq_dotL, dot_eq_dotL, dotL_rsmul]) _

theorem length_rowMul (r : List (Ext p ν)) (B : Mat p ν) : (rowMul r B).length = (Mat.transpose B).length := length_map _ _

theorem length_transpose (B : Mat p ν) : (Mat.transpose B).length = (B.headD []).length := by
  show ((List.range _).map _).length = _; rw [length_map, range_eq_rangeS, length_rangeS]

theorem headD_eq_row (B : Mat p ν) : B.headD [] = row B 0 := by
  cases B with
  | nil => rfl
  | cons r _ => rfl

/-- A square `B` of size `n > 0` has `n` columns, so `M · B` has rows of length `n`. -/
theorem length_transpose_square (B : Mat p ν) (hB : Square B) (h0 : 0 < B.length) : (Mat.transpose B).length = B.length := by
  rw [length_transpose, headD_eq_row]; exact hB 0 h0

theorem square_mul (M B : Mat p ν) (hB : Square B) (hMB : M.length = B.length) (h0 : 0 < B.length) : Square (M * B) := fun i hi => by
  rw [length_mul] at hi ⊢
  rw [row_mul M B i hi, length_rowMul, length_transpose_square B hB h0, hMB]

/-! ## Elementary row operations as data -/

/-- The elementary row operation `addRow i k c`: `c` times row `k` is added to row `i` (`i ≠ k`). -/
inductive Op (p : Nat) [Pos p] (ν : Shell p) where
  | addRow (i k : Nat) (c : Ext p ν)

def apply1 : Op p ν → Mat p ν → Mat p ν
  | .addRow i k c, M => setAt M i (radd (row M i) (rsmul c (row M k)))

def apply : List (Op p ν) → Mat p ν → Mat p ν
  | [], M => M
  | o :: os, M => apply os (apply1 o M)

/-- The operation stays inside an `n × n` matrix. -/
def Valid (n : Nat) : Op p ν → Prop
  | .addRow i k _ => i < n ∧ k < n ∧ i ≠ k

def ValidL (n : Nat) : List (Op p ν) → Prop
  | [] => True
  | o :: os => Valid n o ∧ ValidL n os

theorem validL_append (n : Nat) : ∀ (l m : List (Op p ν)), ValidL n l → ValidL n m → ValidL n (l ++ m)
  | [], _, _, hm => hm
  | _ :: l, m, ⟨ho, hl⟩, hm => ⟨ho, validL_append n l m hl hm⟩

theorem apply_append : ∀ (l m : List (Op p ν)) (M : Mat p ν), apply (l ++ m) M = apply m (apply l M)
  | [], _, _ => rfl
  | o :: l, m, M => apply_append l m (apply1 o M)

theorem length_apply1 : ∀ (o : Op p ν) (M : Mat p ν), (apply1 o M).length = M.length
  | .addRow i _ _, M => length_setAt M i _

theorem length_apply : ∀ (l : List (Op p ν)) (M : Mat p ν), (apply l M).length = M.length
  | [], _ => rfl
  | o :: l, M => by show (apply l (apply1 o M)).length = M.length; rw [length_apply l, length_apply1]

theorem square_apply1 : ∀ (o : Op p ν) (M : Mat p ν), Valid M.length o → Square M → Square (apply1 o M)
  | .addRow i k _, M, ⟨hi, hk, _⟩, hS => square_setAt M hS i _ (by rw [length_radd _ _ (by rw [length_rsmul, hS i hi, hS k hk]), hS i hi])

theorem square_apply : ∀ (l : List (Op p ν)) (M : Mat p ν), ValidL M.length l → Square M → Square (apply l M)
  | [], _, _, hS => hS
  | o :: l, M, ⟨ho, hl⟩, hS => by
    show Square (apply l (apply1 o M))
    exact square_apply l _ (by rw [length_apply1]; exact hl) (square_apply1 o M ho hS)

/-! ## The determinant under the operations -/

theorem det_apply1 : ∀ (o : Op p ν) (M : Mat p ν), Valid M.length o → Square M → det (apply1 o M) = det M
  | .addRow i k c, M, ⟨hi, hk, hik⟩, hS => det_addRow M hS i k hik hi hk c

theorem det_apply : ∀ (l : List (Op p ν)) (M : Mat p ν), ValidL M.length l → Square M → det (apply l M) = det M
  | [], _, _, _ => rfl
  | o :: l, M, ⟨ho, hl⟩, hS => by
    show det (apply l (apply1 o M)) = det M
    rw [det_apply l _ (by rw [length_apply1]; exact hl) (square_apply1 o M ho hS), det_apply1 o M ho hS]

/-! ## The operations commute with the right multiplication -/

theorem addRow_mul (M B : Mat p ν) (hS : Square M) (i k : Nat) (hi : i < M.length) (hk : k < M.length) (c : Ext p ν) :
    setAt M i (radd (row M i) (rsmul c (row M k))) * B = setAt (M * B) i (radd (row (M * B) i) (rsmul c (row (M * B) k))) := by
  show (setAt M i (radd (row M i) (rsmul c (row M k)))).map (rowMul · B) = _
  rw [row_mul M B i hi, row_mul M B k hk, map_setAt, rowMul_radd _ _ _ (by rw [length_rsmul, hS i hi, hS k hk]), rowMul_rsmul]
  rfl

theorem apply1_mul : ∀ (o : Op p ν) (M B : Mat p ν), Valid M.length o → Square M → apply1 o M * B = apply1 o (M * B)
  | .addRow i k c, M, B, ⟨hi, hk, _⟩, hS => addRow_mul M B hS i k hi hk c

theorem apply_mul : ∀ (l : List (Op p ν)) (M B : Mat p ν), ValidL M.length l → Square M → apply l M * B = apply l (M * B)
  | [], _, _, _, _ => rfl
  | o :: l, M, B, ⟨ho, hl⟩, hS => by
    show apply l (apply1 o M) * B = apply l (apply1 o (M * B))
    rw [apply_mul l _ B (by rw [length_apply1]; exact hl) (square_apply1 o M ho hS), apply1_mul o M B ho hS]


/-! ## Gauss–Jordan elimination, its operations read off the matrix

No swaps: when the pivot of column `j` lies in a row `k` below `r`, row `r` gains row `k` (one `addRow r k 1`, which makes
`M[r][j] = M[k][j] ≠ 0` since the rows between have a zero there), then every other row loses its multiple of row `r`. -/

/-- The entry `M[i][c]`. -/
def E (M : Mat p ν) (i c : Nat) : Ext p ν := nth 0 (row M i) c

/-- The least row `k ≥ i` among the next `f` rows with `M[k][j] ≠ 0`. -/
def pivotCol (M : Mat p ν) (j : Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | f + 1, i => if E M i j = 0 then pivotCol M j f (i + 1) else some i

theorem pivotCol_none (M : Mat p ν) (j : Nat) : ∀ (f i : Nat), pivotCol M j f i = none → ∀ k, i ≤ k → k < i + f → E M k j = 0
  | 0, _, _, _, hk, hk' => absurd (Nat.lt_of_le_of_lt hk hk') (Nat.lt_irrefl _)
  | f + 1, i, h, k, hk, hk' => by
    unfold pivotCol at h
    match decEq (E M i j) 0 with
    | .isTrue e =>
      rw [ite_eq_left e] at h
      match Nat.decEq i k with
      | .isTrue e' => subst e'; exact e
      | .isFalse e' => exact pivotCol_none M j f (i + 1) h k (Nat.lt_of_le_of_ne hk e') (Nat.add_right_comm i 1 f ▸ hk')
    | .isFalse e => rw [ite_eq_right e] at h; exact nomatch h

theorem pivotCol_some (M : Mat p ν) (j : Nat) : ∀ (f i k : Nat), pivotCol M j f i = some k →
    i ≤ k ∧ k < i + f ∧ E M k j ≠ 0 ∧ ∀ i', i ≤ i' → i' < k → E M i' j = 0
  | 0, _, _, h => nomatch h
  | f + 1, i, k, h => by
    unfold pivotCol at h
    match decEq (E M i j) 0 with
    | .isTrue e =>
      rw [ite_eq_left e] at h
      obtain ⟨h1, h2, h3, h4⟩ := pivotCol_some M j f (i + 1) k h
      refine ⟨Nat.le_of_succ_le h1, Nat.add_right_comm i 1 f ▸ h2, h3, fun i' hi' hik => ?_⟩
      match Nat.decEq i i' with
      | .isTrue e' => subst e'; exact e
      | .isFalse e' => exact h4 i' (Nat.lt_of_le_of_ne hi' e') hik
    | .isFalse e =>
      rw [ite_eq_right e] at h
      cases h
      exact ⟨Nat.le_refl i, Nat.lt_add_of_pos_right (Nat.succ_pos f), e, fun i' hi' hik => absurd (Nat.lt_of_le_of_lt hi' hik) (Nat.lt_irrefl _)⟩

/-- The entries after a row addition: row `i` gains `c` times row `k`, the others stay. -/
theorem nth_radd : ∀ (r s : List (Ext p ν)) (c : Nat), r.length = s.length → nth 0 (radd r s) c = nth 0 r c + nth 0 s c
  | [], [], _, _ => (add_zero 0).symm
  | [], _ :: _, _, h => absurd h (Nat.ne_of_lt (Nat.succ_pos _))
  | _ :: _, [], _, h => absurd h (Nat.ne_of_gt (Nat.succ_pos _))
  | _ :: _, _ :: _, 0, _ => rfl
  | _ :: r, _ :: s, c + 1, h => nth_radd r s c (Nat.succ.inj h)

theorem E_addRow (M : Mat p ν) (hS : Square M) (i k : Nat) (hi : i < M.length) (hk : k < M.length) (c : Ext p ν) (i' c' : Nat) :
    E (apply1 (.addRow i k c) M) i' c' = if i' = i then E M i c' + c * E M k c' else E M i' c' := by
  show nth 0 (row (setAt M i (radd (row M i) (rsmul c (row M k)))) i') c' = _
  match Nat.decEq i' i with
  | .isTrue e => rw [e, ite_eq_left rfl, row_setAt_eq _ _ _ hi, nth_radd _ _ _ (by rw [length_rsmul, hS i hi, hS k hk]), nth_rsmul]; rfl
  | .isFalse e => rw [ite_eq_right e, row_setAt_ne _ _ _ _ (fun h => e h.symm)]; rfl

/-- The clearing of column `j` below and above the pivot row `r`, from the matrix `M1` whose pivot is `a` with `a · ainv = 1`:
the operations for the rows `i < m`, `i ≠ r`, each reading its coefficient off `M1`. -/
def clearOps (M1 : Mat p ν) (r j : Nat) (ainv : Ext p ν) : Nat → List (Op p ν)
  | 0 => []
  | i + 1 => clearOps M1 r j ainv i ++ (if i = r then [] else [Op.addRow i r (-(E M1 i j) * ainv)])

theorem validL_clearOps (M1 : Mat p ν) (r j : Nat) (ainv : Ext p ν) (n : Nat) (hr : r < n) : ∀ m, m ≤ n → ValidL n (clearOps M1 r j ainv m)
  | 0, _ => trivial
  | m + 1, hm => by
    show ValidL n (clearOps M1 r j ainv m ++ _)
    refine validL_append n _ _ (validL_clearOps M1 r j ainv n hr m (Nat.le_of_succ_le hm)) ?_
    match Nat.decEq m r with
    | .isTrue e => rw [ite_eq_left e]; trivial
    | .isFalse e => rw [ite_eq_right e]; exact ⟨⟨Nat.lt_of_succ_le hm, hr, e⟩, trivial⟩

theorem square_clearOps (M1 : Mat p ν) (hS : Square M1) (r j : Nat) (hr : r < M1.length) (ainv : Ext p ν) (m : Nat) (hm : m ≤ M1.length) :
    Square (apply (clearOps M1 r j ainv m) M1) :=
  square_apply _ _ (validL_clearOps M1 r j ainv M1.length hr m hm) hS

/-- The rows the clearing leaves alone: row `r` and the rows `i ≥ m`. -/
theorem E_clearOps_fixed (M1 : Mat p ν) (hS : Square M1) (r j : Nat) (hr : r < M1.length) (ainv : Ext p ν) :
    ∀ m, m ≤ M1.length → ∀ i c, (i = r ∨ m ≤ i) → E (apply (clearOps M1 r j ainv m) M1) i c = E M1 i c
  | 0, _, _, _, _ => rfl
  | m + 1, hm, i, c, hi => by
    show E (apply (clearOps M1 r j ainv m ++ _) M1) i c = _
    rw [apply_append]
    have ih := E_clearOps_fixed M1 hS r j hr ainv m (Nat.le_of_succ_le hm)
    have hi' : i = r ∨ m ≤ i := match hi with | Or.inl h => Or.inl h | Or.inr h => Or.inr (Nat.le_of_succ_le h)
    match Nat.decEq m r with
    | .isTrue e => rw [ite_eq_left e]; exact ih i c hi'
    | .isFalse e =>
      rw [ite_eq_right e]
      show E (apply1 (.addRow m r (-(E M1 m j) * ainv)) (apply (clearOps M1 r j ainv m) M1)) i c = _
      rw [E_addRow _ (square_clearOps M1 hS r j hr ainv m (Nat.le_of_succ_le hm)) m r
            (by rw [length_apply]; exact Nat.lt_of_succ_le hm) (by rw [length_apply]; exact hr)]
      have him : i ≠ m := fun h => match hi with
        | Or.inl h' => e (h.symm.trans h')
        | Or.inr h' => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (Nat.lt_succ_self m) (h ▸ h'))
      rw [ite_eq_right him]; exact ih i c hi'

/-- The cleared rows `i < m`, `i ≠ r`: `E M1 i c − E M1 i j · ainv · E M1 r c`. -/
theorem E_clearOps_cleared (M1 : Mat p ν) (hS : Square M1) (r j : Nat) (hr : r < M1.length) (ainv : Ext p ν) :
    ∀ m, m ≤ M1.length → ∀ i c, i < m → i ≠ r →
      E (apply (clearOps M1 r j ainv m) M1) i c = E M1 i c + (-(E M1 i j) * ainv) * E M1 r c
  | 0, _, i, _, hi, _ => absurd hi (Nat.not_lt_zero i)
  | m + 1, hm, i, c, hi, hir => by
    show E (apply (clearOps M1 r j ainv m ++ _) M1) i c = _
    rw [apply_append]
    match Nat.decEq m r with
    | .isTrue e =>
      rw [ite_eq_left e]
      exact E_clearOps_cleared M1 hS r j hr ainv m (Nat.le_of_succ_le hm) i c
        (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi) (fun h => hir (h.trans e))) hir
    | .isFalse e =>
      rw [ite_eq_right e]
      show E (apply1 (.addRow m r (-(E M1 m j) * ainv)) (apply (clearOps M1 r j ainv m) M1)) i c = _
      rw [E_addRow _ (square_clearOps M1 hS r j hr ainv m (Nat.le_of_succ_le hm)) m r
            (by rw [length_apply]; exact Nat.lt_of_succ_le hm) (by rw [length_apply]; exact hr)]
      match Nat.decEq i m with
      | .isTrue e' =>
        rw [ite_eq_left e', e']
        rw [E_clearOps_fixed M1 hS r j hr ainv m (Nat.le_of_succ_le hm) m c (Or.inr (Nat.le_refl m)),
          E_clearOps_fixed M1 hS r j hr ainv m (Nat.le_of_succ_le hm) r c (Or.inl rfl)]
      | .isFalse e' =>
        rw [ite_eq_right e']
        exact E_clearOps_cleared M1 hS r j hr ainv m (Nat.le_of_succ_le hm) i c (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi) e') hir


/-- The pivot fix: when the pivot of column `j` among the rows `r, …, n−1` is the row `k ≠ r`, row `r` gains row `k`. -/
def fixOps (n r j : Nat) (M : Mat p ν) : List (Op p ν) :=
  match pivotCol M j (n - r) r with
  | none => []
  | some k => if k = r then [] else [Op.addRow r k 1]

/-- The operations of column `j`: the fix, then the clearing of the column outside the pivot row. -/
def colOps (n r j : Nat) (M : Mat p ν) : List (Op p ν) :=
  match pivotCol M j (n - r) r with
  | none => []
  | some _ =>
    let M1 := apply (fixOps n r j M) M
    fixOps n r j M ++ clearOps M1 r j (inv (E M1 r j)) n

/-- The rows `r, …, n−1` are zero in the columns `c < j`. -/
def InvA (n r j : Nat) (M : Mat p ν) : Prop := ∀ i c, r ≤ i → i < n → c < j → E M i c = 0

/-- The columns `c < j` carry a nonzero diagonal entry and nothing else. -/
def InvC (n j : Nat) (M : Mat p ν) : Prop := ∀ c, c < j → E M c c ≠ 0 ∧ ∀ i, i < n → i ≠ c → E M i c = 0

theorem add_sub_of_le' {r n : Nat} (h : r ≤ n) : r + (n - r) = n := FRC.Nat.add_sub_of_le h

/-- One column with a pivot in row `k`: the entries of the matrix after the fix. -/
theorem E_fix (n r j : Nat) (M : Mat p ν) (hM : M.length = n) (hS : Square M) (k : Nat) (hk : pivotCol M j (n - r) r = some k)
    (hkn : k < n) (hrk : r ≤ k) (i c : Nat) :
    E (apply (fixOps n r j M) M) i c = if i = r ∧ k ≠ r then E M r c + E M k c else E M i c := by
  unfold fixOps; rw [hk]
  show E (apply (if k = r then [] else [Op.addRow r k 1]) M) i c = _
  match Nat.decEq k r with
  | .isTrue e =>
    rw [ite_eq_left e]; show E M i c = _
    rw [ite_eq_right (fun h => h.2 e)]
  | .isFalse e =>
    rw [ite_eq_right e]
    show E (apply1 (.addRow r k 1) M) i c = _
    rw [E_addRow M hS r k (hM ▸ Nat.lt_of_le_of_lt hrk hkn) (hM ▸ hkn) 1 i c, Ext.one_mul]
    match Nat.decEq i r with
    | .isTrue e' => rw [ite_eq_left e', ite_eq_left ⟨e', e⟩]
    | .isFalse e' => rw [ite_eq_right e', ite_eq_right (fun h => e' h.1)]

theorem validL_fixOps (n r j : Nat) (M : Mat p ν) (hr : r ≤ n) : ValidL n (fixOps n r j M) := by
  unfold fixOps
  match h : pivotCol M j (n - r) r with
  | none => exact trivial
  | some k =>
    obtain ⟨h1, h2, _, _⟩ := pivotCol_some M j _ r k h
    rw [add_sub_of_le' hr] at h2
    show ValidL n (if k = r then [] else [Op.addRow r k 1])
    match Nat.decEq k r with
    | .isTrue e => rw [ite_eq_left e]; exact trivial
    | .isFalse e => rw [ite_eq_right e]; exact ⟨⟨Nat.lt_of_le_of_lt h1 h2, h2, fun h' => e h'.symm⟩, trivial⟩

/-- The column step. From a square `n × n` matrix with `InvA n r j` (and `InvC n j` when `r = j`), the column's
operations are valid, the new rank `r'` is `r + 1` or `r`, and the invariants advance to column `j + 1`. -/
theorem colOps_spec {κ : Nat} {g : Shell p} (F : Frame p κ g) (hν : ¬IsSquare ν) (n r j : Nat) (M : Mat p ν)
    (hM : M.length = n) (hS : Square M) (hr : r ≤ n) (hA : InvA n r j M) (hC : r = j → InvC n j M) :
    ValidL n (colOps n r j M) ∧
    ((pivotCol M j (n - r) r = none ∧ InvA n r (j + 1) (apply (colOps n r j M) M)) ∨
     (∃ k, pivotCol M j (n - r) r = some k ∧ r < n ∧ InvA n (r + 1) (j + 1) (apply (colOps n r j M) M) ∧
       (r = j → InvC n (j + 1) (apply (colOps n r j M) M)))) := by
  unfold colOps
  match hk : pivotCol M j (n - r) r with
  | none =>
    refine ⟨trivial, Or.inl ⟨rfl, fun i c hi hin hc => ?_⟩⟩
    show E M i c = 0
    match Nat.lt_or_ge c j with
    | Or.inl hcj => exact hA i c hi hin hcj
    | Or.inr hcj =>
      have e : c = j := Nat.le_antisymm (Nat.le_of_lt_succ hc) hcj
      rw [e]; exact pivotCol_none M j _ r hk i hi (by rw [add_sub_of_le' hr]; exact hin)
  | some k =>
    obtain ⟨hrk, hkn, hkj, hbelow⟩ := pivotCol_some M j _ r k hk
    rw [add_sub_of_le' hr] at hkn
    have hrn : r < n := Nat.lt_of_le_of_lt hrk hkn
    -- the fixed matrix and its pivot
    have hM1len : (apply (fixOps n r j M) M).length = n := by rw [length_apply, hM]
    have hM1sq : Square (apply (fixOps n r j M) M) := square_apply _ _ (hM ▸ validL_fixOps n r j M hr) hS
    have hE1 := E_fix n r j M hM hS k hk hkn hrk
    have ha : E (apply (fixOps n r j M) M) r j ≠ 0 := by
      rw [hE1]
      match Nat.decEq k r with
      | .isTrue e => rw [ite_eq_right (fun h => h.2 e), ← e]; exact hkj
      | .isFalse e => rw [ite_eq_left ⟨rfl, e⟩, hbelow r (Nat.le_refl r) (Nat.lt_of_le_of_ne hrk (fun h => e h.symm)), zero_add]; exact hkj
    -- the entries after the clearing
    have hfix : ∀ i c, E (apply (fixOps n r j M) M) i c = if i = r ∧ k ≠ r then E M r c + E M k c else E M i c := hE1
    have hrn1 : r < (apply (fixOps n r j M) M).length := by rw [hM1len]; exact hrn
    have hcl_fixed := E_clearOps_fixed _ hM1sq r j hrn1 (inv (E (apply (fixOps n r j M) M) r j)) n (Nat.le_of_eq hM1len.symm)
    have hcl := E_clearOps_cleared _ hM1sq r j hrn1 (inv (E (apply (fixOps n r j M) M) r j)) n (Nat.le_of_eq hM1len.symm)
    rw [apply_append]
    -- row r of the fixed matrix is zero in the processed columns
    have hr0 : ∀ c, c < j → E (apply (fixOps n r j M) M) r c = 0 := fun c hc => by
      rw [hfix]
      match Nat.decEq k r with
      | .isTrue e => rw [ite_eq_right (fun h => h.2 e)]; exact hA r c (Nat.le_refl r) hrn hc
      | .isFalse e => rw [ite_eq_left ⟨rfl, e⟩, hA r c (Nat.le_refl r) hrn hc, hA k c hrk hkn hc, add_zero]
    have hinv : E (apply (fixOps n r j M) M) r j * inv (E (apply (fixOps n r j M) M) r j) = 1 := mul_inv F hν ha
    -- every row other than r is zero in column j after the clearing
    have hcolj : ∀ i, i < n → i ≠ r → E (apply (clearOps _ r j _ n) (apply (fixOps n r j M) M)) i j = 0 := fun i hin hir => by
      rw [hcl i j hin hir, ← neg_mul, ← neg_mul, Ext.mul_assoc, Ext.mul_comm (inv _), hinv, Ext.mul_one, add_neg]
    refine ⟨validL_append n _ _ (validL_fixOps n r j M hr) (validL_clearOps _ r j _ n hrn n (Nat.le_refl n)),
      Or.inr ⟨k, rfl, hrn, fun i c hi hin hc => ?_, fun hrj c hc => ?_⟩⟩
    · -- InvA n (r + 1) (j + 1)
      have hir : i ≠ r := fun h => Nat.lt_irrefl r (h ▸ hi)
      match Nat.lt_or_ge c j with
      | Or.inl hcj =>
        rw [hcl i c hin hir, hr0 c hcj, mul_zero, add_zero, hfix, ite_eq_right (fun h => hir h.1)]
        exact hA i c (Nat.le_of_succ_le hi) hin hcj
      | Or.inr hcj =>
        have e : c = j := Nat.le_antisymm (Nat.le_of_lt_succ hc) hcj
        rw [e]; exact hcolj i hin hir
    · -- InvC n (j + 1) when r = j
      subst hrj
      match Nat.lt_or_ge c r with
      | Or.inl hcr =>
        obtain ⟨hdiag, hoff⟩ := hC rfl c hcr
        have hcr' : c ≠ r := Nat.ne_of_lt hcr
        have hr0c : E (apply (fixOps n r r M) M) r c = 0 := hr0 c hcr
        have hfixc : ∀ i, i ≠ r → E (apply (fixOps n r r M) M) i c = E M i c := fun i hir => by
          rw [hfix, ite_eq_right (fun h => hir h.1)]
        refine ⟨?_, fun i hin hic => ?_⟩
        · rw [hcl c c (Nat.lt_trans hcr hrn) hcr', hr0c, mul_zero, add_zero, hfixc c hcr']; exact hdiag
        · match Nat.decEq i r with
          | .isTrue e => rw [e, hcl_fixed r c (Or.inl rfl)]; exact hr0c
          | .isFalse e => rw [hcl i c hin e, hr0c, mul_zero, add_zero, hfixc i e]; exact hoff i hin hic
      | Or.inr hcr =>
        have e : c = r := Nat.le_antisymm (Nat.le_of_lt_succ hc) hcr
        subst e
        exact ⟨by rw [hcl_fixed c c (Or.inl rfl)]; exact ha, fun i hin hic => hcolj i hin hic⟩

/-- The rank after column `j`: one more when the column has a pivot. -/
def rankStep (n r j : Nat) (M : Mat p ν) : Nat :=
  match pivotCol M j (n - r) r with
  | none => r
  | some _ => r + 1

theorem rankStep_none (n r j : Nat) (M : Mat p ν) (h : pivotCol M j (n - r) r = none) : rankStep n r j M = r := by
  unfold rankStep; rw [h]

theorem rankStep_some (n r j : Nat) (M : Mat p ν) (k : Nat) (h : pivotCol M j (n - r) r = some k) : rankStep n r j M = r + 1 := by
  unfold rankStep; rw [h]

/-- Gauss–Jordan over `f` more columns from column `j` with rank `r`: the operations and the final rank. -/
def gj (n : Nat) : Nat → Nat → Nat → Mat p ν → List (Op p ν) × Nat
  | 0, r, _, _ => ([], r)
  | f + 1, r, j, M =>
    (colOps n r j M ++ (gj n f (rankStep n r j M) (j + 1) (apply (colOps n r j M) M)).1,
     (gj n f (rankStep n r j M) (j + 1) (apply (colOps n r j M) M)).2)

theorem gj_spec {κ : Nat} {g : Shell p} (F : Frame p κ g) (hν : ¬IsSquare ν) (n : Nat) :
    ∀ (f r j : Nat) (M : Mat p ν), M.length = n → Square M → r ≤ j → j + f = n → InvA n r j M → (r = j → InvC n j M) →
      ValidL n (gj n f r j M).1 ∧ (gj n f r j M).2 ≤ n ∧
      ((gj n f r j M).2 = n → InvC n n (apply (gj n f r j M).1 M)) ∧
      ((gj n f r j M).2 < n → InvA n (gj n f r j M).2 n (apply (gj n f r j M).1 M))
  | 0, r, j, M, _, _, hrj, hj, hA, hC => by
    rw [Nat.add_zero] at hj; subst hj
    exact ⟨trivial, hrj, fun h => hC h, fun _ => hA⟩
  | f + 1, r, j, M, hM, hS, hrj, hj, hA, hC => by
    have hr : r ≤ n := Nat.le_trans hrj (hj ▸ Nat.le_add_right j (f + 1))
    obtain ⟨hv, hcase⟩ := colOps_spec F hν n r j M hM hS hr hA hC
    have hj' : j + 1 + f = n := by rw [Nat.add_right_comm]; exact hj
    show ValidL n (colOps n r j M ++ (gj n f (rankStep n r j M) (j + 1) (apply (colOps n r j M) M)).1) ∧
      (gj n f (rankStep n r j M) (j + 1) (apply (colOps n r j M) M)).2 ≤ n ∧
      ((gj n f (rankStep n r j M) (j + 1) (apply (colOps n r j M) M)).2 = n →
        InvC n n (apply (colOps n r j M ++ (gj n f (rankStep n r j M) (j + 1) (apply (colOps n r j M) M)).1) M)) ∧
      ((gj n f (rankStep n r j M) (j + 1) (apply (colOps n r j M) M)).2 < n →
        InvA n (gj n f (rankStep n r j M) (j + 1) (apply (colOps n r j M) M)).2 n
          (apply (colOps n r j M ++ (gj n f (rankStep n r j M) (j + 1) (apply (colOps n r j M) M)).1) M))
    have hM' : (apply (colOps n r j M) M).length = n := by rw [length_apply, hM]
    have hS' : Square (apply (colOps n r j M) M) := square_apply _ _ (hM ▸ hv) hS
    match hcase with
    | Or.inl ⟨hnone, hA'⟩ =>
      rw [rankStep_none n r j M hnone]
      obtain ⟨v2, hle, hC2, hA2⟩ := gj_spec F hν n f r (j + 1) _ hM' hS' (Nat.le_succ_of_le hrj) hj' hA'
        (fun h => absurd h (Nat.ne_of_lt (Nat.lt_succ_of_le hrj)))
      refine ⟨validL_append n _ _ hv v2, hle, ?_, ?_⟩
      · intro h; rw [apply_append]; exact hC2 h
      · intro h; rw [apply_append]; exact hA2 h
    | Or.inr ⟨k, hsome, _, hA', hC'⟩ =>
      rw [rankStep_some n r j M k hsome]
      obtain ⟨v2, hle, hC2, hA2⟩ := gj_spec F hν n f (r + 1) (j + 1) _ hM' hS' (Nat.succ_le_succ hrj) hj' hA'
        (fun h => hC' (Nat.succ.inj h))
      refine ⟨validL_append n _ _ hv v2, hle, ?_, ?_⟩
      · intro h; rw [apply_append]; exact hC2 h
      · intro h; rw [apply_append]; exact hA2 h


/-! ## From the end state to the theorem -/

theorem nth_unitRow (n i c : Nat) (hc : c < n) : nth 0 (unitRow (ν := ν) n i) c = if i = c then 1 else 0 := by
  show nth 0 ((rangeS n).map fun j => if i = j then (1 : Ext p ν) else 0) c = _
  rw [nth_map_lt (fun j => if i = j then (1 : Ext p ν) else 0) 0 0 _ c (by rw [length_rangeS]; exact hc), nth_rangeS n c hc]

theorem rows_ext (M N : Mat p ν) (hl : M.length = N.length) (h : ∀ i, i < M.length → row M i = row N i) : M = N :=
  ext_nth [] M N hl h

/-- A diagonal matrix (`InvC n n`): its `i`-th row is the `i`-th diagonal entry times the unit row. -/
theorem row_of_invC (D : Mat p ν) (hD : D.length = n) (hS : Square D) (hC : InvC n n D) (i : Nat) (hi : i < n) :
    row D i = rsmul (E D i i) (unitRow n i) := by
  refine ext_nth 0 _ _ (by rw [length_rsmul, length_unitRow, hS i (hD ▸ hi), hD]) fun c hc => ?_
  rw [hS i (hD ▸ hi), hD] at hc
  rw [nth_rsmul, nth_unitRow n i c hc]
  match Nat.decEq i c with
  | .isTrue e => rw [ite_eq_left e, Ext.mul_one, e]; rfl
  | .isFalse e => rw [ite_eq_right e, mul_zero]; exact (hC c hc).2 i hi e

/-- The rows `i < k` of `N` scaled by `d i`. -/
def scaleRows (d : Nat → Ext p ν) (N : Mat p ν) : Nat → Mat p ν
  | 0 => N
  | k + 1 => setAt (scaleRows d N k) k (rsmul (d k) (row N k))

def prodUpto (d : Nat → Ext p ν) : Nat → Ext p ν
  | 0 => 1
  | k + 1 => prodUpto d k * d k

theorem length_scaleRows (d : Nat → Ext p ν) (N : Mat p ν) : ∀ k, (scaleRows d N k).length = N.length
  | 0 => rfl
  | k + 1 => by show (setAt (scaleRows d N k) k _).length = _; rw [length_setAt, length_scaleRows d N k]

theorem row_scaleRows_ge (d : Nat → Ext p ν) (N : Mat p ν) : ∀ k i, k ≤ i → row (scaleRows d N k) i = row N i
  | 0, _, _ => rfl
  | k + 1, i, h => by
    show row (setAt (scaleRows d N k) k _) i = _
    rw [row_setAt_ne _ _ _ _ (Nat.ne_of_lt h), row_scaleRows_ge d N k i (Nat.le_of_succ_le h)]

theorem row_scaleRows_lt (d : Nat → Ext p ν) (N : Mat p ν) : ∀ k i, i < k → i < N.length → row (scaleRows d N k) i = rsmul (d i) (row N i)
  | 0, i, h, _ => absurd h (Nat.not_lt_zero i)
  | k + 1, i, h, hi => by
    show row (setAt (scaleRows d N k) k _) i = _
    match Nat.decEq i k with
    | .isTrue e => rw [e, row_setAt_eq _ _ _ (by rw [length_scaleRows]; exact e ▸ hi)]
    | .isFalse e => rw [row_setAt_ne _ _ _ _ (fun h' => e h'.symm), row_scaleRows_lt d N k i (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h) e) hi]

theorem det_scaleRows (d : Nat → Ext p ν) (N : Mat p ν) : ∀ k, k ≤ N.length → det (scaleRows d N k) = prodUpto d k * det N
  | 0, _ => (Ext.one_mul _).symm
  | k + 1, hk => by
    show det (setAt (scaleRows d N k) k (rsmul (d k) (row N k))) = prodUpto d k * d k * det N
    have hlen : (scaleRows d N k).length = N.length - 1 + 1 := by
      rw [length_scaleRows]; exact length_form_one (Nat.lt_of_lt_of_le (Nat.succ_pos k) hk)
    have hk' : k < N.length - 1 + 1 := by rw [← length_form_one (Nat.lt_of_lt_of_le (Nat.succ_pos k) hk)]; exact hk
    rw [det_setAt_smul (N.length - 1) _ k (d k) (row N k) hlen hk', ← row_scaleRows_ge d N k k (Nat.le_refl k),
      setAt_row_self _ _ (by rw [length_scaleRows]; exact hk), det_scaleRows d N k (Nat.le_of_succ_le hk),
      ← Ext.mul_assoc, Ext.mul_comm (d k)]

theorem map_nth_rangeS : ∀ r : List (Ext p ν), (rangeS r.length).map (fun j => nth 0 r j) = r
  | [] => rfl
  | x :: r => by
    show (rangeS (r.length + 1)).map (fun j => nth 0 (x :: r) j) = x :: r
    rw [rangeS_succ_eq_map, List.map, map_map']
    exact congrArg (x :: ·) (map_nth_rangeS r)

/-- The unit row times `B` is the corresponding row of `B`. -/
theorem rowMul_unitRow (B : Mat p ν) (hB : Square B) (hBn : B.length = n) (h0 : 0 < n) (i : Nat) (hi : i < n) :
    rowMul (unitRow n i) B = row B i := by
  show ((List.range (B.headD []).length).map (Mat.col B)).map (fun c => Mat.dot (unitRow n i) c) = row B i
  rw [headD_eq_row, hB 0 (hBn ▸ h0), hBn, range_eq_rangeS, map_map']
  have hr : (row B i).length = n := by rw [hB i (hBn ▸ hi), hBn]
  have e : ∀ j, j < n → Mat.dot (unitRow n i) (Mat.col B j) = nth 0 (row B i) j := fun j _ => by
    rw [dot_eq_dotL, dotL_unitRow n i _ hi (by show n ≤ (B.map _).length; rw [length_map, hBn]; exact Nat.le_refl n)]
    exact nth_map_lt (fun r => nth 0 r j) [] 0 B i (hBn ▸ hi)
  calc (rangeS n).map (fun j => Mat.dot (unitRow n i) (Mat.col B j))
      = (rangeS n).map (fun j => nth 0 (row B i) j) := map_congr_rangeS n _ _ e
    _ = row B i := by rw [← hr]; exact map_nth_rangeS (row B i)
where
  map_congr_rangeS : ∀ (n : Nat) (f g : Nat → Ext p ν), (∀ j, j < n → f j = g j) → (rangeS n).map f = (rangeS n).map g
    | 0, _, _, _ => rfl
    | n + 1, f, g, h => by
      show (rangeS n ++ [n]).map f = (rangeS n ++ [n]).map g
      rw [map_append_single, map_append_single, map_congr_rangeS n f g (fun j hj => h j (Nat.lt_succ_of_lt hj)), h n (Nat.lt_succ_self n)]

theorem nth_beyond {α : Type} (d : α) : ∀ (l : List α) (i : Nat), l.length ≤ i → nth d l i = d
  | [], _, _ => rfl
  | _ :: _, 0, h => absurd h (Nat.not_succ_le_zero _)
  | _ :: l, i + 1, h => nth_beyond d l i (Nat.le_of_succ_le_succ h)

/-- A matrix with a zero row has determinant zero. -/
theorem det_zero_row (M : Mat p ν) (i : Nat) (hi : i < M.length) (h : ∀ c, nth 0 (row M i) c = 0) : det M = 0 := by
  have e : row M i = rsmul 0 (row M i) :=
    ext_nth 0 _ _ (by rw [length_rsmul]) fun c _ => by rw [nth_rsmul, zero_mul, h c]
  have hlen : M.length = M.length - 1 + 1 := length_form_one (Nat.lt_of_le_of_lt (Nat.zero_le i) hi)
  calc det M = det (setAt M i (rsmul 0 (row M i))) := by rw [← e, setAt_row_self M i hi]
    _ = 0 * det (setAt M i (row M i)) := det_setAt_smul (M.length - 1) M i 0 (row M i) hlen (by rw [← hlen]; exact hi)
    _ = 0 := zero_mul _

theorem nth_rowMul_zero (r : List (Ext p ν)) (B : Mat p ν) (h : ∀ c, nth 0 r c = 0) (c : Nat) : nth 0 (rowMul r B) c = 0 := by
  have e : r = rsmul 0 r := ext_nth 0 _ _ (by rw [length_rsmul]) fun c _ => by rw [nth_rsmul, zero_mul, h c]
  rw [e, rowMul_rsmul, nth_rsmul, zero_mul]

/-- `det (A · B) = det A · det B` for square matrices of the same size over `K`. -/
theorem det_mul {κ : Nat} {g : Shell p} (F : Frame p κ g) (hν : ¬IsSquare ν) (A B : Mat p ν) (hA : Square A) (hB : Square B)
    (hAB : A.length = B.length) : det (A * B) = det A * det B := by
  match hn : A.length with
  | 0 =>
    have hA0 : A = [] := match A, hn with | [], _ => rfl
    have hB0 : B = [] := match B, hAB.symm.trans hn with | [], _ => rfl
    rw [hA0, hB0]; show (1 : Ext p ν) = 1 * 1; exact (Ext.one_mul 1).symm
  | n + 1 =>
    have hn' : A.length = n + 1 := hn
    have hBn : B.length = n + 1 := hAB.symm.trans hn
    have h0 : 0 < n + 1 := Nat.succ_pos n
    obtain ⟨hv, hle, hdiag, hzero⟩ := gj_spec F hν (n + 1) (n + 1) 0 0 A hn' hA (Nat.le_refl 0) (Nat.zero_add _)
      (fun _ c _ _ hc => absurd hc (Nat.not_lt_zero c)) (fun _ c hc => absurd hc (Nat.not_lt_zero c))
    -- the end state D and the transported product
    have hDlen : (apply (gj (n + 1) (n + 1) 0 0 A).1 A).length = n + 1 := by rw [length_apply, hn']
    have hDsq : Square (apply (gj (n + 1) (n + 1) 0 0 A).1 A) := square_apply _ _ (by rw [hn']; exact hv) hA
    have hdetD : det (apply (gj (n + 1) (n + 1) 0 0 A).1 A) = det A := det_apply _ _ (by rw [hn']; exact hv) hA
    have hABsq : Square (A * B) := square_mul A B hB hAB (by rw [hBn]; exact h0)
    have hABlen : (A * B).length = n + 1 := by rw [length_mul, hn']
    have hdetAB : det (apply (gj (n + 1) (n + 1) 0 0 A).1 A * B) = det (A * B) := by
      rw [apply_mul _ _ _ (by rw [hn']; exact hv) hA]; exact det_apply _ _ (by rw [hABlen]; exact hv) hABsq
    match Nat.lt_or_ge (gj (n + 1) (n + 1) 0 0 A).2 (n + 1) with
    | Or.inr hge =>
      have hC := hdiag (Nat.le_antisymm hle hge)
      -- D = scaleRows d (ident) and D · B = scaleRows d B, with d the diagonal
      have hrow := row_of_invC _ hDlen hDsq hC
      have eD : apply (gj (n + 1) (n + 1) 0 0 A).1 A = scaleRows (fun i => E (apply (gj (n + 1) (n + 1) 0 0 A).1 A) i i) (Mat.ident (n + 1)) (n + 1) := by
        refine rows_ext _ _ (by rw [length_scaleRows, length_ident, hDlen]) fun i hi => ?_
        rw [hDlen] at hi
        rw [hrow i hi, row_scaleRows_lt _ _ _ i hi (by rw [length_ident]; exact hi), row_ident _ _ hi]
      have eDB : apply (gj (n + 1) (n + 1) 0 0 A).1 A * B = scaleRows (fun i => E (apply (gj (n + 1) (n + 1) 0 0 A).1 A) i i) B (n + 1) := by
        refine rows_ext _ _ (by rw [length_scaleRows, length_mul, hDlen, hBn]) fun i hi => ?_
        rw [length_mul, hDlen] at hi
        rw [row_mul _ _ i (by rw [hDlen]; exact hi), hrow i hi, rowMul_rsmul, rowMul_unitRow B hB hBn h0 i hi,
          row_scaleRows_lt _ _ _ i hi (by rw [hBn]; exact hi)]
      have h1 : det (apply (gj (n + 1) (n + 1) 0 0 A).1 A * B) =
          prodUpto (fun i => E (apply (gj (n + 1) (n + 1) 0 0 A).1 A) i i) (n + 1) * det B := by
        rw [eDB]; exact det_scaleRows _ _ _ (Nat.le_of_eq hBn.symm)
      have h2 : det (apply (gj (n + 1) (n + 1) 0 0 A).1 A) = prodUpto (fun i => E (apply (gj (n + 1) (n + 1) 0 0 A).1 A) i i) (n + 1) := by
        have := congrArg det eD
        rw [det_scaleRows _ _ _ (Nat.le_of_eq (length_ident (n + 1)).symm), det_ident, Ext.mul_one] at this
        exact this
      calc det (A * B) = det (apply (gj (n + 1) (n + 1) 0 0 A).1 A * B) := hdetAB.symm
        _ = prodUpto (fun i => E (apply (gj (n + 1) (n + 1) 0 0 A).1 A) i i) (n + 1) * det B := h1
        _ = det (apply (gj (n + 1) (n + 1) 0 0 A).1 A) * det B := by rw [h2]
        _ = det A * det B := by rw [hdetD]
    | Or.inl hlt =>
      have hAz := hzero hlt
      -- row n of D is zero: D and D · B are singular
      have hrow0 : ∀ c, nth 0 (row (apply (gj (n + 1) (n + 1) 0 0 A).1 A) n) c = 0 := fun c => by
        match Nat.lt_or_ge c (n + 1) with
        | Or.inl hc => exact hAz n c (Nat.le_of_lt_succ hlt) (Nat.lt_succ_self n) hc
        | Or.inr hc => exact nth_beyond _ _ _ (by rw [hDsq n (by rw [hDlen]; exact Nat.lt_succ_self n), hDlen]; exact hc)
      have hD0 : det (apply (gj (n + 1) (n + 1) 0 0 A).1 A) = 0 := det_zero_row _ n (by rw [hDlen]; exact Nat.lt_succ_self n) hrow0
      have hDB0 : det (apply (gj (n + 1) (n + 1) 0 0 A).1 A * B) = 0 :=
        det_zero_row _ n (by rw [length_mul, hDlen]; exact Nat.lt_succ_self n)
          (fun c => by rw [row_mul _ _ n (by rw [hDlen]; exact Nat.lt_succ_self n)]; exact nth_rowMul_zero _ B hrow0 c)
      rw [← hdetAB, hDB0, ← hdetD, hD0, zero_mul]

end FRC.Dirac.Det
