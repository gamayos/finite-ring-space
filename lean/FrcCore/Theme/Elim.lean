import FrcCore.Theme.Det
import FrcCore.Theme.Packed
/-!
# FrcCore.Theme.Elim — Gaussian elimination over the coefficient field (the operator theme)

The computation of the determinant of `Theme/Det`: the first-column lemma (`det M = M₀₀ · det (minor 0)` when the
heads below vanish), the clearing of the first column by iterated row additions with the pivot's inverse, the pivot
search, and `detG` with the row count as fuel, equal to `det` on square matrices over `K` (`detG_eq_det`), on the frame
with `ν` a nonsquare. The inverse of a nonzero residue is `x^(p−2)` (Fermat, `mul_invF`), the inverse in `K` the
conjugate over the norm (`mul_inv`), the norm nonzero by the anisotropy of the quadratic form. The kernel decides
determinants through `detG`: `n³` field operations where the expansion would take `n!`. `Theme/Cayley.lean` applies the kernel criterion
to the Cayley denominator `I − αH` of 8-dirac. No axioms.
-/
namespace FRC.Dirac.Det

open FRC FRC.Extension FRC.Dirac FRC.Dirac.Hermitian
open FRC.Dirac.Mat (nth)

variable {p : Nat} [Pos p] {ν : Shell p}

/-! ## The first column -/

/-- When every row below the first has head zero, the determinant is the first head times the first minor. -/
theorem det_first_col (M : Mat p ν) (hM : 0 < M.length) (h : ∀ i, 0 < i → i < M.length → head (row M i) = 0) :
    det M = head (row M 0) * det (minor M 0) := by
  rw [det_expand M hM, length_form_one hM, Nat.add_comm (M.length - 1) 1, ← sumFrom_split _ 1 (M.length - 1) 0]
  show term det M 0 + 0 + sumFrom (term det M) (M.length - 1) (0 + 1) = _
  rw [add_zero, show sumFrom (term det M) (M.length - 1) (0 + 1) = 0 by
    rw [← sumFrom_zero_fn (M.length - 1) (0 + 1)]
    exact sumFrom_congr _ _ fun j hj hj' => by
      unfold term
      rw [h j hj (by rw [length_form_one hM, Nat.add_comm]; exact hj'), mul_zero, zero_mul]]
  unfold term; rw [add_zero, show (sgn 0 : Ext p ν) = 1 from rfl, Ext.one_mul]

/-- A zero first column: the determinant vanishes. -/
theorem det_zero_col (M : Mat p ν) (hM : 0 < M.length) (h : ∀ i, i < M.length → head (row M i) = 0) : det M = 0 := by
  rw [det_first_col M hM fun i _ hi => h i hi, h 0 hM, zero_mul]

/-! ## Clearing the first column below the pivot -/

/-- Row `k` with `−(head k · ainv)` times row `0` added. -/
def clearRow (M : Mat p ν) (ainv : Ext p ν) (k : Nat) : Mat p ν :=
  setAt M k (radd (row M k) (rsmul (-(head (row M k) * ainv)) (row M 0)))

/-- Rows `1 … k` cleared in turn. -/
def clearUpto (ainv : Ext p ν) : Nat → Mat p ν → Mat p ν
  | 0, M => M
  | k + 1, M => clearRow (clearUpto ainv k M) ainv (k + 1)

theorem length_clearRow (M : Mat p ν) (ainv : Ext p ν) (k : Nat) : (clearRow M ainv k).length = M.length := length_setAt _ _ _
theorem length_clearUpto (ainv : Ext p ν) : ∀ (k : Nat) (M : Mat p ν), (clearUpto ainv k M).length = M.length
  | 0, _ => rfl
  | k + 1, M => (length_clearRow _ _ _).trans (length_clearUpto ainv k M)

theorem square_setAt (M : Mat p ν) (hS : Square M) (i : Nat) (r : List (Ext p ν)) (hr : r.length = M.length) :
    Square (setAt M i r) := fun j hj => by
  rw [length_setAt] at hj ⊢
  match Nat.decEq i j with
  | .isTrue e => subst e; rw [row_setAt_eq _ _ _ hj]; exact hr
  | .isFalse e => rw [row_setAt_ne _ _ _ _ e]; exact hS j hj

theorem square_clearRow (M : Mat p ν) (hS : Square M) (ainv : Ext p ν) (k : Nat) (hk : k < M.length) (h0 : 0 < M.length) :
    Square (clearRow M ainv k) :=
  square_setAt M hS k _ (by rw [length_radd _ _ (by rw [length_rsmul]; exact (hS k hk).trans (hS 0 h0).symm)]; exact hS k hk)

theorem square_clearUpto (ainv : Ext p ν) : ∀ (k : Nat) (M : Mat p ν), Square M → k < M.length → Square (clearUpto ainv k M)
  | 0, _, hS, _ => hS
  | k + 1, M, hS, hk =>
    square_clearRow _ (square_clearUpto ainv k M hS (Nat.lt_of_succ_lt hk)) ainv (k + 1)
      (by rw [length_clearUpto]; exact hk) (by rw [length_clearUpto]; exact Nat.lt_of_le_of_lt (Nat.zero_le _) hk)

/-- Clearing rows `1 … k` leaves the determinant unchanged. -/
theorem det_clearUpto (ainv : Ext p ν) : ∀ (k : Nat) (M : Mat p ν), Square M → k < M.length → det (clearUpto ainv k M) = det M
  | 0, _, _, _ => rfl
  | k + 1, M, hS, hk => by
    show det (clearRow (clearUpto ainv k M) ainv (k + 1)) = det M
    unfold clearRow
    rw [det_addRow _ (square_clearUpto ainv k M hS (Nat.lt_of_succ_lt hk)) (k + 1) 0 (Nat.succ_ne_zero k)
      (by rw [length_clearUpto]; exact hk) (by rw [length_clearUpto]; exact Nat.lt_of_le_of_lt (Nat.zero_le _) hk)]
    exact det_clearUpto ainv k M hS (Nat.lt_of_succ_lt hk)

/-- Rows beyond `k`, and row `0`, are untouched. -/
theorem row_clearUpto_of_lt (ainv : Ext p ν) : ∀ (k : Nat) (M : Mat p ν) (i : Nat), k < i → row (clearUpto ainv k M) i = row M i
  | 0, _, _, _ => rfl
  | k + 1, M, i, h => by
    show row (clearRow (clearUpto ainv k M) ainv (k + 1)) i = row M i
    unfold clearRow
    rw [row_setAt_ne _ _ _ _ (Nat.ne_of_lt h)]; exact row_clearUpto_of_lt ainv k M i (Nat.lt_of_succ_lt h)
theorem row_clearUpto_zero (ainv : Ext p ν) : ∀ (k : Nat) (M : Mat p ν), row (clearUpto ainv k M) 0 = row M 0
  | 0, _ => rfl
  | k + 1, M => by
    show row (clearRow (clearUpto ainv k M) ainv (k + 1)) 0 = row M 0
    unfold clearRow
    rw [row_setAt_ne _ _ _ _ (Nat.succ_ne_zero k)]; exact row_clearUpto_zero ainv k M

/-- With `ainv` the inverse of the first head, the cleared rows have head zero. -/
theorem head_clearUpto (ainv : Ext p ν) (M : Mat p ν) (hS : Square M) (ha : head (row M 0) * ainv = 1) :
    ∀ (k : Nat), k < M.length → ∀ i, 0 < i → i ≤ k → head (row (clearUpto ainv k M) i) = 0
  | 0, _, _, hi, hik => absurd (Nat.lt_of_lt_of_le hi hik) (Nat.lt_irrefl 0)
  | k + 1, hk, i, hi, hik => by
    show head (row (clearRow (clearUpto ainv k M) ainv (k + 1)) i) = 0
    unfold clearRow
    match Nat.decEq (k + 1) i with
    | .isTrue e =>
      subst e
      rw [row_setAt_eq _ _ _ (by rw [length_clearUpto]; exact hk), row_clearUpto_zero,
        row_clearUpto_of_lt ainv k M (k + 1) (Nat.lt_succ_self k),
        head_radd _ _ (by rw [length_rsmul]; exact (hS (k + 1) hk).trans (hS 0 (Nat.lt_of_le_of_lt (Nat.zero_le _) hk)).symm),
        head_rsmul, ← Hermitian.neg_mul, Ext.mul_assoc, Ext.mul_comm ainv, ha, Ext.mul_one, add_neg]
    | .isFalse e =>
      rw [row_setAt_ne _ _ _ _ e]
      exact head_clearUpto ainv M hS ha k (Nat.lt_of_succ_lt hk) i hi (Nat.lt_of_le_of_ne hik (Ne.symm e) |> Nat.le_of_lt_succ)

/-! ## Inverses on the frame -/

open FRC.Shell (Frame)
open FRC.Shell.Frame (IsSquare aniso_tx)

/-- Powers by repeated squaring, with fuel: `powBin a f n = a ^ n` once `f ≥ log₂ n` (`powBin_eq` for every `f`), and the
kernel unfolds `log₂ n` levels where `Shell.pow` unfolds `n`. -/
def powBin : Shell p → Nat → Nat → Shell p
  | a, 0, n => a ^ n
  | _, _ + 1, 0 => 1
  | a, f + 1, n + 1 => (if (n + 1) % 2 = 1 then a else 1) * powBin (a * a) f ((n + 1) / 2)

theorem lt_two_cases : ∀ r : Nat, r < 2 → r = 0 ∨ r = 1
  | 0, _ => Or.inl rfl
  | 1, _ => Or.inr rfl
  | _ + 2, h => absurd h (Nat.not_lt_of_le (Nat.le_add_left 2 _))

theorem pow_two' (a : Shell p) : a ^ 2 = a * a := by rw [Shell.pow_succ, Shell.pow_one]

theorem powBin_eq (a : Shell p) : ∀ (f n : Nat), powBin a f n = a ^ n
  | 0, _ => rfl
  | _ + 1, 0 => rfl
  | f + 1, n + 1 => by
    show (if (n + 1) % 2 = 1 then a else 1) * powBin (a * a) f ((n + 1) / 2) = a ^ (n + 1)
    rw [powBin_eq (a * a) f, ← pow_two', ← Shell.pow_mul]
    have e := FRC.Dirac.Packed.div_add_mod' 2 (by decide) (n + 1)
    match lt_two_cases _ (Nat.mod_lt (n + 1) (by decide)) with
    | Or.inl h0 =>
      rw [h0, ite_eq_right (by decide), Shell.one_mul]; rw [h0, Nat.add_zero] at e; exact congrArg (a ^ ·) e.symm
    | Or.inr h1 =>
      rw [h1, ite_eq_left rfl, Shell.mul_comm, ← Shell.pow_succ]; rw [h1] at e; exact congrArg (a ^ ·) e.symm

/-- The inverse of a nonzero residue, `x^(p−2)` (Fermat), computed by repeated squaring; `0` at `0`. -/
def invF (x : Shell p) : Shell p := powBin x p (p - 2)

theorem invF_eq_pow (x : Shell p) : invF x = x ^ (p - 2) := powBin_eq x p (p - 2)

theorem mul_invF {κ : Nat} {g : Shell p} (F : Frame p κ g) {x : Shell p} (hx : x ≠ 0) : x * invF x = 1 := by
  rw [invF_eq_pow]
  obtain ⟨y, hy⟩ := F.exists_inv hx
  have h2 : 2 ≤ p := F.one_lt_p
  have h1 : p - 2 + 1 = p - 1 := by
    have := FRC.Nat.sub_add_cancel h2
    calc p - 2 + 1 = p - 2 + 2 - 1 := rfl
      _ = p - 1 := by rw [this]
  have hp : p - 1 + 1 = p := FRC.Nat.sub_add_cancel (Nat.le_of_lt F.one_lt_p)
  show x * x ^ (p - 2) = 1
  rw [Shell.mul_comm, ← Shell.pow_succ, h1, ← Shell.mul_one (x ^ (p - 1)), ← hy, ← Shell.mul_assoc, ← Shell.pow_succ,
    hp, F.fermat x, hy]

/-- The inverse in `K`: the conjugate over the norm. -/
def inv (z : Ext p ν) : Ext p ν := Ext.conj z * Ext.ofShell (invF (Ext.norm z))

theorem norm_ne_zero {κ : Nat} {g : Shell p} (F : Frame p κ g) (hν : ¬IsSquare ν) {z : Ext p ν} (hz : z ≠ 0) :
    Ext.norm z ≠ 0 := fun h => by
  have e : z.re * z.re = ν * (z.im * z.im) := by
    have := Shell.eq_neg_of_add_eq_zero h
    rw [Shell.neg_neg] at this; exact this
  obtain ⟨hi, hr⟩ := aniso_tx F hν e
  exact hz (Ext.ext hr hi)

theorem mul_inv {κ : Nat} {g : Shell p} (F : Frame p κ g) (hν : ¬IsSquare ν) {z : Ext p ν} (hz : z ≠ 0) : z * inv z = 1 := by
  show z * (Ext.conj z * Ext.ofShell (invF (Ext.norm z))) = 1
  rw [← Ext.mul_assoc, Ext.mul_conj, Ext.ofShell_mul, mul_invF F (norm_ne_zero F hν hz)]; rfl

/-! ## The pivot and Gaussian elimination -/

/-- The least row index `≥ i` with a nonzero head, within `f` rows. -/
def pivotAux (M : Mat p ν) : Nat → Nat → Option Nat
  | 0, _ => none
  | f + 1, i => if head (row M i) = 0 then pivotAux M f (i + 1) else some i

theorem pivotAux_none (M : Mat p ν) : ∀ (f i : Nat), pivotAux M f i = none → ∀ j, i ≤ j → j < i + f → head (row M j) = 0
  | 0, _, _, _, hj, hj' => absurd (Nat.lt_of_le_of_lt hj hj') (Nat.lt_irrefl _)
  | f + 1, i, h, j, hj, hj' => by
    unfold pivotAux at h
    match decEq (head (row M i)) 0 with
    | .isTrue e =>
      rw [ite_eq_left e] at h
      match Nat.decEq i j with
      | .isTrue e' => subst e'; exact e
      | .isFalse e' =>
        exact pivotAux_none M f (i + 1) h j (Nat.lt_of_le_of_ne hj e') (Nat.add_right_comm i 1 f ▸ hj')
    | .isFalse e => rw [ite_eq_right e] at h; exact nomatch h

theorem pivotAux_some (M : Mat p ν) : ∀ (f i k : Nat), pivotAux M f i = some k →
    i ≤ k ∧ k < i + f ∧ head (row M k) ≠ 0 ∧ ∀ j, i ≤ j → j < k → head (row M j) = 0
  | 0, _, _, h => nomatch h
  | f + 1, i, k, h => by
    unfold pivotAux at h
    match decEq (head (row M i)) 0 with
    | .isTrue e =>
      rw [ite_eq_left e] at h
      obtain ⟨h1, h2, h3, h4⟩ := pivotAux_some M f (i + 1) k h
      refine ⟨Nat.le_of_succ_le h1, Nat.add_right_comm i 1 f ▸ h2, h3, fun j hj hjk => ?_⟩
      match Nat.decEq i j with
      | .isTrue e' => subst e'; exact e
      | .isFalse e' => exact h4 j (Nat.lt_of_le_of_ne hj e') hjk
    | .isFalse e =>
      rw [ite_eq_right e] at h
      cases h
      exact ⟨Nat.le_refl i, Nat.lt_add_of_pos_right (Nat.succ_pos f), e,
        fun j hj hjk => absurd (Nat.lt_of_le_of_lt hj hjk) (Nat.lt_irrefl _)⟩

/-- The matrix with row `k` added to row `0` when `k ≠ 0`, so that its first head is the pivot. -/
def pivotFix (M : Mat p ν) : Nat → Mat p ν
  | 0 => M
  | k + 1 => setAt M 0 (radd (row M 0) (rsmul 1 (row M (k + 1))))

/-- Gaussian elimination along the first column, the row count as fuel: the determinant with `n³` operations. -/
def detG : Nat → Mat p ν → Ext p ν
  | 0, _ => 1
  | n + 1, M =>
    match pivotAux M (n + 1) 0 with
    | none => 0
    | some k =>
      let M' := pivotFix M k
      let a := head (row M' 0)
      a * detG n (minor (clearUpto (inv a) n M') 0)

theorem length_tail_of_pos {α : Type} : ∀ (l : List α), 0 < l.length → l.tail.length + 1 = l.length
  | [], h => absurd h (Nat.lt_irrefl 0)
  | _ :: _, _ => rfl

theorem square_minor (M : Mat p ν) (hS : Square M) (j : Nat) (hj : j < M.length) : Square (minor M j) := fun i hi => by
  have hl := length_minor M j hj
  have hiM : i + 1 < M.length := by rw [← hl]; exact Nat.succ_lt_succ hi
  match Nat.decLt i j with
  | .isTrue hij =>
    rw [row_minor_lt M j i hij]
    exact Nat.succ.inj ((length_tail_of_pos _ (by rw [hS i (Nat.lt_of_succ_lt hiM)]; exact Nat.lt_of_le_of_lt (Nat.zero_le _) hiM)).trans
      ((hS i (Nat.lt_of_succ_lt hiM)).trans hl.symm))
  | .isFalse hij =>
    rw [row_minor_ge M j i (Nat.le_of_not_lt hij)]
    exact Nat.succ.inj ((length_tail_of_pos _ (by rw [hS (i + 1) hiM]; exact Nat.lt_of_le_of_lt (Nat.zero_le _) hiM)).trans
      ((hS (i + 1) hiM).trans hl.symm))

theorem length_pivotFix (M : Mat p ν) : ∀ k, (pivotFix M k).length = M.length
  | 0 => rfl
  | _ + 1 => length_setAt _ _ _

theorem square_pivotFix (M : Mat p ν) (hS : Square M) : ∀ k, k < M.length → Square (pivotFix M k)
  | 0, _ => hS
  | k + 1, hk =>
    square_setAt M hS 0 _ (by
      rw [length_radd _ _ (by rw [length_rsmul]; exact (hS 0 (Nat.lt_of_le_of_lt (Nat.zero_le _) hk)).trans (hS (k + 1) hk).symm)]
      exact hS 0 (Nat.lt_of_le_of_lt (Nat.zero_le _) hk))

theorem det_pivotFix (M : Mat p ν) (hS : Square M) : ∀ k, k < M.length → det (pivotFix M k) = det M
  | 0, _ => rfl
  | k + 1, hk => det_addRow M hS 0 (k + 1) (Nat.succ_ne_zero k).symm (Nat.lt_of_le_of_lt (Nat.zero_le _) hk) hk 1

theorem head_pivotFix (M : Mat p ν) (hS : Square M) : ∀ k, k < M.length → (∀ j, j < k → head (row M j) = 0) →
    head (row (pivotFix M k) 0) = head (row M k)
  | 0, _, _ => rfl
  | k + 1, hk, h0 => by
    show head (row (setAt M 0 _) 0) = _
    rw [row_setAt_eq _ _ _ (Nat.lt_of_le_of_lt (Nat.zero_le _) hk),
      head_radd _ _ (by rw [length_rsmul]; exact (hS 0 (Nat.lt_of_le_of_lt (Nat.zero_le _) hk)).trans (hS (k + 1) hk).symm),
      head_rsmul, h0 0 (Nat.succ_pos k), zero_add, Ext.one_mul]

/-- The elimination computes the determinant. -/
theorem detG_eq_det {κ : Nat} {g : Shell p} (F : Frame p κ g) (hν : ¬IsSquare ν) :
    ∀ (n : Nat) (M : Mat p ν), Square M → M.length = n → detG n M = det M
  | 0, [], _, _ => rfl
  | 0, _ :: _, _, h => absurd h (Nat.succ_ne_zero _)
  | n + 1, M, hS, hM => by
    have hpos : 0 < M.length := hM ▸ Nat.succ_pos n
    show (match pivotAux M (n + 1) 0 with
      | none => 0
      | some k => head (row (pivotFix M k) 0) * detG n (minor (clearUpto (inv (head (row (pivotFix M k) 0))) n (pivotFix M k)) 0)) = det M
    match hpiv : pivotAux M (n + 1) 0 with
    | none =>
      show (0 : Ext p ν) = det M
      exact (det_zero_col M hpos fun i hi => pivotAux_none M (n + 1) 0 hpiv i (Nat.zero_le i) (by rw [Nat.zero_add, ← hM]; exact hi)).symm
    | some k =>
      show head (row (pivotFix M k) 0) * detG n (minor (clearUpto (inv (head (row (pivotFix M k) 0))) n (pivotFix M k)) 0) = det M
      obtain ⟨_, hk, hk0, hleast⟩ := pivotAux_some M (n + 1) 0 k hpiv
      have hkM : k < M.length := by rw [hM]; exact Nat.lt_of_lt_of_eq hk (Nat.zero_add _)
      have hS' : Square (pivotFix M k) := square_pivotFix M hS k hkM
      have hlen' : (pivotFix M k).length = n + 1 := (length_pivotFix M k).trans hM
      have ha : head (row (pivotFix M k) 0) ≠ 0 := by
        rw [head_pivotFix M hS k hkM fun j hj => hleast j (Nat.zero_le j) hj]; exact hk0
      have hinv := mul_inv F hν ha
      have hn : n < (pivotFix M k).length := by rw [hlen']; exact Nat.lt_succ_self n
      have hC : Square (clearUpto (inv (head (row (pivotFix M k) 0))) n (pivotFix M k)) := square_clearUpto _ n _ hS' hn
      have hCl : (clearUpto (inv (head (row (pivotFix M k) 0))) n (pivotFix M k)).length = n + 1 := (length_clearUpto _ _ _).trans hlen'
      rw [detG_eq_det F hν n _ (square_minor _ hC 0 (hCl ▸ Nat.succ_pos n))
        (Nat.succ.inj (show (minor _ 0).length + 1 = n + 1 by rw [length_minor _ 0 (hCl ▸ Nat.succ_pos n)]; exact hCl)),
        ← det_pivotFix M hS k hkM, ← det_clearUpto (inv (head (row (pivotFix M k) 0))) n _ hS' hn,
        det_first_col _ (hCl ▸ Nat.succ_pos n) (fun i hi hi' => head_clearUpto _ _ hS' hinv n hn i hi
          (Nat.le_of_lt_succ (Nat.lt_of_lt_of_eq hi' hCl))), row_clearUpto_zero]

/-! ## The kernel: the determinant vanishes exactly on the singular matrices -/

/-- The dot product of two lists (the shorter one decides). -/
def dotL : List (Ext p ν) → List (Ext p ν) → Ext p ν
  | [], _ => 0
  | _ :: _, [] => 0
  | a :: r, x :: v => a * x + dotL r v

/-- `v` lies in the kernel of `M`: every row is orthogonal to it. -/
def InKer (M : Mat p ν) (v : List (Ext p ν)) : Prop := ∀ j, dotL (row M j) v = 0
/-- The zero vector, entrywise. -/
def IsZero (v : List (Ext p ν)) : Prop := ∀ i, nth 0 v i = 0

theorem dotL_nil_right : ∀ r : List (Ext p ν), dotL r [] = 0
  | [] => rfl
  | _ :: _ => rfl

theorem dotL_radd : ∀ (r s v : List (Ext p ν)), r.length = s.length → dotL (radd r s) v = dotL r v + dotL s v
  | [], [], _, _ => (add_zero _).symm
  | [], _ :: _, _, h => absurd h (Nat.ne_of_lt (Nat.succ_pos _))
  | _ :: _, [], _, h => absurd h (Nat.ne_of_gt (Nat.succ_pos _))
  | _ :: _, _ :: _, [], _ => (add_zero _).symm
  | a :: r, b :: s, x :: v, h => by
    show (a + b) * x + dotL (radd r s) v = a * x + dotL r v + (b * x + dotL s v)
    rw [dotL_radd r s v (Nat.succ.inj h), add_mul, add_add_add_comm]

theorem dotL_rsmul (c : Ext p ν) : ∀ (r v : List (Ext p ν)), dotL (rsmul c r) v = c * dotL r v
  | [], _ => (mul_zero c).symm
  | _ :: _, [] => (mul_zero c).symm
  | a :: r, x :: v => by
    show c * a * x + dotL (rsmul c r) v = c * (a * x + dotL r v)
    rw [dotL_rsmul c r v, mul_add, Ext.mul_assoc]

theorem dotL_cons_head : ∀ (r : List (Ext p ν)) (x : Ext p ν) (w : List (Ext p ν)), 0 < r.length →
    dotL r (x :: w) = head r * x + dotL r.tail w
  | [], _, _, h => absurd h (Nat.lt_irrefl 0)
  | _ :: _, _, _, _ => rfl

theorem inKer_setAt_iff (M : Mat p ν) (i k : Nat) (hik : i ≠ k) (c : Ext p ν) (v : List (Ext p ν)) (hi : i < M.length)
    (hl : (row M i).length = (row M k).length) :
    InKer (setAt M i (radd (row M i) (rsmul c (row M k)))) v ↔ InKer M v := by
  constructor
  · intro h j
    match Nat.decEq i j with
    | .isTrue e =>
      subst e
      have hk := h k
      have hi' := h i
      rw [row_setAt_eq _ _ _ hi, dotL_radd _ _ _ (by rw [length_rsmul]; exact hl), dotL_rsmul] at hi'
      rw [row_setAt_ne _ _ _ _ hik] at hk
      rw [hk, mul_zero, add_zero] at hi'; exact hi'
    | .isFalse e => have := h j; rw [row_setAt_ne _ _ _ _ e] at this; exact this
  · intro h j
    match Nat.decEq i j with
    | .isTrue e =>
      subst e
      rw [row_setAt_eq _ _ _ hi, dotL_radd _ _ _ (by rw [length_rsmul]; exact hl), dotL_rsmul, h i, h k, mul_zero, add_zero]
    | .isFalse e => rw [row_setAt_ne _ _ _ _ e]; exact h j

theorem inKer_clearUpto_iff (ainv : Ext p ν) : ∀ (k : Nat) (M : Mat p ν), Square M → k < M.length → ∀ v,
    (InKer (clearUpto ainv k M) v ↔ InKer M v)
  | 0, _, _, _, _ => Iff.rfl
  | k + 1, M, hS, hk, v =>
    have hS' := square_clearUpto ainv k M hS (Nat.lt_of_succ_lt hk)
    have hk' : k + 1 < (clearUpto ainv k M).length := by rw [length_clearUpto]; exact hk
    have h0' : 0 < (clearUpto ainv k M).length := Nat.lt_of_le_of_lt (Nat.zero_le _) hk'
    by
      show InKer (clearRow (clearUpto ainv k M) ainv (k + 1)) v ↔ InKer M v
      unfold clearRow
      exact (inKer_setAt_iff _ (k + 1) 0 (Nat.succ_ne_zero k) _ v hk' ((hS' _ hk').trans (hS' 0 h0').symm)).trans
        (inKer_clearUpto_iff ainv k M hS (Nat.lt_of_succ_lt hk) v)

theorem inKer_pivotFix_iff (M : Mat p ν) (hS : Square M) : ∀ (k : Nat), k < M.length → ∀ v, (InKer (pivotFix M k) v ↔ InKer M v)
  | 0, _, _ => Iff.rfl
  | k + 1, hk, v =>
    inKer_setAt_iff M 0 (k + 1) (Nat.succ_ne_zero k).symm 1 v (Nat.lt_of_le_of_lt (Nat.zero_le _) hk)
      ((hS 0 (Nat.lt_of_le_of_lt (Nat.zero_le _) hk)).trans (hS (k + 1) hk).symm)

theorem row_beyond (M : Mat p ν) : ∀ (j : Nat), M.length ≤ j → row M j = []
  | _, _ => by
    unfold row
    exact aux M _ ‹_›
where
  aux : ∀ (l : Mat p ν) (j : Nat), l.length ≤ j → nth [] l j = []
    | [], _, _ => rfl
    | _ :: _, 0, h => absurd h (Nat.not_succ_le_zero _)
    | _ :: l, j + 1, h => aux l j (Nat.le_of_succ_le_succ h)

theorem dotL_zero_right : ∀ (r w : List (Ext p ν)), IsZero w → dotL r w = 0
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | a :: r, x :: w, h => by
    show a * x + dotL r w = 0
    rw [show x = 0 from h 0, mul_zero, dotL_zero_right r w fun i => h (i + 1), add_zero]

/-- The kernel of a matrix whose first column is `(a, 0, …, 0)`: the first row's equation and the kernel of the minor. -/
theorem inKer_cons_iff (C : Mat p ν) (hS : Square C) (hC : 0 < C.length)
    (hz : ∀ i, 0 < i → i < C.length → head (row C i) = 0) (x : Ext p ν) (w : List (Ext p ν)) :
    InKer C (x :: w) ↔ (head (row C 0) * x + dotL (row C 0).tail w = 0 ∧ InKer (minor C 0) w) := by
  have hr0 : 0 < (row C 0).length := by rw [hS 0 hC]; exact hC
  constructor
  · intro h
    refine ⟨by rw [← dotL_cons_head _ _ _ hr0]; exact h 0, fun j => ?_⟩
    match Nat.decLt (j + 1) C.length with
    | .isTrue hj =>
      have hj' := h (j + 1)
      rw [dotL_cons_head _ _ _ (by rw [hS (j + 1) hj]; exact hC), hz (j + 1) (Nat.succ_pos j) hj, zero_mul, zero_add] at hj'
      rw [row_minor_ge C 0 j (Nat.zero_le j)]; exact hj'
    | .isFalse hj =>
      rw [row_beyond (minor C 0) j (by
        have := length_minor C 0 hC
        exact Nat.le_of_succ_le_succ (show (minor C 0).length + 1 ≤ j + 1 by rw [this]; exact Nat.le_of_not_lt hj))]
      rfl
  · intro ⟨h0, hm⟩ j
    match j with
    | 0 => rw [dotL_cons_head _ _ _ hr0]; exact h0
    | j + 1 =>
      match Nat.decLt (j + 1) C.length with
      | .isTrue hj =>
        rw [dotL_cons_head _ _ _ (by rw [hS (j + 1) hj]; exact hC), hz (j + 1) (Nat.succ_pos j) hj, zero_mul, zero_add,
          ← row_minor_ge C 0 j (Nat.zero_le j)]
        exact hm j
      | .isFalse hj => rw [row_beyond C (j + 1) (Nat.le_of_not_lt hj)]; rfl

/-- Whether every entry vanishes, decided. -/
def allZero : List (Ext p ν) → Bool
  | [] => true
  | x :: w => decide (x = 0) && allZero w

theorem isZero_of_allZero : ∀ w : List (Ext p ν), allZero w = true → IsZero w
  | [], _, _ => rfl
  | x :: w, h, i => by
    have hx : decide (x = 0) = true := FRC.Shell.Frame.and_true_left h
    have hw := isZero_of_allZero w (FRC.Shell.Frame.and_true_right h)
    match i with
    | 0 => exact of_decide_eq_true hx
    | i + 1 => exact hw i

theorem not_isZero_of_allZero_false : ∀ w : List (Ext p ν), allZero w = false → ¬ IsZero w
  | [], h, _ => nomatch h
  | x :: w, h, hz => by
    match hd : decide (x = 0) with
    | true =>
      have hw : allZero w = false := by
        unfold allZero at h; rw [hd] at h; exact h
      exact not_isZero_of_allZero_false w hw fun i => hz (i + 1)
    | false => exact of_decide_eq_false hd (hz 0)

theorem mul_left_cancel_zero {κ : Nat} {g : Shell p} (F : Frame p κ g) (hν : ¬IsSquare ν) {a y : Ext p ν} (ha : a ≠ 0)
    (h : a * y = 0) : y = 0 := by
  rw [← Ext.one_mul y, ← mul_inv F hν ha, Ext.mul_comm a, Ext.mul_assoc, h, mul_zero]

theorem ext_one_ne_zero {κ : Nat} {g : Shell p} (F : Frame p κ g) : (1 : Ext p ν) ≠ 0 := fun h => F.one_ne_zero (Ext.re_congr h)

/-- A nontrivial kernel vector forces the determinant to vanish. -/
theorem det_eq_zero_of_inKer {κ : Nat} {g : Shell p} (F : Frame p κ g) (hν : ¬IsSquare ν) :
    ∀ (n : Nat) (M : Mat p ν), Square M → M.length = n → ∀ v : List (Ext p ν), v.length = n → InKer M v → ¬ IsZero v → det M = 0
  | 0, _, _, _, [], _, _, hnz => absurd (fun _ => rfl) hnz
  | 0, _, _, _, _ :: _, hv, _, _ => absurd hv (Nat.succ_ne_zero _)
  | n + 1, M, hS, hM, v, hv, hker, hnz => by
    have hpos : 0 < M.length := hM ▸ Nat.succ_pos n
    match hpiv : pivotAux M (n + 1) 0 with
    | none => exact det_zero_col M hpos fun i hi => pivotAux_none M (n + 1) 0 hpiv i (Nat.zero_le i) (by rw [Nat.zero_add, ← hM]; exact hi)
    | some k =>
      obtain ⟨_, hk, hk0, hleast⟩ := pivotAux_some M (n + 1) 0 k hpiv
      have hkM : k < M.length := by rw [hM]; exact Nat.lt_of_lt_of_eq hk (Nat.zero_add _)
      have hS' : Square (pivotFix M k) := square_pivotFix M hS k hkM
      have hlen' : (pivotFix M k).length = n + 1 := (length_pivotFix M k).trans hM
      have ha : head (row (pivotFix M k) 0) ≠ 0 := by
        rw [head_pivotFix M hS k hkM fun j hj => hleast j (Nat.zero_le j) hj]; exact hk0
      have hinv := mul_inv F hν ha
      have hn : n < (pivotFix M k).length := by rw [hlen']; exact Nat.lt_succ_self n
      let C := clearUpto (inv (head (row (pivotFix M k) 0))) n (pivotFix M k)
      have hC : Square C := square_clearUpto _ n _ hS' hn
      have hCl : C.length = n + 1 := (length_clearUpto _ _ _).trans hlen'
      have hCpos : 0 < C.length := hCl ▸ Nat.succ_pos n
      have hz : ∀ i, 0 < i → i < C.length → head (row C i) = 0 := fun i hi hi' =>
        head_clearUpto _ _ hS' hinv n hn i hi (Nat.le_of_lt_succ (Nat.lt_of_lt_of_eq hi' hCl))
      have hkerC : InKer C v := (inKer_clearUpto_iff _ n _ hS' hn v).mpr ((inKer_pivotFix_iff M hS k hkM v).mpr hker)
      have hdet : det M = head (row C 0) * det (minor C 0) := by
        rw [← det_pivotFix M hS k hkM, ← det_clearUpto (inv (head (row (pivotFix M k) 0))) n _ hS' hn]
        exact det_first_col C hCpos hz
      have hhead : head (row C 0) = head (row (pivotFix M k) 0) := by rw [row_clearUpto_zero]
      match v, hv with
      | x :: w, hv =>
        obtain ⟨h0, hm⟩ := (inKer_cons_iff C hC hCpos hz x w).mp hkerC
        match hw : allZero w with
        | false =>
          rw [hdet, det_eq_zero_of_inKer F hν n (minor C 0) (square_minor C hC 0 hCpos)
            (Nat.succ.inj (show (minor C 0).length + 1 = n + 1 by rw [length_minor C 0 hCpos]; exact hCl))
            w (Nat.succ.inj hv) hm (not_isZero_of_allZero_false w hw), mul_zero]
        | true =>
          have hw' := isZero_of_allZero w hw
          rw [dotL_zero_right _ _ hw', add_zero, hhead] at h0
          have hx : x = 0 := mul_left_cancel_zero F hν ha h0
          exact absurd (fun i => match i with | 0 => hx | i + 1 => hw' i) hnz

/-- A vanishing determinant yields a nontrivial kernel vector. -/
theorem exists_inKer_of_det_eq_zero {κ : Nat} {g : Shell p} (F : Frame p κ g) (hν : ¬IsSquare ν) :
    ∀ (n : Nat) (M : Mat p ν), Square M → M.length = n → det M = 0 → ∃ v : List (Ext p ν), v.length = n ∧ ¬ IsZero v ∧ InKer M v
  | 0, [], _, _, h => absurd h (ext_one_ne_zero F)
  | 0, _ :: _, _, hM, _ => absurd hM (Nat.succ_ne_zero _)
  | n + 1, M, hS, hM, hdet0 => by
    have hpos : 0 < M.length := hM ▸ Nat.succ_pos n
    match hpiv : pivotAux M (n + 1) 0 with
    | none =>
      have hz : ∀ i, i < M.length → head (row M i) = 0 := fun i hi =>
        pivotAux_none M (n + 1) 0 hpiv i (Nat.zero_le i) (by rw [Nat.zero_add, ← hM]; exact hi)
      refine ⟨1 :: List.replicate n 0, congrArg (· + 1) (length_replicate n), fun h => ext_one_ne_zero F (h 0), fun j => ?_⟩
      match Nat.decLt j M.length with
      | .isTrue hj =>
        rw [dotL_cons_head _ _ _ (by rw [hS j hj]; exact hpos), hz j hj, zero_mul, zero_add]
        exact dotL_zero_right _ _ (isZero_replicate n)
      | .isFalse hj => rw [row_beyond M j (Nat.le_of_not_lt hj)]; rfl
    | some k =>
      obtain ⟨_, hk, hk0, hleast⟩ := pivotAux_some M (n + 1) 0 k hpiv
      have hkM : k < M.length := by rw [hM]; exact Nat.lt_of_lt_of_eq hk (Nat.zero_add _)
      have hS' : Square (pivotFix M k) := square_pivotFix M hS k hkM
      have hlen' : (pivotFix M k).length = n + 1 := (length_pivotFix M k).trans hM
      have ha : head (row (pivotFix M k) 0) ≠ 0 := by
        rw [head_pivotFix M hS k hkM fun j hj => hleast j (Nat.zero_le j) hj]; exact hk0
      have hinv := mul_inv F hν ha
      have hn : n < (pivotFix M k).length := by rw [hlen']; exact Nat.lt_succ_self n
      let C := clearUpto (inv (head (row (pivotFix M k) 0))) n (pivotFix M k)
      have hC : Square C := square_clearUpto _ n _ hS' hn
      have hCl : C.length = n + 1 := (length_clearUpto _ _ _).trans hlen'
      have hCpos : 0 < C.length := hCl ▸ Nat.succ_pos n
      have hz : ∀ i, 0 < i → i < C.length → head (row C i) = 0 := fun i hi hi' =>
        head_clearUpto _ _ hS' hinv n hn i hi (Nat.le_of_lt_succ (Nat.lt_of_lt_of_eq hi' hCl))
      have hhead : head (row C 0) = head (row (pivotFix M k) 0) := by rw [row_clearUpto_zero]
      have hdet : det M = head (row C 0) * det (minor C 0) := by
        rw [← det_pivotFix M hS k hkM, ← det_clearUpto (inv (head (row (pivotFix M k) 0))) n _ hS' hn]
        exact det_first_col C hCpos hz
      have hminor : det (minor C 0) = 0 := by
        rw [hdet, hhead] at hdet0; exact mul_left_cancel_zero F hν ha hdet0
      obtain ⟨w, hwl, hwnz, hwk⟩ := exists_inKer_of_det_eq_zero F hν n (minor C 0) (square_minor C hC 0 hCpos)
        (Nat.succ.inj (show (minor C 0).length + 1 = n + 1 by rw [length_minor C 0 hCpos]; exact hCl)) hminor
      let x : Ext p ν := -(inv (head (row (pivotFix M k) 0)) * dotL (row C 0).tail w)
      refine ⟨x :: w, congrArg (· + 1) hwl, fun h => hwnz fun i => h (i + 1), ?_⟩
      refine (inKer_pivotFix_iff M hS k hkM _).mp ((inKer_clearUpto_iff (inv (head (row (pivotFix M k) 0))) n _ hS' hn _).mp ?_)
      refine (inKer_cons_iff C hC hCpos hz x w).mpr ⟨?_, hwk⟩
      show head (row C 0) * -(inv (head (row (pivotFix M k) 0)) * dotL (row C 0).tail w) + dotL (row C 0).tail w = 0
      rw [hhead, ← Hermitian.mul_neg, ← Ext.mul_assoc, hinv, Ext.one_mul, neg_add]
where
  isZero_replicate : ∀ n : Nat, IsZero (List.replicate n (0 : Ext p ν))
    | 0, _ => rfl
    | n + 1, 0 => rfl
    | n + 1, i + 1 => isZero_replicate n i
  length_replicate : ∀ n : Nat, (List.replicate n (0 : Ext p ν)).length = n
    | 0 => rfl
    | n + 1 => congrArg (· + 1) (length_replicate n)

/-- The determinant vanishes exactly on the singular matrices. -/
theorem det_eq_zero_iff {κ : Nat} {g : Shell p} (F : Frame p κ g) (hν : ¬IsSquare ν) (M : Mat p ν) (hS : Square M) :
    det M = 0 ↔ ∃ v : List (Ext p ν), v.length = M.length ∧ ¬ IsZero v ∧ InKer M v :=
  ⟨exists_inKer_of_det_eq_zero F hν M.length M hS rfl,
   fun ⟨v, hv, hnz, hker⟩ => det_eq_zero_of_inKer F hν M.length M hS rfl v hv hker hnz⟩

/-! ## Decided -/

/-- `I − kwH` for the Hermitian `H = [[0, w], [−w, 0]]`. -/
def skewCayley (ν : Shell p) (k : Shell p) : Mat p ν :=
  let α : Ext p ν := ⟨0, k⟩
  let w : Ext p ν := ⟨0, 1⟩
  [[1, -(α * w)], [α * w, 1]]

/-- [value] — on `𝔽₁₃` (`ν = 2`): the elimination and the expansion agree on `det(I − kwH) = 1 + k²ν²` for every `k`, and
the kernel criterion reads off the two singular parameters `k = 4, 9`. -/
theorem skew_det_values :
    (∀ k : Shell 13, detG 2 (skewCayley 2 k) = 1 + Ext.ofShell (k * 2 * (k * 2))) ∧
    (∀ k : Shell 13, det (skewCayley 2 k) = 1 + Ext.ofShell (k * 2 * (k * 2))) ∧
    (∀ k : Shell 13, detG 2 (skewCayley 2 k) = 0 ↔ (k = 4 ∨ k = 9)) := by
  decide +kernel

end FRC.Dirac.Det
