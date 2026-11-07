import FrcCore.Theme.Elim
/-!
# FrcCore.Theme.Cayley — the Cayley denominator `I − αH` (the operator theme)

The kernel criterion of `Theme/Elim` applied to the denominator of the Cayley transform, `I − αH` on the list
matrices of `Theme/Dirac` (`Mat.ident`, `Mat.add`, `Mat.neg`, `Mat.smul`): `det (I − αH) = 0` exactly when `α·Hv = v`
for some `v ≠ 0`, and for `α ≠ 0` exactly when `α⁻¹` is an eigenvalue of `H` (8:T1's step from the determinant to the
eigenvalues, for every matrix over `K`); `det I = 1`, so `α = 0` is always admissible. The rows of `Mat.ident` are
reached through `rangeS`, the structural form of `List.range`, whose core lemmas carry `propext`. On `𝔽₁₃` the
decided instance exhibits the two singular parameters of the skew Hamiltonian with their eigenvectors. No axioms.
-/

namespace FRC.Dirac.Det

open FRC FRC.Extension FRC.Dirac FRC.Dirac.Hermitian
open FRC.Dirac.Mat (nth)
open FRC.Shell (Frame)
open FRC.Shell.Frame (IsSquare)

variable {p : Nat} [Pos p] {ν : Shell p}

/-! ## The identity, the unit rows and the rows of `I − αH` -/


/-- `Mv`: the matrix applied to a vector, one dot product per row. -/
def mulVec (M : Mat p ν) (v : List (Ext p ν)) : List (Ext p ν) := M.map (fun r => dotL r v)

/-- `I − αH`, the denominator of the Cayley transform (8-dirac, Def. C14: `α` is admissible when it is invertible). -/
def cayleyDen (α : Ext p ν) (H : Mat p ν) : Mat p ν := Mat.add (Mat.ident H.length) (Mat.neg (Mat.smul α H))

/-- `[0, 1, …, n−1]` by appending (the structural form of `List.range`). -/
def rangeS : Nat → List Nat
  | 0 => []
  | n + 1 => rangeS n ++ [n]

/-- The `i`-th unit row of length `n`. -/
def unitRow (n i : Nat) : List (Ext p ν) := (rangeS n).map (fun j => if i = j then 1 else 0)

theorem range_loop_eq : ∀ (n : Nat) (acc : List Nat), List.range.loop n acc = List.range.loop n [] ++ acc
  | 0, _ => rfl
  | n + 1, acc => by
    show List.range.loop n (n :: acc) = List.range.loop n [n] ++ acc
    rw [range_loop_eq n (n :: acc), range_loop_eq n [n], append_assoc']; rfl

theorem range_eq_rangeS : ∀ n : Nat, List.range n = rangeS n
  | 0 => rfl
  | n + 1 => by
    show List.range.loop n [n] = rangeS n ++ [n]
    rw [range_loop_eq n [n]]; exact congrArg (· ++ [n]) (range_eq_rangeS n)

theorem length_rangeS : ∀ n : Nat, (rangeS n).length = n
  | 0 => rfl
  | n + 1 => by show (rangeS n ++ [n]).length = n + 1; rw [length_append', length_rangeS n]; rfl

theorem length_unitRow (n i : Nat) : (unitRow (ν := ν) n i).length = n := by
  show ((rangeS n).map _).length = n; rw [length_map, length_rangeS]

theorem nth_rangeS : ∀ (n i : Nat), i < n → nth 0 (rangeS n) i = i
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, i, h => by
    show nth 0 (rangeS n ++ [n]) i = i
    match Nat.lt_or_ge i n with
    | Or.inl hi => rw [nth_append_lt 0 _ _ i (by rw [length_rangeS]; exact hi)]; exact nth_rangeS n i hi
    | Or.inr hi =>
      have e : i = n := Nat.le_antisymm (Nat.le_of_lt_succ h) hi
      have := nth_append_len 0 (rangeS n) n
      rw [length_rangeS] at this
      rw [e]; exact this

/-- `dotL (r ++ [c]) v = dotL r v + c · v_{|r|}` when `v` reaches that far. -/
theorem dotL_append_single : ∀ (r : List (Ext p ν)) (c : Ext p ν) (v : List (Ext p ν)), r.length < v.length →
    dotL (r ++ [c]) v = dotL r v + c * nth 0 v r.length
  | [], c, x :: _, _ => by show c * x + 0 = 0 + c * x; rw [add_zero, zero_add]
  | [], _, [], h => absurd h (Nat.lt_irrefl 0)
  | _ :: _, _, [], h => absurd h (Nat.not_lt_zero _)
  | a :: r, c, x :: v, h => by
    show a * x + dotL (r ++ [c]) v = a * x + dotL r v + c * nth 0 v r.length
    rw [dotL_append_single r c v (Nat.lt_of_succ_lt_succ h), add_assoc]

theorem dotL_unitRow_ge : ∀ (n i : Nat) (v : List (Ext p ν)), n ≤ i → n ≤ v.length → dotL (unitRow n i) v = 0
  | 0, _, _, _, _ => rfl
  | n + 1, i, v, hi, hv => by
    show dotL ((rangeS n ++ [n]).map _) v = 0
    rw [map_append_single]
    have hl : ((rangeS n).map fun j => if i = j then (1 : Ext p ν) else 0).length < v.length := by
      rw [length_map, length_rangeS]; exact hv
    rw [dotL_append_single _ _ v hl]
    show dotL (unitRow n i) v + (if i = n then 1 else 0) * _ = 0
    rw [dotL_unitRow_ge n i v (Nat.le_of_succ_le hi) (Nat.le_of_succ_le hv), ite_eq_right (Nat.ne_of_gt hi), zero_mul, add_zero]

/-- The unit row reads off the `i`-th entry. -/
theorem dotL_unitRow : ∀ (n i : Nat) (v : List (Ext p ν)), i < n → n ≤ v.length → dotL (unitRow n i) v = nth 0 v i
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, i, v, hi, hv => by
    show dotL ((rangeS n ++ [n]).map _) v = nth 0 v i
    rw [map_append_single]
    have hl : ((rangeS n).map fun j => if i = j then (1 : Ext p ν) else 0).length < v.length := by
      rw [length_map, length_rangeS]; exact hv
    rw [dotL_append_single _ _ v hl]
    show dotL (unitRow n i) v + (if i = n then 1 else 0) * nth 0 v ((rangeS n).map _).length = nth 0 v i
    rw [length_map, length_rangeS]
    match Nat.lt_or_ge i n with
    | Or.inl h => rw [dotL_unitRow n i v h (Nat.le_of_succ_le hv), ite_eq_right (Nat.ne_of_lt h), zero_mul, add_zero]
    | Or.inr h =>
      have e : i = n := Nat.le_antisymm (Nat.le_of_lt_succ hi) h
      rw [dotL_unitRow_ge n i v h (Nat.le_of_succ_le hv), ite_eq_left e, Ext.one_mul, zero_add, e]

theorem length_ident (n : Nat) : (Mat.ident (p := p) (ν := ν) n).length = n := by
  show ((List.range n).map _).length = n; rw [length_map, range_eq_rangeS, length_rangeS]

theorem row_ident (n i : Nat) (h : i < n) : row (Mat.ident (p := p) (ν := ν) n) i = unitRow n i := by
  show nth [] ((List.range n).map fun i => (List.range n).map fun j => if i = j then (1 : Ext p ν) else 0) i = unitRow n i
  rw [nth_map_lt (fun i => (List.range n).map fun j => if i = j then (1 : Ext p ν) else 0) 0 [] _ i
        (by rw [range_eq_rangeS, length_rangeS]; exact h), range_eq_rangeS, nth_rangeS n i h]
  rfl

theorem zipWith_add_eq_radd : ∀ (r s : List (Ext p ν)), List.zipWith (· + ·) r s = radd r s
  | [], _ => rfl
  | _ :: _, [] => rfl
  | _ :: r, _ :: s => congrArg (_ :: ·) (zipWith_add_eq_radd r s)

theorem map_neg_smul (α : Ext p ν) : ∀ r : List (Ext p ν), (r.map (α * ·)).map (- ·) = rsmul (-α) r
  | [] => rfl
  | a :: r => by show -(α * a) :: _ = (-α * a) :: _; rw [neg_mul, map_neg_smul α r]; rfl

theorem length_cayleyDen (α : Ext p ν) (H : Mat p ν) : (cayleyDen α H).length = H.length := by
  show (List.zipWith _ (Mat.ident H.length) (Mat.neg (Mat.smul α H))).length = H.length
  rw [length_zipWith', length_ident]
  show (Mat.ident H.length).length = ((H.map _).map _).length
  rw [length_ident, length_map, length_map]

theorem row_cayleyDen (α : Ext p ν) (H : Mat p ν) (j : Nat) (hj : j < H.length) :
    row (cayleyDen α H) j = radd (unitRow H.length j) (rsmul (-α) (row H j)) := by
  show nth [] (List.zipWith (fun r s => List.zipWith (· + ·) r s) (Mat.ident H.length) (Mat.neg (Mat.smul α H))) j = _
  have h2 : j < (Mat.neg (Mat.smul α H)).length := by
    show j < ((H.map _).map _).length; rw [length_map, length_map]; exact hj
  rw [nth_zipWith (fun r s => List.zipWith (· + ·) r s) [] [] [] _ _ j (by rw [length_ident]; exact hj) h2]
  show List.zipWith (· + ·) (row (Mat.ident H.length) j) (nth [] ((H.map (fun r => r.map (α * ·))).map (fun r => r.map (- ·))) j) = _
  have h1 : j < (H.map (fun r => r.map (α * ·))).length := by rw [length_map]; exact hj
  rw [zipWith_add_eq_radd, row_ident _ _ hj, nth_map_lt (fun r : List (Ext p ν) => r.map (- ·)) [] [] _ j h1,
    nth_map_lt (fun r : List (Ext p ν) => r.map (α * ·)) [] [] _ j hj, map_neg_smul]
  rfl

theorem square_cayleyDen (α : Ext p ν) (H : Mat p ν) (hS : Square H) : Square (cayleyDen α H) := fun j hj => by
  rw [length_cayleyDen] at hj ⊢
  rw [row_cayleyDen α H j hj, length_radd, length_unitRow]
  rw [length_unitRow, length_rsmul]; exact (hS j hj).symm

theorem length_mulVec (H : Mat p ν) (v : List (Ext p ν)) : (mulVec H v).length = H.length := length_map _ H

theorem nth_mulVec (H : Mat p ν) (v : List (Ext p ν)) (j : Nat) : nth 0 (mulVec H v) j = dotL (row H j) v := by
  show nth 0 (H.map fun r => dotL r v) j = dotL (nth [] H j) v
  exact nth_map (fun r => dotL r v) [] H j

theorem nth_rsmul (c : Ext p ν) (v : List (Ext p ν)) (j : Nat) : nth 0 (rsmul c v) j = c * nth 0 v j := by
  show nth 0 (v.map (c * ·)) j = c * nth 0 v j
  rw [← mul_zero c]; exact nth_map (c * ·) 0 v j

/-! ## The eigenvalue criterion -/

/-- `v` lies in the kernel of `I − αH` exactly when `α · Hv = v`. -/
theorem inKer_cayleyDen_iff (α : Ext p ν) (H : Mat p ν) (hS : Square H) (v : List (Ext p ν)) (hv : v.length = H.length) :
    InKer (cayleyDen α H) v ↔ rsmul α (mulVec H v) = v := by
  have key : ∀ j, j < H.length → (dotL (row (cayleyDen α H) j) v = 0 ↔ α * dotL (row H j) v = nth 0 v j) := fun j hj => by
    rw [row_cayleyDen α H j hj, dotL_radd _ _ _ (by rw [length_unitRow, length_rsmul]; exact (hS j hj).symm),
      dotL_rsmul, dotL_unitRow _ _ _ hj (Nat.le_of_eq hv.symm), ← neg_mul]
    exact ⟨fun h => by
             have this : nth 0 v j + -(α * dotL (row H j) v) + α * dotL (row H j) v = 0 + α * dotL (row H j) v :=
               congrArg (· + α * dotL (row H j) v) h
             rw [add_assoc, neg_add, add_zero, zero_add] at this; exact this.symm,
           fun h => by rw [← h, add_neg]⟩
  constructor
  · intro hk
    refine ext_nth 0 _ _ (by rw [length_rsmul, length_mulVec, hv]) fun j hj => ?_
    rw [length_rsmul, length_mulVec] at hj
    rw [nth_rsmul, nth_mulVec H v j]; exact (key j hj).1 (hk j)
  · intro h j
    match Nat.lt_or_ge j H.length with
    | Or.inl hj =>
      refine (key j hj).2 ?_
      have this : nth 0 (rsmul α (mulVec H v)) j = nth 0 v j := congrArg (fun l => nth 0 l j) h
      rw [nth_rsmul, nth_mulVec H v j] at this; exact this
    | Or.inr hj => rw [row_beyond _ j (by rw [length_cayleyDen]; exact hj)]; rfl

/-- The Cayley denominator is singular exactly when `1` is an eigenvalue of `αH`: `det(I − αH) = 0 ↔ ∃ v ≠ 0, α·Hv = v`. -/
theorem cayleyDen_singular_iff {κ : Nat} {g : Shell p} (F : Frame p κ g) (hν : ¬IsSquare ν) (α : Ext p ν) (H : Mat p ν) (hS : Square H) :
    det (cayleyDen α H) = 0 ↔ ∃ v : List (Ext p ν), v.length = H.length ∧ ¬ IsZero v ∧ rsmul α (mulVec H v) = v := by
  refine Iff.trans (det_eq_zero_iff F hν _ (square_cayleyDen α H hS)) ?_
  rw [length_cayleyDen]
  exact ⟨fun ⟨v, hv, hz, hk⟩ => ⟨v, hv, hz, (inKer_cayleyDen_iff α H hS v hv).1 hk⟩,
         fun ⟨v, hv, hz, he⟩ => ⟨v, hv, hz, (inKer_cayleyDen_iff α H hS v hv).2 he⟩⟩

/-- 8:C17 — for `α ≠ 0` the excluded parameters are the inverses of the eigenvalues: `det(I − αH) = 0 ↔ ∃ v ≠ 0, Hv = α⁻¹v`,
for every square matrix over `K` (item (ii) of the classification). -/
theorem cayleyDen_singular_iff_eigen {κ : Nat} {g : Shell p} (F : Frame p κ g) (hν : ¬IsSquare ν) {α : Ext p ν} (hα : α ≠ 0)
    (H : Mat p ν) (hS : Square H) :
    det (cayleyDen α H) = 0 ↔ ∃ v : List (Ext p ν), v.length = H.length ∧ ¬ IsZero v ∧ mulVec H v = rsmul (inv α) v := by
  refine Iff.trans (cayleyDen_singular_iff F hν α H hS) ?_
  have hinv : inv α * α = 1 := by rw [Ext.mul_comm]; exact mul_inv F hν hα
  have rs : ∀ (c d : Ext p ν) (w : List (Ext p ν)), rsmul c (rsmul d w) = rsmul (c * d) w := fun c d w => by
    show (w.map (d * ·)).map (c * ·) = w.map ((c * d) * ·)
    exact map_map_mul c d w
  have one : ∀ w : List (Ext p ν), rsmul 1 w = w := fun w => by
    show w.map (1 * ·) = w; exact map_one_mul w
  exact ⟨fun ⟨v, hv, hz, he⟩ => ⟨v, hv, hz, by
            have := congrArg (rsmul (inv α)) he
            rw [rs, hinv, one] at this; exact this⟩,
         fun ⟨v, hv, hz, he⟩ => ⟨v, hv, hz, by rw [he, rs, mul_inv F hν hα, one]⟩⟩
where
  map_map_mul (c d : Ext p ν) : ∀ w : List (Ext p ν), (w.map (d * ·)).map (c * ·) = w.map ((c * d) * ·)
    | [] => rfl
    | x :: w => by show c * (d * x) :: _ = c * d * x :: _; rw [Ext.mul_assoc, map_map_mul c d w]
  map_one_mul : ∀ w : List (Ext p ν), w.map ((1 : Ext p ν) * ·) = w
    | [] => rfl
    | x :: w => by show 1 * x :: _ = x :: _; rw [Ext.one_mul, map_one_mul w]

/-! ## `det I = 1` -/

theorem rangeS_succ_eq_map : ∀ n : Nat, rangeS (n + 1) = 0 :: (rangeS n).map Nat.succ
  | 0 => rfl
  | n + 1 => by
    show rangeS (n + 1) ++ [n + 1] = 0 :: (rangeS n ++ [n]).map Nat.succ
    rw [rangeS_succ_eq_map n, map_append_single]; rfl

theorem ite_succ (i j : Nat) : (if i + 1 = j + 1 then (1 : Ext p ν) else 0) = if i = j then 1 else 0 :=
  match Nat.decEq i j with
  | isTrue h => by rw [h, ite_eq_left rfl, ite_eq_left rfl]
  | isFalse h => by rw [ite_eq_right h, ite_eq_right (fun e => h (Nat.succ.inj e))]

/-- The first minor of the identity is the identity one size down. -/
theorem minor_ident_zero (n : Nat) : minor (Mat.ident (p := p) (ν := ν) (n + 1)) 0 = Mat.ident n := by
  show ((removeAt ((List.range (n + 1)).map fun i => (List.range (n + 1)).map fun j => if i = j then (1 : Ext p ν) else 0) 0).map List.tail) = _
  rw [range_eq_rangeS, rangeS_succ_eq_map]
  show ((((rangeS n).map Nat.succ).map fun i => (0 :: (rangeS n).map Nat.succ).map fun j => if i = j then (1 : Ext p ν) else 0).map List.tail) = _
  rw [map_map', map_map']
  show ((rangeS n).map fun i => ((rangeS n).map Nat.succ).map fun j => if i + 1 = j then (1 : Ext p ν) else 0) = (List.range n).map _
  rw [range_eq_rangeS]
  exact map_congr' (fun i => by rw [map_map']; exact map_congr' (fun j => ite_succ i j) _) _

theorem head_unitRow_succ (n i : Nat) : head (unitRow (ν := ν) (n + 1) i) = if i = 0 then 1 else 0 := by
  show head ((rangeS (n + 1)).map _) = _
  rw [rangeS_succ_eq_map]; rfl

/-- `det I = 1`. -/
theorem det_ident : ∀ n : Nat, det (Mat.ident (p := p) (ν := ν) n) = 1
  | 0 => det_nil
  | n + 1 => by
    have hl : 0 < (Mat.ident (p := p) (ν := ν) (n + 1)).length := by rw [length_ident]; exact Nat.succ_pos n
    rw [det_first_col _ hl (fun i hi hi' => by
          rw [length_ident] at hi'
          rw [row_ident _ _ hi', head_unitRow_succ, ite_eq_right (Nat.ne_of_gt hi)]),
      row_ident _ _ (Nat.succ_pos n), head_unitRow_succ, ite_eq_left rfl, Ext.one_mul, minor_ident_zero, det_ident n]

/-- 8:C17 — `α = 0` is always admissible: `det(I − 0·H) = 1` (the admissible set contains zero). -/
theorem det_cayleyDen_zero (H : Mat p ν) (hS : Square H) : det (cayleyDen 0 H) = 1 := by
  have e : cayleyDen 0 H = Mat.ident H.length := by
    refine ext_nth [] _ _ (by rw [length_cayleyDen, length_ident]) fun j hj => ?_
    rw [length_cayleyDen] at hj
    show row (cayleyDen 0 H) j = row (Mat.ident H.length) j
    rw [row_cayleyDen 0 H j hj, row_ident _ _ hj]
    have hz : rsmul (-0 : Ext p ν) (row H j) = List.replicate (row H j).length 0 := by
      rw [neg_zero']; exact rsmul_zero _
    rw [hz, hS j hj]; exact radd_replicate_zero _ _ (length_unitRow _ _)
  rw [e, det_ident]
where
  neg_zero' : (-0 : Ext p ν) = 0 := Ext.ext Shell.neg_zero Shell.neg_zero
  rsmul_zero : ∀ r : List (Ext p ν), rsmul 0 r = List.replicate r.length 0
    | [] => rfl
    | x :: r => by show (0 * x) :: rsmul 0 r = 0 :: List.replicate r.length 0; rw [zero_mul, rsmul_zero r]
  radd_replicate_zero : ∀ (r : List (Ext p ν)) (n : Nat), r.length = n → radd r (List.replicate n 0) = r
    | [], 0, _ => rfl
    | [], _ + 1, h => absurd h (Nat.ne_of_lt (Nat.succ_pos _))
    | _ :: _, 0, h => absurd h (Nat.ne_of_gt (Nat.succ_pos _))
    | x :: r, n + 1, h => by show (x + 0) :: radd r (List.replicate n 0) = x :: r; rw [add_zero, radd_replicate_zero r n (Nat.succ.inj h)]

/-! ## Decided -/

/-- The skew Hamiltonian `H = [[0, w], [−w, 0]]`. -/
def skewH (ν : Shell p) : Mat p ν := [[0, ⟨0, 1⟩], [-⟨0, 1⟩, 0]]

/-- 8:C17 [value] — on `𝔽₁₃` (`ν = 2`): `I − kwH` is `skewCayley`; the Cayley denominator is singular exactly at `k = 4, 9`,
and at `k = 4` the vector `(8, 1)` is fixed by `αH`, at `k = 9` the vector `(5, 1)`. -/
theorem skew_cayleyDen_values :
    (∀ k : Shell 13, cayleyDen (⟨0, k⟩ : Ext 13 2) (skewH 2) = skewCayley 2 k) ∧
    (∀ k : Shell 13, detG 2 (cayleyDen (⟨0, k⟩ : Ext 13 2) (skewH 2)) = 0 ↔ (k = 4 ∨ k = 9)) ∧
    rsmul (⟨0, 4⟩ : Ext 13 2) (mulVec (skewH 2) [8, 1]) = [8, 1] ∧
    rsmul (⟨0, 9⟩ : Ext 13 2) (mulVec (skewH 2) [5, 1]) = [5, 1] := by
  decide +kernel


/-- The real symmetric block `[[a, b], [b, −a]]`, a self-adjoint operator on `K²` with `χ = x² − (a² + b²)`. -/
def symH (ν : Shell p) (a b : Shell p) : Mat p ν := [[⟨a, 0⟩, ⟨b, 0⟩], [⟨b, 0⟩, ⟨-a, 0⟩]]

/-- Whether the block `(a, b)` excludes some trace-zero parameter: `det(I − kwH) = 0` for some `k`. -/
def symExcluded (ν : Shell p) (a b : Nat) : Bool :=
  (List.range p).any fun k =>
    decide (detG 2 (cayleyDen (⟨0, Shell.ofNat k⟩ : Ext p ν) (symH ν (Shell.ofNat a) (Shell.ofNat b))) = 0)

/-- The paper's kinetic-plus-potential Hamiltonian `−Δ + V_id` on the cycle of `p` sites (8:E8's instance), as a list matrix. -/
def kinV (p : Nat) [Pos p] (ν : Shell p) : Mat p ν :=
  (List.range p).map fun i => (List.range p).map fun j =>
    nth 0 (kineticRow p ν) ((j + p - i) % p) + if i = j then ⟨Shell.ofNat i, 0⟩ else 0

/-- 8:C17 [value] — on `𝔽₁₃` (`ν = 2`): for every real symmetric block `[[a, b], [b, −a]]` and every `k`, `I − kwH` is
singular exactly when `k²·ν·(a² + b²) = 1`; exactly 72 of the 169 blocks exclude a parameter (those with `a² + b²` a
nonsquare), each of them two. -/
theorem sym_cayleyDen_values13 :
    (∀ a b k : Shell 13, detG 2 (cayleyDen (⟨0, k⟩ : Ext 13 2) (symH 2 a b)) = 0 ↔ k * k * 2 * (a * a + b * b) = 1) ∧
    count2 13 (symExcluded (2 : Shell 13)) = 72 := by
  decide +kernel

/-- 8:C17 [value] — the skew Hamiltonian on `𝔽₁₇₃` (`ν = 2`): the two excluded parameters are `k = 40, 133`, the roots of
`(kν)² = −1`. -/
theorem skew_cayleyDen_values173 :
    ∀ k : Shell 173, detG 2 (cayleyDen (⟨0, k⟩ : Ext 173 2) (skewH 2)) = 0 ↔ (k = 40 ∨ k = 133) := by
  decide +kernel

/-- 8:C17 [value] — the skew Hamiltonian on `𝔽₁₅₄₉` (`ν = 2`): the two excluded parameters are `k = 44, 1505`. -/
theorem skew_cayleyDen_values1549 :
    ∀ k : Shell 1549, detG 2 (cayleyDen (⟨0, k⟩ : Ext 1549 2) (skewH 2)) = 0 ↔ (k = 44 ∨ k = 1505) := by
  decide +kernel

/-- 8:C17 [value] — on `𝔽₁₃`: the paper's `−Δ + V_id` is fully admissible, `det(I − kwH) ≠ 0` for every `k`, read off the
general determinant by elimination. -/
theorem kinV_full13 : ∀ k : Shell 13, detG 13 (cayleyDen (⟨0, k⟩ : Ext 13 2) (kinV 13 2)) ≠ 0 := by
  decide +kernel

end FRC.Dirac.Det
