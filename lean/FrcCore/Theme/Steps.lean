import FrcCore.Theme.Count
import FrcCore.Poly

/-!
# FrcCore.Theme.Steps — the value of a mode at one label (20-rh, 23 November 2026)

Let `x` be a nonzero residue whose powers `x^0, …, x^M` are distinct, and let `(p − 1) ≤ M · W`. Then every nonzero
residue `y` is `x^k · g^r` with `r < W`: `y` is fewer than `W` steps of the drive after a power of `x` (`power_steps`).
The proof is the pigeonhole principle on the scales of the powers, cut into runs of `W` places, and a division of the
scale of `y`. For a label `ℓ ≥ 2` with `ℓ^N < p` the powers `ℓ^0, …, ℓ^N` are distinct residues, so the statement
holds with `M = N` and a count `k < p − 1` (`label_steps`, 20:D19): the mode of count `k` has the value `ℓ^k` at the
label `ℓ`, and every nonzero residue is fewer than `W` steps of the drive after one of these values. The paper writes
`M` and `V` for `N` and `W`. The count theme's third file, above `Theme/Count.lean`. No axioms.
-/

namespace FRC.Horizon

open FRC.Shell FRC.Shell.Frame

/-! ## The pigeonhole principle on the naturals -/

/-- A value is taken at an argument up to `M`, or at none. -/
theorem taken_or_not (f : Nat → Nat) (c : Nat) :
    ∀ M, (∃ i, i ≤ M ∧ f i = c) ∨ (∀ i, i ≤ M → f i ≠ c)
  | 0 =>
    match Nat.decEq (f 0) c with
    | .isTrue h => .inl ⟨0, Nat.le_refl 0, h⟩
    | .isFalse h => .inr fun i hi => by
        rw [Nat.eq_zero_of_le_zero hi]; exact h
  | M + 1 =>
    match taken_or_not f c M with
    | .inl ⟨i, hi, e⟩ => .inl ⟨i, Nat.le_succ_of_le hi, e⟩
    | .inr hno =>
      match Nat.decEq (f (M + 1)) c with
      | .isTrue h => .inl ⟨M + 1, Nat.le_refl _, h⟩
      | .isFalse h => .inr fun i hi =>
          match Nat.eq_or_lt_of_le hi with
          | .inl e => by rw [e]; exact h
          | .inr lt => hno i (Nat.le_of_lt_succ lt)

/-- The squeeze that removes the value `c`: it keeps the values below `c` and lowers the others by one. -/
def squeeze (c v : Nat) : Nat := if v < c then v else v - 1

theorem squeeze_lt {c v M : Nat} (hc : c ≤ M) (hv : v < M + 1) (hne : v ≠ c) : squeeze c v < M := by
  show (if v < c then v else v - 1) < M
  match Nat.lt_or_ge v c with
  | .inl h => rw [ite_eq_left h]; exact Nat.lt_of_lt_of_le h hc
  | .inr h =>
    rw [ite_eq_right (Nat.not_lt.mpr h)]
    have hcv : c < v := Nat.lt_of_le_of_ne h (fun e => hne e.symm)
    have hpos : 0 < v := Nat.lt_of_le_of_lt (Nat.zero_le c) hcv
    exact Nat.lt_of_lt_of_le (Nat.sub_lt hpos (Nat.succ_pos 0)) (Nat.le_of_lt_succ hv)

theorem squeeze_inj {c v w : Nat} (hv : v ≠ c) (hw : w ≠ c) (h : squeeze c v = squeeze c w) : v = w := by
  have key : ∀ {a b : Nat}, a < c → c < b → squeeze c a = squeeze c b → False := by
    intro a b ha hb e
    have e' : (if a < c then a else a - 1) = (if b < c then b else b - 1) := e
    rw [ite_eq_left ha, ite_eq_right (Nat.not_lt.mpr (Nat.le_of_lt hb))] at e'
    have hb1 : c ≤ b - 1 := FRC.Nat.le_sub_of_add_le hb
    exact Nat.lt_irrefl a (Nat.lt_of_lt_of_le ha (e' ▸ hb1))
  have lt_or_gt : ∀ {a : Nat}, a ≠ c → a < c ∨ c < a := fun {a} ha =>
    match Nat.lt_or_ge a c with
    | .inl h => .inl h
    | .inr h => .inr (Nat.lt_of_le_of_ne h (fun e => ha e.symm))
  match lt_or_gt hv, lt_or_gt hw with
  | .inl h1, .inl h2 =>
    have e' : (if v < c then v else v - 1) = (if w < c then w else w - 1) := h
    rw [ite_eq_left h1, ite_eq_left h2] at e'; exact e'
  | .inl h1, .inr h2 => exact absurd (key h1 h2 h) id
  | .inr h1, .inl h2 => exact absurd (key h2 h1 h.symm) id
  | .inr h1, .inr h2 =>
    have e' : (if v < c then v else v - 1) = (if w < c then w else w - 1) := h
    rw [ite_eq_right (Nat.not_lt.mpr (Nat.le_of_lt h1)), ite_eq_right (Nat.not_lt.mpr (Nat.le_of_lt h2))] at e'
    have pv : 0 < v := Nat.lt_of_le_of_lt (Nat.zero_le c) h1
    have pw : 0 < w := Nat.lt_of_le_of_lt (Nat.zero_le c) h2
    calc v = (v - 1) + 1 := (Nat.succ_pred_eq_of_pos pv).symm
      _ = (w - 1) + 1 := by rw [e']
      _ = w := Nat.succ_pred_eq_of_pos pw

/-- The pigeonhole principle: `M + 1` arguments with values below `M` have two equal values. -/
theorem pigeonhole : ∀ (M : Nat) (f : Nat → Nat), (∀ i, i ≤ M → f i < M) →
    ∃ i j, i < j ∧ j ≤ M ∧ f i = f j
  | 0, _, h => absurd (h 0 (Nat.le_refl 0)) (Nat.not_lt_zero _)
  | M + 1, f, h =>
    match taken_or_not f (f (M + 1)) M with
    | .inl ⟨i, hi, e⟩ => ⟨i, M + 1, Nat.lt_succ_of_le hi, Nat.le_refl _, e⟩
    | .inr hno =>
      have hc : f (M + 1) ≤ M := Nat.le_of_lt_succ (h (M + 1) (Nat.le_refl _))
      have hf' : ∀ i, i ≤ M → squeeze (f (M + 1)) (f i) < M := fun i hi =>
        squeeze_lt hc (h i (Nat.le_succ_of_le hi)) (hno i hi)
      match pigeonhole M (fun i => squeeze (f (M + 1)) (f i)) hf' with
      | ⟨i, j, hij, hj, e⟩ =>
        ⟨i, j, hij, Nat.le_succ_of_le hj,
          squeeze_inj (hno i (Nat.le_trans (Nat.le_of_lt hij) hj)) (hno j hj) e⟩

/-! ## The quotient by repeated subtraction -/

/-- The quotient of `e` by `W`, with fuel. -/
def quo (W : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, e => if W ≤ e then quo W f (e - W) + 1 else 0

theorem quo_spec {W : Nat} (hW : 0 < W) : ∀ (f e : Nat), e ≤ f → ∃ r, r < W ∧ e = W * quo W f e + r
  | 0, e, he => ⟨0, hW, by rw [Nat.eq_zero_of_le_zero he]; rfl⟩
  | f + 1, e, he =>
    match Nat.lt_or_ge e W with
    | .inl h => ⟨e, h, by
        show e = W * (if W ≤ e then quo W f (e - W) + 1 else 0) + e
        rw [ite_eq_right (Nat.not_le.mpr h), Nat.mul_zero, Nat.zero_add]⟩
    | .inr h =>
      have hle : e - W ≤ f := FRC.Nat.sub_le_of_le_add (Nat.le_trans he (Nat.add_le_add_left hW f))
      match quo_spec hW f (e - W) hle with
      | ⟨r, hr, e1⟩ => ⟨r, hr, by
          show e = W * (if W ≤ e then quo W f (e - W) + 1 else 0) + r
          rw [ite_eq_left h, Nat.mul_succ]
          calc e = e - W + W := (FRC.Nat.sub_add_cancel h).symm
            _ = W * quo W f (e - W) + r + W := by rw [← e1]
            _ = W * quo W f (e - W) + W + r := Nat.add_right_comm _ _ _⟩

variable {p : Nat} [Pos p] {κ : Nat} {g : Shell p}

/-! ## The scale of a residue, by search -/

/-- The search for an exponent `t < T` with `g^t = x`, from the top. -/
def dlogAux (g x : Shell p) : Nat → Nat
  | 0 => 0
  | t + 1 => if g ^ t = x then t else dlogAux g x t

theorem dlogAux_spec (g x : Shell p) : ∀ T, (∃ m, m < T ∧ g ^ m = x) →
    dlogAux g x T < T ∧ g ^ (dlogAux g x T) = x
  | 0, ⟨m, hm, _⟩ => absurd hm (Nat.not_lt_zero m)
  | T + 1, ⟨m, hm, e⟩ =>
    match (inferInstance : Decidable (g ^ T = x)) with
    | .isTrue h => by
        show (if g ^ T = x then T else dlogAux g x T) < T + 1 ∧ g ^ (if g ^ T = x then T else dlogAux g x T) = x
        rw [ite_eq_left h]; exact ⟨Nat.lt_succ_self T, h⟩
    | .isFalse h => by
        show (if g ^ T = x then T else dlogAux g x T) < T + 1 ∧ g ^ (if g ^ T = x then T else dlogAux g x T) = x
        rw [ite_eq_right h]
        have hmT : m < T := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hm) (fun e' => h (e' ▸ e))
        have ih := dlogAux_spec g x T ⟨m, hmT, e⟩
        exact ⟨Nat.lt_succ_of_lt ih.1, ih.2⟩

/-- A power of a nonzero residue is nonzero. -/
theorem unit_pow_ne_zero (F : Frame p κ g) {x : Shell p} (hx : x ≠ 0) : ∀ i : Nat, x ^ i ≠ 0
  | 0 => F.one_ne_zero
  | i + 1 => F.mul_ne_zero (unit_pow_ne_zero F hx i) hx

/-! ## The steps of the drive after a power -/

/-- If the powers `x^0, …, x^M` of a nonzero residue are distinct and `p − 1 ≤ M · W`, every nonzero residue is
`x^k · g^r` with `r < W`: it is fewer than `W` steps of the drive after a power of `x`. -/
theorem power_steps (F : Frame p κ g) {x : Shell p} (hx : x ≠ 0) {M W : Nat} (hW0 : 0 < W)
    (hd : ∀ i j, i < j → j ≤ M → x ^ i ≠ x ^ j) (hW : p - 1 ≤ M * W) :
    ∀ y : Shell p, y ≠ 0 → ∃ k r : Nat, r < W ∧ x ^ k * g ^ r = y := by
  -- the scales of the powers and their runs
  have ind : ∀ i, dlogAux g (x ^ i) (p - 1) < p - 1 ∧ g ^ (dlogAux g (x ^ i) (p - 1)) = x ^ i := fun i =>
    dlogAux_spec g (x ^ i) (p - 1) (F.eq_pow_of_ne_zero (unit_pow_ne_zero F hx i))
  have run : ∀ i, i ≤ M → quo W (dlogAux g (x ^ i) (p - 1)) (dlogAux g (x ^ i) (p - 1)) < M := fun i _ =>
    match quo_spec hW0 (dlogAux g (x ^ i) (p - 1)) (dlogAux g (x ^ i) (p - 1)) (Nat.le_refl _) with
    | ⟨r, _, e⟩ =>
      match Nat.lt_or_ge (quo W (dlogAux g (x ^ i) (p - 1)) (dlogAux g (x ^ i) (p - 1))) M with
      | .inl h => h
      | .inr h => absurd
          (calc W * M ≤ W * quo W (dlogAux g (x ^ i) (p - 1)) (dlogAux g (x ^ i) (p - 1)) := Nat.mul_le_mul_left W h
            _ ≤ W * quo W (dlogAux g (x ^ i) (p - 1)) (dlogAux g (x ^ i) (p - 1)) + r := Nat.le_add_right _ _
            _ = dlogAux g (x ^ i) (p - 1) := e.symm
            _ < p - 1 := (ind i).1
            _ ≤ M * W := hW
            _ = W * M := Nat.mul_comm M W)
          (Nat.lt_irrefl _)
  match pigeonhole M (fun i => quo W (dlogAux g (x ^ i) (p - 1)) (dlogAux g (x ^ i) (p - 1))) run with
  | ⟨i, j, hij, hjM, hb⟩ =>
    match quo_spec hW0 (dlogAux g (x ^ i) (p - 1)) (dlogAux g (x ^ i) (p - 1)) (Nat.le_refl _),
          quo_spec hW0 (dlogAux g (x ^ j) (p - 1)) (dlogAux g (x ^ j) (p - 1)) (Nat.le_refl _) with
    | ⟨ri, hri, ei⟩, ⟨rj, hrj, ej⟩ =>
      have hb' : quo W (dlogAux g (x ^ i) (p - 1)) (dlogAux g (x ^ i) (p - 1))
          = quo W (dlogAux g (x ^ j) (p - 1)) (dlogAux g (x ^ j) (p - 1)) := hb
      have hxi : x ^ i ≠ 0 := unit_pow_ne_zero F hx i
      have hsplit : x ^ j = x ^ i * x ^ (j - i) := by
        rw [← pow_add, FRC.Nat.add_sub_of_le (Nat.le_of_lt hij)]
      have hne : ri ≠ rj := fun e => hd i j hij hjM (by
        rw [← (ind i).2, ← (ind j).2, ei, ej, hb', e])
      match Nat.lt_or_ge ri rj with
      | .inl hlt =>
        -- x^(j-i) = g^d with d = rj - ri
        have hdW : rj - ri < W := Nat.lt_of_le_of_lt (Nat.sub_le rj ri) hrj
        have hd0 : 0 < rj - ri := FRC.Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hlt)
        have hej : dlogAux g (x ^ j) (p - 1) = dlogAux g (x ^ i) (p - 1) + (rj - ri) := by
          rw [ej, ei, hb', Nat.add_assoc, FRC.Nat.add_sub_of_le (Nat.le_of_lt hlt)]
        have hstep : x ^ (j - i) = g ^ (rj - ri) := F.mul_left_cancel hxi (by
          rw [← hsplit, ← (ind j).2, hej, pow_add, (ind i).2])
        intro y hy
        match F.eq_pow_of_ne_zero hy with
        | ⟨e, _, hye⟩ =>
          match FRC.Nat.mod_spec (rj - ri) hd0 e with
          | ⟨t, ht⟩ =>
            exact ⟨(j - i) * t, e % (rj - ri), Nat.lt_trans (FRC.Nat.mod_lt' e hd0) hdW, by
              rw [pow_mul, hstep, ← pow_mul, ← pow_add, ← ht]; exact hye⟩
      | .inr hge =>
        have hlt : rj < ri := Nat.lt_of_le_of_ne hge (fun e => hne e.symm)
        have hdW : ri - rj < W := Nat.lt_of_le_of_lt (Nat.sub_le ri rj) hri
        have hd0 : 0 < ri - rj := FRC.Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hlt)
        have hei : dlogAux g (x ^ i) (p - 1) = dlogAux g (x ^ j) (p - 1) + (ri - rj) := by
          rw [ei, ej, hb', Nat.add_assoc, FRC.Nat.add_sub_of_le (Nat.le_of_lt hlt)]
        -- 1 = x^(j-i) * g^d with d = ri - rj
        have hstep : (1 : Shell p) = x ^ (j - i) * g ^ (ri - rj) := F.mul_left_cancel hxi (by
          rw [mul_one, ← mul_assoc, ← hsplit, ← (ind j).2, ← pow_add, ← hei, (ind i).2])
        intro y hy
        match F.eq_pow_of_ne_zero hy with
        | ⟨e, he, hye⟩ =>
          match FRC.Nat.mod_spec (ri - rj) hd0 (p - 1 - e) with
          | ⟨q, hq⟩ =>
            have hs : (p - 1 - e) % (ri - rj) ≤ ri - rj := Nat.le_of_lt (FRC.Nat.mod_lt' _ hd0)
            -- e + d (q+1) = (p-1) + (d - s)
            have harith : e + (ri - rj) * (q + 1)
                = (p - 1) + ((ri - rj) - (p - 1 - e) % (ri - rj)) := by
              rw [Nat.mul_succ]
              calc e + ((ri - rj) * q + (ri - rj))
                  = e + ((ri - rj) * q + ((p - 1 - e) % (ri - rj)
                      + ((ri - rj) - (p - 1 - e) % (ri - rj)))) := by rw [FRC.Nat.add_sub_of_le hs]
                _ = e + (((ri - rj) * q + (p - 1 - e) % (ri - rj))
                      + ((ri - rj) - (p - 1 - e) % (ri - rj))) := by rw [Nat.add_assoc ((ri - rj) * q)]
                _ = e + ((p - 1 - e) + ((ri - rj) - (p - 1 - e) % (ri - rj))) := by rw [← hq]
                _ = (e + (p - 1 - e)) + ((ri - rj) - (p - 1 - e) % (ri - rj)) := (Nat.add_assoc _ _ _).symm
                _ = (p - 1) + ((ri - rj) - (p - 1 - e) % (ri - rj)) := by
                    rw [FRC.Nat.add_sub_of_le (Nat.le_of_lt he)]
            have hone : x ^ ((j - i) * (q + 1)) * g ^ ((ri - rj) * (q + 1)) = 1 := by
              rw [pow_mul, pow_mul, ← mul_pow, ← hstep, one_pow]
            have hgr : g ^ ((ri - rj) - (p - 1 - e) % (ri - rj)) = y * g ^ ((ri - rj) * (q + 1)) := by
              rw [← hye, ← pow_add, harith, pow_add, F.pow_n, one_mul]
            exact ⟨(j - i) * (q + 1), (ri - rj) - (p - 1 - e) % (ri - rj),
              Nat.lt_of_le_of_lt (Nat.sub_le _ _) hdW, by
                rw [hgr]
                calc x ^ ((j - i) * (q + 1)) * (y * g ^ ((ri - rj) * (q + 1)))
                    = y * (x ^ ((j - i) * (q + 1)) * g ^ ((ri - rj) * (q + 1))) := by
                      rw [← mul_assoc, mul_comm (x ^ ((j - i) * (q + 1))) y, mul_assoc]
                  _ = y := by rw [hone, mul_one]⟩

/-! ## The labels -/

/-- A label `0 < A < p` is a nonzero residue. -/
theorem label_ne_zero {A : Nat} (hA0 : 0 < A) (hA : A < p) : (ofNat A : Shell p) ≠ 0 := by
  intro h
  have := val_injective h
  rw [val_ofNat, val_zero, FRC.Nat.mod_eq_of_lt hA] at this
  exact absurd this (Nat.ne_of_gt hA0)

/-- The powers of a label are the labels of its powers. -/
theorem label_pow (ℓ : Nat) : ∀ i : Nat, (ofNat ℓ : Shell p) ^ i = ofNat (ℓ ^ i)
  | 0 => ext (by rw [val_ofNat]; exact val_one)
  | i + 1 => by
    show (ofNat ℓ : Shell p) ^ i * ofNat ℓ = ofNat (ℓ ^ i * ℓ)
    rw [label_pow ℓ i, ofNat_mul]

/-- The powers of a label `ℓ ≥ 2` grow. -/
theorem label_pow_lt {ℓ : Nat} (hℓ : 1 < ℓ) {i j : Nat} (hij : i < j) : ℓ ^ i < ℓ ^ j :=
  have hpos : 0 < ℓ ^ i := FRC.Nat.pos_pow_of_pos i (Nat.lt_trans (Nat.zero_lt_one) hℓ)
  have h1 : ℓ ^ i < ℓ ^ (i + 1) := by
    show ℓ ^ i < ℓ ^ i * ℓ
    have := FRC.Nat.mul_lt_mul_of_lt_of_pos hℓ hpos
    rw [Nat.one_mul, Nat.mul_comm] at this
    exact this
  Nat.lt_of_lt_of_le h1 (Nat.pow_le_pow_right (Nat.lt_trans (Nat.zero_lt_one) hℓ) hij)

/-- A power of a nonzero residue is its power at a count: the exponent reduces modulo `p − 1`. -/
theorem pow_count (F : Frame p κ g) {x : Shell p} (hx : x ≠ 0) (hp : 0 < p - 1) (k : Nat) :
    ∃ k' : Nat, k' < p - 1 ∧ x ^ k' = x ^ k := by
  obtain ⟨r, hr, hk⟩ := quo_spec hp k k (Nat.le_refl k)
  refine ⟨r, hr, ?_⟩
  have h : x ^ ((p - 1) * quo (p - 1) k k + r) = x ^ r := by
    rw [pow_add, pow_mul, FRC.Horizon.unit_pow_card F hx, one_pow, one_mul]
  rw [← h, ← hk]

/-- 20:D19 — the value of a mode at one label. Let `ℓ ≥ 2` be a label with `ℓ^N < p`, and let `p − 1 ≤ N · W`. Then
every nonzero residue is `ℓ^k · g^r` with a count `k < p − 1` and `r < W`: the mode of count `k` has the value `ℓ^k`
at the label `ℓ`, and the residue is `r` steps of the drive after that value. -/
theorem label_steps (F : Frame p κ g) {ℓ N W : Nat} (hℓ : 1 < ℓ) (hN0 : 0 < N) (hN : ℓ ^ N < p)
    (hW0 : 0 < W) (hW : p - 1 ≤ N * W) :
    ∀ y : Shell p, y ≠ 0 → ∃ k r : Nat, k < p - 1 ∧ r < W ∧ (ofNat ℓ : Shell p) ^ k * g ^ r = y := by
  have hℓ0 : 0 < ℓ := Nat.lt_trans (Nat.zero_lt_one) hℓ
  have hℓp : ℓ < p := Nat.lt_of_le_of_lt
    (by
      have h : ℓ ^ 1 ≤ ℓ ^ N := Nat.pow_le_pow_right hℓ0 hN0
      have e : ℓ ^ 1 = ℓ := by show ℓ ^ 0 * ℓ = ℓ; rw [Nat.pow_zero, Nat.one_mul]
      rw [e] at h; exact h) hN
  have hp1 : 0 < p - 1 :=
    FRC.Nat.le_sub_of_add_le (Nat.succ_le_of_lt (Nat.lt_trans hℓ hℓp))
  have hcov : ∀ y : Shell p, y ≠ 0 → ∃ k r : Nat, r < W ∧ (ofNat ℓ : Shell p) ^ k * g ^ r = y := by
    refine power_steps F (label_ne_zero hℓ0 hℓp) hW0 (fun i j hij hj e => ?_) hW
    have hi : ℓ ^ i < p := Nat.lt_of_le_of_lt
      (Nat.pow_le_pow_right hℓ0 (Nat.le_trans (Nat.le_of_lt hij) hj)) hN
    have hj' : ℓ ^ j < p := Nat.lt_of_le_of_lt (Nat.pow_le_pow_right hℓ0 hj) hN
    rw [label_pow, label_pow] at e
    exact Nat.lt_irrefl _ (FRC.Shell.Poly.Frame.ofNat_inj_lt hi hj' e ▸ label_pow_lt hℓ hij)
  intro y hy
  obtain ⟨k, r, hr, hkr⟩ := hcov y hy
  obtain ⟨k', hk', hpow⟩ := pow_count F (label_ne_zero hℓ0 hℓp) hp1 k
  exact ⟨k', r, hk', hr, by rw [hpow]; exact hkr⟩

end FRC.Horizon
