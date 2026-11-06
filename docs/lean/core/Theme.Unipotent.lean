import FrcCore.Theme.Operator
import FrcCore.Poly

/-!
# The unipotent file of 8-dirac — the binomial theorem and the Frobenius in characteristic `p`, no axioms

The fifth file of the dirac theme (5 November 2026, the core-proof programme): `t^p ≈ 1` forces `(t − 1)^p ≈ 0` in an
operator ring of characteristic `p` (F7's kinetic unipotency, D10's orders). The binomial coefficients `C(n, k)` by
Pascal's rule, the identity `(k+1) C(n+1, k+1) = (n+1) C(n, k)`, and `p ∣ C(p, k)` for `0 < k < p` read on the shell
`𝔽_p` with a frame as the primality witness (`k · C(p, k) = p · C(p−1, k−1)` vanishes on the shell and `k` does not,
so `C(p, k)` does, the shell having no zero divisors). The binomial theorem in an `OpRing` for commuting elements,
by Pascal's rule and the shift of a sum; in characteristic `p` (`p • 1 ≈ 0`) the middle terms vanish, so
`(x + y)^p ≈ x^p + y^p` for commuting `x`, `y`, and `t^p ≈ 1` gives `(t − 1)^p ≈ t^p + (−1)^p ≈ 0` for odd `p`. No axioms.
-/

namespace FRC.Dirac.Operator

/-! ## Binomial coefficients -/

/-- `C(n, k)` by Pascal's rule. -/
def choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)

theorem choose_zero_right (n : Nat) : choose n 0 = 1 := by cases n <;> rfl
theorem choose_zero_succ (k : Nat) : choose 0 (k + 1) = 0 := rfl
theorem choose_succ_succ (n k : Nat) : choose (n + 1) (k + 1) = choose n k + choose n (k + 1) := rfl

theorem choose_eq_zero_of_lt : ∀ n k, n < k → choose n k = 0
  | 0, k + 1, _ => rfl
  | n + 1, k + 1, h => by
    rw [choose_succ_succ, choose_eq_zero_of_lt n k (Nat.lt_of_succ_lt_succ h),
      choose_eq_zero_of_lt n (k + 1) (Nat.lt_of_succ_lt h)]

theorem choose_one : ∀ n, choose n 1 = n
  | 0 => rfl
  | n + 1 => by rw [choose_succ_succ, choose_zero_right, choose_one n, Nat.add_comm]

/-- `(k+1) C(n+1, k+1) = (n+1) C(n, k)`. -/
theorem succ_mul_choose_succ : ∀ n k, (k + 1) * choose (n + 1) (k + 1) = (n + 1) * choose n k
  | 0, 0 => rfl
  | 0, k + 1 => by
    rw [choose_succ_succ, choose_zero_succ, choose_zero_succ, Nat.add_zero, Nat.mul_zero, Nat.mul_zero]
  | n + 1, 0 => by
    show 1 * choose (n + 1 + 1) 1 = (n + 1 + 1) * choose (n + 1) 0
    rw [choose_one, choose_zero_right, Nat.one_mul, Nat.mul_one]
  | n + 1, k + 1 => by
    have h1 := succ_mul_choose_succ n k
    have h2 := succ_mul_choose_succ n (k + 1)
    rw [choose_succ_succ (n + 1) (k + 1), Nat.mul_add, h2, Nat.add_mul (k + 1) 1 (choose (n + 1) (k + 1)), Nat.one_mul,
      h1, Nat.add_mul (n + 1) 1 (choose (n + 1) (k + 1)), Nat.one_mul, choose_succ_succ n k, Nat.mul_add,
      Nat.add_right_comm]

/-! ## `p ∣ C(p, k)` on the shell -/

open FRC.Shell in
theorem ofNat_mul {p : Nat} [Pos p] (a b : Nat) : (ofNat (a * b) : Shell p) = ofNat a * ofNat b :=
  Shell.ext (by rw [val_mul, val_ofNat, val_ofNat, val_ofNat, FRC.Nat.mul_mod _ _ _ Pos.pos])

open FRC.Shell in
theorem ofNat_self {p : Nat} [Pos p] : (ofNat p : Shell p) = 0 :=
  Shell.ext (by rw [val_ofNat, val_zero, FRC.Nat.mod_self _ Pos.pos])

open FRC.Shell in
theorem ofNat_ne_zero_of {p : Nat} [Pos p] {k : Nat} (h0 : 0 < k) (hk : k < p) : (ofNat k : Shell p) ≠ 0 := fun e => by
  have := val_injective e
  rw [val_ofNat, val_zero, FRC.Nat.mod_eq_of_lt hk] at this
  exact absurd this (Nat.ne_of_gt h0)

open FRC.Shell in
/-- `p ∣ C(p, k)` for `0 < k < p`, on the frame: `k C(p, k) = p C(p−1, k−1)` vanishes on the shell, `k` does not. -/
theorem choose_mod_prime {p κ : Nat} [Pos p] {g : Shell p} (F : Frame p κ g) {k : Nat} (h0 : 0 < k) (hk : k < p) :
    choose p k % p = 0 := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, (FRC.Nat.sub_add_cancel h0).symm⟩
  obtain ⟨p', hp'⟩ : ∃ p', p = p' + 1 := ⟨p - 1, (FRC.Nat.sub_add_cancel (Nat.lt_of_le_of_lt (Nat.zero_le _) hk)).symm⟩
  have hid : (k' + 1) * choose p (k' + 1) = p * choose p' k' := by rw [hp']; exact succ_mul_choose_succ p' k'
  have hsh : (ofNat (k' + 1) : Shell p) * ofNat (choose p (k' + 1)) = 0 := by
    rw [← ofNat_mul, hid, ofNat_mul, ofNat_self, Shell.zero_mul]
  rcases F.mul_eq_zero hsh with h | h
  · exact absurd h (ofNat_ne_zero_of h0 hk)
  · have := val_injective h
    rw [val_ofNat, val_zero] at this
    exact this

/-! ## The binomial theorem in an operator ring -/

variable {R : Type} [Add R] [Mul R] [Neg R] [OfNat R 0] [OfNat R 1] [OpRing R]

open OpRing (add_congr mul_congr neg_congr add_comm add_assoc zero_add add_neg mul_assoc one_mul mul_one left_distrib right_distrib)

omit [Add R] [Mul R] [Neg R] [OfNat R 0] [OfNat R 1] [OpRing R] in
/-- `n − (k+1) + 1 = n − k` for `k < n`. -/
theorem sub_succ_add_one {n k : Nat} (hk : k < n) : n - (k + 1) + 1 = n - k := by
  have hd := FRC.Nat.sub_add_cancel hk
  calc n - (k + 1) + 1 = n - (k + 1) + 1 + k - k := (FRC.Nat.add_sub_cancel _ _).symm
    _ = n - (k + 1) + (k + 1) - k := by rw [Nat.add_assoc, Nat.add_comm 1 k]
    _ = n - k := by rw [hd]

/-- `x^{m n} ≈ (x^m)^n`. -/
theorem opow_mul (x : R) (m : Nat) : ∀ n, opow x (m * n) ≈ opow (opow x m) n
  | 0 => by rw [Nat.mul_zero]; exact eq_refl 1
  | n + 1 => by
    rw [Nat.mul_succ]
    exact eq_trans (opow_add x (m * n) m) (mul_congr_left _ (opow_mul x m n))

/-- A sum split at its first term. -/
theorem osum_succ_left (f : Nat → R) : ∀ n, osum f (n + 1) ≈ f 0 + osum (fun k => f (k + 1)) n
  | 0 => eq_trans (zero_add _) (eq_symm (add_zero _))
  | n + 1 =>
    calc osum f (n + 1) + f (n + 1) ≈ f 0 + osum (fun k => f (k + 1)) n + f (n + 1) :=
          add_congr_left _ (osum_succ_left f n)
      _ ≈ f 0 + (osum (fun k => f (k + 1)) n + f (n + 1)) := add_assoc _ _ _

/-- The binomial sum `Σ_{k≤n} C(n, k) x^k y^{n−k}`. -/
def binom (x y : R) (n : Nat) : R := osum (fun k => nsmul (choose n k) (opow x k * opow y (n - k))) (n + 1)

/-- The binomial theorem for commuting `x`, `y`: `(x + y)^n ≈ Σ_{k≤n} C(n, k) x^k y^{n−k}`. -/
theorem binomial {x y : R} (h : Comm x y) : ∀ n, opow (x + y) n ≈ binom x y n
  | 0 =>
    calc (1 : R) ≈ 1 + 0 := eq_symm (add_zero 1)
      _ ≈ 0 + 1 := add_comm _ _
      _ ≈ 0 + nsmul 1 (1 * 1) := add_congr_right _ (eq_symm (eq_trans (zero_add _) (one_mul 1)))
  | n + 1 => by
    -- `(x+y)^{n+1} = binom n · x + binom n · y`
    have hyx : ∀ j, Comm (opow y j) x := fun j => opow_comm h.symm j
    have hstep : opow (x + y) (n + 1) ≈ binom x y n * x + binom x y n * y :=
      calc opow (x + y) n * (x + y) ≈ binom x y n * (x + y) := mul_congr_left _ (binomial h n)
        _ ≈ binom x y n * x + binom x y n * y := left_distrib _ _ _
    -- the two products, term by term
    have hbx : binom x y n * x ≈ osum (fun k => nsmul (choose n k) (opow x (k + 1) * opow y (n - k))) (n + 1) :=
      eq_trans (osum_mul_right _ _ _) (osum_congr _ fun k _ =>
        calc nsmul (choose n k) (opow x k * opow y (n - k)) * x ≈ nsmul (choose n k) (opow x k * opow y (n - k) * x) :=
              nsmul_mul_left _ _ _
          _ ≈ nsmul (choose n k) (opow x k * (opow y (n - k) * x)) := nsmul_congr (mul_assoc _ _ _) _
          _ ≈ nsmul (choose n k) (opow x k * (x * opow y (n - k))) := nsmul_congr (mul_congr_right _ (hyx _)) _
          _ ≈ nsmul (choose n k) (opow x k * x * opow y (n - k)) := nsmul_congr (eq_symm (mul_assoc _ _ _)) _)
    have hby : binom x y n * y ≈ osum (fun k => nsmul (choose n k) (opow x k * opow y (n - k + 1))) (n + 1) :=
      eq_trans (osum_mul_right _ _ _) (osum_congr _ fun k _ =>
        calc nsmul (choose n k) (opow x k * opow y (n - k)) * y ≈ nsmul (choose n k) (opow x k * opow y (n - k) * y) :=
              nsmul_mul_left _ _ _
          _ ≈ nsmul (choose n k) (opow x k * (opow y (n - k) * y)) := nsmul_congr (mul_assoc _ _ _) _)
    -- the target, split at its first term and expanded by Pascal's rule
    have htarget : binom x y (n + 1) ≈
        opow y (n + 1) + (osum (fun k => nsmul (choose n k) (opow x (k + 1) * opow y (n - k))) (n + 1) +
          osum (fun k => nsmul (choose n (k + 1)) (opow x (k + 1) * opow y (n - k))) (n + 1)) :=
      calc binom x y (n + 1) ≈ nsmul (choose (n + 1) 0) (opow x 0 * opow y (n + 1 - 0)) +
            osum (fun k => nsmul (choose (n + 1) (k + 1)) (opow x (k + 1) * opow y (n + 1 - (k + 1)))) (n + 1) :=
            osum_succ_left _ _
        _ ≈ opow y (n + 1) + osum (fun k => nsmul (choose n k) (opow x (k + 1) * opow y (n - k)) +
              nsmul (choose n (k + 1)) (opow x (k + 1) * opow y (n - k))) (n + 1) := by
            refine add_congr ?_ (osum_congr _ fun k _ => ?_)
            · show nsmul 1 (1 * opow y (n + 1)) ≈ opow y (n + 1)
              exact eq_trans (zero_add _) (one_mul _)
            · rw [Nat.succ_sub_succ n k, choose_succ_succ]
              exact add_nsmul _ _ _
        _ ≈ opow y (n + 1) + (osum (fun k => nsmul (choose n k) (opow x (k + 1) * opow y (n - k))) (n + 1) +
              osum (fun k => nsmul (choose n (k + 1)) (opow x (k + 1) * opow y (n - k))) (n + 1)) :=
            add_congr_right _ (osum_add _ _ _)
    -- `binom n · y` is the first target term plus the second sum: shift, and the last term of the second sum vanishes
    have hshift : osum (fun k => nsmul (choose n k) (opow x k * opow y (n - k + 1))) (n + 1) ≈
        opow y (n + 1) + osum (fun k => nsmul (choose n (k + 1)) (opow x (k + 1) * opow y (n - k))) (n + 1) :=
      calc osum (fun k => nsmul (choose n k) (opow x k * opow y (n - k + 1))) (n + 1)
          ≈ nsmul (choose n 0) (opow x 0 * opow y (n - 0 + 1)) +
              osum (fun k => nsmul (choose n (k + 1)) (opow x (k + 1) * opow y (n - (k + 1) + 1))) n :=
            osum_succ_left _ _
        _ ≈ opow y (n + 1) + osum (fun k => nsmul (choose n (k + 1)) (opow x (k + 1) * opow y (n - k))) n := by
            refine add_congr ?_ (osum_congr _ fun k hk => ?_)
            · rw [choose_zero_right, Nat.sub_zero]
              show nsmul 1 (1 * opow y (n + 1)) ≈ opow y (n + 1)
              exact eq_trans (zero_add _) (one_mul _)
            · show nsmul (choose n (k + 1)) (opow x (k + 1) * opow y (n - (k + 1) + 1)) ≈
                nsmul (choose n (k + 1)) (opow x (k + 1) * opow y (n - k))
              rw [sub_succ_add_one hk]
              exact eq_refl _
        _ ≈ opow y (n + 1) + (osum (fun k => nsmul (choose n (k + 1)) (opow x (k + 1) * opow y (n - k))) n +
              nsmul (choose n (n + 1)) (opow x (n + 1) * opow y (n - n))) := by
            refine add_congr_right _ (eq_symm (eq_trans (add_congr_right _ ?_) (add_zero _)))
            rw [choose_eq_zero_of_lt n (n + 1) (Nat.lt_succ_self n)]
            exact eq_refl _
    calc opow (x + y) (n + 1) ≈ binom x y n * x + binom x y n * y := hstep
      _ ≈ osum (fun k => nsmul (choose n k) (opow x (k + 1) * opow y (n - k))) (n + 1) +
            (opow y (n + 1) + osum (fun k => nsmul (choose n (k + 1)) (opow x (k + 1) * opow y (n - k))) (n + 1)) :=
          add_congr hbx (eq_trans hby hshift)
      _ ≈ opow y (n + 1) + (osum (fun k => nsmul (choose n k) (opow x (k + 1) * opow y (n - k))) (n + 1) +
            osum (fun k => nsmul (choose n (k + 1)) (opow x (k + 1) * opow y (n - k))) (n + 1)) :=
          add_left_comm _ _ _
      _ ≈ binom x y (n + 1) := eq_symm htarget

theorem choose_self : ∀ n, choose n n = 1
  | 0 => rfl
  | n + 1 => by rw [choose_succ_succ, choose_self n, choose_eq_zero_of_lt n (n + 1) (Nat.lt_succ_self n)]

/-! ## Characteristic `p` and the Frobenius -/

/-- The middle binomial coefficients vanish in characteristic `p` (`p • 1 ≈ 0`) on the frame's shell. -/
theorem nsmul_choose_prime {p κ : Nat} [Pos p] {g : Shell p} (F : Shell.Frame p κ g) (hch : nsmul p (1 : R) ≈ 0)
    {k : Nat} (h0 : 0 < k) (hk : k < p) (z : R) : nsmul (choose p k) z ≈ 0 := by
  obtain ⟨q, hq⟩ := FRC.Nat.mod_spec p Pos.pos (choose p k)
  rw [choose_mod_prime F h0 hk, Nat.add_zero] at hq
  calc nsmul (choose p k) z ≈ nsmul (p * q) z := eq_of_eq (by rw [← hq])
    _ ≈ nsmul p (nsmul q z) := mul_nsmul _ _ _
    _ ≈ nsmul p 1 * nsmul q z := nsmul_eq_mul_one _ _
    _ ≈ 0 * nsmul q z := mul_congr_left _ hch
    _ ≈ 0 := zero_mul _

/-- The Frobenius is additive on commuting elements in characteristic `p`: `(x + y)^p ≈ x^p + y^p`. -/
theorem frobenius_add {p κ : Nat} [Pos p] {g : Shell p} (F : Shell.Frame p κ g) (hch : nsmul p (1 : R) ≈ 0) {x y : R}
    (h : Comm x y) : opow (x + y) p ≈ opow x p + opow y p := by
  obtain ⟨p', hp'⟩ : ∃ p', p = p' + 1 := ⟨p - 1, (FRC.Nat.sub_add_cancel (Pos.pos : 0 < p)).symm⟩
  have hmid : ∀ k, k < p' → nsmul (choose p (k + 1)) (opow x (k + 1) * opow y (p - (k + 1))) ≈ 0 := fun k hk =>
    nsmul_choose_prime F hch (Nat.zero_lt_succ k) (hp' ▸ Nat.succ_lt_succ hk) _
  calc opow (x + y) p ≈ binom x y p := binomial h p
    _ ≈ nsmul (choose p 0) (opow x 0 * opow y (p - 0)) +
          osum (fun k => nsmul (choose p (k + 1)) (opow x (k + 1) * opow y (p - (k + 1)))) p := osum_succ_left _ _
    _ ≈ opow y p + (osum (fun k => nsmul (choose p (k + 1)) (opow x (k + 1) * opow y (p - (k + 1)))) p' +
          nsmul (choose p (p' + 1)) (opow x (p' + 1) * opow y (p - (p' + 1)))) := by
        refine add_congr ?_ (eq_of_eq (by rw [hp']; rfl))
        rw [choose_zero_right, Nat.sub_zero]
        show nsmul 1 (1 * opow y p) ≈ opow y p
        exact eq_trans (zero_add _) (one_mul _)
    _ ≈ opow y p + (0 + opow x p) := by
        refine add_congr_right _ (add_congr (osum_eq_zero p' hmid) ?_)
        rw [← hp', choose_self, Nat.sub_self]
        show nsmul 1 (opow x p * 1) ≈ opow x p
        exact eq_trans (zero_add _) (mul_one _)
    _ ≈ opow x p + opow y p := eq_trans (add_congr_right _ (zero_add _)) (add_comm _ _)

/-- `(−1)^{2j} ≈ 1` and `(−1)^{2j+1} ≈ −1`. -/
theorem opow_neg_one_even : ∀ j, opow (-1 : R) (2 * j) ≈ 1
  | 0 => eq_refl 1
  | j + 1 => by
    rw [Nat.mul_succ]
    calc opow (-1 : R) (2 * j + 1) * -1 ≈ opow (-1 : R) (2 * j) * -1 * -1 := eq_refl _
      _ ≈ 1 * -1 * -1 := mul_congr_left _ (mul_congr_left _ (opow_neg_one_even j))
      _ ≈ -1 * -1 := mul_congr_left _ (one_mul _)
      _ ≈ 1 * 1 := neg_mul_neg _ _
      _ ≈ 1 := one_mul 1

theorem opow_neg_one_odd (j : Nat) : opow (-1 : R) (2 * j + 1) ≈ -1 :=
  eq_trans (mul_congr_left _ (opow_neg_one_even j)) (one_mul _)

/-- 8:F7, 8:D10 — the translations are unipotent: on the frame's shell (`p = 4κ + 1`), in characteristic `p`,
`t^p ≈ 1` gives `(t − 1)^p ≈ t^p + (−1)^p ≈ 1 − 1 ≈ 0` (`t` and `−1` commute; the Frobenius is additive). -/
theorem translation_nilpotent {p κ : Nat} [Pos p] {g : Shell p} (F : Shell.Frame p κ g) (hch : nsmul p (1 : R) ≈ 0)
    {t : R} (ht : opow t p ≈ 1) : opow (t + -1) p ≈ 0 := by
  have hodd : opow (-1 : R) p ≈ -1 := by
    have : p = 2 * (2 * κ) + 1 := by rw [F.cap, ← Nat.mul_assoc]
    rw [this]; exact opow_neg_one_odd _
  calc opow (t + -1) p ≈ opow t p + opow (-1) p := frobenius_add F hch (Comm.neg_right (Comm.one_left t).symm)
    _ ≈ 1 + -1 := add_congr ht hodd
    _ ≈ 0 := add_neg 1

/-- 8:D10 — a unipotent step has order dividing `p`: `(u − 1)^p ≈ 0` gives `u^p ≈ 1`, and a phase times a
unipotent, `u ≈ φ + N` with `φ` central and `N^p ≈ 0`, `N` commuting with `φ`, has `u^p ≈ φ^p`. -/
theorem opow_of_nilpotent_shift {p κ : Nat} [Pos p] {g : Shell p} (F : Shell.Frame p κ g) (hch : nsmul p (1 : R) ≈ 0)
    {u φ N : R} (hu : u ≈ φ + N) (hφ : Comm φ N) (hN : opow N p ≈ 0) : opow u p ≈ opow φ p :=
  calc opow u p ≈ opow (φ + N) p := opow_congr hu p
    _ ≈ opow φ p + opow N p := frobenius_add F hch hφ
    _ ≈ opow φ p + 0 := add_congr_right _ hN
    _ ≈ opow φ p := add_zero _

end FRC.Dirac.Operator
