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

/-- The Frobenius is additive on a sum of pairwise commuting terms in characteristic `p`:
`(Σ_{j<n} f j)^p ≈ Σ_{j<n} (f j)^p`, by induction on `n` from `frobenius_add`. -/
theorem frobenius_osum {p κ : Nat} [Pos p] {g : Shell p} (F : Shell.Frame p κ g) (hch : nsmul p (1 : R) ≈ 0)
    {f : Nat → R} : ∀ n, (∀ i j, i < n → j < n → Comm (f i) (f j)) → opow (osum f n) p ≈ osum (fun j => opow (f j) p) n
  | 0, _ => by
    obtain ⟨p', hp'⟩ : ∃ p', p = p' + 1 := ⟨p - 1, (FRC.Nat.sub_add_cancel (Pos.pos : 0 < p)).symm⟩
    show opow (0 : R) p ≈ 0
    rw [hp']; exact opow_zero_of_zero p'
  | n + 1, h =>
    have hc : Comm (osum f n) (f n) := osum_comm n fun j hj => h j n (Nat.lt_succ_of_lt hj) (Nat.lt_succ_self n)
    calc opow (osum f n + f n) p ≈ opow (osum f n) p + opow (f n) p := frobenius_add F hch hc
      _ ≈ osum (fun j => opow (f j) p) n + opow (f n) p :=
          add_congr_left _ (frobenius_osum F hch n fun i j hi hj => h i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj))

/-- 8:D20 — the square bound of a Dirac operator. For `𝒟 = Σ_{μ<n} ∇_μ γ_μ` as in `dirac_square`, in characteristic `p`
on a frame, with every difference nilpotent of index at most `p` (`∇_μ^p ≈ 0`): `𝒟^{2p} ≈ 0`. The square is
`Σ_μ η_μ ∇_μ²`, the Frobenius is additive on its commuting summands, and `(η_μ ∇_μ²)^p ≈ η_μ^p ∇_μ^{2p} ≈ 0`. -/
theorem dirac_square_nilpotent {p κ : Nat} [Pos p] {g : Shell p} (F : Shell.Frame p κ g) (hch : nsmul p (1 : R) ≈ 0)
    {n : Nat} {del γ η : Nat → R}
    (hdd : ∀ μ ν, μ < n → ν < n → Comm (del μ) (del ν)) (hdg : ∀ μ ν, μ < n → ν < n → Comm (del μ) (γ ν))
    (hgg : ∀ μ ν, μ < n → ν < n → μ ≠ ν → Anticomm (γ μ) (γ ν)) (hsq : ∀ μ, μ < n → γ μ * γ μ ≈ η μ)
    (hη : ∀ μ, μ < n → Central (η μ)) (hnil : ∀ μ, μ < n → opow (del μ) p ≈ 0) :
    opow (osum (fun μ => del μ * γ μ) n) (2 * p) ≈ 0 := by
  have hcomm : ∀ i j, i < n → j < n → Comm (η i * (del i * del i)) (η j * (del j * del j)) := fun i j hi hj =>
    Comm.mul_left (hη i hi _)
      (Comm.mul_left (Comm.mul_right (Comm.symm (hη j hj (del i))) (Comm.mul_right (hdd i j hi hj) (hdd i j hi hj)))
        (Comm.mul_right (Comm.symm (hη j hj (del i))) (Comm.mul_right (hdd i j hi hj) (hdd i j hi hj))))
  have hterm : ∀ μ, μ < n → opow (η μ * (del μ * del μ)) p ≈ 0 := fun μ hμ =>
    calc opow (η μ * (del μ * del μ)) p ≈ opow (η μ) p * opow (del μ * del μ) p := mul_opow (hη μ hμ _) p
      _ ≈ opow (η μ) p * (opow (del μ) p * opow (del μ) p) := mul_congr_right _ (mul_opow (Comm.refl _) p)
      _ ≈ opow (η μ) p * (0 * 0) := mul_congr_right _ (mul_congr (hnil μ hμ) (hnil μ hμ))
      _ ≈ opow (η μ) p * 0 := mul_congr_right _ (mul_zero 0)
      _ ≈ 0 := mul_zero _
  calc opow (osum (fun μ => del μ * γ μ) n) (2 * p)
      ≈ opow (opow (osum (fun μ => del μ * γ μ) n) 2) p := opow_mul _ 2 p
    _ ≈ opow (osum (fun μ => del μ * γ μ) n * osum (fun μ => del μ * γ μ) n) p :=
        opow_congr (mul_congr_left _ (opow_one _)) p
    _ ≈ opow (osum (fun μ => η μ * (del μ * del μ)) n) p := opow_congr (dirac_square hdd hdg hgg hsq hη) p
    _ ≈ osum (fun μ => opow (η μ * (del μ * del μ)) p) n := frobenius_osum F hch n hcomm
    _ ≈ 0 := osum_eq_zero n hterm

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

/-! ## The exact index in `0+1` (D20) and the Frobenius of the eigenphase (E9) -/
/-- The power of an inverse pair of commuting elements is an inverse pair. -/
theorem inverse_opow {u v : R} (h : Inverse u v) (n : Nat) : Inverse (opow u n) (opow v n) := by
  have hc : Comm u v := eq_trans h.1 (eq_symm h.2)
  refine ⟨?_, ?_⟩
  · calc opow u n * opow v n ≈ opow (u * v) n := eq_symm (mul_opow hc n)
      _ ≈ opow 1 n := opow_congr h.1 n
      _ ≈ 1 := opow_one_left n
  · calc opow v n * opow u n ≈ opow (v * u) n := eq_symm (mul_opow hc.symm n)
      _ ≈ opow 1 n := opow_congr h.2 n
      _ ≈ 1 := opow_one_left n

/-- `C(p − 1, k) ≡ (−1)^k (mod p)` for `k < p`, read in the ring: `C(p−1, k) • 1 ≈ (−1)^k`. By Pascal's rule and
`p ∣ C(p, k + 1)`. -/
theorem nsmul_choose_pred {p κ : Nat} [Pos p] {g : Shell p} (F : Shell.Frame p κ g) (hch : nsmul p (1 : R) ≈ 0) :
    ∀ k, k < p → nsmul (choose (p - 1) k) (1 : R) ≈ opow (-1) k
  | 0, _ => by rw [choose_zero_right]; exact zero_add 1
  | k + 1, hk => by
    have ih := nsmul_choose_pred F hch k (Nat.lt_of_succ_lt hk)
    obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, (FRC.Nat.sub_add_cancel (Pos.pos : 0 < p)).symm⟩
    subst hq
    rw [FRC.Nat.add_sub_cancel] at ih ⊢
    have h0 : nsmul (choose (q + 1) (k + 1)) (1 : R) ≈ 0 := nsmul_choose_prime F hch (Nat.zero_lt_succ k) hk 1
    have hsum : nsmul (choose q k) (1 : R) + nsmul (choose q (k + 1)) 1 ≈ 0 :=
      eq_trans (eq_symm (add_nsmul _ _ _)) (eq_trans (eq_of_eq (by rw [← choose_succ_succ])) h0)
    calc nsmul (choose q (k + 1)) (1 : R) ≈ -(nsmul (choose q k) 1) := eq_symm (neg_eq_of_add_eq_zero hsum)
      _ ≈ -(opow (-1) k) := neg_congr ih
      _ ≈ opow (-1) k * -1 := eq_symm (mul_neg_one _)
      _ ≈ opow (-1) (k + 1) := eq_refl _

/-- `(t − 1)^{p−1} ≈ Σ_{k<p} t^k` in characteristic `p`, for every `t`: the polynomial identity
`(x − 1)^{p−1} = x^{p−1} + ⋯ + 1` of `𝔽_p[x]`. -/
theorem opow_sub_one_pred {p κ : Nat} [Pos p] {g : Shell p} (F : Shell.Frame p κ g) (hch : nsmul p (1 : R) ≈ 0) (t : R) :
    opow (t + -1) (p - 1) ≈ geom t p := by
  have hp : p = (p - 1) + 1 := (FRC.Nat.sub_add_cancel (Pos.pos : 0 < p)).symm
  have heven : ∀ j, j ≤ p - 1 → opow (-1 : R) (p - 1 - j) * opow (-1) j ≈ 1 := fun j hj => by
    have e : p - 1 - j + j = 4 * κ := by rw [FRC.Nat.sub_add_cancel hj, F.cap, FRC.Nat.add_sub_cancel]
    calc opow (-1 : R) (p - 1 - j) * opow (-1) j ≈ opow (-1) (p - 1 - j + j) := eq_symm (opow_add _ _ _)
      _ ≈ opow (-1) (2 * (2 * κ)) := eq_of_eq (by rw [e, ← Nat.mul_assoc])
      _ ≈ 1 := opow_neg_one_even _
  calc opow (t + -1) (p - 1) ≈ binom t (-1) (p - 1) := binomial (Comm.neg_right (Comm.one_left t).symm) _
    _ ≈ osum (fun k => opow t k) (p - 1 + 1) := by
        refine osum_congr _ fun k hk => ?_
        have hk' : k ≤ p - 1 := Nat.le_of_lt_succ hk
        calc nsmul (choose (p - 1) k) (opow t k * opow (-1) (p - 1 - k))
            ≈ nsmul (choose (p - 1) k) 1 * (opow t k * opow (-1) (p - 1 - k)) := nsmul_eq_mul_one _ _
          _ ≈ opow (-1) k * (opow t k * opow (-1) (p - 1 - k)) :=
              mul_congr_left _ (nsmul_choose_pred F hch k (Nat.lt_of_lt_of_le hk (Nat.le_of_eq hp.symm)))
          _ ≈ opow t k * opow (-1) (p - 1 - k) * opow (-1) k := Central.opow (Central.neg Central.one) k _
          _ ≈ opow t k * (opow (-1) (p - 1 - k) * opow (-1) k) := mul_assoc _ _ _
          _ ≈ opow t k * 1 := mul_congr_right _ (heven k hk')
          _ ≈ opow t k := mul_one _
    _ ≈ geom t p := eq_of_eq (by rw [← hp]; rfl)

/-- `(t + 1)^{p−1} ≈ Σ_{k<p} (−1)^k t^k` in characteristic `p`, for every `t`. -/
theorem opow_add_one_pred {p κ : Nat} [Pos p] {g : Shell p} (F : Shell.Frame p κ g) (hch : nsmul p (1 : R) ≈ 0) (t : R) :
    opow (t + 1) (p - 1) ≈ osum (fun k => opow (-1) k * opow t k) p := by
  have hp : p = (p - 1) + 1 := (FRC.Nat.sub_add_cancel (Pos.pos : 0 < p)).symm
  calc opow (t + 1) (p - 1) ≈ binom t 1 (p - 1) := binomial (Comm.one_left t).symm _
    _ ≈ osum (fun k => opow (-1) k * opow t k) (p - 1 + 1) := by
        refine osum_congr _ fun k hk => ?_
        calc nsmul (choose (p - 1) k) (opow t k * opow 1 (p - 1 - k))
            ≈ nsmul (choose (p - 1) k) 1 * (opow t k * opow 1 (p - 1 - k)) := nsmul_eq_mul_one _ _
          _ ≈ opow (-1) k * (opow t k * 1) := mul_congr (nsmul_choose_pred F hch k (Nat.lt_of_lt_of_le hk (Nat.le_of_eq hp.symm))) (mul_congr_right _ (opow_one_left _))
          _ ≈ opow (-1) k * opow t k := mul_congr_right _ (mul_one _)
    _ ≈ osum (fun k => opow (-1) k * opow t k) p := eq_of_eq (by rw [← hp])

/-- The alternating sum of `2m + 1` signs is `1`: `Σ_{k<2m+1} (−1)^k ≈ 1`. -/
theorem osum_alternating : ∀ m : Nat, osum (fun k => opow (-1 : R) k) (2 * m + 1) ≈ 1
  | 0 => eq_trans (zero_add _) (eq_refl 1)
  | m + 1 => by
    have e : 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 := rfl
    rw [e]
    calc osum (fun k => opow (-1 : R) k) (2 * m + 1 + 1 + 1)
        = osum (fun k => opow (-1 : R) k) (2 * m + 1) + opow (-1) (2 * m + 1) + opow (-1) (2 * m + 1 + 1) := rfl
      _ ≈ 1 + -1 + 1 := add_congr (add_congr (osum_alternating m) (opow_neg_one_odd m))
          (eq_trans (eq_of_eq (by show opow (-1 : R) (2 * (m + 1)) = _; rfl)) (opow_neg_one_even (m + 1)))
      _ ≈ 0 + 1 := add_congr_left 1 (add_neg 1)
      _ ≈ 1 := zero_add 1

/-- `t · geom t p ≈ geom t p` when `t^p ≈ 1`: the sum of the translates is invariant under the translation. -/
theorem mul_geom_self {t : R} {p : Nat} (ht : opow t p ≈ 1) : t * geom t p ≈ geom t p := by
  have h1 : geom t (p + 1) ≈ 1 + t * geom t p := geom_succ_left t p
  have h2 : geom t (p + 1) ≈ geom t p + 1 := eq_trans (eq_of_eq (osum_succ _ _)) (add_congr_right _ ht)
  have h3 : 1 + t * geom t p ≈ 1 + geom t p :=
    eq_trans (eq_symm h1) (eq_trans h2 (add_comm _ _))
  exact add_left_cancel h3

/-- `geom t p · t^k ≈ geom t p` when `t^p ≈ 1`. -/
theorem geom_mul_opow {t : R} {p : Nat} (ht : opow t p ≈ 1) : ∀ k, geom t p * opow t k ≈ geom t p
  | 0 => mul_one _
  | k + 1 =>
    calc geom t p * opow t (k + 1) = geom t p * (opow t k * t) := rfl
      _ ≈ geom t p * opow t k * t := eq_symm (mul_assoc _ _ _)
      _ ≈ geom t p * t := mul_congr_left t (geom_mul_opow ht k)
      _ ≈ t * geom t p := geom_comm (Comm.refl t) p
      _ ≈ geom t p := mul_geom_self ht

/-- `geom t p · Σ_k (−1)^k t^k ≈ geom t p` when `t^p ≈ 1` and `p` is odd. -/
theorem geom_mul_alternating {p κ : Nat} [Pos p] {g : Shell p} (F : Shell.Frame p κ g) {t : R} (ht : opow t p ≈ 1) :
    geom t p * osum (fun k => opow (-1) k * opow t k) p ≈ geom t p := by
  have hp : p = 2 * (2 * κ) + 1 := by rw [F.cap, ← Nat.mul_assoc]
  calc geom t p * osum (fun k => opow (-1) k * opow t k) p
      ≈ osum (fun k => geom t p * (opow (-1) k * opow t k)) p := osum_mul_left _ _ _
    _ ≈ osum (fun k => opow (-1) k * geom t p) p := by
        refine osum_congr _ fun k _ => ?_
        calc geom t p * (opow (-1) k * opow t k) ≈ geom t p * opow (-1) k * opow t k := eq_symm (mul_assoc _ _ _)
          _ ≈ opow (-1) k * geom t p * opow t k :=
              mul_congr_left _ (eq_symm (Central.opow (Central.neg Central.one) k _))
          _ ≈ opow (-1) k * (geom t p * opow t k) := mul_assoc _ _ _
          _ ≈ opow (-1) k * geom t p := mul_congr_right _ (geom_mul_opow ht k)
    _ ≈ osum (fun k => opow (-1) k) p * geom t p := eq_symm (osum_mul_right _ _ _)
    _ ≈ 1 * geom t p := mul_congr_left _ (by rw [hp]; exact osum_alternating _)
    _ ≈ geom t p := one_mul _

/-- 8:D20 — the exact index in `0+1`, the identity: for a translation `t` of order `p` with inverse `s` in characteristic
`p` on a frame, `(t − s)^{p−1} ≈ geom t p`, the sum of the translates, and `(t − s)^p ≈ 0`. The symmetric difference
`∇^s = h (t − s)` with `h` a central unit has the same index: `(∇^s)^{p−1} ≈ h^{p−1} geom t p`, nonzero whenever the sum
of the translates is, and `(∇^s)^p ≈ 0`. -/
theorem symdiff_pred_eq_geom {p κ : Nat} [Pos p] {g : Shell p} (F : Shell.Frame p κ g) (hch : nsmul p (1 : R) ≈ 0)
    {t s : R} (ht : opow t p ≈ 1) (hs : Inverse t s) : opow (t + -s) (p - 1) ≈ geom t p := by
  have hp : p = (p - 1) + 1 := (FRC.Nat.sub_add_cancel (Pos.pos : 0 < p)).symm
  have hts : Comm t s := eq_trans hs.1 (eq_symm hs.2)
  have hc1 : Comm (t + -s) t := Comm.add_left (Comm.refl t) (Comm.neg_left hts.symm)
  -- `(t − s) t ≈ (t − 1)(t + 1)`
  have hfac : (t + -s) * t ≈ (t + -1) * (t + 1) := by
    have h1 : t * t + t ≈ t * (t + 1) := eq_symm (eq_trans (left_distrib t t 1) (add_congr_right _ (mul_one t)))
    have h2 : -t + -1 ≈ -1 * (t + 1) :=
      eq_symm (eq_trans (eq_symm (neg_mul 1 (t + 1))) (eq_trans (neg_congr (one_mul (t + 1))) (neg_add_rev t 1)))
    calc (t + -s) * t ≈ t * t + -s * t := right_distrib _ _ _
      _ ≈ t * t + -1 := add_congr_right _ (eq_trans (eq_symm (neg_mul _ _)) (neg_congr hs.2))
      _ ≈ t * t + (t + -t) + -1 := add_congr_left _ (eq_symm (eq_trans (add_congr_right _ (add_neg t)) (add_zero _)))
      _ ≈ t * t + t + (-t + -1) :=
          eq_trans (add_assoc _ _ _) (eq_trans (add_congr_right _ (add_assoc _ _ _)) (eq_symm (add_assoc _ _ _)))
      _ ≈ t * (t + 1) + -1 * (t + 1) := add_congr h1 h2
      _ ≈ (t + -1) * (t + 1) := eq_symm (right_distrib _ _ _)
  -- `(t − s)^{p−1} t^{p−1} ≈ (t − 1)^{p−1} (t + 1)^{p−1} ≈ geom · Σ(−1)^k t^k ≈ geom`
  have hpow : opow (t + -s) (p - 1) * opow t (p - 1) ≈ geom t p :=
    calc opow (t + -s) (p - 1) * opow t (p - 1) ≈ opow ((t + -s) * t) (p - 1) := eq_symm (mul_opow hc1 _)
      _ ≈ opow ((t + -1) * (t + 1)) (p - 1) := opow_congr hfac _
      _ ≈ opow (t + -1) (p - 1) * opow (t + 1) (p - 1) :=
          mul_opow (Comm.add_left (Comm.add_right (Comm.refl t) (Comm.one_left t).symm)
            (Comm.neg_left (Comm.add_right (Comm.one_left t) (Comm.refl 1)))) _
      _ ≈ geom t p * osum (fun k => opow (-1) k * opow t k) p :=
          mul_congr (opow_sub_one_pred F hch t) (opow_add_one_pred F hch t)
      _ ≈ geom t p := geom_mul_alternating F ht
  -- multiply by `t`: `t^{p−1} t ≈ 1`
  calc opow (t + -s) (p - 1) ≈ opow (t + -s) (p - 1) * 1 := eq_symm (mul_one _)
    _ ≈ opow (t + -s) (p - 1) * (opow t (p - 1) * t) := mul_congr_right _ (eq_symm (eq_trans (eq_of_eq (by rw [← opow_succ, ← hp])) ht))
    _ ≈ opow (t + -s) (p - 1) * opow t (p - 1) * t := eq_symm (mul_assoc _ _ _)
    _ ≈ geom t p * t := mul_congr_left t hpow
    _ ≈ t * geom t p := geom_comm (Comm.refl t) p
    _ ≈ geom t p := mul_geom_self ht

/-- The `d`-fold Frobenius `x ↦ x^{p^d}` is additive on commuting elements in characteristic `p`, by induction on `d`
from `frobenius_add`. -/
theorem frobenius_pow {p κ : Nat} [Pos p] {g : Shell p} (F : Shell.Frame p κ g) (hch : nsmul p (1 : R) ≈ 0) {x y : R}
    (h : Comm x y) : ∀ d : Nat, opow (x + y) (p ^ d) ≈ opow x (p ^ d) + opow y (p ^ d)
  | 0 => by
    show opow (x + y) 1 ≈ opow x 1 + opow y 1
    exact eq_trans (opow_one _) (eq_symm (add_congr (opow_one x) (opow_one y)))
  | d + 1 => by
    rw [Nat.pow_succ]
    calc opow (x + y) (p ^ d * p) ≈ opow (opow (x + y) (p ^ d)) p := opow_mul _ _ _
      _ ≈ opow (opow x (p ^ d) + opow y (p ^ d)) p := opow_congr (frobenius_pow F hch h d) p
      _ ≈ opow (opow x (p ^ d)) p + opow (opow y (p ^ d)) p :=
          frobenius_add F hch (opow_comm (opow_comm h (p ^ d)).symm (p ^ d)).symm
      _ ≈ opow x (p ^ d * p) + opow y (p ^ d * p) := add_congr (eq_symm (opow_mul _ _ _)) (eq_symm (opow_mul _ _ _))

/-- Inverses are unique up to the congruence: two inverses of congruent elements are congruent. -/
theorem Inverse.unique {u u' v v' : R} (hu : u ≈ u') (h : Inverse u v) (h' : Inverse u' v') : v ≈ v' :=
  calc v ≈ v * 1 := eq_symm (mul_one v)
    _ ≈ v * (u' * v') := mul_congr_right v (eq_symm h'.1)
    _ ≈ v * (u * v') := mul_congr_right v (mul_congr_left v' (eq_symm hu))
    _ ≈ v * u * v' := eq_symm (mul_assoc _ _ _)
    _ ≈ 1 * v' := mul_congr_left v' h.2
    _ ≈ v' := one_mul v'

/-- `p^d` is odd on a frame's shell: `p = 4κ + 1`. -/
theorem pow_odd {p κ : Nat} [Pos p] {g : Shell p} (F : Shell.Frame p κ g) (d : Nat) : ∃ j, p ^ d = 2 * j + 1 := by
  have h1 : p % 2 = 1 := by
    rw [F.cap, show 4 * κ = 2 * (2 * κ) from Nat.mul_assoc 2 2 κ, FRC.Nat.add_mul_mod_self_left 1 (2 * κ) 2 (by decide)]
  have h2 : ∀ d, p ^ d % 2 = 1 := fun d => by
    induction d with
    | zero => rfl
    | succ d ih => rw [Nat.pow_succ, FRC.Nat.mul_mod _ _ _ (by decide), ih, h1]
  have h2 := h2 d
  obtain ⟨j, hj⟩ := FRC.Nat.mod_spec 2 (by decide) (p ^ d)
  exact ⟨j, by rw [hj, h2]⟩

/-- `(−1)^{p^d} ≈ −1` on a frame's shell. -/
theorem opow_neg_one_pow {p κ : Nat} [Pos p] {g : Shell p} (F : Shell.Frame p κ g) (d : Nat) :
    opow (-1 : R) (p ^ d) ≈ -1 := by
  obtain ⟨j, hj⟩ := pow_odd F d
  rw [hj]; exact opow_neg_one_odd j

/-- The Frobenius of the two Cayley factors: with `α^{p^d} ≈ ε α` (`ε = ±1`, central) and `λ^{p^d} ≈ λ`,
`(1 + αλ)^{p^d} ≈ 1 + ε αλ` and `(1 − αλ)^{p^d} ≈ 1 − ε αλ`. -/
theorem cayley_factor_frobenius {p κ : Nat} [Pos p] {g : Shell p} (F : Shell.Frame p κ g) (hch : nsmul p (1 : R) ≈ 0)
    {α lam ε : R} (hc : Comm α lam) {d : Nat} (hα : opow α (p ^ d) ≈ ε * α)
    (hl : opow lam (p ^ d) ≈ lam) :
    opow (1 + α * lam) (p ^ d) ≈ 1 + ε * (α * lam) ∧ opow (1 + -(α * lam)) (p ^ d) ≈ 1 + -(ε * (α * lam)) := by
  have hal : opow (α * lam) (p ^ d) ≈ ε * (α * lam) :=
    calc opow (α * lam) (p ^ d) ≈ opow α (p ^ d) * opow lam (p ^ d) := mul_opow hc _
      _ ≈ ε * α * lam := mul_congr hα hl
      _ ≈ ε * (α * lam) := mul_assoc _ _ _
  refine ⟨?_, ?_⟩
  · calc opow (1 + α * lam) (p ^ d) ≈ opow 1 (p ^ d) + opow (α * lam) (p ^ d) := frobenius_pow F hch (Comm.one_left _) d
      _ ≈ 1 + ε * (α * lam) := add_congr (opow_one_left _) hal
  · calc opow (1 + -(α * lam)) (p ^ d) ≈ opow 1 (p ^ d) + opow (-(α * lam)) (p ^ d) :=
          frobenius_pow F hch (Comm.one_left _) d
      _ ≈ 1 + opow (-1 * (α * lam)) (p ^ d) := add_congr (opow_one_left _) (opow_congr (eq_symm (neg_one_mul _)) _)
      _ ≈ 1 + opow (-1) (p ^ d) * opow (α * lam) (p ^ d) :=
          add_congr_right _ (mul_opow (Central.neg Central.one _) _)
      _ ≈ 1 + -1 * (ε * (α * lam)) := add_congr_right _ (mul_congr (opow_neg_one_pow F d) hal)
      _ ≈ 1 + -(ε * (α * lam)) := add_congr_right _ (neg_one_mul _)

/-- 8:E9 — the eigenphase law, the even case, in every operator ring of characteristic `p` on a frame: for commuting
`α`, `λ` with `α^{p^d} ≈ α` and `λ^{p^d} ≈ λ`, and `v` the inverse of `1 − αλ`, the phase `φ = (1 + αλ) v` is fixed by
the `d`-fold Frobenius, `φ^{p^d} ≈ φ`. (On the shell, `α = k w` has `α^{p^d} = α` exactly for even `d`, and an eigenvalue
of degree `d` has `λ^{p^d} = λ`.) -/
theorem eigenphase_frobenius_even {p κ : Nat} [Pos p] {g : Shell p} (F : Shell.Frame p κ g) (hch : nsmul p (1 : R) ≈ 0)
    {α lam v : R} (hc : Comm α lam) {d : Nat} (hα : opow α (p ^ d) ≈ α) (hl : opow lam (p ^ d) ≈ lam)
    (hv : Inverse (1 + -(α * lam)) v) : opow ((1 + α * lam) * v) (p ^ d) ≈ (1 + α * lam) * v := by
  have hα' : opow α (p ^ d) ≈ 1 * α := eq_trans hα (eq_symm (one_mul α))
  obtain ⟨h1, h2⟩ := cayley_factor_frobenius F hch hc hα' hl
  have hu : Comm (1 + -(α * lam)) (1 + α * lam) :=
    Comm.add_left (Comm.one_left _) (Comm.neg_left (Comm.add_right (Comm.one_left _).symm (Comm.refl _)))
  have hcv : Comm (1 + α * lam) v := (Inverse.comm_of_comm hv hu).symm
  have hvN : opow v (p ^ d) ≈ v :=
    Inverse.unique (eq_trans h2 (add_congr_right 1 (neg_congr (one_mul _)))) (inverse_opow hv (p ^ d)) hv
  calc opow ((1 + α * lam) * v) (p ^ d) ≈ opow (1 + α * lam) (p ^ d) * opow v (p ^ d) := mul_opow hcv _
    _ ≈ (1 + 1 * (α * lam)) * v := mul_congr h1 hvN
    _ ≈ (1 + α * lam) * v := mul_congr_left v (add_congr_right 1 (one_mul _))

/-- 8:E9 — the eigenphase law, the odd case, in every operator ring of characteristic `p` on a frame: for commuting
`α`, `λ` with `α^{p^d} ≈ −α` and `λ^{p^d} ≈ λ`, and `v`, `v'` the inverses of `1 − αλ` and `1 + αλ`, the phase
`φ = (1 + αλ) v` is inverted by the `d`-fold Frobenius, `φ^{p^d} φ ≈ 1`, so `φ^{p^d + 1} ≈ 1`: the phase lies on the
norm-one cycle of the Frobenius. (On the shell, `α = k w` has `α^{p^d} = −α` exactly for odd `d`.) -/
theorem eigenphase_frobenius_odd {p κ : Nat} [Pos p] {g : Shell p} (F : Shell.Frame p κ g) (hch : nsmul p (1 : R) ≈ 0)
    {α lam v v' : R} (hc : Comm α lam) {d : Nat} (hα : opow α (p ^ d) ≈ -α) (hl : opow lam (p ^ d) ≈ lam)
    (hv : Inverse (1 + -(α * lam)) v) (hv' : Inverse (1 + α * lam) v') :
    opow ((1 + α * lam) * v) (p ^ d) * ((1 + α * lam) * v) ≈ 1 ∧ opow ((1 + α * lam) * v) (p ^ d + 1) ≈ 1 := by
  have hα' : opow α (p ^ d) ≈ -1 * α := eq_trans hα (eq_symm (neg_one_mul α))
  obtain ⟨h1, h2⟩ := cayley_factor_frobenius F hch hc hα' hl
  have hu : Comm (1 + -(α * lam)) (1 + α * lam) :=
    Comm.add_left (Comm.one_left _) (Comm.neg_left (Comm.add_right (Comm.one_left _).symm (Comm.refl _)))
  have hcv : Comm (1 + α * lam) v := (Inverse.comm_of_comm hv hu).symm
  -- `(1 + αλ)^{p^d} ≈ 1 − αλ` and `(1 − αλ)^{p^d} ≈ 1 + αλ`
  have h1' : opow (1 + α * lam) (p ^ d) ≈ 1 + -(α * lam) :=
    eq_trans h1 (add_congr_right 1 (eq_trans (eq_symm (neg_mul _ _)) (neg_congr (one_mul _))))
  have h2' : opow (1 + -(α * lam)) (p ^ d) ≈ 1 + α * lam :=
    eq_trans h2 (add_congr_right 1 (eq_trans (neg_congr (eq_trans (eq_symm (neg_mul _ _)) (neg_congr (one_mul _)))) (neg_neg _)))
  -- `v^{p^d}` is the inverse of `(1 − αλ)^{p^d} ≈ 1 + αλ`, hence congruent to `v'`
  have hvN : opow v (p ^ d) ≈ v' := Inverse.unique h2' (inverse_opow hv (p ^ d)) hv'
  have hmain : opow ((1 + α * lam) * v) (p ^ d) * ((1 + α * lam) * v) ≈ 1 :=
    calc opow ((1 + α * lam) * v) (p ^ d) * ((1 + α * lam) * v)
        ≈ opow (1 + α * lam) (p ^ d) * opow v (p ^ d) * ((1 + α * lam) * v) := mul_congr_left _ (mul_opow hcv _)
      _ ≈ (1 + -(α * lam)) * v' * ((1 + α * lam) * v) := mul_congr_left _ (mul_congr h1' hvN)
      _ ≈ (1 + -(α * lam)) * (v' * (1 + α * lam)) * v :=
          eq_trans (eq_symm (mul_assoc _ _ _)) (mul_congr_left v (mul_assoc _ _ _))
      _ ≈ (1 + -(α * lam)) * 1 * v := mul_congr_left v (mul_congr_right _ hv'.2)
      _ ≈ (1 + -(α * lam)) * v := mul_congr_left v (mul_one _)
      _ ≈ 1 := hv.1
  exact ⟨hmain, eq_trans (eq_of_eq (opow_succ _ _)) hmain⟩

/-- 8:E9 — the Cayley map is injective, as two relations: for `φ = (1 + αλ) v` with `v` the inverse of `1 − αλ` and
without a commutation hypothesis, `φ + 1 ≈ v + v` and `αλ (φ + 1) ≈ φ − 1`. Read in a field of characteristic `p` containing `α`
and `φ`: `φ + 1 = 2v` is a unit, so `λ = (φ − 1)/(α(φ + 1))` lies in that field. A phase in `𝔽_p` or in `K` has its
eigenvalue there, and a phase of degree three or more lies in neither. -/
theorem cayley_phase_inverse {α lam v : R} (hv : Inverse (1 + -(α * lam)) v) :
    (1 + α * lam) * v + 1 ≈ v + v ∧ α * lam * ((1 + α * lam) * v + 1) ≈ (1 + α * lam) * v + -1 := by
  -- `(1 + αλ) v + (1 − αλ) v ≈ v + v`
  have hsum : (1 + α * lam) * v + 1 ≈ v + v :=
    calc (1 + α * lam) * v + 1 ≈ (1 + α * lam) * v + (1 + -(α * lam)) * v := add_congr_right _ (eq_symm hv.1)
      _ ≈ (1 + α * lam + (1 + -(α * lam))) * v := eq_symm (right_distrib _ _ _)
      _ ≈ (1 + 1) * v := mul_congr_left v (by
          calc 1 + α * lam + (1 + -(α * lam)) ≈ 1 + 1 + (α * lam + -(α * lam)) := add_add_add_comm _ _ _ _
            _ ≈ 1 + 1 + 0 := add_congr_right _ (add_neg _)
            _ ≈ 1 + 1 := add_zero _)
      _ ≈ 1 * v + 1 * v := right_distrib _ _ _
      _ ≈ v + v := add_congr (one_mul v) (one_mul v)
  -- `(1 + αλ) v − (1 − αλ) v ≈ (αλ + αλ) v`
  have hdiff : (1 + α * lam) * v + -1 ≈ (α * lam + α * lam) * v :=
    calc (1 + α * lam) * v + -1 ≈ (1 + α * lam) * v + -((1 + -(α * lam)) * v) := add_congr_right _ (neg_congr (eq_symm hv.1))
      _ ≈ (1 + α * lam) * v + -(1 + -(α * lam)) * v := add_congr_right _ (neg_mul _ _)
      _ ≈ (1 + α * lam + -(1 + -(α * lam))) * v := eq_symm (right_distrib _ _ _)
      _ ≈ (α * lam + α * lam) * v := mul_congr_left v (by
          calc 1 + α * lam + -(1 + -(α * lam)) ≈ 1 + α * lam + (-1 + - -(α * lam)) := add_congr_right _ (neg_add_rev _ _)
            _ ≈ 1 + α * lam + (-1 + α * lam) := add_congr_right _ (add_congr_right _ (neg_neg _))
            _ ≈ 1 + -1 + (α * lam + α * lam) := add_add_add_comm _ _ _ _
            _ ≈ 0 + (α * lam + α * lam) := add_congr_left _ (add_neg _)
            _ ≈ α * lam + α * lam := zero_add _)
  refine ⟨hsum, ?_⟩
  calc α * lam * ((1 + α * lam) * v + 1) ≈ α * lam * (v + v) := mul_congr_right _ hsum
    _ ≈ α * lam * v + α * lam * v := left_distrib _ _ _
    _ ≈ (α * lam + α * lam) * v := eq_symm (right_distrib _ _ _)
    _ ≈ (1 + α * lam) * v + -1 := eq_symm hdiff

/-! ## The exact index on two coordinate directions (D20): the generic identities -/

/-- A sum with one surviving term: if every other term vanishes, `Σ_{j<n} f j ≈ f k₀`. -/
theorem osum_eq_single {f : Nat → R} : ∀ n k0, k0 < n → (∀ j, j < n → j ≠ k0 → f j ≈ 0) → osum f n ≈ f k0
  | 0, k0, hk, _ => absurd hk (Nat.not_lt_zero k0)
  | n + 1, k0, hk, h =>
    match Nat.decEq k0 n with
    | isTrue e =>
      have hz : osum f n ≈ 0 :=
        osum_eq_zero n fun j hj => h j (Nat.lt_succ_of_lt hj) (fun ej => absurd (ej.trans e) (Nat.ne_of_lt hj))
      calc osum f n + f n ≈ 0 + f n := add_congr_left _ hz
        _ ≈ f n := zero_add _
        _ ≈ f k0 := eq_of_eq (by rw [e])
    | isFalse ne =>
      have hk' : k0 < n := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hk) ne
      have hz : f n ≈ 0 := h n (Nat.lt_succ_self n) (fun e => ne e.symm)
      calc osum f n + f n ≈ f k0 + 0 :=
            add_congr (osum_eq_single n k0 hk' fun j hj hj' => h j (Nat.lt_succ_of_lt hj) hj') hz
        _ ≈ f k0 := add_zero _

/-- `(η d²)^j ≈ η^j d^{j+j}` for central `η`. -/
theorem opow_central_sq {η d : R} (hη : Central η) (j : Nat) : opow (η * (d * d)) j ≈ opow η j * opow d (j + j) :=
  calc opow (η * (d * d)) j ≈ opow η j * opow (d * d) j := mul_opow (hη _) j
    _ ≈ opow η j * (opow d j * opow d j) := mul_congr_right _ (mul_opow (Comm.refl d) j)
    _ ≈ opow η j * opow d (j + j) := mul_congr_right _ (eq_symm (opow_add d j j))

/-- A power `d^{m}` with `m ≥ p` vanishes when `d^p ≈ 0`. -/
theorem opow_eq_zero_of_le {d : R} {p : Nat} (hn : opow d p ≈ 0) {m : Nat} (hm : p ≤ m) : opow d m ≈ 0 := by
  have e : p + (m - p) = m := FRC.Nat.add_sub_of_le hm
  rw [← e]; exact opow_eq_zero_of hn _

/-- 8:D20 — the `(p−1)`-st power of the square on two coordinate directions. For commuting `d₀`, `d₁` with `d_μ^p ≈ 0`
and central `η₀`, `η₁`, on a frame `p = 4κ + 1`: of the binomial terms of `(η₀ d₀² + η₁ d₁²)^{p−1}` only `k = 2κ`
survives (every other term carries a power `d_μ^{m}` with `m ≥ p`), and `C(p−1, 2κ) ≡ (−1)^{2κ} = 1`:
`(η₀ d₀² + η₁ d₁²)^{p−1} ≈ η₀^{2κ} η₁^{2κ} d₀^{p−1} d₁^{p−1}`. -/
theorem box_two_pow_pred {p κ : Nat} [Pos p] {g : Shell p} (F : Shell.Frame p κ g) (hch : nsmul p (1 : R) ≈ 0)
    {d0 d1 η0 η1 : R} (h01 : Comm d0 d1) (hη0 : Central η0) (hη1 : Central η1)
    (hn0 : opow d0 p ≈ 0) (hn1 : opow d1 p ≈ 0) :
    opow (η0 * (d0 * d0) + η1 * (d1 * d1)) (p - 1) ≈
      opow η0 (2 * κ) * opow η1 (2 * κ) * (opow d0 (p - 1) * opow d1 (p - 1)) := by
  have hp : p - 1 = 4 * κ := by rw [F.cap, FRC.Nat.add_sub_cancel]
  have hp1 : p - 1 + 1 = p := FRC.Nat.sub_add_cancel (Pos.pos : 0 < p)
  have hab : Comm (η0 * (d0 * d0)) (η1 * (d1 * d1)) :=
    Comm.mul_left (hη0 _) (Comm.mul_left (Comm.mul_right (Comm.symm (hη1 d0)) (Comm.mul_right h01 h01))
      (Comm.mul_right (Comm.symm (hη1 d0)) (Comm.mul_right h01 h01)))
  have hk0 : 2 * κ < p := by
    rw [F.cap]; exact Nat.lt_succ_of_le (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_of_eq (show 2 * κ + 2 * κ = 4 * κ by rw [← FRC.Nat.add_mul])))
  -- the term `j` of the binomial sum
  have hterm : ∀ j, j < p → j ≠ 2 * κ → nsmul (choose (p - 1) j) (opow (η0 * (d0 * d0)) j * opow (η1 * (d1 * d1)) (p - 1 - j)) ≈ 0 := by
    intro j hj hne
    apply nsmul_of_eq_zero
    cases Nat.lt_or_ge j (2 * κ) with
    | inr hge =>
      -- `j ≥ 2κ + 1`: `d₀^{j+j}` with `j + j ≥ p`
      have hj' : 2 * κ + 1 ≤ j := Nat.lt_of_le_of_ne hge (fun e => hne e.symm)
      have hjj : p ≤ j + j := by
        rw [F.cap]
        exact Nat.le_trans (Nat.le_of_eq (show 4 * κ + 1 = 2 * κ + (2 * κ + 1) by
          rw [show 4 * κ = 2 * κ + 2 * κ by rw [← FRC.Nat.add_mul], Nat.add_assoc])) (Nat.add_le_add hge hj')
      calc opow (η0 * (d0 * d0)) j * opow (η1 * (d1 * d1)) (p - 1 - j)
          ≈ opow η0 j * opow d0 (j + j) * opow (η1 * (d1 * d1)) (p - 1 - j) := mul_congr_left _ (opow_central_sq hη0 j)
        _ ≈ opow η0 j * 0 * opow (η1 * (d1 * d1)) (p - 1 - j) :=
            mul_congr_left _ (mul_congr_right _ (opow_eq_zero_of_le hn0 hjj))
        _ ≈ 0 * opow (η1 * (d1 * d1)) (p - 1 - j) := mul_congr_left _ (mul_zero _)
        _ ≈ 0 := zero_mul _
    | inl hlt =>
      -- `j ≤ 2κ − 1`: `m = p − 1 − j ≥ 2κ + 1`, `d₁^{m+m}` with `m + m ≥ p`
      have hm : 2 * κ + 1 ≤ p - 1 - j := by
        apply FRC.Nat.le_sub_of_add_le
        rw [hp, show 4 * κ = 2 * κ + 2 * κ by rw [← FRC.Nat.add_mul], Nat.add_assoc, Nat.add_comm 1 j]
        exact Nat.add_le_add_left hlt _
      have hsum : p ≤ 2 * κ + 1 + (2 * κ + 1) := by
        rw [F.cap, FRC.Nat.add_add_add_comm, ← FRC.Nat.add_mul]; exact Nat.le_succ _
      have hmm : p ≤ (p - 1 - j) + (p - 1 - j) := Nat.le_trans hsum (Nat.add_le_add hm hm)
      calc opow (η0 * (d0 * d0)) j * opow (η1 * (d1 * d1)) (p - 1 - j)
          ≈ opow (η0 * (d0 * d0)) j * (opow η1 (p - 1 - j) * opow d1 ((p - 1 - j) + (p - 1 - j))) :=
            mul_congr_right _ (opow_central_sq hη1 _)
        _ ≈ opow (η0 * (d0 * d0)) j * (opow η1 (p - 1 - j) * 0) :=
            mul_congr_right _ (mul_congr_right _ (opow_eq_zero_of_le hn1 hmm))
        _ ≈ opow (η0 * (d0 * d0)) j * 0 := mul_congr_right _ (mul_zero _)
        _ ≈ 0 := mul_zero _
  -- the surviving term `j = 2κ`
  have h2 : p - 1 - 2 * κ = 2 * κ := by
    rw [hp, show 4 * κ = 2 * κ + 2 * κ by rw [← FRC.Nat.add_mul], FRC.Nat.add_sub_cancel]
  have h4 : 2 * κ + 2 * κ = p - 1 := by rw [hp, ← FRC.Nat.add_mul]
  have hsurv : nsmul (choose (p - 1) (2 * κ)) (opow (η0 * (d0 * d0)) (2 * κ) * opow (η1 * (d1 * d1)) (p - 1 - 2 * κ)) ≈
      opow η0 (2 * κ) * opow η1 (2 * κ) * (opow d0 (p - 1) * opow d1 (p - 1)) := by
    rw [h2]
    calc nsmul (choose (p - 1) (2 * κ)) (opow (η0 * (d0 * d0)) (2 * κ) * opow (η1 * (d1 * d1)) (2 * κ))
        ≈ nsmul (choose (p - 1) (2 * κ)) 1 * (opow (η0 * (d0 * d0)) (2 * κ) * opow (η1 * (d1 * d1)) (2 * κ)) :=
          nsmul_eq_mul_one _ _
      _ ≈ 1 * (opow (η0 * (d0 * d0)) (2 * κ) * opow (η1 * (d1 * d1)) (2 * κ)) :=
          mul_congr_left _ (eq_trans (nsmul_choose_pred F hch _ hk0) (opow_neg_one_even κ))
      _ ≈ opow (η0 * (d0 * d0)) (2 * κ) * opow (η1 * (d1 * d1)) (2 * κ) := one_mul _
      _ ≈ opow η0 (2 * κ) * opow d0 (2 * κ + 2 * κ) * (opow η1 (2 * κ) * opow d1 (2 * κ + 2 * κ)) :=
          mul_congr (opow_central_sq hη0 _) (opow_central_sq hη1 _)
      _ ≈ opow η0 (2 * κ) * (opow d0 (2 * κ + 2 * κ) * opow η1 (2 * κ)) * opow d1 (2 * κ + 2 * κ) :=
          eq_trans (eq_symm (mul_assoc _ _ _)) (mul_congr_left _ (mul_assoc _ _ _))
      _ ≈ opow η0 (2 * κ) * (opow η1 (2 * κ) * opow d0 (2 * κ + 2 * κ)) * opow d1 (2 * κ + 2 * κ) :=
          mul_congr_left _ (mul_congr_right _ (eq_symm (Central.opow hη1 _ _)))
      _ ≈ opow η0 (2 * κ) * opow η1 (2 * κ) * (opow d0 (2 * κ + 2 * κ) * opow d1 (2 * κ + 2 * κ)) :=
          eq_trans (mul_congr_left _ (eq_symm (mul_assoc _ _ _))) (mul_assoc _ _ _)
      _ ≈ opow η0 (2 * κ) * opow η1 (2 * κ) * (opow d0 (p - 1) * opow d1 (p - 1)) := eq_of_eq (by rw [h4])
  calc opow (η0 * (d0 * d0) + η1 * (d1 * d1)) (p - 1) ≈ binom (η0 * (d0 * d0)) (η1 * (d1 * d1)) (p - 1) := binomial hab _
    _ ≈ osum (fun k => nsmul (choose (p - 1) k) (opow (η0 * (d0 * d0)) k * opow (η1 * (d1 * d1)) (p - 1 - k))) p :=
        eq_of_eq (by show binom _ _ _ = osum _ _; unfold binom; rw [hp1])
    _ ≈ nsmul (choose (p - 1) (2 * κ)) (opow (η0 * (d0 * d0)) (2 * κ) * opow (η1 * (d1 * d1)) (p - 1 - 2 * κ)) :=
        osum_eq_single p (2 * κ) hk0 hterm
    _ ≈ opow η0 (2 * κ) * opow η1 (2 * κ) * (opow d0 (p - 1) * opow d1 (p - 1)) := hsurv

/-- 8:D20 — on two coordinate directions `(η₀ d₀² + η₁ d₁²)^{p−1}` is killed by either difference:
`□^{p−1} d₀ ≈ 0` and `□^{p−1} d₁ ≈ 0`, since the surviving term carries `d₀^{p−1} d₁^{p−1}`. -/
theorem box_two_pow_pred_mul {p κ : Nat} [Pos p] {g : Shell p} (F : Shell.Frame p κ g) (hch : nsmul p (1 : R) ≈ 0)
    {d0 d1 η0 η1 : R} (h01 : Comm d0 d1) (hη0 : Central η0) (hη1 : Central η1)
    (hn0 : opow d0 p ≈ 0) (hn1 : opow d1 p ≈ 0) :
    opow (η0 * (d0 * d0) + η1 * (d1 * d1)) (p - 1) * d0 ≈ 0 ∧ opow (η0 * (d0 * d0) + η1 * (d1 * d1)) (p - 1) * d1 ≈ 0 := by
  have hp1 : p - 1 + 1 = p := FRC.Nat.sub_add_cancel (Pos.pos : 0 < p)
  have hb := box_two_pow_pred F hch h01 hη0 hη1 hn0 hn1
  have h0p : opow d0 (p - 1) * d0 ≈ 0 := eq_trans (eq_of_eq (by rw [← opow_succ, hp1])) hn0
  have h1p : opow d1 (p - 1) * d1 ≈ 0 := eq_trans (eq_of_eq (by rw [← opow_succ, hp1])) hn1
  refine ⟨?_, ?_⟩
  · calc opow (η0 * (d0 * d0) + η1 * (d1 * d1)) (p - 1) * d0
        ≈ opow η0 (2 * κ) * opow η1 (2 * κ) * (opow d0 (p - 1) * opow d1 (p - 1)) * d0 := mul_congr_left _ hb
      _ ≈ opow η0 (2 * κ) * opow η1 (2 * κ) * (opow d0 (p - 1) * (opow d1 (p - 1) * d0)) :=
          eq_trans (mul_assoc _ _ _) (mul_congr_right _ (mul_assoc _ _ _))
      _ ≈ opow η0 (2 * κ) * opow η1 (2 * κ) * (opow d0 (p - 1) * (d0 * opow d1 (p - 1))) :=
          mul_congr_right _ (mul_congr_right _ (opow_comm h01.symm _))
      _ ≈ opow η0 (2 * κ) * opow η1 (2 * κ) * (opow d0 (p - 1) * d0 * opow d1 (p - 1)) :=
          mul_congr_right _ (eq_symm (mul_assoc _ _ _))
      _ ≈ opow η0 (2 * κ) * opow η1 (2 * κ) * (0 * opow d1 (p - 1)) := mul_congr_right _ (mul_congr_left _ h0p)
      _ ≈ opow η0 (2 * κ) * opow η1 (2 * κ) * 0 := mul_congr_right _ (zero_mul _)
      _ ≈ 0 := mul_zero _
  · calc opow (η0 * (d0 * d0) + η1 * (d1 * d1)) (p - 1) * d1
        ≈ opow η0 (2 * κ) * opow η1 (2 * κ) * (opow d0 (p - 1) * opow d1 (p - 1)) * d1 := mul_congr_left _ hb
      _ ≈ opow η0 (2 * κ) * opow η1 (2 * κ) * (opow d0 (p - 1) * (opow d1 (p - 1) * d1)) :=
          eq_trans (mul_assoc _ _ _) (mul_congr_right _ (mul_assoc _ _ _))
      _ ≈ opow η0 (2 * κ) * opow η1 (2 * κ) * (opow d0 (p - 1) * 0) := mul_congr_right _ (mul_congr_right _ h1p)
      _ ≈ opow η0 (2 * κ) * opow η1 (2 * κ) * 0 := mul_congr_right _ (mul_zero _)
      _ ≈ 0 := mul_zero _

/-- The square of a Dirac operator on two directions, as a sum of two terms: `𝒟² ≈ η₀ ∇₀² + η₁ ∇₁²`. -/
theorem dirac_two_square {del γ η : Nat → R}
    (hdd : ∀ μ ν, μ < 2 → ν < 2 → Comm (del μ) (del ν)) (hdg : ∀ μ ν, μ < 2 → ν < 2 → Comm (del μ) (γ ν))
    (hgg : ∀ μ ν, μ < 2 → ν < 2 → μ ≠ ν → Anticomm (γ μ) (γ ν)) (hsq : ∀ μ, μ < 2 → γ μ * γ μ ≈ η μ)
    (hη : ∀ μ, μ < 2 → Central (η μ)) :
    opow (osum (fun μ => del μ * γ μ) 2) 2 ≈ η 0 * (del 0 * del 0) + η 1 * (del 1 * del 1) :=
  calc opow (osum (fun μ => del μ * γ μ) 2) 2
      ≈ osum (fun μ => del μ * γ μ) 2 * osum (fun μ => del μ * γ μ) 2 := mul_congr_left _ (opow_one _)
    _ ≈ osum (fun μ => η μ * (del μ * del μ)) 2 := dirac_square hdd hdg hgg hsq hη
    _ ≈ η 0 * (del 0 * del 0) + η 1 * (del 1 * del 1) := add_congr_left _ (zero_add _)

/-- 8:D20 — the exact index on two coordinate directions, the upper bound: for `𝒟 = ∇₀ γ₀ + ∇₁ γ₁` as in `dirac_square`
with `∇_μ^p ≈ 0`, on a frame, `𝒟^{2(p−1)} ≈ η₀^{2κ} η₁^{2κ} ∇₀^{p−1} ∇₁^{p−1}` and `𝒟^{2(p−1)+1} ≈ 0`: the index is at
most `2p − 1`, and `𝒟^{2p−2}` vanishes exactly when `∇₀^{p−1} ∇₁^{p−1}` does (the `η_μ` being units). -/
theorem dirac_two_index {p κ : Nat} [Pos p] {g : Shell p} (F : Shell.Frame p κ g) (hch : nsmul p (1 : R) ≈ 0)
    {del γ η : Nat → R}
    (hdd : ∀ μ ν, μ < 2 → ν < 2 → Comm (del μ) (del ν)) (hdg : ∀ μ ν, μ < 2 → ν < 2 → Comm (del μ) (γ ν))
    (hgg : ∀ μ ν, μ < 2 → ν < 2 → μ ≠ ν → Anticomm (γ μ) (γ ν)) (hsq : ∀ μ, μ < 2 → γ μ * γ μ ≈ η μ)
    (hη : ∀ μ, μ < 2 → Central (η μ)) (hnil : ∀ μ, μ < 2 → opow (del μ) p ≈ 0) :
    opow (osum (fun μ => del μ * γ μ) 2) (2 * (p - 1)) ≈
        opow (η 0) (2 * κ) * opow (η 1) (2 * κ) * (opow (del 0) (p - 1) * opow (del 1) (p - 1)) ∧
      opow (osum (fun μ => del μ * γ μ) 2) (2 * (p - 1) + 1) ≈ 0 := by
  have h01 : Comm (del 0) (del 1) := hdd 0 1 (by decide) (by decide)
  have hη0 : Central (η 0) := hη 0 (by decide)
  have hη1 : Central (η 1) := hη 1 (by decide)
  have hn0 : opow (del 0) p ≈ 0 := hnil 0 (by decide)
  have hn1 : opow (del 1) p ≈ 0 := hnil 1 (by decide)
  have heven : opow (osum (fun μ => del μ * γ μ) 2) (2 * (p - 1)) ≈
      opow (η 0 * (del 0 * del 0) + η 1 * (del 1 * del 1)) (p - 1) :=
    eq_trans (opow_mul _ 2 (p - 1)) (opow_congr (dirac_two_square hdd hdg hgg hsq hη) (p - 1))
  obtain ⟨hk0, hk1⟩ := box_two_pow_pred_mul F hch h01 hη0 hη1 hn0 hn1
  refine ⟨eq_trans heven (box_two_pow_pred F hch h01 hη0 hη1 hn0 hn1), ?_⟩
  calc opow (osum (fun μ => del μ * γ μ) 2) (2 * (p - 1) + 1)
      ≈ opow (osum (fun μ => del μ * γ μ) 2) (2 * (p - 1)) * osum (fun μ => del μ * γ μ) 2 := eq_refl _
    _ ≈ opow (η 0 * (del 0 * del 0) + η 1 * (del 1 * del 1)) (p - 1) * (del 0 * γ 0 + del 1 * γ 1) :=
        mul_congr heven (add_congr_left _ (zero_add _))
    _ ≈ opow (η 0 * (del 0 * del 0) + η 1 * (del 1 * del 1)) (p - 1) * (del 0 * γ 0) +
          opow (η 0 * (del 0 * del 0) + η 1 * (del 1 * del 1)) (p - 1) * (del 1 * γ 1) := left_distrib _ _ _
    _ ≈ opow (η 0 * (del 0 * del 0) + η 1 * (del 1 * del 1)) (p - 1) * del 0 * γ 0 +
          opow (η 0 * (del 0 * del 0) + η 1 * (del 1 * del 1)) (p - 1) * del 1 * γ 1 :=
        add_congr (eq_symm (mul_assoc _ _ _)) (eq_symm (mul_assoc _ _ _))
    _ ≈ 0 * γ 0 + 0 * γ 1 := add_congr (mul_congr_left _ hk0) (mul_congr_left _ hk1)
    _ ≈ 0 + 0 := add_congr (zero_mul _) (zero_mul _)
    _ ≈ 0 := zero_add 0

/-- `2p − 1 = 2(p − 1) + 1` on a frame, so `dirac_two_index` reads `𝒟^{2p−1} ≈ 0`. -/
theorem two_mul_sub_one {p κ : Nat} [Pos p] {g : Shell p} (F : Shell.Frame p κ g) : 2 * p - 1 = 2 * (p - 1) + 1 := by
  rw [F.cap, FRC.Nat.add_sub_cancel, Nat.mul_succ]
  exact FRC.Nat.add_sub_cancel (2 * (4 * κ) + 1) 1

end FRC.Dirac.Operator
