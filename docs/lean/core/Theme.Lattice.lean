import FrcCore.Theme.Shift

/-!
# FrcCore.Theme.Lattice — difference operators on the cycle (the gravity theme; 21-gravity, 10 October 2026)

On the cycle of `n` sites (`FRC.Cycle.cyc`, the fourier theme's `Theme/Shift.lean`): the central difference
`(Δf)(i) = f(i + 1) − f(i − 1)` is anti-self-adjoint, `Σ_i (Δf)(i) g(i) = −Σ_i f(i) (Δg)(i)`
(`central_difference_adjoint`, 21:C9) — the identity carrying the exact gauge invariance of the discrete Fierz–Pauli
functional, whose symbol lines are `Theme/Symbol.lean`'s (00:E1); the one-sided difference's adjoint is the negative
backward difference (`forward_difference_adjoint`); and the cycle Laplacian `f(i + 1) + f(i − 1) − 2f(i)` acts on the
character `χ_k(i) = g^{ki}` as the symbol `g^k + g^{−k} − 2` (`laplacian_symbol`, 21:C15; the pattern of 8:F4). The
sums are reindexed by the cycle's shift (`sum_shift`). No axioms.
-/

namespace FRC.Lattice

open FRC.Shell FRC.Cycle

variable {p : Nat} [Pos p]

/-- The central difference on the cycle: `(Δf)(i) = f(i + 1) − f(i − 1)`, with `i − 1` read as `i + (n − 1)`. -/
def cdiff (n : Nat) (f : Nat → Shell p) (i : Nat) : Shell p := cyc n f (i + 1) + -(cyc n f (i + (n - 1)))

/-- The forward difference `(∂f)(i) = f(i + 1) − f(i)` and the backward difference `(∂̄f)(i) = f(i) − f(i − 1)`. -/
def fdiff (n : Nat) (f : Nat → Shell p) (i : Nat) : Shell p := cyc n f (i + 1) + -(cyc n f i)
def bdiff (n : Nat) (f : Nat → Shell p) (i : Nat) : Shell p := cyc n f i + -(cyc n f (i + (n - 1)))

/-- The cycle Laplacian `(Δ_Φ f)(i) = f(i + 1) + f(i − 1) − 2 f(i)`. -/
def lap (n : Nat) (f : Nat → Shell p) (i : Nat) : Shell p :=
  cyc n f (i + 1) + cyc n f (i + (n - 1)) + -((1 + 1) * cyc n f i)

/-- `Σ_i f(i + 1) g(i) = Σ_i f(i) g(i + (n − 1))` on the cycle: the summation by parts. -/
theorem sum_shift_pair (n : Nat) (hn : 0 < n) (f g : Nat → Shell p) :
    sumRange (fun i => cyc n f (i + 1) * cyc n g i) n = sumRange (fun i => cyc n f i * cyc n g (i + (n - 1))) n := by
  rw [← sum_shift n hn (fun i => cyc n f (i + 1) * cyc n g i) (n - 1)]
  apply sum_congr; intro j _
  show cyc n f ((j + (n - 1)) % n + 1) * cyc n g ((j + (n - 1)) % n) = cyc n f j * cyc n g (j + (n - 1))
  rw [cyc_add_mod n hn, cyc_mod n hn]
  have e : j + (n - 1) + 1 = j + n := by
    rw [Nat.add_assoc, FRC.Nat.sub_add_cancel (Nat.succ_le_of_lt hn)]
  rw [e, cyc_add_n n hn]

/-- 21:C9 — the central difference is anti-self-adjoint on the cycle: `Σ_i (Δf)(i) g(i) = −Σ_i f(i) (Δg)(i)`. -/
theorem central_difference_adjoint (n : Nat) (hn : 0 < n) (f g : Nat → Shell p) :
    sumRange (fun i => cdiff n f i * cyc n g i) n = -(sumRange (fun i => cyc n f i * cdiff n g i) n) := by
  have L : sumRange (fun i => cdiff n f i * cyc n g i) n =
      sumRange (fun i => cyc n f (i + 1) * cyc n g i) n + -(sumRange (fun i => cyc n f (i + (n - 1)) * cyc n g i) n) := by
    rw [← sum_neg, ← sum_add]; apply sum_congr; intro l _; simp only [cdiff]; rw [right_distrib, neg_mul]
  have R : sumRange (fun i => cyc n f i * cdiff n g i) n =
      sumRange (fun i => cyc n f i * cyc n g (i + 1)) n + -(sumRange (fun i => cyc n f i * cyc n g (i + (n - 1))) n) := by
    rw [← sum_neg, ← sum_add]; apply sum_congr; intro l _; simp only [cdiff]; rw [left_distrib, mul_neg]
  have A := sum_shift_pair n hn f g
  have B : sumRange (fun i => cyc n f (i + (n - 1)) * cyc n g i) n = sumRange (fun i => cyc n f i * cyc n g (i + 1)) n := by
    have h := sum_shift_pair n hn g f
    calc sumRange (fun i => cyc n f (i + (n - 1)) * cyc n g i) n
        = sumRange (fun i => cyc n g i * cyc n f (i + (n - 1))) n := sum_congr n (fun i _ => mul_comm _ _)
      _ = sumRange (fun i => cyc n g (i + 1) * cyc n f i) n := h.symm
      _ = sumRange (fun i => cyc n f i * cyc n g (i + 1)) n := sum_congr n (fun i _ => mul_comm _ _)
  rw [L, R, A, B, neg_add_rev, neg_neg, add_comm]

/-- 21:C9 — the adjoint of the forward difference is the negative backward difference:
`Σ_i (∂f)(i) g(i) = −Σ_i f(i) (∂̄g)(i)`. -/
theorem forward_difference_adjoint (n : Nat) (hn : 0 < n) (f g : Nat → Shell p) :
    sumRange (fun i => fdiff n f i * cyc n g i) n = -(sumRange (fun i => cyc n f i * bdiff n g i) n) := by
  have L : sumRange (fun i => fdiff n f i * cyc n g i) n =
      sumRange (fun i => cyc n f (i + 1) * cyc n g i) n + -(sumRange (fun i => cyc n f i * cyc n g i) n) := by
    rw [← sum_neg, ← sum_add]; apply sum_congr; intro l _; simp only [fdiff]; rw [right_distrib, neg_mul]
  have R : sumRange (fun i => cyc n f i * bdiff n g i) n =
      sumRange (fun i => cyc n f i * cyc n g i) n + -(sumRange (fun i => cyc n f i * cyc n g (i + (n - 1))) n) := by
    rw [← sum_neg, ← sum_add]; apply sum_congr; intro l _; simp only [bdiff]; rw [left_distrib, mul_neg]
  rw [L, R, sum_shift_pair n hn f g, neg_add_rev, neg_neg, add_comm]

/-! ## The character and the Laplacian's symbol (21:C15) -/

/-- The character `χ_k(i) = g^{ki}` on the cycle, read mod `n`. -/
def chi (n : Nat) (g : Shell p) (k : Nat) (i : Nat) : Shell p := g ^ (k * (i % n))

theorem chi_cyc (n : Nat) (hn : 0 < n) (g : Shell p) (k i : Nat) : cyc n (chi n g k) i = chi n g k i := by
  show g ^ (k * (i % n % n)) = g ^ (k * (i % n)); rw [FRC.Nat.mod_mod i n hn]

/-- 21:C15 — on a character `g` with `gⁿ = 1`, the cycle Laplacian acts on `χ_k` as the symbol
`g^k + g^{k(n−1)} − 2` (`g^{k(n−1)} = g^{−k}` on the cycle): `(Δ_Φ χ_k)(i) = (g^k + g^{−k} − 2) χ_k(i)`,
the dispersion relation `2 − g^k − g^{−k}` of 8:F4, whose chart is `2 − 2 cos k = 4 sin²(k/2)`. -/
theorem laplacian_symbol (n : Nat) (hn : 0 < n) {g : Shell p} (hg : g ^ n = 1) (k i : Nat) :
    lap n (chi n g k) i = (g ^ k + g ^ (k * (n - 1)) + -(1 + 1)) * chi n g k i := by
  have hk : (g ^ k) ^ n = 1 := by rw [pow_mul_comm, hg, one_pow]
  have e1 : cyc n (chi n g k) (i + 1) = g ^ k * chi n g k i := by
    rw [chi_cyc n hn]
    show g ^ (k * ((i + 1) % n)) = g ^ k * g ^ (k * (i % n))
    rw [pow_mul, pow_mul, ← pow_mod n hn hk (i + 1), ← pow_mod n hn hk i, pow_succ, mul_comm]
  have e2 : cyc n (chi n g k) (i + (n - 1)) = g ^ (k * (n - 1)) * chi n g k i := by
    rw [chi_cyc n hn]
    show g ^ (k * ((i + (n - 1)) % n)) = g ^ (k * (n - 1)) * g ^ (k * (i % n))
    rw [pow_mul, pow_mul, pow_mul, ← pow_mod n hn hk (i + (n - 1)), ← pow_mod n hn hk i, pow_add, mul_comm]
  show cyc n (chi n g k) (i + 1) + cyc n (chi n g k) (i + (n - 1)) + -((1 + 1) * cyc n (chi n g k) i) = _
  rw [e1, e2, chi_cyc n hn, right_distrib (g ^ k + g ^ (k * (n - 1))) (-(1 + 1)) (chi n g k i),
    right_distrib (g ^ k) (g ^ (k * (n - 1))) (chi n g k i), neg_mul]

end FRC.Lattice
