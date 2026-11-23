import FrcCore.Theme.Shift
import FrcCore.Theme.Field

/-!
# FrcCore.Theme.Lattice — difference operators on the cycle (the gravity theme; 21-gravity, 10 October 2026)

On the cycle of `n` sites (`FRC.Cycle.cyc`, the fourier theme's `Theme/Shift.lean`): the central difference
`(Δf)(i) = f(i + 1) − f(i − 1)` is anti-self-adjoint, `Σ_i (Δf)(i) g(i) = −Σ_i f(i) (Δg)(i)`
(`central_difference_adjoint`, 21:C9) — the identity carrying the exact gauge invariance of the discrete Fierz–Pauli
functional, whose symbol lines are `Theme/Symbol.lean`'s (00:E1); the one-sided difference's adjoint is the negative
backward difference (`forward_difference_adjoint`); and the cycle Laplacian `f(i + 1) + f(i − 1) − 2f(i)` acts on the
character `χ_k(i) = g^{ki}` as the symbol `g^k + g^{−k} − 2` (`laplacian_symbol`, 21:C15; the pattern of 8:F4). The
sums are reindexed by the cycle's shift (`sum_shift`). The central difference acts on the same character as the symbol
`g^k − g^{−k}` (`cdiff_symbol`), which vanishes exactly when `g^{2k} = 1` (`cdiff_symbol_zero_iff`), and on an odd prime
cycle `2k ≡ 0` forces `k ≡ 0` (`two_mul_mod_odd_prime`): the exponent face of the cyclotomic zero set of 21:C15, whose
characteristic-zero statement is FrcMathlib's `FRC.Strong.central_symbol_nonzero` (21 November 2026). No axioms.
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

/-- 21:C15, 21:C10, 21:X5 — on a character `g` with `gⁿ = 1`, the cycle Laplacian acts on `χ_k` as the symbol
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

/-! ## The central difference on the character and its zero set (21:C15; 21 November 2026) -/

/-- 21:C15 — the central difference acts on the character `χ_k` as the symbol `g^k − g^{k(n−1)}` (`g^{−k}` on the
cycle): `(Δχ_k)(i) = (g^k − g^{k(n−1)}) χ_k(i)` for `gⁿ = 1`. The `𝔽_p`-valued statement; the cyclotomic one is
FrcMathlib's `FRC.Strong.central_symbol_nonzero`. -/
theorem cdiff_symbol (n : Nat) (hn : 0 < n) {g : Shell p} (hg : g ^ n = 1) (k i : Nat) :
    cdiff n (chi n g k) i = (g ^ k + -(g ^ (k * (n - 1)))) * chi n g k i := by
  have hk : (g ^ k) ^ n = 1 := by rw [pow_mul_comm, hg, one_pow]
  have e1 : cyc n (chi n g k) (i + 1) = g ^ k * chi n g k i := by
    rw [chi_cyc n hn]
    show g ^ (k * ((i + 1) % n)) = g ^ k * g ^ (k * (i % n))
    rw [pow_mul, pow_mul, ← pow_mod n hn hk (i + 1), ← pow_mod n hn hk i, pow_succ, mul_comm]
  have e2 : cyc n (chi n g k) (i + (n - 1)) = g ^ (k * (n - 1)) * chi n g k i := by
    rw [chi_cyc n hn]
    show g ^ (k * ((i + (n - 1)) % n)) = g ^ (k * (n - 1)) * g ^ (k * (i % n))
    rw [pow_mul, pow_mul, pow_mul, ← pow_mod n hn hk (i + (n - 1)), ← pow_mod n hn hk i, pow_add, mul_comm]
  show cyc n (chi n g k) (i + 1) + -(cyc n (chi n g k) (i + (n - 1))) = _
  rw [e1, e2, right_distrib, neg_mul]

/-- `g^{k(n−1)} · g^k = 1` for `gⁿ = 1`, `n > 0`: the two factors of the symbol are inverse. -/
theorem symbol_factors_inverse (n : Nat) (hn : 0 < n) {g : Shell p} (hg : g ^ n = 1) (k : Nat) :
    g ^ (k * (n - 1)) * g ^ k = 1 := by
  have e : k * (n - 1) + k = n * k := by
    calc k * (n - 1) + k = k * (n - 1 + 1) := by rw [Nat.mul_succ]
      _ = k * n := by rw [FRC.Nat.sub_add_cancel (Nat.succ_le_of_lt hn)]
      _ = n * k := Nat.mul_comm k n
  rw [← pow_add, e, pow_mul, hg, one_pow]

/-- 21:C15 — the zero set of the central-difference symbol: `g^k − g^{k(n−1)} = 0` exactly when `g^{2k} = 1`
(for `gⁿ = 1`, `n > 0`). -/
theorem cdiff_symbol_zero_iff (n : Nat) (hn : 0 < n) {g : Shell p} (hg : g ^ n = 1) (k : Nat) :
    g ^ k + -(g ^ (k * (n - 1))) = 0 ↔ g ^ (2 * k) = 1 := by
  have hu := symbol_factors_inverse n hn hg k
  have two : g ^ (2 * k) = g ^ k * g ^ k := by rw [Nat.two_mul, pow_add]
  constructor
  · intro h
    have e : g ^ k = g ^ (k * (n - 1)) := by
      have h' := eq_neg_of_add_eq_zero h
      rw [h', neg_neg]
    calc g ^ (2 * k) = g ^ k * g ^ k := two
      _ = g ^ (k * (n - 1)) * g ^ k := congrArg (fun x => x * g ^ k) e
      _ = 1 := hu
  · intro h
    have e : g ^ k = g ^ (k * (n - 1)) := by
      calc g ^ k = g ^ k * 1 := (mul_one _).symm
        _ = g ^ k * (g ^ (k * (n - 1)) * g ^ k) := by rw [hu]
        _ = g ^ (k * (n - 1)) * (g ^ k * g ^ k) := mul_left_comm _ _ _
        _ = g ^ (k * (n - 1)) * g ^ (2 * k) := by rw [← two]
        _ = g ^ (k * (n - 1)) := by rw [h, mul_one]
    rw [e]; exact add_neg _

/-- 21:C15 — the transport identity at the symbol (the quarter of Proposition 7.5(ii); 21 November 2026): the square of
the central-difference symbol at `k` is the Laplacian's symbol at `2k`, `(g^k − g^{−k})² = g^{2k} + g^{−2k} − 2` for
`gⁿ = 1`. With the paper's central difference `D = (T − T⁻¹)/2`, which carries one half per step, this reads
`K = −D² = ¼ P⁻¹ L P` for the relabelling `P : x ↦ 2x`: the quarter is the two halves. -/
theorem transport_symbol (n : Nat) (hn : 0 < n) {g : Shell p} (hg : g ^ n = 1) (k : Nat) :
    (g ^ k + -(g ^ (k * (n - 1)))) * (g ^ k + -(g ^ (k * (n - 1)))) =
      g ^ (2 * k) + g ^ ((2 * k) * (n - 1)) + -(1 + 1) := by
  have hu := symbol_factors_inverse n hn hg k
  have hu' : g ^ k * g ^ (k * (n - 1)) = 1 := by rw [mul_comm]; exact hu
  have e1 : g ^ k * g ^ k = g ^ (2 * k) := by rw [Nat.two_mul, pow_add]
  have e2 : g ^ (k * (n - 1)) * g ^ (k * (n - 1)) = g ^ ((2 * k) * (n - 1)) := by
    rw [FRC.Nat.mul_assoc, Nat.two_mul, pow_add]
  calc (g ^ k + -(g ^ (k * (n - 1)))) * (g ^ k + -(g ^ (k * (n - 1))))
      = g ^ k * g ^ k + g ^ k * -(g ^ (k * (n - 1))) + (-(g ^ (k * (n - 1))) * g ^ k + -(g ^ (k * (n - 1))) * -(g ^ (k * (n - 1)))) := by
        rw [right_distrib, left_distrib, left_distrib]
    _ = g ^ (2 * k) + -1 + (-1 + g ^ ((2 * k) * (n - 1))) := by
        rw [e1, ← mul_neg, hu', ← neg_mul, hu, ← neg_mul, ← mul_neg, neg_neg, e2]
    _ = g ^ (2 * k) + g ^ ((2 * k) * (n - 1)) + -(1 + 1) := by
        rw [neg_add_rev, add_assoc, add_assoc, add_left_comm (-1) (-1) _, ← add_assoc (-1) (-1), add_comm (-1 + -1)]

/-- 21:C15 — on an odd prime cycle the exponent `2k` vanishes exactly when `k` does: `(2k) % q = 0 ↔ k % q = 0` for
`q` prime with `2 % q ≠ 0`. With `ζ` of order `q` this is the cyclotomic zero set `{k : ζ^{2k} = 1} = {k : q ∣ k}`. -/
theorem two_mul_mod_odd_prime {q k : Nat} (hq : FRC.Nat.isPrime q) (h2 : 2 % q ≠ 0) : (2 * k) % q = 0 ↔ k % q = 0 := by
  constructor
  · intro h
    rcases FRC.Nat.prime_mul_mod hq h with h2' | hk
    · exact absurd h2' h2
    · exact hk
  · intro h
    have hq0 : 0 < q := Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) hq.1
    rw [Nat.mul_comm 2 k, FRC.Nat.mul_mod k 2 q hq0, h, Nat.zero_mul, FRC.Nat.zero_mod q]

end FRC.Lattice
