import FrcCore.Theme.Lattice
import FrcCore.Theme.Drift

/-!
# FrcCore.Theme.Relaxation — the Kuramoto form as exact identities on the cycle (the gravity theme; 26 October 2026)

The exact finite skeleton of 21-gravity's relaxation dynamics (Lemma lem:pairtally, Theorem thm:indrelax, equation
eq:kuramoto, Lemma pre:unit), stated on every shell with no continuum and no axioms; the rows 21:C1, C9, C22, C26
and C27 cite it. Python: `frc/drift.py` (`tally_gradient`, `odd_kernels`, `pulse_sequence`) and `frc/lattice.py`
(`bdiff_fdiff_identity`, `leakage_form_identity`).

* `tally_gradient` — the oriented mate `z − z⁻¹` of the pair tally `W(z) = 2 + z + z⁻¹` is the tally's centred
  difference along the drive: `W(zg) − W(zg⁻¹) = (g − g⁻¹)(z − z⁻¹)`. The Kuramoto current is the gradient of the
  coincidence tally, exactly; `sin` is its chart.
* `failure_norm` — the failure tally `E(z) = 2 − z − z⁻¹` is the norm of the link mismatch, `(1 − z)(1 − z⁻¹)`
  (`E + W = 4` is `Drift.tally_weight`).
* `odd_kernel_is_cdiff` — an adjacency-local shift-invariant kernel that is odd under edge reversal is a multiple of
  the central difference; `odd_kernel_coeffs` — oddness forces the centre coefficient to vanish on every frame.
* `bdiff_fdiff` and `leakage_contraction` — the adjoint composite of the forward difference (the incidence map) is
  the cycle Laplacian, and the leakage quadratic form `Σ (∂f)²` is `−Σ f Δf`: the linearised Kuramoto relaxation is
  the Laplacian flow, with the quadratic free energy its exact quadratic form.
* `pulse_law` — unit capacity: a transfer of `M ≤ N` quanta over `N` chronons is realised by the balanced pulse
  sequence `s(k) = ⌊kM/N⌋`, whose increments are `0` or `1` and whose total is `M`; the mean rate `M/N` is the
  observer's reading of the current.

What is not here, by the framework's own doctrine: the continuous-time equation and "to first order" (the chart), and
the direction of relaxation (an order on counts, which the shell does not carry; it lives on the readout window's
coincidence counts, 22:C7, C10). The prelude's `Nat` division and subtraction lemmas carry `propext`, so the pulse law
is stated with quotient and remainder as hypotheses and proved with the shell's `FRC.Nat.mod_spec`; the prelude's
`Nat.lt_of_mul_lt_mul_right` is classical, so `lt_of_mul_lt_mul_right'` restates it.
-/

namespace FRC.Relaxation

open FRC.Shell FRC.Shell.Frame FRC.Cycle FRC.Lattice

variable {p : Nat} [Pos p]

/-! ## The pair tally and its oriented mate (21:C1, lem:pairtally) -/

/-- The pair tally `W(z) = 2 + z + w` with `w` the inverse phase ratio. -/
def tally (z w : Shell p) : Shell p := 1 + 1 + z + w

/-- The failure tally `E(z) = 2 − z − w`. -/
def failure (z w : Shell p) : Shell p := 1 + 1 + -z + -w

/-- The oriented mate `z − w`, the Kuramoto current up to the frame constant `2i`. -/
def current (z w : Shell p) : Shell p := z + -w

/-- 21:C1, 21:C22, 21:C26 — the current is the centred drive-difference of the tally: with `h = g⁻¹` the one-chronon
drive step, `W(zg) − W(zg⁻¹) = (g − g⁻¹)(z − z⁻¹)`. Exact on every shell; `sin` is the chart reading of the right-hand
side (lem:pairtally). -/
theorem tally_gradient (z w g h : Shell p) :
    tally (z * g) (w * h) + -(tally (z * h) (w * g)) = (g + -h) * current z w := by
  unfold tally current
  exact RE.sound (look [z, w, g, h])
    (.add (.add (.add (.add .one .one) (.mul (.var 0) (.var 2))) (.mul (.var 1) (.var 3)))
      (.neg (.add (.add (.add .one .one) (.mul (.var 0) (.var 3))) (.mul (.var 1) (.var 2)))))
    (.mul (.add (.var 2) (.neg (.var 3))) (.add (.var 0) (.neg (.var 1))))
    (by decide +kernel)

/-- 21:C26 — the failure tally is the norm of the link mismatch: `(1 − z)(1 − z⁻¹) = 2 − z − z⁻¹` when `z z⁻¹ = 1`;
the quadratic free energy of lem:gradient is its chart. -/
theorem failure_norm (z w : Shell p) (hzw : z * w = 1) : (1 + -z) * (1 + -w) = failure z w := by
  unfold failure
  have e : (1 + -z) * (1 + -w) = 1 + -z + -w + z * w :=
    RE.sound (look [z, w])
      (.mul (.add .one (.neg (.var 0))) (.add .one (.neg (.var 1))))
      (.add (.add (.add .one (.neg (.var 0))) (.neg (.var 1))) (.mul (.var 0) (.var 1)))
      (by decide +kernel)
  rw [e, hzw]
  exact RE.sound (look [z, w])
    (.add (.add (.add .one (.neg (.var 0))) (.neg (.var 1))) .one)
    (.add (.add (.add .one .one) (.neg (.var 0))) (.neg (.var 1)))
    (by decide +kernel)

/-! ## The leakage map: locality, shift invariance, edge reversal (thm:indrelax, the linear level) -/

/-- An adjacency-local shift-invariant kernel on the cycle: `(Tf)(i) = a f(i + 1) + b f(i) + c f(i − 1)`. -/
def kernel (n : Nat) (a b c : Shell p) (f : Nat → Shell p) (i : Nat) : Shell p :=
  a * cyc n f (i + 1) + b * cyc n f i + c * cyc n f (i + (n - 1))

/-- Edge reversal sends the kernel `(a, b, c)` to `(c, b, a)`; a kernel is odd when the reversed kernel is its negative:
`(c, b, a) = (−a, −b, −c)`. -/
def Odd (a b c : Shell p) : Prop := c = -a ∧ b = -b

/-- Oddness forces the centre coefficient to vanish on every frame (`2b = 0 ⇒ b = 0`) and the end coefficients to be
opposite. -/
theorem odd_kernel_coeffs {κ : Nat} {g : Shell p} (F : Frame p κ g) {a b c : Shell p} (h : Odd a b c) :
    b = 0 ∧ c = -a :=
  ⟨F.eq_zero_of_eq_neg h.2, h.1⟩

/-- 21:C9, 21:C22, 21:C26 — an odd adjacency-local shift-invariant kernel is a multiple of the central difference:
the leading leakage map of thm:indrelax is forced to `α B` by locality, shift invariance and edge reversal. -/
theorem odd_kernel_is_cdiff {κ : Nat} {g : Shell p} (F : Frame p κ g) (n : Nat) {a b c : Shell p} (h : Odd a b c)
    (f : Nat → Shell p) (i : Nat) : kernel n a b c f i = a * cdiff n f i := by
  rcases odd_kernel_coeffs F h with ⟨hb, hc⟩
  unfold kernel cdiff
  rw [hb, hc]
  exact RE.sound (look [a, cyc n f (i + 1), cyc n f i, cyc n f (i + (n - 1))])
    (.add (.add (.mul (.var 0) (.var 1)) (.mul .zero (.var 2))) (.mul (.neg (.var 0)) (.var 3)))
    (.mul (.var 0) (.add (.var 1) (.neg (.var 3))))
    (by decide +kernel)

/-- 21:C9, 21:C22 — the adjoint composite of the forward difference is the cycle Laplacian, `∂̄ ∂ f = Δ f`: the
leading contraction `C₁†C₁ = |α|² L` of thm:indrelax. -/
theorem bdiff_fdiff (n : Nat) (hn : 0 < n) (f : Nat → Shell p) (i : Nat) :
    bdiff n (fdiff n f) i = lap n f i := by
  unfold bdiff lap
  have h1 : cyc n (fdiff n f) i = cyc n f (i + 1) + -(cyc n f i) := by
    show fdiff n f (i % n) = _
    unfold fdiff
    rw [cyc_add_mod n hn, cyc_mod n hn]
  have h2 : cyc n (fdiff n f) (i + (n - 1)) = cyc n f i + -(cyc n f (i + (n - 1))) := by
    show fdiff n f ((i + (n - 1)) % n) = _
    unfold fdiff
    rw [cyc_add_mod n hn, cyc_mod n hn]
    have e : i + (n - 1) + 1 = i + n := by
      rw [Nat.add_assoc, FRC.Nat.sub_add_cancel (Nat.succ_le_of_lt hn)]
    rw [e, cyc_add_n n hn]
  rw [h1, h2]
  exact RE.sound (look [cyc n f (i + 1), cyc n f i, cyc n f (i + (n - 1))])
    (.add (.add (.var 0) (.neg (.var 1))) (.neg (.add (.var 1) (.neg (.var 2)))))
    (.add (.add (.var 0) (.var 2)) (.neg (.mul (.add .one .one) (.var 1))))
    (by decide +kernel)

/-- 21:C1, 21:C22 — thm:indrelax at the linear level: the leakage quadratic form is the Laplacian form,
`Σ (∂f)² = −Σ f Δf`. The quadratic free energy of lem:gradient is this identity read on the chart. -/
theorem leakage_contraction (n : Nat) (hn : 0 < n) (f : Nat → Shell p) :
    sumRange (fun i => fdiff n f i * fdiff n f i) n = -(sumRange (fun i => cyc n f i * lap n f i) n) := by
  have A : sumRange (fun i => fdiff n f i * fdiff n f i) n = sumRange (fun i => fdiff n f i * cyc n (fdiff n f) i) n := by
    apply sum_congr; intro i hi
    have : cyc n (fdiff n f) i = fdiff n f i := by
      show fdiff n f (i % n) = fdiff n f i
      unfold fdiff; rw [cyc_add_mod n hn, cyc_mod n hn]
    rw [this]
  rw [A, forward_difference_adjoint n hn f (fdiff n f)]
  congr 1
  apply sum_congr; intro i hi
  rw [bdiff_fdiff n hn f i]

/-! ## Unit capacity: the pulse law (pre:unit) -/

/-- `a c < b c ⇒ a < b`, without the classical lemma of the prelude. -/
theorem lt_of_mul_lt_mul_right' {a b c : Nat} (h : a * c < b * c) : a < b := by
  cases Nat.lt_or_ge a b with
  | inl hab => exact hab
  | inr hba => exact absurd (Nat.lt_of_lt_of_le h (Nat.mul_le_mul_right c hba)) (Nat.lt_irrefl _)

/-- The balanced pulse count at chronon `k` of a transfer of `M` quanta over `N` chronons is the quotient `s` of
`k M = s N + r`, `r < N` (it exists and is unique by the shell's own division, `FRC.Nat.mod_spec`, `mod_unique`).
Two consecutive quotients differ by at most one when `M ≤ N`: each chronon carries at most one quantum, and none is
returned. No division and no subtraction are used. -/
theorem pulse_increment {N M k s r s' r' : Nat} (hM : M ≤ N)
    (h1 : s * N + r = k * M) (hr : r < N) (h2 : s' * N + r' = (k + 1) * M) (hr' : r' < N) :
    s ≤ s' ∧ s' ≤ s + 1 := by
  constructor
  · -- `s N ≤ k M ≤ (k + 1) M = s' N + r' < (s' + 1) N`
    have a1 : s * N ≤ k * M := by rw [← h1]; exact Nat.le_add_right _ _
    have a2 : k * M ≤ (k + 1) * M := by rw [Nat.succ_mul]; exact Nat.le_add_right _ _
    have a3 : (k + 1) * M < (s' + 1) * N := by
      rw [← h2, Nat.succ_mul]; exact Nat.add_lt_add_left hr' _
    exact Nat.le_of_lt_succ (lt_of_mul_lt_mul_right' (Nat.lt_of_le_of_lt (Nat.le_trans a1 a2) a3))
  · -- `s' N ≤ (k + 1) M = k M + M ≤ s N + r + N < (s + 2) N`
    have b1 : s' * N ≤ (k + 1) * M := by rw [← h2]; exact Nat.le_add_right _ _
    have b2 : (k + 1) * M ≤ s * N + r + N := by
      rw [Nat.succ_mul, h1]; exact Nat.add_le_add_left hM _
    have b3 : s * N + r + N < (s + 1 + 1) * N := by
      rw [Nat.succ_mul, Nat.succ_mul, Nat.add_assoc (s * N) N N, Nat.add_assoc (s * N) r N]
      exact Nat.add_lt_add_left (Nat.add_lt_add_right hr N) _
    exact Nat.le_of_lt_succ (lt_of_mul_lt_mul_right' (Nat.lt_of_le_of_lt (Nat.le_trans b1 b2) b3))

/-- The whole transfer is delivered over the window: at `k = N` the quotient is `M`. -/
theorem pulse_total {N M s r : Nat} (h1 : s * N + r = N * M) (hr : r < N) : s = M := by
  apply Nat.le_antisymm
  · have a1 : s * N ≤ M * N := by rw [Nat.mul_comm M N, ← h1]; exact Nat.le_add_right _ _
    cases Nat.lt_or_ge M s with
    | inl hMs => exact absurd (Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le hMs (Nat.le_refl N) (Nat.lt_of_le_of_lt (Nat.zero_le r) hr)) a1) (Nat.lt_irrefl _)
    | inr hsM => exact hsM
  · have b1 : M * N < (s + 1) * N := by
      rw [Nat.mul_comm M N, ← h1, Nat.succ_mul]; exact Nat.add_lt_add_left hr _
    exact Nat.le_of_lt_succ (lt_of_mul_lt_mul_right' b1)

/-- 21:C27 — the pulse law: the quotients `s_k` of `k M = s_k N + r_k` exist for every `k`, rise by at most one per
chronon and reach `M` at `k = N`: unit capacity (pre:unit) realises any transfer `M ≤ N` as a balanced sequence of
unit pulses, the Christoffel word of lem:isopair, whose mean rate `M/N` is the chart's reading of the current. -/
theorem pulse_law (N M : Nat) (hN : 0 < N) (hM : M ≤ N) :
    (∀ k, ∃ s r, s * N + r = k * M ∧ r < N) ∧
    (∀ k s r s' r', s * N + r = k * M → r < N → s' * N + r' = (k + 1) * M → r' < N → s ≤ s' ∧ s' ≤ s + 1) ∧
    (∀ s r, s * N + r = N * M → r < N → s = M) := by
  refine ⟨?_, fun k s r s' r' h1 hr h2 hr' => pulse_increment hM h1 hr h2 hr', fun s r h1 hr => pulse_total h1 hr⟩
  intro k
  rcases FRC.Nat.mod_spec N hN (k * M) with ⟨q, hq⟩
  exact ⟨q, k * M % N, by rw [Nat.mul_comm q N]; exact hq.symm, FRC.Nat.mod_lt' _ hN⟩

end FRC.Relaxation
