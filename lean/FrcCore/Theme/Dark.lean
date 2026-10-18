import FrcCore.Theme.Drift

/-!
# FrcCore.Theme.Dark — the dark theme: 32-dark's exact content (18 October 2026)

The dark sector of *The Dark Sector over Finite Relational Substrate* (32-dark), on the gravity theme's Gauss law
(`FRC.Drift.gauss_law`, 00:E3) and locked sum, the frame theme's vanishing cycle sum and the extension norm of
`Theme/Quadratic`. Every statement is on a shell `Shell p` or its quadratic extension `Ext p ν`; every proof is the
kernel's (`decide +kernel` through the normaliser `RE.sound`, with explicit cofactors for the identities that hold
modulo a hypothesis) or a structural induction, and no axiom enters.

* **The first-passage law (32:C7, B8, C6, X4).** With `z(f² + 1) = 2f` (the single-step generating factor of the
  first-passage quadratic), the sequence `u_k = f^k` satisfies the walk's recursion `z(u_{k−1} + u_{k+1}) = 2u_k` at
  every step (`passage_step`, `line_passage`), and so does the two-image sum `f^{·} + f^{N−·}` on the cycle `Z_N`
  (`cycle_passage`): divided by `1 + f^N` it is the exact escape transform with the absorbing point at distance
  `a` one way and `N − a` the other, the second image the wrap correction. Two distinct roots of the quadratic have
  `z(f + g) = 2` and `fg = 1` (`passage_vieta`): the second root is `1/f`, the long route round the cycle.
* **The deep regime (32:C4, C5, X3).** `s² = GMa₀` and `v² = s` give `v⁴ = GMa₀` (`tully_fisher`): the baryonic
  Tully–Fisher relation as a ring identity of the amplitude reading.
* **The amplitude identity (32:C3).** `N(a + b) + N(a − b) = 2N(a) + 2N(b)` (`parallelogram`); `n` copies of one
  phasor have norm `n² N(u)` (`coherent_stack`); the norms of the `2^n` signed sums add up to `2^n Σ N(u_k)`
  (`tot_eq`, `incoherent_mean`), so the mean squared amplitude of an incoherent ensemble of unit phasors is `n`, its
  amplitude `√n`.
* **The coherence sums (32:C10, X7, X8, P5, B9).** `(s₁ + s₂ + s₃)² = Σ s_i² + 2Σ_{i<j} s_i s_j` (`cohsum_three`), the
  amplitude law at `C_ij = 1`; `N` equal components give `(Σ s)² = N Σ s²` (`neff_equal`), `N_eff = N`.
* **The enclosed flux (32:C1, X1, C4).** For antisymmetric link currents with divergence `src`, the flux through a
  region's boundary is the enclosed source (`enclosed_flux`); a source-free current has zero flux (`source_free_flux`);
  fluxes superpose (`flux_superposition`). A unit source gives unit flux through every enclosing surface, and the
  floor noise, source-free, leaves the mean force unchanged.
-/

namespace FRC.Dark
open FRC.Shell FRC.Shell.Frame FRC.Extension FRC.Extension.Ext FRC.Drift

variable {p : Nat} [Pos p] {ν : Shell p}

/-- An identity modulo one hypothesis: from `L = R + A·X` and `A = 0`, `L = R`. -/
theorem red1 {L R A X : Shell p} (e : L = R + A * X) (ha : A = 0) : L = R := by
  rw [e, ha, zero_mul, add_zero]

/-- An identity modulo two hypotheses. -/
theorem red2 {L R A B X Y : Shell p} (e : L = R + A * X + B * Y) (ha : A = 0) (hb : B = 0) : L = R := by
  rw [e, ha, hb, zero_mul, zero_mul, add_zero, add_zero]

/-! ## The first-passage law on the cycle (32:C7, B8) -/

/-- 32:C7, 32:B8 — one step of the killed walk's recursion: if `z(f² + 1) = 2f` (the single-step generating factor `f` of the
first-passage quadratic `(z/2)f² − f + z/2 = 0`), then for every `t` (standing for `f^k`) `z(t + t f²) = 2 t f`:
the sequence `u_k = f^k` satisfies `z(u_{k−1} + u_{k+1}) = 2u_k`. -/
theorem passage_step (z f t : Shell p) (h : z * (f * f + 1) + -(f + f) = 0) :
    z * (t + t * f * f) = t * f + t * f :=
  red1 (RE.sound (look [z, f, t]) (.mul (.var 0) (.add (.var 2) (.mul (.mul (.var 2) (.var 1)) (.var 1)))) (.add (.add (.mul (.var 2) (.var 1)) (.mul (.var 2) (.var 1))) (.mul (.add (.mul (.var 0) (.add (.mul (.var 1) (.var 1)) .one)) (.neg (.add (.var 1) (.var 1)))) (.var 2))) (by decide +kernel) : z * (t + t * f * f) = t * f + t * f + (z * (f * f + 1) + -(f + f)) * t) h

/-- 32:C7, 32:C6, 32:X4 — the line solution: `u_k = f^k` solves the recursion at every interior step, `z(f^k + f^{k+2}) = 2 f^{k+1}`. -/
theorem line_passage (z f : Shell p) (h : z * (f * f + 1) + -(f + f) = 0) (k : Nat) :
    z * (f ^ k + f ^ (k + 2)) = f ^ (k + 1) + f ^ (k + 1) := by
  have e2 : f ^ (k + 2) = f ^ k * f * f := by rw [pow_succ, pow_succ]
  have e1 : f ^ (k + 1) = f ^ k * f := pow_succ f k
  rw [e2, e1]; exact passage_step z f (f ^ k) h

/-- 32:C7, 32:B8 — the two-image solution on the cycle `Z_N` with the absorbing point at distance `k+1` one way and `j+1` the
other (`N = k + j + 2`): `u = f^{·} + f^{N−·}` satisfies the same recursion, `z(u_{k} + u_{k+2}) = 2u_{k+1}`, written
with the two exponents `k, j`; the normalisation by `1 + f^N` makes the absorbing value one. -/
theorem cycle_passage (z f : Shell p) (h : z * (f * f + 1) + -(f + f) = 0) (k j : Nat) :
    z * ((f ^ k + f ^ (j + 2)) + (f ^ (k + 2) + f ^ j)) =
      (f ^ (k + 1) + f ^ (j + 1)) + (f ^ (k + 1) + f ^ (j + 1)) := by
  have hk := line_passage z f h k
  have hj := line_passage z f h j
  have e : (f ^ k + f ^ (j + 2)) + (f ^ (k + 2) + f ^ j) = (f ^ k + f ^ (k + 2)) + (f ^ j + f ^ (j + 2)) := by
    rw [add_add_add_comm, add_comm (f ^ (j + 2)) (f ^ j)]
  rw [e, left_distrib, hk, hj, add_add_add_comm]

/-- 32:C6, 32:X4, 32:C7 — Vieta for the first-passage quadratic: two distinct roots `f ≠ g` of `z(x² + 1) = 2x` have `z(f + g) = 2` and
`f g = 1` (`z ≠ 0`): the second root is `1/f`, the long route round the cycle. -/
theorem passage_vieta {κ : Nat} {g0 : Shell p} (F : Frame p κ g0) (z f g : Shell p) (hz : z ≠ 0) (hfg : f + -g ≠ 0)
    (h1 : z * (f * f + 1) + -(f + f) = 0) (h2 : z * (g * g + 1) + -(g + g) = 0) :
    z * (f + g) + -(1 + 1) = 0 ∧ f * g = 1 := by
  have s : z * ((f + g) * (f + -g)) = f + -g + (f + -g) :=
    red2 (RE.sound (look [z, f, g]) (.mul (.var 0) (.mul (.add (.var 1) (.var 2)) (.add (.var 1) (.neg (.var 2))))) (.add (.add (.add (.add (.var 1) (.neg (.var 2))) (.add (.var 1) (.neg (.var 2)))) (.mul (.add (.mul (.var 0) (.add (.mul (.var 1) (.var 1)) .one)) (.neg (.add (.var 1) (.var 1)))) .one)) (.mul (.add (.mul (.var 0) (.add (.mul (.var 2) (.var 2)) .one)) (.neg (.add (.var 2) (.var 2)))) (.neg .one))) (by decide +kernel) : z * ((f + g) * (f + -g)) = f + -g + (f + -g) + (z * (f * f + 1) + -(f + f)) * 1 + (z * (g * g + 1) + -(g + g)) * (-1)) h1 h2
  -- (z(f+g) − 2)(f − g) = 0, so z(f+g) = 2
  have s' : (z * (f + g) + -(1 + 1)) * (f + -g) = 0 := by
    have : (z * (f + g) + -(1 + 1)) * (f + -g) = z * ((f + g) * (f + -g)) + -(f + -g + (f + -g)) :=
      RE.sound (look [z, f, g]) (.mul (.add (.mul (.var 0) (.add (.var 1) (.var 2))) (.neg (.add .one .one))) (.add (.var 1) (.neg (.var 2)))) (.add (.mul (.var 0) (.mul (.add (.var 1) (.var 2)) (.add (.var 1) (.neg (.var 2))))) (.neg (.add (.add (.var 1) (.neg (.var 2))) (.add (.var 1) (.neg (.var 2)))))) (by decide +kernel)
    rw [this, s, add_neg]
  have h3 : z * (f + g) + -(1 + 1) = 0 := by
    rcases F.mul_eq_zero s' with h | h
    · exact h
    · exact absurd h hfg
  refine ⟨h3, ?_⟩
  have pz : z * (1 + -(f * g)) = 0 :=
    red2 (RE.sound (look [z, f, g]) (.mul (.var 0) (.add .one (.neg (.mul (.var 1) (.var 2))))) (.add (.add .zero (.mul (.add (.mul (.var 0) (.add (.mul (.var 1) (.var 1)) .one)) (.neg (.add (.var 1) (.var 1)))) .one)) (.mul (.add (.mul (.var 0) (.add (.var 1) (.var 2))) (.neg (.add .one .one))) (.neg (.var 1)))) (by decide +kernel) : z * (1 + -(f * g)) = 0 + (z * (f * f + 1) + -(f + f)) * 1 + (z * (f + g) + -(1 + 1)) * (-f)) h1 h3
  rcases F.mul_eq_zero pz with h | h
  · exact absurd h hz
  · -- 1 + -(f g) = 0, so f g = 1
    have e1 : (1 : Shell p) = f * g := by
      have := eq_neg_of_add_eq_zero h
      rw [this, neg_neg]
    exact e1.symm

/-! ## The deep regime and Tully–Fisher (32:C4, C5, X3) -/

/-- 32:C4, 32:C5, 32:X3 — the amplitude reading squared is the flux: with `s² = G M a₀` (the deep-regime registered force times `r`) and
`v² = s` (the circular speed, `v² = g r` with `g = s/r`), `v⁴ = G M a₀` — the baryonic Tully–Fisher relation as a
ring identity. -/
theorem tully_fisher (G M a r v s : Shell p) (hs : s * s + -(G * M * a) = 0) (hv : v * v + -s = 0) :
    v * v * v * v = G * M * a :=
  red2 (RE.sound (look [G, M, a, r, v, s]) (.mul (.mul (.mul (.var 4) (.var 4)) (.var 4)) (.var 4)) (.add (.add (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.mul (.add (.mul (.var 5) (.var 5)) (.neg (.mul (.mul (.var 0) (.var 1)) (.var 2)))) .one)) (.mul (.add (.mul (.var 4) (.var 4)) (.neg (.var 5))) (.add (.mul (.var 4) (.var 4)) (.var 5)))) (by decide +kernel) : v * v * v * v = G * M * a + (s * s + -(G * M * a)) * 1 + (v * v + -s) * (v * v + s)) hs hv

/-! ## The amplitude identity (32:C3) -/

/-- 32:C3 — the parallelogram law of the extension norm: `N(a + b) + N(a − b) = 2N(a) + 2N(b)` — the cross terms of two
phasors cancel between the two signs. -/
theorem parallelogram (a b : Ext p ν) :
    norm (a + b) + norm (a + -b) = (norm a + norm a) + (norm b + norm b) := by
  show (a.re + b.re) * (a.re + b.re) + -(ν * ((a.im + b.im) * (a.im + b.im))) + ((a.re + -b.re) * (a.re + -b.re) + -(ν * ((a.im + -b.im) * (a.im + -b.im)))) = a.re * a.re + -(ν * (a.im * a.im)) + (a.re * a.re + -(ν * (a.im * a.im))) + (b.re * b.re + -(ν * (b.im * b.im)) + (b.re * b.re + -(ν * (b.im * b.im))))
  exact RE.sound (look [a.re, a.im, b.re, b.im, ν]) (.add (.add (.mul (.add (.var 0) (.var 2)) (.add (.var 0) (.var 2))) (.neg (.mul (.var 4) (.mul (.add (.var 1) (.var 3)) (.add (.var 1) (.var 3)))))) (.add (.mul (.add (.var 0) (.neg (.var 2))) (.add (.var 0) (.neg (.var 2)))) (.neg (.mul (.var 4) (.mul (.add (.var 1) (.neg (.var 3))) (.add (.var 1) (.neg (.var 3)))))))) (.add (.add (.add (.mul (.var 0) (.var 0)) (.neg (.mul (.var 4) (.mul (.var 1) (.var 1))))) (.add (.mul (.var 0) (.var 0)) (.neg (.mul (.var 4) (.mul (.var 1) (.var 1)))))) (.add (.add (.mul (.var 2) (.var 2)) (.neg (.mul (.var 4) (.mul (.var 3) (.var 3))))) (.add (.mul (.var 2) (.var 2)) (.neg (.mul (.var 4) (.mul (.var 3) (.var 3))))))) (by decide +kernel)

/-- 32:C3, 32:C10 — the coherent stack: `n` copies of one phasor have norm `n²N(u)` (`norm_scale` with `c = ofNat n`). -/
theorem coherent_stack (u : Ext p ν) (n : Nat) : norm (ofShell (ofNat n) * u) = ofNat n * ofNat n * norm u :=
  norm_scale (ofNat n) u

/-- 32:C3 — the sum over all sign patterns of the norm of the signed sum: `tot acc us` branches on the sign of each phasor,
`tot acc [] = N(acc)`, `tot acc (u :: us) = tot (acc + u) us + tot (acc − u) us`, so `tot 0 us` is `Σ_ε N(Σ ε_k u_k)`
over the `2^n` patterns. -/
def tot (acc : Ext p ν) : List (Ext p ν) → Shell p
  | [] => norm acc
  | u :: us => tot (acc + u) us + tot (acc + -u) us

/-- 32:C3 — the sum of the norms of the phasors. -/
def normSum : List (Ext p ν) → Shell p
  | [] => 0
  | u :: us => norm u + normSum us

/-- 32:C3 — the pattern sum from any starting phasor: `tot acc us = 2^n (N(acc) + Σ N(u_k))`. -/
theorem tot_eq (us : List (Ext p ν)) : ∀ acc : Ext p ν, tot acc us = ofNat (2 ^ us.length) * (norm acc + normSum us) := by
  induction us with
  | nil =>
    intro acc
    show norm acc = ofNat 1 * (norm acc + 0)
    rw [add_zero, show (ofNat 1 : Shell p) = 1 from rfl, FRC.Shell.one_mul]
  | cons u us ih =>
    intro acc
    show tot (acc + u) us + tot (acc + -u) us = ofNat (2 ^ (us.length + 1)) * (norm acc + (norm u + normSum us))
    rw [ih (acc + u), ih (acc + -u)]
    have h2 : (ofNat (2 ^ (us.length + 1)) : Shell p) = ofNat (2 ^ us.length) + ofNat (2 ^ us.length) := by
      rw [Nat.pow_succ, Nat.mul_two, ← ofNat_add]
    rw [h2]
    have par := parallelogram acc u
    -- 2^n (N(acc+u) + S) + 2^n (N(acc−u) + S) = (2^n + 2^n)(N(acc) + N(u) + S), given the parallelogram law
    have e : ∀ c A B S Na Nu : Shell p, A + B = (Na + Na) + (Nu + Nu) →
        c * (A + S) + c * (B + S) = (c + c) * (Na + (Nu + S)) := by
      intro c A B S Na Nu hAB
      rw [← left_distrib]
      have : A + S + (B + S) = (A + B) + (S + S) := add_add_add_comm A S B S
      rw [this, hAB]
      exact RE.sound (look [c, S, Na, Nu]) (.mul (.var 0) (.add (.add (.add (.var 2) (.var 2)) (.add (.var 3) (.var 3))) (.add (.var 1) (.var 1)))) (.mul (.add (.var 0) (.var 0)) (.add (.var 2) (.add (.var 3) (.var 1)))) (by decide +kernel)
    exact e _ _ _ _ _ _ par

/-- 32:C3 — the incoherent mean: the norms of the `2^n` signed sums add up to `2^n` times the sum of the norms, so
the mean squared amplitude of an incoherent ensemble is `Σ N(u_k)` (the count `n` for unit phasors), its amplitude
`√n`, while the coherent stack has `n²`. -/
theorem incoherent_mean (us : List (Ext p ν)) : tot 0 us = ofNat (2 ^ us.length) * normSum us := by
  rw [tot_eq us 0]
  have h0 : norm (0 : Ext p ν) = 0 := by
    show (0 : Shell p) * 0 + -(ν * (0 * 0)) = 0
    rw [mul_zero, mul_zero, neg_zero, add_zero]
  rw [h0, zero_add]

/-! ## The coherence sums (32:C10, X8, P5, B9) -/

/-- 32:C10, 32:X7, 32:X8, 32:P5 — three mutually coherent components add as amplitudes: `(s₁ + s₂ + s₃)² = Σ s_i² + 2Σ_{i<j} s_i s_j`, the law
`g²_amp/a₀ = Σ g_i + 2Σ_{i<j} √(g_i g_j) Re C_ij` at `C_ij = 1`; at `C_ij = 0` only `Σ g_i` remains. -/
theorem cohsum_three (s1 s2 s3 : Shell p) :
    (s1 + s2 + s3) * (s1 + s2 + s3) = s1 * s1 + s2 * s2 + s3 * s3 + (s1 * s2 + s1 * s2 + (s1 * s3 + s1 * s3) + (s2 * s3 + s2 * s3)) :=
  RE.sound (look [s1, s2, s3]) (.mul (.add (.add (.var 0) (.var 1)) (.var 2)) (.add (.add (.var 0) (.var 1)) (.var 2))) (.add (.add (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.add (.add (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1))) (.add (.mul (.var 0) (.var 2)) (.mul (.var 0) (.var 2)))) (.add (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 2))))) (by decide +kernel)

/-- 32:X8 — `N` equal coherent components: `(Σ√g)² = N² g = N · Σ g`, so `N_eff = N` (the coherent core's `√N_eff` boost). -/
theorem neff_equal (s : Shell p) (N : Nat) : sumRange (fun _ => s) N * sumRange (fun _ => s) N = ofNat N * sumRange (fun _ => s * s) N := by
  rw [locked_sum, locked_sum]
  exact RE.sound (look [ofNat N, s]) (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1))) (.mul (.var 0) (.mul (.var 0) (.mul (.var 1) (.var 1)))) (by decide +kernel)

/-! ## The enclosed flux (32:C1, X1, C4) -/

/-- 32:C1, 32:X1, 32:C4 — the flux through the boundary of a region equals the source it encloses: for antisymmetric link currents with
divergence `src`, `Σ_{x∈R} Σ_{y∉R} J_xy = Σ_{x∈R} src x` (the Gauss law). A unit source inside gives unit flux
through every enclosing surface. -/
theorem enclosed_flux {κ : Nat} {g : Shell p} (F : Frame p κ g) (n : Nat) (J : Nat → Nat → Shell p)
    (hJ : ∀ x y, J x y = -(J y x)) (R : Nat → Bool) (src : Nat → Shell p)
    (hdiv : ∀ x, sumRange (fun y => J x y) n = src x) :
    sumRange (fun x => ind R x * sumRange (fun y => (1 + -(ind R y)) * J x y) n) n = sumRange (fun x => ind R x * src x) n := by
  rw [← gauss_law F n J hJ R]
  exact sum_congr n (fun x _ => by rw [hdiv x])

/-- 32:C1, 32:X1, 32:C4 — a source-free current has zero flux through every closed surface: the floor noise, zero-mean and source-free,
leaves the mean force unchanged. -/
theorem source_free_flux {κ : Nat} {g : Shell p} (F : Frame p κ g) (n : Nat) (J : Nat → Nat → Shell p)
    (hJ : ∀ x y, J x y = -(J y x)) (R : Nat → Bool) (hdiv : ∀ x, sumRange (fun y => J x y) n = 0) :
    sumRange (fun x => ind R x * sumRange (fun y => (1 + -(ind R y)) * J x y) n) n = 0 := by
  rw [enclosed_flux F n J hJ R (fun _ => 0) hdiv]
  exact sum_zero n (fun x _ => mul_zero _)

/-- 32:C1, 32:X1 — superposition: the flux of `J + K` is the sum of the fluxes — a source-free perturbation adds nothing. -/
theorem flux_superposition (n : Nat) (J K : Nat → Nat → Shell p) (R : Nat → Bool) :
    sumRange (fun x => ind R x * sumRange (fun y => (1 + -(ind R y)) * (J x y + K x y)) n) n =
      sumRange (fun x => ind R x * sumRange (fun y => (1 + -(ind R y)) * J x y) n) n +
      sumRange (fun x => ind R x * sumRange (fun y => (1 + -(ind R y)) * K x y) n) n := by
  rw [← sum_add]
  exact sum_congr n (fun x _ => by
    rw [← left_distrib, ← sum_add]
    congr 1
    exact sum_congr n (fun y _ => by rw [left_distrib]))

end FRC.Dark
