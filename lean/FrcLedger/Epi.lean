import Mathlib

/-!
# 13-epi — the classical constants on the shell: the ledger rows in Lean (2026-09-18)

Rows of the predicate ledger of *Finite Field Realisation of the Classical Constants π and e* (tree
`13-epi-20260713`).  The wall of `e`: Wilson reflection, the wall identity `!(p−1) ≡ !p`, the terminal residue
`−(!p)⁻¹`, antiperiodicity `!(n+p) ≡ −!n`, the series duals, the fixed-shell tower exact at every grade
(F1–F4, F7); the wall hierarchy of `π`: the legibility window, the half-wall terminus `−2`, the quarter-wall
two-squares invariant given Gauss's congruence, Lucas on the tower `C(2p^r, p^r) ≡ 2`, the first revival `8`,
the tower of `π` exact (G1–G3, G5, G9); the Cayley quarter-turn map and its composition law (C3); the Wallis
pair: strict monotonicity, the width identity and the enclosure `v_n < π < w_n` (E2, with Mathlib's Wallis
product); the impossibility of exact calibration of `e` from the irrationality of `π` (H3); the index condition
of the null experiment (H5).  Classical (tier 2) on Mathlib's hierarchy; the finite content — the derangement
recurrence, antiperiodicity, the tower, orientation transport, the wrap-free window and the value rows on
`𝔽₁₃` and the six wall shells — is proved with no axioms in `FrcCore/Epi.lean`.

The ring arithmetic of the wall is proved once over an arbitrary field `K` with `p = 0`, `(p−1)! = −1` and
`k! ≠ 0` (`k ≤ p−1`); the sections `prime` and `primepi` instantiate `K := ZMod p`.
-/

namespace FRC.Epi

open Finset Nat
/-! ## The Wallis pair (13:E1, E2) -/
section wallis

variable {K : Type*} [Field K]

/-- 13:E1 — the Wallis pair on the framed rationals: `v n = 2·16^n/((2n+1)·C(2n,n)²)` (the doubled Wallis
partial product) and `w n = 16^n/(n·C(2n,n)²)` (the joint-return tally). -/
noncomputable def wallisV (n : ℕ) : K := 2 * (16 : K) ^ n / ((2 * (n : K) + 1) * ((centralBinom n : ℕ) : K) ^ 2)

/-- The Wallis chain on a field: `w n = 16^n / (n · C(2n,n)²)`. -/
noncomputable def wallisW (n : ℕ) : K := (16 : K) ^ n / ((n : K) * ((centralBinom n : ℕ) : K) ^ 2)

end wallis


/-- Kurepa's left factorial `!n = Σ_{k<n} k!`. -/
def kurepa (n : ℕ) : ℕ := ∑ k ∈ range n, k !

/-- The alternating factorial sum `A(n) = Σ_{k<n} (−1)^k k!`. -/
def altFact (n : ℕ) : ℤ := ∑ k ∈ range n, (-1 : ℤ) ^ k * (k ! : ℤ)

/-! ## The wall, over any field of characteristic `p` with Wilson's value

Everything is proved once over a field `K` in which `p = 0`, `(p−1)! = −1` and `k! ≠ 0` for `k ≤ p − 1`;
the section `prime` instantiates `K := ZMod p` (whose instances under `Fact p.Prime` are not `ring`-friendly). -/
section wall

variable {K : Type*} [Field K]

theorem neg_one_pow_mul_self (k : ℕ) : (-1 : K) ^ k * (-1) ^ k = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]; simp

theorem neg_one_pow_sub_of_pow_eq_one {a k : ℕ} (h : (-1 : K) ^ a = 1) (hk : k ≤ a) :
    (-1 : K) ^ (a - k) = (-1) ^ k := by
  have : (-1 : K) ^ (a - k) * ((-1) ^ k * (-1) ^ k) = (-1) ^ a * (-1) ^ k := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hk]
  rwa [neg_one_pow_mul_self, mul_one, h, one_mul] at this

theorem natCast_pred_sub (p : ℕ) (hp0 : (p : K) = 0) (h1 : 1 ≤ p) (k : ℕ) (hk : k ≤ p - 1) :
    ((p - 1 - k : ℕ) : K) = -((k : K) + 1) := by
  rw [Nat.cast_sub hk, Nat.cast_sub h1, hp0]; ring

theorem factorial_mul_reflect (p : ℕ) (hp0 : (p : K) = 0) (hw : (((p - 1) ! : ℕ) : K) = -1)
    (h1 : 1 ≤ p) (k : ℕ) (hk : k ≤ p - 1) :
    ((k ! : ℕ) : K) * (((p - 1 - k) ! : ℕ) : K) = -(-1) ^ k := by
  induction k with
  | zero => rw [Nat.factorial_zero, Nat.cast_one, one_mul, Nat.sub_zero, hw, pow_zero]
  | succ k ih =>
    have hk' : k ≤ p - 1 := Nat.le_of_succ_le hk
    have e : p - 1 - k = (p - 1 - (k + 1)) + 1 := by omega
    have := ih hk'
    rw [e, Nat.factorial_succ, ← e, Nat.cast_mul, natCast_pred_sub p hp0 h1 k hk'] at this
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    linear_combination -this

theorem wilson_reflection (p : ℕ) (hp0 : (p : K) = 0) (hw : (((p - 1) ! : ℕ) : K) = -1)
    (h1 : 1 ≤ p) (k : ℕ) (hk : k ≤ p - 1) :
    ((k ! : ℕ) : K)⁻¹ = -(-1) ^ k * (((p - 1 - k) ! : ℕ) : K) := by
  apply inv_eq_of_mul_eq_one_right
  linear_combination -(-1 : K) ^ k * factorial_mul_reflect p hp0 hw h1 k hk + neg_one_pow_mul_self (K := K) k

theorem ascFactorial_reflect (p : ℕ) (hp0 : (p : K) = 0) (hw : (((p - 1) ! : ℕ) : K) = -1)
    (hfac : ∀ k, k ≤ p - 1 → ((k ! : ℕ) : K) ≠ 0) (h1 : 1 ≤ p) (k : ℕ) (hk : k ≤ p - 1) :
    (((k + 1).ascFactorial (p - 1 - k) : ℕ) : K) = (-1) ^ k * (((p - 1 - k) ! : ℕ) : K) := by
  apply mul_left_cancel₀ (hfac k hk)
  have hA : ((k ! : ℕ) : K) * ((k + 1).ascFactorial (p - 1 - k) : ℕ) = -1 := by
    rw [← Nat.cast_mul, Nat.factorial_mul_ascFactorial, Nat.add_sub_cancel' hk, hw]
  linear_combination hA - (-1 : K) ^ k * factorial_mul_reflect p hp0 hw h1 k hk + neg_one_pow_mul_self (K := K) k

theorem derangements_wall (p : ℕ) (hp0 : (p : K) = 0) (hw : (((p - 1) ! : ℕ) : K) = -1)
    (hfac : ∀ k, k ≤ p - 1 → ((k ! : ℕ) : K) ≠ 0) (h1 : 1 ≤ p) :
    ((numDerangements (p - 1) : ℕ) : K) = (kurepa p : K) := by
  have h := numDerangements_sum (p - 1)
  have hcast : ((numDerangements (p - 1) : ℕ) : K) = ((numDerangements (p - 1) : ℤ) : K) := by
    rw [Int.cast_natCast]
  rw [hcast, h, Int.cast_sum]
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast]
  rw [Nat.sub_add_cancel h1]
  unfold kurepa
  rw [Nat.cast_sum, ← sum_range_reflect (fun j => ((j ! : ℕ) : K)) p]
  apply sum_congr rfl
  intro k hk
  have hk' : k ≤ p - 1 := by have := mem_range.1 hk; omega
  rw [ascFactorial_reflect p hp0 hw hfac h1 k hk', ← mul_assoc, neg_one_pow_mul_self, one_mul]

theorem derangements_succ_cast (n : ℕ) :
    ((numDerangements (n + 1) : ℕ) : K) = ((n : K) + 1) * (numDerangements n : ℕ) - (-1) ^ n := by
  have := congrArg (fun z : ℤ => (z : K)) (numDerangements_succ n)
  simp only [Int.cast_natCast, Int.cast_sub, Int.cast_mul, Int.cast_add, Int.cast_one, Int.cast_pow,
    Int.cast_neg] at this
  exact this

theorem neg_one_pow_pred_of_odd (p : ℕ) (hodd : Odd p) : (-1 : K) ^ (p - 1) = 1 := by
  obtain ⟨m, hm⟩ := hodd
  rw [hm, Nat.add_sub_cancel, pow_mul]; simp

theorem derangements_antiperiodic (p : ℕ) (hp0 : (p : K) = 0) (hodd : Odd p) (n : ℕ) :
    ((numDerangements (n + p) : ℕ) : K) = -((numDerangements n : ℕ) : K) := by
  have hneg : (-1 : K) ^ p = -1 := hodd.neg_one_pow
  have h1 : 1 ≤ p := hodd.pos
  induction n with
  | zero =>
    have h := derangements_succ_cast (K := K) (p - 1)
    rw [Nat.sub_add_cancel h1] at h
    rw [zero_add, h, neg_one_pow_pred_of_odd p hodd, numDerangements_zero, Nat.cast_one,
      Nat.cast_sub h1, hp0]
    ring
  | succ n ih =>
    rw [show n + 1 + p = (n + p) + 1 by omega, derangements_succ_cast, ih,
      derangements_succ_cast, pow_add, hneg, Nat.cast_add, hp0]
    ring

theorem series_duals (p : ℕ) (hp0 : (p : K) = 0) (hw : (((p - 1) ! : ℕ) : K) = -1) (hodd : Odd p) :
    (∑ k ∈ range p, (-1 : K) ^ k * ((k ! : ℕ) : K)⁻¹) = -(kurepa p : K) ∧
    (∑ k ∈ range p, ((k ! : ℕ) : K)⁻¹) = -((altFact p : ℤ) : K) := by
  have h1 : 1 ≤ p := hodd.pos
  constructor
  · unfold kurepa
    rw [Nat.cast_sum, ← sum_range_reflect (fun j => ((j ! : ℕ) : K)) p, ← sum_neg_distrib]
    apply sum_congr rfl
    intro k hk
    have hk' : k ≤ p - 1 := by have := mem_range.1 hk; omega
    rw [wilson_reflection p hp0 hw h1 k hk']
    linear_combination -((((p - 1 - k) ! : ℕ) : K)) * neg_one_pow_mul_self (K := K) k
  · unfold altFact
    rw [Int.cast_sum]
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast]
    rw [← sum_range_reflect (fun j => (-1 : K) ^ j * ((j ! : ℕ) : K)) p, ← sum_neg_distrib]
    apply sum_congr rfl
    intro k hk
    have hk' : k ≤ p - 1 := by have := mem_range.1 hk; omega
    rw [wilson_reflection p hp0 hw h1 k hk',
      neg_one_pow_sub_of_pow_eq_one (neg_one_pow_pred_of_odd p hodd) hk']
    ring

theorem tower_e_exact (p : ℕ) (hp0 : (p : K) = 0) (hodd : Odd p)
    (hfacp : ∀ m, 1 ≤ m → (((m * p) ! : ℕ) : K) = 0) (m : ℕ) (hm : 1 ≤ m) (e δ : K)
    (hδ : δ = (-1) ^ m * e) :
    (((m * p) ! : ℕ) : K) = 0 ∧ ((numDerangements (m * p) : ℕ) : K) = (-1) ^ m ∧
    ((((m * p) ! : ℕ) : K) + δ) / ((numDerangements (m * p) : ℕ) : K) = e := by
  have hder : ∀ m, ((numDerangements (m * p) : ℕ) : K) = (-1) ^ m := by
    intro m
    induction m with
    | zero => rw [Nat.zero_mul, numDerangements_zero, Nat.cast_one, pow_zero]
    | succ m ih => rw [Nat.succ_mul, derangements_antiperiodic p hp0 hodd, ih, pow_succ, mul_neg_one]
  refine ⟨hfacp m hm, hder m, ?_⟩
  rw [hfacp m hm, hder, zero_add, hδ]
  exact mul_div_cancel_left₀ e (pow_ne_zero m (neg_ne_zero.2 one_ne_zero))

/-- The tail identity: `j! · !(p−1−j) = (−1)^j · (K(p) − K(j))` for `0 ≤ j ≤ p − 1` — the derangement residue
line read from the wall is the sequence of tails `Σ_{m=j}^{p−1} m!` of Kurepa's left factorial. -/
theorem tail_identity (p : ℕ) (hp0 : (p : K) = 0) (hw : (((p - 1) ! : ℕ) : K) = -1)
    (hfac : ∀ k, k ≤ p - 1 → ((k ! : ℕ) : K) ≠ 0) (h1 : 1 ≤ p) (j : ℕ) (hj : j ≤ p - 1) :
    ((j ! : ℕ) : K) * ((numDerangements (p - 1 - j) : ℕ) : K) = (-1) ^ j * ((kurepa p : K) - (kurepa j : K)) := by
  have hcast : ((numDerangements (p - 1 - j) : ℕ) : K) = ((numDerangements (p - 1 - j) : ℤ) : K) := by
    rw [Int.cast_natCast]
  rw [hcast, numDerangements_sum, Int.cast_sum]
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast]
  rw [Finset.mul_sum]
  have hterm : ∀ k ∈ range (p - 1 - j + 1),
      ((j ! : ℕ) : K) * ((-1) ^ k * (((k + 1).ascFactorial (p - 1 - j - k) : ℕ) : K)) =
        (-1) ^ j * (((p - 1 - k) ! : ℕ) : K) := by
    intro k hk
    have hk' : k ≤ p - 1 - j := by have := mem_range.1 hk; omega
    have hA : ((k ! : ℕ) : K) * (((k + 1).ascFactorial (p - 1 - j - k) : ℕ) : K) = (((p - 1 - j) ! : ℕ) : K) := by
      rw [← Nat.cast_mul, Nat.factorial_mul_ascFactorial, Nat.add_sub_cancel' hk']
    have hjr := factorial_mul_reflect p hp0 hw h1 j hj
    have hkr := factorial_mul_reflect p hp0 hw h1 k (by omega)
    apply mul_left_cancel₀ (hfac k (by omega))
    linear_combination (-1 : K) ^ k * ((j ! : ℕ) : K) * hA + (-1 : K) ^ k * hjr - (-1 : K) ^ j * hkr
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  congr 1
  have hn : p - 1 - j + 1 = p - j := by omega
  rw [hn]
  have hre : ∀ k ∈ range (p - j), (((p - 1 - k) ! : ℕ) : K) = (fun i => (((j + i) ! : ℕ) : K)) ((p - j) - 1 - k) := by
    intro k hk
    have := mem_range.1 hk
    show (((p - 1 - k) ! : ℕ) : K) = (((j + ((p - j) - 1 - k)) ! : ℕ) : K)
    congr 2; omega
  rw [Finset.sum_congr rfl hre, Finset.sum_range_reflect (fun i => (((j + i) ! : ℕ) : K)) (p - j),
    ← Finset.sum_Ico_eq_sum_range (fun m => ((m ! : ℕ) : K)) j p]
  unfold kurepa
  rw [Nat.cast_sum, Nat.cast_sum, eq_sub_iff_add_eq, add_comm, Finset.sum_range_add_sum_Ico _ (by omega)]

end wall

/-! ## The prime shell: `K := ZMod p` -/
section prime

variable (p : ℕ) [hp : Fact p.Prime]

theorem factorial_ne_zero_zmod (k : ℕ) (hk : k ≤ p - 1) : ((k ! : ℕ) : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  have := (hp.out.dvd_factorial).1 h
  have := hp.out.two_le
  omega

theorem factorial_mul_prime_eq_zero (m : ℕ) (hm : 1 ≤ m) : (((m * p) ! : ℕ) : ZMod p) = 0 := by
  rw [ZMod.natCast_eq_zero_iff]
  exact (hp.out.dvd_factorial).2 (Nat.le_mul_of_pos_left p hm)

/-- 13:F1 — Wilson reflection: `1/k! ≡ −(−1)^k (p−1−k)! (mod p)` for `0 ≤ k ≤ p − 1`, from Wilson's
theorem `(p−1)! ≡ −1` and `p − j ≡ −j`. -/
theorem wilson_reflection_zmod (k : ℕ) (hk : k ≤ p - 1) :
    ((k ! : ℕ) : ZMod p)⁻¹ = -(-1) ^ k * (((p - 1 - k) ! : ℕ) : ZMod p) :=
  wilson_reflection p (ZMod.natCast_self p) (ZMod.wilsons_lemma p) hp.out.one_le k hk

/-- 13:F2 — the wall identity: `!(p−1) ≡ !p (mod p)` for every prime `p` — the derangement number at the wall
is Kurepa's left factorial (the odd-prime case of the Mijajlović–Šami congruence), from Wilson reflection. -/
theorem derangements_wall_zmod : ((numDerangements (p - 1) : ℕ) : ZMod p) = (kurepa p : ZMod p) :=
  derangements_wall p (ZMod.natCast_self p) (ZMod.wilsons_lemma p) (factorial_ne_zero_zmod p) hp.out.one_le

/-- 13:F2 — the terminal residue of `e`: `⟦ε_{p−1}⟧ = (p−1)!/!(p−1) = −(!p)⁻¹`, and the terminal link exists
(`!(p−1) ≢ 0`) exactly when `p ∤ !p`. -/
theorem terminal_residue :
    (((p - 1) ! : ℕ) : ZMod p) / ((numDerangements (p - 1) : ℕ) : ZMod p) = -(kurepa p : ZMod p)⁻¹ ∧
    (((numDerangements (p - 1) : ℕ) : ZMod p) ≠ 0 ↔ ¬ p ∣ kurepa p) := by
  rw [derangements_wall_zmod, ZMod.wilsons_lemma, div_eq_mul_inv, neg_one_mul, Ne,
    ZMod.natCast_eq_zero_iff]
  exact ⟨rfl, Iff.rfl⟩

/-- 13:F3 — antiperiodicity: `!(n + p) ≡ −!n (mod p)` for every odd prime `p` and every `n ≥ 0`, so
`!n mod p` depends on `n mod 2p`; the blind set always contains `n = 1` (`!1 = 0`). -/
theorem derangements_antiperiodic_zmod (hp2 : p ≠ 2) (n : ℕ) :
    ((numDerangements (n + p) : ℕ) : ZMod p) = -((numDerangements n : ℕ) : ZMod p) ∧
    numDerangements 1 = 0 :=
  ⟨derangements_antiperiodic p (ZMod.natCast_self p) (hp.out.odd_of_ne_two hp2) n, numDerangements_one⟩

/-- 13:F4 — the series duals at the wall: `Σ_{k<p} (−1)^k/k! ≡ −!p` and `Σ_{k<p} 1/k! ≡ −A(p)`, `A(p)` the
alternating factorial sum, for every odd prime `p`. -/
theorem series_duals_zmod (hp2 : p ≠ 2) :
    (∑ k ∈ range p, (-1 : ZMod p) ^ k * ((k ! : ℕ) : ZMod p)⁻¹) = -(kurepa p : ZMod p) ∧
    (∑ k ∈ range p, ((k ! : ℕ) : ZMod p)⁻¹) = -((altFact p : ℤ) : ZMod p) :=
  series_duals p (ZMod.natCast_self p) (ZMod.wilsons_lemma p) (hp.out.odd_of_ne_two hp2)

/-- 13:F7 — the fixed-shell tower of `e` is exact at every grade: `(mp)! ≡ 0` and `!(mp) ≡ (−1)^m (mod p)`
for `m ≥ 1`, so `q_m = ((mp)! + δ_m)/!(mp)` reads `e_p` on the shell whenever `δ_m ≡ (−1)^m e_p`. -/
theorem tower_e_exact_zmod (hp2 : p ≠ 2) (m : ℕ) (hm : 1 ≤ m) (e δ : ZMod p) (hδ : δ = (-1) ^ m * e) :
    (((m * p) ! : ℕ) : ZMod p) = 0 ∧ ((numDerangements (m * p) : ℕ) : ZMod p) = (-1) ^ m ∧
    ((((m * p) ! : ℕ) : ZMod p) + δ) / ((numDerangements (m * p) : ℕ) : ZMod p) = e :=
  tower_e_exact p (ZMod.natCast_self p) (hp.out.odd_of_ne_two hp2) (factorial_mul_prime_eq_zero p) m hm e δ hδ

/-- 13:F8, 13:Y1 — the tail identity on the shell: `j! · !(p−1−j) ≡ (−1)^j (!p − !j) (mod p)`, `0 ≤ j ≤ p − 1`. -/
theorem tail_identity_zmod (j : ℕ) (hj : j ≤ p - 1) :
    ((j ! : ℕ) : ZMod p) * ((numDerangements (p - 1 - j) : ℕ) : ZMod p) =
      (-1) ^ j * ((kurepa p : ZMod p) - (kurepa j : ZMod p)) :=
  tail_identity p (ZMod.natCast_self p) (ZMod.wilsons_lemma p) (factorial_ne_zero_zmod p) hp.out.one_le j hj

/-- 13:F8, 13:Y1 — the collision reading of the blind set: for `n ≤ p − 1`, `!n ≡ 0 (mod p)` exactly when the partial
sum `!(p−1−n)` of the left factorial collides with `!p`; Kurepa's hypothesis at `p` is the case `n = p − 1`,
`!(0) = 0 ≢ !p`; the universal blind scale `n = 1` is `!(p−2) ≡ !p` (the tail `(p−2)! + (p−1)! ≡ 0`). -/
theorem blind_iff_collision (n : ℕ) (hn : n ≤ p - 1) :
    (((numDerangements n : ℕ) : ZMod p) = 0 ↔ (kurepa (p - 1 - n) : ZMod p) = (kurepa p : ZMod p)) ∧
    (kurepa (p - 2) : ZMod p) = (kurepa p : ZMod p) := by
  have key : ∀ n, n ≤ p - 1 →
      (((numDerangements n : ℕ) : ZMod p) = 0 ↔ (kurepa (p - 1 - n) : ZMod p) = (kurepa p : ZMod p)) := by
    intro n hn
    have h := tail_identity_zmod p (p - 1 - n) (by omega)
    rw [show p - 1 - (p - 1 - n) = n by omega] at h
    have hf := factorial_ne_zero_zmod p (p - 1 - n) (by omega)
    have hs : ((-1 : ZMod p) ^ (p - 1 - n)) ≠ 0 := by
      apply pow_ne_zero; intro h1
      exact (one_ne_zero : (1 : ZMod p) ≠ 0) (neg_eq_zero.1 h1)
    constructor
    · intro h0
      rw [h0, mul_zero] at h
      have := (mul_eq_zero.1 h.symm).resolve_left hs
      exact (sub_eq_zero.1 this).symm
    · intro hc
      have : ((-1 : ZMod p) ^ (p - 1 - n)) * ((kurepa p : ZMod p) - (kurepa (p - 1 - n) : ZMod p)) = 0 := by
        rw [hc, sub_self, mul_zero]
      rw [← h] at this
      exact (mul_eq_zero.1 this).resolve_left hf
  refine ⟨key n hn, ?_⟩
  have h2 := hp.out.two_le
  have := (key 1 (by omega)).1 (by rw [numDerangements_one, Nat.cast_zero])
  rwa [show p - 1 - 1 = p - 2 by omega] at this

end prime



/-! ## The wall hierarchy of `π`: the Wallis chain `w_n = 16^n/(n C_n²)` on the shell -/
section wallpi

variable {K : Type*} [Field K]

theorem sq_eq_one_of_eq_neg_one_pow (c : K) (m : ℕ) (h : c = (-1) ^ m) : c ^ 2 = 1 := by
  rw [h, ← pow_mul, mul_comm, pow_mul]; norm_num

/-- `C(p−1, k) ≡ (−1)^k`, from `C(n, k+1)(k+1) = C(n, k)(n − k)` and `p − 1 − k ≡ −(k+1)`. -/
theorem choose_pred_eq_neg_one_pow (p : ℕ) (hp0 : (p : K) = 0) (h1 : 1 ≤ p)
    (hunit : ∀ j, 1 ≤ j → j ≤ p - 1 → (j : K) ≠ 0) (k : ℕ) (hk : k ≤ p - 1) :
    ((choose (p - 1) k : ℕ) : K) = (-1) ^ k := by
  induction k with
  | zero => rw [choose_zero_right, Nat.cast_one, pow_zero]
  | succ k ih =>
    have hk' : k ≤ p - 1 := Nat.le_of_succ_le hk
    have h := congrArg (fun m : ℕ => (m : K)) (Nat.choose_succ_right_eq (p - 1) k)
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h
    rw [ih hk', Nat.cast_sub hk', Nat.cast_sub h1, hp0] at h
    have hne : ((k : K) + 1) ≠ 0 := by
      have := hunit (k + 1) (by omega) hk
      rwa [Nat.cast_add, Nat.cast_one] at this
    apply mul_right_cancel₀ hne
    rw [h, pow_succ]; ring

theorem half_wall_generic (m : K) (h2m : (2 : K) * m = -1) (x c : K)
    (hx : x = 1) (hc : c ^ 2 = 1) :
    x / (m * c ^ 2) = -2 ∧ m⁻¹ = -2 ∧ (4 : K) * m = -2 := by
  have hinv : m⁻¹ = -2 := inv_eq_of_mul_eq_one_right (by linear_combination -h2m)
  refine ⟨?_, hinv, by linear_combination 2 * h2m⟩
  rw [hx, hc, mul_one, one_div, hinv]

theorem quarter_wall_generic (κ a b c : K) (hκ : (4 : K) * κ = -1) (h2 : (2 : K) ≠ 0)
    (hC : c = 2 * a) (ha : a ≠ 0) (hab : a ^ 2 + b ^ 2 = 0) (x : K) (hx : x = 1) :
    x / (κ * c ^ 2) = -(a ^ 2)⁻¹ ∧ -(a ^ 2)⁻¹ = (b ^ 2)⁻¹ := by
  have hκ0 : κ ≠ 0 := by
    intro h; rw [h, mul_zero] at hκ; exact one_ne_zero (by linear_combination hκ)
  have hc0 : c ≠ 0 := by rw [hC]; exact mul_ne_zero h2 ha
  have hinv : (a ^ 2)⁻¹ * a ^ 2 = 1 := inv_mul_cancel₀ (pow_ne_zero 2 ha)
  constructor
  · rw [div_eq_iff (mul_ne_zero hκ0 (pow_ne_zero 2 hc0)), hx, hC]
    linear_combination 4 * κ * hinv + hκ
  · rw [neg_inv]; congr 1; linear_combination -hab

theorem first_revival_generic (x c d : K) (h2 : (2 : K) ≠ 0) (hx : x = 16) (hc : c = 2) (hd : d = 1) :
    2 * x / (d * c ^ 2) = 8 := by
  subst hx hc hd; field_simp; ring

theorem tower_pi_generic (x c d δ κ : K) (h2 : (2 : K) ≠ 0) (hx : x = 16) (hc : c = 2) (hd : d = 1)
    (hδ : δ = -34) (hκ : (4 : K) * κ = -1) :
    (2 * x + δ) / (d * c ^ 2) = 2 * κ := by
  subst hx hc hd hδ; field_simp; linear_combination -2 * hκ

end wallpi

section primepi

variable (p : ℕ) [hp : Fact p.Prime]

theorem natCast_ne_zero_of_lt (j : ℕ) (hj0 : 1 ≤ j) (hj : j < p) : (j : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  have := Nat.le_of_dvd (by omega) h
  omega

theorem two_ne_zero_zmod (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  have := natCast_ne_zero_of_lt p 2 (by omega) (lt_of_le_of_ne hp.out.two_le (Ne.symm hp2))
  rwa [Nat.cast_ofNat] at this

/-- 13:G1 — the legibility window: `p ∤ C(2n,n)` for `1 ≤ n ≤ (p−1)/2` and `p ∣ C(2n,n)` for
`(p−1)/2 < n < p` — the residue line of the Wallis chain is defined exactly on `[1, (p−1)/2]`. -/
theorem legibility_window (n : ℕ) :
    (2 * n ≤ p - 1 → ¬ p ∣ centralBinom n) ∧ (p ≤ 2 * n → n < p → p ∣ centralBinom n) := by
  have hfac : centralBinom n * n ! * n ! = (2 * n) ! := by
    have := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
    rwa [show 2 * n - n = n by omega, ← centralBinom_eq_two_mul_choose] at this
  constructor
  · intro hn hdvd
    have : p ∣ (2 * n) ! := hfac ▸ Dvd.dvd.mul_right (Dvd.dvd.mul_right hdvd _) _
    have := (hp.out.dvd_factorial).1 this
    have := hp.out.pos
    omega
  · intro hn hnp
    have h1 : p ∣ (2 * n) ! := (hp.out.dvd_factorial).2 hn
    rw [← hfac] at h1
    have hnf : ¬ p ∣ n ! := fun h => by have := (hp.out.dvd_factorial).1 h; omega
    rcases (hp.out.dvd_mul).1 h1 with h | h
    · rcases (hp.out.dvd_mul).1 h with h | h
      · exact h
      · exact absurd h hnf
    · exact absurd h hnf

/-- 13:G2 — the half-wall terminus, the calibration face: with `m = (p−1)/2`, `16^m ≡ 1`,
`C(2m,m)² ≡ 1`, and `⟦w_m⟧ = m⁻¹ = −2` for every odd prime; the identity `4·π_A ≡ −2` beside it. -/
theorem half_wall_terminus (hp2 : p ≠ 2) (m : ℕ) (hm : p = 2 * m + 1) :
    (16 : ZMod p) ^ m = 1 ∧ ((centralBinom m : ℕ) : ZMod p) ^ 2 = 1 ∧
    wallisW m = (-2 : ZMod p) ∧ (m : ZMod p)⁻¹ = -2 ∧ (4 : ZMod p) * m = -2 := by
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod p hp2
  have h4 : (4 : ZMod p) ≠ 0 := by
    have : (4 : ZMod p) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have h16 : (16 : ZMod p) ^ m = 1 := by
    have : (16 : ZMod p) ^ m = (4 : ZMod p) ^ (p - 1) := by
      rw [show p - 1 = 2 * m by omega, pow_mul]; norm_num
    rw [this]; exact ZMod.pow_card_sub_one_eq_one h4
  have hC : ((centralBinom m : ℕ) : ZMod p) = (-1) ^ m := by
    have hm' : m ≤ p - 1 := by omega
    have := choose_pred_eq_neg_one_pow (K := ZMod p) p (ZMod.natCast_self p) hp.out.one_le
      (fun j hj0 hj => natCast_ne_zero_of_lt p j hj0 (by omega)) m hm'
    rw [centralBinom_eq_two_mul_choose, show 2 * m = p - 1 by omega]; exact this
  have hC2 : ((centralBinom m : ℕ) : ZMod p) ^ 2 = 1 := by
    exact sq_eq_one_of_eq_neg_one_pow _ m hC
  have h2m : (2 : ZMod p) * m = -1 := by
    have : ((2 * m + 1 : ℕ) : ZMod p) = 0 := by rw [← hm]; exact ZMod.natCast_self p
    push_cast at this
    exact eq_neg_of_add_eq_zero_left this
  obtain ⟨hw, hinv, h4m⟩ := half_wall_generic (K := ZMod p) m h2m _ _ h16 hC2
  exact ⟨h16, hC2, hw, hinv, h4m⟩

/-- 13:G3 — the quarter-wall two-squares invariant: on `p = 4κ + 1 = a² + b²`, given Gauss's congruence
`C(2κ,κ) ≡ 2a` (the import A3), `⟦w_κ⟧ = −(a²)⁻¹ = (b²)⁻¹`. -/
theorem quarter_wall_invariant (κ a b : ℕ) (hκ : p = 4 * κ + 1) (hab : a ^ 2 + b ^ 2 = p)
    (ha : 0 < a) (hb : 0 < b) (hG : ((centralBinom κ : ℕ) : ZMod p) = 2 * a) :
    wallisW κ = -((a : ZMod p) ^ 2)⁻¹ ∧ -((a : ZMod p) ^ 2)⁻¹ = ((b : ZMod p) ^ 2)⁻¹ := by
  have hp2 : p ≠ 2 := by omega
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod p hp2
  have hκ' : (4 : ZMod p) * κ = -1 := by
    have : ((4 * κ + 1 : ℕ) : ZMod p) = 0 := by rw [← hκ]; exact ZMod.natCast_self p
    push_cast at this
    exact eq_neg_of_add_eq_zero_left this
  have h16 : (16 : ZMod p) ^ κ = 1 := by
    have : (16 : ZMod p) ^ κ = (2 : ZMod p) ^ (p - 1) := by
      rw [show p - 1 = 4 * κ by omega, pow_mul]; norm_num
    rw [this]; exact ZMod.pow_card_sub_one_eq_one h2
  have hab' : (a : ZMod p) ^ 2 + (b : ZMod p) ^ 2 = 0 := by
    have : ((a ^ 2 + b ^ 2 : ℕ) : ZMod p) = 0 := by rw [hab]; exact ZMod.natCast_self p
    push_cast at this; exact this
  have ha2 : a ≤ a ^ 2 := Nat.le_self_pow (by norm_num) a
  have hb2 : 1 ≤ b ^ 2 := Nat.one_le_pow _ _ hb
  have ha' : (a : ZMod p) ≠ 0 := natCast_ne_zero_of_lt p a ha (by omega)
  exact quarter_wall_generic (K := ZMod p) κ a b _ hκ' h2 hG ha' hab' _ h16

/-- Lucas at the first revival and up the tower: `C(2p^{r+1}, p^{r+1}) ≡ C(2p^r, p^r) (mod p)`. -/
theorem choose_two_mul_pow_succ (r : ℕ) :
    ((choose (2 * p ^ (r + 1)) (p ^ (r + 1)) : ℕ) : ZMod p) = ((choose (2 * p ^ r) (p ^ r) : ℕ) : ZMod p) := by
  have hpos : 0 < p := hp.out.pos
  have h := Choose.choose_modEq_choose_mod_mul_choose_div (p := p) (n := 2 * p ^ (r + 1)) (k := p ^ (r + 1))
  have e1 : 2 * p ^ (r + 1) % p = 0 := by rw [pow_succ, ← mul_assoc]; exact Nat.mul_mod_left _ _
  have e2 : p ^ (r + 1) % p = 0 := by rw [pow_succ]; exact Nat.mul_mod_left _ _
  have e3 : 2 * p ^ (r + 1) / p = 2 * p ^ r := by rw [pow_succ, ← mul_assoc]; exact Nat.mul_div_cancel _ hpos
  have e4 : p ^ (r + 1) / p = p ^ r := by rw [pow_succ]; exact Nat.mul_div_cancel _ hpos
  rw [e1, e2, e3, e4, choose_zero_right] at h
  simp only [Nat.cast_one, one_mul] at h
  have := (ZMod.intCast_eq_intCast_iff _ _ p).2 h
  exact_mod_cast this

/-- 13:G5, 13:G9 — Lucas on the tower: `C(2p^r, p^r) ≡ 2 (mod p)` for every `r` (the first revival is `r = 1`). -/
theorem choose_two_mul_pow (r : ℕ) : ((choose (2 * p ^ r) (p ^ r) : ℕ) : ZMod p) = 2 := by
  induction r with
  | zero => norm_num
  | succ r ih => rw [choose_two_mul_pow_succ p r, ih]

/-- 13:G5 — the first revival: `⟦v_p⟧ = 2·16^p/((2p+1)·C(2p,p)²) ≡ 8` on every odd prime shell, by Lucas
(`C(2p,p) ≡ 2`), Fermat (`16^p ≡ 16`) and `2p + 1 ≡ 1`. -/
theorem first_revival (hp2 : p ≠ 2) :
    (2 : ZMod p) * 16 ^ p / (((2 * p + 1 : ℕ) : ZMod p) * ((centralBinom p : ℕ) : ZMod p) ^ 2) = 8 := by
  apply first_revival_generic _ _ _ (two_ne_zero_zmod p hp2)
  · exact ZMod.pow_card 16
  · rw [centralBinom_eq_two_mul_choose]
    have := choose_two_mul_pow p 1
    rwa [pow_one] at this
  · push_cast; rw [ZMod.natCast_self]; ring

/-- 13:G9 — the fixed-shell tower of `π`: for `n = p^r`, `r ≥ 1`, `16^n ≡ 16`, `C(2n,n) ≡ 2` and `2n + 1 ≡ 1`,
so `π̂_{p,r} = (2·16^n + δ)/((2n+1)·C(2n,n)²)` reads `π_A = 2κ` exactly, whenever `δ ≡ −34`. -/
theorem tower_pi_exact (κ : ℕ) (hκ : p = 4 * κ + 1) (r : ℕ) (hr : 1 ≤ r) (δ : ZMod p) (hδ : δ = -34) :
    (2 * (16 : ZMod p) ^ (p ^ r) + δ) /
      (((2 * p ^ r + 1 : ℕ) : ZMod p) * ((centralBinom (p ^ r) : ℕ) : ZMod p) ^ 2) = 2 * κ := by
  have hp2 : p ≠ 2 := by omega
  apply tower_pi_generic _ _ _ _ _ (two_ne_zero_zmod p hp2)
  · exact ZMod.pow_card_pow 16
  · rw [centralBinom_eq_two_mul_choose]; exact choose_two_mul_pow p r
  · push_cast
    rw [ZMod.natCast_self, zero_pow (by omega)]; ring
  · exact hδ
  · have : ((4 * κ + 1 : ℕ) : ZMod p) = 0 := by rw [← hκ]; exact ZMod.natCast_self p
    push_cast at this
    exact eq_neg_of_add_eq_zero_left this

end primepi

/-! ## The Cayley quarter-turn map (13:C3) -/
section cayley

variable {K : Type*} [Field K]

/-- The Cayley quarter-turn map `C(x) = (1 + i x)/(1 − i x)`. -/
noncomputable def cayley (i x : K) : K := (1 + i * x) / (1 - i * x)

/-- 13:C3 — `C(0) = 1` and `C(1) = i` for a quarter turn `i` (`i² = −1`) in characteristic `≠ 2`. -/
theorem cayley_values (i : K) (hi : i * i = -1) (h2 : (2 : K) ≠ 0) :
    cayley i 0 = 1 ∧ cayley i 1 = i := by
  constructor
  · simp [cayley]
  · have h1 : 1 - i * 1 ≠ 0 := by
      intro h; apply h2
      have : i = 1 := by linear_combination -h
      rw [this] at hi; linear_combination hi
    unfold cayley
    rw [div_eq_iff h1]; linear_combination hi

/-- 13:C3 — the composition law `C(x)·C(y) = C((x + y)/(1 − xy))`: the rational law is the half-angle form
of phase composition, with denominators units. -/
theorem cayley_mul (i x y : K) (hi : i * i = -1) (hx : 1 - i * x ≠ 0) (hy : 1 - i * y ≠ 0)
    (hxy : 1 - x * y ≠ 0) :
    cayley i x * cayley i y = cayley i ((x + y) / (1 - x * y)) := by
  have key : (1 - i * x) * (1 - i * y) = (1 - x * y) - i * (x + y) := by linear_combination x * y * hi
  have hden : 1 - i * ((x + y) / (1 - x * y)) ≠ 0 := by
    rw [show 1 - i * ((x + y) / (1 - x * y)) = ((1 - x * y) - i * (x + y)) / (1 - x * y) by
      field_simp]
    rw [← key]
    exact div_ne_zero (mul_ne_zero hx hy) hxy
  unfold cayley
  rw [eq_div_iff hden]
  field_simp
  linear_combination (-2 * i * x * y * (x + y)) * hi

end cayley

/-! ## Angular structure: exact calibration of `e` is impossible (13:H3) -/
section angular

open Real

/-- 13:H3 — `θ = 2πλ/(p−1) ≠ 1` for every label `λ ≥ 1` and every `p`: `θ = 1` would make `π` rational. -/
theorem calibration_ne_one (n l : ℕ) (hl : 0 < l) : 2 * π * l / n ≠ 1 := by
  intro h
  have hn : (n : ℝ) ≠ 0 := by intro hn; rw [hn, div_zero] at h; exact zero_ne_one h
  have hl' : (l : ℝ) ≠ 0 := by exact_mod_cast hl.ne'
  have : π = (n : ℝ) / (2 * l) := by
    field_simp at h ⊢; linarith
  exact irrational_pi.ne_rat ((n : ℚ) / (2 * l)) (by rw [this]; push_cast; ring)

/-- 13:H3 — `e^{i n} ≠ 1` for every `n ≥ 1`: `e^{i}` is not a root of unity (while `χ(e_p)` is one). -/
theorem exp_I_ne_one (n : ℕ) (hn : 0 < n) : Complex.exp (n * Complex.I) ≠ 1 := by
  rw [Ne, Complex.exp_eq_one_iff]
  rintro ⟨k, hk⟩
  have h2 : (n : ℂ) * Complex.I = (k * (2 * π)) * Complex.I := by rw [hk]; ring
  have h1 : (n : ℂ) = k * (2 * π) := mul_right_cancel₀ Complex.I_ne_zero h2
  have h3 : (n : ℝ) = k * (2 * π) := by exact_mod_cast h1
  have hk0 : (k : ℝ) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at h3
    exact (Nat.cast_pos.2 hn).ne' h3
  exact irrational_pi.ne_rat ((n : ℚ) / (2 * k)) (by push_cast; field_simp; linarith)

end angular

/-! ## The null experiment: the index condition (13:H5) -/
section index

/-- 13:H5 — the index condition: `u·l ≡ s (mod n)` is solvable with `u` coprime to `n` exactly when
`gcd(l, n) = gcd(s, n)`. -/
theorem index_condition (n l s : ℕ) [NeZero n] :
    (∃ u : ℕ, u.Coprime n ∧ u * l ≡ s [MOD n]) ↔ Nat.gcd l n = Nat.gcd s n := by
  constructor
  · rintro ⟨u, hu, h⟩
    rw [← Nat.ModEq.gcd_eq h, Nat.Coprime.gcd_mul_left_cancel l hu]
  · intro hg
    obtain ⟨d, hd⟩ : ∃ d, Nat.gcd l n = d := ⟨_, rfl⟩
    have hd0 : 0 < d := hd ▸ Nat.gcd_pos_of_pos_right l (NeZero.pos n)
    obtain ⟨n', hn'⟩ : d ∣ n := hd ▸ Nat.gcd_dvd_right l n
    obtain ⟨l', hl'⟩ : d ∣ l := hd ▸ Nat.gcd_dvd_left l n
    obtain ⟨s', hs'⟩ : d ∣ s := (hd ▸ hg : d = Nat.gcd s n) ▸ Nat.gcd_dvd_left s n
    have hl'c : Nat.Coprime l' n' := by
      have := Nat.coprime_div_gcd_div_gcd (m := l) (n := n) (hd ▸ hd0)
      rw [hd] at this
      rwa [hl', hn', Nat.mul_div_cancel_left _ hd0, Nat.mul_div_cancel_left _ hd0] at this
    have hs'c : Nat.Coprime s' n' := by
      have hg' : Nat.gcd s n = d := hd ▸ hg.symm
      have := Nat.coprime_div_gcd_div_gcd (m := s) (n := n) (hg' ▸ hd0)
      rw [hg'] at this
      rwa [hs', hn', Nat.mul_div_cancel_left _ hd0, Nat.mul_div_cancel_left _ hd0] at this
    have : NeZero n' := ⟨fun h0 => NeZero.ne n (by rw [hn', h0, mul_zero])⟩
    have hdvd : n' ∣ n := ⟨d, by rw [hn', mul_comm]⟩
    let U' : (ZMod n')ˣ := ZMod.unitOfCoprime s' hs'c * (ZMod.unitOfCoprime l' hl'c)⁻¹
    obtain ⟨U, hU⟩ := ZMod.unitsMap_surjective hdvd U'
    refine ⟨(U : ZMod n).val, ZMod.val_coe_unit_coprime U, ?_⟩
    have key : (U : ZMod n).val * l' ≡ s' [MOD n'] := by
      rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_mul, ZMod.natCast_val]
      have hcast : ((U : ZMod n).cast : ZMod n') = (U' : ZMod n') := by
        rw [← ZMod.unitsMap_val hdvd, hU]
      rw [hcast]
      simp only [U', Units.val_mul, ZMod.coe_unitOfCoprime]
      rw [mul_assoc, ← ZMod.coe_unitOfCoprime l' hl'c, Units.inv_mul, mul_one]
    have := Nat.ModEq.mul_left' d key
    rw [← hn'] at this
    rw [hl', hs', mul_left_comm]
    exact this

/-- 13:H5 — for an element `g` of order `n` in a monoid: `(g^u)^l = g^s` for some `u` coprime to `n` — some other
generator of the cycle raised to the label — exactly when `gcd(l, n) = gcd(s, n)`. -/
theorem index_condition_pow {G : Type*} [Monoid G] (g : G) (hfin : IsOfFinOrder g) (n : ℕ) [NeZero n]
    (hn : orderOf g = n) (l s : ℕ) :
    (∃ u : ℕ, u.Coprime n ∧ (g ^ u) ^ l = g ^ s) ↔ Nat.gcd l n = Nat.gcd s n := by
  rw [← index_condition n l s]
  apply exists_congr; intro u
  rw [← pow_mul, hfin.pow_eq_pow_iff_modEq, hn]

/-- 13:H5 — the null experiment's index condition on the shell: for a primitive root `g` of `ZMod p`, the
target `g^s` is `h^l` for some primitive root `h = g^u` (either chirality, `u` coprime to `p − 1`) exactly when
`gcd(l, p−1) = gcd(s, p−1)`. -/
theorem index_condition_shell (p : ℕ) [hp : Fact p.Prime] (g : ZMod p) (hg : IsPrimitiveRoot g (p - 1))
    (l s : ℕ) :
    (∃ u : ℕ, u.Coprime (p - 1) ∧ (g ^ u) ^ l = g ^ s) ↔ Nat.gcd l (p - 1) = Nat.gcd s (p - 1) := by
  have h2 := hp.out.two_le
  have : NeZero (p - 1) := ⟨by omega⟩
  have hfin : IsOfFinOrder g := orderOf_pos_iff.1 (by rw [← hg.eq_orderOf]; omega)
  exact index_condition_pow g hfin (p - 1) hg.eq_orderOf.symm l s

end index


section wallisQ

theorem centralBinom_succ_rat (n : ℕ) :
    ((centralBinom (n + 1) : ℕ) : ℚ) = 2 * (2 * n + 1) * (centralBinom n : ℚ) / (n + 1) := by
  have h := congrArg (fun m : ℕ => (m : ℚ)) (Nat.succ_mul_centralBinom_succ n)
  push_cast at h
  rw [eq_div_iff (by positivity)]
  linear_combination h

theorem centralBinom_pos_rat (n : ℕ) : (0 : ℚ) < (centralBinom n : ℕ) := by
  exact_mod_cast centralBinom_pos n

/-- 13:E2 — the exact width identity `w_n − v_n = w_n/(2n+1)` for `n ≥ 1`. -/
theorem wallis_width (n : ℕ) (hn : 1 ≤ n) :
    wallisW n - wallisV n = (wallisW n : ℚ) / (2 * n + 1) := by
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  have hC := centralBinom_pos_rat n
  unfold wallisW wallisV
  field_simp
  ring

/-- 13:E2 — `v_{n+1} = v_n · 4(n+1)²/((2n+3)(2n+1))`. -/
theorem wallisV_succ (n : ℕ) :
    (wallisV (n + 1) : ℚ) = wallisV n * (4 * (n + 1) ^ 2 / ((2 * n + 3) * (2 * n + 1))) := by
  have hC := centralBinom_pos_rat n
  unfold wallisV
  rw [centralBinom_succ_rat]
  push_cast
  field_simp
  ring

theorem wallisV_pos (n : ℕ) : (0 : ℚ) < wallisV n := by
  have hC := centralBinom_pos_rat n
  unfold wallisV; positivity

/-- 13:E2 — the Wallis lower chain `v_n` is strictly increasing. -/
theorem wallisV_strictMono (n : ℕ) : (wallisV n : ℚ) < wallisV (n + 1) := by
  rw [wallisV_succ]
  apply lt_mul_of_one_lt_right (wallisV_pos n)
  rw [one_lt_div (by positivity)]
  nlinarith

/-- 13:E2 — `w_{n+1} = w_n · 4n(n+1)/(2n+1)²`. -/
theorem wallisW_succ (n : ℕ) (hn : 1 ≤ n) :
    (wallisW (n + 1) : ℚ) = wallisW n * (4 * n * (n + 1) / (2 * n + 1) ^ 2) := by
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  have hC := centralBinom_pos_rat n
  unfold wallisW
  rw [centralBinom_succ_rat]
  push_cast
  field_simp
  ring

theorem wallisW_pos (n : ℕ) (hn : 1 ≤ n) : (0 : ℚ) < wallisW n := by
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  have hC := centralBinom_pos_rat n
  unfold wallisW; positivity

/-- 13:E2 — the Wallis upper chain `w_n` is strictly decreasing from `n = 1`. -/
theorem wallisW_strictAnti (n : ℕ) (hn : 1 ≤ n) : (wallisW (n + 1) : ℚ) < wallisW n := by
  rw [wallisW_succ n hn]
  apply mul_lt_of_lt_one_right (wallisW_pos n hn)
  rw [div_lt_one (by positivity)]
  nlinarith

end wallisQ

section wallisR

open Real

theorem centralBinom_real (n : ℕ) :
    ((centralBinom n : ℕ) : ℝ) = ((2 * n) ! : ℝ) / ((n ! : ℝ) ^ 2) := by
  have h : centralBinom n * n ! * n ! = (2 * n) ! := by
    have := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
    rwa [show 2 * n - n = n by omega, ← centralBinom_eq_two_mul_choose] at this
  have h' := congrArg (fun m : ℕ => (m : ℝ)) h
  push_cast at h'
  rw [eq_div_iff (by positivity)]
  linear_combination h'

theorem wallisV_real (n : ℕ) : ((wallisV n : ℚ) : ℝ) = 2 * Real.Wallis.W n := by
  rw [Real.Wallis.W_eq_factorial_ratio]
  unfold wallisV
  push_cast
  rw [centralBinom_real]
  have h1 : (0 : ℝ) < (n ! : ℝ) := by positivity
  have h2 : (0 : ℝ) < ((2 * n) ! : ℝ) := by positivity
  rw [show (16 : ℝ) ^ n = 2 ^ (4 * n) by rw [pow_mul]; norm_num]
  field_simp

theorem wallisW_real (n : ℕ) (hn : 1 ≤ n) :
    ((wallisW n : ℚ) : ℝ) = Real.Wallis.W n * (2 * n + 1) / n := by
  rw [Real.Wallis.W_eq_factorial_ratio]
  unfold wallisW
  push_cast
  rw [centralBinom_real]
  have h1 : (0 : ℝ) < (n ! : ℝ) := by positivity
  have h2 : (0 : ℝ) < ((2 * n) ! : ℝ) := by positivity
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [show (16 : ℝ) ^ n = 2 ^ (4 * n) by rw [pow_mul]; norm_num]
  field_simp

/-- 13:E2 — the two-sided enclosure `v_n < π < w_n` for every `n ≥ 1`: the lower chain is the doubled Wallis
partial product `2W_n < 2W_{n+1} ≤ π`, the upper chain is `W_n(2n+1)/n ≥ π(2n+1)²/(4n(n+1)) > π`. -/
theorem wallis_enclosure (n : ℕ) (hn : 1 ≤ n) :
    ((wallisV n : ℚ) : ℝ) < π ∧ π < ((wallisW n : ℚ) : ℝ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · rw [wallisV_real]
    have hs := Real.Wallis.W_succ n
    have hpos := Real.Wallis.W_pos n
    have hlt : Real.Wallis.W n < Real.Wallis.W (n + 1) := by
      rw [hs]
      apply lt_mul_of_one_lt_right hpos
      rw [_root_.div_mul_div_comm, one_lt_div (by positivity)]
      nlinarith
    have := Real.Wallis.W_le (n + 1)
    linarith
  · rw [wallisW_real n hn]
    have hle := Real.Wallis.le_W n
    have hpi := Real.pi_pos
    rw [lt_div_iff₀ hn']
    have key : π * n < ((2 * n + 1) / (2 * n + 2) * (π / 2)) * (2 * n + 1) := by
      rw [_root_.div_mul_div_comm, div_mul_eq_mul_div, lt_div_iff₀ (by positivity)]
      nlinarith
    calc π * n < ((2 * n + 1) / (2 * n + 2) * (π / 2)) * (2 * n + 1) := key
      _ ≤ Real.Wallis.W n * (2 * n + 1) := by
        apply mul_le_mul_of_nonneg_right hle; positivity

end wallisR

end FRC.Epi
