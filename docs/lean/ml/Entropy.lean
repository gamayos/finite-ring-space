import Mathlib
import FrcMathlib.Theme.Chart
import FrcMathlib.Keys.Chart

/-!
# 14-entropy — the de Sitter import, the octant and the age–rate locus: the ledger predicates in Lean (2026-09-19)

Rows of the predicate ledger of *De Sitter Entropy Estimates over Finite Holographic Substrate* (tree
`14-entropy-20260722`). The import and its congruences: `Ω = 4S + 1` fixes `S = (Ω − 1)/4` and `4 ∣ Ω − 1`
(A1); on every Carrier the quarter-turn `i² = −1` exists — the generative four of the quarter identity
`4S = Ω − 1`, the area law's chart face `4π n_A = 4S` (B9); the triality centre `3 ∣ Ω + 1` with no element of
order three on the Carrier, the c-square `2` a square exactly when `S` is even, and the laboratory Carrier
`2 408 561` decided (A2). The angle–count dictionary `2π ↔ 4S`, `π/4 ↔ S/2`, the octant's chart conversion
`(S/2)/(4S) · 2π r_H/c = (π/4) r_H/c` and Milgrom's rebooking `cH/2π = cHħ/h` (B2, C5, X2); the octant sector:
`8 ∣ 4S ⟺ S` even, the closure budget `2x ≤ S ⟺ x ≤ S/2`, the character of order eight with `ζ⁴ = −1` and the
Tsirelson square `(2(ζ + ζ⁻¹))² = 8`, the sector realised on every Carrier exactly when `S` is even, and the
c-square congruence as the sector's second face (C5, C6, X4); the horizon-quarter closure (C2). The rival
chart's age identity `t₀H_Λ = (2/3) artanh √Ω_Λ` taken as the import it is, verified against the chart's own
Friedmann equation (the standard closed form `(Ω_m/Ω_Λ)^{1/3} sinh^{2/3}(3H_Λ t/2)` solves
`(ȧ/a)² = H₀²(Ω_m a⁻³ + Ω_Λ)` with `a(0) = 0`, expanding, and in the flat case `Ω_m + Ω_Λ = 1` reaches `1`
exactly at `t H_Λ = (2/3) artanh √Ω_Λ`, with rate `H₀` there; that it is the unique such solution is not
formalised), its numeral at the fitted `0.685` bracketed, and its inversion: `π/4` is reached at
`Ω_Λ = tanh²(3π/8)` and, on `[0, 1)`, only there (A8, C3, C7, X3); the age–rate locus
`t H₀ = (π/4)/tanh(3π/8)`, the channel-1 consistency and the two-cluster chart identity (P3, C8, C4); the
effective-fluid reading `w = −1` (B8, P4); the count face and its chart dress `√(S/π)` (C9); the capacity axis —
`κ = 2` has no shell, hydrogen at `κ = 3`, the `3N` shell exactly when `12N + 1` is prime and none at `N = 2`,
the nesting bound `q⁴ < Ω` with `N ≤ 3` on the laboratory Carrier (C10, B10). Classical (tier 2) on Mathlib's
hierarchy; the finite content — the congruences, the octant on every framed shell, the Carrier and the nesting
decided by the kernel — is proved with no axioms in `FrcCore/Entropy.lean`. Since the ledger migration (task LM30) the
octant's chart theorems — the conversion, the brackets of `tanh(3π/8)`, the landing and the locus — live in the
chart theme, `FrcMathlib/Theme/Chart.lean`, as `FRC.Chart.*`; the old names below are aliases. What is outside both modules: the
realisation premises of the octant lemma (A4 reciprocity, A5 the equatorial horizon, B6 the closure budget, B7
the depth rule) — the modules decide the lemma's arithmetic, clause (iv) and the closure count, not its
realisation content; and the chart identities marked [chart] or [ΛCDM] below are identities of the continuum
reading, with no finite content of their own.
-/

namespace FRC.Entropy

open Real

/-! ## The import and its congruences (14:A1, A2, B9) -/
section carrier

/-- 14:A1, 14:B9 — the arithmetic behind the import: `Ω = 4S + 1` gives `S = (Ω − 1)/4`, `4 ∣ Ω − 1` and
`Ω ≡ 1 (mod 4)`; the quarter identity `4S = Ω − 1` is exact, the finite face of B9's area law `A = 4S`. -/
theorem cardinality {Ω S : ℕ} (h : Ω = 4 * S + 1) :
    S = (Ω - 1) / 4 ∧ 4 ∣ Ω - 1 ∧ Ω % 4 = 1 ∧ 4 * S = Ω - 1 := by
  subst h; refine ⟨by omega, ⟨S, by omega⟩, by omega, by omega⟩

/-- In any field of characteristic `≠ 2`, a root of `i² = −1` has `i⁴ = 1` and is neither `1` nor `−1`. -/
theorem quarter_turn_of_sq {K : Type*} [Field K] (i : K) (h2 : (2 : K) ≠ 0) (hi : i ^ 2 = -1) :
    i ^ 4 = 1 ∧ i ≠ 1 ∧ i ≠ -1 := by
  refine ⟨?_, ?_, ?_⟩
  · calc i ^ 4 = (i ^ 2) ^ 2 := by ring
      _ = 1 := by rw [hi]; ring
  · rintro rfl; apply h2; linear_combination hi
  · rintro rfl; apply h2; linear_combination hi

/-- 14:B9 — the arithmetic precondition of the reading (the quarter-turn rows 1:B3, 2:D2 at Carrier scale): on
every Carrier `Ω = 4S + 1` prime, `−1` is a square, so a quarter-turn `i` with `i² = −1`, `i⁴ = 1`, `i ≠ ±1`
exists in `𝔽_Ω`. That the Bekenstein–Hawking quarter `S = A/4` is this quarter-turn read on the area face is
B9's realisation clause, not formal content. -/
theorem quarter_turn (S : ℕ) [hp : Fact (Nat.Prime (4 * S + 1))] :
    IsSquare (-1 : ZMod (4 * S + 1)) ∧
    ∃ i : ZMod (4 * S + 1), i ^ 2 = -1 ∧ i ^ 4 = 1 ∧ i ≠ 1 ∧ i ≠ -1 := by
  have hsq : IsSquare (-1 : ZMod (4 * S + 1)) :=
    (ZMod.exists_sq_eq_neg_one_iff (p := 4 * S + 1)).2 (by omega)
  refine ⟨hsq, ?_⟩
  obtain ⟨i, hi⟩ := hsq
  have h2 : (2 : ZMod (4 * S + 1)) ≠ 0 := by
    intro h
    have := (ZMod.natCast_eq_zero_iff 2 (4 * S + 1)).1 (by exact_mod_cast h)
    have h5 : 5 ≤ 4 * S + 1 := by
      have := hp.out.two_le
      have h1 : 4 * S + 1 ≠ 4 := by omega
      have h3 : 4 * S + 1 ≠ 3 := by omega
      have h4 : 4 * S + 1 ≠ 2 := by omega
      omega
    exact absurd (Nat.le_of_dvd (by norm_num) this) (by omega)
  have hi2 : i ^ 2 = -1 := by rw [sq, ← hi]
  exact ⟨i, hi2, quarter_turn_of_sq i h2 hi2⟩

/-- 14:B9 [chart] — the area law's chart face: with `n_A = S/π` Planck cells in the projected horizon,
`4π n_A = 4S`, the full phase cycle; a chart identity with no finite content (the finite face is
`cardinality`). -/
theorem area_law_chart (S : ℝ) : 4 * π * (S / π) = 4 * S := by
  have := Real.pi_ne_zero
  field_simp

/-- 14:A2 — the arithmetic behind the triality centre: `S ≡ 1 (mod 3)` gives `3 ∣ Ω + 1` and `3 ∤ Ω − 1 = 4S`,
so the Carrier `𝔽_Ω` carries no element of order three in its unit group (that the centre lives in the
quadratic extension, `C₃ ⊂ C_{Ω+1}`, is the corpus's gloss, not proved here). -/
theorem triality_centre (S : ℕ) (h : S % 3 = 1) [Fact (Nat.Prime (4 * S + 1))] :
    3 ∣ 4 * S + 1 + 1 ∧ ¬ 3 ∣ 4 * S ∧ ∀ x : (ZMod (4 * S + 1))ˣ, orderOf x ≠ 3 := by
  refine ⟨⟨(4 * S + 2) / 3, by omega⟩, by omega, fun x hx => ?_⟩
  have hd := orderOf_dvd_card (x := x)
  rw [ZMod.card_units, hx] at hd
  omega

/-- 14:A2 — the relation behind the c-square (upstream 2-geometry; Mathlib's quadratic-reciprocity
supplement): on a Carrier `Ω = 4S + 1` prime, `2` is a square in `𝔽_Ω` — equivalently `2⁻¹`, the residue `c²`
of the constants correspondence — exactly when `S` is even (`Ω ≡ 1 (mod 8)`). -/
theorem c_square (S : ℕ) [hp : Fact (Nat.Prime (4 * S + 1))] :
    (IsSquare (2 : ZMod (4 * S + 1)) ↔ Even S) ∧ (IsSquare (2⁻¹ : ZMod (4 * S + 1)) ↔ Even S) := by
  have hne : 4 * S + 1 ≠ 2 := by omega
  have h2 : (IsSquare (2 : ZMod (4 * S + 1)) ↔ Even S) := by
    rw [ZMod.exists_sq_eq_two_iff hne, Nat.even_iff]; omega
  refine ⟨h2, ?_⟩
  rw [← h2]
  have h2z : (2 : ZMod (4 * S + 1)) ≠ 0 := by
    intro h
    have := (ZMod.natCast_eq_zero_iff 2 (4 * S + 1)).1 (by exact_mod_cast h)
    have := Nat.le_of_dvd (by norm_num) this
    have := hp.out.two_le
    omega
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨r⁻¹, by rw [← mul_inv, ← hr, inv_inv]⟩
  · rintro ⟨r, hr⟩
    exact ⟨r⁻¹, by rw [← mul_inv, ← hr]⟩

/-- 14:A2 — the laboratory Carrier `Ω = 2 408 561`, `S = 602 140`: the three congruences as host-decided
values — `S` even, `S ≡ 1 (mod 3)`, `4S + 1` prime. -/
theorem carrierLab :
    4 * 602140 + 1 = 2408561 ∧ Even 602140 ∧ 602140 % 3 = 1 ∧ Nat.Prime 2408561 :=
  ⟨by norm_num, by decide, by norm_num, by norm_num⟩

/-- 14:C2 [chart] — the horizon-quarter closure is a consistency loop: the shell entropy `S(p) = (p² − 1)/4`
read at the coherence-horizon point `p² = Ω` returns `(Ω − 1)/4 = S`, the import itself. No shell has `p² = Ω`
(`Ω` is prime); the closure is read at the chart point `√Ω`. -/
theorem horizon_quarter_closure (Ω S : ℕ) (p : ℝ) (hΩ : Ω = 4 * S + 1) (hp : p ^ 2 = Ω) :
    (p ^ 2 - 1) / 4 = S := by
  rw [hp, hΩ]; push_cast; ring

end carrier

/-! ## The angle–count dictionary (14:B2, C5, X2) -/
section dictionary

/-- 14:B2 [chart] — the angle–count dictionary: with the full cycle `2π ↔ 4S`, an angle `θ` is the chart face
of the count `θ/(2π) · 4S`: `π ↔ 2S`, `π/2 ↔ S`, `π/4 ↔ S/2` chronons; the count face is
`FRC.Entropy.octant_count` in the core. -/
theorem dictionary (S : ℝ) :
    π / (2 * π) * (4 * S) = 2 * S ∧ (π / 2) / (2 * π) * (4 * S) = S ∧
    (π / 4) / (2 * π) * (4 * S) = S / 2 := by
  have := Real.pi_ne_zero
  refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> ring

/-- 14:X2 [chart] — Milgrom's rebooking, the substitution `h = 2πħ`: the floor `a₀ = cH/2π` is `cHħ/h`, the
per-cycle rate budget per step. That the `2π` carries zero freedom is X2's realisation clause (B2 fixes the
convention), not formal content. -/
theorem milgrom_rebooking (c H ħ h : ℝ) (hh : h = 2 * π * ħ) (hħ : ħ ≠ 0) :
    c * H / (2 * π) = c * H * ħ / h := by
  subst hh; have := Real.pi_ne_zero; field_simp

end dictionary

/-! ## The octant sector (14:C5, C6, X4) -/
section octant

/-- 14:C6, 14:X4 — the arithmetic face: the octant sector `C₈ ⊂ C_{4S}` exists exactly when `8 ∣ 4S`, that is
when `S` is even (X4's claim about what certifies the congruence is a realisation clause, not this
equivalence). -/
theorem octant_sector_iff (S : ℕ) : 8 ∣ 4 * S ↔ Even S := by
  rw [Nat.even_iff, Nat.dvd_iff_mod_eq_zero]; omega

/-- 14:C5, 14:B6 — the closure count, clauses (iii)–(iv): given B6's accounting (a two-way registration of
depth `x` costs `2x` of the one-way budget `S`; the realisation, not formalised), the closable depths are exactly
`x ≤ S/2`, and on a Carrier with `S` even the octant count `S/2` closes the budget, `2 · (S/2) = S`. -/
theorem closure_budget (S : ℕ) :
    (∀ x, 2 * x ≤ S ↔ x ≤ S / 2) ∧ (Even S → 2 * (S / 2) = S) := by
  refine ⟨fun x => by omega, fun hS => ?_⟩
  rw [Nat.even_iff] at hS; omega

/-- 14:C6 — the octant character: in any field an element `ζ` of order eight (`ζ⁸ = 1`, `ζ⁴ ≠ 1`) has
`ζ⁴ = −1`, and the residue the Tsirelson identity carries has square `(ζ + ζ⁻¹)² = 2`, `(2(ζ + ζ⁻¹))² = 8`. -/
theorem octant_character {K : Type*} [Field K] (ζ : K) (h8 : ζ ^ 8 = 1) (h4 : ζ ^ 4 ≠ 1) :
    ζ ^ 4 = -1 ∧ (ζ + ζ⁻¹) ^ 2 = 2 ∧ (2 * (ζ + ζ⁻¹)) ^ 2 = 8 := by
  have hz : ζ ≠ 0 := by rintro rfl; simp at h8
  have hsq : ζ ^ 4 * ζ ^ 4 = 1 := by rw [← pow_add]; exact h8
  have h4' : ζ ^ 4 = -1 := by
    rcases mul_self_eq_one_iff.1 hsq with h | h
    · exact absurd h h4
    · exact h
  refine ⟨h4', ?_, ?_⟩
  · field_simp; linear_combination h4'
  · field_simp; linear_combination 4 * h4'

/-- 14:C6, 14:X4 — on every Carrier `Ω = 4S + 1` prime the octant sector is realised exactly when `S` is even:
the unit group of `𝔽_Ω` has an element of order eight iff `8 ∣ 4S`. -/
theorem octant_exists_iff (S : ℕ) [Fact (Nat.Prime (4 * S + 1))] :
    (∃ ζ : (ZMod (4 * S + 1))ˣ, orderOf ζ = 8) ↔ Even S := by
  rw [← octant_sector_iff]
  constructor
  · rintro ⟨ζ, hζ⟩
    have hd := orderOf_dvd_card (x := ζ)
    rwa [ZMod.card_units, hζ, Nat.add_sub_cancel] at hd
  · intro h8
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod (4 * S + 1))ˣ)
    rw [Nat.card_eq_fintype_card, ZMod.card_units, Nat.add_sub_cancel] at hg
    refine ⟨g ^ (orderOf g / 8), orderOf_pow_orderOf_div ?_ ?_⟩
    · rw [hg]; have := (Fact.out : Nat.Prime (4 * S + 1)).two_le; omega
    · rw [hg]; exact h8

/-- 14:X4 — the arithmetic face of the second face: the c-square (`2` a square in `𝔽_Ω`) holds exactly when
the octant sector exists — the two congruence faces coincide on every Carrier. The reading of the octant as
the well-definedness of the measured age is X4's realisation clause, not formal content. -/
theorem octant_second_face (S : ℕ) [Fact (Nat.Prime (4 * S + 1))] :
    IsSquare (2 : ZMod (4 * S + 1)) ↔ ∃ ζ : (ZMod (4 * S + 1))ˣ, orderOf ζ = 8 := by
  rw [(c_square S).1, octant_exists_iff]

end octant

/-! ## The rival chart's age identity and the locus (14:C3, C7, C8, P3, C4, B8) -/
section age

/-- 14:A8 [ΛCDM], consumed by 14:C3 — the rival chart's age identity as the import it is: in flat
matter-plus-`Λ` the product of the age and the asymptotic rate is `t₀H_Λ = (2/3) artanh √Ω_Λ`. Moved to the chart
theme (`FRC.Chart.lcdmAge`, 7 October 2026); this name is its alias. It is verified against the chart's own Friedmann
equation in `lcdm_age` below. That a landing of it on `π/4` restates the fit is C3's judgment under B5, not formal
content. -/
noncomputable def lcdmAge (Ω : ℝ) : ℝ := FRC.Chart.lcdmAge Ω

/-- 14:C7, 14:X3, 14:X6 [ΛCDM] — the octant inversion, moved to the chart theme (`FRC.Chart.octant_inversion`); this name
is its alias. -/
theorem octant_inversion :
    lcdmAge (tanh (3 * π / 8) ^ 2) = π / 4 ∧
    ∀ Ω : ℝ, 0 ≤ Ω → Ω < 1 → lcdmAge Ω = π / 4 → Ω = tanh (3 * π / 8) ^ 2 :=
  FRC.Chart.octant_inversion

/-- 14:C8 [ΛCDM] — the channel-1 consistency: with `Λ = 3Ω_Λ H₀²/c²` (the definition of `Ω_Λ`) the asymptotic
rate is `H_Λ = c√(Λ/3) = H₀√Ω_Λ`, and the locus read on it, `H_Λ/tanh(3π/8)`, returns `H₀` exactly when
`Ω_Λ = tanh²(3π/8)`; at the fitted `0.685` the return is within `0.1 %` (`channel_one_numeral`). -/
theorem channel_one_consistency (H0 c Ω Λ : ℝ) (hH0 : 0 < H0) (hc : 0 < c) (hΩ : 0 ≤ Ω)
    (hΛ : Λ = 3 * Ω * H0 ^ 2 / c ^ 2) :
    c * √(Λ / 3) = H0 * √Ω ∧ (H0 * √Ω / tanh (3 * π / 8) = H0 ↔ Ω = tanh (3 * π / 8) ^ 2) := by
  have hpos := FRC.Chart.tanh_octant_pos
  constructor
  · rw [hΛ, show 3 * Ω * H0 ^ 2 / c ^ 2 / 3 = Ω * (H0 / c) ^ 2 by field_simp,
      Real.sqrt_mul hΩ, Real.sqrt_sq (by positivity)]
    field_simp
  · constructor
    · intro h
      have h' : √Ω = tanh (3 * π / 8) := by
        field_simp at h
        nlinarith [h]
      rw [← h', Real.sq_sqrt hΩ]
    · intro h
      rw [h, Real.sqrt_sq hpos.le]; field_simp

/-- 14:C8 [ΛCDM] — the two-cluster chart identity: with `S = π (r_H/ℓ_P)²`, a `Λ`-face reading
`r_H = c/(H₀√Ω_Λ)` against a rate-face reading `r_H = c/H_rate` gives `S_Λ/S_rate = (H_rate/H₀)²/Ω_Λ` — the
definition of `Ω_Λ` read on the rows, the Hubble tension displayed and no framework content. -/
theorem cluster_identity (c H0 Hr Ω ℓ : ℝ) (hc : c ≠ 0) (hΩ : 0 < Ω) (hℓ : ℓ ≠ 0) :
    (π * (c / (H0 * √Ω) / ℓ) ^ 2) / (π * (c / Hr / ℓ) ^ 2) = (Hr / H0) ^ 2 / Ω := by
  have hs : √Ω ≠ 0 := (Real.sqrt_pos.2 hΩ).ne'
  have hpi := Real.pi_ne_zero
  rcases eq_or_ne H0 0 with rfl | hH0
  · simp
  rcases eq_or_ne Hr 0 with rfl | hr
  · simp
  field_simp
  rw [Real.sq_sqrt hΩ.le]

/-- 14:B8, 14:P4 [ΛCDM] — the arithmetic of the effective-fluid reading: the rival chart's continuity law
`ρ̇ + 3H(ρ + p) = 0` with `ρ̇ = 0` (a fixed cardinality admits no evolution) and `H ≠ 0` gives `p = −ρ`,
`w = p/ρ = −1` exactly. B8's single-component clause and P4's `w₀w_a` rigidity are realisation content, not
formalised. -/
theorem fluid_w (H ρ p ρ' : ℝ) (hH : H ≠ 0) (hρ : ρ ≠ 0) (hρ' : ρ' = 0) (h : ρ' + 3 * H * (ρ + p) = 0) :
    p = -ρ ∧ p / ρ = -1 := by
  subst hρ'
  have hp : p = -ρ := by
    have : ρ + p = 0 := by
      rcases mul_eq_zero.1 (by linarith : 3 * H * (ρ + p) = 0) with h3 | h3
      · exact absurd (by linarith : H = 0) hH
      · exact h3
    linarith
  exact ⟨hp, by rw [hp, neg_div, div_self hρ]⟩


/-- 14:C8 — the channel-1 return bracketed: at the fitted `Ω_Λ = 0.685` (A8, taken as data) the locus returns
`H_Λ/tanh(3π/8) = H₀ √0.685/tanh(3π/8)` with `1 < √0.685/tanh(3π/8) < 1.001` — the channel-1 `H₀` to
`0.1 %`. -/
theorem channel_one_numeral :
    (1 : ℝ) < √0.685 / tanh (3 * π / 8) ∧ √0.685 / tanh (3 * π / 8) < 1.001 := by
  obtain ⟨hl, hu⟩ := FRC.Chart.tanh_octant_bounds
  have hpos : (0 : ℝ) < tanh (3 * π / 8) := by linarith
  have hs1 : (0.82764 : ℝ) < √0.685 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hs2 : √(0.685 : ℝ) < 0.82765 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  constructor
  · rw [lt_div_iff₀ hpos]; linarith
  · rw [div_lt_iff₀ hpos]; linarith

end age

/-! ## The rival chart's age identity, verified against its own Friedmann equation (14:A8, C3) -/
section friedmann

/-- 14:A8 [ΛCDM] — the standard flat matter-plus-`Λ` scale factor of the rival chart, for `t ≥ 0`:
`a(t) = (Ω_m/Ω_Λ)^{1/3} sinh^{2/3}(3H_Λ t/2)`, with `H_Λ` the asymptotic rate. -/
noncomputable def lcdmScale (Ωm ΩΛ HΛ t : ℝ) : ℝ :=
  (Ωm / ΩΛ) ^ ((1 : ℝ) / 3) * sinh (3 * HΛ * t / 2) ^ ((2 : ℝ) / 3)

/-- The cube of the scale factor for `t ≥ 0`: `a³ = (Ω_m/Ω_Λ) sinh²(3H_Λ t/2)`. -/
theorem lcdmScale_cube (Ωm ΩΛ HΛ t : ℝ) (hm : 0 < Ωm) (hΛ : 0 < ΩΛ) (hH : 0 ≤ HΛ) (ht : 0 ≤ t) :
    lcdmScale Ωm ΩΛ HΛ t ^ 3 = Ωm / ΩΛ * sinh (3 * HΛ * t / 2) ^ 2 := by
  have hs : 0 ≤ sinh (3 * HΛ * t / 2) := by
    rw [← Real.sinh_zero]; exact Real.sinh_le_sinh.2 (by positivity)
  have hq : 0 ≤ Ωm / ΩΛ := by positivity
  unfold lcdmScale
  rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hq, ← Real.rpow_mul hs]
  norm_num

/-- The scale factor is positive for `t > 0`. -/
theorem lcdmScale_pos (Ωm ΩΛ HΛ t : ℝ) (hm : 0 < Ωm) (hΛ : 0 < ΩΛ) (hH : 0 < HΛ) (ht : 0 < t) :
    0 < lcdmScale Ωm ΩΛ HΛ t :=
  mul_pos (Real.rpow_pos_of_pos (by positivity) _)
    (Real.rpow_pos_of_pos (Real.sinh_pos_iff.2 (by positivity)) _)

/-- The derivative of the scale factor for `t > 0`: `ȧ = H_Λ · (cosh x / sinh x) · a` with `x = 3H_Λ t/2`. -/
theorem lcdm_hasDerivAt (Ωm ΩΛ HΛ t : ℝ) (hm : 0 < Ωm) (hΛ : 0 < ΩΛ) (hH : 0 < HΛ) (ht : 0 < t) :
    HasDerivAt (lcdmScale Ωm ΩΛ HΛ)
      (HΛ * (cosh (3 * HΛ * t / 2) / sinh (3 * HΛ * t / 2)) * lcdmScale Ωm ΩΛ HΛ t) t := by
  set x := 3 * HΛ * t / 2 with hx
  have hxpos : 0 < x := by positivity
  set s := sinh x with hsdef
  have hs : 0 < s := Real.sinh_pos_iff.2 hxpos
  set K := (Ωm / ΩΛ) ^ ((1 : ℝ) / 3) with hK
  have hKpos : 0 < K := Real.rpow_pos_of_pos (by positivity) _
  have ha : lcdmScale Ωm ΩΛ HΛ t = K * s ^ ((2 : ℝ) / 3) := rfl
  have h1 : HasDerivAt (fun y : ℝ => 3 * HΛ * y / 2) (3 * HΛ / 2) t := by
    have := ((hasDerivAt_id t).const_mul (3 * HΛ)).div_const 2
    simpa using this
  have h2 : HasDerivAt (fun y : ℝ => sinh (3 * HΛ * y / 2)) (cosh x * (3 * HΛ / 2)) t := h1.sinh
  have h3 : HasDerivAt (fun y : ℝ => sinh (3 * HΛ * y / 2) ^ ((2 : ℝ) / 3))
      (cosh x * (3 * HΛ / 2) * ((2 : ℝ) / 3) * s ^ ((2 : ℝ) / 3 - 1)) t :=
    h2.rpow_const (Or.inl hs.ne')
  have h4 : HasDerivAt (lcdmScale Ωm ΩΛ HΛ)
      (K * (cosh x * (3 * HΛ / 2) * ((2 : ℝ) / 3) * s ^ ((2 : ℝ) / 3 - 1))) t := h3.const_mul K
  refine h4.congr_deriv ?_
  have hsub : s ^ ((2 : ℝ) / 3 - 1) = s ^ ((2 : ℝ) / 3) / s := by
    rw [Real.rpow_sub hs, Real.rpow_one]
  rw [ha, hsub]; field_simp

/-- 14:A8, 14:C3 [ΛCDM] — the closed form solves the flat Friedmann equation of the rival chart with matter
and `Λ`: `a(0) = 0`, `a(t) > 0` and `ȧ > 0` for `t > 0` (the expanding branch), and
`(ȧ/a)² = H₀²(Ω_m a⁻³ + Ω_Λ)` with `H_Λ = H₀ √Ω_Λ`; that it is the unique such solution is not formalised. -/
theorem lcdm_friedmann (Ωm ΩΛ H0 t : ℝ) (hm : 0 < Ωm) (hΛ : 0 < ΩΛ) (hH : 0 < H0) (ht : 0 < t) :
    let HΛ := H0 * √ΩΛ
    let a' := HΛ * (cosh (3 * HΛ * t / 2) / sinh (3 * HΛ * t / 2)) * lcdmScale Ωm ΩΛ HΛ t
    lcdmScale Ωm ΩΛ HΛ 0 = 0 ∧ 0 < lcdmScale Ωm ΩΛ HΛ t ∧ 0 < a' ∧
    HasDerivAt (lcdmScale Ωm ΩΛ HΛ) a' t ∧
    (a' / lcdmScale Ωm ΩΛ HΛ t) ^ 2 = H0 ^ 2 * (Ωm / lcdmScale Ωm ΩΛ HΛ t ^ 3 + ΩΛ) := by
  intro HΛ a'
  have hHpos : 0 < HΛ := by positivity
  have hxpos : 0 < 3 * HΛ * t / 2 := by positivity
  have hs : 0 < sinh (3 * HΛ * t / 2) := Real.sinh_pos_iff.2 hxpos
  have hc : 0 < cosh (3 * HΛ * t / 2) := Real.cosh_pos _
  have hapos := lcdmScale_pos Ωm ΩΛ HΛ t hm hΛ hHpos ht
  refine ⟨?_, hapos, by positivity, lcdm_hasDerivAt Ωm ΩΛ HΛ t hm hΛ hHpos ht, ?_⟩
  · unfold lcdmScale
    simp [Real.zero_rpow (by norm_num : (2 : ℝ) / 3 ≠ 0)]
  · have hcube := lcdmScale_cube Ωm ΩΛ HΛ t hm hΛ hHpos.le ht.le
    have hH2 : HΛ ^ 2 = H0 ^ 2 * ΩΛ := by
      show (H0 * √ΩΛ) ^ 2 = H0 ^ 2 * ΩΛ
      rw [mul_pow, Real.sq_sqrt hΛ.le]
    have hratio : a' / lcdmScale Ωm ΩΛ HΛ t = HΛ * (cosh (3 * HΛ * t / 2) / sinh (3 * HΛ * t / 2)) := by
      show HΛ * (cosh (3 * HΛ * t / 2) / sinh (3 * HΛ * t / 2)) * lcdmScale Ωm ΩΛ HΛ t /
        lcdmScale Ωm ΩΛ HΛ t = _
      field_simp
    rw [hratio, hcube, mul_pow, div_pow, Real.cosh_sq, hH2]
    field_simp
    ring

/-- The scale factor reaches `1` exactly when `sinh²(3H_Λ t/2) = Ω_Λ/Ω_m` (`t > 0`). -/
theorem lcdmScale_eq_one_iff (Ωm ΩΛ HΛ t : ℝ) (hm : 0 < Ωm) (hΛ : 0 < ΩΛ) (hH : 0 < HΛ) (ht : 0 < t) :
    lcdmScale Ωm ΩΛ HΛ t = 1 ↔ sinh (3 * HΛ * t / 2) ^ 2 = ΩΛ / Ωm := by
  have hapos := lcdmScale_pos Ωm ΩΛ HΛ t hm hΛ hH ht
  rw [← pow_eq_one_iff_of_nonneg hapos.le (by norm_num : (3 : ℕ) ≠ 0),
    lcdmScale_cube Ωm ΩΛ HΛ t hm hΛ hH.le ht.le]
  constructor
  · intro h; field_simp at h ⊢; linarith
  · intro h; rw [h]; field_simp

/-- 14:A8, 14:C3, 14:X6 [ΛCDM] — the age identity verified: with `Ω_m + Ω_Λ = 1` the closed-form scale factor
reaches `1` at the time `t` exactly when `t H_Λ = (2/3) artanh √Ω_Λ`, so the product `t₀H_Λ` of C3 is the
chart's own age–rate relation, a function of the one fitted parameter. -/
theorem lcdm_age (Ωm ΩΛ H0 t : ℝ) (hm : 0 < Ωm) (hΛ : 0 < ΩΛ) (hsum : Ωm + ΩΛ = 1) (hH : 0 < H0)
    (ht : 0 < t) :
    lcdmScale Ωm ΩΛ (H0 * √ΩΛ) t = 1 ↔ t * (H0 * √ΩΛ) = lcdmAge ΩΛ := by
  set HΛ := H0 * √ΩΛ with hHΛ
  have hHpos : 0 < HΛ := by positivity
  set x := 3 * HΛ * t / 2 with hx
  have hxpos : 0 < x := by positivity
  have hs : 0 < sinh x := Real.sinh_pos_iff.2 hxpos
  have hΛ1 : ΩΛ < 1 := by linarith
  have hsq : √ΩΛ ∈ Set.Ioo (-1 : ℝ) 1 := by
    refine ⟨by linarith [Real.sqrt_nonneg ΩΛ], ?_⟩
    rw [Real.sqrt_lt' one_pos]; linarith
  rw [lcdmScale_eq_one_iff Ωm ΩΛ HΛ t hm hΛ hHpos ht]
  have hx' : t * HΛ = lcdmAge ΩΛ ↔ x = artanh √ΩΛ := by
    unfold lcdmAge FRC.Chart.lcdmAge; rw [hx]; constructor <;> intro h <;> linarith
  rw [hx']
  constructor
  · intro h
    have htanh : tanh x = √ΩΛ := by
      have hc : 0 < cosh x := Real.cosh_pos x
      have ht2 : tanh x ^ 2 = ΩΛ := by
        rw [Real.tanh_eq_sinh_div_cosh, div_pow, Real.cosh_sq, h]
        field_simp; linarith
      have htpos : 0 < tanh x := by
        rw [Real.tanh_eq_sinh_div_cosh]; exact div_pos hs hc
      rw [← ht2, Real.sqrt_sq htpos.le]
    rw [← htanh, Real.artanh_tanh]
  · intro h
    show sinh x ^ 2 = ΩΛ / Ωm
    rw [h, Real.sinh_artanh hsq, div_pow, Real.sq_sqrt hΛ.le, Real.sq_sqrt (by linarith)]
    congr 1; linarith

/-- 14:A8, 14:C3 [ΛCDM] — the rate today: at the time the flat closed form reaches `1`, its derivative is
`H₀` — `H₀` is the present rate of the solution, `H_Λ = H₀√Ω_Λ` its asymptotic rate. -/
theorem lcdm_rate_today (Ωm ΩΛ H0 t : ℝ) (hm : 0 < Ωm) (hΛ : 0 < ΩΛ) (hsum : Ωm + ΩΛ = 1) (hH : 0 < H0)
    (ht : 0 < t) (h1 : lcdmScale Ωm ΩΛ (H0 * √ΩΛ) t = 1) :
    HasDerivAt (lcdmScale Ωm ΩΛ (H0 * √ΩΛ)) H0 t := by
  set HΛ := H0 * √ΩΛ with hHΛ
  have hHpos : 0 < HΛ := by positivity
  have hxpos : 0 < 3 * HΛ * t / 2 := by positivity
  have hs : 0 < sinh (3 * HΛ * t / 2) := Real.sinh_pos_iff.2 hxpos
  have hc : 0 < cosh (3 * HΛ * t / 2) := Real.cosh_pos _
  have hsin := (lcdmScale_eq_one_iff Ωm ΩΛ HΛ t hm hΛ hHpos ht).1 h1
  have hsqrt : 0 < √ΩΛ := Real.sqrt_pos.2 hΛ
  -- `(cosh/sinh)² = 1/Ω_Λ`, both sides positive
  have hcs : cosh (3 * HΛ * t / 2) / sinh (3 * HΛ * t / 2) = (√ΩΛ)⁻¹ := by
    rw [← pow_left_inj₀ (by positivity) (by positivity) (by norm_num : (2 : ℕ) ≠ 0), div_pow,
      Real.cosh_sq, hsin, inv_pow, Real.sq_sqrt hΛ.le]
    field_simp; linarith
  refine (lcdm_hasDerivAt Ωm ΩΛ HΛ t hm hΛ hHpos ht).congr_deriv ?_
  rw [h1, hcs, mul_one, hHΛ]; field_simp

/-- The Taylor brackets of `e^t` at `t = 0.36118` and `t = 0.36128` (seven terms, Mathlib's tail bound). -/
theorem exp_tail_bounds' : exp (0.36118 : ℝ) < 1.4350218 ∧ (1.4351649 : ℝ) < exp 0.36128 := by
  constructor
  · have h := Real.exp_bound' (x := 0.36118) (by norm_num) (by norm_num) (n := 7) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  · have h := abs_le.1 (Real.exp_bound (x := 0.36128) (by rw [abs_of_pos (by norm_num)]; norm_num)
      (n := 7) (by norm_num))
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 0.36128)] at h
    have h1 := h.1
    norm_num [Finset.sum_range_succ, Nat.factorial] at h1 ⊢
    linarith

/-- 14:C3 — the audit numeral bracketed: at the fitted `Ω_Λ = 0.685` (A8, taken as data) the rival chart's
`t₀H_Λ = (2/3) artanh √0.685` lies in `(0.7870, 0.7871)` — the paper's `0.7871` — and exceeds `π/4` by
between `0.21 %` and `0.22 %` of `π/4`, the audit's "≈ 0.2 %". -/
theorem age_bracket :
    (0.7870 : ℝ) < lcdmAge 0.685 ∧ lcdmAge 0.685 < 0.7871 ∧
    0.0021 * (π / 4) < lcdmAge 0.685 - π / 4 ∧ lcdmAge 0.685 - π / 4 < 0.0022 * (π / 4) := by
  have hs1 : (0.82764 : ℝ) < √0.685 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hs2 : √(0.685 : ℝ) < 0.82765 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hlog : lcdmAge 0.685 = 2 / 3 * (1 / 2 * log ((1 + √0.685) / (1 - √0.685))) := by
    unfold lcdmAge FRC.Chart.lcdmAge; rw [Real.artanh_eq_half_log ⟨by linarith, by linarith⟩]
  have hy1 : (10.6036 : ℝ) < (1 + √0.685) / (1 - √0.685) := by
    rw [lt_div_iff₀ (by linarith)]; linarith
  have hy2 : (1 + √0.685) / (1 - √0.685) < 10.6044 := by
    rw [div_lt_iff₀ (by linarith)]; linarith
  have he := exp_tail_bounds'
  have he1 := Real.exp_one_gt_d9
  have he2 := Real.exp_one_lt_d9
  have hpos : (0 : ℝ) < exp 1 := Real.exp_pos 1
  have hE1 : exp (2.36118 : ℝ) < 10.6036 := by
    rw [show (2.36118 : ℝ) = 1 + 1 + 0.36118 by norm_num, Real.exp_add, Real.exp_add]
    nlinarith [mul_pos hpos hpos, Real.exp_pos (0.36118 : ℝ)]
  have hE2 : (10.6044 : ℝ) < exp 2.36128 := by
    rw [show (2.36128 : ℝ) = 1 + 1 + 0.36128 by norm_num, Real.exp_add, Real.exp_add]
    nlinarith [mul_pos hpos hpos, Real.exp_pos (0.36128 : ℝ)]
  have hl1 : (2.36118 : ℝ) < log ((1 + √0.685) / (1 - √0.685)) := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]; linarith
  have hl2 : log ((1 + √0.685) / (1 - √0.685)) < 2.36128 := by
    rw [Real.log_lt_iff_lt_exp (by linarith)]; linarith
  have hpi1 := Real.pi_gt_d6
  have hpi2 := Real.pi_lt_d6
  rw [hlog]
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

end friedmann

/-! ## The registrable triangle and the capacity axis (14:C9, C10, B10) -/
section triangle

/-- 14:C9 [chart] — the count face and its chart dress: `S = π x²` with `x = r_H/ℓ_P > 0` gives `x = √(S/π)`
and `√S = √π · x`, the solid-angle `π` the declared transport between the count face `√S` and the drawn
width. -/
theorem count_face (S x : ℝ) (hx : 0 < x) (h : S = π * x ^ 2) :
    x = √(S / π) ∧ √S = √π * x := by
  have hpi := Real.pi_pos
  constructor
  · rw [h, mul_div_cancel_left₀ _ hpi.ne', Real.sqrt_sq hx.le]
  · rw [h, Real.sqrt_mul hpi.le, Real.sqrt_sq hx.le]

/-- 14:C10 — the primality behind the capacity axis's identifications: `κ = 1` (the bare proton) is a shell,
`𝔽₅`; `κ = 2` has no shell (`9` is composite); `κ_H = 3` (ground-state hydrogen, the first non-trivial Object)
is the shell `𝔽₁₃`. -/
theorem capacity_zero : Nat.Prime (4 * 1 + 1) ∧ ¬ Nat.Prime (4 * 2 + 1) ∧ Nat.Prime (4 * 3 + 1) :=
  ⟨by norm_num, by norm_num, by norm_num⟩

/-- 14:B10 — hydrogen units: the shell of capacity `3N` is `𝔽_{12N+1}`, so it exists exactly when `12N + 1` is
prime — `N = 1` (`13`) and `N = 3` (`37`) exist, `N = 2` (`25`) does not; and the nesting bound, the necessity
direction: a shell `q` registered whole by a Subject `p` of the Carrier `Ω` (`q² < p`, `p² < Ω`) has `q⁴ < Ω`,
so `(12N + 1)⁴ < Ω`; the existence of such a Subject is exhibited on the laboratory Carrier (`nesting_lab`). -/
theorem hydrogen_units :
    Nat.Prime 13 ∧ ¬ Nat.Prime 25 ∧ Nat.Prime 37 ∧
    ∀ q p Ω : ℕ, q ^ 2 < p → p ^ 2 < Ω → q ^ 4 < Ω := by
  refine ⟨by norm_num, by norm_num, by norm_num, fun q p Ω hq hp => ?_⟩
  calc q ^ 4 = (q ^ 2) ^ 2 := by ring
    _ < p ^ 2 := by gcongr
    _ < Ω := hp

/-- 14:B10 — on the laboratory Carrier `Ω = 2 408 561` the bound is `N ≤ 3`: `37⁴ < Ω < 49⁴`; and the shell of
capacity `9` (`q = 37`) nests through the Subject `p = 1373 = 4 · 343 + 1`, prime: `37² < 1373`,
`1373² < Ω`. -/
theorem nesting_lab :
    37 ^ 4 < 2408561 ∧ 2408561 < 49 ^ 4 ∧ (∀ N : ℕ, (12 * N + 1) ^ 4 < 2408561 → N ≤ 3) ∧
    Nat.Prime 1373 ∧ 1373 = 4 * 343 + 1 ∧ 37 ^ 2 < 1373 ∧ 1373 ^ 2 < 2408561 := by
  refine ⟨by norm_num, by norm_num, fun N h => ?_, by norm_num, by norm_num, by norm_num, by norm_num⟩
  by_contra hN
  have h4 : 4 ≤ N := by omega
  have : (12 * 4 + 1) ^ 4 ≤ (12 * N + 1) ^ 4 := by gcongr
  omega

end triangle

/-! ## 14:B11–B13 — the additive window, the lock of like units, the shells of capacity `3N` (master F7, returned
15 October 2026) -/
section window

/-- 14:B11 — the additive window: for modes at heights `hᵢ` with `|hᵢ| ≤ κᵢ` (as a list of pairs `(hᵢ, κᵢ)`) the
total has `|Σhᵢ| ≤ Σκᵢ`; the bound is attained by `hᵢ = κᵢ`; and every total `t` with `|t| ≤ Σκᵢ` occurs — the
first height the clamp of `t` to `[−κ₁, κ₁]`, the rest by induction. -/
theorem additive_window :
    (∀ (l : List (ℤ × ℕ)), (∀ x ∈ l, x.1.natAbs ≤ x.2) → (l.map Prod.fst).sum.natAbs ≤ (l.map Prod.snd).sum) ∧
    (∀ (κ : List ℕ), ((κ.map fun (k : ℕ) => (k : ℤ)).sum).natAbs = κ.sum) ∧
    (∀ (κ : List ℕ) (t : ℤ), t.natAbs ≤ κ.sum →
      ∃ l : List (ℤ × ℕ), l.map Prod.snd = κ ∧ (∀ x ∈ l, x.1.natAbs ≤ x.2) ∧ (l.map Prod.fst).sum = t) := by
  refine ⟨?_, ?_, ?_⟩
  · intro l
    induction l with
    | nil => intro _; simp
    | cons x t ih =>
      intro hb
      have h1 : x.1.natAbs ≤ x.2 := hb x (List.mem_cons_self ..)
      have ih' := ih (fun y hy => hb y (List.mem_cons_of_mem _ hy))
      simp only [List.map_cons, List.sum_cons]
      exact Nat.le_trans (Int.natAbs_add_le _ _) (Nat.add_le_add h1 ih')
  · intro κ
    induction κ with
    | nil => simp
    | cons k t ih =>
      simp only [List.map_cons, List.sum_cons]
      have hnn : 0 ≤ (t.map fun (k : ℕ) => (k : ℤ)).sum := by
        clear ih
        induction t with
        | nil => simp
        | cons a t iht => simp only [List.map_cons, List.sum_cons]; omega
      omega
  · intro κ
    induction κ with
    | nil =>
      intro t ht
      refine ⟨[], rfl, fun x hx => absurd hx List.not_mem_nil, ?_⟩
      simp only [List.sum_nil] at ht; simp only [List.map_nil, List.sum_nil]; omega
    | cons k κ' ih =>
      intro t ht
      let h₀ : ℤ := if t > (k : ℤ) then (k : ℤ) else if t < -(k : ℤ) then -(k : ℤ) else t
      have hk : h₀.natAbs ≤ k := by
        simp only [h₀]; split
        · omega
        · split <;> omega
      have hr : (t - h₀).natAbs ≤ κ'.sum := by
        simp only [List.sum_cons] at ht
        simp only [h₀]; split
        · omega
        · split <;> omega
      obtain ⟨l, hl, hb, hs⟩ := ih (t - h₀) hr
      refine ⟨(h₀, k) :: l, by simp [hl], ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hk
        · exact hb x hx'
      · simp only [List.map_cons, List.sum_cons, hs]; omega

/-- 14:B12 — the lock of like units: the joint recurrence of `N + 1` cycles of period `12` is `12` for every `N`,
`lcm (12, …, 12) = 12`, so no element of the lock has order `12N` for `N ≥ 2`; the diagonal drive on `ZMod 12 × ZMod 12`
keeps the offset `x − y` (one superselected `C₁₂` offset per further unit), and `144 = 12 · 12`, `1728 = 144 · 12`
points fall into orbits of length `12`. -/
theorem lock_recurrence :
    (∀ N : ℕ, (List.replicate (N + 1) (12 : ℕ)).foldr Nat.lcm 1 = 12) ∧
    (∀ N : ℕ, 2 ≤ N → 12 * N ≠ 12) ∧
    (∀ x y : ZMod 12, (x + 1) - (y + 1) = x - y) ∧ (∀ x : ZMod 12, x + 12 = x) ∧
    144 = 12 * 12 ∧ 1728 = 144 * 12 := by
  refine ⟨fun N => ?_, fun N hN => by omega, fun x y => by ring, fun x => by
      have h12 : (12 : ZMod 12) = 0 := by decide
      rw [h12, add_zero], by norm_num, by norm_num⟩
  induction N with
  | zero => simp
  | succ n ih => simp only [List.replicate_succ, List.foldr_cons] at ih ⊢; rw [ih]; decide

/-- 14:B13 — the shell of capacity `3N` is `𝔽_{12N+1}`, `4 · 3N + 1 = 12N + 1`, and exists exactly when `12N + 1` is
prime: below `N = 10` for `N = 1, 3, 5, 6, 8, 9` and not at `N = 2` (`25 = 5²`), `4`, `7`. -/
theorem shells_of_capacity :
    (∀ N : ℕ, 4 * (3 * N) + 1 = 12 * N + 1) ∧
    (∀ N : ℕ, N < 10 → (Nat.Prime (12 * N + 1) ↔ N = 1 ∨ N = 3 ∨ N = 5 ∨ N = 6 ∨ N = 8 ∨ N = 9)) ∧
    25 = 5 ^ 2 := by
  refine ⟨fun N => by ring, fun N hN => ?_, by norm_num⟩
  interval_cases N <;> norm_num

/-- 14:B13 — fusion of coprime cycles is multiplicative: for coprime periods `n₁, n₂` the joint recurrence is
`lcm n₁ n₂ = n₁ n₂`, and the fused capacity `n₁ n₂ / 4`; hydrogen `(4, 3)`: `lcm = 12`, capacity `3`; like cycles do
not fuse, `lcm (12, 12) = 12 = gcd (12, 12)`, and the capacity-`3` shell `13` is not the lock's register `12`. -/
theorem fusion_capacity :
    (∀ n₁ n₂ : ℕ, Nat.Coprime n₁ n₂ → Nat.lcm n₁ n₂ = n₁ * n₂) ∧
    Nat.lcm 4 3 = 12 ∧ 4 * 3 / 4 = 3 ∧ Nat.lcm 12 12 = 12 ∧ Nat.gcd 12 12 = 12 ∧ (13 : ℕ) ≠ 12 :=
  ⟨fun _ _ h => h.lcm_eq_mul, by decide, by norm_num, by decide, by decide, by norm_num⟩

end window

/-! ## The channels, the imports and the predictions: the chart arithmetic each row consumes
(14:C1, X1, X5, X7, X8, P1, P2; 15 October 2026) -/
section channels

/-- 14:C1 [chart] — the two faces: with `c > 0` the conversion `r = c t` is a bijection between the temporal
and the spatial datum, `r = c t ↔ t = r/c`, and each face returns the other, `(c t)/c = t`, `c (r/c) = r`. That an
instrument reads exactly one of the two faces is C1's realisation clause (a frame supplies one datum of each kind),
not formal content. -/
theorem two_faces (c r t : ℝ) (hc : 0 < c) :
    (r = c * t ↔ t = r / c) ∧ c * t / c = t ∧ c * (r / c) = r := by
  have hc' := hc.ne'
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, mul_div_cancel_left₀ t hc', mul_div_cancel₀ r hc'⟩
  · rw [h, mul_div_cancel_left₀ t hc']
  · rw [h, mul_div_cancel₀ r hc']

/-- 14:X1 [chart] — the curvature face of the one cardinality: with `Λ = 3/r_H²` (the de Sitter radius) and
`S = π (r_H/ℓ_P)²` (the count face, B9), `Λ ℓ_P² = 3π/S` identically. The constant is the cardinality read on the
curvature face; that no mode sum enters is X1's realisation clause. -/
theorem lambda_face (Λ S r ℓ : ℝ) (hr : r ≠ 0) (hℓ : ℓ ≠ 0) (hΛ : Λ = 3 / r ^ 2)
    (hS : S = π * (r / ℓ) ^ 2) : Λ * ℓ ^ 2 = 3 * π / S := by
  subst hΛ hS
  have hpi := Real.pi_ne_zero
  field_simp

/-- 14:X5 [chart] — the over-closure exit of the typical-density diagonal: a body of density `ρ₀` (the paper's `c̃`) on the cubic
`M = ρ₀ R³` that sits on its own Schwarzschild radius `R = 2GM/c²` has `M² = c⁶/(8 G³ ρ₀)`, one positive mass —
the exit of C9 read as a bound. Its value `1.8 × 10⁸ M☉` at `ρ₀ = 0.97 × 10³ kg/m³` is the python witness's
(`tri.W`). -/
theorem wall_exit (M R G c ρ₀ : ℝ) (hc : 0 < c) (hG : 0 < G) (hM : 0 < M)
    (hρ : M = ρ₀ * R ^ 3) (hR : R = 2 * G * M / c ^ 2) :
    0 < ρ₀ ∧ M ^ 2 = c ^ 6 / (8 * G ^ 3 * ρ₀) := by
  subst hR
  have hc6 : (c ^ 6) ≠ 0 := by positivity
  have h1 : ρ₀ * (2 * G * M / c ^ 2) ^ 3 = 8 * ρ₀ * G ^ 3 * M ^ 3 / c ^ 6 := by
    field_simp; ring
  have h2 : M * c ^ 6 = 8 * ρ₀ * G ^ 3 * M ^ 3 := by
    have := hρ
    rw [h1, eq_div_iff hc6] at this
    exact this
  have hρpos : 0 < ρ₀ := by
    by_contra h
    have h8 : 8 * ρ₀ ≤ 0 := by linarith [not_lt.1 h]
    have : 8 * ρ₀ * G ^ 3 * M ^ 3 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg h8 (pow_pos hG 3).le) (pow_pos hM 3).le
    have : 0 < M * c ^ 6 := by positivity
    linarith
  refine ⟨hρpos, ?_⟩
  rw [eq_div_iff (by positivity)]
  have h3 : M * c ^ 6 = M * (M ^ 2 * (8 * G ^ 3 * ρ₀)) := by rw [h2]; ring
  exact (mul_left_cancel₀ hM.ne' h3).symm

/-- 14:X7, 14:X8 [ΛCDM] — the Hubble radius on the black-hole line: the density of a Schwarzschild mass
`M = r c²/2G` spread over its own ball is `ρ_BH(r) = 3c²/(8πG r²)`; at `r = c/H` it is the critical density
`ρ_c = 3H²/(8πG)` identically, and the equality `ρ_BH(r) = ρ_c` holds at `r = c/H` alone — the saturation
identity X7 and X8 share. That the Schwarzschild reading consumes an exterior, and what each interior completion
consumes, is the rows' realisation content. -/
theorem hubble_on_bh_line (c G H r : ℝ) (hc : 0 < c) (hG : 0 < G) (hH : 0 < H) (hr : 0 < r) :
    (r * c ^ 2 / (2 * G)) / (4 / 3 * π * r ^ 3) = 3 * c ^ 2 / (8 * π * G * r ^ 2) ∧
    ((c / H) * c ^ 2 / (2 * G)) / (4 / 3 * π * (c / H) ^ 3) = 3 * H ^ 2 / (8 * π * G) ∧
    (3 * c ^ 2 / (8 * π * G * r ^ 2) = 3 * H ^ 2 / (8 * π * G) ↔ r = c / H) := by
  have hpi := Real.pi_pos
  refine ⟨?_, ?_, ?_⟩
  · field_simp; try ring
  · field_simp; try ring
  · rw [div_eq_div_iff (by positivity) (by positivity)]
    constructor
    · intro h
      have h2 : c ^ 2 * (24 * π * G) = (H * r) ^ 2 * (24 * π * G) := by linear_combination h
      have h3 : c ^ 2 = (H * r) ^ 2 := mul_right_cancel₀ (by positivity) h2
      have h4 : c = H * r := (pow_left_inj₀ hc.le (by positivity) two_ne_zero).1 h3
      rw [h4, mul_div_cancel_left₀ r hH.ne']
    · intro h
      rw [h]; field_simp; try ring

/-- 14:P1 [ΛCDM] — the running floor: with `a₀(z) = A H(z)/2π` and `H(z) = H₀ E(z)`,
`E(z) = √(Ω_m (1+z)³ + Ω_Λ)`, the floor's ratio to today is the chart's `E(z)` (`E(0) = 1` on a flat chart), and at
`z = 1` on the fitted chart (`Ω_m = 0.315`) it lies in `(1.79, 1.80)`: the floor runs with the registered rate. The
confrontation with the four redshift bins is the python witness's (`est.P1`). -/
theorem running_floor (A H0 Ωm ΩΛ z : ℝ) (hA : A ≠ 0) (hH : H0 ≠ 0) (hsum : Ωm + ΩΛ = 1) :
    (A * (H0 * √(Ωm * (1 + z) ^ 3 + ΩΛ)) / (2 * π)) / (A * (H0 * √(Ωm * (1 + 0) ^ 3 + ΩΛ)) / (2 * π))
      = √(Ωm * (1 + z) ^ 3 + ΩΛ) ∧
    (1.79 : ℝ) < √(0.315 * (1 + 1) ^ 3 + 0.685) ∧ √(0.315 * (1 + 1) ^ 3 + 0.685) < 1.80 := by
  have hpi := Real.pi_ne_zero
  refine ⟨?_, ?_, ?_⟩
  · have h0 : Ωm * (1 + 0) ^ 3 + ΩΛ = 1 := by norm_num; linarith
    rw [h0, Real.sqrt_one]
    field_simp
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- 14:P2, 14:X8 [chart, ΛCDM] — the registered record depth: the octant's chart conversion `(S/2)/(4S) · 2π r_H/c =
(π/4) r_H/c` (C5) at every frame chronon; the rival chart's `t₀ H_Λ` at the fitted `Ω_Λ = 0.685` exceeds `π/4` by
`0.21–0.22 %` (the "degenerate to 0.2 % now", C3); and a `t₀` growing one Gyr per Gyr of chart time separates from
the fixed `13.79 Gyr` at `1/13.79` per Gyr, which lies in `(7 %, 7.5 %)`. The numeral `13.79 Gyr` and the
confrontation with the cluster ages are the python witness's (`est.P2`). -/
theorem record_depth :
    (∀ S r c : ℝ, S ≠ 0 → (S / 2) / (4 * S) * (2 * π * r / c) = (π / 4) * r / c) ∧
    (0.0021 * (π / 4) < lcdmAge 0.685 - π / 4 ∧ lcdmAge 0.685 - π / 4 < 0.0022 * (π / 4)) ∧
    ((0.07 : ℝ) < 1 / 13.79 ∧ (1 : ℝ) / 13.79 < 0.075) :=
  ⟨fun S r c hS => FRC.Chart.octant_chart S r c hS, age_bracket.2.2, by norm_num, by norm_num⟩

end channels

/-! ## Old names (ledger migration, task LM30): the theorems moved to the chart theme (`FRC.Chart`,
`FrcMathlib/Theme/Chart.lean`), each under its old name -/

/-- 14:C5 [chart] — the chart conversion of the octant: `(S/2)/(4S) · 2π r_H/c = (π/4) r_H/c`. -/
theorem octant_chart (S r c : ℝ) (hS : S ≠ 0) :
    (S / 2) / (4 * S) * (2 * π * r / c) = (π / 4) * r / c :=
  FRC.Chart.octant_chart S r c hS

/-- The octant's rate factor `tanh(3π/8)` is positive. -/
theorem tanh_octant_pos : 0 < tanh (3 * π / 8) :=
  FRC.Chart.tanh_octant_pos

/-- 14:P3 [ΛCDM] — the algebraic locus `t H₀ = (π/4)/tanh(3π/8)`. -/
theorem age_rate_locus (t H0 HΛ Ω : ℝ) (hoct : t * HΛ = π / 4) (hΛ : HΛ = H0 * √Ω)
    (hΩ : Ω = tanh (3 * π / 8) ^ 2) : t * H0 = (π / 4) / tanh (3 * π / 8) :=
  FRC.Chart.age_rate_locus t H0 HΛ Ω hoct hΛ hΩ

/-- `tanh x = (e^{2x} − 1)/(e^{2x} + 1)`. -/
theorem tanh_eq_exp_two_mul (x : ℝ) : tanh x = (exp (2 * x) - 1) / (exp (2 * x) + 1) :=
  FRC.Chart.tanh_eq_exp_two_mul x

/-- The Taylor brackets of `e^t` at the two ends of `t = 3π/4 − 2`. -/
theorem exp_tail_bounds :
    (1.427884 : ℝ) < exp 0.356194 ∧ exp (0.35619475 : ℝ) < 1.4278857 :=
  FRC.Chart.exp_tail_bounds

/-- `10.55071 < e^{3π/4} < 10.55073`. -/
theorem exp_three_pi_four_bounds : (10.55071 : ℝ) < exp (3 * π / 4) ∧ exp (3 * π / 4) < 10.55073 :=
  FRC.Chart.exp_three_pi_four_bounds

/-- `0.82685 < tanh(3π/8) < 0.826851`. -/
theorem tanh_octant_bounds : (0.82685 : ℝ) < tanh (3 * π / 8) ∧ tanh (3 * π / 8) < 0.826851 :=
  FRC.Chart.tanh_octant_bounds

/-- 14:P3 — `0.9498 < (π/4)/tanh(3π/8) < 0.9499`. -/
theorem locus_bracket : (0.9498 : ℝ) < (π / 4) / tanh (3 * π / 8) ∧ (π / 4) / tanh (3 * π / 8) < 0.9499 :=
  FRC.Chart.locus_bracket

/-- 14:C7, 14:X3 — `0.68368 < tanh²(3π/8) < 0.68369`, a deviation between `0.18σ` and `0.19σ` from `0.685 ± 0.007`. -/
theorem landing_bracket :
    (0.68368 : ℝ) < tanh (3 * π / 8) ^ 2 ∧ tanh (3 * π / 8) ^ 2 < 0.68369 ∧
    0.18 * 0.007 < 0.685 - tanh (3 * π / 8) ^ 2 ∧ 0.685 - tanh (3 * π / 8) ^ 2 < 0.19 * 0.007 :=
  FRC.Chart.landing_bracket

-- Ledger predicates of 14-entropy (generated by make_predicates.py from docs/14-entropy/14-entropy-ledger.json; edit the ledger, not this section)
/-- 14:A1 (p14001) — The de Sitter entropy $\dS$, the single quantitative import, fixing the cardinality exactly, $\Om=4\dS+1$. -/
theorem p14001 : ∀ {Ω S : ℕ}, Ω = (4 : ℕ) * S + (1 : ℕ) → S = (Ω - (1 : ℕ)) / (4 : ℕ) ∧ (4 : ℕ) ∣ Ω - (1 : ℕ) ∧ Ω % (4 : ℕ) = (1 : ℕ) ∧ (4 : ℕ) * S = Ω - (1 : ℕ) :=
  @FRC.Entropy.cardinality
/-- 14:A2 (p14002) — The Carrier congruences, relations certified by the realisations (the $c$-square $\dS$ even, the triality centre $\dS\equiv1\pmod3$, completeness $4\dS+1$ prime); instantiated on the laboratory Carrier as host-decided values. -/
theorem p14002 : ((4 : ℕ) * (602140 : ℕ) + (1 : ℕ) = (2408561 : ℕ) ∧ Even (602140 : ℕ) ∧ (602140 : ℕ) % (3 : ℕ) = (1 : ℕ) ∧ Nat.Prime (2408561 : ℕ)) ∧ (∀ (S : ℕ) [hp : Fact (Nat.Prime ((4 : ℕ) * S + (1 : ℕ)))], (IsSquare (2 : ZMod ((4 : ℕ) * S + (1 : ℕ))) ↔ Even S) ∧ (IsSquare (2 : ZMod ((4 : ℕ) * S + (1 : ℕ)))⁻¹ ↔ Even S)) ∧ ∀ (S : ℕ), S % (3 : ℕ) = (1 : ℕ) → ∀ [Fact (Nat.Prime ((4 : ℕ) * S + (1 : ℕ)))], (3 : ℕ) ∣ (4 : ℕ) * S + (1 : ℕ) + (1 : ℕ) ∧ ¬(3 : ℕ) ∣ (4 : ℕ) * S ∧ ∀ (x : (ZMod ((4 : ℕ) * S + (1 : ℕ)))ˣ), orderOf x ≠ (3 : ℕ) :=
  And.intro @FRC.Entropy.carrierLab (And.intro @FRC.Entropy.c_square (@FRC.Entropy.triality_centre))
/-- 14:B2 (p14010) — The angle--count dictionary: $2\pi$ the full cycle, $h=2\pi\hbar$; every angular numeral is the chart face of a count ($\pi/4\leftrightarrow\dS/2$ chronons). -/
theorem p14010 : ∀ (S : ℝ), Real.pi / ((2 : ℝ) * Real.pi) * ((4 : ℝ) * S) = (2 : ℝ) * S ∧ Real.pi / (2 : ℝ) / ((2 : ℝ) * Real.pi) * ((4 : ℝ) * S) = S ∧ Real.pi / (4 : ℝ) / ((2 : ℝ) * Real.pi) * ((4 : ℝ) * S) = S / (2 : ℝ) :=
  @FRC.Entropy.dictionary
/-- 14:B8 (p14016) — The effective-fluid correspondence behind P4: the rival chart's continuity law $\dot\rho_\Lambda+3H(\rho_\Lambda+p_\Lambda)=0$ \lcdm{} with $\dot\rho_\Lambda=0$ gives $w=-1$; and the single-component clause --- the framework's dark sector is derived with no second dark-energy component available, so an observed $w_{\mathrm{eff}}\neq-1$ cannot be reassigned to an extra evolving fluid. The clause makes P4's falsifier total rather than escapable. -/
theorem p14016 : ∀ (H ρ p ρ' : ℝ), H ≠ (0 : ℝ) → ρ ≠ (0 : ℝ) → ρ' = (0 : ℝ) → ρ' + (3 : ℝ) * H * (ρ + p) = (0 : ℝ) → p = -ρ ∧ p / ρ = (-1 : ℝ) :=
  @FRC.Entropy.fluid_w
/-- 14:B9 (p14017) — The area law: the projected horizon area in Planck cells is the full phase cycle, $A=4\dS$ \apx{} at the horizon ($4\pi n_A=4\dS$, $n_A=(r_H/\lP)^{2}$ \apx); the Bekenstein--Hawking quarter $\dS=A/4$ is the quarter-turn $Q_4$, the generative four of $\Om=4\dS+1$ and $\p=4\kap+1$; area is a Subject-projection property, the Carrier carrying none. -/
theorem p14017 : (∀ (S : ℕ) [hp : Fact (Nat.Prime ((4 : ℕ) * S + (1 : ℕ)))], IsSquare (-1 : ZMod ((4 : ℕ) * S + (1 : ℕ))) ∧ ∃ i, i ^ (2 : ℕ) = (-1 : ZMod ((4 : ℕ) * S + (1 : ℕ))) ∧ i ^ (4 : ℕ) = (1 : ZMod ((4 : ℕ) * S + (1 : ℕ))) ∧ i ≠ (1 : ZMod ((4 : ℕ) * S + (1 : ℕ))) ∧ i ≠ (-1 : ZMod ((4 : ℕ) * S + (1 : ℕ)))) ∧ ∀ (S : ℝ), (4 : ℝ) * Real.pi * (S / Real.pi) = (4 : ℝ) * S :=
  And.intro @FRC.Entropy.quarter_turn (@FRC.Entropy.area_law_chart)
/-- 14:B10 (p14044) — The capacity axis counts hydrogen units (one gram at $N_A$ to $0.003$ dex \apx): a definition, not a registered shell. The least register window resolving the total winding of $N$ units is $3N$, a theorem about the observing Subject (B11); a phase-locked composite of like units is an aggregate, never one shell (B12; a shell of capacity $3N$ exists only when $12N+1$ is prime, B13); the largest shell any Subject registers whole is the nesting bound $\mathsf{q}<\Om^{1/4}$ (00:B8), $N<(\Om^{1/4}-1)/12$ units, $8\times10^{2}$\,kg at $\dS=3.3\times10^{122}$ \apx{} ($\Om^{1/4}$ units overcounts by $12$); everything heavier an aggregate of locks; the proton's $1$ against $3$ compares a tower label with a chart count. -/
theorem p14044 : (Nat.Prime (13 : ℕ) ∧ ¬Nat.Prime (25 : ℕ) ∧ Nat.Prime (37 : ℕ) ∧ ∀ (q p Ω : ℕ), q ^ (2 : ℕ) < p → p ^ (2 : ℕ) < Ω → q ^ (4 : ℕ) < Ω) ∧ (37 : ℕ) ^ (4 : ℕ) < (2408561 : ℕ) ∧ (2408561 : ℕ) < (49 : ℕ) ^ (4 : ℕ) ∧ (∀ (N : ℕ), ((12 : ℕ) * N + (1 : ℕ)) ^ (4 : ℕ) < (2408561 : ℕ) → N ≤ (3 : ℕ)) ∧ Nat.Prime (1373 : ℕ) ∧ (1373 : ℕ) = (4 : ℕ) * (343 : ℕ) + (1 : ℕ) ∧ (37 : ℕ) ^ (2 : ℕ) < (1373 : ℕ) ∧ (1373 : ℕ) ^ (2 : ℕ) < (2408561 : ℕ) :=
  And.intro @FRC.Entropy.hydrogen_units (@FRC.Entropy.nesting_lab)
/-- 14:B11 (p14046) — The additive window: for $N$ modes at resolvable heights $|\hat h_i|\le\kap_i$ (38:A8) the total winding satisfies $|\sum_i\hat h_i|\le\sum_i\kap_i$, attained, every total in the range occurring; the least register window resolving the total exactly is the capacity sum $\sum_i\kap_i$, $3N$ for $N$ hydrogen units --- a capacity of the observing Subject, not a shell of the composite (B10). -/
theorem p14046 : And (∀ (l : List (Prod Int Nat)), (∀ (x : Prod Int Nat), @Membership.mem (Prod Int Nat) (List (Prod Int Nat)) (@List.instMembership (Prod Int Nat)) l x → @LE.le Nat instLENat (@Prod.fst Int Nat x).natAbs (@Prod.snd Int Nat x)) → @LE.le Nat instLENat (@List.sum Int Int.instAdd (@MulZeroClass.toZero Int (@instMulZeroClassOfSemiring Int Int.instSemiring)) (@List.map (Prod Int Nat) Int (@Prod.fst Int Nat) l)).natAbs (@List.sum Nat instAddNat (@MulZeroClass.toZero Nat Nat.instMulZeroClass) (@List.map (Prod Int Nat) Nat (@Prod.snd Int Nat) l))) (And (∀ (κ : List Nat), @Eq Nat (@List.sum Int Int.instAdd (@MulZeroClass.toZero Int (@instMulZeroClassOfSemiring Int Int.instSemiring)) (@List.map Nat Int (fun k => @Nat.cast Int instNatCastInt k) κ)).natAbs (@List.sum Nat instAddNat (@MulZeroClass.toZero Nat Nat.instMulZeroClass) κ)) (∀ (κ : List Nat) (t : Int), @LE.le Nat instLENat t.natAbs (@List.sum Nat instAddNat (@MulZeroClass.toZero Nat Nat.instMulZeroClass) κ) → ∃ l, And (@Eq (List Nat) (@List.map (Prod Int Nat) Nat (@Prod.snd Int Nat) l) κ) (And (∀ (x : Prod Int Nat), @Membership.mem (Prod Int Nat) (List (Prod Int Nat)) (@List.instMembership (Prod Int Nat)) l x → @LE.le Nat instLENat (@Prod.fst Int Nat x).natAbs (@Prod.snd Int Nat x)) (@Eq Int (@List.sum Int Int.instAdd (@MulZeroClass.toZero Int (@instMulZeroClassOfSemiring Int Int.instSemiring)) (@List.map (Prod Int Nat) Int (@Prod.fst Int Nat) l)) t)))) :=
  @FRC.Entropy.additive_window
/-- 14:B12 (p14047) — The lock of like units: $N$ like units never fuse (00:F6, $\gcd(12,12)=12$): their joint registration (00:F2) recurs on $C_{12}$ with period $12$ for every $N$, one superselected $C_{12}$ offset per further unit --- an aggregate, never one shell. Instances: the diagonal drive on $C_{12}^{2}$ has $12$ orbits of length $12$, on $C_{12}^{3}$ $144$. -/
theorem p14047 : (∀ (N : ℕ), List.foldr Nat.lcm (1 : ℕ) (List.replicate (N + (1 : ℕ)) (12 : ℕ)) = (12 : ℕ)) ∧ (∀ (N : ℕ), (2 : ℕ) ≤ N → (12 : ℕ) * N ≠ (12 : ℕ)) ∧ (∀ (x y : ZMod (12 : ℕ)), x + (1 : ZMod (12 : ℕ)) - (y + (1 : ZMod (12 : ℕ))) = x - y) ∧ (∀ (x : ZMod (12 : ℕ)), x + (12 : ZMod (12 : ℕ)) = x) ∧ (144 : ℕ) = (12 : ℕ) * (12 : ℕ) ∧ (1728 : ℕ) = (144 : ℕ) * (12 : ℕ) :=
  @FRC.Entropy.lock_recurrence
/-- 14:B13 (p14048) — Shells of capacity $3N$ and fusion: the shell of capacity $3N$ is $\F_{12N+1}$ and exists iff $12N+1$ is prime ($N=1,3,5,6,8,9$ below $10$; none at $N=2$, $25=5^{2}$), never the lock's register (B12); fusion of coprime cycles is multiplicative, $\kap=n_{1}n_{2}/4$: hydrogen $(4,3)\to3$, one orbit of length $12$ (00:F6). -/
theorem p14048 : ((∀ (N : ℕ), (4 : ℕ) * ((3 : ℕ) * N) + (1 : ℕ) = (12 : ℕ) * N + (1 : ℕ)) ∧ (∀ N < (10 : ℕ), Nat.Prime ((12 : ℕ) * N + (1 : ℕ)) ↔ N = (1 : ℕ) ∨ N = (3 : ℕ) ∨ N = (5 : ℕ) ∨ N = (6 : ℕ) ∨ N = (8 : ℕ) ∨ N = (9 : ℕ)) ∧ (25 : ℕ) = (5 : ℕ) ^ (2 : ℕ)) ∧ (∀ (n₁ n₂ : ℕ), n₁.Coprime n₂ → n₁.lcm n₂ = n₁ * n₂) ∧ Nat.lcm (4 : ℕ) (3 : ℕ) = (12 : ℕ) ∧ (4 : ℕ) * (3 : ℕ) / (4 : ℕ) = (3 : ℕ) ∧ Nat.lcm (12 : ℕ) (12 : ℕ) = (12 : ℕ) ∧ Nat.gcd (12 : ℕ) (12 : ℕ) = (12 : ℕ) ∧ (13 : ℕ) ≠ (12 : ℕ) :=
  And.intro @FRC.Entropy.shells_of_capacity (@FRC.Entropy.fusion_capacity)
/-- 14:C1 (p14018) — Two faces: a frame supplies one spatial and one temporal datum, so every instrument reading the size of the totality is one of exactly two faces, converted by $c$. -/
theorem p14018 : ∀ (c r t : ℝ), (0 : ℝ) < c → (r = c * t ↔ t = r / c) ∧ c * t / c = t ∧ c * (r / c) = r :=
  @FRC.Entropy.two_faces
/-- 14:C2 (p14019) — The non-channels: the constants correspondence carries no dimensional readout, the horizon-quarter closure is an internal consistency loop, the registered entropy budget is a floor eighteen orders below $\dS$ \apx. -/
theorem p14019 : ∀ (Ω S : ℕ) (p : ℝ), Ω = (4 : ℕ) * S + (1 : ℕ) → p ^ (2 : ℕ) = ↑Ω → (p ^ (2 : ℕ) - (1 : ℝ)) / (4 : ℝ) = ↑S :=
  @FRC.Entropy.horizon_quarter_closure
/-- 14:C3 (p14020) — The same-channel demotion: $t_0H_\Lambda=\tfrac23\artanh\sqrt{\Omega_\Lambda}$ \lcdm{} depends on the one fitted parameter, so the $0.2\%$ landing on $\pi/4$ restates the fit (by B5). Cited definitions (not proofs): FRC.Entropy.lcdmAge. -/
theorem p14020 : (∀ (Ωm ΩΛ H0 t : ℝ), (0 : ℝ) < Ωm → (0 : ℝ) < ΩΛ → Ωm + ΩΛ = (1 : ℝ) → (0 : ℝ) < H0 → (0 : ℝ) < t → (FRC.Entropy.lcdmScale Ωm ΩΛ (H0 * √ΩΛ) t = (1 : ℝ) ↔ t * (H0 * √ΩΛ) = FRC.Entropy.lcdmAge ΩΛ)) ∧ 0.7870 < FRC.Entropy.lcdmAge 0.685 ∧ FRC.Entropy.lcdmAge 0.685 < 0.7871 ∧ 21e-4 * (Real.pi / (4 : ℝ)) < FRC.Entropy.lcdmAge 0.685 - Real.pi / (4 : ℝ) ∧ FRC.Entropy.lcdmAge 0.685 - Real.pi / (4 : ℝ) < 22e-4 * (Real.pi / (4 : ℝ)) :=
  And.intro @FRC.Entropy.lcdm_age (@FRC.Entropy.age_bracket)
/-- 14:C5 (p14022) — The octant lemma: the measured age is $\dS/2$ chronons, $(\pi/4)\,r_H/c$ in the chart \apx; the halving and the sector are exact through the enumerated realisation set $B_{\mathrm{oct}}=\{$A4, A5, B2, B3, B6, B7$\}$, the same class as the constants correspondence. -/
theorem p14022 : (∀ (S r c : ℝ), S ≠ (0 : ℝ) → S / (2 : ℝ) / ((4 : ℝ) * S) * ((2 : ℝ) * Real.pi * r / c) = Real.pi / (4 : ℝ) * r / c) ∧ ∀ (S : ℕ), (∀ (x : ℕ), (2 : ℕ) * x ≤ S ↔ x ≤ S / (2 : ℕ)) ∧ (Even S → (2 : ℕ) * (S / (2 : ℕ)) = S) :=
  And.intro @FRC.Entropy.octant_chart (@FRC.Entropy.closure_budget)
set_option linter.defProp false in
/-- 14:C6 (p14023) — The octant sector: $C_{8}\subset C_{4\dS}$ exists exactly when $\dS$ is even, its character $\zeta_8$ the residue the Tsirelson identity carries; the octant count $\dS/2$ is an integer on every admissible Carrier. -/
def p14023 := And.intro @FRC.Entropy.octant_exists_iff (@FRC.Entropy.octant_character)
/-- 14:C7 (p14024) — The dark-energy output: $\Omega_\Lambda=\tanh^{2}(3\pi/8)=0.6837$ \lcdm{} against the fitted $0.685\pm0.007$, a $0.19\sigma$ landing --- a zero-freedom derivation, not an independent measurement (two-register separation, \S\ref{sec:audit}). -/
theorem p14024 : (FRC.Entropy.lcdmAge (Real.tanh ((3 : ℝ) * Real.pi / (8 : ℝ)) ^ (2 : ℕ)) = Real.pi / (4 : ℝ) ∧ ∀ (Ω : ℝ), (0 : ℝ) ≤ Ω → Ω < (1 : ℝ) → FRC.Entropy.lcdmAge Ω = Real.pi / (4 : ℝ) → Ω = Real.tanh ((3 : ℝ) * Real.pi / (8 : ℝ)) ^ (2 : ℕ)) ∧ 0.68368 < Real.tanh ((3 : ℝ) * Real.pi / (8 : ℝ)) ^ (2 : ℕ) ∧ Real.tanh ((3 : ℝ) * Real.pi / (8 : ℝ)) ^ (2 : ℕ) < 0.68369 ∧ 0.18 * 7e-3 < 0.685 - Real.tanh ((3 : ℝ) * Real.pi / (8 : ℝ)) ^ (2 : ℕ) ∧ 0.685 - Real.tanh ((3 : ℝ) * Real.pi / (8 : ℝ)) ^ (2 : ℕ) < 0.19 * 7e-3 :=
  And.intro @FRC.Entropy.octant_inversion (@FRC.Entropy.landing_bracket)
/-- 14:C8 (p14025) — The entailed-rate consistency: with the channel-1 $\Lambda$ the age--rate locus returns the channel-1 $H_0$ (to $0.1\%$), same-channel by the definition $\Lambda=3\Omega_\Lambda H_0^{2}/c^{2}$, a corollary of C7 and not a prediction --- the floor value itself consumed as import (A6) under the role realisation (B4), not derived here; the two-cluster ratio is the chart identity $(H_{\mathrm{rate}}/H_0)^2/\Omega_\Lambda$, displayed, not claimed. -/
theorem p14025 : (∀ (H0 c Ω Λ : ℝ), (0 : ℝ) < H0 → (0 : ℝ) < c → (0 : ℝ) ≤ Ω → Λ = (3 : ℝ) * Ω * H0 ^ (2 : ℕ) / c ^ (2 : ℕ) → c * √(Λ / (3 : ℝ)) = H0 * √Ω ∧ (H0 * √Ω / Real.tanh ((3 : ℝ) * Real.pi / (8 : ℝ)) = H0 ↔ Ω = Real.tanh ((3 : ℝ) * Real.pi / (8 : ℝ)) ^ (2 : ℕ))) ∧ ((1 : ℝ) < √0.685 / Real.tanh ((3 : ℝ) * Real.pi / (8 : ℝ)) ∧ √0.685 / Real.tanh ((3 : ℝ) * Real.pi / (8 : ℝ)) < 1.001) ∧ ∀ (c H0 Hr Ω ℓ : ℝ), c ≠ (0 : ℝ) → (0 : ℝ) < Ω → ℓ ≠ (0 : ℝ) → Real.pi * (c / (H0 * √Ω) / ℓ) ^ (2 : ℕ) / (Real.pi * (c / Hr / ℓ) ^ (2 : ℕ)) = (Hr / H0) ^ (2 : ℕ) / Ω :=
  And.intro @FRC.Entropy.channel_one_consistency (And.intro @FRC.Entropy.channel_one_numeral (@FRC.Entropy.cluster_identity))
/-- 14:C9 (p14026) — The registrable triangle \apx: width $\log_{10}(r_H/\lP)=61.0$ dex --- the count face $\sqrt{\dS}$ in its chart dress $\sqrt{\dS/\pi}$, the solid angle the declared transport; the thirteen-object diagonal, slope $3.03$ (intercept $1.00\times10^{3}$ at the metre pivot); the constrained $k=3$ cubic coefficient $\tilde c=m/R^{3}=0.97\times10^{3}\,\mathrm{kg\,m^{-3}}$ (not a density: a sphere's is $0.62$ dex lower); the Compton entry returns its input, the Schwarzschild exit is the chart's one derived quantity, the over-closure bound $1.8\times10^{8}M_\odot$ within the $(1.4\text{--}2.8)\times10^{8}$ sensitivity band --- a bound, no observed scale predicted (X5); classified a consistency chart, not a channel. -/
theorem p14026 : ∀ (S x : ℝ), (0 : ℝ) < x → S = Real.pi * x ^ (2 : ℕ) → x = √(S / Real.pi) ∧ √S = √Real.pi * x :=
  @FRC.Entropy.count_face
/-- 14:C10 (p14027) — The capacity axis \apx: holographic ring capacity $\log_{10}\kap_{q}$, zero at hydrogen ($\kap_H=3$; $\kap_{q}=2$ has no shell), one dex per chart dex, terminating at the count face $\sqrt{\dS}$ --- the triangle's own sixty dex; the one-gram horizontal lands on $N_A$ to $0.0035$ dex (the $1.008$\,u offset), asserted before drawing. -/
theorem p14027 : Nat.Prime ((4 : ℕ) * (1 : ℕ) + (1 : ℕ)) ∧ ¬Nat.Prime ((4 : ℕ) * (2 : ℕ) + (1 : ℕ)) ∧ Nat.Prime ((4 : ℕ) * (3 : ℕ) + (1 : ℕ)) :=
  @FRC.Entropy.capacity_zero
/-- 14:X1 (p14028) — \textbf{The cosmological-constant problem} dissolves: $\Lambda$ is the curvature face of the one cardinality, not a vacuum energy, so there is no mode sum to cancel and the $10^{120}$-order discrepancy does not arise. -/
theorem p14028 : ∀ (Λ S r ℓ : ℝ), r ≠ (0 : ℝ) → ℓ ≠ (0 : ℝ) → Λ = (3 : ℝ) / r ^ (2 : ℕ) → S = Real.pi * (r / ℓ) ^ (2 : ℕ) → Λ * ℓ ^ (2 : ℕ) = (3 : ℝ) * Real.pi / S :=
  @FRC.Entropy.lambda_face
/-- 14:X2 (p14029) — \textbf{Milgrom's coincidence} $a_0\approx cH_0/2\pi$, on record since 1983, becomes a value with zero freedom: the $2\pi$ is the fixed cycle convention, the reverse rebooking of $h=2\pi\hbar$, and the $H$ is the observer's registered rate. -/
theorem p14029 : ∀ (c H ħ h : ℝ), h = (2 : ℝ) * Real.pi * ħ → ħ ≠ (0 : ℝ) → c * H / ((2 : ℝ) * Real.pi) = c * H * ħ / h :=
  @FRC.Entropy.milgrom_rebooking
/-- 14:X3 (p14030) — \textbf{The age coincidence} $t_0H_\Lambda\approx\pi/4$ becomes the octant: $\Omega_\Lambda=\tanh^{2}(3\pi/8)=0.6837$ \lcdm{} is an output of the realisation set, landing at $0.19\sigma$ on the fitted $0.685\pm0.007$ --- never an independent measurement of $\dS$ (same-channel, X6), a zero-freedom derivation in full standing; the $(\Lambda,H_0)$ entailment at the channel-1 $\Lambda$ is this same landing read on $H_0$, not a further prediction. -/
theorem p14030 : (FRC.Entropy.lcdmAge (Real.tanh ((3 : ℝ) * Real.pi / (8 : ℝ)) ^ (2 : ℕ)) = Real.pi / (4 : ℝ) ∧ ∀ (Ω : ℝ), (0 : ℝ) ≤ Ω → Ω < (1 : ℝ) → FRC.Entropy.lcdmAge Ω = Real.pi / (4 : ℝ) → Ω = Real.tanh ((3 : ℝ) * Real.pi / (8 : ℝ)) ^ (2 : ℕ)) ∧ 0.68368 < Real.tanh ((3 : ℝ) * Real.pi / (8 : ℝ)) ^ (2 : ℕ) ∧ Real.tanh ((3 : ℝ) * Real.pi / (8 : ℝ)) ^ (2 : ℕ) < 0.68369 ∧ 0.18 * 7e-3 < 0.685 - Real.tanh ((3 : ℝ) * Real.pi / (8 : ℝ)) ^ (2 : ℕ) ∧ 0.685 - Real.tanh ((3 : ℝ) * Real.pi / (8 : ℝ)) ^ (2 : ℕ) < 0.19 * 7e-3 :=
  And.intro @FRC.Entropy.octant_inversion (@FRC.Entropy.landing_bracket)
set_option linter.defProp false in
/-- 14:X4 (p14031) — \textbf{The congruence $\dS$ even} acquires a second physical face: it is the existence of the octant sector, hence the well-definedness of the measured age --- a structure of the Carrier's cycle lattice, certified by realisation and read as an observational condition, never an arithmetic property of the numeral. -/
def p14031 := And.intro @FRC.Entropy.octant_second_face (@FRC.Entropy.octant_sector_iff)
/-- 14:X5 (p14032) — \textbf{The termination of the single-object sequence} is a consistency of the wall structure, the exit of C9 read as a bound: the typical-density diagonal over-closes at $1.8\times10^{8}M_\odot$ \apx{} (sensitivity band $(1.4\text{--}2.8)\times10^{8}$ across fit variants), so every heavier single object continuing the condensed-density sequence is necessarily wall-bound; the supermassive holes are that continuation, not an anomaly beyond it. Classified with the triangle: consistency, not derivation of an observed scale. -/
theorem p14032 : ∀ (M R G c ρ₀ : ℝ), (0 : ℝ) < c → (0 : ℝ) < G → (0 : ℝ) < M → M = ρ₀ * R ^ (3 : ℕ) → R = (2 : ℝ) * G * M / c ^ (2 : ℕ) → (0 : ℝ) < ρ₀ ∧ M ^ (2 : ℕ) = c ^ (6 : ℕ) / ((8 : ℝ) * G ^ (3 : ℕ) * ρ₀) :=
  @FRC.Entropy.wall_exit
/-- 14:X6 (p14033) — \textbf{The celebrated sub-percent age agreement} is judged: same-channel by the circularity criterion, a restatement of the fitted dark-energy fraction --- consistency, not evidence --- and the criterion locates exactly which confrontations do carry weight. -/
theorem p14033 : (∀ (Ωm ΩΛ H0 t : ℝ), (0 : ℝ) < Ωm → (0 : ℝ) < ΩΛ → Ωm + ΩΛ = (1 : ℝ) → (0 : ℝ) < H0 → (0 : ℝ) < t → (FRC.Entropy.lcdmScale Ωm ΩΛ (H0 * √ΩΛ) t = (1 : ℝ) ↔ t * (H0 * √ΩΛ) = FRC.Entropy.lcdmAge ΩΛ)) ∧ FRC.Entropy.lcdmAge (Real.tanh ((3 : ℝ) * Real.pi / (8 : ℝ)) ^ (2 : ℕ)) = Real.pi / (4 : ℝ) ∧ ∀ (Ω : ℝ), (0 : ℝ) ≤ Ω → Ω < (1 : ℝ) → FRC.Entropy.lcdmAge Ω = Real.pi / (4 : ℝ) → Ω = Real.tanh ((3 : ℝ) * Real.pi / (8 : ℝ)) ^ (2 : ℕ) :=
  And.intro @FRC.Entropy.lcdm_age (@FRC.Entropy.octant_inversion)
/-- 14:X7 (p14034) — \textbf{The universe-as-black-hole puzzle dissolves}: the Hubble radius sits on the black-hole line identically ($\rho_{\mathrm{BH}}(r_H)=\rho_c$ \lcdm), but the Schwarzschild reading consumes an exterior, and the containment argument (A3) makes an exterior incoherent --- the totality on its own horizon is the chart's closing point, not a hole in a background. -/
theorem p14034 : ∀ (c G H r : ℝ), (0 : ℝ) < c → (0 : ℝ) < G → (0 : ℝ) < H → (0 : ℝ) < r → r * c ^ (2 : ℕ) / ((2 : ℝ) * G) / ((4 / 3 : ℝ) * Real.pi * r ^ (3 : ℕ)) = (3 : ℝ) * c ^ (2 : ℕ) / ((8 : ℝ) * Real.pi * G * r ^ (2 : ℕ)) ∧ c / H * c ^ (2 : ℕ) / ((2 : ℝ) * G) / ((4 / 3 : ℝ) * Real.pi * (c / H) ^ (3 : ℕ)) = (3 : ℝ) * H ^ (2 : ℕ) / ((8 : ℝ) * Real.pi * G) ∧ ((3 : ℝ) * c ^ (2 : ℕ) / ((8 : ℝ) * Real.pi * G * r ^ (2 : ℕ)) = (3 : ℝ) * H ^ (2 : ℕ) / ((8 : ℝ) * Real.pi * G) ↔ r = c / H) :=
  @FRC.Entropy.hubble_on_bh_line
/-- 14:X8 (p14035) — \textbf{The interior completions weighed}: black-hole cosmology keeps the same saturation identity by consuming a parent exterior and a singularity-replacing mechanism (torsion; exclusion pressure); the finite reading consumes neither: the containment argument (A3) closes the chart at $\Om$, and no singularity is available over a finite totality. The registered record-depth bound separates the completions empirically (P2). -/
theorem p14035 : (∀ (c G H r : ℝ), (0 : ℝ) < c → (0 : ℝ) < G → (0 : ℝ) < H → (0 : ℝ) < r → r * c ^ (2 : ℕ) / ((2 : ℝ) * G) / ((4 / 3 : ℝ) * Real.pi * r ^ (3 : ℕ)) = (3 : ℝ) * c ^ (2 : ℕ) / ((8 : ℝ) * Real.pi * G * r ^ (2 : ℕ)) ∧ c / H * c ^ (2 : ℕ) / ((2 : ℝ) * G) / ((4 / 3 : ℝ) * Real.pi * (c / H) ^ (3 : ℕ)) = (3 : ℝ) * H ^ (2 : ℕ) / ((8 : ℝ) * Real.pi * G) ∧ ((3 : ℝ) * c ^ (2 : ℕ) / ((8 : ℝ) * Real.pi * G * r ^ (2 : ℕ)) = (3 : ℝ) * H ^ (2 : ℕ) / ((8 : ℝ) * Real.pi * G) ↔ r = c / H)) ∧ (∀ (S r c : ℝ), S ≠ (0 : ℝ) → S / (2 : ℝ) / ((4 : ℝ) * S) * ((2 : ℝ) * Real.pi * r / c) = Real.pi / (4 : ℝ) * r / c) ∧ (21e-4 * (Real.pi / (4 : ℝ)) < FRC.Entropy.lcdmAge 0.685 - Real.pi / (4 : ℝ) ∧ FRC.Entropy.lcdmAge 0.685 - Real.pi / (4 : ℝ) < 22e-4 * (Real.pi / (4 : ℝ))) ∧ 7e-2 < (1 : ℝ) / 13.79 ∧ (1 : ℝ) / 13.79 < 75e-3 :=
  And.intro @FRC.Entropy.hubble_on_bh_line (@FRC.Entropy.record_depth)
/-- 14:P1 (p14036) — \textbf{(Lead.)} The floor runs with the registered rate, $a_0(z)\propto H(z)$, the role statement of the floor closure, against both a constant fundamental $a_0$ and feedback-emergent scaling. Status: the constant-floor branch is excluded --- four redshift bins rising from $1.99$ to $2.71\times10^{-10}\,\mathrm{m/s^2}$ over $z=0.50$--$1.28$ \citep{ciocan2026}, $\Delta\chi^2=23$ against $A\,H(z)/H_0$ \lcdm{} --- and the running form fits the bins at free amplitude ($A=1.39\pm0.03$, $\chi^2=5.4/3$); the binned rate sits on the $\propto H(z)$ chord while the authors' global linear fit runs above it, so the shape waits on the likelihood refit of the resolved tracks, and the amplitude's $0.12$\,dex excess over $cH_0/2\pi$ lies inside the $0.2$\,dex gas systematic. Falsifier: a likelihood refit or a wider-redshift sample excluding the $\propto H(z)$ form after the baryonic-mass and pressure-support systematics close. -/
theorem p14036 : ∀ (A H0 Ωm ΩΛ z : ℝ), A ≠ (0 : ℝ) → H0 ≠ (0 : ℝ) → Ωm + ΩΛ = (1 : ℝ) → A * (H0 * √(Ωm * ((1 : ℝ) + z) ^ (3 : ℕ) + ΩΛ)) / ((2 : ℝ) * Real.pi) / (A * (H0 * √(Ωm * ((1 : ℝ) + (0 : ℝ)) ^ (3 : ℕ) + ΩΛ)) / ((2 : ℝ) * Real.pi)) = √(Ωm * ((1 : ℝ) + z) ^ (3 : ℕ) + ΩΛ) ∧ 1.79 < √(0.315 * ((1 : ℝ) + (1 : ℝ)) ^ (3 : ℕ) + 0.685) ∧ √(0.315 * ((1 : ℝ) + (1 : ℝ)) ^ (3 : ℕ) + 0.685) < 1.80 :=
  @FRC.Entropy.running_floor
/-- 14:P2 (p14037) — The registered record depth is bounded by $(\pi/4)\,r_H/c=13.79$ Gyr \apx{} (channel-1 anchor) at every observational frame chronon, against a $\Lambda$CDM $t_0$ that grows with chart time: degenerate to $0.2\%$ now, separating at ${\sim}7\%$ per Gyr; the octant carries zero parameter freedom at fixed $\Lambda$. Status \citep{valcin2026}: the oldest cluster population $0.5\sigma$ below the bound, the inferred age straddling it within $0.1\sigma$ (\S\ref{sec:open}). Falsifier: one well-dated object older than the octant value, in any frame --- fit-independent, fatal; the same bound excludes interior-bounce black-hole cosmology (X8). -/
theorem p14037 : (∀ (S r c : ℝ), S ≠ (0 : ℝ) → S / (2 : ℝ) / ((4 : ℝ) * S) * ((2 : ℝ) * Real.pi * r / c) = Real.pi / (4 : ℝ) * r / c) ∧ (21e-4 * (Real.pi / (4 : ℝ)) < FRC.Entropy.lcdmAge 0.685 - Real.pi / (4 : ℝ) ∧ FRC.Entropy.lcdmAge 0.685 - Real.pi / (4 : ℝ) < 22e-4 * (Real.pi / (4 : ℝ))) ∧ 7e-2 < (1 : ℝ) / 13.79 ∧ (1 : ℝ) / 13.79 < 75e-3 :=
  @FRC.Entropy.record_depth
/-- 14:P3 (p14038) — The age--rate locus $t_{\mathrm{age}}H_0=(\pi/4)/\tanh(3\pi/8)=0.950$, exact for the realisation set. Read on the fit-independent stellar age ($13.61\pm0.34$ Gyr): $H_0=68.2\pm1.7$ km/s/Mpc \apx, $0.5\sigma$ from Planck, $0.65\sigma$ from TRGB, $2.4\sigma$ from the Cepheid ladder --- the framework favours the CMB/TRGB value at that significance, and forbids the $\Omega_\Lambda\approx0.76$ by which the rival chart would accommodate the ladder value at the same age. Read on the channel-1 $\Lambda$ it returns the channel-1 $H_0$ (to $0.1\%$): a consistency, not a prediction (C8). Falsifier: a confirmed ladder $H_0$ with the stellar age standing ($t_\star H_0\ge1.0$ against $0.950$). -/
theorem p14038 : (∀ (t H0 HΛ Ω : ℝ), t * HΛ = Real.pi / (4 : ℝ) → HΛ = H0 * √Ω → Ω = Real.tanh ((3 : ℝ) * Real.pi / (8 : ℝ)) ^ (2 : ℕ) → t * H0 = Real.pi / (4 : ℝ) / Real.tanh ((3 : ℝ) * Real.pi / (8 : ℝ))) ∧ 0.9498 < Real.pi / (4 : ℝ) / Real.tanh ((3 : ℝ) * Real.pi / (8 : ℝ)) ∧ Real.pi / (4 : ℝ) / Real.tanh ((3 : ℝ) * Real.pi / (8 : ℝ)) < 0.9499 :=
  @FRC.LedgerML.p14038
/-- 14:P4 (p14039) — \textbf{(Lead.)} The dark-energy equation of state is rigid: $\Lambda$ is the curvature face of the fixed cardinality, constant, its effective-fluid reading $w=-1$ exactly with no $w_0w_a$ freedom; the fluid statement consumes the conservation-law correspondence and the single-component clause (B8). Status: DESI-era combined fits prefer evolving dark energy at $3$--$4.2\sigma$ \citep{desi2025}, contested by reanalyses (\S\ref{sec:import}). Falsifier: confirmed evolution of $w$, which kills $\Lambda\sim1/\Om$ outright and exposes P2 through $\Lambda$. -/
theorem p14039 : ∀ (H ρ p ρ' : ℝ), H ≠ (0 : ℝ) → ρ ≠ (0 : ℝ) → ρ' = (0 : ℝ) → ρ' + (3 : ℝ) * H * (ρ + p) = (0 : ℝ) → p = -ρ ∧ p / ρ = (-1 : ℝ) :=
  @FRC.Entropy.fluid_w
-- end ledger predicates

end FRC.Entropy
