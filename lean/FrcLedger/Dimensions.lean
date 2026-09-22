import Mathlib
import FrcLedger.Fourier

/-!
# 10-dimensions — the shell-domain calculus with the unit flag: the ledger rows in Lean (2026-09-18)

Rows of the predicate ledger of *Dimensional Analysis over Finite Holographic Substrate* (tree
`10-dimensions-20260720`). The domain lattice `D_p = C_p × C_{p−1}`, `p = 4κ + 1`, with the labels `U_{r,s}`
as the basis of the monoid algebra `A_p = ⊕ F_p U_{r,s}`: the label group, the grading, fibrewise addition
and the neutral-domain criterion (C2, C3); the chart duality `δ_S` and the crossed duality `δ_C` (D1); the
internal flag — the elements of order four are `(0, ±κ)`, the one element of order two is `(0, 2κ)`, no flag
of space, the unique subgroup of order four, meridian transport `(L T^κ)^p = I_q` (D2, C6); the lift — the
record map `Z_4 → ⟨I_q⟩`, its kernel, the quotient by the half-period, the operator four-cycle from
6-fourier, the Carrier face `ħ² = −1 ⇒ ħ⁴ = 1 ≠ ħ²` (D3); the flagged readings and the horizon
inaccessibility of the flag (D6); window covariance — the dilation character, the invariants `{0, 2κ}` of the
pushforward, the quarter-turn fix/swap law, the `σ`-twisted lift (C5); the unit face of the quartet — the
action identity, the rank-three parametrisation, the pairing closure, the cancellation identity, the
normalisation and the positive root (E2, E3); the defining congruences at pair level — the linear pin, the
root pairs, the linkage, the pair consequences, representative inertness, the `h`-form, the existence of the
residues on every admissible Carrier, and the two Carriers `233` and `2 408 561` decided (E4, E5); the
lifted labels `(r, s; j)` and the mechanical, gravitational and thermal domains (F2–F4); local recovery, the
crossing embedding and its windowed faithfulness (G1); the window ladder (G2); the `κ = 3` examples and the
energy–momentum relation on the lift (G3); the window coincidence and Buckingham's count on the pendulum (G4).
Classical (tier 2) on Mathlib's hierarchy; the finite content — the lattice as pairs of residues, the flag,
the transport, the Carrier values and the minimality scan — is proved with no axioms in
`FrcCore/Dimensions.lean`.
-/

namespace FRC.Dimensions

open AddMonoidAlgebra

/-! ## The domain lattice and the quantity algebra (10:C1–C3) -/
section lattice

variable (κ : ℕ)

instance instNeZeroFour [NeZero κ] : NeZero (4 * κ) := ⟨by have := NeZero.ne κ; omega⟩

/-- 10:C1 — the domain lattice `D_p = C_p × C_{p−1}`, `p = 4κ + 1`: the space exponent mod `p`, the time
exponent mod `p − 1 = 4κ`. -/
abbrev Dom := ZMod (4 * κ + 1) × ZMod (4 * κ)

/-- 10:C1 — the space generator `[L] = U_{1,0}`, anchored on the unit. -/
def L : Dom κ := (1, 0)

/-- 10:C1 — the time generator `[T] = U_{0,1}`, anchored on the chronon step. -/
def T : Dom κ := (0, 1)

/-- 10:D2 — the unit flag `I_q = [T]^κ`, the label `(0, κ)`. -/
def flag : Dom κ := (0, (κ : ZMod (4 * κ)))

/-- 10:C1 — the homogeneous quantity algebra `A_p = ⊕_{(r,s)} F_p U_{r,s}`: the monoid algebra of the
lattice over the shell. -/
abbrev QA := AddMonoidAlgebra (ZMod (4 * κ + 1)) (Dom κ)

/-- 10:C1 — the modular unit-domain label `U_{r,s} = [L]^r [T]^s`, the basis element of the fibre `(r, s)`. -/
noncomputable def U (a : Dom κ) : QA κ := single a 1

/-- 10:C2 — the product of labels: `U_{r,s} U_{r',s'} = U_{r+r', s+s'}`. -/
theorem U_mul (a b : Dom κ) : U κ a * U κ b = U κ (a + b) := by
  unfold U; rw [single_mul_single, one_mul]

/-- 10:C2 — the neutral label is the unit: `U_{0,0} = 1`. -/
theorem U_zero : U κ 0 = 1 := one_def.symm

/-- 10:C2 — the inverse of `U_{r,s}` is `U_{−r,−s}`. -/
theorem U_add_neg (a : Dom κ) : U κ a * U κ (-a) = 1 := by rw [U_mul, add_neg_cancel, U_zero]

theorem U_neg_add (a : Dom κ) : U κ (-a) * U κ a = 1 := by rw [U_mul, neg_add_cancel, U_zero]

/-- 10:C2 — distinct labels are distinct elements of `A_p` (`κ ≥ 1`). -/
theorem U_injective [NeZero κ] : Function.Injective (U κ) := by
  have : Fact (1 < 4 * κ + 1) := ⟨by have := NeZero.pos κ; omega⟩
  exact single_left_injective one_ne_zero

/-- The label as a unit of `A_p`. -/
noncomputable def Uunit (a : Dom κ) : (QA κ)ˣ := ⟨U κ a, U κ (-a), U_add_neg κ a, U_neg_add κ a⟩

/-- 10:C2 — the modular unit-domain group: `(r, s) ↦ U_{r,s}` is a homomorphism from `D_p` (written
multiplicatively) to the units of `A_p`; with `U_injective` the label group is `D_p`. -/
noncomputable def Uhom : Multiplicative (Dom κ) →* (QA κ)ˣ where
  toFun a := Uunit κ a.toAdd
  map_one' := Units.ext (U_zero κ)
  map_mul' := fun a b => Units.ext (by
    show U κ (a * b).toAdd = U κ a.toAdd * U κ b.toAdd
    rw [U_mul, toAdd_mul])

theorem Uhom_apply (a : Dom κ) : (Uhom κ (Multiplicative.ofAdd a) : QA κ) = U κ a := rfl

/-- 10:C2 — the label group is `D_p`: the homomorphism is injective (`κ ≥ 1`). -/
theorem Uhom_injective [NeZero κ] : Function.Injective (Uhom κ) := fun a b h =>
  Multiplicative.toAdd.injective (U_injective κ (congrArg Units.val h))

/-- 10:C2 — the grading `A_p^{(r,s)} A_p^{(r',s')} ⊆ A_p^{(r+r', s+s')}` on the basis:
`(q U_{r,s})(q' U_{r',s'}) = q q' U_{r+r', s+s'}`. -/
theorem fibre_mul (a b : Dom κ) (q q' : ZMod (4 * κ + 1)) :
    single a q * single b q' = single (a + b) (q * q') :=
  single_mul_single a b q q'

/-- 10:C2 — the grading on the fibres `A_p^{(r,s)} = F_p U_{r,s}` (Mathlib's `grade`): the product of two
homogeneous quantities lies in the fibre of the sum of their domains. -/
theorem graded {x y : QA κ} {a b : Dom κ} (hx : x ∈ grade (ZMod (4 * κ + 1)) a)
    (hy : y ∈ grade (ZMod (4 * κ + 1)) b) : x * y ∈ grade (ZMod (4 * κ + 1)) (a + b) :=
  SetLike.mul_mem_graded (A := grade (ZMod (4 * κ + 1))) hx hy

/-- 10:C3 — fibrewise addition: two quantities of one domain add within the fibre,
`q U_{r,s} + q' U_{r,s} = (q + q') U_{r,s}`. -/
theorem fibre_add (a : Dom κ) (q q' : ZMod (4 * κ + 1)) :
    single a q + single a q' = single a (q + q') :=
  (single_add a q q').symm

/-- 10:C3 — the component of a sum of homogeneous quantities in the fibre `a` is the sum of the summands of
domain `a`: the sum is homogeneous of domain `a` exactly when every other component vanishes. -/
theorem coeff_sum_single {ι : Type*} (s : Finset ι) (m : ι → Dom κ) (q : ι → ZMod (4 * κ + 1))
    (a : Dom κ) : (∑ j ∈ s, single (m j) (q j)).coeff a = ∑ j ∈ s with m j = a, q j := by
  rw [coeff_sum, Finsupp.finsetSum_apply, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [coeff_single, Finsupp.single_apply]

/-- 10:C3 — the domain of a monomial: `∏ (q_j U_{a_j})^{k_j} = (∏ q_j^{k_j}) U_{Σ k_j a_j}`. -/
theorem monomial {ι : Type*} (s : Finset ι) (m : ι → Dom κ) (q : ι → ZMod (4 * κ + 1)) (k : ι → ℕ) :
    ∏ j ∈ s, single (m j) (q j) ^ k j = single (∑ j ∈ s, k j • m j) (∏ j ∈ s, q j ^ k j) := by
  simp_rw [single_pow]; exact prod_single s _ _

/-- 10:C3, 10:G4 — the domain of a monomial with integer exponents, in the label group:
`∏ U_{a_j}^{k_j} = U_{Σ k_j a_j}`; so on the shell a monomial is neutral iff `Σ k_j a_j = 0`, the neutrality
criterion that G4's count reads on the lift through the window coincidence (`window_neutrality`). -/
theorem monomial_units {ι : Type*} (s : Finset ι) (m : ι → Dom κ) (k : ι → ℤ) :
    ∏ j ∈ s, Uhom κ (Multiplicative.ofAdd (m j)) ^ k j
      = Uhom κ (Multiplicative.ofAdd (∑ j ∈ s, k j • m j)) := by
  rw [ofAdd_sum, map_prod]
  exact Finset.prod_congr rfl (fun j _ => by rw [ofAdd_zsmul, map_zpow])

/-- 10:C3 — the neutral-domain criterion: a nonzero homogeneous quantity `c U_a` lies in the fibre `b` iff
`a = b`; so a monomial with nonzero coefficient is a neutral-domain invariant iff `Σ k_j a_j = 0` in `D_p`. -/
theorem single_mem_grade_iff (a b : Dom κ) {c : ZMod (4 * κ + 1)} (hc : c ≠ 0) :
    single a c ∈ grade (ZMod (4 * κ + 1)) b ↔ a = b := by
  rw [mem_grade_iff, coeff_single, Finsupp.support_single_ne_zero _ hc,
    Finset.singleton_subset_iff, Finset.mem_singleton]

end lattice

/-! ## Arithmetic of the time factor `C_{4κ}`, and the flag (10:D2, 10:C6, 10:D3) -/
section timefactor

variable (κ : ℕ) [NeZero κ]

theorem kappa_ne_zero : (κ : ZMod (4 * κ)) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  have h1 := Nat.le_of_dvd (NeZero.pos κ) h
  have h2 := NeZero.pos κ
  omega

theorem two_kappa_ne_zero : 2 * (κ : ZMod (4 * κ)) ≠ 0 := by
  rw [show 2 * (κ : ZMod (4 * κ)) = ((2 * κ : ℕ) : ZMod (4 * κ)) by push_cast; rfl, Ne,
    ZMod.natCast_eq_zero_iff]
  intro h
  have h2 := NeZero.pos κ
  have h1 := Nat.le_of_dvd (by omega) h
  omega

theorem three_kappa_ne_zero : 3 * (κ : ZMod (4 * κ)) ≠ 0 := by
  rw [show 3 * (κ : ZMod (4 * κ)) = ((3 * κ : ℕ) : ZMod (4 * κ)) by push_cast; rfl, Ne,
    ZMod.natCast_eq_zero_iff]
  intro h
  have h2 := NeZero.pos κ
  have h1 := Nat.le_of_dvd (by omega) h
  omega

omit [NeZero κ] in
theorem four_kappa : 4 * (κ : ZMod (4 * κ)) = 0 := by
  rw [show 4 * (κ : ZMod (4 * κ)) = ((4 * κ : ℕ) : ZMod (4 * κ)) by push_cast; rfl]
  exact ZMod.natCast_self _

omit [NeZero κ] in
/-- `3κ = −κ` in `C_{4κ}`: the two generators of the flag subgroup are inverse. -/
theorem three_kappa : 3 * (κ : ZMod (4 * κ)) = -(κ : ZMod (4 * κ)) := by
  have := four_kappa κ; linear_combination this

/-- `a·s = 0` in `C_{4κ}` iff `b ∣ s.val`, where `4κ = a·b`. -/
theorem nat_mul_eq_zero_iff (a b : ℕ) (ha : 0 < a) (hb : 4 * κ = a * b) (s : ZMod (4 * κ)) :
    (a : ZMod (4 * κ)) * s = 0 ↔ b ∣ s.val := by
  have h1 : (a : ZMod (4 * κ)) * s = ((a * s.val : ℕ) : ZMod (4 * κ)) := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
  rw [h1, ZMod.natCast_eq_zero_iff]
  generalize s.val = v
  rw [hb]
  exact Nat.mul_dvd_mul_iff_left ha

/-- `2s = 0` in `C_{4κ}` iff `s ∈ {0, 2κ}`: the one element of order two is the half-period. -/
theorem two_mul_eq_zero_iff (s : ZMod (4 * κ)) :
    2 * s = 0 ↔ s = 0 ∨ s = 2 * (κ : ZMod (4 * κ)) := by
  have hκ := NeZero.pos κ
  have h := nat_mul_eq_zero_iff κ 2 (2 * κ) (by norm_num) (by ring) s
  push_cast at h
  rw [h]
  constructor
  · rintro ⟨m, hm⟩
    have hlt := s.val_lt
    rw [hm] at hlt
    have hm2 : m < 2 := by
      have : 2 * κ * m < 2 * κ * 2 := by rw [show 2 * κ * 2 = 4 * κ by ring]; exact hlt
      exact Nat.lt_of_mul_lt_mul_left this
    have hs : s = ((2 * κ * m : ℕ) : ZMod (4 * κ)) := by rw [← hm, ZMod.natCast_zmod_val]
    interval_cases m
    · left; rw [hs]; simp
    · right; rw [hs]; push_cast; ring
  · rintro (rfl | rfl)
    · simp
    · rw [show (2 * (κ : ZMod (4 * κ))) = ((2 * κ : ℕ) : ZMod (4 * κ)) by push_cast; rfl,
        ZMod.val_natCast_of_lt (by omega)]

/-- `4s = 0` in `C_{4κ}` iff `s ∈ {0, κ, 2κ, 3κ}`: the subgroup of order four. -/
theorem four_mul_eq_zero_iff (s : ZMod (4 * κ)) :
    4 * s = 0 ↔ s = 0 ∨ s = κ ∨ s = 2 * (κ : ZMod (4 * κ)) ∨ s = 3 * (κ : ZMod (4 * κ)) := by
  have hκ := NeZero.pos κ
  have h := nat_mul_eq_zero_iff κ 4 κ (by norm_num) rfl s
  push_cast at h
  rw [h]
  constructor
  · rintro ⟨m, hm⟩
    have hlt := s.val_lt
    rw [hm] at hlt
    have hm4 : m < 4 := by
      have : κ * m < κ * 4 := by rw [Nat.mul_comm κ 4]; exact hlt
      exact Nat.lt_of_mul_lt_mul_left this
    have hs : s = ((κ * m : ℕ) : ZMod (4 * κ)) := by rw [← hm, ZMod.natCast_zmod_val]
    interval_cases m
    · left; rw [hs]; simp
    · right; left; rw [hs]; simp
    · right; right; left; rw [hs]; push_cast; ring
    · right; right; right; rw [hs]; push_cast; ring
  · rintro (rfl | rfl | rfl | rfl)
    · simp
    · rw [ZMod.val_natCast_of_lt (by omega)]
    · rw [show (2 * (κ : ZMod (4 * κ))) = ((2 * κ : ℕ) : ZMod (4 * κ)) by push_cast; rfl,
        ZMod.val_natCast_of_lt (by omega)]
      exact Dvd.intro_left 2 rfl
    · rw [show (3 * (κ : ZMod (4 * κ))) = ((3 * κ : ℕ) : ZMod (4 * κ)) by push_cast; rfl,
        ZMod.val_natCast_of_lt (by omega)]
      exact Dvd.intro_left 3 rfl

omit [NeZero κ] in
/-- Every unit of `C_{4κ}` is odd: its representative is coprime to `4κ`, hence to `2`. -/
theorem unit_odd (ε : (ZMod (4 * κ))ˣ) : Odd (ε : ZMod (4 * κ)).val := by
  have h := ZMod.val_coe_unit_coprime ε
  have h2 : Nat.Coprime 2 (ε : ZMod (4 * κ)).val :=
    (Nat.Coprime.coprime_dvd_right ⟨2 * κ, by ring⟩ h).symm
  exact Nat.Coprime.odd_of_left h2

/-- `ε · u` for a unit, written through the odd representative `2m + 1`. -/
theorem unit_mul (ε : (ZMod (4 * κ))ˣ) (u : ZMod (4 * κ)) :
    ∃ m : ℕ, (ε : ZMod (4 * κ)) * u = ((2 * m + 1 : ℕ) : ZMod (4 * κ)) * u := by
  obtain ⟨m, hm⟩ := unit_odd κ ε
  exact ⟨m, by rw [← ZMod.natCast_zmod_val (ε : ZMod (4 * κ)), hm]⟩

theorem flag_ne_zero : flag κ ≠ 0 := fun h => kappa_ne_zero κ (congrArg Prod.snd h)

omit [NeZero κ] in
/-- 10:D2 — `I_q⁴ = 1`. -/
theorem four_smul_flag : 4 • flag κ = 0 := by
  ext
  · simp [flag]
  · simp only [flag, nsmul_eq_mul, Nat.cast_ofNat, Prod.snd_zero]; exact four_kappa κ

omit [NeZero κ] in
/-- 10:D2 — `I_q² = [T]^π`, the half-period `π = 2κ`. -/
theorem two_smul_flag : 2 • flag κ = (0, 2 * (κ : ZMod (4 * κ))) := by
  ext <;> simp [flag]

theorem two_smul_flag_ne_zero : 2 • flag κ ≠ 0 := by
  rw [two_smul_flag]; intro h; exact two_kappa_ne_zero κ (congrArg Prod.snd h)

theorem three_smul_flag_ne_zero : 3 • flag κ ≠ 0 := by
  intro h
  have := congrArg Prod.snd h
  simp only [flag, nsmul_eq_mul, Nat.cast_ofNat, Prod.snd_zero] at this
  exact three_kappa_ne_zero κ this

/-- 10:D2 — the flag has order four. -/
theorem addOrderOf_flag : addOrderOf (flag κ) = 4 := by
  rw [addOrderOf_eq_iff (by norm_num)]
  refine ⟨four_smul_flag κ, fun m hm hm0 => ?_⟩
  interval_cases m
  · rw [one_smul]; exact flag_ne_zero κ
  · exact two_smul_flag_ne_zero κ
  · exact three_smul_flag_ne_zero κ

/-- 10:D2 — the conjugate generator `I_q⁻¹ = (0, 3κ)` has order four as well. -/
theorem addOrderOf_neg_flag : addOrderOf (-flag κ) = 4 := by
  rw [addOrderOf_eq_iff (by norm_num)]
  refine ⟨by rw [smul_neg, four_smul_flag, neg_zero], fun m hm hm0 h => ?_⟩
  rw [smul_neg, neg_eq_zero] at h
  interval_cases m
  · rw [one_smul] at h; exact flag_ne_zero κ h
  · exact two_smul_flag_ne_zero κ h
  · exact three_smul_flag_ne_zero κ h

omit [NeZero κ] in
/-- 10:D2, 10:C6 — meridian transport onto the flag: the two periods interfere, `([L][T]^κ)^p = I_q` —
the meridian component wraps (`p ≡ 0 (mod p)`) while the phase component advances by
`pκ = 4κ·κ + κ ≡ κ (mod 4κ)`; for every shell. -/
theorem meridian_transport : (4 * κ + 1) • (L κ + κ • T κ) = flag κ := by
  have h1 : L κ + κ • T κ = (1, (κ : ZMod (4 * κ))) := by ext <;> simp [L, T]
  rw [h1, flag, Prod.smul_mk]
  ext
  · show (4 * κ + 1) • (1 : ZMod (4 * κ + 1)) = 0
    rw [nsmul_eq_mul, mul_one]; exact ZMod.natCast_self _
  · show (4 * κ + 1) • (κ : ZMod (4 * κ)) = κ
    rw [nsmul_eq_mul]; push_cast
    rw [show (4 : ZMod (4 * κ)) * κ = ((4 * κ : ℕ) : ZMod (4 * κ)) by push_cast; rfl,
      ZMod.natCast_self, zero_add, one_mul]

/-- 10:D3 — the record map `s ↦ I_q^s`, `Z_4 → D_p`: index-preserving (the flag exponent `κ` is the
fractional index of one quarter), a homomorphism because `I_q⁴ = 1`. -/
def record : ZMod 4 →+ Dom κ :=
  ZMod.lift 4 ⟨zmultiplesHom _ (flag κ), by
    rw [zmultiplesHom_apply, natCast_zsmul]; exact four_smul_flag κ⟩

omit [NeZero κ] in
theorem record_natCast (m : ℕ) : record κ (m : ZMod 4) = m • flag κ := by
  have h : ((m : ℤ) : ZMod 4) = (m : ZMod 4) := Int.cast_natCast m
  rw [← h, record, ZMod.lift_coe, zmultiplesHom_apply, natCast_zsmul]

/-- 10:D3 — the record map is injective: an isomorphism of `Z_4` onto the flag subgroup. -/
theorem record_injective : Function.Injective (record κ) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  rw [← ZMod.natCast_zmod_val s, record_natCast, ← addOrderOf_dvd_iff_nsmul_eq_zero,
    addOrderOf_flag] at hs
  have h0 := Nat.eq_zero_of_dvd_of_lt hs s.val_lt
  exact (ZMod.natCast_zmod_val s).symm.trans (by rw [h0, Nat.cast_zero])

omit [NeZero κ] in
/-- 10:D3 — the image of the record map is the flag subgroup `⟨I_q⟩ = {1, I_q, I_q², I_q³}`. -/
theorem record_range : (record κ).range = AddSubgroup.zmultiples (flag κ) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨s, rfl⟩ := AddMonoidHom.mem_range.mp hx
    rw [← ZMod.natCast_zmod_val s, record_natCast, ← natCast_zsmul]
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨_, rfl⟩
  · intro x hx
    obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
    refine AddMonoidHom.mem_range.mpr ⟨(n : ZMod 4), ?_⟩
    rw [record, ZMod.lift_coe, zmultiplesHom_apply]

omit [NeZero κ] in
/-- An element of the parity subgroup `⟨I_q²⟩` is killed by `2`. -/
theorem two_smul_of_mem_parity (x : Dom κ) (hx : x ∈ AddSubgroup.zmultiples (2 • flag κ)) :
    2 • x = 0 := by
  obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
  rw [smul_comm, smul_smul, show 2 * 2 = 4 from rfl, four_smul_flag, smul_zero]

/-- 10:D3 — the chart shadow: `I_q^s` lies in the parity subgroup `{1, I_q²}` exactly when `s` is even —
the quotient of the record by `⟨I_q²⟩ = ⟨[T]^π⟩` returns `s mod 2`, and the kernel of the forgetting is
`{id, J}`. -/
theorem record_mem_parity_iff (s : ZMod 4) :
    record κ s ∈ AddSubgroup.zmultiples (2 • flag κ) ↔ 2 ∣ s.val := by
  obtain ⟨v, hv, rfl⟩ : ∃ v : ℕ, v < 4 ∧ s = (v : ZMod 4) :=
    ⟨s.val, s.val_lt, (ZMod.natCast_zmod_val s).symm⟩
  rw [record_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hv]
  interval_cases v
  · simp
  · rw [one_smul]
    refine ⟨fun h => ?_, fun h => by omega⟩
    exact absurd (two_smul_of_mem_parity κ _ h) (two_smul_flag_ne_zero κ)
  · exact ⟨fun _ => dvd_refl 2, fun _ => AddSubgroup.mem_zmultiples _⟩
  · refine ⟨fun h => ?_, fun h => by omega⟩
    have h2 := two_smul_of_mem_parity κ _ h
    rw [smul_smul, show 2 * 3 = 4 + 2 from rfl, add_nsmul, four_smul_flag, zero_add] at h2
    exact absurd h2 (two_smul_flag_ne_zero κ)

end timefactor

/-! ## The chart duality and the crossed duality (10:D1, 10:D6) -/
section duality

variable (κ : ℕ)

/-- 10:D1 — the chart duality `δ_S : D ↦ D⁻¹`, an automorphism of the domain group. -/
def deltaS : Dom κ ≃+ Dom κ := AddEquiv.neg _

/-- 10:D1 — `δ_S` is an involution. -/
theorem deltaS_involutive (a : Dom κ) : deltaS κ (deltaS κ a) = a := neg_neg a

/-- 10:D1 — the orbit of `δ_S` on the generators: `[L] ↦ [L]⁻¹` (the momentum chart), `[T] ↦ [T]⁻¹` (the
energy chart). -/
theorem deltaS_generators : deltaS κ (L κ) = -L κ ∧ deltaS κ (T κ) = -T κ := ⟨rfl, rfl⟩

/-- 10:D1 — the four labels `[L], [L]⁻¹, [T], [T]⁻¹` are pairwise distinct (`κ ≥ 1`): the orbit is the
four-domain structure. -/
theorem four_domains [NeZero κ] :
    L κ ≠ -L κ ∧ T κ ≠ -T κ ∧ L κ ≠ T κ ∧ L κ ≠ -T κ ∧ -L κ ≠ T κ ∧ -L κ ≠ -T κ := by
  have : Fact (2 < 4 * κ + 1) := ⟨by have := NeZero.pos κ; omega⟩
  have : Fact (2 < 4 * κ) := ⟨by have := NeZero.pos κ; omega⟩
  have : Fact (1 < 4 * κ + 1) := ⟨by have := NeZero.pos κ; omega⟩
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := congrArg Prod.fst h; simp [L] at this; exact ZMod.neg_one_ne_one this.symm
  · have := congrArg Prod.snd h; simp [T] at this; exact ZMod.neg_one_ne_one this.symm
  · have := congrArg Prod.fst h; simp [L, T] at this
  · have := congrArg Prod.fst h; simp [L, T] at this
  · have := congrArg Prod.fst h; simp [L, T] at this
  · have := congrArg Prod.fst h; simp [L, T] at this

/-- 10:D6 — the flagged reading of frequency: the energy domain `[E] = [h][f] = I_q [T]⁻¹`. -/
def energy : Dom κ := flag κ - T κ

/-- 10:D6 — the flagged reading of wavenumber: the momentum domain `[p] = [ħ][k] = I_q [L]⁻¹`. -/
def mom : Dom κ := flag κ - L κ

/-- 10:D1, 10:E8 — the crossed duality `δ_C = I_q δ_S : D ↦ I_q D⁻¹`, the primal-to-dual passage of the
Carrier register. -/
def deltaC (a : Dom κ) : Dom κ := flag κ - a

/-- 10:D1 — `δ_C` is an involution: `δ_C²(D) = I_q (I_q D⁻¹)⁻¹ = D`. -/
theorem deltaC_involutive (a : Dom κ) : deltaC κ (deltaC κ a) = a := sub_sub_cancel _ _

/-- 10:D1 — `δ_C` carries `[L] ↦ [p]` and `[T] ↦ [E]`: the dual horizons are the flag-crossed images of the
primal charts, while `δ_S` is flag-free. -/
theorem deltaC_generators : deltaC κ (L κ) = mom κ ∧ deltaC κ (T κ) = energy κ := ⟨rfl, rfl⟩

/-- 10:D6 — the flagged readings sit one capacity step above their counts: `[E] = [T]^{κ−1}` and
`[p] = [L]^{−1}[T]^κ` on the realized lattice; `[S] = [E][T] = I_q` and the phase counts are neutral,
`[E][T][ħ]⁻¹ = 1`, `[p][L][ħ]⁻¹ = 1`. -/
theorem flagged_readings :
    energy κ = (0, (κ : ZMod (4 * κ)) - 1) ∧ mom κ = (-1, (κ : ZMod (4 * κ))) ∧
    energy κ + T κ = flag κ ∧ energy κ + T κ - flag κ = 0 ∧ mom κ + L κ - flag κ = 0 := by
  refine ⟨?_, ?_, sub_add_cancel _ _, ?_, ?_⟩
  · ext <;> simp [energy, flag, T]
  · ext <;> simp [mom, flag, L]
  · rw [energy, sub_add_cancel, sub_self]
  · rw [mom, sub_add_cancel, sub_self]

/-- 10:D6 — the flag is horizon-inaccessible: no in-window label `(r, s)` with `|s| ≤ H < κ` realizes
`I_q = (0, κ)`, since `s ≡ κ (mod 4κ)` with `|κ − s| < 2κ` and `κ − s ≠ 0` is impossible; at
`κ ≤ H < 2κ` the chart monomial `[T]^κ` itself is the flag. -/
theorem flag_inaccessible (H : ℕ) (hH : H < κ) (r s : ℤ) (hs : |s| ≤ H) :
    ((r : ZMod (4 * κ + 1)), (s : ZMod (4 * κ))) ≠ flag κ ∧
    ((0 : ZMod (4 * κ + 1)), ((κ : ℤ) : ZMod (4 * κ))) = flag κ := by
  refine ⟨fun h => ?_, by simp [flag]⟩
  have h2 := congrArg Prod.snd h
  simp only [flag] at h2
  rw [← Int.cast_natCast κ, ZMod.intCast_eq_intCast_iff_dvd_sub] at h2
  have hb := abs_le.mp hs
  have := Int.eq_zero_of_abs_lt_dvd h2 (abs_lt.mpr ⟨by push_cast; omega, by push_cast; omega⟩)
  omega

end duality

/-! ## The internal flag on the prime shell (10:D2) -/
section flagprime

variable (κ : ℕ) [NeZero κ] [hp : Fact (Nat.Prime (4 * κ + 1))]

omit [NeZero κ] in
/-- 10:D2 — no flag of space: `4r = 0` in `C_p` forces `r = 0` (`p` an odd prime), so the meridian factor
contributes no element of order four. -/
theorem no_flag_of_space (r : ZMod (4 * κ + 1)) (h : 4 * r = 0) : r = 0 := by
  have h4 : (4 : ZMod (4 * κ + 1)) ≠ 0 := by
    rw [show (4 : ZMod (4 * κ + 1)) = ((4 : ℕ) : ZMod (4 * κ + 1)) by norm_cast, Ne,
      ZMod.natCast_eq_zero_iff]
    intro hd
    have h1 : 4 * κ + 1 ≤ 4 := Nat.le_of_dvd (by norm_num) hd
    have h2 : 2 ≤ 4 * κ + 1 := hp.out.two_le
    omega
  rcases mul_eq_zero.mp h with h | h
  · exact absurd h h4
  · exact h

/-- `2r = 0` in `C_p` forces `r = 0`. -/
theorem two_mul_eq_zero (r : ZMod (4 * κ + 1)) (h : 2 * r = 0) : r = 0 := by
  have h2 : (2 : ZMod (4 * κ + 1)) ≠ 0 := by
    rw [show (2 : ZMod (4 * κ + 1)) = ((2 : ℕ) : ZMod (4 * κ + 1)) by norm_cast, Ne,
      ZMod.natCast_eq_zero_iff]
    intro hd
    have h1 : 4 * κ + 1 ≤ 2 := Nat.le_of_dvd (by norm_num) hd
    have h2 := NeZero.pos κ
    omega
  rcases mul_eq_zero.mp h with h | h
  · exact absurd h h2
  · exact h

/-- 10:D2 — the elements of order four of `D_p` are exactly `I_q = (0, κ)` and `I_q⁻¹ = (0, 3κ)`: every one
lies in the time-exponent factor. -/
theorem order_four_iff (x : Dom κ) : addOrderOf x = 4 ↔ x = flag κ ∨ x = -flag κ := by
  constructor
  · intro h
    rw [addOrderOf_eq_iff (by norm_num)] at h
    obtain ⟨h4, hlt⟩ := h
    obtain ⟨r, s⟩ := x
    have h4' := h4
    rw [Prod.smul_mk, Prod.mk_eq_zero, nsmul_eq_mul, nsmul_eq_mul] at h4'
    obtain ⟨hr, hs⟩ := h4'
    have hr0 : r = 0 := no_flag_of_space κ r (by exact_mod_cast hr)
    subst hr0
    have hs' := (four_mul_eq_zero_iff κ s).mp (by exact_mod_cast hs)
    rcases hs' with rfl | rfl | rfl | rfl
    · exact absurd (by simp) (hlt 1 (by norm_num) (by norm_num))
    · left; rfl
    · exfalso
      apply hlt 2 (by norm_num) (by norm_num)
      ext
      · simp
      · simp only [Prod.smul_mk, nsmul_eq_mul, Nat.cast_ofNat, Prod.snd_zero]
        linear_combination four_kappa κ
    · right; ext
      · show (0 : ZMod (4 * κ + 1)) = -(0 : ZMod (4 * κ + 1)); exact neg_zero.symm
      · show 3 * (κ : ZMod (4 * κ)) = -(κ : ZMod (4 * κ)); exact three_kappa κ
  · rintro (rfl | rfl)
    · exact addOrderOf_flag κ
    · exact addOrderOf_neg_flag κ

/-- 10:D2 — the one element of order two of `D_p` is the half-period `I_q² = (0, 2κ)`. -/
theorem order_two_iff (x : Dom κ) : addOrderOf x = 2 ↔ x = 2 • flag κ := by
  constructor
  · intro h
    rw [addOrderOf_eq_iff (by norm_num)] at h
    obtain ⟨h2, hlt⟩ := h
    obtain ⟨r, s⟩ := x
    have h2' := h2
    rw [Prod.smul_mk, Prod.mk_eq_zero, nsmul_eq_mul, nsmul_eq_mul] at h2'
    obtain ⟨hr, hs⟩ := h2'
    have hr0 : r = 0 := two_mul_eq_zero κ r (by exact_mod_cast hr)
    subst hr0
    have hs' := (two_mul_eq_zero_iff κ s).mp (by exact_mod_cast hs)
    rcases hs' with rfl | rfl
    · exact absurd (by simp) (hlt 1 (by norm_num) (by norm_num))
    · rw [two_smul_flag]
  · rintro rfl
    rw [addOrderOf_eq_iff (by norm_num)]
    refine ⟨?_, fun m hm hm0 => ?_⟩
    · rw [smul_smul, show 2 * 2 = 4 from rfl]; exact four_smul_flag κ
    · interval_cases m; rw [one_smul]; exact two_smul_flag_ne_zero κ

/-- 10:D2 — `D_p` contains exactly one subgroup of order four, `⟨I_q⟩ = {1, I_q, I_q², I_q³}`. -/
theorem unique_order_four_subgroup (H : AddSubgroup (Dom κ)) (hH : Nat.card H = 4) :
    H = AddSubgroup.zmultiples (flag κ) := by
  have horder : ∀ x ∈ H, addOrderOf x ∣ 4 := fun x hx => by
    have := addOrderOf_dvd_natCard (⟨x, hx⟩ : H)
    rw [← AddSubgroup.addOrderOf_coe, hH] at this
    exact this
  by_cases hex : ∃ x ∈ H, addOrderOf x = 4
  · obtain ⟨x, hx, hx4⟩ := hex
    have hflag : flag κ ∈ H := by
      rcases (order_four_iff κ x).mp hx4 with rfl | rfl
      · exact hx
      · exact H.neg_mem_iff.mp hx
    have hle : AddSubgroup.zmultiples (flag κ) ≤ H := by
      rw [AddSubgroup.zmultiples_le]; exact hflag
    symm
    refine AddSubgroup.eq_of_le_of_card_ge hle ?_
    rw [hH, Nat.card_zmultiples, addOrderOf_flag]
  · exfalso
    have hex' : ∀ x ∈ H, addOrderOf x ≠ 4 := fun x hx h4 => hex ⟨x, hx, h4⟩
    -- every element has order one or two, so `H ≤ ⟨I_q²⟩`, of order two
    have hle : H ≤ AddSubgroup.zmultiples (2 • flag κ) := by
      intro x hx
      have hd : addOrderOf x ∣ 2 ^ 2 := horder x hx
      rw [Nat.dvd_prime_pow Nat.prime_two] at hd
      obtain ⟨k, hk, hk'⟩ := hd
      interval_cases k
      · rw [pow_zero] at hk'
        have h1 : 1 • x = 0 := addOrderOf_dvd_iff_nsmul_eq_zero.mp (by rw [hk'])
        rw [one_smul] at h1
        rw [h1]; exact zero_mem _
      · rw [pow_one, order_two_iff] at hk'
        rw [hk']; exact AddSubgroup.mem_zmultiples _
      · exact absurd hk' (hex' x hx)
    have hcard := AddSubgroup.card_le_of_le hle
    rw [hH, Nat.card_zmultiples, (order_two_iff κ _).mpr rfl] at hcard
    omega

end flagprime

/-! ## The lift: the operator four-cycle and the Carrier face (10:D3) -/
section lift

/-- 10:D3 — the operator four-cycle behind the lift, on the shell `F_p`, `p = 4κ + 1`: `F = i W` with
`i = −g^κ` has `F² = J` and `F⁴ = 1` (6-fourier's B7, `Fourier.shell_relations`), and `F² = J ≠ 1` since
`J` exchanges the index `1` with `−1 ≠ 1` on a cycle of length `4κ ≥ 4`: the operator has order four, its
square the parity. -/
theorem operator_four_cycle (κ : ℕ) [NeZero κ] [Fact (Nat.Prime (4 * κ + 1))]
    (g : ZMod (4 * κ + 1)) (hg : IsPrimitiveRoot g (Fintype.card (ZMod (4 * κ + 1)) - 1)) :
    haveI : NeZero (Fintype.card (ZMod (4 * κ + 1)) - 1) :=
      ⟨by have := Fintype.one_lt_card (α := ZMod (4 * κ + 1)); omega⟩
    ((-(g ^ κ)) • Fourier.W g : Matrix (Fin (Fintype.card (ZMod (4 * κ + 1)) - 1))
        (Fin (Fintype.card (ZMod (4 * κ + 1)) - 1)) (ZMod (4 * κ + 1))) ^ 2 = Fourier.J ∧
    ((-(g ^ κ)) • Fourier.W g : Matrix (Fin (Fintype.card (ZMod (4 * κ + 1)) - 1))
        (Fin (Fintype.card (ZMod (4 * κ + 1)) - 1)) (ZMod (4 * κ + 1))) ^ 4 = 1 ∧
    (Fourier.J : Matrix (Fin (Fintype.card (ZMod (4 * κ + 1)) - 1))
        (Fin (Fintype.card (ZMod (4 * κ + 1)) - 1)) (ZMod (4 * κ + 1))) ≠ 1 := by
  have : NeZero (Fintype.card (ZMod (4 * κ + 1)) - 1) :=
    ⟨by have := Fintype.one_lt_card (α := ZMod (4 * κ + 1)); omega⟩
  have hc : Fintype.card (ZMod (4 * κ + 1)) = 4 * κ + 1 := ZMod.card _
  obtain ⟨-, hF2, hF4, -⟩ := Fourier.shell_relations κ hc g hg
  refine ⟨hF2, hF4, fun hJ => ?_⟩
  have hn : 4 ≤ Fintype.card (ZMod (4 * κ + 1)) - 1 := by
    rw [hc]; have := NeZero.pos κ; omega
  have h1 : ((1 : Fin (Fintype.card (ZMod (4 * κ + 1)) - 1)) : ℕ) = 1 := by
    rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
  have hne : (1 : Fin (Fintype.card (ZMod (4 * κ + 1)) - 1)) ≠ -1 := by
    intro h
    have h0 : (1 : Fin (Fintype.card (ZMod (4 * κ + 1)) - 1)) ≠ 0 := by
      intro h0; have := congrArg Fin.val h0; rw [h1] at this; exact one_ne_zero this
    have := congrArg Fin.val h
    simp only [Fin.val_neg, h0, ite_false, h1] at this
    omega
  have := congrFun (congrFun hJ 1) (-1)
  rw [Matrix.one_apply_ne hne] at this
  simp [Fourier.J] at this

/-- 10:D3 — the Carrier face of the lift: the crossing quantum `ħ` with `ħ² ≡ −1 (mod Ω)` has `ħ⁴ = 1` and
`ħ² ≠ 1` — two crossings the half-turn, four the identity, never two (`Ω > 2`). -/
theorem crossing_order_four {Ω : ℕ} [Fact (2 < Ω)] (hbar : ZMod Ω) (h : hbar ^ 2 = -1) :
    hbar ^ 4 = 1 ∧ hbar ^ 2 ≠ 1 := by
  refine ⟨by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h]; norm_num, ?_⟩
  rw [h]; exact ZMod.neg_one_ne_one

end lift

/-! ## Window covariance (10:C5) -/
section covariance

variable (κ : ℕ) [NeZero κ]

/-- 10:C5, 10:D3 — invariance under the pushforward `u ↦ εu` of every unit `ε` of `C_{4κ}` holds exactly on
the cardinal pair `{0, 2κ}`: `ε = −1` is always admissible and forces `2u = 0`; conversely every unit is
odd, so it fixes the half-period. -/
theorem invariant_iff (u : ZMod (4 * κ)) :
    (∀ ε : (ZMod (4 * κ))ˣ, (ε : ZMod (4 * κ)) * u = u) ↔ u = 0 ∨ u = 2 * (κ : ZMod (4 * κ)) := by
  constructor
  · intro h
    have := h (-1)
    rw [Units.val_neg, Units.val_one, neg_one_mul] at this
    exact (two_mul_eq_zero_iff κ u).mp (by linear_combination -this)
  · rintro (rfl | rfl) ε
    · exact mul_zero _
    · obtain ⟨m, hm⟩ := unit_mul κ ε (2 * (κ : ZMod (4 * κ)))
      rw [hm]
      have : ((2 * m + 1 : ℕ) : ZMod (4 * κ)) * (2 * (κ : ZMod (4 * κ)))
          = ((m * (4 * κ) : ℕ) : ZMod (4 * κ)) + 2 * (κ : ZMod (4 * κ)) := by push_cast; ring
      rw [this, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add]

/-- 10:C5 — the sharpness of the window bound: the half-period label `(0, π)`, `π = 2κ`, is invariant under
every re-presentation and is not neutral. -/
theorem half_period_invariant_not_neutral :
    (∀ ε : (ZMod (4 * κ))ˣ, (ε : ZMod (4 * κ)) * (2 * (κ : ZMod (4 * κ))) = 2 * (κ : ZMod (4 * κ))) ∧
    2 * (κ : ZMod (4 * κ)) ≠ 0 :=
  ⟨(invariant_iff κ _).mpr (Or.inr rfl), two_kappa_ne_zero κ⟩

/-- 10:C5 — the flagged label `(0, 0; 1)` moves under `ε = −1`: its realization `κ` goes to `3κ ≠ κ`, so
the flag-free restriction of window covariance cannot be dropped. -/
theorem flag_moves : -(κ : ZMod (4 * κ)) ≠ (κ : ZMod (4 * κ)) := by
  intro h
  exact two_kappa_ne_zero κ (by linear_combination -h)

/-- 10:C5, 10:D2 — the quarter-turn labels `±κ` are fixed or exchanged by the pushforward exactly as
`ε mod 4 ∈ {1, 3}`: `ε κ ≡ (ε mod 4) κ (mod 4κ)`, so `εκ = κ` for `ε ≡ 1` and `εκ = 3κ = −κ` for
`ε ≡ 3`; the flag subgroup is preserved and its generator fixed or conjugated, as the residue quarter-turn
`±i` is. -/
theorem quarter_turn_law (ε : (ZMod (4 * κ))ˣ) :
    ((ε : ZMod (4 * κ)).val % 4 = 1 ∧ (ε : ZMod (4 * κ)) * κ = κ) ∨
    ((ε : ZMod (4 * κ)).val % 4 = 3 ∧ (ε : ZMod (4 * κ)) * κ = -(κ : ZMod (4 * κ))) := by
  obtain ⟨m, hm⟩ := unit_odd κ ε
  rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
  · left
    refine ⟨by omega, ?_⟩
    rw [← ZMod.natCast_zmod_val (ε : ZMod (4 * κ)), hm, hk]
    have : ((2 * (k + k) + 1 : ℕ) : ZMod (4 * κ)) * κ
        = ((k * (4 * κ) : ℕ) : ZMod (4 * κ)) + κ := by push_cast; ring
    rw [this, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add]
  · right
    refine ⟨by omega, ?_⟩
    rw [← ZMod.natCast_zmod_val (ε : ZMod (4 * κ)), hm, hk]
    have : ((2 * (2 * k + 1) + 1 : ℕ) : ZMod (4 * κ)) * κ
        = ((k * (4 * κ) : ℕ) : ZMod (4 * κ)) + 3 * κ := by push_cast; ring
    rw [this, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add, three_kappa]

omit [NeZero κ] in
/-- 10:C5 — the `σ`-twisted lift of the pushforward: for `4 ∣ ε − σ` (so `σ = ±1` as `ε ≡ 1, 3 (mod 4)`),
`ε(s + jκ) ≡ εs + σ jκ (mod 4κ)` — the integer formula `(r, s; j) ↦ (r, εs; σ(ε) j)` is a lift
representative of the action `u ↦ εu` on the realized coordinate `u = s + jκ`, exact as a congruence. -/
theorem sigma_twist (ε σ s j : ℤ) (hσ : (4 : ℤ) ∣ ε - σ) :
    ((ε * (s + j * κ) : ℤ) : ZMod (4 * κ)) = ((ε * s + σ * j * κ : ℤ) : ZMod (4 * κ)) := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  obtain ⟨m, hm⟩ := hσ
  have hσ' : σ = ε - 4 * m := by linear_combination -hm
  subst hσ'
  exact ⟨-(m * j), by push_cast; ring⟩

omit [NeZero κ] in
/-- 10:C5 — the dilation character on the lift: for a primitive `m` (of order `p − 1`), `m^{−r} = 1` iff
`(p − 1) ∣ r`; on a window `|r| ≤ H < 2κ < p − 1` this forces `r = 0` — in-window invariance under every
dilation is `r = 0`. -/
theorem dilation_character (m : (ZMod (4 * κ + 1))ˣ) (hm : orderOf m = 4 * κ) (r : ℤ) :
    (m ^ (-r) = 1 ↔ ((4 * κ : ℕ) : ℤ) ∣ r) ∧
    (∀ H : ℕ, H < 2 * κ → |r| ≤ H → m ^ (-r) = 1 → r = 0) := by
  have key : m ^ (-r) = 1 ↔ ((4 * κ : ℕ) : ℤ) ∣ r := by
    rw [← orderOf_dvd_iff_zpow_eq_one, hm, dvd_neg]
  refine ⟨key, fun H hH hr h => ?_⟩
  have hd := key.mp h
  have hb := abs_le.mp hr
  refine Int.eq_zero_of_abs_lt_dvd hd (abs_lt.mpr ⟨?_, ?_⟩) <;> push_cast <;> omega

/-- 10:C5 — the boundary witnesses on `F_13` (`κ = 3`, `2⁻¹ = 7`, `5⁻¹ = 8`): the naive character is
ill-defined on the modular projection (`7³ ≠ 7¹⁶` although `3 ≡ 16 (mod 13)`), and the would-be temporal
character fails composition (`5² ≡ 1` in `Z_12^×` while `(5⁻¹)² ≠ 1` in `F_13`). -/
theorem witnesses13 :
    (2 : ZMod 13) * 7 = 1 ∧ (7 : ZMod 13) ^ 3 ≠ (7 : ZMod 13) ^ 16 ∧ (3 : ZMod 13) = 16 ∧
    (5 : ZMod 12) * 5 = 1 ∧ (5 : ZMod 13) * 8 = 1 ∧ (8 : ZMod 13) ^ 2 ≠ 1 := by
  decide

end covariance

/-! ## The unit face of the quartet (10:E1–E3) -/
section unitface

variable {K : Type*} [Field K]

/-- 10:E1, 10:E2 — one crossing, one action: with the dual horizons the crossed images `p_P = ħ/ℓ_P`,
`E_P = ħ/t_P`, the quartet satisfies the single identity `ℓ_P p_P = t_P E_P = ħ`. -/
theorem action_identity (l t hbar : K) (hl : l ≠ 0) (ht : t ≠ 0) :
    l * (hbar / l) = hbar ∧ t * (hbar / t) = hbar :=
  ⟨mul_div_cancel₀ hbar hl, mul_div_cancel₀ hbar ht⟩

/-- 10:E2 — the relation lattice has rank `4 − 1 = 3`: a quartet `(ℓ, t, p, E)` of scales with `ℓ, t ≠ 0`
satisfies `ℓp = tE` exactly when it is `(ℓ, t, ħ/ℓ, ħ/t)` for the one value `ħ = ℓp` — three free scales,
in bijection with the primitive triple `(ℓ_P, t_P, ħ)`. -/
theorem quartet_param (l t p E : K) (hl : l ≠ 0) (ht : t ≠ 0) :
    l * p = t * E ↔ (p = (l * p) / l ∧ E = (l * p) / t) := by
  constructor
  · intro h
    refine ⟨by rw [mul_div_cancel_left₀ p hl], ?_⟩
    rw [h, mul_div_cancel_left₀ E ht]
  · rintro ⟨-, hE⟩
    rw [hE, mul_div_cancel₀ _ ht]

/-- 10:E2 — pairing closure: the cross-domain relations reduce to `c` and `ħ` — the two faces of `c` agree,
`ℓ/t = E/p`; the mixed products are their monomials, `|k_B| = p t = ħ/c` and `ℓE = ħ c`. -/
theorem pairing_closure (l t p E : K) (hl : l ≠ 0) (ht : t ≠ 0) (hp : p ≠ 0) (h : l * p = t * E) :
    l / t = E / p ∧ p * t = (l * p) / (l / t) ∧ l * E = (l * p) * (l / t) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [div_eq_div_iff ht hp]; linear_combination h
  · rw [eq_div_iff (div_ne_zero hl ht), mul_div_assoc', div_eq_iff ht]; ring
  · rw [mul_div_assoc', eq_div_iff ht]; linear_combination (-l) * h

/-- 10:E3 — the cancellation identity `|k_B| c = ħ` at the unit face, `(p t)(ℓ/t) = ℓ p`; mass derived,
`m_P = p/c = E/c²`; the temperature horizon `Θ_P = E/|k_B| = E c/ħ`. -/
theorem cancellation (l t p E : K) (hl : l ≠ 0) (ht : t ≠ 0) (hp : p ≠ 0) (h : l * p = t * E) :
    (p * t) * (l / t) = l * p ∧ p / (l / t) = E / (l / t) ^ 2 ∧ E / (p * t) = E * (l / t) / (l * p) := by
  have hc : l / t ≠ 0 := div_ne_zero hl ht
  refine ⟨?_, ?_, ?_⟩
  · rw [mul_div_assoc', div_eq_iff ht]; ring
  · rw [div_eq_div_iff hc (pow_ne_zero 2 hc), div_pow, mul_div_assoc', mul_div_assoc',
      div_eq_div_iff (pow_ne_zero 2 ht) ht]
    linear_combination (l * t) * h
  · rw [mul_div_assoc', div_div, div_eq_div_iff (mul_ne_zero hp ht) (mul_ne_zero ht (mul_ne_zero hl hp))]
    ring

/-- 10:E2 — the normalisation to the totality, `G = ħ c / m_P² = ℓ² c³ / ħ`, and the recovery of the free
scale, `ℓ² = G ħ / c³`, `t = ℓ/c`, `p = ħ/ℓ`, `E = ħ c/ℓ`: `(c, ħ, G)` and `(ℓ_P, t_P, ħ)` carry the same
three scales, monomially in one direction and by the square of `ℓ` in the other. -/
theorem normalisation (l t p E : K) (hl : l ≠ 0) (ht : t ≠ 0) (hp : p ≠ 0) (h : l * p = t * E) :
    (l * p) * (l / t) / (p / (l / t)) ^ 2 = l ^ 2 * (l / t) ^ 3 / (l * p) ∧
    l ^ 2 = ((l * p) * (l / t) / (p / (l / t)) ^ 2) * (l * p) / (l / t) ^ 3 ∧
    t = l / (l / t) ∧ p = (l * p) / l ∧ E = (l * p) * (l / t) / l := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · field_simp
  · field_simp
  · rw [div_div_eq_mul_div, mul_div_cancel_left₀ t hl]
  · rw [mul_div_cancel_left₀ p hl]
  · rw [mul_div_assoc', eq_div_iff hl, eq_div_iff ht]; linear_combination (-l) * h

/-- 10:E2 — the sublattice `⟨c, ħ, G⟩` has index two in the free lattice on `{ℓ_P, t_P, ħ}`: the exponent
matrix of `c = ℓ t⁻¹`, `ħ`, `G = ℓ⁵ t⁻³ ħ⁻¹` has determinant `−2`. -/
theorem index_two : Matrix.det !![(1 : ℤ), -1, 0; 0, 0, 1; 5, -3, -1] = -2 := by
  rw [Matrix.det_fin_three]; simp

/-- 10:E2 — the positive root closes the bijection: for `c, ħ, G > 0` there is exactly one `ℓ > 0` with
`ℓ² = G ħ / c³`. -/
theorem scale_from_constants (c hbar G : ℝ) (hc : 0 < c) (hh : 0 < hbar) (hG : 0 < G) :
    ∃! l : ℝ, 0 < l ∧ l ^ 2 = G * hbar / c ^ 3 := by
  have hpos : 0 < G * hbar / c ^ 3 := by positivity
  refine ⟨Real.sqrt (G * hbar / c ^ 3), ⟨Real.sqrt_pos.mpr hpos, Real.sq_sqrt hpos.le⟩, ?_⟩
  rintro l ⟨hl, hl2⟩
  rw [← hl2, Real.sqrt_sq hl.le]

/-- 10:E2 — the exponent vectors over `(ℓ, t, p, E)`: the two faces of `c` differ by the relation
`ℓ − t + p − E` (`ℓp = tE`), as do the two faces of `ħ`; `ℓE = ħ c` and `p t = ħ/c` as exponent identities. -/
theorem exponent_faces :
    (![1, -1, 0, 0] : Fin 4 → ℤ) - ![0, 0, -1, 1] = ![1, -1, 1, -1] ∧
    (![1, 0, 1, 0] : Fin 4 → ℤ) - ![0, 1, 0, 1] = ![1, -1, 1, -1] ∧
    (![1, 0, 0, 1] : Fin 4 → ℤ) = ![0, 1, 0, 1] + ![1, -1, 0, 0] ∧
    (![0, 1, 1, 0] : Fin 4 → ℤ) = ![0, 1, 0, 1] - ![0, 0, -1, 1] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (ext i; fin_cases i <;> rfl)

end unitface

/-! ## The defining congruences at pair level (10:E4, 10:E5) -/
section carrier

variable {K : Type*} [Field K]

/-- 10:E4, 21:C2 — the linear defining congruence: on the Carrier chart (`4S + 1 = 0`, `2 ≠ 0`), `2G + 1 = 0`
has the unique solution `G = 2S`, the half-cycle. -/
theorem G_unique (S : ℕ) (hΩ : ((4 * S + 1 : ℕ) : K) = 0) (h2 : (2 : K) ≠ 0) (x : K) :
    2 * x + 1 = 0 ↔ x = ((2 * S : ℕ) : K) := by
  push_cast at hΩ ⊢
  constructor
  · intro h
    apply mul_left_cancel₀ h2
    linear_combination h - hΩ
  · rintro rfl; linear_combination hΩ

/-- 10:E4 — each quadratic defining congruence has exactly two roots, the pair `{x, −x}`: if `x² = a` with
`x ≠ 0` (`2 ≠ 0`), then `y² = a` iff `y = x` or `y = −x`, and `−x ≠ x`. -/
theorem root_pair (a x : K) (hx : x ^ 2 = a) (hx0 : x ≠ 0) (h2 : (2 : K) ≠ 0) :
    (∀ y : K, y ^ 2 = a ↔ y = x ∨ y = -x) ∧ -x ≠ x := by
  refine ⟨fun y => by rw [← hx]; exact sq_eq_sq_iff_eq_or_eq_neg, fun h => hx0 ?_⟩
  apply mul_left_cancel₀ h2
  linear_combination -h

/-- 10:E4 — the linkage derived at pair level: `k_B² = −2` and `2c² = 1` give `(k_B c)² = −1`, so
`k_B c ∈ {ħ, −ħ}` for any root `ħ` of `−1`: `{±k_B}{±c} = {±ħ}`. -/
theorem linkage (k c h : K) (hk : k ^ 2 = -2) (hc : 2 * c ^ 2 = 1) (hh : h ^ 2 = -1) :
    (k * c) ^ 2 = -1 ∧ (k * c = h ∨ k * c = -h) := by
  have h1 : (k * c) ^ 2 = -1 := by rw [mul_pow, hk]; linear_combination -hc
  exact ⟨h1, sq_eq_sq_iff_eq_or_eq_neg.mp (h1.trans hh.symm)⟩

/-- 10:E5 — the pair consequences, by field arithmetic from the defining congruences: `G = −c²`,
`G² = 4⁻¹`, `ħ⁴ = 1`, `(k_B c)² = −1`, and `(ħ c G⁻¹)² = −2`, so the monomial `ħ c G⁻¹` lands in the
pair `{±k_B}`. -/
theorem pair_consequences (G c h k : K) (h2 : (2 : K) ≠ 0) (hG : 2 * G + 1 = 0) (hc : 2 * c ^ 2 = 1)
    (hh : h ^ 2 = -1) (hk : k ^ 2 = -2) :
    G = -c ^ 2 ∧ G ^ 2 = 4⁻¹ ∧ h ^ 4 = 1 ∧ (k * c) ^ 2 = -1 ∧ (h * c * G⁻¹) ^ 2 = -2 ∧
    (h * c * G⁻¹ = k ∨ h * c * G⁻¹ = -k) := by
  have h4 : (4 : K) * G ^ 2 = 1 := by linear_combination (2 * G - 1) * hG
  have hG2 : G ^ 2 = 4⁻¹ := eq_inv_of_mul_eq_one_right h4
  have hm : (h * c * G⁻¹) ^ 2 = -2 := by
    rw [mul_pow, mul_pow, hh, inv_pow, hG2, inv_inv]; linear_combination (-2) * hc
  refine ⟨?_, hG2, ?_, (linkage k c h hk hc hh).1, hm, ?_⟩
  · apply mul_left_cancel₀ h2; linear_combination hG + hc
  · rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hh]; norm_num
  · exact sq_eq_sq_iff_eq_or_eq_neg.mp (hm.trans hk.symm)

/-- 10:E5 — representative inertness: the quadratics are sign-blind, and with `k_B c = −ħ` at one
assignment the sign assignment `(σ_c, σ_ħ, σ_k)` keeps the linkage iff `σ_ħ = σ_c σ_k` — so exactly the
four assignments with `σ_ħ = σ_c σ_k` are admissible (`σ_c, σ_k` free), a `(Z/2)²`; every identity of
`pair_consequences` holds on each, and the `ħ`-flip relabels within `{ħ, h}`. -/
theorem sign_assignments (c h k sc sh sk : K) (hh0 : h ≠ 0) (hl : k * c = -h)
    (hsc : sc = 1 ∨ sc = -1) (hsh : sh = 1 ∨ sh = -1) (hsk : sk = 1 ∨ sk = -1) :
    ((sk * k) * (sc * c) = -(sh * h) ↔ sh = sc * sk) ∧
    (sc * c) ^ 2 = c ^ 2 ∧ (sh * h) ^ 2 = h ^ 2 ∧ (sk * k) ^ 2 = k ^ 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : (sk * k) * (sc * c) = -(sc * sk * h) := by linear_combination (sk * sc) * hl
    rw [this, neg_inj]
    constructor
    · intro e; exact (mul_right_cancel₀ hh0 e).symm
    · intro e; rw [e]
  · rcases hsc with rfl | rfl <;> ring
  · rcases hsh with rfl | rfl <;> ring
  · rcases hsk with rfl | rfl <;> ring

/-- `−2` is a square when `−1` and `2` are (any commutative ring). -/
theorem isSquare_neg_two {R : Type*} [CommRing R] (h1 : IsSquare (-1 : R)) (h2 : IsSquare (2 : R)) :
    IsSquare (-2 : R) := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  exact ⟨a * b, by linear_combination 2 * ha + (a * a) * hb⟩

/-- 10:E4 — the `h`-form: `h = 2π ħ` with `2π = 4S ≡ −1` on the Carrier chart, so `h = −ħ` — the root
pair of `−1` is `{ħ, h}`. -/
theorem h_form (S : ℕ) (hΩ : ((4 * S + 1 : ℕ) : K) = 0) (hbar : K) :
    ((2 * (2 * S) : ℕ) : K) * hbar = -hbar := by
  push_cast at hΩ ⊢
  linear_combination hbar * hΩ

end carrier

section carrierZ

variable (S : ℕ) [hΩ : Fact (Nat.Prime (4 * S + 1))]

theorem omega_two_ne_zero : (2 : ZMod (4 * S + 1)) ≠ 0 := by
  rw [show (2 : ZMod (4 * S + 1)) = ((2 : ℕ) : ZMod (4 * S + 1)) by norm_cast, Ne,
    ZMod.natCast_eq_zero_iff]
  intro hd
  have h1 : 4 * S + 1 ≤ 2 := Nat.le_of_dvd (by norm_num) hd
  have h2 : 2 ≤ 4 * S + 1 := hΩ.out.two_le
  omega

/-- 10:E4 — existence on every admissible Carrier: `Ω = 4S + 1 ≡ 1 (mod 4)` makes `−1` a square
unconditionally; `S` even is `Ω ≡ 1 (mod 8)`, which makes `2` and hence `2⁻¹` squares; `−2` is the product.
So the four defining congruences are solvable, and `G = 2S` is their linear solution. -/
theorem residues_exist (hS : Even S) :
    IsSquare (-1 : ZMod (4 * S + 1)) ∧ IsSquare (2 : ZMod (4 * S + 1)) ∧
    IsSquare ((2 : ZMod (4 * S + 1))⁻¹) ∧ IsSquare (-2 : ZMod (4 * S + 1)) ∧
    2 * ((2 * S : ℕ) : ZMod (4 * S + 1)) + 1 = 0 := by
  have h1 : IsSquare (-1 : ZMod (4 * S + 1)) := ZMod.exists_sq_eq_neg_one_iff.mpr (by omega)
  have h2 : IsSquare (2 : ZMod (4 * S + 1)) := by
    obtain ⟨m, hm⟩ := hS
    exact (ZMod.exists_sq_eq_two_iff (by omega)).mpr (Or.inl (by omega))
  refine ⟨h1, h2, h2.inv, ?_, ?_⟩
  · exact isSquare_neg_two h1 h2
  · have : ((4 * S + 1 : ℕ) : ZMod (4 * S + 1)) = 0 := ZMod.natCast_self _
    push_cast at this ⊢; linear_combination this

omit [Fact (Nat.Prime (4 * S + 1))] in
/-- 10:E4 — the admissibility residues: `Ω = 4S + 1 ≡ 1 (mod 4)` for every `S`, and `S` even iff
`Ω ≡ 1 (mod 8)`. -/
theorem admissibility_residues : (4 * S + 1) % 4 = 1 ∧ (Even S ↔ (4 * S + 1) % 8 = 1) := by
  refine ⟨by omega, ?_⟩
  constructor
  · rintro ⟨m, hm⟩; omega
  · intro h; exact ⟨S / 2, by omega⟩

end carrierZ

/-- 10:E4, 10:E5 — the Carrier `Ω = 233` (`S = 58`, admissible: `58` even, `58 ≡ 1 (mod 3)`, `233` prime):
`G = 116 = 2S`, `ħ = 89`, `k_B = 124`, `c = 159`, `h = 144 = −ħ` satisfy the defining congruences, the
linkage `k_B c = −ħ`, `G = −c²`, `G² = 4⁻¹`, `ħ⁴ = 1`, and `ħ c = k_B G` (the monomial on the `k_B` residue);
the partner root `109 = −124` fails the linkage; decided in `ZMod 233`. -/
theorem carrier233 :
    Nat.Prime 233 ∧ 233 = 4 * 58 + 1 ∧ 58 % 2 = 0 ∧ 58 % 3 = 1 ∧
    2 * (116 : ZMod 233) + 1 = 0 ∧ (89 : ZMod 233) ^ 2 = -1 ∧ (124 : ZMod 233) ^ 2 = -2 ∧
    2 * (159 : ZMod 233) ^ 2 = 1 ∧ (124 : ZMod 233) * 159 = -89 ∧ (144 : ZMod 233) = -89 ∧
    (116 : ZMod 233) = -(159 : ZMod 233) ^ 2 ∧ 4 * (116 : ZMod 233) ^ 2 = 1 ∧
    (89 : ZMod 233) ^ 4 = 1 ∧ (89 : ZMod 233) * 159 = 124 * 116 ∧
    (109 : ZMod 233) = -124 ∧ (109 : ZMod 233) * 159 ≠ -89 := by
  refine ⟨by norm_num, ?_⟩; decide

/-- 10:E4, 10:E5, 21:C5 — the laboratory Carrier `Ω = 2 408 561` (`S = 602 140`, admissible):
`G = 1 204 280 = 2S`, `ħ = 18 688`, `k_B = 1 880 160`, `c = 171 106`, `h = 2 389 873 = −ħ` satisfy the defining
congruences, the linkage, `G = −c²`, `G² = 4⁻¹`, `ħ⁴ = 1`, `ħ c = k_B G`; decided in `ZMod 2408561`. -/
theorem carrierLab :
    Nat.Prime 2408561 ∧ 2408561 = 4 * 602140 + 1 ∧ 602140 % 2 = 0 ∧ 602140 % 3 = 1 ∧
    2 * (1204280 : ZMod 2408561) + 1 = 0 ∧ (18688 : ZMod 2408561) ^ 2 = -1 ∧
    (1880160 : ZMod 2408561) ^ 2 = -2 ∧ 2 * (171106 : ZMod 2408561) ^ 2 = 1 ∧
    (1880160 : ZMod 2408561) * 171106 = -18688 ∧ (2389873 : ZMod 2408561) = -18688 ∧
    (1204280 : ZMod 2408561) = -(171106 : ZMod 2408561) ^ 2 ∧
    4 * (1204280 : ZMod 2408561) ^ 2 = 1 ∧ (18688 : ZMod 2408561) ^ 4 = 1 ∧
    (18688 : ZMod 2408561) * 171106 = 1880160 * 1204280 := by
  refine ⟨by norm_num, ?_⟩; decide

/-! ## The lifted labels and the derived domains (10:D4, 10:F2–F4) -/
section labels

/-- 10:D4 — the full label `(r, s; j)`: the two exponents and the integer crossing degree `j`. -/
abbrev Lab := ℤ × ℤ × ℤ

/-- 10:D4 — the realization of the full label on the shell, `(r, s; j) ↦ U_{r, s + jκ}`. -/
def realize (κ : ℕ) : Lab →+ Dom κ where
  toFun x := ((x.1 : ZMod (4 * κ + 1)), ((x.2.1 + x.2.2 * κ : ℤ) : ZMod (4 * κ)))
  map_zero' := by simp
  map_add' x y := by ext <;> simp; ring

/-- 10:D4 — realization is a homomorphism: the sector of a product is the sum of the sectors. -/
theorem realize_add (κ : ℕ) (x y : Lab) : realize κ (x + y) = realize κ x + realize κ y :=
  map_add _ x y

/-- 10:D4 — the realized flag: `(0, 0; 1) ↦ I_q`. -/
theorem realize_flag (κ : ℕ) : realize κ (0, 0, 1) = flag κ := by
  ext <;> simp [realize, flag]

/-- The labels of the paper's Table (lifted): speed `[L][T]⁻¹`; energy `I_q[T]⁻¹`; the flag; time. -/
def speedL : Lab := (1, -1, 0)
def timeL : Lab := (0, 1, 0)
def spaceL : Lab := (1, 0, 0)
def flagL : Lab := (0, 0, 1)
def energyL : Lab := (0, -1, 1)
def massL : Lab := (-2, 1, 1)
def accelL : Lab := (1, -2, 0)
def forceL : Lab := (-1, -1, 1)
def momL : Lab := (-1, 0, 1)
def actionL : Lab := (0, 0, 1)
def powerL : Lab := (0, -2, 1)
def pressureL : Lab := (-3, -1, 1)
def gravL : Lab := (5, -3, -1)
def kBL : Lab := (-1, 1, 1)
def thetaL : Lab := (1, -2, 0)

/-- 10:F2 — the mechanical and gravitational domains from `[E] = I_q[T]⁻¹` and `[v] = [L][T]⁻¹`:
`[m] = [E][v]⁻² = I_q[L]⁻²[T]`, `[a] = [v][T]⁻¹`, `[F] = [m][a] = I_q[L]⁻¹[T]⁻¹`, `[p] = [m][v] = I_q[L]⁻¹`
(the flagged wavenumber `I_q[L]⁻¹` again), `[S] = [E][T] = I_q`, `[P] = [E][T]⁻¹ = I_q[T]⁻²`,
`[pressure] = [F][L]⁻² = I_q[L]⁻³[T]⁻¹`, `[G] = [F][L]²[m]⁻² = I_q⁻¹[L]⁵[T]⁻³`, and the quartet face
`[ħ][c][m]⁻² = [G]`; mass is derived, not primitive. -/
theorem mechanical_domains :
    massL = energyL - (2 : ℤ) • speedL ∧ massL = (-2, 1, 1) ∧
    accelL = speedL - timeL ∧ forceL = massL + accelL ∧ forceL = (-1, -1, 1) ∧
    momL = massL + speedL ∧ momL = flagL - spaceL ∧
    actionL = energyL + timeL ∧ actionL = flagL ∧
    powerL = energyL - timeL ∧ powerL = (0, -2, 1) ∧
    pressureL = forceL - (2 : ℤ) • spaceL ∧ pressureL = (-3, -1, 1) ∧
    gravL = forceL + (2 : ℤ) • spaceL - (2 : ℤ) • massL ∧ gravL = (5, -3, -1) ∧
    gravL = flagL + speedL - (2 : ℤ) • massL := by
  decide

/-- 10:F2 — the geometric conversions are flag-free: `[Għ/c³] = [L]²`, `[Gm/c²] = [L]`, `[Gm/c³] = [T]`,
`[Gρ_m] = [T]⁻²`, `[Gρ_E/c⁴] = [L]⁻²` (the curvature domain), and the Compton closure `[mc/ħ] = [L]⁻¹`. -/
theorem geometric_conversions :
    gravL + flagL - (3 : ℤ) • speedL = (2, 0, 0) ∧
    gravL + massL - (2 : ℤ) • speedL = (1, 0, 0) ∧
    gravL + massL - (3 : ℤ) • speedL = (0, 1, 0) ∧
    gravL + (massL - (3 : ℤ) • spaceL) = (0, -2, 0) ∧
    gravL - (4 : ℤ) • speedL + (energyL - (3 : ℤ) • spaceL) = (-2, 0, 0) ∧
    massL + speedL - flagL = (-1, 0, 0) := by
  decide

/-- 10:F3 — temperature carries the acceleration domain: with `[k_B] = [p_P t_P] = I_q[L]⁻¹[T]`,
`[Θ] = [E][k_B]⁻¹ = [L][T]⁻² = [a]`, flag-free; and the Unruh combination `[ħ a / (c k_B)] = [Θ]` closes
flag-free. -/
theorem temperature_domain :
    thetaL = energyL - kBL ∧ thetaL = accelL ∧ thetaL.2.2 = 0 ∧
    flagL + accelL - speedL - kBL = thetaL := by
  decide

/-- 10:E3 — the flag positions of the quartet `(ℓ_P, t_P, p_P, E_P)` are `(0, 0, 1, 1)` — the dual horizons
`p_P = ħ/ℓ_P`, `E_P = ħ/t_P` are the crossed images `[p] = I_q[L]⁻¹`, `[E] = I_q[T]⁻¹` — and every quartet
relation closes on the flag component: `ħ = ℓ_P p_P` at `0 + 1 = 1`, `c = ℓ_P/t_P` at `0`, `c = E_P/p_P` at
`1 − 1 = 0`, `|k_B| = p_P t_P` at `1`, `G = ℓ_P² c³/ħ` at `−1` (the inverse flag, `[G]`). -/
theorem quartet_flags :
    spaceL.2.2 = 0 ∧ timeL.2.2 = 0 ∧ momL.2.2 = 1 ∧ energyL.2.2 = 1 ∧
    spaceL + momL = flagL ∧ (spaceL - timeL).2.2 = 0 ∧ (energyL - momL).2.2 = 0 ∧
    momL + timeL = kBL ∧ (2 : ℤ) • spaceL + (3 : ℤ) • (spaceL - timeL) - (spaceL + momL) = gravL ∧
    gravL.2.2 = -1 := by
  decide

/-- 10:F4 — count-valued comparisons are flag-free: the ratio of two labels of equal crossing degree has
crossing degree zero — the flag enters unitful measures only. -/
theorem equal_crossing_flag_free (x y : Lab) (h : x.2.2 = y.2.2) : (x - y).2.2 = 0 := by
  simp [h]

/-- 10:F4, 10:G3 — the examples: the phase exponent `[E][T]/[ħ]` neutral; the gravitational frequency
`[Gm/r³] = [T]⁻²` flag-free; and the scope witness — `F/a = [m]` has crossing degree `1` (the degrees `1`
and `0` are not equal), so the equal-crossing-degree hypothesis cannot be dropped. -/
theorem comparison_examples :
    energyL + timeL - flagL = 0 ∧ gravL + massL - (3 : ℤ) • spaceL = (0, -2, 0) ∧
    (gravL + massL - (3 : ℤ) • spaceL).2.2 = 0 ∧
    forceL - accelL = massL ∧ (forceL - accelL).2.2 = 1 ∧ forceL.2.2 ≠ accelL.2.2 := by
  decide

end labels

/-! ## Local recovery, the window ladder, the examples and Buckingham's count (10:G1–G4) -/
section recovery

/-- 10:G1 — local recovery of classical exponent bookkeeping: for `4κ > 2H`, two conventional pairs
`(r, s)`, `(r', s')` with `|r|, |r'|, |s|, |s'| ≤ H` and the same modular label are equal. -/
theorem local_recovery (κ H : ℕ) (hH : 2 * H < 4 * κ) (r r' s s' : ℤ) (hr : |r| ≤ H) (hr' : |r'| ≤ H)
    (hs : |s| ≤ H) (hs' : |s'| ≤ H)
    (h : ((r : ZMod (4 * κ + 1)), (s : ZMod (4 * κ))) = ((r' : ZMod (4 * κ + 1)), (s' : ZMod (4 * κ)))) :
    r = r' ∧ s = s' := by
  obtain ⟨h1, h2⟩ := Prod.ext_iff.mp h
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h1 h2
  have hb := abs_le.mp hr; have hb' := abs_le.mp hr'
  have hc := abs_le.mp hs; have hc' := abs_le.mp hs'
  have e1 := Int.eq_zero_of_abs_lt_dvd h1 (abs_lt.mpr ⟨by push_cast; omega, by push_cast; omega⟩)
  have e2 := Int.eq_zero_of_abs_lt_dvd h2 (abs_lt.mpr ⟨by push_cast; omega, by push_cast; omega⟩)
  omega

/-- 10:G1 — the crossing embedding of classical `M`-`L`-`T` bookkeeping, `M^u L^a T^b ↦ (a − 2u, b + u; u)`. -/
def embed (u a b : ℤ) : Lab := (a - 2 * u, b + u, u)

/-- 10:G1, 10:G4 — the embedding is injective on `Z³` (triangular with unit diagonal): the crossing degree
carries the mass exponent exactly; the map being linear by its formula, the lifted label matrix of quantities
with classical `M`-`L`-`T` dimensions has the kernel, hence the rank, of the classical one (G4). -/
theorem embed_injective (u a b u' a' b' : ℤ) (h : embed u a b = embed u' a' b') :
    u = u' ∧ a = a' ∧ b = b' := by
  simp only [embed, Prod.ext_iff] at h
  omega

/-- 10:G1 — windowed faithfulness of the realization: on `|r|, |s| ≤ H` with `2H < κ` and `|j| ≤ 1`, two
full labels with the same realization `(r, s + jκ)` are equal — `r` from the meridian factor, and
`(j − j')κ ≡ s' − s (mod 4κ)` with `|j − j'| ≤ 2`, `|s − s'| < κ` forces `j = j'` and then `s = s'`;
beyond the window the sector saturates, `4 • I_q = 0`. -/
theorem realize_faithful (κ H : ℕ) [NeZero κ] (hH : 2 * H < κ) (r r' s s' j j' : ℤ)
    (hr : |r| ≤ H) (hr' : |r'| ≤ H) (hs : |s| ≤ H) (hs' : |s'| ≤ H) (hj : |j| ≤ 1) (hj' : |j'| ≤ 1)
    (h : realize κ (r, s, j) = realize κ (r', s', j')) : r = r' ∧ s = s' ∧ j = j' := by
  obtain ⟨h1, h2⟩ := Prod.ext_iff.mp h
  simp only [realize, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h1 h2
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h1 h2
  have hb := abs_le.mp hr; have hb' := abs_le.mp hr'
  have hc := abs_le.mp hs; have hc' := abs_le.mp hs'
  have hd := abs_le.mp hj; have hd' := abs_le.mp hj'
  have hκ : (0 : ℤ) < κ := by exact_mod_cast NeZero.pos κ
  have e1 := Int.eq_zero_of_abs_lt_dvd h1 (abs_lt.mpr ⟨by push_cast; omega, by push_cast; omega⟩)
  obtain ⟨m, hm⟩ := h2
  push_cast at hm
  -- `(s' − s) + (j' − j)κ = 4κ m` with `|s' − s| < κ` and `|j' − j| ≤ 2` forces `m = 0`
  have hm0 : m = 0 := by
    rcases lt_trichotomy m 0 with hlt | heq | hgt
    · exfalso
      have : (4 : ℤ) * κ * m ≤ -4 * κ := by nlinarith
      nlinarith
    · exact heq
    · exfalso
      have : (4 : ℤ) * κ ≤ 4 * κ * m := by nlinarith
      nlinarith
  subst hm0
  -- now `(j' − j)κ = s − s'` with `|s − s'| < κ`, so `j = j'`
  have hjj : j' - j = 0 := by
    rcases lt_trichotomy (j' - j) 0 with hlt | heq | hgt
    · exfalso
      have : (j' - j) * κ ≤ -κ := by nlinarith
      nlinarith
    · exact heq
    · exfalso
      have : (κ : ℤ) ≤ (j' - j) * κ := by nlinarith
      nlinarith
  refine ⟨by omega, ?_, by omega⟩
  have : (j' - j) * κ = 0 := by rw [hjj]; ring
  nlinarith

/-- 10:G2 — the window ladder `2√κ < κ/2 < κ < 2κ`, by integer squares: `16κ < κ²` iff `κ > 16`, and
`κ/2 < κ < 2κ` for `κ > 0` — nested for every `κ ≥ 17`, failing for the toy `κ = 3`; the coherence identity
`(2√κ)² = 4κ = p − 1` and the totality closure `(2√S)² = 4S = Ω − 1`. -/
theorem window_ladder (κ S : ℕ) :
    (16 * κ < κ ^ 2 ↔ 16 < κ) ∧ (0 < κ → κ / 2 < κ ∧ κ < 2 * κ) ∧ ¬ (16 * 3 < 3 ^ 2) ∧
    (2 * 2 * κ = 4 * κ ∧ 4 * κ = (4 * κ + 1) - 1) ∧ 4 * S = (4 * S + 1) - 1 := by
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun h => ⟨by omega, by omega⟩, by norm_num, ⟨by ring, by omega⟩,
    by omega⟩
  · by_contra hc; have hc' : κ ≤ 16 := Nat.le_of_not_lt hc; nlinarith
  · nlinarith

instance fact13 : Fact (Nat.Prime (4 * 3 + 1)) := ⟨by norm_num⟩

/-- 10:G3 — the worked examples on the shell of capacity `κ = 3` (`p = 13`, phase cycle `12`): `12 > 10 = 2H`
at `H = 5`; kinetic energy `[m][v]² = [E]`; `Q + Q²` inhomogeneous (`[L] ≠ [L]²`); the phase exponent
neutral; flag arithmetic — `Għ/c³` flag-free, `I_q² = [T]^π = (0, 6)`; the Schwarzschild length
`[Gm/c²] = [L]`; the gravitational frequency `[Gm/r³] = [T]⁻²`; the realized mass `(11, 4) = (−2, 1 + κ)`. -/
theorem examples13 :
    12 > 2 * 5 ∧ massL + (2 : ℤ) • speedL = energyL ∧ L 3 ≠ 2 • L 3 ∧
    energyL + timeL - flagL = 0 ∧ (gravL + flagL - (3 : ℤ) • speedL).2.2 = 0 ∧
    2 • flag 3 = ((0 : ZMod 13), (6 : ZMod 12)) ∧
    gravL + massL - (2 : ℤ) • speedL = (1, 0, 0) ∧ gravL + massL - (3 : ℤ) • spaceL = (0, -2, 0) ∧
    realize 3 massL = ((11 : ZMod 13), (4 : ZMod 12)) := by
  refine ⟨by norm_num, by decide, by decide, by decide, by decide, ?_, by decide, by decide, ?_⟩
  · rw [two_smul_flag]; decide
  · ext <;> simp [realize, massL] <;> decide

/-- 10:G3 — local recovery on `κ = 3` at `H = 5`: the instance of the theorem. -/
theorem recovery13 (r r' s s' : ℤ) (hr : |r| ≤ 5) (hr' : |r'| ≤ 5) (hs : |s| ≤ 5) (hs' : |s'| ≤ 5)
    (h : ((r : ZMod 13), (s : ZMod 12)) = ((r' : ZMod 13), (s' : ZMod 12))) : r = r' ∧ s = s' :=
  local_recovery 3 5 (by norm_num) r r' s s' hr hr' hs hs' h

/-- 10:G3 — the energy–momentum relation `E² = p²c² + m²c⁴` is homogeneous on the lift: the three labels
`[E]²`, `[p]²[c]²`, `[m]²[c]⁴` coincide, `(0, −2; 2)`, one fibre at crossing degree two; its massless case
`E = pc` at crossing degree one, and `E = mc²` on the energy fibre; realized on `κ = 3`, `[E]² = (0, 4)`,
the lifted and the shell computation agreeing. -/
theorem energy_momentum :
    (2 : ℤ) • energyL = (2 : ℤ) • (momL + speedL) ∧ (2 : ℤ) • energyL = (2 : ℤ) • (massL + (2 : ℤ) • speedL) ∧
    (2 : ℤ) • energyL = (0, -2, 2) ∧ ((2 : ℤ) • energyL).2.2 = 2 ∧
    energyL = momL + speedL ∧ energyL.2.2 = 1 ∧ energyL = massL + (2 : ℤ) • speedL ∧
    realize 3 ((2 : ℤ) • energyL) = ((0 : ZMod 13), (4 : ZMod 12)) ∧
    2 • energy 3 = ((0 : ZMod 13), (4 : ZMod 12)) := by
  decide

/-- 10:G4 — the window coincidence: on `|r|, |s| ≤ H` with `2H < κ` and `|j| ≤ 1`, a lifted label realizes to
the neutral label iff it is `(0, 0; 0)` — lifted and realized neutrality coincide on the window (the
instance of `realize_faithful` against the neutral label). -/
theorem window_neutrality (κ H : ℕ) [NeZero κ] (hH : 2 * H < κ) (r s j : ℤ)
    (hr : |r| ≤ H) (hs : |s| ≤ H) (hj : |j| ≤ 1) :
    realize κ (r, s, j) = 0 ↔ (r, s, j) = (0, 0, 0) := by
  constructor
  · intro h
    obtain ⟨h1, h2, h3⟩ := realize_faithful κ H hH r 0 s 0 j 0 hr (by simp) hs (by simp) hj (by simp)
      (by rw [h]; exact (map_zero _).symm)
    rw [h1, h2, h3]
  · rintro ⟨⟩; exact map_zero _

/-- 10:G4 — Buckingham's count on the pendulum `(T, ℓ, g, m)`: the classical dimensions lie in `M`-`L`-`T`
and embed to the lifted labels `[T] = (0, 1; 0)`, `[ℓ] = (1, 0; 0)`, `[g] = (1, −2; 0)`, `[m] = (−2, 1; 1)`;
a monomial `T^{k₁} ℓ^{k₂} g^{k₃} m^{k₄}` is neutral on the lift iff `(k₁, k₂, k₃, k₄) = t·(2, −1, 1, 0)` —
the kernel of the `4 × 3` label matrix is the line of `T²g/ℓ`, one dimensionless product, so the rank is
`3 = 4 − 1` (the mass, alone in carrying crossing degree, enters no neutral product, `k₄ = 0`); the minor
of the label matrix on the rows `(ℓ, g, m)` is `−2 ≠ 0`. -/
theorem pendulum_kernel :
    embed 0 0 1 = timeL ∧ embed 0 1 0 = spaceL ∧ embed 0 1 (-2) = accelL ∧ embed 1 0 0 = massL ∧
    (∀ k₁ k₂ k₃ k₄ : ℤ, k₁ • timeL + k₂ • spaceL + k₃ • accelL + k₄ • massL = 0 ↔
      ∃ t : ℤ, k₁ = 2 * t ∧ k₂ = -t ∧ k₃ = t ∧ k₄ = 0) ∧
    (2 : ℤ) • timeL - spaceL + accelL = 0 ∧
    Matrix.det !![spaceL.1, spaceL.2.1, spaceL.2.2; accelL.1, accelL.2.1, accelL.2.2;
      massL.1, massL.2.1, massL.2.2] = -2 := by
  refine ⟨by decide, by decide, by decide, by decide, fun k₁ k₂ k₃ k₄ => ?_, by decide, ?_⟩
  · simp only [timeL, spaceL, accelL, massL, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk, Prod.mk_eq_zero]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨k₃, by omega, by omega, rfl, by omega⟩
    · rintro ⟨t, rfl, rfl, rfl, rfl⟩; omega
  · rw [Matrix.det_fin_three]; simp [spaceL, accelL, massL]

end recovery

-- Ledger rows of 10-dimensions (generated by make_rows.py from docs/10-dimensions/10-dimensions-ledger.json; edit the ledger, not this section)
/-- 10:C2 — The modular unit-domain group and the grading: $\{U_{r,s}\}$ is a finite abelian group isomorphic to $\Dp$ under $U_{r,s}U_{r',s'}=U_{r+r',s+s'}$, and $\Ap$ is $\Dp$-graded, $\Ap^{(r,s)}\Ap^{(r',s')}\subseteq\Ap^{(r+r',s+s')}$. -/
theorem row_C2 : (∀ (κ : ℕ) (a b : FRC.Dimensions.Dom κ), FRC.Dimensions.U κ a * FRC.Dimensions.U κ b = FRC.Dimensions.U κ (a + b)) ∧ (∀ (κ : ℕ) [NeZero κ], Function.Injective ⇑(FRC.Dimensions.Uhom κ)) ∧ ∀ (κ : ℕ) {x y : FRC.Dimensions.QA κ} {a b : FRC.Dimensions.Dom κ}, x ∈ AddMonoidAlgebra.grade (ZMod ((4 : ℕ) * κ + (1 : ℕ))) a → y ∈ AddMonoidAlgebra.grade (ZMod ((4 : ℕ) * κ + (1 : ℕ))) b → x * y ∈ AddMonoidAlgebra.grade (ZMod ((4 : ℕ) * κ + (1 : ℕ))) (a + b) :=
  And.intro @FRC.Dimensions.U_mul (And.intro @FRC.Dimensions.Uhom_injective (@FRC.Dimensions.graded))
/-- 10:C3 — Fibrewise addition and the neutral-domain criterion: a sum of homogeneous quantities is homogeneous exactly when its nonzero summands share a domain, the fibre components adding separately; a monomial $\prod Q_j^{k_j}$ has domain $\sum k_j(r_j,s_j)$ and is a neutral-domain invariant iff that sum is $(0,0)$ in $\Dp$. -/
theorem row_C3 : (∀ (κ : ℕ) (a : FRC.Dimensions.Dom κ) (q q' : ZMod ((4 : ℕ) * κ + (1 : ℕ))), AddMonoidAlgebra.single a q + AddMonoidAlgebra.single a q' = AddMonoidAlgebra.single a (q + q')) ∧ (∀ (κ : ℕ) {ι : Type u_1} (s : Finset ι) (m : ι → FRC.Dimensions.Dom κ) (q : ι → ZMod ((4 : ℕ) * κ + (1 : ℕ))) (a : FRC.Dimensions.Dom κ), (∑ j ∈ s, AddMonoidAlgebra.single (m j) (q j)).coeff a = ∑ j ∈ s with m j = a, q j) ∧ (∀ (κ : ℕ) {ι : Type u_2} (s : Finset ι) (m : ι → FRC.Dimensions.Dom κ) (k : ι → ℤ), ∏ j ∈ s, (FRC.Dimensions.Uhom κ) (Multiplicative.ofAdd (m j)) ^ k j = (FRC.Dimensions.Uhom κ) (Multiplicative.ofAdd (∑ j ∈ s, k j • m j))) ∧ ∀ (κ : ℕ) (a b : FRC.Dimensions.Dom κ) {c : ZMod ((4 : ℕ) * κ + (1 : ℕ))}, c ≠ (0 : ZMod ((4 : ℕ) * κ + (1 : ℕ))) → (AddMonoidAlgebra.single a c ∈ AddMonoidAlgebra.grade (ZMod ((4 : ℕ) * κ + (1 : ℕ))) b ↔ a = b) :=
  And.intro @FRC.Dimensions.fibre_add (And.intro @FRC.Dimensions.coeff_sum_single (And.intro @FRC.Dimensions.monomial_units (@FRC.Dimensions.single_mem_grade_iff)))
set_option linter.defProp false in
/-- 10:C5 — Window covariance: on a bounded window $|r|,|s|\le H<2\kap$ in the flag-free sector the labels are covariant under every admissible reframing; the bound is sharp (the label $(0,\pi)$ is pushforward-invariant yet non-neutral); the naive character is ill-defined on the modular projection and the would-be temporal character fails composition ($5^{2}\equiv1$ in $\Z_{12}^{\times}$); on the realized lattice the invariant labels are exactly $\{0,2\kap\}$; the $\sigma$-twisted action is equivariant by full sweep on $\p=13$ and $229$; the flagged label $(0,0;1)$ moves under $\eps=-1$. -/
def row_C5 := And.intro @FRC.Dimensions.dilation_character (And.intro @FRC.Dimensions.invariant_iff (And.intro @FRC.Dimensions.quarter_turn_law (And.intro @FRC.Dimensions.sigma_twist (And.intro @FRC.Dimensions.half_period_invariant_not_neutral (And.intro @FRC.Dimensions.flag_moves (@FRC.Dimensions.witnesses13))))))
/-- 10:C6 — What the action forces and what is declared: the time-exponent period $\p-1$ is forced by the pushforward action of $\Zp^{\times}$, the space-exponent refinement to period $\p$ is declared and carried by the transport theorem (D2); classical temporal unit change is nominal re-assignment within a fixed presentation, the chronon atomic. -/
theorem row_C6 : ∀ (κ : ℕ), ((4 : ℕ) * κ + (1 : ℕ)) • (FRC.Dimensions.L κ + κ • FRC.Dimensions.T κ) = FRC.Dimensions.flag κ :=
  @FRC.Dimensions.meridian_transport
/-- 10:D1 — Chart duality: $[f]=\unitT^{-1}$; $\delta_S:D\mapsto D^{-1}$ is an involution of the domain group whose orbit on the generators is the four-domain structure (space, momentum, time, energy); $\delta_C$ the second involution, carrying $\unitL\mapsto[p]$, $\unitT\mapsto\unitE$. -/
theorem row_D1 : (∀ (κ : ℕ) (a : FRC.Dimensions.Dom κ), (FRC.Dimensions.deltaS κ) ((FRC.Dimensions.deltaS κ) a) = a) ∧ (∀ (κ : ℕ) [NeZero κ], FRC.Dimensions.L κ ≠ -FRC.Dimensions.L κ ∧ FRC.Dimensions.T κ ≠ -FRC.Dimensions.T κ ∧ FRC.Dimensions.L κ ≠ FRC.Dimensions.T κ ∧ FRC.Dimensions.L κ ≠ -FRC.Dimensions.T κ ∧ -FRC.Dimensions.L κ ≠ FRC.Dimensions.T κ ∧ -FRC.Dimensions.L κ ≠ -FRC.Dimensions.T κ) ∧ (∀ (κ : ℕ) (a : FRC.Dimensions.Dom κ), FRC.Dimensions.deltaC κ (FRC.Dimensions.deltaC κ a) = a) ∧ ∀ (κ : ℕ), FRC.Dimensions.deltaC κ (FRC.Dimensions.L κ) = FRC.Dimensions.mom κ ∧ FRC.Dimensions.deltaC κ (FRC.Dimensions.T κ) = FRC.Dimensions.energy κ :=
  And.intro @FRC.Dimensions.deltaS_involutive (And.intro @FRC.Dimensions.four_domains (And.intro @FRC.Dimensions.deltaC_involutive (@FRC.Dimensions.deltaC_generators)))
set_option linter.defProp false in
/-- 10:D2 — The internal flag: $\Dp$ contains exactly one subgroup of order four, $\langle\unitT^{\kap}\rangle$, entirely in the time-exponent factor; $\Iq:=\unitT^{\kap}$, $\Iq^{4}=1$, $\Iq^{2}=\unitT^{\pi}$; no flag of space ($\Z_\p$ has no element of order four); the two periods interfere, $(\unitL\unitT^{\kap})^{\p}=\Iq$, on three shells. -/
def row_D2 := And.intro @FRC.Dimensions.order_four_iff (And.intro @FRC.Dimensions.unique_order_four_subgroup (And.intro @FRC.Dimensions.no_flag_of_space (And.intro @FRC.Dimensions.order_two_iff (And.intro @FRC.Dimensions.meridian_transport (@FRC.Dimensions.quarter_turn_law)))))
set_option linter.defProp false in
/-- 10:D3 — The lift: the flag records the quarter the chart duality forgets --- on charts the cardinal skeleton acts as $s\bmod2$ ($F$ exchanges the conjugate charts, $J$ fixes them), on labels $s\mapsto\Iq^{s}$ is an isomorphism $\Z_4\to\langle\Iq\rangle$ whose quotient by $\{0,2\kap\}$ returns the chart action; on the Carrier $\hbar^{2}=-1$, $\hbar^{4}=1$, $\hbar^{2}\ne1$, the crossing quantum of order four, never two. Shells $(13,2)$, $(173,3)$; Carriers $233$, $2\,408\,561$. -/
def row_D3 := And.intro @FRC.Dimensions.operator_four_cycle (And.intro @FRC.Dimensions.record_injective (And.intro @FRC.Dimensions.record_range (And.intro @FRC.Dimensions.record_mem_parity_iff (@FRC.Dimensions.crossing_order_four))))
/-- 10:D6 — The flagged readings over the counts: $\unitE=[h][f]=\Iq\unitT^{-1}$, $[p]=\unithbar[k]=\Iq\unitL^{-1}$, one quantity per pair, the flagged reading one capacity step above its count; $[S]=\unitE\unitT=\Iq$ and every phase count neutral, $\unitE\unitT\unithbar^{-1}=1$; the absolute unit is horizon-inaccessible (no monomial of a window $H\ll\kap$ expresses the flag) and becomes visible at $\kap\le H<2\kap$. -/
theorem row_D6 : And (∀ (κ : Nat), And (@Eq (FRC.Dimensions.Dom κ) (FRC.Dimensions.energy κ) (@Prod.mk (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@OfNat.ofNat (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (nat_lit 0) (@Zero.toOfNat0 (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@MulZeroClass.toZero (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@instMulZeroClassOfSemiring (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@CommSemiring.toSemiring (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@CommRing.toCommSemiring (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (ZMod.commRing (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))))) (@HSub.hSub (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@instHSub (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@SubNegMonoid.toSub (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@AddGroup.toSubNegMonoid (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@AddGroupWithOne.toAddGroup (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@Ring.toAddGroupWithOne (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@CommRing.toRing (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (ZMod.commRing (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)))))))) (@Nat.cast (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@AddMonoidWithOne.toNatCast (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@AddGroupWithOne.toAddMonoidWithOne (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@Ring.toAddGroupWithOne (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@CommRing.toRing (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (ZMod.commRing (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)))))) κ) (@OfNat.ofNat (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (nat_lit 1) (@One.toOfNat1 (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@AddMonoidWithOne.toOne (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@AddGroupWithOne.toAddMonoidWithOne (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@Ring.toAddGroupWithOne (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@CommRing.toRing (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (ZMod.commRing (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ))))))))))) (And (@Eq (FRC.Dimensions.Dom κ) (FRC.Dimensions.mom κ) (@Prod.mk (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@Neg.neg (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@NegZeroClass.toNeg (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@SubNegZeroMonoid.toNegZeroClass (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@SubtractionMonoid.toSubNegZeroMonoid (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@SubtractionCommMonoid.toSubtractionMonoid (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@AddCommGroup.toDivisionAddCommMonoid (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@Ring.toAddCommGroup (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@CommRing.toRing (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (ZMod.commRing (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))))) (@OfNat.ofNat (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (nat_lit 1) (@One.toOfNat1 (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@AddMonoidWithOne.toOne (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@AddGroupWithOne.toAddMonoidWithOne (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@Ring.toAddGroupWithOne (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@CommRing.toRing (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (ZMod.commRing (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))))) (@Nat.cast (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@AddMonoidWithOne.toNatCast (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@AddGroupWithOne.toAddMonoidWithOne (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@Ring.toAddGroupWithOne (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@CommRing.toRing (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (ZMod.commRing (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)))))) κ))) (And (@Eq (FRC.Dimensions.Dom κ) (@HAdd.hAdd (FRC.Dimensions.Dom κ) (FRC.Dimensions.Dom κ) (FRC.Dimensions.Dom κ) (@instHAdd (FRC.Dimensions.Dom κ) (@Prod.instAdd (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@Distrib.toAdd (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@instDistribOfSemiring (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@CommSemiring.toSemiring (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@CommRing.toCommSemiring (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (ZMod.commRing (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))) (@Distrib.toAdd (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@instDistribOfSemiring (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@CommSemiring.toSemiring (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@CommRing.toCommSemiring (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (ZMod.commRing (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)))))))) (FRC.Dimensions.energy κ) (FRC.Dimensions.T κ)) (FRC.Dimensions.flag κ)) (And (@Eq (FRC.Dimensions.Dom κ) (@HSub.hSub (FRC.Dimensions.Dom κ) (FRC.Dimensions.Dom κ) (FRC.Dimensions.Dom κ) (@instHSub (FRC.Dimensions.Dom κ) (@Prod.instSub (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@SubNegMonoid.toSub (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@AddGroup.toSubNegMonoid (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@AddGroupWithOne.toAddGroup (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@Ring.toAddGroupWithOne (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@CommRing.toRing (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (ZMod.commRing (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))) (@SubNegMonoid.toSub (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@AddGroup.toSubNegMonoid (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@AddGroupWithOne.toAddGroup (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@Ring.toAddGroupWithOne (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@CommRing.toRing (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (ZMod.commRing (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ))))))))) (@HAdd.hAdd (FRC.Dimensions.Dom κ) (FRC.Dimensions.Dom κ) (FRC.Dimensions.Dom κ) (@instHAdd (FRC.Dimensions.Dom κ) (@Prod.instAdd (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@Distrib.toAdd (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@instDistribOfSemiring (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@CommSemiring.toSemiring (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@CommRing.toCommSemiring (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (ZMod.commRing (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))) (@Distrib.toAdd (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@instDistribOfSemiring (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@CommSemiring.toSemiring (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@CommRing.toCommSemiring (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (ZMod.commRing (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)))))))) (FRC.Dimensions.energy κ) (FRC.Dimensions.T κ)) (FRC.Dimensions.flag κ)) (@OfNat.ofNat (FRC.Dimensions.Dom κ) (nat_lit 0) (@Zero.toOfNat0 (FRC.Dimensions.Dom κ) (@Prod.instZero (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@MulZeroClass.toZero (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@instMulZeroClassOfSemiring (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@CommSemiring.toSemiring (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@CommRing.toCommSemiring (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (ZMod.commRing (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))) (@MulZeroClass.toZero (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@instMulZeroClassOfSemiring (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@CommSemiring.toSemiring (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@CommRing.toCommSemiring (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (ZMod.commRing (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)))))))))) (@Eq (FRC.Dimensions.Dom κ) (@HSub.hSub (FRC.Dimensions.Dom κ) (FRC.Dimensions.Dom κ) (FRC.Dimensions.Dom κ) (@instHSub (FRC.Dimensions.Dom κ) (@Prod.instSub (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@SubNegMonoid.toSub (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@AddGroup.toSubNegMonoid (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@AddGroupWithOne.toAddGroup (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@Ring.toAddGroupWithOne (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@CommRing.toRing (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (ZMod.commRing (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))) (@SubNegMonoid.toSub (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@AddGroup.toSubNegMonoid (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@AddGroupWithOne.toAddGroup (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@Ring.toAddGroupWithOne (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@CommRing.toRing (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (ZMod.commRing (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ))))))))) (@HAdd.hAdd (FRC.Dimensions.Dom κ) (FRC.Dimensions.Dom κ) (FRC.Dimensions.Dom κ) (@instHAdd (FRC.Dimensions.Dom κ) (@Prod.instAdd (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@Distrib.toAdd (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@instDistribOfSemiring (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@CommSemiring.toSemiring (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@CommRing.toCommSemiring (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (ZMod.commRing (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))) (@Distrib.toAdd (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@instDistribOfSemiring (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@CommSemiring.toSemiring (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@CommRing.toCommSemiring (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (ZMod.commRing (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)))))))) (FRC.Dimensions.mom κ) (FRC.Dimensions.L κ)) (FRC.Dimensions.flag κ)) (@OfNat.ofNat (FRC.Dimensions.Dom κ) (nat_lit 0) (@Zero.toOfNat0 (FRC.Dimensions.Dom κ) (@Prod.instZero (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@MulZeroClass.toZero (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@instMulZeroClassOfSemiring (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@CommSemiring.toSemiring (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@CommRing.toCommSemiring (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (ZMod.commRing (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))) (@MulZeroClass.toZero (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@instMulZeroClassOfSemiring (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@CommSemiring.toSemiring (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@CommRing.toCommSemiring (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (ZMod.commRing (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)))))))))))))) (∀ (κ H : Nat), @LT.lt Nat instLTNat H κ → ∀ (r s : Int), @LE.le Int Int.instLEInt (@abs Int instLatticeInt Int.instAddGroup s) (@Nat.cast Int instNatCastInt H) → And (@Ne (Prod (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ))) (@Prod.mk (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@Int.cast (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@AddGroupWithOne.toIntCast (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@Ring.toAddGroupWithOne (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@CommRing.toRing (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (ZMod.commRing (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))) r) (@Int.cast (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@AddGroupWithOne.toIntCast (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@Ring.toAddGroupWithOne (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@CommRing.toRing (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (ZMod.commRing (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ))))) s)) (FRC.Dimensions.flag κ)) (@Eq (Prod (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ))) (@Prod.mk (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@OfNat.ofNat (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (nat_lit 0) (@Zero.toOfNat0 (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@MulZeroClass.toZero (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@instMulZeroClassOfSemiring (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@CommSemiring.toSemiring (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@CommRing.toCommSemiring (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (ZMod.commRing (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))))) (@Int.cast (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@AddGroupWithOne.toIntCast (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@Ring.toAddGroupWithOne (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@CommRing.toRing (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (ZMod.commRing (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ))))) (@Nat.cast Int instNatCastInt κ))) (FRC.Dimensions.flag κ))) :=
  And.intro @FRC.Dimensions.flagged_readings (@FRC.Dimensions.flag_inaccessible)
/-- 10:E2 — One crossing, one action, and pairing closure: $\lP\pP=\tPl\EP=\hbar$ (the two faces of $c$ and $\hbar$ differ by the single relation $\ell p=tE$); the cross-domain relations reduce to the two generators $c$, $\hbar$, the mixed products their monomials, $|k_B|=\hbar/c$ derived; the relation lattice over $\{\lP,\tPl,\hbar\}$ has rank two and $k_B$, $\lP\EP$ add nothing; $4-1=3$ free scales in bijection with $\{c,\hbar,G\}$, the classical arity derived. -/
theorem row_E2 : (∀ {K : Type u_1} [Field K] (l t hbar : K), l ≠ (0 : K) → t ≠ (0 : K) → l * (hbar / l) = hbar ∧ t * (hbar / t) = hbar) ∧ (∀ {K : Type u_2} [Field K] (l t p E : K), l ≠ (0 : K) → t ≠ (0 : K) → (l * p = t * E ↔ p = l * p / l ∧ E = l * p / t)) ∧ (∀ {K : Type u_3} [Field K] (l t p E : K), l ≠ (0 : K) → t ≠ (0 : K) → p ≠ (0 : K) → l * p = t * E → l / t = E / p ∧ p * t = l * p / (l / t) ∧ l * E = l * p * (l / t)) ∧ (∀ {K : Type u_4} [Field K] (l t p E : K), l ≠ (0 : K) → t ≠ (0 : K) → p ≠ (0 : K) → l * p = t * E → l * p * (l / t) / (p / (l / t)) ^ (2 : ℕ) = l ^ (2 : ℕ) * (l / t) ^ (3 : ℕ) / (l * p) ∧ l ^ (2 : ℕ) = l * p * (l / t) / (p / (l / t)) ^ (2 : ℕ) * (l * p) / (l / t) ^ (3 : ℕ) ∧ t = l / (l / t) ∧ p = l * p / l ∧ E = l * p * (l / t) / l) ∧ !![(1 : ℤ), (-1 : ℤ), (0 : ℤ); (0 : ℤ), (0 : ℤ), (1 : ℤ); (5 : ℤ), (-3 : ℤ), (-1 : ℤ)].det = (-2 : ℤ) ∧ (∀ (c hbar G : ℝ), (0 : ℝ) < c → (0 : ℝ) < hbar → (0 : ℝ) < G → ∃! l, (0 : ℝ) < l ∧ l ^ (2 : ℕ) = G * hbar / c ^ (3 : ℕ)) ∧ ![(1 : ℤ), (-1 : ℤ), (0 : ℤ), (0 : ℤ)] - ![(0 : ℤ), (0 : ℤ), (-1 : ℤ), (1 : ℤ)] = ![(1 : ℤ), (-1 : ℤ), (1 : ℤ), (-1 : ℤ)] ∧ ![(1 : ℤ), (0 : ℤ), (1 : ℤ), (0 : ℤ)] - ![(0 : ℤ), (1 : ℤ), (0 : ℤ), (1 : ℤ)] = ![(1 : ℤ), (-1 : ℤ), (1 : ℤ), (-1 : ℤ)] ∧ ![(1 : ℤ), (0 : ℤ), (0 : ℤ), (1 : ℤ)] = ![(0 : ℤ), (1 : ℤ), (0 : ℤ), (1 : ℤ)] + ![(1 : ℤ), (-1 : ℤ), (0 : ℤ), (0 : ℤ)] ∧ ![(0 : ℤ), (1 : ℤ), (1 : ℤ), (0 : ℤ)] = ![(0 : ℤ), (1 : ℤ), (0 : ℤ), (1 : ℤ)] - ![(0 : ℤ), (0 : ℤ), (-1 : ℤ), (1 : ℤ)] :=
  And.intro @FRC.Dimensions.action_identity (And.intro @FRC.Dimensions.quartet_param (And.intro @FRC.Dimensions.pairing_closure (And.intro @FRC.Dimensions.normalisation (And.intro @FRC.Dimensions.index_two (And.intro @FRC.Dimensions.scale_from_constants (@FRC.Dimensions.exponent_faces))))))
/-- 10:E3 — The cancellation identity $|k_B|c=\hbar$ at the unit face, $(\pP\tPl)(\lP/\tPl)=\lP\pP$; mass derived, $m_P=\pP/c=\EP/c^{2}$; the temperature horizon $\Theta_P=\EP/|k_B|$; the flag positions $(0,0,1,1)$ and the closure of every quartet relation on the flag component; no $\hbar$ of space and time. -/
theorem row_E3 : (∀ {K : Type u_1} [Field K] (l t p E : K), l ≠ (0 : K) → t ≠ (0 : K) → p ≠ (0 : K) → l * p = t * E → p * t * (l / t) = l * p ∧ p / (l / t) = E / (l / t) ^ (2 : ℕ) ∧ E / (p * t) = E * (l / t) / (l * p)) ∧ FRC.Dimensions.spaceL.2.2 = (0 : ℤ) ∧ FRC.Dimensions.timeL.2.2 = (0 : ℤ) ∧ FRC.Dimensions.momL.2.2 = (1 : ℤ) ∧ FRC.Dimensions.energyL.2.2 = (1 : ℤ) ∧ FRC.Dimensions.spaceL + FRC.Dimensions.momL = FRC.Dimensions.flagL ∧ (FRC.Dimensions.spaceL - FRC.Dimensions.timeL).2.2 = (0 : ℤ) ∧ (FRC.Dimensions.energyL - FRC.Dimensions.momL).2.2 = (0 : ℤ) ∧ FRC.Dimensions.momL + FRC.Dimensions.timeL = FRC.Dimensions.kBL ∧ (2 : ℤ) • FRC.Dimensions.spaceL + (3 : ℤ) • (FRC.Dimensions.spaceL - FRC.Dimensions.timeL) - (FRC.Dimensions.spaceL + FRC.Dimensions.momL) = FRC.Dimensions.gravL ∧ FRC.Dimensions.gravL.2.2 = (-1 : ℤ) :=
  And.intro @FRC.Dimensions.cancellation (@FRC.Dimensions.quartet_flags)
/-- 10:E4 — The defining congruences, pair form: on the Carrier chart $2G+1\equiv0$, $2c^{2}\equiv1$, $\hbar^{2}\equiv-1$, $k_B^{2}\equiv-2\pmod\Om$ determine the constants uniquely at pair level --- $G=2\dS$ exact, the quadratics each with exactly two roots $\{x,-x\}$ (admissibility guarantees the residues: $\Om\equiv1\bmod4$, $\dS$ even for $2$, hence $-2$) --- and the linkage $\{\pm k_B\}\{\pm c\}=\{\pm\hbar\}$ is derived at pair level; the root pair of $-1$ is $\{\hbar,h\}$ with $h=2\pi\hbar\equiv-\hbar$. Exhaustive on both Carriers. -/
theorem row_E4 : (∀ {K : Type u_1} [Field K] (S : ℕ), ↑((4 : ℕ) * S + (1 : ℕ)) = (0 : K) → (2 : K) ≠ (0 : K) → ∀ (x : K), (2 : K) * x + (1 : K) = (0 : K) ↔ x = ↑((2 : ℕ) * S)) ∧ (∀ {K : Type u_2} [Field K] (a x : K), x ^ (2 : ℕ) = a → x ≠ (0 : K) → (2 : K) ≠ (0 : K) → (∀ (y : K), y ^ (2 : ℕ) = a ↔ y = x ∨ y = -x) ∧ -x ≠ x) ∧ (∀ {K : Type u_3} [Field K] (k c h : K), k ^ (2 : ℕ) = (-2 : K) → (2 : K) * c ^ (2 : ℕ) = (1 : K) → h ^ (2 : ℕ) = (-1 : K) → (k * c) ^ (2 : ℕ) = (-1 : K) ∧ (k * c = h ∨ k * c = -h)) ∧ (∀ (S : ℕ) [hΩ : Fact (Nat.Prime ((4 : ℕ) * S + (1 : ℕ)))], Even S → IsSquare (-1 : ZMod ((4 : ℕ) * S + (1 : ℕ))) ∧ IsSquare (2 : ZMod ((4 : ℕ) * S + (1 : ℕ))) ∧ IsSquare (2 : ZMod ((4 : ℕ) * S + (1 : ℕ)))⁻¹ ∧ IsSquare (-2 : ZMod ((4 : ℕ) * S + (1 : ℕ))) ∧ (2 : ZMod ((4 : ℕ) * S + (1 : ℕ))) * ↑((2 : ℕ) * S) + (1 : ZMod ((4 : ℕ) * S + (1 : ℕ))) = (0 : ZMod ((4 : ℕ) * S + (1 : ℕ)))) ∧ (∀ {K : Type u_4} [Field K] (S : ℕ), ↑((4 : ℕ) * S + (1 : ℕ)) = (0 : K) → ∀ (hbar : K), ↑((2 : ℕ) * ((2 : ℕ) * S)) * hbar = -hbar) ∧ (Nat.Prime (233 : ℕ) ∧ (233 : ℕ) = (4 : ℕ) * (58 : ℕ) + (1 : ℕ) ∧ (58 : ℕ) % (2 : ℕ) = (0 : ℕ) ∧ (58 : ℕ) % (3 : ℕ) = (1 : ℕ) ∧ (2 : ZMod (233 : ℕ)) * (116 : ZMod (233 : ℕ)) + (1 : ZMod (233 : ℕ)) = (0 : ZMod (233 : ℕ)) ∧ (89 : ZMod (233 : ℕ)) ^ (2 : ℕ) = (-1 : ZMod (233 : ℕ)) ∧ (124 : ZMod (233 : ℕ)) ^ (2 : ℕ) = (-2 : ZMod (233 : ℕ)) ∧ (2 : ZMod (233 : ℕ)) * (159 : ZMod (233 : ℕ)) ^ (2 : ℕ) = (1 : ZMod (233 : ℕ)) ∧ (124 : ZMod (233 : ℕ)) * (159 : ZMod (233 : ℕ)) = (-89 : ZMod (233 : ℕ)) ∧ (144 : ZMod (233 : ℕ)) = (-89 : ZMod (233 : ℕ)) ∧ (116 : ZMod (233 : ℕ)) = -(159 : ZMod (233 : ℕ)) ^ (2 : ℕ) ∧ (4 : ZMod (233 : ℕ)) * (116 : ZMod (233 : ℕ)) ^ (2 : ℕ) = (1 : ZMod (233 : ℕ)) ∧ (89 : ZMod (233 : ℕ)) ^ (4 : ℕ) = (1 : ZMod (233 : ℕ)) ∧ (89 : ZMod (233 : ℕ)) * (159 : ZMod (233 : ℕ)) = (124 : ZMod (233 : ℕ)) * (116 : ZMod (233 : ℕ)) ∧ (109 : ZMod (233 : ℕ)) = (-124 : ZMod (233 : ℕ)) ∧ (109 : ZMod (233 : ℕ)) * (159 : ZMod (233 : ℕ)) ≠ (-89 : ZMod (233 : ℕ))) ∧ Nat.Prime (2408561 : ℕ) ∧ (2408561 : ℕ) = (4 : ℕ) * (602140 : ℕ) + (1 : ℕ) ∧ (602140 : ℕ) % (2 : ℕ) = (0 : ℕ) ∧ (602140 : ℕ) % (3 : ℕ) = (1 : ℕ) ∧ (2 : ZMod (2408561 : ℕ)) * (1204280 : ZMod (2408561 : ℕ)) + (1 : ZMod (2408561 : ℕ)) = (0 : ZMod (2408561 : ℕ)) ∧ (18688 : ZMod (2408561 : ℕ)) ^ (2 : ℕ) = (-1 : ZMod (2408561 : ℕ)) ∧ (1880160 : ZMod (2408561 : ℕ)) ^ (2 : ℕ) = (-2 : ZMod (2408561 : ℕ)) ∧ (2 : ZMod (2408561 : ℕ)) * (171106 : ZMod (2408561 : ℕ)) ^ (2 : ℕ) = (1 : ZMod (2408561 : ℕ)) ∧ (1880160 : ZMod (2408561 : ℕ)) * (171106 : ZMod (2408561 : ℕ)) = (-18688 : ZMod (2408561 : ℕ)) ∧ (2389873 : ZMod (2408561 : ℕ)) = (-18688 : ZMod (2408561 : ℕ)) ∧ (1204280 : ZMod (2408561 : ℕ)) = -(171106 : ZMod (2408561 : ℕ)) ^ (2 : ℕ) ∧ (4 : ZMod (2408561 : ℕ)) * (1204280 : ZMod (2408561 : ℕ)) ^ (2 : ℕ) = (1 : ZMod (2408561 : ℕ)) ∧ (18688 : ZMod (2408561 : ℕ)) ^ (4 : ℕ) = (1 : ZMod (2408561 : ℕ)) ∧ (18688 : ZMod (2408561 : ℕ)) * (171106 : ZMod (2408561 : ℕ)) = (1880160 : ZMod (2408561 : ℕ)) * (1204280 : ZMod (2408561 : ℕ)) :=
  And.intro @FRC.Dimensions.G_unique (And.intro @FRC.Dimensions.root_pair (And.intro @FRC.Dimensions.linkage (And.intro @FRC.Dimensions.residues_exist (And.intro @FRC.Dimensions.h_form (And.intro @FRC.Dimensions.carrier233 (@FRC.Dimensions.carrierLab))))))
/-- 10:E5 — Pair consequences and representative inertness: $G=-c^{2}$, $G^{2}\equiv4^{-1}$, $\hbar^{4}\equiv1$, $(k_Bc)^{2}\equiv-1$, and $\hbar cG^{-1}$ lands in $\{\pm k_B\}$; of the eight sign assignments exactly the four with $\sigma_\hbar=\sigma_c\sigma_k$ are admissible, a $(\Z/2)^{2}$, every identity holding on each and the $\hbar$-flip relabelling within $\{\hbar,h\}$; what a bounded observer registers is exactly the pair-inert content. -/
theorem row_E5 : (∀ {K : Type u_1} [Field K] (G c h k : K), (2 : K) ≠ (0 : K) → (2 : K) * G + (1 : K) = (0 : K) → (2 : K) * c ^ (2 : ℕ) = (1 : K) → h ^ (2 : ℕ) = (-1 : K) → k ^ (2 : ℕ) = (-2 : K) → G = -c ^ (2 : ℕ) ∧ G ^ (2 : ℕ) = (4 : K)⁻¹ ∧ h ^ (4 : ℕ) = (1 : K) ∧ (k * c) ^ (2 : ℕ) = (-1 : K) ∧ (h * c * G⁻¹) ^ (2 : ℕ) = (-2 : K) ∧ (h * c * G⁻¹ = k ∨ h * c * G⁻¹ = -k)) ∧ (∀ {K : Type u_2} [Field K] (c h k sc sh sk : K), h ≠ (0 : K) → k * c = -h → sc = (1 : K) ∨ sc = (-1 : K) → sh = (1 : K) ∨ sh = (-1 : K) → sk = (1 : K) ∨ sk = (-1 : K) → (sk * k * (sc * c) = -(sh * h) ↔ sh = sc * sk) ∧ (sc * c) ^ (2 : ℕ) = c ^ (2 : ℕ) ∧ (sh * h) ^ (2 : ℕ) = h ^ (2 : ℕ) ∧ (sk * k) ^ (2 : ℕ) = k ^ (2 : ℕ)) ∧ (Nat.Prime (233 : ℕ) ∧ (233 : ℕ) = (4 : ℕ) * (58 : ℕ) + (1 : ℕ) ∧ (58 : ℕ) % (2 : ℕ) = (0 : ℕ) ∧ (58 : ℕ) % (3 : ℕ) = (1 : ℕ) ∧ (2 : ZMod (233 : ℕ)) * (116 : ZMod (233 : ℕ)) + (1 : ZMod (233 : ℕ)) = (0 : ZMod (233 : ℕ)) ∧ (89 : ZMod (233 : ℕ)) ^ (2 : ℕ) = (-1 : ZMod (233 : ℕ)) ∧ (124 : ZMod (233 : ℕ)) ^ (2 : ℕ) = (-2 : ZMod (233 : ℕ)) ∧ (2 : ZMod (233 : ℕ)) * (159 : ZMod (233 : ℕ)) ^ (2 : ℕ) = (1 : ZMod (233 : ℕ)) ∧ (124 : ZMod (233 : ℕ)) * (159 : ZMod (233 : ℕ)) = (-89 : ZMod (233 : ℕ)) ∧ (144 : ZMod (233 : ℕ)) = (-89 : ZMod (233 : ℕ)) ∧ (116 : ZMod (233 : ℕ)) = -(159 : ZMod (233 : ℕ)) ^ (2 : ℕ) ∧ (4 : ZMod (233 : ℕ)) * (116 : ZMod (233 : ℕ)) ^ (2 : ℕ) = (1 : ZMod (233 : ℕ)) ∧ (89 : ZMod (233 : ℕ)) ^ (4 : ℕ) = (1 : ZMod (233 : ℕ)) ∧ (89 : ZMod (233 : ℕ)) * (159 : ZMod (233 : ℕ)) = (124 : ZMod (233 : ℕ)) * (116 : ZMod (233 : ℕ)) ∧ (109 : ZMod (233 : ℕ)) = (-124 : ZMod (233 : ℕ)) ∧ (109 : ZMod (233 : ℕ)) * (159 : ZMod (233 : ℕ)) ≠ (-89 : ZMod (233 : ℕ))) ∧ Nat.Prime (2408561 : ℕ) ∧ (2408561 : ℕ) = (4 : ℕ) * (602140 : ℕ) + (1 : ℕ) ∧ (602140 : ℕ) % (2 : ℕ) = (0 : ℕ) ∧ (602140 : ℕ) % (3 : ℕ) = (1 : ℕ) ∧ (2 : ZMod (2408561 : ℕ)) * (1204280 : ZMod (2408561 : ℕ)) + (1 : ZMod (2408561 : ℕ)) = (0 : ZMod (2408561 : ℕ)) ∧ (18688 : ZMod (2408561 : ℕ)) ^ (2 : ℕ) = (-1 : ZMod (2408561 : ℕ)) ∧ (1880160 : ZMod (2408561 : ℕ)) ^ (2 : ℕ) = (-2 : ZMod (2408561 : ℕ)) ∧ (2 : ZMod (2408561 : ℕ)) * (171106 : ZMod (2408561 : ℕ)) ^ (2 : ℕ) = (1 : ZMod (2408561 : ℕ)) ∧ (1880160 : ZMod (2408561 : ℕ)) * (171106 : ZMod (2408561 : ℕ)) = (-18688 : ZMod (2408561 : ℕ)) ∧ (2389873 : ZMod (2408561 : ℕ)) = (-18688 : ZMod (2408561 : ℕ)) ∧ (1204280 : ZMod (2408561 : ℕ)) = -(171106 : ZMod (2408561 : ℕ)) ^ (2 : ℕ) ∧ (4 : ZMod (2408561 : ℕ)) * (1204280 : ZMod (2408561 : ℕ)) ^ (2 : ℕ) = (1 : ZMod (2408561 : ℕ)) ∧ (18688 : ZMod (2408561 : ℕ)) ^ (4 : ℕ) = (1 : ZMod (2408561 : ℕ)) ∧ (18688 : ZMod (2408561 : ℕ)) * (171106 : ZMod (2408561 : ℕ)) = (1880160 : ZMod (2408561 : ℕ)) * (1204280 : ZMod (2408561 : ℕ)) :=
  And.intro @FRC.Dimensions.pair_consequences (And.intro @FRC.Dimensions.sign_assignments (And.intro @FRC.Dimensions.carrier233 (@FRC.Dimensions.carrierLab)))
/-- 10:F2 — The mechanical and gravitational domains: $[m]=\Iq\unitL^{-2}\unitT$; $[a]=\unitL\unitT^{-2}$, $[F]=\Iq\unitL^{-1}\unitT^{-1}$, $[p]=\Iq\unitL^{-1}$, $[S]=\Iq$, $[P]=\Iq\unitT^{-2}$, $[\text{pressure}]=\Iq\unitL^{-3}\unitT^{-1}$; $[G]=\Iq^{-1}\unitL^{5}\unitT^{-3}$; the geometric conversions $[G\hbar/c^{3}]=\unitL^{2}$, $[Gm/c^{2}]=\unitL$, $[Gm/c^{3}]=\unitT$, $[G\rho_m]=\unitT^{-2}$; mass derived, not primitive. -/
theorem row_F2 : (FRC.Dimensions.massL = FRC.Dimensions.energyL - (2 : ℤ) • FRC.Dimensions.speedL ∧ FRC.Dimensions.massL = ((-2 : ℤ), (1 : ℤ), (1 : ℤ)) ∧ FRC.Dimensions.accelL = FRC.Dimensions.speedL - FRC.Dimensions.timeL ∧ FRC.Dimensions.forceL = FRC.Dimensions.massL + FRC.Dimensions.accelL ∧ FRC.Dimensions.forceL = ((-1 : ℤ), (-1 : ℤ), (1 : ℤ)) ∧ FRC.Dimensions.momL = FRC.Dimensions.massL + FRC.Dimensions.speedL ∧ FRC.Dimensions.momL = FRC.Dimensions.flagL - FRC.Dimensions.spaceL ∧ FRC.Dimensions.actionL = FRC.Dimensions.energyL + FRC.Dimensions.timeL ∧ FRC.Dimensions.actionL = FRC.Dimensions.flagL ∧ FRC.Dimensions.powerL = FRC.Dimensions.energyL - FRC.Dimensions.timeL ∧ FRC.Dimensions.powerL = ((0 : ℤ), (-2 : ℤ), (1 : ℤ)) ∧ FRC.Dimensions.pressureL = FRC.Dimensions.forceL - (2 : ℤ) • FRC.Dimensions.spaceL ∧ FRC.Dimensions.pressureL = ((-3 : ℤ), (-1 : ℤ), (1 : ℤ)) ∧ FRC.Dimensions.gravL = FRC.Dimensions.forceL + (2 : ℤ) • FRC.Dimensions.spaceL - (2 : ℤ) • FRC.Dimensions.massL ∧ FRC.Dimensions.gravL = ((5 : ℤ), (-3 : ℤ), (-1 : ℤ)) ∧ FRC.Dimensions.gravL = FRC.Dimensions.flagL + FRC.Dimensions.speedL - (2 : ℤ) • FRC.Dimensions.massL) ∧ FRC.Dimensions.gravL + FRC.Dimensions.flagL - (3 : ℤ) • FRC.Dimensions.speedL = ((2 : ℤ), (0 : ℤ), (0 : ℤ)) ∧ FRC.Dimensions.gravL + FRC.Dimensions.massL - (2 : ℤ) • FRC.Dimensions.speedL = ((1 : ℤ), (0 : ℤ), (0 : ℤ)) ∧ FRC.Dimensions.gravL + FRC.Dimensions.massL - (3 : ℤ) • FRC.Dimensions.speedL = ((0 : ℤ), (1 : ℤ), (0 : ℤ)) ∧ FRC.Dimensions.gravL + (FRC.Dimensions.massL - (3 : ℤ) • FRC.Dimensions.spaceL) = ((0 : ℤ), (-2 : ℤ), (0 : ℤ)) ∧ FRC.Dimensions.gravL - (4 : ℤ) • FRC.Dimensions.speedL + (FRC.Dimensions.energyL - (3 : ℤ) • FRC.Dimensions.spaceL) = ((-2 : ℤ), (0 : ℤ), (0 : ℤ)) ∧ FRC.Dimensions.massL + FRC.Dimensions.speedL - FRC.Dimensions.flagL = ((-1 : ℤ), (0 : ℤ), (0 : ℤ)) :=
  And.intro @FRC.Dimensions.mechanical_domains (@FRC.Dimensions.geometric_conversions)
/-- 10:F3 — Temperature carries the acceleration domain: $[\Theta]=\unitE[k_B]^{-1}=\unitL\unitT^{-2}=[a]$, flag-free; the Unruh combination $\hbar a/c\,k_B$ closes flag-free in the algebra; neither mass nor temperature is primitive, the classical $M$-$L$-$T$-plus-thermal system the torsion-free shadow of two generators plus the flag. -/
theorem row_F3 : FRC.Dimensions.thetaL = FRC.Dimensions.energyL - FRC.Dimensions.kBL ∧ FRC.Dimensions.thetaL = FRC.Dimensions.accelL ∧ FRC.Dimensions.thetaL.2.2 = (0 : ℤ) ∧ FRC.Dimensions.flagL + FRC.Dimensions.accelL - FRC.Dimensions.speedL - FRC.Dimensions.kBL = FRC.Dimensions.thetaL :=
  @FRC.Dimensions.temperature_domain
/-- 10:F4 — Count-valued comparisons are flag-free: every ratio of two quantities of equal crossing degree ($Gm/r^{3}$, the phase exponent $[E][T]/[\hbar]$) is a neutral or flag-free label, the flag entering unitful measures only; $F/a=[m]$, crossing degrees $1$ and $0$, is the flagged boundary case. -/
theorem row_F4 : (∀ (x y : FRC.Dimensions.Lab), x.2.2 = y.2.2 → (x - y).2.2 = (0 : ℤ)) ∧ FRC.Dimensions.energyL + FRC.Dimensions.timeL - FRC.Dimensions.flagL = (0 : FRC.Dimensions.Lab) ∧ FRC.Dimensions.gravL + FRC.Dimensions.massL - (3 : ℤ) • FRC.Dimensions.spaceL = ((0 : ℤ), (-2 : ℤ), (0 : ℤ)) ∧ (FRC.Dimensions.gravL + FRC.Dimensions.massL - (3 : ℤ) • FRC.Dimensions.spaceL).2.2 = (0 : ℤ) ∧ FRC.Dimensions.forceL - FRC.Dimensions.accelL = FRC.Dimensions.massL ∧ (FRC.Dimensions.forceL - FRC.Dimensions.accelL).2.2 = (1 : ℤ) ∧ FRC.Dimensions.forceL.2.2 ≠ FRC.Dimensions.accelL.2.2 :=
  And.intro @FRC.Dimensions.equal_crossing_flag_free (@FRC.Dimensions.comparison_examples)
/-- 10:G1 — Local recovery: for an exponent horizon $H$ with $4\kap>2H$ the modular labels distinguish every conventional pair $|r|,|s|\le H$; the flagged sector is recovered through the crossing degree, $M^{u}L^{a}T^{b}\mapsto(a-2u,\,b+u;\,u)$ injective and windowed-faithful. -/
theorem row_G1 : And (∀ (κ H : Nat), @LT.lt Nat instLTNat (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) H) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) → ∀ (r r' s s' : Int), @LE.le Int Int.instLEInt (@abs Int instLatticeInt Int.instAddGroup r) (@Nat.cast Int instNatCastInt H) → @LE.le Int Int.instLEInt (@abs Int instLatticeInt Int.instAddGroup r') (@Nat.cast Int instNatCastInt H) → @LE.le Int Int.instLEInt (@abs Int instLatticeInt Int.instAddGroup s) (@Nat.cast Int instNatCastInt H) → @LE.le Int Int.instLEInt (@abs Int instLatticeInt Int.instAddGroup s') (@Nat.cast Int instNatCastInt H) → @Eq (Prod (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ))) (@Prod.mk (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@Int.cast (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@AddGroupWithOne.toIntCast (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@Ring.toAddGroupWithOne (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@CommRing.toRing (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (ZMod.commRing (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))) r) (@Int.cast (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@AddGroupWithOne.toIntCast (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@Ring.toAddGroupWithOne (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@CommRing.toRing (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (ZMod.commRing (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ))))) s)) (@Prod.mk (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@Int.cast (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@AddGroupWithOne.toIntCast (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@Ring.toAddGroupWithOne (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@CommRing.toRing (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (ZMod.commRing (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))) r') (@Int.cast (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@AddGroupWithOne.toIntCast (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@Ring.toAddGroupWithOne (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@CommRing.toRing (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (ZMod.commRing (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ))))) s')) → And (@Eq Int r r') (@Eq Int s s')) (And (∀ (u a b u' a' b' : Int), @Eq FRC.Dimensions.Lab (FRC.Dimensions.embed u a b) (FRC.Dimensions.embed u' a' b') → And (@Eq Int u u') (And (@Eq Int a a') (@Eq Int b b'))) (∀ (κ H : Nat) [@NeZero Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass) κ], @LT.lt Nat instLTNat (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) H) κ → ∀ (r r' s s' j j' : Int), @LE.le Int Int.instLEInt (@abs Int instLatticeInt Int.instAddGroup r) (@Nat.cast Int instNatCastInt H) → @LE.le Int Int.instLEInt (@abs Int instLatticeInt Int.instAddGroup r') (@Nat.cast Int instNatCastInt H) → @LE.le Int Int.instLEInt (@abs Int instLatticeInt Int.instAddGroup s) (@Nat.cast Int instNatCastInt H) → @LE.le Int Int.instLEInt (@abs Int instLatticeInt Int.instAddGroup s') (@Nat.cast Int instNatCastInt H) → @LE.le Int Int.instLEInt (@abs Int instLatticeInt Int.instAddGroup j) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) → @LE.le Int Int.instLEInt (@abs Int instLatticeInt Int.instAddGroup j') (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) → @Eq (FRC.Dimensions.Dom κ) (@DFunLike.coe (@AddMonoidHom FRC.Dimensions.Lab (FRC.Dimensions.Dom κ) (@AddZeroClass.toAddZero FRC.Dimensions.Lab (@Prod.instAddZeroClass Int (Prod Int Int) (@AddMonoid.toAddZeroClass Int Int.instAddMonoid) (@Prod.instAddZeroClass Int Int (@AddMonoid.toAddZeroClass Int Int.instAddMonoid) (@AddMonoid.toAddZeroClass Int Int.instAddMonoid)))) (@AddZeroClass.toAddZero (FRC.Dimensions.Dom κ) (@Prod.instAddZeroClass (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@AddMonoid.toAddZeroClass (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@AddMonoidWithOne.toAddMonoid (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@AddGroupWithOne.toAddMonoidWithOne (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@Ring.toAddGroupWithOne (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@CommRing.toRing (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (ZMod.commRing (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))) (@AddMonoid.toAddZeroClass (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@AddMonoidWithOne.toAddMonoid (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@AddGroupWithOne.toAddMonoidWithOne (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@Ring.toAddGroupWithOne (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@CommRing.toRing (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (ZMod.commRing (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)))))))))) FRC.Dimensions.Lab (fun x => FRC.Dimensions.Dom κ) (@AddMonoidHom.instFunLike FRC.Dimensions.Lab (FRC.Dimensions.Dom κ) (@AddZeroClass.toAddZero FRC.Dimensions.Lab (@Prod.instAddZeroClass Int (Prod Int Int) (@AddMonoid.toAddZeroClass Int Int.instAddMonoid) (@Prod.instAddZeroClass Int Int (@AddMonoid.toAddZeroClass Int Int.instAddMonoid) (@AddMonoid.toAddZeroClass Int Int.instAddMonoid)))) (@AddZeroClass.toAddZero (FRC.Dimensions.Dom κ) (@Prod.instAddZeroClass (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@AddMonoid.toAddZeroClass (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@AddMonoidWithOne.toAddMonoid (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@AddGroupWithOne.toAddMonoidWithOne (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@Ring.toAddGroupWithOne (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@CommRing.toRing (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (ZMod.commRing (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))) (@AddMonoid.toAddZeroClass (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@AddMonoidWithOne.toAddMonoid (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@AddGroupWithOne.toAddMonoidWithOne (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@Ring.toAddGroupWithOne (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@CommRing.toRing (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (ZMod.commRing (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)))))))))) (FRC.Dimensions.realize κ) (@Prod.mk Int (Prod Int Int) r (@Prod.mk Int Int s j))) (@DFunLike.coe (@AddMonoidHom FRC.Dimensions.Lab (FRC.Dimensions.Dom κ) (@AddZeroClass.toAddZero FRC.Dimensions.Lab (@Prod.instAddZeroClass Int (Prod Int Int) (@AddMonoid.toAddZeroClass Int Int.instAddMonoid) (@Prod.instAddZeroClass Int Int (@AddMonoid.toAddZeroClass Int Int.instAddMonoid) (@AddMonoid.toAddZeroClass Int Int.instAddMonoid)))) (@AddZeroClass.toAddZero (FRC.Dimensions.Dom κ) (@Prod.instAddZeroClass (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@AddMonoid.toAddZeroClass (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@AddMonoidWithOne.toAddMonoid (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@AddGroupWithOne.toAddMonoidWithOne (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@Ring.toAddGroupWithOne (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@CommRing.toRing (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (ZMod.commRing (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))) (@AddMonoid.toAddZeroClass (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@AddMonoidWithOne.toAddMonoid (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@AddGroupWithOne.toAddMonoidWithOne (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@Ring.toAddGroupWithOne (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@CommRing.toRing (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (ZMod.commRing (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)))))))))) FRC.Dimensions.Lab (fun x => FRC.Dimensions.Dom κ) (@AddMonoidHom.instFunLike FRC.Dimensions.Lab (FRC.Dimensions.Dom κ) (@AddZeroClass.toAddZero FRC.Dimensions.Lab (@Prod.instAddZeroClass Int (Prod Int Int) (@AddMonoid.toAddZeroClass Int Int.instAddMonoid) (@Prod.instAddZeroClass Int Int (@AddMonoid.toAddZeroClass Int Int.instAddMonoid) (@AddMonoid.toAddZeroClass Int Int.instAddMonoid)))) (@AddZeroClass.toAddZero (FRC.Dimensions.Dom κ) (@Prod.instAddZeroClass (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@AddMonoid.toAddZeroClass (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@AddMonoidWithOne.toAddMonoid (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@AddGroupWithOne.toAddMonoidWithOne (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@Ring.toAddGroupWithOne (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@CommRing.toRing (ZMod (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (ZMod.commRing (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))) (@AddMonoid.toAddZeroClass (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@AddMonoidWithOne.toAddMonoid (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@AddGroupWithOne.toAddMonoidWithOne (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@Ring.toAddGroupWithOne (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (@CommRing.toRing (ZMod (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)) (ZMod.commRing (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) κ)))))))))) (FRC.Dimensions.realize κ) (@Prod.mk Int (Prod Int Int) r' (@Prod.mk Int Int s' j'))) → And (@Eq Int r r') (And (@Eq Int s s') (@Eq Int j j')))) :=
  And.intro @FRC.Dimensions.local_recovery (And.intro @FRC.Dimensions.embed_injective (@FRC.Dimensions.realize_faithful))
/-- 10:G2 — The window ladder: coherence $2\sqrt\kap$ below recovery $\kap/2$ below flag inaccessibility $\kap$ below covariance $2\kap$, nested strictly for every $\kap\ge17$ and failing for the toy $\kap=3$, all orderings by integer squares; the coherence identity $(2\sqrt\kap)^{2}=\p-1$ and the totality closure $(2\sqrt\dS)^{2}=\Om-1$. -/
theorem row_G2 : ∀ (κ S : ℕ), ((16 : ℕ) * κ < κ ^ (2 : ℕ) ↔ (16 : ℕ) < κ) ∧ ((0 : ℕ) < κ → κ / (2 : ℕ) < κ ∧ κ < (2 : ℕ) * κ) ∧ ¬(16 : ℕ) * (3 : ℕ) < (3 : ℕ) ^ (2 : ℕ) ∧ ((2 : ℕ) * (2 : ℕ) * κ = (4 : ℕ) * κ ∧ (4 : ℕ) * κ = (4 : ℕ) * κ + (1 : ℕ) - (1 : ℕ)) ∧ (4 : ℕ) * S = (4 : ℕ) * S + (1 : ℕ) - (1 : ℕ) :=
  @FRC.Dimensions.window_ladder
set_option linter.defProp false in
/-- 10:G3 — The worked examples: $\kap=3$, $H=5$, $12>10$ so every pair in $[-5,5]^{2}$ is distinguished; kinetic energy $[m][v]^{2}=[E]$; $Q+Q^{2}$ inhomogeneous; the phase exponent neutral; flag arithmetic ($G\hbar/c^{3}$ flag-free, $\Iq^{2}=\unitT^{\pi}$); the Schwarzschild length $[Gm/c^{2}]=\unitL$; the gravitational frequency $[Gm/r^{3}]=\unitT^{-2}$; the energy--momentum relation $E^{2}=p^{2}c^{2}+m^{2}c^{4}$ homogeneous at crossing degree two, its massless case $E=pc$ at crossing degree one. -/
def row_G3 := And.intro @FRC.Dimensions.examples13 (And.intro @FRC.Dimensions.recovery13 (@FRC.Dimensions.energy_momentum))
/-- 10:G4 — Buckingham's count: on the integer lift the neutral monomials of $N$ quantities are the kernel of their $N\times3$ label matrix, $N-\operatorname{rank}$ independent dimensionless products with rank $\le3$, the classical count for quantities whose classical dimensions lie in $M$-$L$-$T$ and the derived-$k_B$ count for thermal ones; on the window $2H<\kap$, $|j|\le1$ lifted and realized neutrality coincide; the pendulum $(T,\ell,g,m)$: rank $3$, one product. -/
theorem row_G4 : (∀ (κ : ℕ) {ι : Type u_1} (s : Finset ι) (m : ι → FRC.Dimensions.Dom κ) (k : ι → ℤ), ∏ j ∈ s, (FRC.Dimensions.Uhom κ) (Multiplicative.ofAdd (m j)) ^ k j = (FRC.Dimensions.Uhom κ) (Multiplicative.ofAdd (∑ j ∈ s, k j • m j))) ∧ (∀ (u a b u' a' b' : ℤ), FRC.Dimensions.embed u a b = FRC.Dimensions.embed u' a' b' → u = u' ∧ a = a' ∧ b = b') ∧ (∀ (κ H : ℕ) [NeZero κ], (2 : ℕ) * H < κ → ∀ (r s j : ℤ), |r| ≤ ↑H → |s| ≤ ↑H → |j| ≤ (1 : ℤ) → ((FRC.Dimensions.realize κ) (r, s, j) = (0 : FRC.Dimensions.Dom κ) ↔ (r, s, j) = ((0 : ℤ), (0 : ℤ), (0 : ℤ)))) ∧ FRC.Dimensions.embed (0 : ℤ) (0 : ℤ) (1 : ℤ) = FRC.Dimensions.timeL ∧ FRC.Dimensions.embed (0 : ℤ) (1 : ℤ) (0 : ℤ) = FRC.Dimensions.spaceL ∧ FRC.Dimensions.embed (0 : ℤ) (1 : ℤ) (-2 : ℤ) = FRC.Dimensions.accelL ∧ FRC.Dimensions.embed (1 : ℤ) (0 : ℤ) (0 : ℤ) = FRC.Dimensions.massL ∧ (∀ (k₁ k₂ k₃ k₄ : ℤ), k₁ • FRC.Dimensions.timeL + k₂ • FRC.Dimensions.spaceL + k₃ • FRC.Dimensions.accelL + k₄ • FRC.Dimensions.massL = (0 : FRC.Dimensions.Lab) ↔ ∃ t, k₁ = (2 : ℤ) * t ∧ k₂ = -t ∧ k₃ = t ∧ k₄ = (0 : ℤ)) ∧ (2 : ℤ) • FRC.Dimensions.timeL - FRC.Dimensions.spaceL + FRC.Dimensions.accelL = (0 : FRC.Dimensions.Lab) ∧ !![FRC.Dimensions.spaceL.1, FRC.Dimensions.spaceL.2.1, FRC.Dimensions.spaceL.2.2; FRC.Dimensions.accelL.1, FRC.Dimensions.accelL.2.1, FRC.Dimensions.accelL.2.2; FRC.Dimensions.massL.1, FRC.Dimensions.massL.2.1, FRC.Dimensions.massL.2.2].det = (-2 : ℤ) :=
  And.intro @FRC.Dimensions.monomial_units (And.intro @FRC.Dimensions.embed_injective (And.intro @FRC.Dimensions.window_neutrality (@FRC.Dimensions.pendulum_kernel)))
-- end ledger rows

end FRC.Dimensions
