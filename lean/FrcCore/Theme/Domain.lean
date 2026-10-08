/-!
# FrcCore.Theme.Domain — the unit-domain lattice: the torsion-free lift of the Subject's domain group (00:C12)

The Subject's quantity algebra is graded by the modular domain group `D_p = C_p × C_{p−1}` of the labels
`U_{r,s} = L^r T^s` (10-dimensions C1, C2): `L` attached to the additive meridian chart, `T` to the drive's phase chart,
and the flag `Iq = T^κ` of order four. This file is the lattice above it — exponent triples `(r, s, j)` of `L`, `T`
and the flag over the integers, the torsion-free shadow in which classical dimensional analysis lives — and the
domain identities the master's row C12 states: the temperature domain is acceleration, `[Θ] = [E][k_B]⁻¹ = L T⁻²`,
flag-free; the Unruh combination `ħ a/(c k_B)` closes on it; neither mass nor temperature is primitive, each a monomial
in the two generators and the flag; and the classical `M`-`L`-`T`-`Θ` exponents of the mechanical, gravitational and
thermal quantities (10:F2, F3) map to their domains under `M ↦ Iq L⁻² T`, `Θ ↦ L T⁻²`. Every statement is closed and
decided by the kernel. No axioms.
-/

namespace FRC.Domain

/-- An exponent triple `L^r T^s Iq^j` of the lift lattice. -/
structure Lift where
  r : Int
  s : Int
  j : Int
deriving DecidableEq

namespace Lift

/-- The product of domains adds exponents. -/
def mul (a b : Lift) : Lift := ⟨a.r + b.r, a.s + b.s, a.j + b.j⟩
/-- The inverse domain. -/
def inv (a : Lift) : Lift := ⟨-a.r, -a.s, -a.j⟩
/-- The dimensionless domain. -/
def one : Lift := ⟨0, 0, 0⟩

instance : Mul Lift := ⟨mul⟩
instance : Inv Lift := ⟨inv⟩
instance : OfNat Lift 1 := ⟨one⟩

/-- The length generator `L` (10:C1). -/
def L : Lift := ⟨1, 0, 0⟩
/-- The time generator `T` (10:C1). -/
def T : Lift := ⟨0, 1, 0⟩
/-- The flag `Iq = T^κ` (10:C4), the third coordinate of the lift. -/
def flag : Lift := ⟨0, 0, 1⟩

/-- `[v] = L T⁻¹` (10:F1). -/
def speed : Lift := L * T⁻¹
/-- `[a] = L T⁻²` (10:F2). -/
def accel : Lift := L * T⁻¹ * T⁻¹
/-- `[E] = Iq T⁻¹` (10:E, the energy face of the flag). -/
def energy : Lift := flag * T⁻¹
/-- `[ħ] = [E][T] = Iq`. -/
def hbar : Lift := energy * T
/-- `[k_B] = [ħ][c]⁻¹`: the Carrier linkage `k_B c = −ħ` (00:B7) read in domains, `Iq L⁻¹ T`. -/
def kB : Lift := hbar * speed⁻¹
/-- `[Θ] = [E][k_B]⁻¹` (10:F3). -/
def temp : Lift := energy * kB⁻¹
/-- `[m] = Iq L⁻² T` (10:F2), mass derived. -/
def mass : Lift := flag * L⁻¹ * L⁻¹ * T
/-- `[F] = [m][a]`. -/
def force : Lift := mass * accel
/-- `[p] = [m][v]`. -/
def momentum : Lift := mass * speed
/-- `[P] = [E][T]⁻¹`. -/
def power : Lift := energy * T⁻¹
/-- `[pressure] = [F][L]⁻²`. -/
def pressure : Lift := force * L⁻¹ * L⁻¹
/-- `[G] = [a][L]²[m]⁻¹`, from `a = G m / r²`. -/
def G : Lift := accel * L * L * mass⁻¹
/-- The Unruh combination `ħ a/(c k_B)`. -/
def unruh : Lift := hbar * accel * speed⁻¹ * kB⁻¹

/-- The classical dictionary: the exponent vector `M^a L^b T^c Θ^d` of classical dimensional analysis, read in the
lift under `M ↦ Iq L⁻² T` (the mass primitive standing in for the flag) and `Θ ↦ L T⁻²`. -/
def classical (a b c d : Int) : Lift := ⟨-2 * a + b + d, a + c - 2 * d, a⟩

/-- 00:C12, 10:F3 — the temperature domain is acceleration: `[Θ] = [E][k_B]⁻¹ = L T⁻² = [a]`, and `[k_B] = Iq L⁻¹ T`. -/
theorem temp_eq_accel : temp = accel ∧ temp = ⟨1, -2, 0⟩ ∧ kB = ⟨-1, 1, 1⟩ := by decide

/-- 00:C12 — flag-free: the flag exponent of the temperature domain is zero, while energy, `ħ` and `k_B` each carry
the flag once. -/
theorem temp_flag_free : temp.j = 0 ∧ energy.j = 1 ∧ hbar.j = 1 ∧ kB.j = 1 := by decide

/-- 00:C12 — the Unruh combination `ħ a/(c k_B)` closes as a domain identity: it is the temperature domain, flag-free. -/
theorem unruh_closes : unruh = temp ∧ unruh.j = 0 := by decide

/-- 00:C12 — neither mass nor temperature is primitive: each is a monomial in the two generators and the flag, and
the Planck temperature `Θ_P = E_P/|k_B|` carries the temperature domain by the same identity. -/
theorem not_primitive : mass = ⟨-2, 1, 1⟩ ∧ temp = L * T⁻¹ * T⁻¹ ∧ energy * kB⁻¹ = temp := by decide

/-- 00:C12 — classical dimensional analysis recovered in exponents: the classical `M`-`L`-`T`-`Θ` exponents of the
mechanical, gravitational and thermal quantities (10:F2, F3) map to their domains under the dictionary. -/
theorem classical_exponents :
    classical 1 0 0 0 = mass ∧ classical 0 1 (-1) 0 = speed ∧ classical 0 1 (-2) 0 = accel ∧
    classical 1 2 (-2) 0 = energy ∧ classical 1 2 (-1) 0 = hbar ∧ classical 1 1 (-2) 0 = force ∧
    classical 1 1 (-1) 0 = momentum ∧ classical 1 2 (-3) 0 = power ∧ classical 1 (-1) (-2) 0 = pressure ∧
    classical (-1) 3 (-2) 0 = G ∧ classical 1 2 (-2) (-1) = kB ∧ classical 0 0 0 1 = temp := by decide

/-- 00:C12 — recovered in arity: the classical four symbols generate the lift's three (two generators and the
flag) — `L`, `T` and the flag are classical monomials — with the one relation `Θ = L T⁻²`, so temperature is not a
fourth generator; and the flag's fourth power is the trivial domain's shadow only modulo `4κ`, which the lift does not
carry: `flag⁴ ≠ 1` in the lattice. -/
theorem classical_arity :
    classical 0 1 0 0 = L ∧ classical 0 0 1 0 = T ∧ classical 1 2 (-1) 0 = flag ∧
    classical 0 0 0 1 = classical 0 1 (-2) 0 ∧ flag * flag * flag * flag ≠ 1 := by decide

end Lift

end FRC.Domain
