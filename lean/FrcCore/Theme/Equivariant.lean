import FrcCore.Nat
import FrcCore.Shell

/-!
# The logic theme — equivariant choice: a section exists iff every stabiliser has a fixed point

5-reductio's Theorem equivariant-choice (5:E3), the Fraenkel–Mostowski mechanism in positive form, on the kernel alone
(21 October 2026): a group as a structure with its four laws, actions on an index type and on a fibre type, an
equivariant family `π : A → I`. On one orbit (a transitivity datum `tr i • i₀ = i`) an equivariant section exists
exactly when the stabiliser of the base point fixes a point of its fibre; over finitely many orbits, exactly when
every orbit's representative does. The hard direction defines the section by transport, `s i = tr i • a`, and shows
it well defined through the stabiliser. The paper's obstruction (5:E4): on the line over `𝔽₅` the map `v ↦ −v`
fixes no basis vector, over `𝔽₂` it fixes `1`. No Mathlib, no axioms.
-/

namespace FRC.Equivariant

/-- A group: carrier `G`, the operation, the unit, the inverse, the laws. -/
structure Group (G : Type) where
  mul : G → G → G
  one : G
  inv : G → G
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a, mul one a = a
  mul_one : ∀ a, mul a one = a
  inv_mul : ∀ a, mul (inv a) a = one
  mul_inv : ∀ a, mul a (inv a) = one

/-- An action of the group on `X`. -/
structure Action {G : Type} (Γ : Group G) (X : Type) where
  act : G → X → X
  one_act : ∀ x, act Γ.one x = x
  mul_act : ∀ g h x, act (Γ.mul g h) x = act g (act h x)

variable {G I A : Type} {Γ : Group G}

/-- The family `π : A → I` is equivariant: `π (g • a) = g • π a`. -/
def Equivariant (ρI : Action Γ I) (ρA : Action Γ A) (π : A → I) : Prop :=
  ∀ g a, π (ρA.act g a) = ρI.act g (π a)

/-- `s` is a section of `π`. -/
def IsSection (π : A → I) (s : I → A) : Prop := ∀ i, π (s i) = i

/-- `s : I → A` is an equivariant map: `s (g • i) = g • s i`. -/
def EquivariantMap (ρI : Action Γ I) (ρA : Action Γ A) (s : I → A) : Prop :=
  ∀ g i, s (ρI.act g i) = ρA.act g (s i)

/-- `g` lies in the stabiliser of `i₀`. -/
def Stab (ρI : Action Γ I) (i₀ : I) (g : G) : Prop := ρI.act g i₀ = i₀

/-- 5:E3 (Theorem equivariant-choice, ⇒) — an equivariant section picks, at every point `i₀`, a point of the fibre
fixed by the stabiliser of `i₀`: `g • i₀ = i₀` gives `g • s i₀ = s (g • i₀) = s i₀`. -/
theorem fixed_point_of_section (ρI : Action Γ I) (ρA : Action Γ A) (π : A → I) (s : I → A)
    (hs : IsSection π s) (he : EquivariantMap ρI ρA s) (i₀ : I) :
    π (s i₀) = i₀ ∧ ∀ g, Stab ρI i₀ g → ρA.act g (s i₀) = s i₀ :=
  ⟨hs i₀, fun g hg => by rw [← he g i₀]; exact congrArg s hg⟩

theorem Group.inv_mul_cancel_left (Γ : Group G) (a b : G) : Γ.mul a (Γ.mul (Γ.inv a) b) = b := by
  rw [← Γ.mul_assoc, Γ.mul_inv, Γ.one_mul]

/-- The transport datum undone: `tr j⁻¹ • j = i₀`. -/
theorem act_inv_tr (ρI : Action Γ I) (i₀ : I) (tr : I → G) (htr : ∀ i, ρI.act (tr i) i₀ = i) (j : I) :
    ρI.act (Γ.inv (tr j)) j = i₀ :=
  calc ρI.act (Γ.inv (tr j)) j = ρI.act (Γ.inv (tr j)) (ρI.act (tr j) i₀) := by rw [htr j]
    _ = i₀ := by rw [← ρI.mul_act, Γ.inv_mul, ρI.one_act]

/-- 5:E3 (Theorem equivariant-choice, ⇐, one orbit) — on a transitive index set, given the transport datum
`tr i • i₀ = i`, a point `a` of the fibre over `i₀` fixed by the stabiliser of `i₀` yields the equivariant section
`s i = tr i • a`: it is a section since `π (tr i • a) = tr i • i₀ = i`, and equivariant since
`tr (g • i)⁻¹ · g · tr i` stabilises `i₀` and so fixes `a`. -/
theorem section_of_fixed_point (ρI : Action Γ I) (ρA : Action Γ A) (π : A → I)
    (hπ : Equivariant ρI ρA π) (i₀ : I) (tr : I → G) (htr : ∀ i, ρI.act (tr i) i₀ = i)
    (a : A) (ha : π a = i₀) (hfix : ∀ g, Stab ρI i₀ g → ρA.act g a = a) :
    ∃ s, IsSection π s ∧ EquivariantMap ρI ρA s :=
  ⟨fun i => ρA.act (tr i) a,
   fun i => by rw [hπ, ha, htr],
   fun g i => by
     -- h = tr (g • i)⁻¹ · (g · tr i) stabilises i₀
     have hstab : Stab ρI i₀ (Γ.mul (Γ.inv (tr (ρI.act g i))) (Γ.mul g (tr i))) := by
       show ρI.act (Γ.mul (Γ.inv (tr (ρI.act g i))) (Γ.mul g (tr i))) i₀ = i₀
       rw [ρI.mul_act, ρI.mul_act, htr i]; exact act_inv_tr ρI i₀ tr htr (ρI.act g i)
     have e := hfix _ hstab
     show ρA.act (tr (ρI.act g i)) a = ρA.act g (ρA.act (tr i) a)
     rw [← ρA.mul_act]
     -- g · tr i = tr (g • i) · h
     have e2 : Γ.mul g (tr i) = Γ.mul (tr (ρI.act g i)) (Γ.mul (Γ.inv (tr (ρI.act g i))) (Γ.mul g (tr i))) :=
       (Γ.inv_mul_cancel_left _ _).symm
     rw [e2, ρA.mul_act, e]⟩

/-- 5:E3 (Theorem equivariant-choice, one orbit) — on a transitive index set an equivariant section exists exactly
when the stabiliser of the base point fixes a point of its fibre. -/
theorem equivariant_section_iff (ρI : Action Γ I) (ρA : Action Γ A) (π : A → I)
    (hπ : Equivariant ρI ρA π) (i₀ : I) (tr : I → G) (htr : ∀ i, ρI.act (tr i) i₀ = i) :
    (∃ s, IsSection π s ∧ EquivariantMap ρI ρA s) ↔ ∃ a, π a = i₀ ∧ ∀ g, Stab ρI i₀ g → ρA.act g a = a :=
  ⟨fun ⟨s, hs, he⟩ => ⟨s i₀, fixed_point_of_section ρI ρA π s hs he i₀⟩,
   fun ⟨a, ha, hfix⟩ => section_of_fixed_point ρI ρA π hπ i₀ tr htr a ha hfix⟩

/-- 5:E3 (Theorem equivariant-choice, finitely many orbits) — with a representative `rep i` of every orbit, constant
on orbits, and the transport `tr i • rep i = i`, an equivariant section exists exactly when every representative's
stabiliser fixes a point of its fibre, the choice `a` of fixed points being itself constant on orbits. -/
theorem equivariant_section_orbits (ρI : Action Γ I) (ρA : Action Γ A) (π : A → I)
    (hπ : Equivariant ρI ρA π) (rep : I → I) (hrep : ∀ g i, rep (ρI.act g i) = rep i)
    (tr : I → G) (htr : ∀ i, ρI.act (tr i) (rep i) = i) :
    (∃ s, IsSection π s ∧ EquivariantMap ρI ρA s) ↔
      ∃ a : I → A, (∀ g i, a (ρI.act g i) = a i) ∧ ∀ i, π (a i) = rep i ∧ ∀ g, Stab ρI (rep i) g → ρA.act g (a i) = a i :=
  ⟨fun ⟨s, hs, he⟩ => ⟨fun i => s (rep i), fun g i => by show s (rep (ρI.act g i)) = s (rep i); rw [hrep],
     fun i => fixed_point_of_section ρI ρA π s hs he (rep i)⟩,
   fun ⟨a, hconst, hfix⟩ =>
    ⟨fun i => ρA.act (tr i) (a i),
     fun i => by rw [hπ, (hfix i).1, htr],
     fun g i => by
       have hstab : Stab ρI (rep i) (Γ.mul (Γ.inv (tr (ρI.act g i))) (Γ.mul g (tr i))) := by
         show ρI.act (Γ.mul (Γ.inv (tr (ρI.act g i))) (Γ.mul g (tr i))) (rep i) = rep i
         have h1 : ρI.act (tr (ρI.act g i)) (rep i) = ρI.act g i := by
           have := htr (ρI.act g i); rwa [hrep] at this
         rw [ρI.mul_act, ρI.mul_act, htr i]
         calc ρI.act (Γ.inv (tr (ρI.act g i))) (ρI.act g i)
             = ρI.act (Γ.inv (tr (ρI.act g i))) (ρI.act (tr (ρI.act g i)) (rep i)) := by rw [h1]
           _ = rep i := by rw [← ρI.mul_act, Γ.inv_mul, ρI.one_act]
       have e := (hfix i).2 _ hstab
       show ρA.act (tr (ρI.act g i)) (a (ρI.act g i)) = ρA.act g (ρA.act (tr i) (a i))
       rw [hconst, ← ρA.mul_act]
       have e2 : Γ.mul g (tr i) = Γ.mul (tr (ρI.act g i)) (Γ.mul (Γ.inv (tr (ρI.act g i))) (Γ.mul g (tr i))) :=
         (Γ.inv_mul_cancel_left _ _).symm
       rw [e2, ρA.mul_act, e]⟩⟩

/-! ### 5:E4 — the equivariant obstruction on `𝔽₅` (moved from the paper module, 21 October 2026) -/

/-- 5:E4 (Example basis-obstruction) — on the line over `𝔽₅` the map `v ↦ −v` fixes no basis: `−v ≠ v` for every
`v ≠ 0`; over `𝔽₂` it fixes `1`, so the obstruction is arithmetic. -/
theorem obstruction_five :
    (-(1 : FRC.Shell 5) ≠ 1) ∧ (-(2 : FRC.Shell 5) ≠ 2) ∧ (-(3 : FRC.Shell 5) ≠ 3) ∧ (-(4 : FRC.Shell 5) ≠ 4) ∧
      (-(1 : FRC.Shell 2) = 1) := by
  decide

end FRC.Equivariant


