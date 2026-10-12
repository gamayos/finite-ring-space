import FrcCore.Theme.Field
import FrcCore.Theme.Projective

/-! # The Hopf section and the frame triple on every prime shell (38:A9, 12 October 2026)
`Theme/Projective.lean` proves them from the field laws (`Frame.Fld`), `Theme/Field.lean` proves the laws from primality;
this file joins the two (Theorem *The two fibrations and the frame triple*, "for every odd prime `p` of the totality";
the master's C22 states it on `p = 4κ + 1`). The subject theme's third core file; it imports neither `Subject.lean` nor
`Pair.lean`, so its closure stays small. -/

namespace FRC
namespace Shell
namespace Prime

open Frame

variable {p : Nat} [Pos p]

/-- Every nonzero residue of a prime shell has an inverse: `x · x^(p − 2) = x^(p − 1) = 1` (Fermat). -/
theorem exists_inv (hp : FRC.Nat.isPrime p) {x : Shell p} (hx : x ≠ 0) : ∃ y, x * y = 1 := by
  refine ⟨x ^ (p - 2), ?_⟩
  have e : p - 1 = (p - 2) + 1 := by
    have h2 : 2 ≤ p := two_le hp
    have : p = (p - 2) + 2 := (FRC.Nat.sub_add_cancel h2).symm
    rw [this, FRC.Nat.add_sub_cancel]; rfl
  rw [mul_comm, ← pow_succ, ← e]; exact fermat hp hx

/-- A prime shell has the field laws (`Theme/Field.lean`'s lemmas and `exists_inv`). -/
theorem fld (hp : FRC.Nat.isPrime p) : Frame.Fld p :=
  ⟨one_ne_zero hp, fun hx => exists_inv hp hx, fun h => mul_eq_zero hp h, fun ha hb => mul_ne_zero hp ha hb,
   fun ha h => mul_left_cancel hp ha h, fun h => sq_eq_one hp h⟩

/-- 38:A9 — the Hopf section on every prime shell (`Fld.hopf_section` under primality, `ν` any nonsquare; on `𝔽₂` no
nonsquare exists, and the rows quantify over the odd primes). -/
theorem hopf_section (hp : FRC.Nat.isPrime p) {ν : Shell p} (hν : ¬ ∃ y : Shell p, y * y = ν) :
    (∀ α β x y : Shell p, β ≠ 0 → (x ≠ 0 ∨ y ≠ 0) → ¬ PEq ((boost ν α β).act x y) (x, y)) ∧
    (∀ α β a b e l : Shell p, boost ν α β = M2.smul l (borel a b e) → β = 0) ∧
    (∀ M : M2 p, M.det ≠ 0 → ∃ N a b e α β : Shell p, N ≠ 0 ∧ a * e ≠ 0 ∧ (α ≠ 0 ∨ β ≠ 0) ∧
      M2.smul N M = (borel a b e).mul (boost ν α β)) ∧
    (∀ l a1 b1 e1 α1 β1 a2 b2 e2 α2 β2 : Shell p, l ≠ 0 → e2 ≠ 0 → (α1 ≠ 0 ∨ β1 ≠ 0) →
      M2.smul l ((borel a1 b1 e1).mul (boost ν α1 β1)) = (borel a2 b2 e2).mul (boost ν α2 β2) →
      α1 * β2 = α2 * β1 ∧ e2 * a1 = e1 * a2 ∧ e2 * b1 = e1 * b2) ∧
    (∀ α β α' β' : Shell p, (α ≠ 0 ∨ β ≠ 0) → (α' ≠ 0 ∨ β' ≠ 0) →
      ((∃ μ : Shell p, μ ≠ 0 ∧ boost ν α' β' = M2.smul μ (boost ν α β)) ↔ α * β' = α' * β)) ∧
    natCount (fun _ => True) p * natCount (fun b => b ≠ 0) p = p * (p - 1) ∧
    (boost ν (-1) 0 = borel (-1) 0 (-1) ∧ (-1 : Shell p) * -1 + -(ν * (0 * 0)) = 1 ∧ (-1 : Shell p) * -1 = 1 ∧
      (∀ α β a b e : Shell p, boost ν α β = borel a b e → α * α + -(ν * (β * β)) = 1 → β = 0 ∧ (α = 1 ∨ α = -1)) ∧
      ∀ M N : M2 p, (M2.smul (-1) M).mul (M2.smul (-1) N) = M.mul N) :=
  (fld hp).hopf_section hν

/-- 38:A9 — the frame counts on every prime shell: `Fld.hopf_counts` under primality. -/
theorem hopf_counts (hp : FRC.Nat.isPrime p) (ν : Shell p) :
    (∀ a b e : Shell p, a * e ≠ 0 → ∃ i j : Nat, i < p ∧ j < p ∧ i ≠ 0 ∧
      ∃ l : Shell p, l ≠ 0 ∧ M2.smul l (borel a b e) = borel (ofNat i) (ofNat j) 1) ∧
    (∀ i j i' j' : Nat, i < p → j < p → i' < p → j' < p → ∀ l : Shell p,
      M2.smul l (borel (ofNat i) (ofNat j) 1) = borel (ofNat i') (ofNat j') 1 → i = i' ∧ j = j') ∧
    natCount (fun _ => True) p * natCount (fun b => b ≠ 0) p = p * (p - 1) ∧
    (∀ α β : Shell p, (α ≠ 0 ∨ β ≠ 0) →
      (∃ i : Nat, i < p ∧ ∃ μ : Shell p, μ ≠ 0 ∧ M2.smul μ (boost ν α β) = boost ν (ofNat i) 1) ∨
      (∃ μ : Shell p, μ ≠ 0 ∧ M2.smul μ (boost ν α β) = boost ν 1 0)) ∧
    (∀ i i' : Nat, i < p → i' < p → ∀ μ : Shell p, M2.smul μ (boost ν (ofNat i) 1) = boost ν (ofNat i') 1 → i = i') ∧
    (∀ i : Nat, ∀ μ : Shell p, μ ≠ 0 → M2.smul μ (boost ν (ofNat i) 1) ≠ boost ν 1 0) ∧
    (∀ i : Nat, ∀ μ : Shell p, M2.smul μ (boost ν 1 0) ≠ boost ν (ofNat i) 1) ∧
    natCount (fun _ => True) p + 1 = p + 1 :=
  (fld hp).hopf_counts ν

/-- 38:A9 — the frame triple on every prime shell (`Fld.frame_triple` under primality). -/
theorem frame_triple (hp : FRC.Nat.isPrime p) {ν : Shell p} (hν : ¬ ∃ y : Shell p, y * y = ν) :
    (∀ M : M2 p, M.det ≠ 0 → (M.a ≠ 0 ∨ M.c ≠ 0) ∧ M.act 1 0 = (M.a, M.c) ∧ (boost ν M.a M.c).act 1 0 = (M.a, M.c) ∧
      M.a * M.a + -(ν * (M.c * M.c)) ≠ 0 ∧
      M2.smul (M.a * M.a + -(ν * (M.c * M.c))) M =
        (boost ν M.a M.c).mul (borel (M.a * M.a + -(ν * (M.c * M.c))) (M.a * M.b + -(ν * (M.c * M.d))) M.det)) ∧
    (∀ a b e : Shell p, (borel a b e).act 1 0 = (a, 0)) ∧
    (∀ l α1 β1 a1 b1 e1 α2 β2 a2 b2 e2 : Shell p, l ≠ 0 → a1 ≠ 0 → a2 ≠ 0 → (α1 ≠ 0 ∨ β1 ≠ 0) →
      M2.smul l ((boost ν α1 β1).mul (borel a1 b1 e1)) = (boost ν α2 β2).mul (borel a2 b2 e2) →
      α1 * β2 = α2 * β1 ∧ e2 * a1 = e1 * a2 ∧ e2 * b1 = e1 * b2) :=
  (fld hp).frame_triple hν

end Prime
end Shell
end FRC
