import FrcCore.Frame

/-!
# FrcCore.Orbit — the generators form one orbit (2:B3; 1-algebra's torsor of primitive roots)

`Coprime u n` is taken in its invertible form — some `a < n` has `a·u ≡ 1 (mod n)` — which is decidable by
search and, for `n ≥ 1`, the same as `gcd(u, n) = 1` (Bezout); it is what every proof uses. Theorem:
`h` is primitive of order `n = p − 1` exactly when `h = g^u` with `u < n` coprime to `n`. No axioms.
-/

namespace FRC
namespace Shell

/-- `u` is invertible mod `n`: some `a < n` has `a·u % n = 1`. -/
def Coprime (u n : Nat) : Prop := ∃ a, a < n ∧ (a * u) % n = 1

instance (u n : Nat) : Decidable (Coprime u n) := decExistsLT (fun a => (a * u) % n = 1) n

namespace Frame
variable {p : Nat} [Pos p] {κ : Nat} {g : Shell p}

/-- A power of the drive with an invertible exponent is again primitive. -/
theorem primitive_pow_of_coprime (F : Frame p κ g) {u : Nat} (hu : Coprime u (p - 1)) :
    IsPrimitive (g ^ u) (p - 1) := by
  have hn := F.n_pos
  match hu with
  | ⟨a, _, ha⟩ =>
    refine ⟨by rw [pow_mul_comm, F.pow_n, one_pow], ?_⟩
    intro l hl hl0 hpow
    -- (g^u)^l = 1 gives (u·l) % n = 0; with a·u = n·q + 1, g^l = g^{l·a·u} = ((g^u)^l)^a = 1
    have h1 : (u * l) % (p - 1) = 0 := F.mod_eq_zero_of_pow_eq_one (by rw [pow_mul]; exact hpow)
    match FRC.Nat.mod_spec (p - 1) hn (a * u) with
    | ⟨q, hq⟩ =>
      rw [ha] at hq
      have e : l * (a * u) = (p - 1) * (q * l) + l := by
        rw [hq, Nat.left_distrib, Nat.mul_one, FRC.Nat.mul_left_comm, Nat.mul_comm l q]
      have h2 : g ^ (l * (a * u)) = 1 := by
        rw [show l * (a * u) = (u * l) * a by rw [Nat.mul_comm u l, FRC.Nat.mul_assoc, Nat.mul_comm a u]]
        rw [pow_mul, F.pow_eq_one_of_mod h1, one_pow]
      rw [e, pow_add, pow_mul, F.pow_n, one_pow, one_mul] at h2
      have := F.mod_eq_zero_of_pow_eq_one h2
      rw [FRC.Nat.mod_eq_of_lt hl] at this
      exact Nat.lt_irrefl 0 (this ▸ hl0)

/-- The frame of another primitive drive on the same shell. -/
theorem of_primitive (F : Frame p κ g) {h : Shell p} (hh : IsPrimitive h (p - 1)) : Frame p κ h :=
  ⟨F.cap, F.cap_pos, hh⟩

/-- 2:B3 (Props. 2.7, 4.5), 1-algebra's torsor — the primitive generators form one orbit: `h` is primitive
of order `p − 1` exactly when `h = g^u` for some `u < p − 1` coprime to `p − 1`. -/
theorem generator_orbit (F : Frame p κ g) (h : Shell p) :
    IsPrimitive h (p - 1) ↔ ∃ u, u < p - 1 ∧ Coprime u (p - 1) ∧ h = g ^ u := by
  have hn := F.n_pos
  constructor
  · intro hh
    have Fh : Frame p κ h := F.of_primitive hh
    have hh0 : h ≠ 0 := Fh.g_ne_zero
    match F.eq_pow_of_ne_zero hh0 with
    | ⟨u, hu, e⟩ =>
      refine ⟨u, hu, ?_, e.symm⟩
      -- g is a power of h: g = h^v; then g^{u v} = g, so u·v ≡ 1 (mod n)
      match Fh.eq_pow_of_ne_zero F.g_ne_zero with
      | ⟨v, hv, ev⟩ =>
        refine ⟨v, hv, ?_⟩
        have e1 : g ^ (v * u) = g ^ 1 := by
          rw [pow_one, Nat.mul_comm v u, pow_mul, e, ev]
        have h1n : 1 < p - 1 := by
          rw [F.n_eq]; exact Nat.lt_of_lt_of_le (by decide : 1 < 4 * 1) (Nat.mul_le_mul_left 4 F.cap_pos)
        have := F.pow_inj (Nat.mod_lt _ hn) h1n (by rw [← F.pow_mod, e1])
        exact this
  · intro ⟨u, _, hu, e⟩
    rw [e]; exact F.primitive_pow_of_coprime hu

/-- 1:G1, the finitary core (Fermat): every residue satisfies `x^p = x` — the polynomial `X^p − X` vanishes on
the whole shell, which is what the root test of 1:G1 rests on. -/
theorem fermat (F : Frame p κ g) (x : Shell p) : x ^ p = x := by
  have hp1 : x ^ p = x ^ (p - 1) * x :=
    congrArg (fun k => x ^ k) (FRC.Nat.sub_add_cancel Pos.pos).symm
  rw [hp1]
  exact match Shell.instDecidableEq x 0 with
    | isTrue e => by rw [e, mul_zero]
    | isFalse e => by
        match F.eq_pow_of_ne_zero e with
        | ⟨m, _, em⟩ => rw [← em, pow_mul_comm, F.pow_n, one_pow, one_mul]

end Frame
end Shell
end FRC
