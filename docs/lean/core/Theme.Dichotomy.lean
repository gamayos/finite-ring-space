import FrcCore.Theme.Lifts

/-!
# FrcCore.Theme.Dichotomy — the multiplicity dichotomy in trace form (the fourier theme)

The fourth file of the fourier theme (6-fourier's blueprint of 8 October 2026, task T05). With the Gauss sum
`G = Σ_k g^{k²}` over the cycle and its conjugate `Ḡ = Σ_k z^{k²}` (`z = g⁻¹`), the traces of the cardinal powers are
`Tr I = n = −1`, `Tr F = i G`, `Tr F² = Tr J = 2`, `Tr F³ = Tr FJ = i Ḡ`, and the trace of a projector is
`Tr Π_ℓ = q Σ_r w^{ℓr} Tr F^r` (`q = 4⁻¹`, `w = i⁻¹`). The product `G Ḡ = −2` comes from the substitution
`k = l + d` and the geometric sum. When `G = ε (1 + i)` with `ε = ±1` (the sign of the Gauss sum, the paper's import A3,
decided by the kernel on the six shells of its table), the conjugate sum is `Ḡ = −ε (1 − i)` (the conjugate law
`ε(g⁻¹) = −ε(g)`) and the four traces are `(κ, κ, κ+1, κ−1)` for `ε = 1` and `(κ+1, κ−1, κ, κ)` for `ε = −1`, read in
the field (6:C7). No axioms.
-/

namespace FRC
namespace Shell
namespace Frame

variable {p : Nat} [Pos p]

/-! ## Ring identities (generated; `RE.sound`, decided by the kernel) -/

theorem gauss_pt_id (A B D E : Shell p) :
    ((A * B) * (B * D)) * E = D * (B * B) + (A * E + -1) * ((D * B) * B) :=
  RE.sound (look [A, B, D, E])
    (.mul (.mul (.mul (.var 0) (.var 1)) (.mul (.var 1) (.var 2))) (.var 3))
    (.add (.mul (.var 2) (.mul (.var 1) (.var 1))) (.mul (.add (.mul (.var 0) (.var 3)) (.neg .one)) (.mul (.mul (.var 2) (.var 1)) (.var 1)))) (by decide +kernel)

theorem one_add_i_mul (i : Shell p) :
    (1 + i) * (1 + -i) = 1 + 1 + (i * i + 1) * (-1) :=
  RE.sound (look [i])
    (.mul (.add .one (.var 0)) (.add .one (.neg (.var 0))))
    (.add (.add .one .one) (.mul (.add (.mul (.var 0) (.var 0)) .one) (.neg .one))) (by decide +kernel)

theorem conj_sign_id (e i : Shell p) :
    (e * (1 + i)) * -(e * (1 + -i)) = -(1 + 1) + (e * e + -1) * -(1 + 1) + (i * i + 1) * (e * e) :=
  RE.sound (look [e, i])
    (.mul (.mul (.var 0) (.add .one (.var 1))) (.neg (.mul (.var 0) (.add .one (.neg (.var 1))))))
    (.add (.add (.neg (.add .one .one)) (.mul (.add (.mul (.var 0) (.var 0)) (.neg .one)) (.neg (.add .one .one)))) (.mul (.add (.mul (.var 1) (.var 1)) .one) (.mul (.var 0) (.var 0)))) (by decide +kernel)

theorem tuple_plus_0 (q i : Shell p) :
    q * -1 + (q * 1) * (i * (1 * (1 + i))) + (q * (1 * 1)) * (1 + 1) + (q * ((1 * 1) * 1)) * (i * -(1 * (1 + -i))) = -q + (i * i + 1) * ((1 + 1) * q) + ((1 + 1 + 1 + 1) * q + -1) * (0) :=
  RE.sound (look [q, i])
    (.add (.add (.add (.mul (.var 0) (.neg .one)) (.mul (.mul (.var 0) .one) (.mul (.var 1) (.mul .one (.add .one (.var 1)))))) (.mul (.mul (.var 0) (.mul .one .one)) (.add .one .one))) (.mul (.mul (.var 0) (.mul (.mul .one .one) .one)) (.mul (.var 1) (.neg (.mul .one (.add .one (.neg (.var 1))))))))
    (.add (.add (.neg (.var 0)) (.mul (.add (.mul (.var 1) (.var 1)) .one) (.mul (.add .one .one) (.var 0)))) (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.neg .one)) .zero)) (by decide +kernel)

theorem tuple_plus_1 (q i : Shell p) :
    q * -1 + (q * -i) * (i * (1 * (1 + i))) + (q * (-i * -i)) * (1 + 1) + (q * ((-i * -i) * -i)) * (i * -(1 * (1 + -i))) = -q + (i * i + 1) * (-(q * i * i * i) + q * i * i) + ((1 + 1 + 1 + 1) * q + -1) * (0) :=
  RE.sound (look [q, i])
    (.add (.add (.add (.mul (.var 0) (.neg .one)) (.mul (.mul (.var 0) (.neg (.var 1))) (.mul (.var 1) (.mul .one (.add .one (.var 1)))))) (.mul (.mul (.var 0) (.mul (.neg (.var 1)) (.neg (.var 1)))) (.add .one .one))) (.mul (.mul (.var 0) (.mul (.mul (.neg (.var 1)) (.neg (.var 1))) (.neg (.var 1)))) (.mul (.var 1) (.neg (.mul .one (.add .one (.neg (.var 1))))))))
    (.add (.add (.neg (.var 0)) (.mul (.add (.mul (.var 1) (.var 1)) .one) (.add (.neg (.mul (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.var 1))) (.mul (.mul (.var 0) (.var 1)) (.var 1))))) (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.neg .one)) .zero)) (by decide +kernel)

theorem tuple_plus_2 (q i : Shell p) :
    q * -1 + (q * (-i * -i)) * (i * (1 * (1 + i))) + (q * ((-i * -i) * (-i * -i))) * (1 + 1) + (q * (((-i * -i) * (-i * -i)) * (-i * -i))) * (i * -(1 * (1 + -i))) = -q + 1 + (i * i + 1) * (q * i * i * i * i * i * i + -(q * i * i * i * i * i) + -(q * i * i * i * i) + q * i * i * i + (1 + 1 + 1 + 1) * q * i * i + -((1 + 1 + 1 + 1) * q)) + ((1 + 1 + 1 + 1) * q + -1) * (1) :=
  RE.sound (look [q, i])
    (.add (.add (.add (.mul (.var 0) (.neg .one)) (.mul (.mul (.var 0) (.mul (.neg (.var 1)) (.neg (.var 1)))) (.mul (.var 1) (.mul .one (.add .one (.var 1)))))) (.mul (.mul (.var 0) (.mul (.mul (.neg (.var 1)) (.neg (.var 1))) (.mul (.neg (.var 1)) (.neg (.var 1))))) (.add .one .one))) (.mul (.mul (.var 0) (.mul (.mul (.mul (.neg (.var 1)) (.neg (.var 1))) (.mul (.neg (.var 1)) (.neg (.var 1)))) (.mul (.neg (.var 1)) (.neg (.var 1))))) (.mul (.var 1) (.neg (.mul .one (.add .one (.neg (.var 1))))))))
    (.add (.add (.add (.neg (.var 0)) .one) (.mul (.add (.mul (.var 1) (.var 1)) .one) (.add (.add (.add (.add (.add (.mul (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.neg (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1)))) (.neg (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.var 1)) (.var 1)))) (.mul (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.var 1))) (.mul (.mul (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.var 1)) (.var 1))) (.neg (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)))))) (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.neg .one)) .one)) (by decide +kernel)

theorem tuple_plus_3 (q i : Shell p) :
    q * -1 + (q * ((-i * -i) * -i)) * (i * (1 * (1 + i))) + (q * (((-i * -i) * -i) * ((-i * -i) * -i))) * (1 + 1) + (q * ((((-i * -i) * -i) * ((-i * -i) * -i)) * ((-i * -i) * -i))) * (i * -(1 * (1 + -i))) = -q + -1 + (i * i + 1) * (-(q * i * i * i * i * i * i * i * i * i) + q * i * i * i * i * i * i * i * i + q * i * i * i * i * i * i * i + -(q * i * i * i * i * i * i) + -(q * i * i * i * i * i) + (1 + 1 + 1) * q * i * i * i * i + -((1 + 1 + 1 + 1) * q * i * i) + (1 + 1 + 1 + 1) * q) + ((1 + 1 + 1 + 1) * q + -1) * (-1) :=
  RE.sound (look [q, i])
    (.add (.add (.add (.mul (.var 0) (.neg .one)) (.mul (.mul (.var 0) (.mul (.mul (.neg (.var 1)) (.neg (.var 1))) (.neg (.var 1)))) (.mul (.var 1) (.mul .one (.add .one (.var 1)))))) (.mul (.mul (.var 0) (.mul (.mul (.mul (.neg (.var 1)) (.neg (.var 1))) (.neg (.var 1))) (.mul (.mul (.neg (.var 1)) (.neg (.var 1))) (.neg (.var 1))))) (.add .one .one))) (.mul (.mul (.var 0) (.mul (.mul (.mul (.mul (.neg (.var 1)) (.neg (.var 1))) (.neg (.var 1))) (.mul (.mul (.neg (.var 1)) (.neg (.var 1))) (.neg (.var 1)))) (.mul (.mul (.neg (.var 1)) (.neg (.var 1))) (.neg (.var 1))))) (.mul (.var 1) (.neg (.mul .one (.add .one (.neg (.var 1))))))))
    (.add (.add (.add (.neg (.var 0)) (.neg .one)) (.mul (.add (.mul (.var 1) (.var 1)) .one) (.add (.add (.add (.add (.add (.add (.add (.neg (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1))) (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1))) (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1))) (.neg (.mul (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1)))) (.neg (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1)))) (.mul (.mul (.mul (.mul (.mul (.add (.add .one .one) .one) (.var 0)) (.var 1)) (.var 1)) (.var 1)) (.var 1))) (.neg (.mul (.mul (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.var 1)) (.var 1)))) (.mul (.add (.add (.add .one .one) .one) .one) (.var 0))))) (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.neg .one)) (.neg .one))) (by decide +kernel)

theorem tuple_minus_0 (q i : Shell p) :
    q * -1 + (q * 1) * (i * (-1 * (1 + i))) + (q * (1 * 1)) * (1 + 1) + (q * ((1 * 1) * 1)) * (i * -(-1 * (1 + -i))) = -q + 1 + (i * i + 1) * (-((1 + 1) * q)) + ((1 + 1 + 1 + 1) * q + -1) * (1) :=
  RE.sound (look [q, i])
    (.add (.add (.add (.mul (.var 0) (.neg .one)) (.mul (.mul (.var 0) .one) (.mul (.var 1) (.mul (.neg .one) (.add .one (.var 1)))))) (.mul (.mul (.var 0) (.mul .one .one)) (.add .one .one))) (.mul (.mul (.var 0) (.mul (.mul .one .one) .one)) (.mul (.var 1) (.neg (.mul (.neg .one) (.add .one (.neg (.var 1))))))))
    (.add (.add (.add (.neg (.var 0)) .one) (.mul (.add (.mul (.var 1) (.var 1)) .one) (.neg (.mul (.add .one .one) (.var 0))))) (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.neg .one)) .one)) (by decide +kernel)

theorem tuple_minus_1 (q i : Shell p) :
    q * -1 + (q * -i) * (i * (-1 * (1 + i))) + (q * (-i * -i)) * (1 + 1) + (q * ((-i * -i) * -i)) * (i * -(-1 * (1 + -i))) = -q + -1 + (i * i + 1) * (q * i * i * i + -(q * i * i) + (1 + 1 + 1 + 1) * q) + ((1 + 1 + 1 + 1) * q + -1) * (-1) :=
  RE.sound (look [q, i])
    (.add (.add (.add (.mul (.var 0) (.neg .one)) (.mul (.mul (.var 0) (.neg (.var 1))) (.mul (.var 1) (.mul (.neg .one) (.add .one (.var 1)))))) (.mul (.mul (.var 0) (.mul (.neg (.var 1)) (.neg (.var 1)))) (.add .one .one))) (.mul (.mul (.var 0) (.mul (.mul (.neg (.var 1)) (.neg (.var 1))) (.neg (.var 1)))) (.mul (.var 1) (.neg (.mul (.neg .one) (.add .one (.neg (.var 1))))))))
    (.add (.add (.add (.neg (.var 0)) (.neg .one)) (.mul (.add (.mul (.var 1) (.var 1)) .one) (.add (.add (.mul (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.var 1)) (.neg (.mul (.mul (.var 0) (.var 1)) (.var 1)))) (.mul (.add (.add (.add .one .one) .one) .one) (.var 0))))) (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.neg .one)) (.neg .one))) (by decide +kernel)

theorem tuple_minus_2 (q i : Shell p) :
    q * -1 + (q * (-i * -i)) * (i * (-1 * (1 + i))) + (q * ((-i * -i) * (-i * -i))) * (1 + 1) + (q * (((-i * -i) * (-i * -i)) * (-i * -i))) * (i * -(-1 * (1 + -i))) = -q + (i * i + 1) * (-(q * i * i * i * i * i * i) + q * i * i * i * i * i + q * i * i * i * i + -(q * i * i * i)) + ((1 + 1 + 1 + 1) * q + -1) * (0) :=
  RE.sound (look [q, i])
    (.add (.add (.add (.mul (.var 0) (.neg .one)) (.mul (.mul (.var 0) (.mul (.neg (.var 1)) (.neg (.var 1)))) (.mul (.var 1) (.mul (.neg .one) (.add .one (.var 1)))))) (.mul (.mul (.var 0) (.mul (.mul (.neg (.var 1)) (.neg (.var 1))) (.mul (.neg (.var 1)) (.neg (.var 1))))) (.add .one .one))) (.mul (.mul (.var 0) (.mul (.mul (.mul (.neg (.var 1)) (.neg (.var 1))) (.mul (.neg (.var 1)) (.neg (.var 1)))) (.mul (.neg (.var 1)) (.neg (.var 1))))) (.mul (.var 1) (.neg (.mul (.neg .one) (.add .one (.neg (.var 1))))))))
    (.add (.add (.neg (.var 0)) (.mul (.add (.mul (.var 1) (.var 1)) .one) (.add (.add (.add (.neg (.mul (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1))) (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1))) (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.var 1)) (.var 1))) (.neg (.mul (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.var 1)))))) (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.neg .one)) .zero)) (by decide +kernel)

theorem tuple_minus_3 (q i : Shell p) :
    q * -1 + (q * ((-i * -i) * -i)) * (i * (-1 * (1 + i))) + (q * (((-i * -i) * -i) * ((-i * -i) * -i))) * (1 + 1) + (q * ((((-i * -i) * -i) * ((-i * -i) * -i)) * ((-i * -i) * -i))) * (i * -(-1 * (1 + -i))) = -q + (i * i + 1) * (q * i * i * i * i * i * i * i * i * i + -(q * i * i * i * i * i * i * i * i) + -(q * i * i * i * i * i * i * i) + q * i * i * i * i * i * i + q * i * i * i * i * i + q * i * i * i * i) + ((1 + 1 + 1 + 1) * q + -1) * (0) :=
  RE.sound (look [q, i])
    (.add (.add (.add (.mul (.var 0) (.neg .one)) (.mul (.mul (.var 0) (.mul (.mul (.neg (.var 1)) (.neg (.var 1))) (.neg (.var 1)))) (.mul (.var 1) (.mul (.neg .one) (.add .one (.var 1)))))) (.mul (.mul (.var 0) (.mul (.mul (.mul (.neg (.var 1)) (.neg (.var 1))) (.neg (.var 1))) (.mul (.mul (.neg (.var 1)) (.neg (.var 1))) (.neg (.var 1))))) (.add .one .one))) (.mul (.mul (.var 0) (.mul (.mul (.mul (.mul (.neg (.var 1)) (.neg (.var 1))) (.neg (.var 1))) (.mul (.mul (.neg (.var 1)) (.neg (.var 1))) (.neg (.var 1)))) (.mul (.mul (.neg (.var 1)) (.neg (.var 1))) (.neg (.var 1))))) (.mul (.var 1) (.neg (.mul (.neg .one) (.add .one (.neg (.var 1))))))))
    (.add (.add (.neg (.var 0)) (.mul (.add (.mul (.var 1) (.var 1)) .one) (.add (.add (.add (.add (.add (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.neg (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1)))) (.neg (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1)))) (.mul (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1))) (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1))) (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.var 1)) (.var 1))))) (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.neg .one)) .zero)) (by decide +kernel)

variable {κ : Nat} {g : Shell p}

/-- The quadratic Gauss sum over the cycle, `G = Σ_{k<n} g^{k²}`; `Tr W = G`. -/
def gauss (g : Shell p) (n : Nat) : Shell p := sumRange (fun k => g ^ (k * k)) n

/-! ## The traces of the four basis matrices -/

theorem trace_comb (c0 c1 c2 c3 : Shell p) :
    sumRange (fun k => comb g κ c0 c1 c2 c3 k k) (p - 1) =
      c0 * trace (idm : Nat → Nat → Shell p) (p - 1) + c1 * trace (Fmat g κ) (p - 1) +
        c2 * trace (J (p - 1) : Nat → Nat → Shell p) (p - 1) + c3 * trace (FJ g κ) (p - 1) := by
  show sumRange (fun k => c0 * idm k k + c1 * Fmat g κ k k + c2 * J (p - 1) k k + c3 * FJ g κ k k) (p - 1) =
    c0 * sumRange (fun k => idm k k) (p - 1) + c1 * sumRange (fun k => Fmat g κ k k) (p - 1) +
      c2 * sumRange (fun k => J (p - 1) k k) (p - 1) + c3 * sumRange (fun k => FJ g κ k k) (p - 1)
  rw [sum_add, sum_add, sum_add, sum_mul_left, sum_mul_left, sum_mul_left, sum_mul_left]

theorem trace_idm (F : Frame p κ g) : trace (idm : Nat → Nat → Shell p) (p - 1) = -1 := by
  show sumRange (fun k => idm k k) (p - 1) = -1
  rw [sum_congr _ (fun k _ => idm_self k), sum_const, mul_one, F.ofNat_n]

theorem trace_Fmat : trace (Fmat g κ) (p - 1) = quarterTurn g κ * gauss g (p - 1) :=
  sum_mul_left (fun k => g ^ (k * k)) (quarterTurn g κ) (p - 1)

theorem J_diag (F : Frame p κ g) {k : Nat} (hk : k < p - 1) : (J (p - 1) k k : Shell p) = idm k 0 + idm k (2 * κ) := by
  show (if (k + k) % (p - 1) = 0 then (1 : Shell p) else 0) = (if k = 0 then 1 else 0) + (if k = 2 * κ then 1 else 0)
  match Nat.decEq ((k + k) % (p - 1)) 0 with
  | isTrue h =>
    rw [ite_eq_left h]
    match double_mod_n F hk h with
    | Or.inl e =>
      rw [ite_eq_left e, ite_eq_right (fun e2 => absurd F.two_kappa_pos (by rw [← e2, e]; exact Nat.lt_irrefl 0)), add_zero]
    | Or.inr e =>
      rw [ite_eq_right (fun e0 => absurd F.two_kappa_pos (by rw [← e, e0]; exact Nat.lt_irrefl 0)), ite_eq_left e, zero_add]
  | isFalse h =>
    rw [ite_eq_right h, ite_eq_right (fun e => h (by rw [e]; exact FRC.Nat.zero_mod _)),
      ite_eq_right (fun e => h (by rw [e, F.four_kappa]; exact FRC.Nat.mod_self _ F.n_pos)), add_zero]

/-- `Tr J = 2`: the reversal fixes the two sites `0` and `2κ`. -/
theorem trace_J (F : Frame p κ g) : trace (J (p - 1) : Nat → Nat → Shell p) (p - 1) = 1 + 1 := by
  show sumRange (fun k => (J (p - 1) k k : Shell p)) (p - 1) = 1 + 1
  rw [sum_congr _ (fun k hk => J_diag F hk), sum_add, sum_eq_single F.n_pos (fun l _ hne => idm_ne hne),
    sum_eq_single F.two_kappa_lt (fun l _ hne => idm_ne hne), idm_self, idm_self]

/-- `g^{(−k) k} = z^{k²}`: the reversed exponent is the conjugate's. -/
theorem W_rev_diag (F : Frame p κ g) {z : Shell p} (hz : g * z = 1) {k : Nat} (hk : k < p - 1) :
    g ^ (rev (p - 1) k * k) = z ^ (k * k) := by
  have hn := F.n_pos
  apply inv_unique (y := g ^ (k * k))
  · rw [← pow_add, ← FRC.Nat.add_mul, F.pow_mod, ← FRC.Nat.mod_mul_mod _ _ _ hn, rev_add_mod hk, Nat.zero_mul,
      FRC.Nat.zero_mod, pow_zero]
  · rw [← mul_pow, mul_comm, hz, one_pow]

theorem trace_FJ (F : Frame p κ g) {z : Shell p} (hz : g * z = 1) :
    trace (FJ g κ) (p - 1) = quarterTurn g κ * gauss z (p - 1) := by
  show sumRange (fun k => quarterTurn g κ * g ^ (rev (p - 1) k * k)) (p - 1) =
    quarterTurn g κ * sumRange (fun k => z ^ (k * k)) (p - 1)
  rw [sum_congr _ (fun k hk => by rw [W_rev_diag F hz hk])]
  exact sum_mul_left _ _ _

/-- 6:C7, the traces of the cardinal powers: `Tr I = −1`, `Tr F = i G`, `Tr F² = Tr J = 2`, `Tr F³ = Tr FJ = i Ḡ`. -/
theorem trace_powers (F : Frame p κ g) {z : Shell p} (hz : g * z = 1) :
    trace (idm : Nat → Nat → Shell p) (p - 1) = -1 ∧ trace (Fmat g κ) (p - 1) = quarterTurn g κ * gauss g (p - 1) ∧
      trace (J (p - 1) : Nat → Nat → Shell p) (p - 1) = 1 + 1 ∧
      trace (FJ g κ) (p - 1) = quarterTurn g κ * gauss z (p - 1) :=
  ⟨trace_idm F, trace_Fmat, trace_J F, trace_FJ F hz⟩

/-- 6:C7, the trace of a projector in trace form: `Tr Π_ℓ = q (Tr I + u Tr F + u² Tr J + u³ Tr FJ)`, `u = w^ℓ`, i.e.
`Tr Π_ℓ = ¼ Σ_r i^{−ℓr} Tr F^r`. -/
theorem trace_proj (F : Frame p κ g) {z : Shell p} (hz : g * z = 1) (ℓ : Nat) :
    trace (proj g κ ℓ) (p - 1) =
      -(ofNat κ) * -1 + -(ofNat κ) * (-(quarterTurn g κ)) ^ ℓ * (quarterTurn g κ * gauss g (p - 1)) +
        -(ofNat κ) * ((-(quarterTurn g κ)) ^ ℓ * (-(quarterTurn g κ)) ^ ℓ) * (1 + 1) +
        -(ofNat κ) * ((-(quarterTurn g κ)) ^ ℓ * (-(quarterTurn g κ)) ^ ℓ * (-(quarterTurn g κ)) ^ ℓ) *
          (quarterTurn g κ * gauss z (p - 1)) := by
  show sumRange (fun k => proj g κ ℓ k k) (p - 1) = _
  rw [sum_congr _ (fun k _ => proj_eq ℓ k k), trace_comb, trace_idm F, trace_Fmat, trace_J F, trace_FJ F hz]

/-! ## `G Ḡ = −2` -/

/-- The sums commute. -/
theorem sum_swap (f : Nat → Nat → Shell p) (n : Nat) : ∀ m : Nat,
    sumRange (fun l => sumRange (fun d => f l d) n) m = sumRange (fun d => sumRange (fun l => f l d) m) n
  | 0 => (sum_zero n (fun _ _ => rfl)).symm
  | m + 1 => by
    show sumRange (fun l => sumRange (fun d => f l d) n) m + sumRange (fun d => f m d) n =
      sumRange (fun d => sumRange (fun l => f l d) m + f m d) n
    rw [sum_swap f n m, ← sum_add]

/-- The shift `d ↦ (l + d) % n` is injective on the cycle. -/
theorem shift_inj (F : Frame p κ g) {l : Nat} (hl : l < p - 1) (i j : Nat) (hi : i < p - 1) (hj : j < p - 1)
    (h : (l + i) % (p - 1) = (l + j) % (p - 1)) : i = j := by
  have hn := F.n_pos
  have key : ∀ i, i < p - 1 → i = (rev (p - 1) l + (l + i) % (p - 1)) % (p - 1) := fun i hi => by
    rw [FRC.Nat.add_mod_mod _ _ _ hn, ← Nat.add_assoc, ← FRC.Nat.mod_add_mod _ _ _ hn, rev_add_mod hl, Nat.zero_add,
      FRC.Nat.mod_eq_of_lt hi]
  rw [key i hi, key j hj, h]

/-- The term of the double sum after the substitution `k = l + d`: `g^{(l+d)²} z^{l²} = g^{d²} (g^{2d})^l`. -/
theorem gauss_pt {z : Shell p} (hz : g * z = 1) (l d : Nat) :
    g ^ ((l + d) * (l + d)) * z ^ (l * l) = g ^ (d * d) * (g ^ (d + d)) ^ l := by
  have hAE : g ^ (l * l) * z ^ (l * l) + -1 = 0 := by rw [← mul_pow, hz, one_pow, add_neg]
  rw [Nat.add_mul, pow_add g (l * (l + d)), Nat.mul_add, Nat.mul_add, pow_add g (l * l), pow_add g (d * l),
    ← pow_mul g (d + d) l, Nat.add_mul d d l, pow_add g (d * l), Nat.mul_comm l d]
  exact red1 (gauss_pt_id _ _ _ _) hAE

/-- The inner geometric sum: `Σ_{l<n} (g^{2d})^l` is `−1` at `d ∈ {0, 2κ}` and `0` elsewhere. -/
theorem gauss_inner (F : Frame p κ g) {d : Nat} (hd : d < p - 1) :
    g ^ (d * d) * sumRange (fun l => (g ^ (d + d)) ^ l) (p - 1) = -(idm d 0 + idm d (2 * κ)) := by
  match Nat.decEq ((d + d) % (p - 1)) 0 with
  | isTrue h =>
    have h1 : g ^ (d + d) = 1 := F.pow_eq_one_of_mod h
    have hs : sumRange (fun l => (g ^ (d + d)) ^ l) (p - 1) = -1 := by
      rw [sum_congr _ (fun l _ => by rw [h1, one_pow]), sum_const, mul_one, F.ofNat_n]
    rw [hs]
    match double_mod_n F hd h with
    | Or.inl e =>
      rw [e, idm_self, idm_ne (fun e2 => absurd F.two_kappa_pos (by rw [← e2]; exact Nat.lt_irrefl 0)), add_zero,
        Nat.mul_zero, pow_zero, one_mul]
    | Or.inr e =>
      rw [e, idm_ne (fun e0 => absurd F.two_kappa_pos (by rw [e0]; exact Nat.lt_irrefl 0)), idm_self, zero_add,
        pow_mul, F.half_period, pow_mul, pow_two, neg_mul_neg, one_mul, one_pow, one_mul]
  | isFalse h =>
    rw [F.geom_sum_eq_zero _ (by rw [pow_mul_comm, F.pow_n, one_pow]) (fun e => h (F.mod_eq_zero_of_pow_eq_one e)),
      mul_zero, idm_ne (fun e => h (by rw [e]; exact FRC.Nat.zero_mod _)),
      idm_ne (fun e => h (by rw [e, F.four_kappa]; exact FRC.Nat.mod_self _ F.n_pos)), add_zero, neg_zero]

/-- 6:C7, `G Ḡ = −2`: the substitution `k = l + d` and the geometric sum over `l`. -/
theorem gauss_mul (F : Frame p κ g) {z : Shell p} (hz : g * z = 1) :
    gauss g (p - 1) * gauss z (p - 1) = -(1 + 1) := by
  have hn := F.n_pos
  show sumRange (fun k => g ^ (k * k)) (p - 1) * sumRange (fun l => z ^ (l * l)) (p - 1) = -(1 + 1)
  rw [← sum_mul_left]
  rw [sum_congr _ (fun l hl => by
    show sumRange (fun k => g ^ (k * k)) (p - 1) * z ^ (l * l) =
      sumRange (fun d => g ^ (d * d) * (g ^ (d + d)) ^ l) (p - 1)
    rw [← sum_mul_right, ← sum_perm (fun k => g ^ (k * k) * z ^ (l * l)) (fun d => (l + d) % (p - 1)) (p - 1)
      (fun d _ => FRC.Nat.mod_lt' _ hn) (shift_inj F hl)]
    exact sum_congr _ (fun d _ => by
      show g ^ ((l + d) % (p - 1) * ((l + d) % (p - 1))) * z ^ (l * l) = g ^ (d * d) * (g ^ (d + d)) ^ l
      rw [F.pow_mod ((l + d) % (p - 1) * ((l + d) % (p - 1))), FRC.Nat.mod_mul_mod _ _ _ hn,
        FRC.Nat.mul_mod_mod _ _ _ hn, ← F.pow_mod, gauss_pt hz l d]))]
  rw [sum_swap (fun l d => g ^ (d * d) * (g ^ (d + d)) ^ l) (p - 1) (p - 1)]
  rw [sum_congr _ (fun d hd => by rw [sum_mul_left, gauss_inner F hd]), sum_neg, sum_add,
    sum_eq_single F.n_pos (fun l _ hne => idm_ne hne), sum_eq_single F.two_kappa_lt (fun l _ hne => idm_ne hne),
    idm_self, idm_self]

/-! ## The sign and the two tuples (6:C7) -/

/-- `G ≠ 0`, since `G Ḡ = −2`. -/
theorem gauss_ne_zero (F : Frame p κ g) {z : Shell p} (hz : g * z = 1) : gauss g (p - 1) ≠ 0 := fun h =>
  F.two_ne_zero (by
    have e := gauss_mul F hz
    rw [h, zero_mul] at e
    rw [two_eq_one_add_one (p := p), ← neg_neg (1 + 1 : Shell p), ← e, neg_zero])

/-- 6:C7, the conjugate law: when `G = ε (1 + i)` with `ε² = 1`, the conjugate frame's Gauss sum is
`Ḡ = −ε (1 − i)`, i.e. `ε(g⁻¹) = −ε(g)`. -/
theorem gauss_conj (F : Frame p κ g) {z : Shell p} (hz : g * z = 1) {ε : Shell p} (hε : ε * ε = 1)
    (hG : gauss g (p - 1) = ε * (1 + quarterTurn g κ)) :
    gauss z (p - 1) = -(ε * (1 + -(quarterTurn g κ))) := by
  apply F.mul_left_cancel (gauss_ne_zero F hz)
  rw [gauss_mul F hz, hG, conj_sign_id, hε, add_neg, zero_mul, add_zero, hii F, zero_mul, add_zero]

theorem sign_sq {ε : Shell p} (h : ε = 1 ∨ ε = -1) : ε * ε = 1 := by
  match h with
  | Or.inl e => rw [e, one_mul]
  | Or.inr e => rw [e, neg_mul_neg, one_mul]

/-- 6:C7, the dichotomy: under `G = ε (1 + i)` the traces of the projectors are `(κ, κ, κ+1, κ−1)` for `ε = 1` and
`(κ+1, κ−1, κ, κ)` for `ε = −1`, read in the field. -/
theorem trace_tuples (F : Frame p κ g) {z : Shell p} (hz : g * z = 1) {ε : Shell p} (hε : ε = 1 ∨ ε = -1)
    (hG : gauss g (p - 1) = ε * (1 + quarterTurn g κ)) :
    (ε = 1 ∧ trace (proj g κ 0) (p - 1) = ofNat κ ∧ trace (proj g κ 1) (p - 1) = ofNat κ ∧
        trace (proj g κ 2) (p - 1) = ofNat κ + 1 ∧ trace (proj g κ 3) (p - 1) = ofNat κ + -1) ∨
      (ε = -1 ∧ trace (proj g κ 0) (p - 1) = ofNat κ + 1 ∧ trace (proj g κ 1) (p - 1) = ofNat κ + -1 ∧
        trace (proj g κ 2) (p - 1) = ofNat κ ∧ trace (proj g κ 3) (p - 1) = ofNat κ) := by
  have hGb := gauss_conj F hz (sign_sq hε) hG
  have t0 := trace_proj F hz 0
  have t1 := trace_proj F hz 1
  have t2 := trace_proj F hz 2
  have t3 := trace_proj F hz 3
  rw [pow_zero, hG, hGb] at t0
  rw [pow_one, hG, hGb] at t1
  rw [pow_two, hG, hGb] at t2
  rw [pow_succ, pow_two, hG, hGb] at t3
  have hq := hq F
  have hi := hii F
  have nn : ∀ b : Shell p, -(-(ofNat κ)) + b = ofNat κ + b := fun b => by rw [neg_neg]
  match hε with
  | Or.inl e =>
    subst e
    refine Or.inl ⟨rfl, ?_, ?_, ?_, ?_⟩
    · rw [t0]; exact (red2 (tuple_plus_0 _ _) hi hq).trans (neg_neg _)
    · rw [t1]; exact (red2 (tuple_plus_1 _ _) hi hq).trans (neg_neg _)
    · rw [t2]; exact (red2 (tuple_plus_2 _ _) hi hq).trans (nn 1)
    · rw [t3]; exact (red2 (tuple_plus_3 _ _) hi hq).trans (nn (-1))
  | Or.inr e =>
    subst e
    refine Or.inr ⟨rfl, ?_, ?_, ?_, ?_⟩
    · rw [t0]; exact (red2 (tuple_minus_0 _ _) hi hq).trans (nn 1)
    · rw [t1]; exact (red2 (tuple_minus_1 _ _) hi hq).trans (nn (-1))
    · rw [t2]; exact (red2 (tuple_minus_2 _ _) hi hq).trans (neg_neg _)
    · rw [t3]; exact (red2 (tuple_minus_3 _ _) hi hq).trans (neg_neg _)

/-! The six shells of the paper's table, decided by the kernel: the sign of the Gauss sum and the tuple of traces. -/

theorem frame17_three : Frame 17 4 (3 : Shell 17) := ⟨rfl, Nat.zero_lt_succ 3, by decide⟩
theorem frame29_two : Frame 29 7 (2 : Shell 29) := ⟨rfl, Nat.zero_lt_succ 6, by decide⟩
theorem frame37_two : Frame 37 9 (2 : Shell 37) := ⟨rfl, Nat.zero_lt_succ 8, by decide⟩
theorem frame41_six : Frame 41 10 (6 : Shell 41) := ⟨rfl, Nat.zero_lt_succ 9, by decide⟩

/-- 6:C7, the sign on the six shells: `G = ε (1 + i)` with `ε = −1` at `(5, 2)` and `ε = +1` at `(13, 2)`, `(17, 3)`,
`(29, 2)`, `(37, 2)`, `(41, 6)`. -/
theorem six_signs :
    gauss (2 : Shell 5) 4 = -1 * (1 + quarterTurn 2 1) ∧ gauss (2 : Shell 13) 12 = 1 * (1 + quarterTurn 2 3) ∧
    gauss (3 : Shell 17) 16 = 1 * (1 + quarterTurn 3 4) ∧ gauss (2 : Shell 29) 28 = 1 * (1 + quarterTurn 2 7) ∧
    gauss (2 : Shell 37) 36 = 1 * (1 + quarterTurn 2 9) ∧ gauss (6 : Shell 41) 40 = 1 * (1 + quarterTurn 6 10) := by
  decide +kernel

/-- 6:C7, the tuples on the six shells: `(2, 0, 1, 1)` at `p = 5` (`ε = −1`) and `(κ, κ, κ+1, κ−1)` at the five others. -/
theorem six_tuples :
    (trace (proj (2 : Shell 5) 1 0) 4 = 2 ∧ trace (proj (2 : Shell 5) 1 1) 4 = 0 ∧
      trace (proj (2 : Shell 5) 1 2) 4 = 1 ∧ trace (proj (2 : Shell 5) 1 3) 4 = 1) ∧
    (trace (proj (2 : Shell 13) 3 0) 12 = 3 ∧ trace (proj (2 : Shell 13) 3 1) 12 = 3 ∧
      trace (proj (2 : Shell 13) 3 2) 12 = 4 ∧ trace (proj (2 : Shell 13) 3 3) 12 = 2) ∧
    (trace (proj (3 : Shell 17) 4 0) 16 = 4 ∧ trace (proj (3 : Shell 17) 4 1) 16 = 4 ∧
      trace (proj (3 : Shell 17) 4 2) 16 = 5 ∧ trace (proj (3 : Shell 17) 4 3) 16 = 3) ∧
    (trace (proj (2 : Shell 29) 7 0) 28 = 7 ∧ trace (proj (2 : Shell 29) 7 1) 28 = 7 ∧
      trace (proj (2 : Shell 29) 7 2) 28 = 8 ∧ trace (proj (2 : Shell 29) 7 3) 28 = 6) ∧
    (trace (proj (2 : Shell 37) 9 0) 36 = 9 ∧ trace (proj (2 : Shell 37) 9 1) 36 = 9 ∧
      trace (proj (2 : Shell 37) 9 2) 36 = 10 ∧ trace (proj (2 : Shell 37) 9 3) 36 = 8) ∧
    (trace (proj (6 : Shell 41) 10 0) 40 = 10 ∧ trace (proj (6 : Shell 41) 10 1) 40 = 10 ∧
      trace (proj (6 : Shell 41) 10 2) 40 = 11 ∧ trace (proj (6 : Shell 41) 10 3) 40 = 9) := by
  decide +kernel

end Frame
end Shell
end FRC
