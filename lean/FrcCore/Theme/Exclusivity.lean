import FrcCore.Theme.Spectra

/-!
# FrcCore.Theme.Exclusivity — cardinal exclusivity: no intermediate conjugate of the shift is monomial (the fourier theme)

The eighth file of the fourier theme (6-fourier's blueprint of 8 October 2026, task T09). With `F^{[s]} = Σ_r c_r F^r`
(`frft_eq`) and `F^{[−s]} = F^{[n−s]} = Σ_r c'_r F^r`, the entry `(0, j)` of `F^{[s]} σ F^{[−s]}` off the three sites
`j ∈ {n−1, 0, 1}` is `i [(c₀ + c₂)(c'₃ x + c'₁ x⁻¹) + (c₁ + c₃)(c'₀ + c'₂)]` with `x = g^j`: row 0 of `F^{[s]} σ` is
`(c₀ + c₂) δ_{n−1} + (c₁ + c₃) i`, the last row of `F^{[−s]}` is `i (c'₁ x⁻¹ + c'₃ x)` off the sites, and its column
sums are `c'₀ + c'₂` by the geometric sum. So `x` times the entry is a quadratic in `x` with leading coefficient
`i (c₀ + c₂) c'₃`, nonzero for `s ∉ {0, κ, 2κ, 3κ}` (`c₀ + c₂ = ½ (1 + z_s²)` vanishes only at `z_s = ±i`; `c'₃` is a
geometric sum of a nontrivial root), and a quadratic has at most two roots: the row vanishes at no three distinct indices
off the sites (6:E8; the paper counts at least `4κ − 5` nonzero entries from this, a count not stated here). No axioms.
-/

namespace FRC
namespace Shell
namespace Frame

variable {p : Nat} [Pos p]

/-! ## Ring identities (generated; `RE.sound`, decided by the kernel) -/

theorem quad_diff_id (a b c x1 x2 : Shell p) :
    a * (x1 * x1) + b * x1 + c + -(a * (x2 * x2) + b * x2 + c) = (x1 + -x2) * (a * (x1 + x2) + b) :=
  RE.sound (look [a, b, c, x1, x2])
    (.add (.add (.add (.mul (.var 0) (.mul (.var 3) (.var 3))) (.mul (.var 1) (.var 3))) (.var 2)) (.neg (.add (.add (.mul (.var 0) (.mul (.var 4) (.var 4))) (.mul (.var 1) (.var 4))) (.var 2))))
    (.mul (.add (.var 3) (.neg (.var 4))) (.add (.mul (.var 0) (.add (.var 3) (.var 4))) (.var 1))) (by decide +kernel)

theorem quad_lin_id (a b x1 x2 x3 : Shell p) :
    a * (x1 + x2) + b + -(a * (x1 + x3) + b) = a * (x2 + -x3) :=
  RE.sound (look [a, b, x1, x2, x3])
    (.add (.add (.mul (.var 0) (.add (.var 2) (.var 3))) (.var 1)) (.neg (.add (.mul (.var 0) (.add (.var 2) (.var 4))) (.var 1))))
    (.mul (.var 0) (.add (.var 3) (.neg (.var 4)))) (by decide +kernel)

theorem row_quad_id (i s0 s1 d0 d1 d3 Z G : Shell p) :
    G * (s0 * ((d1 * i) * Z + (d3 * i) * G) + (s1 * i) * d0) = i * ((s0 * d3) * (G * G) + (s1 * d0) * G + s0 * d1) + (Z * G + -1) * (i * s0 * d1) :=
  RE.sound (look [i, s0, s1, d0, d1, d3, Z, G])
    (.mul (.var 7) (.add (.mul (.var 1) (.add (.mul (.mul (.var 4) (.var 0)) (.var 6)) (.mul (.mul (.var 5) (.var 0)) (.var 7)))) (.mul (.mul (.var 2) (.var 0)) (.var 3))))
    (.add (.mul (.var 0) (.add (.add (.mul (.mul (.var 1) (.var 5)) (.mul (.var 7) (.var 7))) (.mul (.mul (.var 2) (.var 3)) (.var 7))) (.mul (.var 1) (.var 4)))) (.mul (.add (.mul (.var 6) (.var 7)) (.neg .one)) (.mul (.mul (.var 0) (.var 1)) (.var 4)))) (by decide +kernel)

/-- 6:E8, `c₀ + c₂ = ½ (1 + u²)`, `u = z^s`, i.e. `½ (1 + g^{−2s})`. -/
theorem even_coeff_id (q jj u : Shell p) :
    NF0 q jj u + NF2 q jj u = (q + q) * (1 + u * u) :=
  RE.sound (look [q, jj, u])
    (.add (.mul (.var 0) (.add (.add (.add .one (.var 2)) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 2) (.var 2)) (.var 2)))) (.mul (.var 0) (.add (.add (.add .one (.neg (.var 2))) (.mul (.var 2) (.var 2))) (.neg (.mul (.mul (.var 2) (.var 2)) (.var 2))))))
    (.mul (.add (.var 0) (.var 0)) (.add .one (.mul (.var 2) (.var 2)))) (by decide +kernel)

theorem odd_coeff_id (q jj u : Shell p) :
    NF3 q jj u = q * (1 + u * ((jj * jj) * jj) + (u * ((jj * jj) * jj)) * (u * ((jj * jj) * jj)) + ((u * ((jj * jj) * jj)) * (u * ((jj * jj) * jj))) * (u * ((jj * jj) * jj))) + (jj * jj + 1) * (-(q * jj * jj * jj * jj * jj * jj * jj * u * u * u) + q * jj * jj * jj * jj * jj * u * u * u + -(q * jj * jj * jj * jj * u * u) + -(q * jj * jj * jj * u * u * u) + q * jj * jj * u * u + q * jj * u * u * u + -(q * jj * u) + -(q * u * u)) :=
  RE.sound (look [q, jj, u])
    (.mul (.var 0) (.add (.add (.add .one (.neg (.mul (.var 1) (.var 2)))) (.neg (.mul (.var 2) (.var 2)))) (.mul (.var 1) (.mul (.mul (.var 2) (.var 2)) (.var 2)))))
    (.add (.mul (.var 0) (.add (.add (.add .one (.mul (.var 2) (.mul (.mul (.var 1) (.var 1)) (.var 1)))) (.mul (.mul (.var 2) (.mul (.mul (.var 1) (.var 1)) (.var 1))) (.mul (.var 2) (.mul (.mul (.var 1) (.var 1)) (.var 1))))) (.mul (.mul (.mul (.var 2) (.mul (.mul (.var 1) (.var 1)) (.var 1))) (.mul (.var 2) (.mul (.mul (.var 1) (.var 1)) (.var 1)))) (.mul (.var 2) (.mul (.mul (.var 1) (.var 1)) (.var 1)))))) (.mul (.add (.mul (.var 1) (.var 1)) .one) (.add (.add (.add (.add (.add (.add (.add (.neg (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 2)) (.var 2)) (.var 2))) (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 2)) (.var 2)) (.var 2))) (.neg (.mul (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 2)) (.var 2)))) (.neg (.mul (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.var 1)) (.var 2)) (.var 2)) (.var 2)))) (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.var 2)) (.var 2))) (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 2)) (.var 2))) (.neg (.mul (.mul (.var 0) (.var 1)) (.var 2)))) (.neg (.mul (.mul (.var 0) (.var 2)) (.var 2)))))) (by decide +kernel)

theorem geom4_id (y : Shell p) :
    (y + -1) * (1 + y + y * y + (y * y) * y) = ((y * y) * y) * y + -1 :=
  RE.sound (look [y])
    (.mul (.add (.var 0) (.neg .one)) (.add (.add (.add .one (.var 0)) (.mul (.var 0) (.var 0))) (.mul (.mul (.var 0) (.var 0)) (.var 0))))
    (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.var 0)) (.var 0)) (.neg .one)) (by decide +kernel)

theorem row_comb_id (c0 c1 c2 c3 i d : Shell p) :
    c0 * d + c1 * i + c2 * d + c3 * i = (c0 + c2) * d + ((c1 + c3) * i) :=
  RE.sound (look [c0, c1, c2, c3, i, d])
    (.add (.add (.add (.mul (.var 0) (.var 5)) (.mul (.var 1) (.var 4))) (.mul (.var 2) (.var 5))) (.mul (.var 3) (.var 4)))
    (.add (.mul (.add (.var 0) (.var 2)) (.var 5)) (.mul (.add (.var 1) (.var 3)) (.var 4))) (by decide +kernel)

theorem last_row_id (d0 d1 d2 d3 i Z G : Shell p) :
    d0 * 0 + d1 * (i * Z) + d2 * 0 + d3 * (i * G) = (d1 * i) * Z + (d3 * i) * G :=
  RE.sound (look [d0, d1, d2, d3, i, Z, G])
    (.add (.add (.add (.mul (.var 0) .zero) (.mul (.var 1) (.mul (.var 4) (.var 5)))) (.mul (.var 2) .zero)) (.mul (.var 3) (.mul (.var 4) (.var 6))))
    (.add (.mul (.mul (.var 1) (.var 4)) (.var 5)) (.mul (.mul (.var 3) (.var 4)) (.var 6))) (by decide +kernel)

theorem col_sum_id (d0 d1 d2 d3 i : Shell p) :
    d0 * 1 + d1 * 0 + d2 * 1 + d3 * 0 = d0 + d2 :=
  RE.sound (look [d0, d1, d2, d3, i])
    (.add (.add (.add (.mul (.var 0) .one) (.mul (.var 1) .zero)) (.mul (.var 2) .one)) (.mul (.var 3) .zero))
    (.add (.var 0) (.var 2)) (by decide +kernel)

variable {κ : Nat} {g : Shell p}

/-! ## A quadratic has at most two roots -/

/-- Three distinct roots of `a x² + b x + c` force `a = 0`. -/
theorem quad_roots (F : Frame p κ g) {a b c x1 x2 x3 : Shell p} (ha : a ≠ 0)
    (h1 : a * (x1 * x1) + b * x1 + c = 0) (h2 : a * (x2 * x2) + b * x2 + c = 0)
    (h3 : a * (x3 * x3) + b * x3 + c = 0) (d12 : x1 ≠ x2) (d13 : x1 ≠ x3) (d23 : x2 ≠ x3) : False := by
  have ne : ∀ {u v : Shell p}, u ≠ v → u + -v ≠ 0 := fun {u v} h e =>
    h (by rw [eq_neg_of_add_eq_zero e, neg_neg])
  have lin : ∀ {y : Shell p}, a * (y * y) + b * y + c = 0 → x1 ≠ y → a * (x1 + y) + b = 0 := fun {y} hy hne => by
    have e : (x1 + -y) * (a * (x1 + y) + b) = 0 := by rw [← quad_diff_id, h1, hy, neg_zero, add_zero]
    match F.mul_eq_zero e with
    | Or.inl e1 => exact absurd e1 (ne hne)
    | Or.inr e2 => exact e2
  have e : a * (x2 + -x3) = 0 := by rw [← quad_lin_id, lin h2 d12, lin h3 d13, neg_zero, add_zero]
  match F.mul_eq_zero e with
  | Or.inl e1 => exact ha e1
  | Or.inr e2 => exact ne d23 e2

/-! ## The last row of `F^{[−s]}` and its column sums -/

theorem last_lt (F : Frame p κ g) : p - 1 - 1 < p - 1 := Nat.sub_lt F.n_pos (Nat.zero_lt_succ 0)

theorem last_pos (F : Frame p κ g) : 0 < p - 1 - 1 := FRC.Nat.le_sub_of_add_le (one_lt_n F)

/-- `F_{n−1, j} = i z^j`: the last row of `F` is the conjugate's. -/
theorem Fmat_last (F : Frame p κ g) {z : Shell p} (hz : g * z = 1) (j : Nat) :
    Fmat g κ (p - 1 - 1) j = quarterTurn g κ * z ^ j := by
  show quarterTurn g κ * g ^ (j * (p - 1 - 1)) = _
  congr 1
  apply inv_unique (y := g ^ j)
  · rw [← pow_add, ← Nat.mul_succ, Nat.succ_eq_add_one, FRC.Nat.sub_add_cancel F.n_pos, pow_mul, pow_mul_comm, F.pow_n,
      one_pow]
  · rw [← mul_pow, mul_comm, hz, one_pow]

/-- `(FJ)_{n−1, j} = i g^j`. -/
theorem FJ_last (F : Frame p κ g) {j : Nat} (hj : j < p - 1) : FJ g κ (p - 1 - 1) j = quarterTurn g κ * g ^ j := by
  show quarterTurn g κ * g ^ (rev (p - 1) j * (p - 1 - 1)) = _
  congr 1
  apply inv_unique (y := g ^ rev (p - 1) j)
  · rw [← pow_add, ← Nat.mul_succ, Nat.succ_eq_add_one, FRC.Nat.sub_add_cancel F.n_pos, pow_mul, pow_mul_comm, F.pow_n,
      one_pow]
  · have e := pow_rev_mul F hj 1
    rw [Nat.mul_one, Nat.mul_one, mul_comm] at e
    exact e

/-- `J_{n−1, j} = 0` off `j = 1`. -/
theorem J_last (F : Frame p κ g) {j : Nat} (hj : j < p - 1) (hj1 : j ≠ 1) : (J (p - 1) (p - 1 - 1) j : Shell p) = 0 := by
  show (if (p - 1 - 1 + j) % (p - 1) = 0 then (1 : Shell p) else 0) = 0
  apply ite_eq_right
  intro e
  have hn := F.n_pos
  match j, hj, hj1 with
  | 0, _, _ =>
    rw [Nat.add_zero, FRC.Nat.mod_eq_of_lt (last_lt F)] at e
    exact Nat.lt_irrefl 0 (e ▸ last_pos F)
  | 1, _, h1 => exact h1 rfl
  | m + 2, hj, _ =>
    have e2 := FRC.Nat.add_mul_mod_self_left (m + 1) 1 (p - 1) hn
    rw [Nat.mul_one] at e2
    change (p - 1 - 1 + (m + 1 + 1)) % (p - 1) = 0 at e
    rw [Nat.add_left_comm, FRC.Nat.sub_add_cancel hn, Nat.add_comm, e2, FRC.Nat.mod_eq_of_lt (Nat.lt_of_succ_lt hj)] at e
    exact Nat.noConfusion e

theorem sum_idm_col {j : Nat} (hj : j < p - 1) : sumRange (fun l => (idm l j : Shell p)) (p - 1) = 1 := by
  rw [sum_eq_single hj (fun l _ hne => idm_ne hne), idm_self]

theorem sum_J_col {j : Nat} (hj : j < p - 1) : sumRange (fun l => (J (p - 1) l j : Shell p)) (p - 1) = 1 := by
  rw [sum_congr _ (fun l _ => by
    show (if (l + j) % (p - 1) = 0 then (1 : Shell p) else 0) = (J (p - 1) j l : Shell p) * 1
    rw [mul_one, Nat.add_comm]; rfl)]
  exact @mm_J_X p _ (fun _ _ => (1 : Shell p)) j 0 hj

theorem sum_F_col (F : Frame p κ g) {j : Nat} (hj0 : 0 < j) (hj : j < p - 1) :
    sumRange (fun l => Fmat g κ l j) (p - 1) = 0 := by
  show sumRange (fun l => quarterTurn g κ * g ^ (j * l)) (p - 1) = 0
  rw [sum_congr _ (fun l _ => by rw [pow_mul]), sum_mul_left,
    F.geom_sum_eq_zero _ (by rw [pow_mul_comm, F.pow_n, one_pow]) (F.prim.2 j hj hj0), mul_zero]

theorem sum_FJ_col (F : Frame p κ g) {j : Nat} (hj0 : 0 < j) (hj : j < p - 1) :
    sumRange (fun l => FJ g κ l j) (p - 1) = 0 := by
  have hn := F.n_pos
  have hr : rev (p - 1) j = p - 1 - j := rev_of_pos hj hj0
  have hr0 : 0 < rev (p - 1) j := by rw [hr]; exact FRC.Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hj)
  show sumRange (fun l => quarterTurn g κ * g ^ (rev (p - 1) j * l)) (p - 1) = 0
  rw [sum_congr _ (fun l _ => by rw [pow_mul]), sum_mul_left,
    F.geom_sum_eq_zero _ (by rw [pow_mul_comm, F.pow_n, one_pow]) (F.prim.2 _ (rev_lt hn j) hr0), mul_zero]

/-- The column sums of `F^{[t]} = Σ_r c_r F^r` off `j = 0`: `c₀ + c₂`. -/
theorem frft_col_sum (F : Frame p κ g) (z : Shell p) (t : Nat) {j : Nat} (hj0 : 0 < j) (hj : j < p - 1) :
    sumRange (fun l => frft g κ z t l j) (p - 1) =
      NF0 (-(ofNat κ)) (-(quarterTurn g κ)) (z ^ t) + NF2 (-(ofNat κ)) (-(quarterTurn g κ)) (z ^ t) := by
  rw [sum_congr _ (fun l _ => frft_eq F z t l j)]
  show sumRange (fun l => NF0 (-(ofNat κ)) (-(quarterTurn g κ)) (z ^ t) * idm l j +
    NF1 (-(ofNat κ)) (-(quarterTurn g κ)) (z ^ t) * Fmat g κ l j + NF2 (-(ofNat κ)) (-(quarterTurn g κ)) (z ^ t) * J (p - 1) l j +
    NF3 (-(ofNat κ)) (-(quarterTurn g κ)) (z ^ t) * FJ g κ l j) (p - 1) = _
  rw [sum_add, sum_add, sum_add, sum_mul_left, sum_mul_left, sum_mul_left, sum_mul_left, sum_idm_col hj, sum_J_col hj,
    sum_F_col F hj0 hj, sum_FJ_col F hj0 hj]
  exact col_sum_id _ _ _ _ (quarterTurn g κ)

/-- The last-row entry of `F^{[t]}` off `j ∈ {1, n−1}`: `i (c₁ z^j + c₃ g^j)`. -/
theorem frft_last (F : Frame p κ g) {z : Shell p} (hz : g * z = 1) (t : Nat) {j : Nat} (hj : j < p - 1) (hj1 : j ≠ 1)
    (hjn : j ≠ p - 1 - 1) :
    frft g κ z t (p - 1 - 1) j =
      NF1 (-(ofNat κ)) (-(quarterTurn g κ)) (z ^ t) * quarterTurn g κ * z ^ j +
        NF3 (-(ofNat κ)) (-(quarterTurn g κ)) (z ^ t) * quarterTurn g κ * g ^ j := by
  rw [frft_eq F z t]
  show NF0 (-(ofNat κ)) (-(quarterTurn g κ)) (z ^ t) * idm (p - 1 - 1) j +
    NF1 (-(ofNat κ)) (-(quarterTurn g κ)) (z ^ t) * Fmat g κ (p - 1 - 1) j +
    NF2 (-(ofNat κ)) (-(quarterTurn g κ)) (z ^ t) * J (p - 1) (p - 1 - 1) j +
    NF3 (-(ofNat κ)) (-(quarterTurn g κ)) (z ^ t) * FJ g κ (p - 1 - 1) j = _
  rw [idm_ne (fun e => hjn e.symm), J_last F hj hj1, Fmat_last F hz, FJ_last F hj]
  exact last_row_id _ _ _ _ _ _ _

/-! ## Row 0 of `F^{[s]} σ` -/

theorem succ_mod_zero (F : Frame p κ g) {l : Nat} (hl : l < p - 1) : (l + 1) % (p - 1) = 0 ↔ l = p - 1 - 1 := by
  constructor
  · intro h
    match Nat.lt_or_ge (l + 1) (p - 1) with
    | Or.inl hlt => rw [FRC.Nat.mod_eq_of_lt hlt] at h; exact Nat.noConfusion h
    | Or.inr hge =>
      have e : l + 1 = p - 1 := Nat.le_antisymm hl hge
      rw [← e, FRC.Nat.add_sub_cancel]
  · intro e
    rw [e, FRC.Nat.sub_add_cancel F.n_pos]
    exact FRC.Nat.mod_self _ F.n_pos

/-- Row 0 of `F^{[s]} σ`: `(F^{[s]} σ)_{0l} = F^{[s]}_{0, l+1} = (c₀ + c₂) [l = n−1] + (c₁ + c₃) i`. -/
theorem row_shift (F : Frame p κ g) (z : Shell p) (s : Nat) {l : Nat} (hl : l < p - 1) :
    frft g κ z s 0 ((l + 1) % (p - 1)) =
      (NF0 (-(ofNat κ)) (-(quarterTurn g κ)) (z ^ s) + NF2 (-(ofNat κ)) (-(quarterTurn g κ)) (z ^ s)) * idm l (p - 1 - 1) +
        (NF1 (-(ofNat κ)) (-(quarterTurn g κ)) (z ^ s) + NF3 (-(ofNat κ)) (-(quarterTurn g κ)) (z ^ s)) * quarterTurn g κ := by
  rw [frft_eq F z s]
  show NF0 (-(ofNat κ)) (-(quarterTurn g κ)) (z ^ s) * idm 0 ((l + 1) % (p - 1)) +
    NF1 (-(ofNat κ)) (-(quarterTurn g κ)) (z ^ s) * Fmat g κ 0 ((l + 1) % (p - 1)) +
    NF2 (-(ofNat κ)) (-(quarterTurn g κ)) (z ^ s) * J (p - 1) 0 ((l + 1) % (p - 1)) +
    NF3 (-(ofNat κ)) (-(quarterTurn g κ)) (z ^ s) * FJ g κ 0 ((l + 1) % (p - 1)) = _
  have e1 : (idm 0 ((l + 1) % (p - 1)) : Shell p) = idm l (p - 1 - 1) :=
    ite_iff (Iff.trans ⟨Eq.symm, Eq.symm⟩ (succ_mod_zero F hl))
  have e2 : (J (p - 1) 0 ((l + 1) % (p - 1)) : Shell p) = idm l (p - 1 - 1) := by
    show (if (0 + (l + 1) % (p - 1)) % (p - 1) = 0 then (1 : Shell p) else 0) = _
    rw [Nat.zero_add, FRC.Nat.mod_mod _ _ F.n_pos]
    exact ite_iff (succ_mod_zero F hl)
  rw [e1, e2, Fmat_zero_row, FJ_zero_row]
  exact row_comb_id _ _ _ _ _ _

/-- 6:E8, the entry `(0, j)` of `F^{[s]} σ F^{[−s]}` off the three sites `j ∈ {0, 1, n−1}`, with `F^{[−s]} = F^{[n−s]}`
(`n − s` the natural difference, so `s ≤ n` is the reading): `i [(c₀ + c₂)(c'₁ z^j + c'₃ g^j) + (c₁ + c₃)(c'₀ + c'₂)]`. -/
theorem row_entry (F : Frame p κ g) {z : Shell p} (hz : g * z = 1) (s : Nat) {j : Nat} (hj : j < p - 1) (hj0 : j ≠ 0)
    (hj1 : j ≠ 1) (hjn : j ≠ p - 1 - 1) :
    mmul (mmul (frft g κ z s) (shift p) (p - 1)) (frft g κ z (p - 1 - s)) (p - 1) 0 j =
      (NF0 (-(ofNat κ)) (-(quarterTurn g κ)) (z ^ s) + NF2 (-(ofNat κ)) (-(quarterTurn g κ)) (z ^ s)) *
          (NF1 (-(ofNat κ)) (-(quarterTurn g κ)) (z ^ (p - 1 - s)) * quarterTurn g κ * z ^ j +
            NF3 (-(ofNat κ)) (-(quarterTurn g κ)) (z ^ (p - 1 - s)) * quarterTurn g κ * g ^ j) +
        (NF1 (-(ofNat κ)) (-(quarterTurn g κ)) (z ^ s) + NF3 (-(ofNat κ)) (-(quarterTurn g κ)) (z ^ s)) * quarterTurn g κ *
          (NF0 (-(ofNat κ)) (-(quarterTurn g κ)) (z ^ (p - 1 - s)) + NF2 (-(ofNat κ)) (-(quarterTurn g κ)) (z ^ (p - 1 - s))) := by
  have hj0' : 0 < j := Nat.pos_of_ne_zero hj0
  show sumRange (fun l => mmul (frft g κ z s) (shift p) (p - 1) 0 l * frft g κ z (p - 1 - s) l j) (p - 1) = _
  rw [sum_congr _ (fun l hl => by
    rw [show mmul (frft g κ z s) (shift p) (p - 1) 0 l = frft g κ z s 0 ((l + 1) % (p - 1)) from
      shift_single F (frft g κ z s) 0 l, row_shift F z s hl, right_distrib,
      mul_assoc (NF0 (-(ofNat κ)) (-(quarterTurn g κ)) (z ^ s) + NF2 (-(ofNat κ)) (-(quarterTurn g κ)) (z ^ s))])]
  rw [sum_add, sum_mul_left, sum_mul_left, sum_eq_single (last_lt F) (fun l _ hne => by rw [idm_ne hne, zero_mul]),
    idm_self, one_mul, frft_last F hz _ hj hj1 hjn, frft_col_sum F z _ hj0' hj]

/-! ## The coefficients off the cardinal indices -/

theorem three_kappa_lt (F : Frame p κ g) : 3 * κ < p - 1 := by
  rw [F.n_eq]; exact FRC.Nat.mul_lt_mul_of_lt_of_pos (by decide) F.cap_pos

theorem kappa_lt_n (F : Frame p κ g) : κ < p - 1 := by
  rw [F.n_eq]
  have := FRC.Nat.mul_lt_mul_of_lt_of_pos (by decide : 1 < 4) F.cap_pos
  rw [Nat.one_mul] at this
  exact this

/-- 6:E8, `c₀ + c₂ = ½ (1 + z_s²)` (`even_coeff_id`) is nonzero off `s ∈ {κ, 3κ}`, where `z_s = ±i`. -/
theorem even_coeff_ne_zero (F : Frame p κ g) {z : Shell p} (hz : g * z = 1) {s : Nat} (hs : s < p - 1) (h1 : s ≠ κ)
    (h3 : s ≠ 3 * κ) :
    NF0 (-(ofNat κ)) (-(quarterTurn g κ)) (z ^ s) + NF2 (-(ofNat κ)) (-(quarterTurn g κ)) (z ^ s) ≠ 0 := by
  rw [even_coeff_id]
  refine F.mul_ne_zero (half_ne_zero F) (fun e => ?_)
  have e2 : z ^ s * z ^ s = -1 := (neg_eq_of_add_eq_zero e).symm
  have hzk := inv_pow_kappa F hz
  match (sqrt_neg_one F (z ^ s)).1 e2 with
  | Or.inl e3 => exact h1 ((inv_frame F hz).pow_inj hs (kappa_lt_n F) (by rw [e3, hzk]))
  | Or.inr e3 => exact h3 ((inv_frame F hz).pow_inj hs (three_kappa_lt F) (by
      rw [e3, pow_mul, pow_mul_comm, hzk, pow_succ, pow_two, F.quarter_turn_sq, neg_one_mul]))

/-- `4t ≡ 0 (mod 4κ)` below `4κ` forces `t ∈ {0, κ, 2κ, 3κ}`. -/
theorem quad_mod_n (F : Frame p κ g) {t : Nat} (ht : t < p - 1) (h : (4 * t) % (p - 1) = 0) :
    t = 0 ∨ t = κ ∨ t = 2 * κ ∨ t = 3 * κ := by
  obtain ⟨c, hc⟩ := FRC.Nat.mod_spec (p - 1) F.n_pos (4 * t)
  rw [h, Nat.add_zero, F.n_eq, Nat.mul_assoc] at hc
  have e : t = κ * c := Nat.eq_of_mul_eq_mul_left (by decide) hc
  have hc4 : c < 4 := by
    rw [F.n_eq, e] at ht
    have ht' : κ * c < κ * 4 := by rw [Nat.mul_comm κ 4]; exact ht
    match Nat.lt_or_ge c 4 with
    | Or.inl h => exact h
    | Or.inr h => exact absurd (Nat.lt_of_lt_of_le ht' (Nat.mul_le_mul_left κ h)) (Nat.lt_irrefl _)
  match c, hc4, e with
  | 0, _, e => exact Or.inl (by rw [e, Nat.mul_zero])
  | 1, _, e => exact Or.inr (Or.inl (by rw [e, Nat.mul_one]))
  | 2, _, e => exact Or.inr (Or.inr (Or.inl (by rw [e, Nat.mul_comm])))
  | 3, _, e => exact Or.inr (Or.inr (Or.inr (by rw [e, Nat.mul_comm])))
  | c + 4, hc4, _ => exact absurd (Nat.lt_of_lt_of_le hc4 (Nat.le_add_left 4 c)) (Nat.lt_irrefl _)

/-- `z^{n−s} = g^s`: the conjugate family's base at `−s`. -/
theorem pow_sub_eq (F : Frame p κ g) {z : Shell p} (hz : g * z = 1) {s : Nat} (hs : s ≤ p - 1) :
    z ^ (p - 1 - s) = g ^ s := by
  apply inv_unique (y := z ^ s)
  · rw [← pow_add, FRC.Nat.sub_add_cancel hs, inv_pow_n F hz]
  · rw [← mul_pow, hz, one_pow]

/-- 6:E8, `c'₃ = c₃(−s) = ¼ Σ_ℓ y^ℓ` with `y = g^s i = g^{s + 3κ}`, nonzero off the cardinal indices: `y ≠ 1` (else
`s = κ`) and `y⁴ = g^{4s} ≠ 1` (else `κ ∣ s`); with `even_coeff_ne_zero`, the leading coefficient `i (c₀ + c₂) c'₃ ≠ 0`. -/
theorem odd_coeff_ne_zero (F : Frame p κ g) {z : Shell p} (hz : g * z = 1) {s : Nat} (hs : s < p - 1) (h0 : s ≠ 0)
    (h1 : s ≠ κ) (h2 : s ≠ 2 * κ) (h3 : s ≠ 3 * κ) :
    NF3 (-(ofNat κ)) (-(quarterTurn g κ)) (z ^ (p - 1 - s)) ≠ 0 := by
  rw [red1 (odd_coeff_id _ _ _) (hjj F), ← neg_w F, neg_neg, pow_sub_eq F hz (Nat.le_of_lt hs)]
  refine F.mul_ne_zero (q_ne_zero F) (fun e => ?_)
  have hy1 : g ^ s * quarterTurn g κ ≠ 1 := fun e1 => h1 (F.pow_inj hs (kappa_lt_n F) (inv_unique (y := quarterTurn g κ) e1 (by
        show g ^ κ * -(g ^ κ) = 1
        rw [← mul_neg, ← pow_two, F.quarter_turn_order.1, neg_neg])))
  have hy4 : g ^ s * quarterTurn g κ * (g ^ s * quarterTurn g κ) * (g ^ s * quarterTurn g κ) * (g ^ s * quarterTurn g κ) ≠ 1 :=
    fun e4 => by
      have e5 : g ^ (4 * s) = 1 := by
        rw [show (4 : Nat) = 2 * 2 from rfl, Nat.mul_assoc, pow_mul, pow_two, pow_mul, pow_two, ← e4]
        rw [show g ^ s * quarterTurn g κ * (g ^ s * quarterTurn g κ) * (g ^ s * quarterTurn g κ) * (g ^ s * quarterTurn g κ) =
          (g ^ s * g ^ s) * (g ^ s * g ^ s) * (quarterTurn g κ * quarterTurn g κ * (quarterTurn g κ * quarterTurn g κ)) from
          RE.sound (look [g ^ s, quarterTurn g κ]) (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1))) (.mul (.var 0) (.var 1))) (.mul (.var 0) (.var 1)))
            (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 0) (.var 0))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 1) (.var 1)))) (by decide +kernel),
          F.quarter_turn_sq, neg_mul_neg, one_mul, mul_one, mul_pow, mul_pow]
      match quad_mod_n F hs (F.mod_eq_zero_of_pow_eq_one e5) with
      | Or.inl e => exact h0 e
      | Or.inr (Or.inl e) => exact h1 e
      | Or.inr (Or.inr (Or.inl e)) => exact h2 e
      | Or.inr (Or.inr (Or.inr e)) => exact h3 e
  have e6 : (g ^ s * quarterTurn g κ + -1) * (1 + g ^ s * quarterTurn g κ + g ^ s * quarterTurn g κ * (g ^ s * quarterTurn g κ) +
      g ^ s * quarterTurn g κ * (g ^ s * quarterTurn g κ) * (g ^ s * quarterTurn g κ)) = 0 := by rw [e, mul_zero]
  rw [geom4_id] at e6
  exact hy4 (by rw [eq_neg_of_add_eq_zero e6, neg_neg])

/-! ## Cardinal exclusivity (6:E8) -/

/-- 6:E8, cardinal exclusivity: for `s ∉ {0, κ, 2κ, 3κ}` the row `0` of `F^{[s]} σ F^{[−s]}` vanishes at no three
distinct indices off the sites `{0, 1, n−1}`: `x = g^j` times the entry is a quadratic in `x` with leading coefficient
`i (c₀ + c₂) c'₃ ≠ 0` (the paper counts: at least `4κ − 5` nonzero entries, so the conjugate is not monomial). -/
theorem exclusivity (F : Frame p κ g) {z : Shell p} (hz : g * z = 1) {s : Nat} (hs : s < p - 1) (h0 : s ≠ 0)
    (h1 : s ≠ κ) (h2 : s ≠ 2 * κ) (h3 : s ≠ 3 * κ) {j1 j2 j3 : Nat}
    (hj1 : j1 < p - 1) (hj2 : j2 < p - 1) (hj3 : j3 < p - 1)
    (o1 : j1 ≠ 0 ∧ j1 ≠ 1 ∧ j1 ≠ p - 1 - 1) (o2 : j2 ≠ 0 ∧ j2 ≠ 1 ∧ j2 ≠ p - 1 - 1)
    (o3 : j3 ≠ 0 ∧ j3 ≠ 1 ∧ j3 ≠ p - 1 - 1) (d12 : j1 ≠ j2) (d13 : j1 ≠ j3) (d23 : j2 ≠ j3) :
    ¬(mmul (mmul (frft g κ z s) (shift p) (p - 1)) (frft g κ z (p - 1 - s)) (p - 1) 0 j1 = 0 ∧
      mmul (mmul (frft g κ z s) (shift p) (p - 1)) (frft g κ z (p - 1 - s)) (p - 1) 0 j2 = 0 ∧
      mmul (mmul (frft g κ z s) (shift p) (p - 1)) (frft g κ z (p - 1 - s)) (p - 1) 0 j3 = 0) := by
  intro ⟨e1, e2, e3⟩
  have quad : ∀ {j : Nat}, j < p - 1 → j ≠ 0 → j ≠ 1 → j ≠ p - 1 - 1 →
      mmul (mmul (frft g κ z s) (shift p) (p - 1)) (frft g κ z (p - 1 - s)) (p - 1) 0 j = 0 →
      (NF0 (-(ofNat κ)) (-(quarterTurn g κ)) (z ^ s) + NF2 (-(ofNat κ)) (-(quarterTurn g κ)) (z ^ s)) *
          NF3 (-(ofNat κ)) (-(quarterTurn g κ)) (z ^ (p - 1 - s)) * (g ^ j * g ^ j) +
        (NF1 (-(ofNat κ)) (-(quarterTurn g κ)) (z ^ s) + NF3 (-(ofNat κ)) (-(quarterTurn g κ)) (z ^ s)) *
          (NF0 (-(ofNat κ)) (-(quarterTurn g κ)) (z ^ (p - 1 - s)) + NF2 (-(ofNat κ)) (-(quarterTurn g κ)) (z ^ (p - 1 - s))) *
          g ^ j +
        (NF0 (-(ofNat κ)) (-(quarterTurn g κ)) (z ^ s) + NF2 (-(ofNat κ)) (-(quarterTurn g κ)) (z ^ s)) *
          NF1 (-(ofNat κ)) (-(quarterTurn g κ)) (z ^ (p - 1 - s)) = 0 := fun {j} hj hj0 hj1 hjn e => by
    rw [row_entry F hz s hj hj0 hj1 hjn] at e
    have e' := congrArg (fun x => g ^ j * x) e
    rw [mul_zero, row_quad_id, show z ^ j * g ^ j = 1 by rw [← mul_pow, mul_comm, hz, one_pow], add_neg, zero_mul,
      add_zero] at e'
    match F.mul_eq_zero e' with
    | Or.inl e0 => exact absurd e0 (quarter_ne_zero F)
    | Or.inr e0 => exact e0
  have ha := F.mul_ne_zero (even_coeff_ne_zero F hz hs h1 h3) (odd_coeff_ne_zero F hz hs h0 h1 h2 h3)
  exact quad_roots F ha (quad hj1 o1.1 o1.2.1 o1.2.2 e1) (quad hj2 o2.1 o2.2.1 o2.2.2 e2) (quad hj3 o3.1 o3.2.1 o3.2.2 e3)
    (fun e => d12 (F.pow_inj hj1 hj2 e)) (fun e => d13 (F.pow_inj hj1 hj3 e)) (fun e => d23 (F.pow_inj hj2 hj3 e))

end Frame
end Shell
end FRC
