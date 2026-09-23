import FrcCore.Frame

/-!
# 6-fourier — the meridians and the meridian-scale map (predicates D4, D5), no axioms

The meridian `M_m = (a g^m)_{a = 0..π}`, `π = 2κ`, as an ordered list of `2κ + 1` entries, and the
meridian-scale map `S_r(x) = g^r x`: `S_r(M_m) = M_{m+r}` as ordered lists, consecutive entries of `M_m`
differ by the effective step `g^m`, and `S_{r + (p−1)} = S_r` (the `(p−1)`-periodicity of the framed-rational
zoom). The `p = 13`, `g = 2` ladder `M_0, …, M_3` at steps `1, 2, 4, 8`, decided by computation: unwrapped
while `π g^r < p` (`r ≤ 1`), wrapping from `M_2`.
-/

namespace FRC.Shell

variable {p : Nat} [Pos p]

/-- 6:D3 — the meridian `M_m = (0, g^m, 2g^m, …, π g^m)`, `π = 2κ`, as an ordered list. -/
def meridian (g : Shell p) (κ m : Nat) : List (Shell p) :=
  (List.range (2 * κ + 1)).map (fun a => ofNat a * g ^ m)

/-- 6:D3 — the meridian-scale map `S_r(x) = g^r x`. -/
def scale (g : Shell p) (r : Nat) (x : Shell p) : Shell p := g ^ r * x

/-- The scale map on a list of multiples, entry by entry: `g^r (a g^m) = a g^{m+r}`. -/
theorem map_scale_aux (g : Shell p) (m r : Nat) : ∀ l : List Nat,
    (l.map (fun a => ofNat a * g ^ m)).map (scale g r) = l.map (fun a => ofNat a * g ^ (m + r))
  | [] => rfl
  | a :: l => by
    rw [List.map_cons, List.map_cons, List.map_cons, map_scale_aux g m r l]
    show scale g r (ofNat a * g ^ m) :: _ = (ofNat a * g ^ (m + r)) :: _
    rw [scale, pow_add, mul_left_comm, mul_comm (g ^ m)]

/-- 6:D4 — meridian-scale covariance: `S_r(M_m) = M_{m+r}` as ordered lists, for every `m, r`. -/
theorem meridian_scale (g : Shell p) (κ m r : Nat) :
    (meridian g κ m).map (scale g r) = meridian g κ (m + r) :=
  map_scale_aux g m r (List.range (2 * κ + 1))

/-- `ofNat (a + 1) = ofNat a + 1` in the shell. -/
theorem ofNat_succ (a : Nat) : (ofNat (a + 1) : Shell p) = ofNat a + 1 := by
  apply ext
  rw [val_add, val_ofNat, val_ofNat, val_one]
  exact Nat.add_mod a 1 p hp

/-- 6:D4 — the effective step: consecutive entries of `M_m` differ by `g^m`,
`(a + 1) g^m = a g^m + g^m`. -/
theorem meridian_step (g : Shell p) (m a : Nat) :
    (ofNat (a + 1) : Shell p) * g ^ m = ofNat a * g ^ m + g ^ m := by
  rw [ofNat_succ, right_distrib, one_mul]

/-- 6:D4 — `S_{r + (p−1)} = S_r`: the meridian-scale map is `(p − 1)`-periodic in `r` (the periodicity of the
framed-rational zoom, A5). -/
theorem scale_periodic {κ : Nat} {g : Shell p} (F : Frame p κ g) (r : Nat) (x : Shell p) :
    scale g (r + (p - 1)) x = scale g r x := by
  unfold scale
  rw [pow_add, F.pow_n, mul_one]

/-- 6:D5 — the `p = 13`, `g = 2`, `κ = 3` ladder: `M_0, M_1, M_2, M_3` at the effective steps `1, 2, 4, 8`;
`M_0` and `M_1` are unwrapped (`π g^r = 6 g^r < 13` for `r ≤ 1`), `M_2` wraps (`6 · 4 = 24 ≥ 13`: its entries
`0, 4, 8, 12, 3, 7, 11` return through the seam). -/
theorem ladder13 :
    meridian (2 : Shell 13) 3 0 = [0, 1, 2, 3, 4, 5, 6] ∧
    meridian (2 : Shell 13) 3 1 = [0, 2, 4, 6, 8, 10, 12] ∧
    meridian (2 : Shell 13) 3 2 = [0, 4, 8, 12, 3, 7, 11] ∧
    meridian (2 : Shell 13) 3 3 = [0, 8, 3, 11, 6, 1, 9] ∧
    (6 * 2 ^ 1 < 13) ∧ ¬ (6 * 2 ^ 2 < 13) := by
  decide

end FRC.Shell
