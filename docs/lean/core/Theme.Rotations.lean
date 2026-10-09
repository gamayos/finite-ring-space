import FrcCore.Theme.Fractional

/-!
# FrcCore.Theme.Rotations — the phase cycle as the rotation group of the coordinate plane (the fourier theme)

The fifth file of the fourier theme (6-fourier's blueprint of 8 October 2026, task T06). With `z_s = g^{−s} = z^s`,
`c_s = (z_s + z_s⁻¹)/2` and `d_s = (z_s − z_s⁻¹)/(2i)`, the rotation `R_s = [[c_s, −d_s], [d_s, c_s]]` has
`c_s² + d_s² = 1` and `R_{s+r} = R_s R_r`; the change of variables `c + i d = z_s` (and `c − i d = z_s⁻¹`) makes
`s ↦ R_s` injective below the period and onto the circle `c² + d² = 1`, so the cycle `ℤ/4κ` is `SO(2, 𝔽_p)` (6:E2),
with the four cardinal rotations `R_0 = I`, `R_κ = [[0, −1], [1, 0]]`, `R_{2κ} = −I`, `R_{3κ} = [[0, 1], [−1, 0]]` and
`z_κ = i` (6:E3). On the plane the rotation scales `u = x + i y` by `z_s` and `v = x − i y` by `z_s⁻¹`, so every orbit
off the origin is free; `plane_count` is the arithmetic identity `p² = 1 + (4κ + 2) · 4κ`, which the paper reads as the
origin and `4κ + 2` orbits of size `4κ` (the orbit count is not stated here) (6:E10). The size of the circle on the six
shells of the paper's table is decided by the kernel. No axioms.
-/

namespace FRC
namespace Shell
namespace Frame

variable {p : Nat} [Pos p]

theorem red3 {L T a b c X Y Z : Shell p} (h : L = T + a * X + b * Y + c * Z) (ha : a = 0) (hb : b = 0) (hc : c = 0) :
    L = T := by
  rw [h, ha, hb, hc, zero_mul, zero_mul, zero_mul, add_zero, add_zero, add_zero]

/-! ## Ring identities (generated; `RE.sound`, decided by the kernel) -/

theorem rot_eq_id (q i Z G : Shell p) :
    (q + q) * (Z + G) + (i * (((q + q) * -i) * (Z + -G))) = Z + (i * i + 1) * (-((1 + 1) * q * Z) + (1 + 1) * q * G) + ((1 + 1 + 1 + 1) * q + -1) * (Z) :=
  RE.sound (look [q, i, Z, G])
    (.add (.mul (.add (.var 0) (.var 0)) (.add (.var 2) (.var 3))) (.mul (.var 1) (.mul (.mul (.add (.var 0) (.var 0)) (.neg (.var 1))) (.add (.var 2) (.neg (.var 3))))))
    (.add (.add (.var 2) (.mul (.add (.mul (.var 1) (.var 1)) .one) (.add (.neg (.mul (.mul (.add .one .one) (.var 0)) (.var 2))) (.mul (.mul (.add .one .one) (.var 0)) (.var 3))))) (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.neg .one)) (.var 2))) (by decide +kernel)

theorem rot_conj_id (q i Z G : Shell p) :
    (q + q) * (Z + G) + -(i * (((q + q) * -i) * (Z + -G))) = G + (i * i + 1) * ((1 + 1) * q * Z + -((1 + 1) * q * G)) + ((1 + 1 + 1 + 1) * q + -1) * (G) :=
  RE.sound (look [q, i, Z, G])
    (.add (.mul (.add (.var 0) (.var 0)) (.add (.var 2) (.var 3))) (.neg (.mul (.var 1) (.mul (.mul (.add (.var 0) (.var 0)) (.neg (.var 1))) (.add (.var 2) (.neg (.var 3)))))))
    (.add (.add (.var 3) (.mul (.add (.mul (.var 1) (.var 1)) .one) (.add (.mul (.mul (.add .one .one) (.var 0)) (.var 2)) (.neg (.mul (.mul (.add .one .one) (.var 0)) (.var 3)))))) (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.neg .one)) (.var 3))) (by decide +kernel)

theorem rot_circle_id (q i Z G : Shell p) :
    ((q + q) * (Z + G)) * ((q + q) * (Z + G)) + ((((q + q) * -i) * (Z + -G)) * (((q + q) * -i) * (Z + -G))) = 1 + (Z * G + -1) * (-((1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) * q * q * i * i) + (1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) * q * q) + (i * i + 1) * ((1 + 1 + 1 + 1) * q * q * Z * Z + (1 + 1 + 1 + 1) * q * q * G * G + -((1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) * q * q)) + ((1 + 1 + 1 + 1) * q + -1) * ((1 + 1 + 1 + 1) * q + 1) :=
  RE.sound (look [q, i, Z, G])
    (.add (.mul (.mul (.add (.var 0) (.var 0)) (.add (.var 2) (.var 3))) (.mul (.add (.var 0) (.var 0)) (.add (.var 2) (.var 3)))) (.mul (.mul (.mul (.add (.var 0) (.var 0)) (.neg (.var 1))) (.add (.var 2) (.neg (.var 3)))) (.mul (.mul (.add (.var 0) (.var 0)) (.neg (.var 1))) (.add (.var 2) (.neg (.var 3))))))
    (.add (.add (.add .one (.mul (.add (.mul (.var 2) (.var 3)) (.neg .one)) (.add (.neg (.mul (.mul (.mul (.mul (.add (.add (.add (.add (.add (.add (.add .one .one) .one) .one) .one) .one) .one) .one) (.var 0)) (.var 0)) (.var 1)) (.var 1))) (.mul (.mul (.add (.add (.add (.add (.add (.add (.add .one .one) .one) .one) .one) .one) .one) .one) (.var 0)) (.var 0))))) (.mul (.add (.mul (.var 1) (.var 1)) .one) (.add (.add (.mul (.mul (.mul (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.var 0)) (.var 2)) (.var 2)) (.mul (.mul (.mul (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.var 0)) (.var 3)) (.var 3))) (.neg (.mul (.mul (.add (.add (.add (.add (.add (.add (.add .one .one) .one) .one) .one) .one) .one) .one) (.var 0)) (.var 0)))))) (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.neg .one)) (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) .one))) (by decide +kernel)

theorem rot_mul_c_id (q i Zs Gs Zr Gr : Shell p) :
    (q + q) * (Zs * Zr + Gs * Gr) = ((q + q) * (Zs + Gs)) * ((q + q) * (Zr + Gr)) + -((((q + q) * -i) * (Zs + -Gs)) * (((q + q) * -i) * (Zr + -Gr))) + (i * i + 1) * ((1 + 1 + 1 + 1) * q * q * Zs * Zr + -((1 + 1 + 1 + 1) * q * q * Zs * Gr) + -((1 + 1 + 1 + 1) * q * q * Gs * Zr) + (1 + 1 + 1 + 1) * q * q * Gs * Gr) + ((1 + 1 + 1 + 1) * q + -1) * (-((1 + 1) * q * Zs * Zr) + -((1 + 1) * q * Gs * Gr)) :=
  RE.sound (look [q, i, Zs, Gs, Zr, Gr])
    (.mul (.add (.var 0) (.var 0)) (.add (.mul (.var 2) (.var 4)) (.mul (.var 3) (.var 5))))
    (.add (.add (.add (.mul (.mul (.add (.var 0) (.var 0)) (.add (.var 2) (.var 3))) (.mul (.add (.var 0) (.var 0)) (.add (.var 4) (.var 5)))) (.neg (.mul (.mul (.mul (.add (.var 0) (.var 0)) (.neg (.var 1))) (.add (.var 2) (.neg (.var 3)))) (.mul (.mul (.add (.var 0) (.var 0)) (.neg (.var 1))) (.add (.var 4) (.neg (.var 5))))))) (.mul (.add (.mul (.var 1) (.var 1)) .one) (.add (.add (.add (.mul (.mul (.mul (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.var 0)) (.var 2)) (.var 4)) (.neg (.mul (.mul (.mul (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.var 0)) (.var 2)) (.var 5)))) (.neg (.mul (.mul (.mul (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.var 0)) (.var 3)) (.var 4)))) (.mul (.mul (.mul (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.var 0)) (.var 3)) (.var 5))))) (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.neg .one)) (.add (.neg (.mul (.mul (.mul (.add .one .one) (.var 0)) (.var 2)) (.var 4))) (.neg (.mul (.mul (.mul (.add .one .one) (.var 0)) (.var 3)) (.var 5)))))) (by decide +kernel)

theorem rot_mul_d_id (q i Zs Gs Zr Gr : Shell p) :
    ((q + q) * -i) * (Zs * Zr + -(Gs * Gr)) = ((q + q) * (Zs + Gs)) * (((q + q) * -i) * (Zr + -Gr)) + ((((q + q) * -i) * (Zs + -Gs)) * ((q + q) * (Zr + Gr))) + (i * i + 1) * (0) + ((1 + 1 + 1 + 1) * q + -1) * ((1 + 1) * q * i * Zs * Zr + -((1 + 1) * q * i * Gs * Gr)) :=
  RE.sound (look [q, i, Zs, Gs, Zr, Gr])
    (.mul (.mul (.add (.var 0) (.var 0)) (.neg (.var 1))) (.add (.mul (.var 2) (.var 4)) (.neg (.mul (.var 3) (.var 5)))))
    (.add (.add (.add (.mul (.mul (.add (.var 0) (.var 0)) (.add (.var 2) (.var 3))) (.mul (.mul (.add (.var 0) (.var 0)) (.neg (.var 1))) (.add (.var 4) (.neg (.var 5))))) (.mul (.mul (.mul (.add (.var 0) (.var 0)) (.neg (.var 1))) (.add (.var 2) (.neg (.var 3)))) (.mul (.add (.var 0) (.var 0)) (.add (.var 4) (.var 5))))) (.mul (.add (.mul (.var 1) (.var 1)) .one) .zero)) (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.neg .one)) (.add (.mul (.mul (.mul (.mul (.add .one .one) (.var 0)) (.var 1)) (.var 2)) (.var 4)) (.neg (.mul (.mul (.mul (.mul (.add .one .one) (.var 0)) (.var 1)) (.var 3)) (.var 5)))))) (by decide +kernel)

theorem card_c_zero (q i : Shell p) :
    (q + q) * (1 + 1) = 1 + (i * i + 1) * (0) + ((1 + 1 + 1 + 1) * q + -1) * (1) :=
  RE.sound (look [q, i])
    (.mul (.add (.var 0) (.var 0)) (.add .one .one))
    (.add (.add .one (.mul (.add (.mul (.var 1) (.var 1)) .one) .zero)) (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.neg .one)) .one)) (by decide +kernel)

theorem card_d_zero (q i : Shell p) :
    ((q + q) * -i) * (1 + -1) = 0 + (i * i + 1) * (0) + ((1 + 1 + 1 + 1) * q + -1) * (0) :=
  RE.sound (look [q, i])
    (.mul (.mul (.add (.var 0) (.var 0)) (.neg (.var 1))) (.add .one (.neg .one)))
    (.add (.add .zero (.mul (.add (.mul (.var 1) (.var 1)) .one) .zero)) (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.neg .one)) .zero)) (by decide +kernel)

theorem card_c_kappa (q i : Shell p) :
    (q + q) * (i + -i) = 0 + (i * i + 1) * (0) + ((1 + 1 + 1 + 1) * q + -1) * (0) :=
  RE.sound (look [q, i])
    (.mul (.add (.var 0) (.var 0)) (.add (.var 1) (.neg (.var 1))))
    (.add (.add .zero (.mul (.add (.mul (.var 1) (.var 1)) .one) .zero)) (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.neg .one)) .zero)) (by decide +kernel)

theorem card_d_kappa (q i : Shell p) :
    ((q + q) * -i) * (i + -(-i)) = 1 + (i * i + 1) * (-((1 + 1 + 1 + 1) * q)) + ((1 + 1 + 1 + 1) * q + -1) * (1) :=
  RE.sound (look [q, i])
    (.mul (.mul (.add (.var 0) (.var 0)) (.neg (.var 1))) (.add (.var 1) (.neg (.neg (.var 1)))))
    (.add (.add .one (.mul (.add (.mul (.var 1) (.var 1)) .one) (.neg (.mul (.add (.add (.add .one .one) .one) .one) (.var 0))))) (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.neg .one)) .one)) (by decide +kernel)

theorem card_c_two (q i : Shell p) :
    (q + q) * (i * i + -i * -i) = -1 + (i * i + 1) * ((1 + 1 + 1 + 1) * q) + ((1 + 1 + 1 + 1) * q + -1) * (-1) :=
  RE.sound (look [q, i])
    (.mul (.add (.var 0) (.var 0)) (.add (.mul (.var 1) (.var 1)) (.mul (.neg (.var 1)) (.neg (.var 1)))))
    (.add (.add (.neg .one) (.mul (.add (.mul (.var 1) (.var 1)) .one) (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)))) (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.neg .one)) (.neg .one))) (by decide +kernel)

theorem card_d_two (q i : Shell p) :
    ((q + q) * -i) * (i * i + -(-i * -i)) = 0 + (i * i + 1) * (0) + ((1 + 1 + 1 + 1) * q + -1) * (0) :=
  RE.sound (look [q, i])
    (.mul (.mul (.add (.var 0) (.var 0)) (.neg (.var 1))) (.add (.mul (.var 1) (.var 1)) (.neg (.mul (.neg (.var 1)) (.neg (.var 1))))))
    (.add (.add .zero (.mul (.add (.mul (.var 1) (.var 1)) .one) .zero)) (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.neg .one)) .zero)) (by decide +kernel)

theorem card_c_three (q i : Shell p) :
    (q + q) * ((i * i) * i + (-i * -i) * -i) = 0 + (i * i + 1) * (0) + ((1 + 1 + 1 + 1) * q + -1) * (0) :=
  RE.sound (look [q, i])
    (.mul (.add (.var 0) (.var 0)) (.add (.mul (.mul (.var 1) (.var 1)) (.var 1)) (.mul (.mul (.neg (.var 1)) (.neg (.var 1))) (.neg (.var 1)))))
    (.add (.add .zero (.mul (.add (.mul (.var 1) (.var 1)) .one) .zero)) (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.neg .one)) .zero)) (by decide +kernel)

theorem card_d_three (q i : Shell p) :
    ((q + q) * -i) * ((i * i) * i + -((-i * -i) * -i)) = -1 + (i * i + 1) * (-((1 + 1 + 1 + 1) * q * i * i) + (1 + 1 + 1 + 1) * q) + ((1 + 1 + 1 + 1) * q + -1) * (-1) :=
  RE.sound (look [q, i])
    (.mul (.mul (.add (.var 0) (.var 0)) (.neg (.var 1))) (.add (.mul (.mul (.var 1) (.var 1)) (.var 1)) (.neg (.mul (.mul (.neg (.var 1)) (.neg (.var 1))) (.neg (.var 1))))))
    (.add (.add (.neg .one) (.mul (.add (.mul (.var 1) (.var 1)) .one) (.add (.neg (.mul (.mul (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.var 1)) (.var 1))) (.mul (.add (.add (.add .one .one) .one) .one) (.var 0))))) (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.neg .one)) (.neg .one))) (by decide +kernel)

theorem orbit_u_id (i c d x y : Shell p) :
    c * x + -(d * y) + (i * (d * x + c * y)) = (c + i * d) * (x + i * y) + (i * i + 1) * (-(d * y)) :=
  RE.sound (look [i, c, d, x, y])
    (.add (.add (.mul (.var 1) (.var 3)) (.neg (.mul (.var 2) (.var 4)))) (.mul (.var 0) (.add (.mul (.var 2) (.var 3)) (.mul (.var 1) (.var 4)))))
    (.add (.mul (.add (.var 1) (.mul (.var 0) (.var 2))) (.add (.var 3) (.mul (.var 0) (.var 4)))) (.mul (.add (.mul (.var 0) (.var 0)) .one) (.neg (.mul (.var 2) (.var 4))))) (by decide +kernel)

theorem orbit_v_id (i c d x y : Shell p) :
    c * x + -(d * y) + -(i * (d * x + c * y)) = (c + -(i * d)) * (x + -(i * y)) + (i * i + 1) * (-(d * y)) :=
  RE.sound (look [i, c, d, x, y])
    (.add (.add (.mul (.var 1) (.var 3)) (.neg (.mul (.var 2) (.var 4)))) (.neg (.mul (.var 0) (.add (.mul (.var 2) (.var 3)) (.mul (.var 1) (.var 4))))))
    (.add (.mul (.add (.var 1) (.neg (.mul (.var 0) (.var 2)))) (.add (.var 3) (.neg (.mul (.var 0) (.var 4))))) (.mul (.add (.mul (.var 0) (.var 0)) .one) (.neg (.mul (.var 2) (.var 4))))) (by decide +kernel)

theorem surj_c_id (q i c d : Shell p) :
    (q + q) * (c + i * d + (c + -(i * d))) = c + (i * i + 1) * (0) + ((1 + 1 + 1 + 1) * q + -1) * (c) :=
  RE.sound (look [q, i, c, d])
    (.mul (.add (.var 0) (.var 0)) (.add (.add (.var 2) (.mul (.var 1) (.var 3))) (.add (.var 2) (.neg (.mul (.var 1) (.var 3))))))
    (.add (.add (.var 2) (.mul (.add (.mul (.var 1) (.var 1)) .one) .zero)) (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.neg .one)) (.var 2))) (by decide +kernel)

theorem surj_d_id (q i c d : Shell p) :
    ((q + q) * -i) * (c + i * d + -(c + -(i * d))) = d + (i * i + 1) * (-((1 + 1 + 1 + 1) * q * d)) + ((1 + 1 + 1 + 1) * q + -1) * (d) :=
  RE.sound (look [q, i, c, d])
    (.mul (.mul (.add (.var 0) (.var 0)) (.neg (.var 1))) (.add (.add (.var 2) (.mul (.var 1) (.var 3))) (.neg (.add (.var 2) (.neg (.mul (.var 1) (.var 3)))))))
    (.add (.add (.var 3) (.mul (.add (.mul (.var 1) (.var 1)) .one) (.neg (.mul (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.var 3))))) (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.neg .one)) (.var 3))) (by decide +kernel)

theorem norm_id (q i c d : Shell p) :
    (c + i * d) * (c + -(i * d)) = c * c + d * d + (i * i + 1) * (-(d * d)) :=
  RE.sound (look [q, i, c, d])
    (.mul (.add (.var 2) (.mul (.var 1) (.var 3))) (.add (.var 2) (.neg (.mul (.var 1) (.var 3)))))
    (.add (.add (.mul (.var 2) (.var 2)) (.mul (.var 3) (.var 3))) (.mul (.add (.mul (.var 1) (.var 1)) .one) (.neg (.mul (.var 3) (.var 3))))) (by decide +kernel)

variable {κ : Nat} {g : Shell p}

/-! ## The rotation `R_s` -/

/-- `c_s = (z_s + z_s⁻¹)/2`, with `z_s = z^s`, `z_s⁻¹ = g^s` and `1/2 = q + q`. -/
def cs (g : Shell p) (κ : Nat) (z : Shell p) (s : Nat) : Shell p := (-(ofNat κ) + -(ofNat κ)) * (z ^ s + g ^ s)

/-- `d_s = (z_s − z_s⁻¹)/(2i)`, with `1/i = −i`. -/
def ds (g : Shell p) (κ : Nat) (z : Shell p) (s : Nat) : Shell p :=
  (-(ofNat κ) + -(ofNat κ)) * -(quarterTurn g κ) * (z ^ s + -(g ^ s))

/-- The change of variables: `c_s + i d_s = z_s` and `c_s − i d_s = z_s⁻¹ = g^s`. -/
theorem rot_eq (F : Frame p κ g) (z : Shell p) (s : Nat) :
    cs g κ z s + quarterTurn g κ * ds g κ z s = z ^ s ∧ cs g κ z s + -(quarterTurn g κ * ds g κ z s) = g ^ s :=
  ⟨red2 (rot_eq_id _ _ _ _) (hii F) (hq F), red2 (rot_conj_id _ _ _ _) (hii F) (hq F)⟩

/-- 6:E2, `R_s ∈ SO(2, 𝔽_p)`: `c_s² + d_s² = 1` (the determinant), since `z_s z_s⁻¹ = 1`. -/
theorem rot_circle (F : Frame p κ g) {z : Shell p} (hz : g * z = 1) (s : Nat) :
    cs g κ z s * cs g κ z s + ds g κ z s * ds g κ z s = 1 :=
  red3 (rot_circle_id _ _ _ _) (by rw [← mul_pow, mul_comm, hz, one_pow, add_neg]) (hii F) (hq F)

/-- 6:E2, `s ↦ R_s` is a homomorphism: `R_{s+r} = R_s R_r` entrywise. -/
theorem rot_hom (F : Frame p κ g) (z : Shell p) (s r : Nat) :
    cs g κ z (s + r) = cs g κ z s * cs g κ z r + -(ds g κ z s * ds g κ z r) ∧
      ds g κ z (s + r) = cs g κ z s * ds g κ z r + ds g κ z s * cs g κ z r := by
  constructor
  · show (-(ofNat κ) + -(ofNat κ)) * (z ^ (s + r) + g ^ (s + r)) = _
    rw [pow_add, pow_add]; exact red2 (rot_mul_c_id _ _ _ _ _ _) (hii F) (hq F)
  · show (-(ofNat κ) + -(ofNat κ)) * -(quarterTurn g κ) * (z ^ (s + r) + -(g ^ (s + r))) = _
    rw [pow_add, pow_add]; exact red2 (rot_mul_d_id _ _ _ _ _ _) (hii F) (hq F)

/-- 6:E2, injectivity below the period: `R_s = R_r` forces `s = r`, since `c + i d = z^s` and `z` has order `4κ`. -/
theorem rot_inj (F : Frame p κ g) {z : Shell p} (hz : g * z = 1) {s r : Nat} (hs : s < p - 1) (hr : r < p - 1)
    (hc : cs g κ z s = cs g κ z r) (hd : ds g κ z s = ds g κ z r) : s = r := by
  apply (inv_frame F hz).pow_inj hs hr
  rw [← (rot_eq F z s).1, ← (rot_eq F z r).1, hc, hd]

/-- 6:E2, surjectivity: every point of the circle `c² + d² = 1` is a rotation `R_s`, `s < 4κ`: `c + i d ≠ 0` is a
power `z^s` of the generator, and then `c = c_s`, `d = d_s`. -/
theorem rot_surj (F : Frame p κ g) {z : Shell p} (hz : g * z = 1) {c d : Shell p} (h : c * c + d * d = 1) :
    ∃ s, s < p - 1 ∧ c = cs g κ z s ∧ d = ds g κ z s := by
  have hn : (c + quarterTurn g κ * d) * (c + -(quarterTurn g κ * d)) = 1 := by
    rw [red1 (norm_id (-(ofNat κ)) _ _ _) (hii F), h]
  have hu : c + quarterTurn g κ * d ≠ 0 := fun e => F.one_ne_zero (by rw [← hn, e, zero_mul])
  obtain ⟨s, hs, hu⟩ := (inv_frame F hz).eq_pow_of_ne_zero hu
  have hv : c + -(quarterTurn g κ * d) = g ^ s :=
    inv_unique (x := c + -(quarterTurn g κ * d)) (y := z ^ s) (by rw [hu, mul_comm]; exact hn)
      (by rw [← mul_pow, hz, one_pow])
  refine ⟨s, hs, ?_, ?_⟩
  · show c = (-(ofNat κ) + -(ofNat κ)) * (z ^ s + g ^ s)
    rw [hu, ← hv]; exact (red2 (surj_c_id _ _ _ _) (hii F) (hq F)).symm
  · show d = (-(ofNat κ) + -(ofNat κ)) * -(quarterTurn g κ) * (z ^ s + -(g ^ s))
    rw [hu, ← hv]; exact (red2 (surj_d_id _ _ _ _) (hii F) (hq F)).symm

/-- 6:E3, the four cardinal rotations and `z_κ = i`: `R_0 = I`, `R_κ = [[0, −1], [1, 0]]`, `R_{2κ} = −I`,
`R_{3κ} = [[0, 1], [−1, 0]]`. -/
theorem rot_cardinal (F : Frame p κ g) {z : Shell p} (hz : g * z = 1) :
    (cs g κ z 0 = 1 ∧ ds g κ z 0 = 0) ∧ (cs g κ z κ = 0 ∧ ds g κ z κ = 1) ∧
      (cs g κ z (2 * κ) = -1 ∧ ds g κ z (2 * κ) = 0) ∧ (cs g κ z (3 * κ) = 0 ∧ ds g κ z (3 * κ) = -1) ∧
      z ^ κ = quarterTurn g κ := by
  have hzk := inv_pow_kappa F hz
  have hgk : g ^ κ = -(quarterTurn g κ) := (neg_neg _).symm
  have hi := hii F
  have hq := hq F
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, hzk⟩
  · show (-(ofNat κ) + -(ofNat κ)) * (z ^ 0 + g ^ 0) = 1
    rw [pow_zero, pow_zero]; exact red2 (card_c_zero _ (quarterTurn g κ)) hi hq
  · show (-(ofNat κ) + -(ofNat κ)) * -(quarterTurn g κ) * (z ^ 0 + -(g ^ 0)) = 0
    rw [pow_zero, pow_zero]; exact red2 (card_d_zero _ _) hi hq
  · show (-(ofNat κ) + -(ofNat κ)) * (z ^ κ + g ^ κ) = 0
    rw [hzk, hgk]; exact red2 (card_c_kappa _ _) hi hq
  · show (-(ofNat κ) + -(ofNat κ)) * -(quarterTurn g κ) * (z ^ κ + -(g ^ κ)) = 1
    rw [hzk, hgk]; exact red2 (card_d_kappa _ _) hi hq
  · show (-(ofNat κ) + -(ofNat κ)) * (z ^ (2 * κ) + g ^ (2 * κ)) = -1
    rw [pow_mul_comm' z, pow_mul_comm' g, hzk, hgk, pow_two, pow_two]; exact red2 (card_c_two _ _) hi hq
  · show (-(ofNat κ) + -(ofNat κ)) * -(quarterTurn g κ) * (z ^ (2 * κ) + -(g ^ (2 * κ))) = 0
    rw [pow_mul_comm' z, pow_mul_comm' g, hzk, hgk, pow_two, pow_two]; exact red2 (card_d_two _ _) hi hq
  · show (-(ofNat κ) + -(ofNat κ)) * (z ^ (3 * κ) + g ^ (3 * κ)) = 0
    rw [pow_mul_comm' z, pow_mul_comm' g, hzk, hgk, pow_succ, pow_two, pow_succ, pow_two]
    exact red2 (card_c_three _ _) hi hq
  · show (-(ofNat κ) + -(ofNat κ)) * -(quarterTurn g κ) * (z ^ (3 * κ) + -(g ^ (3 * κ))) = -1
    rw [pow_mul_comm' z, pow_mul_comm' g, hzk, hgk, pow_succ, pow_two, pow_succ, pow_two]
    exact red2 (card_d_three _ _) hi hq
where
  /-- `a^(m κ) = (a^κ)^m`. -/
  pow_mul_comm' (a : Shell p) {m : Nat} : a ^ (m * κ) = (a ^ κ) ^ m := by rw [pow_mul, pow_mul_comm]

/-! ## The plane as orbits of the cycle (6:E10) -/

/-- 6:E10, the rotation on the plane in the coordinates `u = x + i y`, `v = x − i y`: `R_s` scales `u` by `z_s` and `v`
by `z_s⁻¹`. -/
theorem rot_uv (F : Frame p κ g) (z : Shell p) (s : Nat) (x y : Shell p) :
    (cs g κ z s * x + -(ds g κ z s * y)) + quarterTurn g κ * (ds g κ z s * x + cs g κ z s * y) =
        z ^ s * (x + quarterTurn g κ * y) ∧
      (cs g κ z s * x + -(ds g κ z s * y)) + -(quarterTurn g κ * (ds g κ z s * x + cs g κ z s * y)) =
        g ^ s * (x + -(quarterTurn g κ * y)) :=
  ⟨by rw [red1 (orbit_u_id _ _ _ _ _) (hii F), (rot_eq F z s).1],
   by rw [red1 (orbit_v_id _ _ _ _ _) (hii F), (rot_eq F z s).2]⟩

/-- 6:E10, the orbits off the origin are free: a rotation `R_s`, `s < 4κ`, fixing a point `(x, y) ≠ (0, 0)` is the
identity, `s = 0`. -/
theorem orbit_free (F : Frame p κ g) {z : Shell p} (hz : g * z = 1) {x y : Shell p} (hxy : ¬(x = 0 ∧ y = 0))
    {s : Nat} (hs : s < p - 1) (hfix : cs g κ z s * x + -(ds g κ z s * y) = x ∧ ds g κ z s * x + cs g κ z s * y = y) :
    s = 0 := by
  have hu := (rot_uv F z s x y).1
  have hv := (rot_uv F z s x y).2
  rw [hfix.1, hfix.2] at hu hv
  have key : ∀ {a : Shell p} {t : Shell p}, t ≠ 0 → a * t = t → a = 1 := fun {a t} ht e =>
    F.mul_left_cancel ht (by rw [mul_comm, e, mul_one])
  match Nat.decEq s 0 with
  | isTrue e => exact e
  | isFalse hs0 =>
    exfalso
    have hz1 : z ^ s ≠ 1 := (inv_frame F hz).prim.2 s hs (Nat.pos_of_ne_zero hs0)
    have hg1 : g ^ s ≠ 1 := F.prim.2 s hs (Nat.pos_of_ne_zero hs0)
    have hu0 : x + quarterTurn g κ * y = 0 := match Decidable.em (x + quarterTurn g κ * y = 0) with
      | Or.inl e => e
      | Or.inr ne => absurd (key ne hu.symm) hz1
    have hv0 : x + -(quarterTurn g κ * y) = 0 := match Decidable.em (x + -(quarterTurn g κ * y) = 0) with
      | Or.inl e => e
      | Or.inr ne => absurd (key ne hv.symm) hg1
    have hx : x = 0 := F.no_south_pole x (by rw [two_mul']; exact uv_sum hu0 hv0)
    have hy : y = 0 := by
      rw [hx, zero_add] at hu0
      match F.mul_eq_zero hu0 with
      | Or.inl e => exact absurd e (quarter_ne_zero F)
      | Or.inr e => exact e
    exact hxy ⟨hx, hy⟩
where
  uv_sum {x w : Shell p} (h1 : x + w = 0) (h2 : x + -w = 0) : x + x = 0 := by
    have e : x + x = (x + w) + (x + -w) :=
      RE.sound (look [x, w]) (.add (.var 0) (.var 0)) (.add (.add (.var 0) (.var 1)) (.add (.var 0) (.neg (.var 1))))
        (by decide +kernel)
    rw [e, h1, h2, add_zero]

/-- 6:E10, the count `p² = 1 + (4κ + 2) · 4κ` (the paper reads it as the origin and `4κ + 2` free orbits of size `4κ`). -/
theorem plane_count (F : Frame p κ g) : p * p = 1 + (4 * κ + 2) * (4 * κ) := by
  rw [F.cap, Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.one_mul, Nat.add_mul, Nat.two_mul, Nat.mul_one,
    ← Nat.add_assoc (4 * κ * (4 * κ) + 4 * κ) (4 * κ) 1, Nat.add_comm 1 (4 * κ * (4 * κ) + (4 * κ + 4 * κ)),
    ← Nat.add_assoc (4 * κ * (4 * κ)) (4 * κ) (4 * κ)]

/-! The circle on the six shells of the paper's table: `|SO(2, 𝔽_p)| = 4κ`, decided by the kernel. -/

/-- `countRow p a b`: the number of `b' < b` with `a² + b'² = 1` in the shell, for the fixed `a`; `countCircle p a` sums
`countRow p a' p` over `a' < a`, so `countCircle p p` counts the circle. -/
def countRow (p : Nat) [Pos p] (a : Nat) : Nat → Nat
  | 0 => 0
  | b + 1 => countRow p a b + (if (ofNat a : Shell p) * ofNat a + ofNat b * ofNat b = 1 then 1 else 0)
def countCircle (p : Nat) [Pos p] : Nat → Nat
  | 0 => 0
  | a + 1 => countCircle p a + countRow p a p

/-- 6:E2, 6:E10, the circle has `4κ` points on the six shells: `4, 12, 16, 28, 36, 40`. -/
theorem six_circles :
    countCircle 5 5 = 4 ∧ countCircle 13 13 = 12 ∧ countCircle 17 17 = 16 ∧ countCircle 29 29 = 28 ∧
      countCircle 37 37 = 36 ∧ countCircle 41 41 = 40 := by decide +kernel

end Frame
end Shell
end FRC
