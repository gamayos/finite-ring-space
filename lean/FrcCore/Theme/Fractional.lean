import FrcCore.Theme.Fourier

/-!
# FrcCore.Theme.Fractional — the projector algebra of the fractional family (the fourier theme)

The second file of the fourier theme (one theme; the 800-line limit of decision Q03 forces the file), opened for the
revised 6-fourier of 8 October 2026 (`6-fourier-20260716/reports/blueprint-20261008.md`, task T02). Every projector
`Π_ℓ = 4⁻¹ Σ_m i^{−ℓm} F^m` is a combination `c₀ I + c₁ F + c₂ J + c₃ F J` (`Theme/Fourier.lean`), and the product of
two combinations is the cyclic convolution of their coefficients (`comb_mul`). So the algebra of the projectors is four
coefficient identities per product, decided by the kernel through the normaliser `RE.sound` with the two relations
`w² = −1` (`w = i⁻¹ = −i`) and `4 q = 1` (`q = 4⁻¹ = −κ`), and the orthogonality `Π_ℓ Π_m = 0` for `ℓ ≠ m` is the
geometric sum `1 + x + x² + x³ = 0` of the nontrivial fourth root `x = i^{m−ℓ}`: `Π_ℓ Π_m = [ℓ = m] Π_ℓ`,
`Σ_ℓ Π_ℓ = I`, `F Π_ℓ = i^ℓ Π_ℓ` (6:C2), and the two sums `Π₀ + Π₂ = (I + J)/2`, `Π₁ + Π₃ = (I − J)/2` (6:C5). No
axioms.
-/

namespace FRC
namespace Shell
namespace Frame

variable {p : Nat} [Pos p]

/-! ## Ring identities (generated; `RE.sound`, decided by the kernel) -/

theorem comb_add_id (a0 a1 a2 a3 b0 b1 b2 b3 I F J G : Shell p) :
    a0 * I + a1 * F + a2 * J + a3 * G + (b0 * I + b1 * F + b2 * J + b3 * G) =
      (a0 + b0) * I + (a1 + b1) * F + (a2 + b2) * J + (a3 + b3) * G :=
  RE.sound (look [a0, a1, a2, a3, b0, b1, b2, b3, I, F, J, G])
    (.add (.add (.add (.add (.mul (.var 0) (.var 8)) (.mul (.var 1) (.var 9))) (.mul (.var 2) (.var 10))) (.mul (.var 3) (.var 11))) (.add (.add (.add (.mul (.var 4) (.var 8)) (.mul (.var 5) (.var 9))) (.mul (.var 6) (.var 10))) (.mul (.var 7) (.var 11))))
    (.add (.add (.add (.mul (.add (.var 0) (.var 4)) (.var 8)) (.mul (.add (.var 1) (.var 5)) (.var 9))) (.mul (.add (.var 2) (.var 6)) (.var 10))) (.mul (.add (.var 3) (.var 7)) (.var 11))) (by decide +kernel)

theorem comb_smul_id (c a0 a1 a2 a3 I F J G : Shell p) :
    c * (a0 * I + a1 * F + a2 * J + a3 * G) = c * a0 * I + c * a1 * F + c * a2 * J + c * a3 * G :=
  RE.sound (look [c, a0, a1, a2, a3, I, F, J, G])
    (.mul (.var 0) (.add (.add (.add (.mul (.var 1) (.var 5)) (.mul (.var 2) (.var 6))) (.mul (.var 3) (.var 7))) (.mul (.var 4) (.var 8))))
    (.add (.add (.add (.mul (.mul (.var 0) (.var 1)) (.var 5)) (.mul (.mul (.var 0) (.var 2)) (.var 6))) (.mul (.mul (.var 0) (.var 3)) (.var 7))) (.mul (.mul (.var 0) (.var 4)) (.var 8))) (by decide +kernel)

theorem comb_zero_id (I F J G : Shell p) :
    0 * I + 0 * F + 0 * J + 0 * G = 0 :=
  RE.sound (look [I, F, J, G])
    (.add (.add (.add (.mul .zero (.var 0)) (.mul .zero (.var 1))) (.mul .zero (.var 2))) (.mul .zero (.var 3)))
    .zero (by decide +kernel)

theorem comb_idm_id (I F J G : Shell p) :
    1 * I + 0 * F + 0 * J + 0 * G = I :=
  RE.sound (look [I, F, J, G])
    (.add (.add (.add (.mul .one (.var 0)) (.mul .zero (.var 1))) (.mul .zero (.var 2))) (.mul .zero (.var 3)))
    (.var 0) (by decide +kernel)

theorem comb_Fmat_id (I F J G : Shell p) :
    0 * I + 1 * F + 0 * J + 0 * G = F :=
  RE.sound (look [I, F, J, G])
    (.add (.add (.add (.mul .zero (.var 0)) (.mul .one (.var 1))) (.mul .zero (.var 2))) (.mul .zero (.var 3)))
    (.var 1) (by decide +kernel)

theorem comb_J_id (I F J G : Shell p) :
    0 * I + 0 * F + 1 * J + 0 * G = J :=
  RE.sound (look [I, F, J, G])
    (.add (.add (.add (.mul .zero (.var 0)) (.mul .zero (.var 1))) (.mul .one (.var 2))) (.mul .zero (.var 3)))
    (.var 2) (by decide +kernel)

theorem comb_FJ_id (I F J G : Shell p) :
    0 * I + 0 * F + 0 * J + 1 * G = G :=
  RE.sound (look [I, F, J, G])
    (.add (.add (.add (.mul .zero (.var 0)) (.mul .zero (.var 1))) (.mul .zero (.var 2))) (.mul .one (.var 3)))
    (.var 3) (by decide +kernel)

theorem even_sum_id (q w I F J G : Shell p) :
    (q + q) * I + (q + -q) * F + (q + q) * J + (q + -q) * G = (q + q) * (I + J) :=
  RE.sound (look [q, w, I, F, J, G])
    (.add (.add (.add (.mul (.add (.var 0) (.var 0)) (.var 2)) (.mul (.add (.var 0) (.neg (.var 0))) (.var 3))) (.mul (.add (.var 0) (.var 0)) (.var 4))) (.mul (.add (.var 0) (.neg (.var 0))) (.var 5)))
    (.mul (.add (.var 0) (.var 0)) (.add (.var 2) (.var 4))) (by decide +kernel)

theorem odd_sum_id (q w I F J G : Shell p) :
    (q + q) * I + (q * w + -(q * w)) * F + (-q + -q) * J + (-(q * w) + q * w) * G = (q + q) * (I + -J) :=
  RE.sound (look [q, w, I, F, J, G])
    (.add (.add (.add (.mul (.add (.var 0) (.var 0)) (.var 2)) (.mul (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 0) (.var 1)))) (.var 3))) (.mul (.add (.neg (.var 0)) (.neg (.var 0))) (.var 4))) (.mul (.add (.neg (.mul (.var 0) (.var 1))) (.mul (.var 0) (.var 1))) (.var 5)))
    (.mul (.add (.var 0) (.var 0)) (.add (.var 2) (.neg (.var 4)))) (by decide +kernel)

theorem proj1_c2 (q w : Shell p) :
    q * (w * w) = -q + (w * w + 1) * (q) :=
  RE.sound (look [q, w])
    (.mul (.var 0) (.mul (.var 1) (.var 1)))
    (.add (.neg (.var 0)) (.mul (.add (.mul (.var 1) (.var 1)) .one) (.var 0))) (by decide +kernel)

theorem proj1_c3 (q w : Shell p) :
    q * ((w * w) * w) = -(q * w) + (w * w + 1) * (q * w) :=
  RE.sound (look [q, w])
    (.mul (.var 0) (.mul (.mul (.var 1) (.var 1)) (.var 1)))
    (.add (.neg (.mul (.var 0) (.var 1))) (.mul (.add (.mul (.var 1) (.var 1)) .one) (.mul (.var 0) (.var 1)))) (by decide +kernel)

theorem proj2_c1 (q w : Shell p) :
    q * (w * w) = -q + (w * w + 1) * (q) :=
  RE.sound (look [q, w])
    (.mul (.var 0) (.mul (.var 1) (.var 1)))
    (.add (.neg (.var 0)) (.mul (.add (.mul (.var 1) (.var 1)) .one) (.var 0))) (by decide +kernel)

theorem proj2_c2 (q w : Shell p) :
    q * ((w * w) * (w * w)) = q + (w * w + 1) * (q * w * w + -q) :=
  RE.sound (look [q, w])
    (.mul (.var 0) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 1) (.var 1))))
    (.add (.var 0) (.mul (.add (.mul (.var 1) (.var 1)) .one) (.add (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.neg (.var 0))))) (by decide +kernel)

theorem proj2_c3 (q w : Shell p) :
    q * (((w * w) * (w * w)) * (w * w)) = -q + (w * w + 1) * (q * w * w * w * w + -(q * w * w) + q) :=
  RE.sound (look [q, w])
    (.mul (.var 0) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 1) (.var 1))) (.mul (.var 1) (.var 1))))
    (.add (.neg (.var 0)) (.mul (.add (.mul (.var 1) (.var 1)) .one) (.add (.add (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.neg (.mul (.mul (.var 0) (.var 1)) (.var 1)))) (.var 0)))) (by decide +kernel)

theorem proj3_c1 (q w : Shell p) :
    q * ((w * w) * w) = -(q * w) + (w * w + 1) * (q * w) :=
  RE.sound (look [q, w])
    (.mul (.var 0) (.mul (.mul (.var 1) (.var 1)) (.var 1)))
    (.add (.neg (.mul (.var 0) (.var 1))) (.mul (.add (.mul (.var 1) (.var 1)) .one) (.mul (.var 0) (.var 1)))) (by decide +kernel)

theorem proj3_c2 (q w : Shell p) :
    q * (((w * w) * w) * ((w * w) * w)) = -q + (w * w + 1) * (q * w * w * w * w + -(q * w * w) + q) :=
  RE.sound (look [q, w])
    (.mul (.var 0) (.mul (.mul (.mul (.var 1) (.var 1)) (.var 1)) (.mul (.mul (.var 1) (.var 1)) (.var 1))))
    (.add (.neg (.var 0)) (.mul (.add (.mul (.var 1) (.var 1)) .one) (.add (.add (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.neg (.mul (.mul (.var 0) (.var 1)) (.var 1)))) (.var 0)))) (by decide +kernel)

theorem proj3_c3 (q w : Shell p) :
    q * ((((w * w) * w) * ((w * w) * w)) * ((w * w) * w)) = q * w + (w * w + 1) * (q * w * w * w * w * w * w * w + -(q * w * w * w * w * w) + q * w * w * w + -(q * w)) :=
  RE.sound (look [q, w])
    (.mul (.var 0) (.mul (.mul (.mul (.mul (.var 1) (.var 1)) (.var 1)) (.mul (.mul (.var 1) (.var 1)) (.var 1))) (.mul (.mul (.var 1) (.var 1)) (.var 1))))
    (.add (.mul (.var 0) (.var 1)) (.mul (.add (.mul (.var 1) (.var 1)) .one) (.add (.add (.add (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.neg (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1)))) (.mul (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.var 1))) (.neg (.mul (.var 0) (.var 1)))))) (by decide +kernel)

theorem neg_w_id (q w : Shell p) :
    -w = (w * w) * w + (w * w + 1) * (-w) :=
  RE.sound (look [q, w])
    (.neg (.var 1))
    (.add (.mul (.mul (.var 1) (.var 1)) (.var 1)) (.mul (.add (.mul (.var 1) (.var 1)) .one) (.neg (.var 1)))) (by decide +kernel)

theorem self_c0 (q u : Shell p) :
    q * q + (q * u) * (q * ((u * u) * u)) + (q * (u * u)) * (q * (u * u)) + (q * ((u * u) * u)) * (q * u) = q + (u * u * u * u + -1) * ((1 + 1 + 1) * q * q) + ((1 + 1 + 1 + 1) * q + -1) * (q) :=
  RE.sound (look [q, u])
    (.add (.add (.add (.mul (.var 0) (.var 0)) (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.mul (.mul (.var 1) (.var 1)) (.var 1))))) (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.mul (.var 0) (.mul (.var 1) (.var 1))))) (.mul (.mul (.var 0) (.mul (.mul (.var 1) (.var 1)) (.var 1))) (.mul (.var 0) (.var 1))))
    (.add (.add (.var 0) (.mul (.add (.mul (.mul (.mul (.var 1) (.var 1)) (.var 1)) (.var 1)) (.neg .one)) (.mul (.mul (.add (.add .one .one) .one) (.var 0)) (.var 0)))) (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.neg .one)) (.var 0))) (by decide +kernel)

theorem self_c1 (q u : Shell p) :
    q * (q * u) + (q * u) * q + (q * (u * u)) * (q * ((u * u) * u)) + (q * ((u * u) * u)) * (q * (u * u)) = q * u + (u * u * u * u + -1) * ((1 + 1) * q * q * u) + ((1 + 1 + 1 + 1) * q + -1) * (q * u) :=
  RE.sound (look [q, u])
    (.add (.add (.add (.mul (.var 0) (.mul (.var 0) (.var 1))) (.mul (.mul (.var 0) (.var 1)) (.var 0))) (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.mul (.var 0) (.mul (.mul (.var 1) (.var 1)) (.var 1))))) (.mul (.mul (.var 0) (.mul (.mul (.var 1) (.var 1)) (.var 1))) (.mul (.var 0) (.mul (.var 1) (.var 1)))))
    (.add (.add (.mul (.var 0) (.var 1)) (.mul (.add (.mul (.mul (.mul (.var 1) (.var 1)) (.var 1)) (.var 1)) (.neg .one)) (.mul (.mul (.mul (.add .one .one) (.var 0)) (.var 0)) (.var 1)))) (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.neg .one)) (.mul (.var 0) (.var 1)))) (by decide +kernel)

theorem self_c2 (q u : Shell p) :
    q * (q * (u * u)) + (q * u) * (q * u) + (q * (u * u)) * q + (q * ((u * u) * u)) * (q * ((u * u) * u)) = q * (u * u) + (u * u * u * u + -1) * (q * q * u * u) + ((1 + 1 + 1 + 1) * q + -1) * (q * u * u) :=
  RE.sound (look [q, u])
    (.add (.add (.add (.mul (.var 0) (.mul (.var 0) (.mul (.var 1) (.var 1)))) (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))) (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.var 0))) (.mul (.mul (.var 0) (.mul (.mul (.var 1) (.var 1)) (.var 1))) (.mul (.var 0) (.mul (.mul (.var 1) (.var 1)) (.var 1)))))
    (.add (.add (.mul (.var 0) (.mul (.var 1) (.var 1))) (.mul (.add (.mul (.mul (.mul (.var 1) (.var 1)) (.var 1)) (.var 1)) (.neg .one)) (.mul (.mul (.mul (.var 0) (.var 0)) (.var 1)) (.var 1)))) (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.neg .one)) (.mul (.mul (.var 0) (.var 1)) (.var 1)))) (by decide +kernel)

theorem self_c3 (q u : Shell p) :
    q * (q * ((u * u) * u)) + (q * u) * (q * (u * u)) + (q * (u * u)) * (q * u) + (q * ((u * u) * u)) * q = q * ((u * u) * u) + (u * u * u * u + -1) * (0) + ((1 + 1 + 1 + 1) * q + -1) * (q * u * u * u) :=
  RE.sound (look [q, u])
    (.add (.add (.add (.mul (.var 0) (.mul (.var 0) (.mul (.mul (.var 1) (.var 1)) (.var 1)))) (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.mul (.var 1) (.var 1))))) (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.mul (.var 0) (.var 1)))) (.mul (.mul (.var 0) (.mul (.mul (.var 1) (.var 1)) (.var 1))) (.var 0)))
    (.add (.add (.mul (.var 0) (.mul (.mul (.var 1) (.var 1)) (.var 1))) (.mul (.add (.mul (.mul (.mul (.var 1) (.var 1)) (.var 1)) (.var 1)) (.neg .one)) .zero)) (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.neg .one)) (.mul (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.var 1)))) (by decide +kernel)

theorem ne_c0 (q u v : Shell p) :
    q * q + (q * u) * (q * ((v * v) * v)) + (q * (u * u)) * (q * (v * v)) + (q * ((u * u) * u)) * (q * v) = 0 + (v * v * v * v + -1) * (-(q * q * u * u * u * v * v * v * v * v) + -(q * q * u * u * u * v) + -(q * q * u * u * v * v)) + (1 + u * ((v * v) * v) + (u * ((v * v) * v)) * (u * ((v * v) * v)) + ((u * ((v * v) * v)) * (u * ((v * v) * v))) * (u * ((v * v) * v))) * (q * q) :=
  RE.sound (look [q, u, v])
    (.add (.add (.add (.mul (.var 0) (.var 0)) (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.mul (.mul (.var 2) (.var 2)) (.var 2))))) (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.mul (.var 0) (.mul (.var 2) (.var 2))))) (.mul (.mul (.var 0) (.mul (.mul (.var 1) (.var 1)) (.var 1))) (.mul (.var 0) (.var 2))))
    (.add (.add .zero (.mul (.add (.mul (.mul (.mul (.var 2) (.var 2)) (.var 2)) (.var 2)) (.neg .one)) (.add (.add (.neg (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 0)) (.var 1)) (.var 1)) (.var 1)) (.var 2)) (.var 2)) (.var 2)) (.var 2)) (.var 2))) (.neg (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 0)) (.var 1)) (.var 1)) (.var 1)) (.var 2)))) (.neg (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 0)) (.var 1)) (.var 1)) (.var 2)) (.var 2)))))) (.mul (.add (.add (.add .one (.mul (.var 1) (.mul (.mul (.var 2) (.var 2)) (.var 2)))) (.mul (.mul (.var 1) (.mul (.mul (.var 2) (.var 2)) (.var 2))) (.mul (.var 1) (.mul (.mul (.var 2) (.var 2)) (.var 2))))) (.mul (.mul (.mul (.var 1) (.mul (.mul (.var 2) (.var 2)) (.var 2))) (.mul (.var 1) (.mul (.mul (.var 2) (.var 2)) (.var 2)))) (.mul (.var 1) (.mul (.mul (.var 2) (.var 2)) (.var 2))))) (.mul (.var 0) (.var 0)))) (by decide +kernel)

theorem ne_c1 (q u v : Shell p) :
    q * (q * v) + (q * u) * q + (q * (u * u)) * (q * ((v * v) * v)) + (q * ((u * u) * u)) * (q * (v * v)) = 0 + (v * v * v * v + -1) * (-(q * q * u * u * u * v * v * v * v * v * v) + -(q * q * u * u * u * v * v) + -(q * q * u * u * v * v * v) + -(q * q * u)) + (1 + u * ((v * v) * v) + (u * ((v * v) * v)) * (u * ((v * v) * v)) + ((u * ((v * v) * v)) * (u * ((v * v) * v))) * (u * ((v * v) * v))) * ((q * q) * v) :=
  RE.sound (look [q, u, v])
    (.add (.add (.add (.mul (.var 0) (.mul (.var 0) (.var 2))) (.mul (.mul (.var 0) (.var 1)) (.var 0))) (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.mul (.var 0) (.mul (.mul (.var 2) (.var 2)) (.var 2))))) (.mul (.mul (.var 0) (.mul (.mul (.var 1) (.var 1)) (.var 1))) (.mul (.var 0) (.mul (.var 2) (.var 2)))))
    (.add (.add .zero (.mul (.add (.mul (.mul (.mul (.var 2) (.var 2)) (.var 2)) (.var 2)) (.neg .one)) (.add (.add (.add (.neg (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 0)) (.var 1)) (.var 1)) (.var 1)) (.var 2)) (.var 2)) (.var 2)) (.var 2)) (.var 2)) (.var 2))) (.neg (.mul (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 0)) (.var 1)) (.var 1)) (.var 1)) (.var 2)) (.var 2)))) (.neg (.mul (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 0)) (.var 1)) (.var 1)) (.var 2)) (.var 2)) (.var 2)))) (.neg (.mul (.mul (.var 0) (.var 0)) (.var 1)))))) (.mul (.add (.add (.add .one (.mul (.var 1) (.mul (.mul (.var 2) (.var 2)) (.var 2)))) (.mul (.mul (.var 1) (.mul (.mul (.var 2) (.var 2)) (.var 2))) (.mul (.var 1) (.mul (.mul (.var 2) (.var 2)) (.var 2))))) (.mul (.mul (.mul (.var 1) (.mul (.mul (.var 2) (.var 2)) (.var 2))) (.mul (.var 1) (.mul (.mul (.var 2) (.var 2)) (.var 2)))) (.mul (.var 1) (.mul (.mul (.var 2) (.var 2)) (.var 2))))) (.mul (.mul (.var 0) (.var 0)) (.var 2)))) (by decide +kernel)

theorem ne_c2 (q u v : Shell p) :
    q * (q * (v * v)) + (q * u) * (q * v) + (q * (u * u)) * q + (q * ((u * u) * u)) * (q * ((v * v) * v)) = 0 + (v * v * v * v + -1) * (-(q * q * u * u * u * v * v * v * v * v * v * v) + -(q * q * u * u * u * v * v * v) + -(q * q * u * u * v * v * v * v) + -(q * q * u * u) + -(q * q * u * v)) + (1 + u * ((v * v) * v) + (u * ((v * v) * v)) * (u * ((v * v) * v)) + ((u * ((v * v) * v)) * (u * ((v * v) * v))) * (u * ((v * v) * v))) * ((q * q) * (v * v)) :=
  RE.sound (look [q, u, v])
    (.add (.add (.add (.mul (.var 0) (.mul (.var 0) (.mul (.var 2) (.var 2)))) (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 2)))) (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.var 0))) (.mul (.mul (.var 0) (.mul (.mul (.var 1) (.var 1)) (.var 1))) (.mul (.var 0) (.mul (.mul (.var 2) (.var 2)) (.var 2)))))
    (.add (.add .zero (.mul (.add (.mul (.mul (.mul (.var 2) (.var 2)) (.var 2)) (.var 2)) (.neg .one)) (.add (.add (.add (.add (.neg (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 0)) (.var 1)) (.var 1)) (.var 1)) (.var 2)) (.var 2)) (.var 2)) (.var 2)) (.var 2)) (.var 2)) (.var 2))) (.neg (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 0)) (.var 1)) (.var 1)) (.var 1)) (.var 2)) (.var 2)) (.var 2)))) (.neg (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 0)) (.var 1)) (.var 1)) (.var 2)) (.var 2)) (.var 2)) (.var 2)))) (.neg (.mul (.mul (.mul (.var 0) (.var 0)) (.var 1)) (.var 1)))) (.neg (.mul (.mul (.mul (.var 0) (.var 0)) (.var 1)) (.var 2)))))) (.mul (.add (.add (.add .one (.mul (.var 1) (.mul (.mul (.var 2) (.var 2)) (.var 2)))) (.mul (.mul (.var 1) (.mul (.mul (.var 2) (.var 2)) (.var 2))) (.mul (.var 1) (.mul (.mul (.var 2) (.var 2)) (.var 2))))) (.mul (.mul (.mul (.var 1) (.mul (.mul (.var 2) (.var 2)) (.var 2))) (.mul (.var 1) (.mul (.mul (.var 2) (.var 2)) (.var 2)))) (.mul (.var 1) (.mul (.mul (.var 2) (.var 2)) (.var 2))))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))))) (by decide +kernel)

theorem ne_c3 (q u v : Shell p) :
    q * (q * ((v * v) * v)) + (q * u) * (q * (v * v)) + (q * (u * u)) * (q * v) + (q * ((u * u) * u)) * q = 0 + (v * v * v * v + -1) * (-(q * q * u * u * u * v * v * v * v * v * v * v * v) + -(q * q * u * u * u * v * v * v * v) + -(q * q * u * u * v * v * v * v * v) + -(q * q * u * u * u) + -(q * q * u * u * v) + -(q * q * u * v * v)) + (1 + u * ((v * v) * v) + (u * ((v * v) * v)) * (u * ((v * v) * v)) + ((u * ((v * v) * v)) * (u * ((v * v) * v))) * (u * ((v * v) * v))) * ((q * q) * ((v * v) * v)) :=
  RE.sound (look [q, u, v])
    (.add (.add (.add (.mul (.var 0) (.mul (.var 0) (.mul (.mul (.var 2) (.var 2)) (.var 2)))) (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.mul (.var 2) (.var 2))))) (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.mul (.var 0) (.var 2)))) (.mul (.mul (.var 0) (.mul (.mul (.var 1) (.var 1)) (.var 1))) (.var 0)))
    (.add (.add .zero (.mul (.add (.mul (.mul (.mul (.var 2) (.var 2)) (.var 2)) (.var 2)) (.neg .one)) (.add (.add (.add (.add (.add (.neg (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 0)) (.var 1)) (.var 1)) (.var 1)) (.var 2)) (.var 2)) (.var 2)) (.var 2)) (.var 2)) (.var 2)) (.var 2)) (.var 2))) (.neg (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 0)) (.var 1)) (.var 1)) (.var 1)) (.var 2)) (.var 2)) (.var 2)) (.var 2)))) (.neg (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 0)) (.var 1)) (.var 1)) (.var 2)) (.var 2)) (.var 2)) (.var 2)) (.var 2)))) (.neg (.mul (.mul (.mul (.mul (.var 0) (.var 0)) (.var 1)) (.var 1)) (.var 1)))) (.neg (.mul (.mul (.mul (.mul (.var 0) (.var 0)) (.var 1)) (.var 1)) (.var 2)))) (.neg (.mul (.mul (.mul (.mul (.var 0) (.var 0)) (.var 1)) (.var 2)) (.var 2)))))) (.mul (.add (.add (.add .one (.mul (.var 1) (.mul (.mul (.var 2) (.var 2)) (.var 2)))) (.mul (.mul (.var 1) (.mul (.mul (.var 2) (.var 2)) (.var 2))) (.mul (.var 1) (.mul (.mul (.var 2) (.var 2)) (.var 2))))) (.mul (.mul (.mul (.var 1) (.mul (.mul (.var 2) (.var 2)) (.var 2))) (.mul (.var 1) (.mul (.mul (.var 2) (.var 2)) (.var 2)))) (.mul (.var 1) (.mul (.mul (.var 2) (.var 2)) (.var 2))))) (.mul (.mul (.var 0) (.var 0)) (.mul (.mul (.var 2) (.var 2)) (.var 2))))) (by decide +kernel)

theorem F_c0 (q u : Shell p) :
    0 * q + 1 * (q * ((u * u) * u)) + 0 * (q * (u * u)) + 0 * (q * u) = ((u * u) * u) * q + (u * u * u * u + -1) * (0) :=
  RE.sound (look [q, u])
    (.add (.add (.add (.mul .zero (.var 0)) (.mul .one (.mul (.var 0) (.mul (.mul (.var 1) (.var 1)) (.var 1))))) (.mul .zero (.mul (.var 0) (.mul (.var 1) (.var 1))))) (.mul .zero (.mul (.var 0) (.var 1))))
    (.add (.mul (.mul (.mul (.var 1) (.var 1)) (.var 1)) (.var 0)) (.mul (.add (.mul (.mul (.mul (.var 1) (.var 1)) (.var 1)) (.var 1)) (.neg .one)) .zero)) (by decide +kernel)

theorem F_c1 (q u : Shell p) :
    0 * (q * u) + 1 * q + 0 * (q * ((u * u) * u)) + 0 * (q * (u * u)) = ((u * u) * u) * (q * u) + (u * u * u * u + -1) * (-q) :=
  RE.sound (look [q, u])
    (.add (.add (.add (.mul .zero (.mul (.var 0) (.var 1))) (.mul .one (.var 0))) (.mul .zero (.mul (.var 0) (.mul (.mul (.var 1) (.var 1)) (.var 1))))) (.mul .zero (.mul (.var 0) (.mul (.var 1) (.var 1)))))
    (.add (.mul (.mul (.mul (.var 1) (.var 1)) (.var 1)) (.mul (.var 0) (.var 1))) (.mul (.add (.mul (.mul (.mul (.var 1) (.var 1)) (.var 1)) (.var 1)) (.neg .one)) (.neg (.var 0)))) (by decide +kernel)

theorem F_c2 (q u : Shell p) :
    0 * (q * (u * u)) + 1 * (q * u) + 0 * q + 0 * (q * ((u * u) * u)) = ((u * u) * u) * (q * (u * u)) + (u * u * u * u + -1) * (-(q * u)) :=
  RE.sound (look [q, u])
    (.add (.add (.add (.mul .zero (.mul (.var 0) (.mul (.var 1) (.var 1)))) (.mul .one (.mul (.var 0) (.var 1)))) (.mul .zero (.var 0))) (.mul .zero (.mul (.var 0) (.mul (.mul (.var 1) (.var 1)) (.var 1)))))
    (.add (.mul (.mul (.mul (.var 1) (.var 1)) (.var 1)) (.mul (.var 0) (.mul (.var 1) (.var 1)))) (.mul (.add (.mul (.mul (.mul (.var 1) (.var 1)) (.var 1)) (.var 1)) (.neg .one)) (.neg (.mul (.var 0) (.var 1))))) (by decide +kernel)

theorem F_c3 (q u : Shell p) :
    0 * (q * ((u * u) * u)) + 1 * (q * (u * u)) + 0 * (q * u) + 0 * q = ((u * u) * u) * (q * ((u * u) * u)) + (u * u * u * u + -1) * (-(q * u * u)) :=
  RE.sound (look [q, u])
    (.add (.add (.add (.mul .zero (.mul (.var 0) (.mul (.mul (.var 1) (.var 1)) (.var 1)))) (.mul .one (.mul (.var 0) (.mul (.var 1) (.var 1))))) (.mul .zero (.mul (.var 0) (.var 1)))) (.mul .zero (.var 0)))
    (.add (.mul (.mul (.mul (.var 1) (.var 1)) (.var 1)) (.mul (.var 0) (.mul (.mul (.var 1) (.var 1)) (.var 1)))) (.mul (.add (.mul (.mul (.mul (.var 1) (.var 1)) (.var 1)) (.var 1)) (.neg .one)) (.neg (.mul (.mul (.var 0) (.var 1)) (.var 1))))) (by decide +kernel)

theorem sum_c0 (q w : Shell p) :
    q + q + q + q = 1 + ((1 + 1 + 1 + 1) * q + -1) * (1) :=
  RE.sound (look [q, w])
    (.add (.add (.add (.var 0) (.var 0)) (.var 0)) (.var 0))
    (.add .one (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.neg .one)) .one)) (by decide +kernel)

theorem sum_c1 (q w : Shell p) :
    q + q * w + -q + -(q * w) = 0 + ((1 + 1 + 1 + 1) * q + -1) * (0) :=
  RE.sound (look [q, w])
    (.add (.add (.add (.var 0) (.mul (.var 0) (.var 1))) (.neg (.var 0))) (.neg (.mul (.var 0) (.var 1))))
    (.add .zero (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.neg .one)) .zero)) (by decide +kernel)

theorem sum_c2 (q w : Shell p) :
    q + -q + q + -q = 0 + ((1 + 1 + 1 + 1) * q + -1) * (0) :=
  RE.sound (look [q, w])
    (.add (.add (.add (.var 0) (.neg (.var 0))) (.var 0)) (.neg (.var 0)))
    (.add .zero (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.neg .one)) .zero)) (by decide +kernel)

theorem sum_c3 (q w : Shell p) :
    q + -(q * w) + -q + q * w = 0 + ((1 + 1 + 1 + 1) * q + -1) * (0) :=
  RE.sound (look [q, w])
    (.add (.add (.add (.var 0) (.neg (.mul (.var 0) (.var 1)))) (.neg (.var 0))) (.mul (.var 0) (.var 1)))
    (.add .zero (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.neg .one)) .zero)) (by decide +kernel)

theorem half_id (q : Shell p) :
    (1 + 1) * (q + q) = 1 + ((1 + 1 + 1 + 1) * q + -1) * (1) :=
  RE.sound (look [q])
    (.mul (.add .one .one) (.add (.var 0) (.var 0)))
    (.add .one (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.neg .one)) .one)) (by decide +kernel)

/-! ## The algebra of combinations -/

variable {κ : Nat} {g : Shell p}

theorem comb_add (a0 a1 a2 a3 b0 b1 b2 b3 : Shell p) (k j : Nat) :
    comb g κ a0 a1 a2 a3 k j + comb g κ b0 b1 b2 b3 k j = comb g κ (a0 + b0) (a1 + b1) (a2 + b2) (a3 + b3) k j :=
  comb_add_id a0 a1 a2 a3 b0 b1 b2 b3 _ _ _ _

theorem comb_smul (c a0 a1 a2 a3 : Shell p) (k j : Nat) :
    c * comb g κ a0 a1 a2 a3 k j = comb g κ (c * a0) (c * a1) (c * a2) (c * a3) k j :=
  comb_smul_id c a0 a1 a2 a3 _ _ _ _

theorem comb_zero (k j : Nat) : comb g κ 0 0 0 0 k j = 0 := comb_zero_id _ _ _ _
theorem comb_idm (k j : Nat) : comb g κ 1 0 0 0 k j = idm k j := comb_idm_id _ _ _ _
theorem comb_Fmat (k j : Nat) : comb g κ 0 1 0 0 k j = Fmat g κ k j := comb_Fmat_id _ _ _ _
theorem comb_J (k j : Nat) : comb g κ 0 0 1 0 k j = J (p - 1) k j := comb_J_id _ _ _ _
theorem comb_FJ (k j : Nat) : comb g κ 0 0 0 1 k j = FJ g κ k j := comb_FJ_id _ _ _ _

/-! ## The constants `w = −i` and `q = −κ` -/

theorem pow_two_mul (a : Shell p) (n : Nat) : a ^ (2 * n) = a ^ n * a ^ n := by
  rw [pow_mul, pow_mul_comm, pow_two]

theorem pow_three_mul (a : Shell p) (n : Nat) : a ^ (3 * n) = a ^ n * a ^ n * a ^ n := by
  rw [pow_mul, pow_mul_comm, pow_succ, pow_two]

theorem w_sq (F : Frame p κ g) : -(quarterTurn g κ) * -(quarterTurn g κ) = -1 := by
  rw [neg_mul_neg, F.quarter_turn_sq]

theorem w_four (F : Frame p κ g) : (-(quarterTurn g κ)) ^ 4 = 1 := by
  rw [show (4 : Nat) = 2 * 2 from rfl, pow_mul, pow_two, pow_two, w_sq F, neg_mul_neg, one_mul]

/-- `w^ℓ` is a fourth root of unity, in the form the normaliser takes. -/
theorem u_four (F : Frame p κ g) (ℓ : Nat) :
    (-(quarterTurn g κ)) ^ ℓ * (-(quarterTurn g κ)) ^ ℓ * (-(quarterTurn g κ)) ^ ℓ * (-(quarterTurn g κ)) ^ ℓ + -1 = 0 := by
  have e : ((-(quarterTurn g κ)) ^ ℓ) ^ 4 = (-(quarterTurn g κ)) ^ ℓ * (-(quarterTurn g κ)) ^ ℓ *
      (-(quarterTurn g κ)) ^ ℓ * (-(quarterTurn g κ)) ^ ℓ := by
    rw [pow_succ, pow_succ, pow_succ, pow_one]
  rw [← e, pow_mul_comm, w_four F, one_pow, add_neg]

theorem w_pow_mod (F : Frame p κ g) (l : Nat) : (-(quarterTurn g κ)) ^ l = (-(quarterTurn g κ)) ^ (l % 4) := by
  obtain ⟨m, hm⟩ := FRC.Nat.mod_spec 4 (by decide) l
  rw [congrArg (fun e => (-(quarterTurn g κ)) ^ e) hm, pow_add, pow_mul, w_four F, one_pow, one_mul]

theorem neg_one_ne_one (F : Frame p κ g) : (-1 : Shell p) ≠ 1 := fun h => F.two_ne_zero (by
  rw [two_eq_one_add_one]
  calc (1 : Shell p) + 1 = 1 + -1 := by rw [h]
    _ = 0 := add_neg 1)

theorem neg_w (F : Frame p κ g) : -(-(quarterTurn g κ)) = -(quarterTurn g κ) * -(quarterTurn g κ) * -(quarterTurn g κ) :=
  red1 (neg_w_id (-(ofNat κ)) (-(quarterTurn g κ))) (hjj F)

/-- `i = w³`: the quarter-turn is the cube of its inverse. -/
theorem quarter_eq (F : Frame p κ g) : quarterTurn g κ = -(quarterTurn g κ) * -(quarterTurn g κ) * -(quarterTurn g κ) := by
  rw [← neg_w F, neg_neg]

theorem quarter_pow (F : Frame p κ g) (ℓ : Nat) :
    quarterTurn g κ ^ ℓ = (-(quarterTurn g κ)) ^ ℓ * (-(quarterTurn g κ)) ^ ℓ * (-(quarterTurn g κ)) ^ ℓ :=
  (congrArg (· ^ ℓ) (quarter_eq F)).trans (by rw [mul_pow, mul_pow])

theorem w_ne_one (F : Frame p κ g) : -(quarterTurn g κ) ≠ 1 := fun h =>
  F.neg_one_ne_one (by rw [← w_sq F, h, mul_one])

theorem w_sq_ne_one (F : Frame p κ g) : -(quarterTurn g κ) * -(quarterTurn g κ) ≠ 1 := by
  rw [w_sq F]; exact F.neg_one_ne_one

theorem w_cube_ne_one (F : Frame p κ g) : -(quarterTurn g κ) * -(quarterTurn g κ) * -(quarterTurn g κ) ≠ 1 := fun h => by
  have hw : -(quarterTurn g κ) = -1 := by rw [← neg_neg (-(quarterTurn g κ)), neg_w F, h]
  exact F.neg_one_ne_one (by rw [← w_sq F, hw, neg_mul_neg, one_mul])

/-- The nontrivial fourth roots: `w^r ≠ 1` for `0 < r < 4`. -/
theorem w_pow_ne_one (F : Frame p κ g) : ∀ {r : Nat}, 0 < r → r < 4 → (-(quarterTurn g κ)) ^ r ≠ 1
  | 0, h, _ => absurd h (Nat.lt_irrefl 0)
  | 1, _, _ => by rw [pow_one]; exact w_ne_one F
  | 2, _, _ => by rw [pow_two]; exact w_sq_ne_one F
  | 3, _, _ => by rw [pow_succ, pow_two]; exact w_cube_ne_one F
  | n + 4, _, h => absurd (Nat.lt_of_lt_of_le h (Nat.le_add_left 4 n)) (Nat.lt_irrefl _)

theorem orth_index : ∀ ℓ, ℓ < 4 → ∀ m, m < 4 → ℓ ≠ m → 0 < (ℓ + 3 * m) % 4 := by decide

/-- The geometric sum of the nontrivial fourth root `x = w^ℓ (w^m)³ = i^{m−ℓ}`, `ℓ ≠ m` below 4. -/
theorem geo_zero (F : Frame p κ g) {ℓ m : Nat} (hℓ : ℓ < 4) (hm : m < 4) (hne : ℓ ≠ m) :
    1 + (-(quarterTurn g κ)) ^ ℓ * ((-(quarterTurn g κ)) ^ m * (-(quarterTurn g κ)) ^ m * (-(quarterTurn g κ)) ^ m) +
      (-(quarterTurn g κ)) ^ ℓ * ((-(quarterTurn g κ)) ^ m * (-(quarterTurn g κ)) ^ m * (-(quarterTurn g κ)) ^ m) *
        ((-(quarterTurn g κ)) ^ ℓ * ((-(quarterTurn g κ)) ^ m * (-(quarterTurn g κ)) ^ m * (-(quarterTurn g κ)) ^ m)) +
      (-(quarterTurn g κ)) ^ ℓ * ((-(quarterTurn g κ)) ^ m * (-(quarterTurn g κ)) ^ m * (-(quarterTurn g κ)) ^ m) *
        ((-(quarterTurn g κ)) ^ ℓ * ((-(quarterTurn g κ)) ^ m * (-(quarterTurn g κ)) ^ m * (-(quarterTurn g κ)) ^ m)) *
        ((-(quarterTurn g κ)) ^ ℓ * ((-(quarterTurn g κ)) ^ m * (-(quarterTurn g κ)) ^ m * (-(quarterTurn g κ)) ^ m)) = 0 := by
  have ex : (-(quarterTurn g κ)) ^ ℓ * ((-(quarterTurn g κ)) ^ m * (-(quarterTurn g κ)) ^ m * (-(quarterTurn g κ)) ^ m) =
      (-(quarterTurn g κ)) ^ (ℓ + 3 * m) := by
    rw [pow_add, pow_mul, pow_mul_comm, pow_succ, pow_two]
  have hx4 : ((-(quarterTurn g κ)) ^ (ℓ + 3 * m)) ^ 4 = 1 := by rw [pow_mul_comm, w_four F, one_pow]
  have hx1 : (-(quarterTurn g κ)) ^ (ℓ + 3 * m) ≠ 1 := by
    rw [w_pow_mod F]
    exact w_pow_ne_one F (orth_index ℓ hℓ m hm hne) (Nat.mod_lt _ (by decide))
  have h4 : (0 : Shell p) + ((-(quarterTurn g κ)) ^ (ℓ + 3 * m)) ^ 0 + ((-(quarterTurn g κ)) ^ (ℓ + 3 * m)) ^ 1 +
      ((-(quarterTurn g κ)) ^ (ℓ + 3 * m)) ^ 2 + ((-(quarterTurn g κ)) ^ (ℓ + 3 * m)) ^ 3 = 0 :=
    F.geom_sum_eq_zero 4 hx4 hx1
  rw [zero_add, pow_zero, pow_one, pow_two, pow_succ, pow_two] at h4
  rw [ex]; exact h4

/-! ## The projectors in coefficient form -/

/-- `Π_ℓ = q (I + u F + u² J + u³ F J)` with `u = w^ℓ`. -/
theorem proj_eq (ℓ k j : Nat) :
    proj g κ ℓ k j = comb g κ (-(ofNat κ)) (-(ofNat κ) * (-(quarterTurn g κ)) ^ ℓ)
      (-(ofNat κ) * ((-(quarterTurn g κ)) ^ ℓ * (-(quarterTurn g κ)) ^ ℓ))
      (-(ofNat κ) * ((-(quarterTurn g κ)) ^ ℓ * (-(quarterTurn g κ)) ^ ℓ * (-(quarterTurn g κ)) ^ ℓ)) k j := by
  show comb g κ (-(ofNat κ)) (-(ofNat κ) * (-(quarterTurn g κ)) ^ ℓ) (-(ofNat κ) * (-(quarterTurn g κ)) ^ (2 * ℓ))
    (-(ofNat κ) * (-(quarterTurn g κ)) ^ (3 * ℓ)) k j = _
  rw [pow_two_mul, pow_three_mul]

theorem proj_zero_eq (k j : Nat) : proj g κ 0 k j = comb g κ (-(ofNat κ)) (-(ofNat κ)) (-(ofNat κ)) (-(ofNat κ)) k j := by
  rw [proj_eq, pow_zero, one_mul, one_mul, mul_one]

theorem proj_one_eq (F : Frame p κ g) (k j : Nat) :
    proj g κ 1 k j = comb g κ (-(ofNat κ)) (-(ofNat κ) * -(quarterTurn g κ)) (-(-(ofNat κ)))
      (-(-(ofNat κ) * -(quarterTurn g κ))) k j := by
  rw [proj_eq, pow_one, red1 (proj1_c2 _ _) (hjj F), red1 (proj1_c3 _ _) (hjj F)]

theorem proj_two_eq (F : Frame p κ g) (k j : Nat) :
    proj g κ 2 k j = comb g κ (-(ofNat κ)) (-(-(ofNat κ))) (-(ofNat κ)) (-(-(ofNat κ))) k j := by
  rw [proj_eq, pow_two, red1 (proj2_c1 _ _) (hjj F), red1 (proj2_c2 _ _) (hjj F), red1 (proj2_c3 _ _) (hjj F)]

theorem proj_three_eq (F : Frame p κ g) (k j : Nat) :
    proj g κ 3 k j = comb g κ (-(ofNat κ)) (-(-(ofNat κ) * -(quarterTurn g κ))) (-(-(ofNat κ)))
      (-(ofNat κ) * -(quarterTurn g κ)) k j := by
  rw [proj_eq, pow_succ, pow_two, red1 (proj3_c1 _ _) (hjj F), red1 (proj3_c2 _ _) (hjj F), red1 (proj3_c3 _ _) (hjj F)]

/-! ## The projector algebra (6:C2) -/

theorem proj_mul_pt (ℓ m k j l : Nat) :
    proj g κ ℓ k l * proj g κ m l j =
      comb g κ (-(ofNat κ)) (-(ofNat κ) * (-(quarterTurn g κ)) ^ ℓ)
        (-(ofNat κ) * ((-(quarterTurn g κ)) ^ ℓ * (-(quarterTurn g κ)) ^ ℓ))
        (-(ofNat κ) * ((-(quarterTurn g κ)) ^ ℓ * (-(quarterTurn g κ)) ^ ℓ * (-(quarterTurn g κ)) ^ ℓ)) k l *
      comb g κ (-(ofNat κ)) (-(ofNat κ) * (-(quarterTurn g κ)) ^ m)
        (-(ofNat κ) * ((-(quarterTurn g κ)) ^ m * (-(quarterTurn g κ)) ^ m))
        (-(ofNat κ) * ((-(quarterTurn g κ)) ^ m * (-(quarterTurn g κ)) ^ m * (-(quarterTurn g κ)) ^ m)) l j := by
  rw [proj_eq, proj_eq]

/-- 6:C2, the idempotence: `Π_ℓ Π_ℓ = Π_ℓ`, the four coefficients `q² Σ u^a u^{r−a} = q u^r` with `u⁴ = 1`, `4q = 1`. -/
theorem proj_mul_self (F : Frame p κ g) (ℓ : Nat) {k j : Nat} (hk : k < p - 1) (hj : j < p - 1) :
    sumRange (fun l => proj g κ ℓ k l * proj g κ ℓ l j) (p - 1) = proj g κ ℓ k j := by
  have hu := u_four F ℓ
  have hq := hq F
  rw [sum_congr _ (fun l _ => proj_mul_pt ℓ ℓ k j l), comb_mul F hk hj, proj_eq,
    red2 (self_c0 _ _) hu hq, red2 (self_c1 _ _) hu hq, red2 (self_c2 _ _) hu hq, red2 (self_c3 _ _) hu hq]

/-- 6:C2, the orthogonality: `Π_ℓ Π_m = 0` for `ℓ ≠ m` below 4, each coefficient `q² v^r (1 + x + x² + x³)` with
`x = u v³` a nontrivial fourth root of unity. -/
theorem proj_mul_ne (F : Frame p κ g) {ℓ m : Nat} (hℓ : ℓ < 4) (hm : m < 4) (hne : ℓ ≠ m) {k j : Nat}
    (hk : k < p - 1) (hj : j < p - 1) :
    sumRange (fun l => proj g κ ℓ k l * proj g κ m l j) (p - 1) = 0 := by
  have hv := u_four F m
  have hx := geo_zero F hℓ hm hne
  rw [sum_congr _ (fun l _ => proj_mul_pt ℓ m k j l), comb_mul F hk hj,
    red2 (ne_c0 _ _ _) hv hx, red2 (ne_c1 _ _ _) hv hx, red2 (ne_c2 _ _ _) hv hx, red2 (ne_c3 _ _ _) hv hx]
  exact comb_zero k j

/-- 6:C2, the resolution of the identity: `Π₀ + Π₁ + Π₂ + Π₃ = I`. -/
theorem sum_proj (F : Frame p κ g) (k j : Nat) :
    proj g κ 0 k j + proj g κ 1 k j + proj g κ 2 k j + proj g κ 3 k j = idm k j := by
  rw [proj_zero_eq, proj_one_eq F, proj_two_eq F, proj_three_eq F, comb_add, comb_add, comb_add,
    red1 (sum_c0 (-(ofNat κ)) (-(quarterTurn g κ))) (hq F), red1 (sum_c1 _ _) (hq F),
    red1 (sum_c2 (-(ofNat κ)) (-(quarterTurn g κ))) (hq F), red1 (sum_c3 _ _) (hq F)]
  exact comb_idm k j

theorem Fmat_proj_pt (ℓ k j l : Nat) :
    Fmat g κ k l * proj g κ ℓ l j =
      comb g κ 0 1 0 0 k l *
      comb g κ (-(ofNat κ)) (-(ofNat κ) * (-(quarterTurn g κ)) ^ ℓ)
        (-(ofNat κ) * ((-(quarterTurn g κ)) ^ ℓ * (-(quarterTurn g κ)) ^ ℓ))
        (-(ofNat κ) * ((-(quarterTurn g κ)) ^ ℓ * (-(quarterTurn g κ)) ^ ℓ * (-(quarterTurn g κ)) ^ ℓ)) l j := by
  rw [comb_Fmat, proj_eq]

/-- 6:C2, the eigen-relation: `F Π_ℓ = i^ℓ Π_ℓ`, the coefficients of `F Π_ℓ` the cyclic shift of `Π_ℓ`'s and
`i^ℓ = u³` with `u = w^ℓ`. -/
theorem Fmat_proj (F : Frame p κ g) (ℓ : Nat) {k j : Nat} (hk : k < p - 1) (hj : j < p - 1) :
    sumRange (fun l => Fmat g κ k l * proj g κ ℓ l j) (p - 1) = quarterTurn g κ ^ ℓ * proj g κ ℓ k j := by
  have hu := u_four F ℓ
  rw [sum_congr _ (fun l _ => Fmat_proj_pt ℓ k j l), comb_mul F hk hj, quarter_pow F ℓ, proj_eq, comb_smul,
    red1 (F_c0 _ _) hu, red1 (F_c1 _ _) hu, red1 (F_c2 _ _) hu, red1 (F_c3 _ _) hu]

/-! ## The two sums (6:C5) -/

/-- 6:C5, the even sum: `Π₀ + Π₂ = (q + q)(I + J)`, with `q + q = 2⁻¹` (`half`). -/
theorem proj_even_sum (F : Frame p κ g) (k j : Nat) :
    proj g κ 0 k j + proj g κ 2 k j = (-(ofNat κ) + -(ofNat κ)) * (idm k j + J (p - 1) k j) := by
  rw [proj_zero_eq, proj_two_eq F, comb_add]
  exact even_sum_id (-(ofNat κ)) (-(quarterTurn g κ)) _ _ _ _

/-- 6:C5, the odd sum: `Π₁ + Π₃ = (q + q)(I − J)`. -/
theorem proj_odd_sum (F : Frame p κ g) (k j : Nat) :
    proj g κ 1 k j + proj g κ 3 k j = (-(ofNat κ) + -(ofNat κ)) * (idm k j + -(J (p - 1) k j)) := by
  rw [proj_one_eq F, proj_three_eq F, comb_add]
  exact odd_sum_id (-(ofNat κ)) (-(quarterTurn g κ)) _ _ _ _

/-- 6:C5, the half: `2 (q + q) = 1`, so `q + q = 2⁻¹ = −2κ`. -/
theorem half (F : Frame p κ g) : (1 + 1 : Shell p) * (-(ofNat κ) + -(ofNat κ)) = 1 :=
  red1 (half_id (-(ofNat κ))) (hq F)

end Frame
end Shell
end FRC
