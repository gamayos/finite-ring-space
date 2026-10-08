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

theorem frft_mul_id (v0 v1 v2 v3 P0 P1 P2 P3 Q : Shell p) :
    (v0 * P0 + v1 * P1 + v2 * P2 + v3 * P3) * Q = v0 * (P0 * Q) + v1 * (P1 * Q) + v2 * (P2 * Q) + v3 * (P3 * Q) :=
  RE.sound (look [v0, v1, v2, v3, P0, P1, P2, P3, Q])
    (.mul (.add (.add (.add (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 5))) (.mul (.var 2) (.var 6))) (.mul (.var 3) (.var 7))) (.var 8))
    (.add (.add (.add (.mul (.var 0) (.mul (.var 4) (.var 8))) (.mul (.var 1) (.mul (.var 5) (.var 8)))) (.mul (.var 2) (.mul (.var 6) (.var 8)))) (.mul (.var 3) (.mul (.var 7) (.var 8)))) (by decide +kernel)

theorem entry21_one (q i A B : Shell p) :
    q * 0 + (q * -i) * (i * A) + -(-q) * 0 + -(q * -i) * (i * B) = q * (A + -B) + (i * i + 1) * (-(q * A) + q * B) :=
  RE.sound (look [q, i, A, B])
    (.add (.add (.add (.mul (.var 0) .zero) (.mul (.mul (.var 0) (.neg (.var 1))) (.mul (.var 1) (.var 2)))) (.mul (.neg (.neg (.var 0))) .zero)) (.mul (.neg (.mul (.var 0) (.neg (.var 1)))) (.mul (.var 1) (.var 3))))
    (.add (.mul (.var 0) (.add (.var 2) (.neg (.var 3)))) (.mul (.add (.mul (.var 1) (.var 1)) .one) (.add (.neg (.mul (.var 0) (.var 2))) (.mul (.var 0) (.var 3))))) (by decide +kernel)

theorem entry21_three (q i A B : Shell p) :
    q * 0 + -(q * -i) * (i * A) + -(-q) * 0 + (q * -i) * (i * B) = -(q * (A + -B)) + (i * i + 1) * (q * A + -(q * B)) :=
  RE.sound (look [q, i, A, B])
    (.add (.add (.add (.mul (.var 0) .zero) (.mul (.neg (.mul (.var 0) (.neg (.var 1)))) (.mul (.var 1) (.var 2)))) (.mul (.neg (.neg (.var 0))) .zero)) (.mul (.mul (.var 0) (.neg (.var 1))) (.mul (.var 1) (.var 3))))
    (.add (.neg (.mul (.var 0) (.add (.var 2) (.neg (.var 3))))) (.mul (.add (.mul (.var 1) (.var 1)) .one) (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 0) (.var 3)))))) (by decide +kernel)

theorem entry00_zero (q i : Shell p) :
    q * 1 + q * i + q * 1 + q * i = (q + q) * (1 + i) :=
  RE.sound (look [q, i])
    (.add (.add (.add (.mul (.var 0) .one) (.mul (.var 0) (.var 1))) (.mul (.var 0) .one)) (.mul (.var 0) (.var 1)))
    (.mul (.add (.var 0) (.var 0)) (.add .one (.var 1))) (by decide +kernel)

theorem entry00_two (q i : Shell p) :
    q * 1 + -q * i + q * 1 + -q * i = (q + q) * (1 + -i) :=
  RE.sound (look [q, i])
    (.add (.add (.add (.mul (.var 0) .one) (.mul (.neg (.var 0)) (.var 1))) (.mul (.var 0) .one)) (.mul (.neg (.var 0)) (.var 1)))
    (.mul (.add (.var 0) (.var 0)) (.add .one (.neg (.var 1)))) (by decide +kernel)

theorem row_zero_id (q jj u i : Shell p) :
    NF0 q jj u * 0 + NF1 q jj u * i + NF2 q jj u * 0 + NF3 q jj u * i = (q + q) * (1 + -(u * u)) * i :=
  RE.sound (look [q, jj, u, i])
    (.add (.add (.add (.mul (.mul (.var 0) (.add (.add (.add .one (.var 2)) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 2) (.var 2)) (.var 2)))) .zero) (.mul (.mul (.var 0) (.add (.add (.add .one (.mul (.var 1) (.var 2))) (.neg (.mul (.var 2) (.var 2)))) (.neg (.mul (.var 1) (.mul (.mul (.var 2) (.var 2)) (.var 2)))))) (.var 3))) (.mul (.mul (.var 0) (.add (.add (.add .one (.neg (.var 2))) (.mul (.var 2) (.var 2))) (.neg (.mul (.mul (.var 2) (.var 2)) (.var 2))))) .zero)) (.mul (.mul (.var 0) (.add (.add (.add .one (.neg (.mul (.var 1) (.var 2)))) (.neg (.mul (.var 2) (.var 2)))) (.mul (.var 1) (.mul (.mul (.var 2) (.var 2)) (.var 2))))) (.var 3)))
    (.mul (.mul (.add (.var 0) (.var 0)) (.add .one (.neg (.mul (.var 2) (.var 2))))) (.var 3)) (by decide +kernel)

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

/-! ## The character sector, nonvanishing, faithfulness and the domains (T03) -/

theorem proj_mul (F : Frame p κ g) {ℓ m : Nat} (hℓ : ℓ < 4) (hm : m < 4) {k j : Nat} (hk : k < p - 1) (hj : j < p - 1) :
    sumRange (fun l => proj g κ ℓ k l * proj g κ m l j) (p - 1) = if ℓ = m then proj g κ ℓ k j else 0 :=
  match Nat.decEq ℓ m with
  | isTrue e => by rw [ite_eq_left e]; subst e; exact proj_mul_self F ℓ hk hj
  | isFalse e => by rw [ite_eq_right e]; exact proj_mul_ne F hℓ hm e hk hj

theorem frft_mul_pt (z : Shell p) (s m k j l : Nat) :
    frft g κ z s k l * proj g κ m l j =
      (z ^ s) ^ 0 * (proj g κ 0 k l * proj g κ m l j) + (z ^ s) ^ 1 * (proj g κ 1 k l * proj g κ m l j) +
      (z ^ s) ^ 2 * (proj g κ 2 k l * proj g κ m l j) + (z ^ s) ^ 3 * (proj g κ 3 k l * proj g κ m l j) :=
  frft_mul_id _ _ _ _ _ _ _ _ _

/-- 6:C4, 6:E6, the character sector: `F^{[s]} Π_m = (z^s)^m Π_m` on every projector, `m < 4`; the family acts on
`Π_m`'s range by the character `s ↦ z^{ms}`. -/
theorem frft_proj (F : Frame p κ g) (z : Shell p) (s : Nat) {m : Nat} (hm : m < 4) {k j : Nat} (hk : k < p - 1)
    (hj : j < p - 1) :
    sumRange (fun l => frft g κ z s k l * proj g κ m l j) (p - 1) = (z ^ s) ^ m * proj g κ m k j := by
  rw [sum_congr _ (fun l _ => frft_mul_pt z s m k j l), sum_add, sum_add, sum_add, sum_mul_left, sum_mul_left,
    sum_mul_left, sum_mul_left, proj_mul F (Nat.zero_lt_succ 3) hm hk hj, proj_mul F (by decide : (1 : Nat) < 4) hm hk hj,
    proj_mul F (by decide : (2 : Nat) < 4) hm hk hj, proj_mul F (by decide : (3 : Nat) < 4) hm hk hj]
  match m, hm with
  | 0, _ => rw [ite_eq_left rfl, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
      mul_zero, mul_zero, mul_zero, add_zero, add_zero, add_zero]
  | 1, _ => rw [ite_eq_right (by decide), ite_eq_left rfl, ite_eq_right (by decide), ite_eq_right (by decide),
      mul_zero, mul_zero, mul_zero, zero_add, add_zero, add_zero]
  | 2, _ => rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl, ite_eq_right (by decide),
      mul_zero, mul_zero, mul_zero, zero_add, zero_add, add_zero]
  | 3, _ => rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl,
      mul_zero, mul_zero, mul_zero, zero_add, zero_add, zero_add]
  | n + 4, h => exact absurd (Nat.lt_of_lt_of_le h (Nat.le_add_left 4 n)) (Nat.lt_irrefl _)

/-! The basis entries the nonvanishing reads. -/

theorem idm_ne {k j : Nat} (h : k ≠ j) : (idm k j : Shell p) = 0 := ite_eq_right h
theorem idm_self (k : Nat) : (idm k k : Shell p) = 1 := ite_eq_left rfl

theorem Fmat_zero_row (g : Shell p) (κ j : Nat) : Fmat g κ 0 j = quarterTurn g κ := by
  show quarterTurn g κ * g ^ (j * 0) = _
  rw [Nat.mul_zero, pow_zero, mul_one]

theorem FJ_zero_row (g : Shell p) (κ j : Nat) : FJ g κ 0 j = quarterTurn g κ := by
  show quarterTurn g κ * g ^ (rev (p - 1) j * 0) = _
  rw [Nat.mul_zero, pow_zero, mul_one]

theorem J_zero_zero : (J (p - 1) 0 0 : Shell p) = 1 := ite_eq_left (FRC.Nat.zero_mod _)

theorem J_zero_row {j : Nat} (hj0 : 0 < j) (hj : j < p - 1) : (J (p - 1) 0 j : Shell p) = 0 :=
  ite_eq_right (fun e => by
    rw [Nat.zero_add, FRC.Nat.mod_eq_of_lt hj] at e
    exact Nat.lt_irrefl 0 (e ▸ hj0))

theorem three_lt_n (F : Frame p κ g) : 2 + 1 < p - 1 := by
  rw [F.n_eq]; exact Nat.lt_of_lt_of_le (by decide) (Nat.mul_le_mul_left 4 F.cap_pos)

theorem J_two_one (F : Frame p κ g) : (J (p - 1) 2 1 : Shell p) = 0 :=
  ite_eq_right (fun e => by rw [FRC.Nat.mod_eq_of_lt (three_lt_n F)] at e; exact absurd e (by decide))

theorem hii (F : Frame p κ g) : quarterTurn g κ * quarterTurn g κ + 1 = 0 := by
  rw [F.quarter_turn_sq, neg_add]

theorem q_ne_zero (F : Frame p κ g) : -(ofNat κ) ≠ (0 : Shell p) := fun h =>
  F.one_ne_zero (by
    have e := hq F
    rw [h, mul_zero, zero_add] at e
    rw [← neg_neg (1 : Shell p), e, neg_zero])

theorem half_ne_zero (F : Frame p κ g) : -(ofNat κ) + -(ofNat κ) ≠ (0 : Shell p) := fun h =>
  F.one_ne_zero (by rw [← half F, h, mul_zero])

theorem quarter_ne_zero (F : Frame p κ g) : quarterTurn g κ ≠ 0 := fun h =>
  F.one_ne_zero (by rw [← neg_neg (1 : Shell p), ← F.quarter_turn_sq, h, mul_zero, neg_zero])

theorem one_add_quarter_ne_zero (F : Frame p κ g) : 1 + quarterTurn g κ ≠ 0 := fun h =>
  F.neg_one_ne_one (by rw [← F.quarter_turn_sq, ← neg_eq_of_add_eq_zero h, neg_mul_neg, one_mul])

theorem one_sub_quarter_ne_zero (F : Frame p κ g) : 1 + -(quarterTurn g κ) ≠ 0 := fun h => by
  have hi : quarterTurn g κ = 1 := by rw [← neg_neg (quarterTurn g κ), ← neg_eq_of_add_eq_zero h, neg_neg]
  exact F.neg_one_ne_one (by rw [← F.quarter_turn_sq, hi, one_mul])

/-- 6:C5, the entry `(0, 0)` of the even projectors: `(Π₀)₀₀ = (q + q)(1 + i)` and `(Π₂)₀₀ = (q + q)(1 − i)`. -/
theorem even_proj_entry (F : Frame p κ g) :
    proj g κ 0 0 0 = (-(ofNat κ) + -(ofNat κ)) * (1 + quarterTurn g κ) ∧
      proj g κ 2 0 0 = (-(ofNat κ) + -(ofNat κ)) * (1 + -(quarterTurn g κ)) := by
  rw [proj_zero_eq, proj_two_eq F]
  show -(ofNat κ) * idm 0 0 + -(ofNat κ) * Fmat g κ 0 0 + -(ofNat κ) * J (p - 1) 0 0 + -(ofNat κ) * FJ g κ 0 0 = _ ∧
    -(ofNat κ) * idm 0 0 + -(-(ofNat κ)) * Fmat g κ 0 0 + -(ofNat κ) * J (p - 1) 0 0 + -(-(ofNat κ)) * FJ g κ 0 0 = _
  rw [idm_self, Fmat_zero_row, FJ_zero_row, J_zero_zero]
  exact ⟨entry00_zero _ _, entry00_two _ _⟩

/-- 6:C5, the even projectors never vanish: `(Π₀)₀₀ ≠ 0` and `(Π₂)₀₀ ≠ 0` on every frame, since `q + q = 2⁻¹` and
`1 ± i` are nonzero. -/
theorem even_proj_ne_zero (F : Frame p κ g) : proj g κ 0 0 0 ≠ 0 ∧ proj g κ 2 0 0 ≠ 0 := by
  rw [(even_proj_entry F).1, (even_proj_entry F).2]
  exact ⟨F.mul_ne_zero (half_ne_zero F) (one_add_quarter_ne_zero F),
    F.mul_ne_zero (half_ne_zero F) (one_sub_quarter_ne_zero F)⟩

/-- 6:C5, the odd projectors at the entry `(2, 1)`: `(Π₁)₂₁ = q (g² − g^{−2})` and `(Π₃)₂₁ = −q (g² − g^{−2})`,
with `g^{−2}` read as `g^{2 (n−1)}`. -/
theorem odd_proj_entry (F : Frame p κ g) :
    proj g κ 1 2 1 = -(ofNat κ) * (g ^ (1 * 2) + -(g ^ (rev (p - 1) 1 * 2))) ∧
      proj g κ 3 2 1 = -(-(ofNat κ) * (g ^ (1 * 2) + -(g ^ (rev (p - 1) 1 * 2)))) := by
  rw [proj_one_eq F, proj_three_eq F]
  show -(ofNat κ) * idm 2 1 + -(ofNat κ) * -(quarterTurn g κ) * Fmat g κ 2 1 + -(-(ofNat κ)) * J (p - 1) 2 1 +
      -(-(ofNat κ) * -(quarterTurn g κ)) * FJ g κ 2 1 = _ ∧
    -(ofNat κ) * idm 2 1 + -(-(ofNat κ) * -(quarterTurn g κ)) * Fmat g κ 2 1 + -(-(ofNat κ)) * J (p - 1) 2 1 +
      -(ofNat κ) * -(quarterTurn g κ) * FJ g κ 2 1 = _
  rw [idm_ne (by decide), J_two_one F]
  exact ⟨red1 (entry21_one _ _ _ _) (hii F), red1 (entry21_three _ _ _ _) (hii F)⟩

theorem four_lt_n (F : Frame p κ g) (hκ : 2 ≤ κ) : 4 < p - 1 := by
  rw [F.n_eq]; exact Nat.lt_of_lt_of_le (by decide) (Nat.mul_le_mul_left 4 hκ)

/-- `g² ≠ g^{−2}` for `κ ≥ 2`: otherwise `g⁴ = 1` below the order `4κ`. -/
theorem sq_ne_inv_sq (F : Frame p κ g) (hκ : 2 ≤ κ) : g ^ (1 * 2) + -(g ^ (rev (p - 1) 1 * 2)) ≠ 0 := fun h => by
  have hn := F.n_pos
  have h1 : 1 < p - 1 := Nat.lt_trans (by decide) (four_lt_n F hκ)
  have e : g ^ (1 * 2) = g ^ (rev (p - 1) 1 * 2) := by rw [eq_neg_of_add_eq_zero h, neg_neg]
  have e1 : g ^ (rev (p - 1) 1 * 2) * g ^ (1 * 2) = 1 := by
    rw [← pow_add, ← FRC.Nat.add_mul]
    exact F.pow_eq_one_of_mod (by rw [FRC.Nat.mul_mod_left' _ _ _ hn, rev_add_mod h1, Nat.zero_mul]; rfl)
  rw [← e, ← pow_add] at e1
  exact F.prim.2 4 (four_lt_n F hκ) (by decide) e1

/-- 6:C5, the odd projectors do not vanish for `κ ≥ 2`: the entry `(2, 1)` of each is `±q (g² − g^{−2}) ≠ 0`. -/
theorem odd_proj_ne_zero (F : Frame p κ g) (hκ : 2 ≤ κ) : proj g κ 1 2 1 ≠ 0 ∧ proj g κ 3 2 1 ≠ 0 := by
  rw [(odd_proj_entry F).1, (odd_proj_entry F).2]
  have h := F.mul_ne_zero (q_ne_zero F) (sq_ne_inv_sq F hκ)
  exact ⟨h, fun e => h (by rw [← neg_neg (-(ofNat κ) * _), e, neg_zero])⟩

/-- 6:C4, 6:D2, faithfulness: `F^{[s]} = F^{[r]}` entrywise forces `s = r` below the period, for `κ ≥ 2`. The entry
`(2, 1)` of `F^{[s]} Π₁ = z^s Π₁` reads `z^s (Π₁)₂₁` with `(Π₁)₂₁ ≠ 0`, so `z^s = z^r` and `z` has order `4κ`. -/
theorem frft_injective (F : Frame p κ g) (hκ : 2 ≤ κ) {z : Shell p} (hz : g * z = 1) {s r : Nat} (hs : s < p - 1)
    (hr : r < p - 1) (h : ∀ k j, k < p - 1 → j < p - 1 → frft g κ z s k j = frft g κ z r k j) : s = r := by
  have h2 : 2 < p - 1 := Nat.lt_trans (by decide) (four_lt_n F hκ)
  have h1 : 1 < p - 1 := Nat.lt_trans (by decide) h2
  have es := frft_proj F z s (by decide : (1 : Nat) < 4) h2 h1
  have er := frft_proj F z r (by decide : (1 : Nat) < 4) h2 h1
  have hsum : sumRange (fun l => frft g κ z s 2 l * proj g κ 1 l 1) (p - 1) =
      sumRange (fun l => frft g κ z r 2 l * proj g κ 1 l 1) (p - 1) :=
    sum_congr _ (fun l hl => by rw [h 2 l h2 hl])
  rw [es, er, pow_one, pow_one] at hsum
  have hz' : z ^ s = z ^ r :=
    (inv_frame F hz).mul_left_cancel (odd_proj_ne_zero F hκ).1
      ((mul_comm _ _).trans (hsum.trans (mul_comm _ _)))
  exact (inv_frame F hz).pow_inj hs hr hz'

/-! The shell `p = 5` (`κ = 1`), its two frames `g = 2, 3`, decided by the kernel. -/

theorem frame5_two : Frame 5 1 (2 : Shell 5) := ⟨rfl, Nat.zero_lt_succ 0, by decide⟩
theorem frame5_three : Frame 5 1 (3 : Shell 5) := ⟨rfl, Nat.zero_lt_succ 0, by decide⟩

/-- 6:C5, 6:C4, at `p = 5` exactly one odd projector vanishes: `Π₁ = 0 ≠ Π₃` at `g = 2`, `Π₃ = 0 ≠ Π₁` at `g = 3`;
the surviving odd projector carries the faithful character `s ↦ z^{ms}`, `m` its index. -/
theorem five_odd_proj :
    (∀ k, k < 4 → ∀ j, j < 4 → proj (2 : Shell 5) 1 1 k j = 0) ∧ proj (2 : Shell 5) 1 3 1 1 ≠ 0 ∧
    (∀ k, k < 4 → ∀ j, j < 4 → proj (3 : Shell 5) 1 3 k j = 0) ∧ proj (3 : Shell 5) 1 1 1 1 ≠ 0 ∧
    (∀ s, s < 4 → ∀ r, r < 4 → (3 : Shell 5) ^ (3 * s) = 3 ^ (3 * r) → s = r) ∧
    (∀ s, s < 4 → ∀ r, r < 4 → (2 : Shell 5) ^ (1 * s) = 2 ^ (1 * r) → s = r) := by decide +kernel

/-- 6:C4, faithfulness at `p = 5` on both frames (`z = g⁻¹`: `3` for `g = 2`, `2` for `g = 3`). -/
theorem five_faithful :
    (∀ s, s < 4 → ∀ r, r < 4 → (∀ k, k < 4 → ∀ j, j < 4 → frft (2 : Shell 5) 1 3 s k j = frft (2 : Shell 5) 1 3 r k j) →
      s = r) ∧
    (∀ s, s < 4 → ∀ r, r < 4 → (∀ k, k < 4 → ∀ j, j < 4 → frft (3 : Shell 5) 1 2 s k j = frft (3 : Shell 5) 1 2 r k j) →
      s = r) := by decide +kernel

/-! The domains (6:D1, 6:D2, 6:D7). -/

/-- 6:D1, every `F^{[s]}` is invertible: `F^{[s]} F^{[n−s]} = I = F^{[n−s]} F^{[s]}` for `s ≤ n = p − 1`. -/
theorem frft_inverse (F : Frame p κ g) {z : Shell p} (hz : g * z = 1) {s : Nat} (hs : s ≤ p - 1) {k j : Nat}
    (hk : k < p - 1) (hj : j < p - 1) :
    sumRange (fun l => frft g κ z s k l * frft g κ z (p - 1 - s) l j) (p - 1) = idm k j ∧
      sumRange (fun l => frft g κ z (p - 1 - s) k l * frft g κ z s l j) (p - 1) = idm k j := by
  have hn : frft g κ z (p - 1) k j = idm k j := by
    have e := frft_period F hz 0 k j
    rw [Nat.zero_add] at e
    rw [e]; exact (frft_cardinal F hz k j).1
  constructor
  · rw [← frft_add F z s (p - 1 - s) hk hj, FRC.Nat.add_sub_of_le hs]; exact hn
  · rw [← frft_add F z (p - 1 - s) s hk hj, FRC.Nat.sub_add_cancel hs]; exact hn

/-- 6:D2, the half-turn is the reversal: `F^{[s + 2κ]} = F^{[s]} J`, entrywise `F^{[s+2κ]}_{kj} = F^{[s]}_{k, rev j}`,
so the framed bases `B_{s+2κ}` and `B_s` agree as unordered bases. -/
theorem frft_half_turn (F : Frame p κ g) {z : Shell p} (hz : g * z = 1) (s : Nat) {k j : Nat} (hk : k < p - 1)
    (hj : j < p - 1) : frft g κ z (s + 2 * κ) k j = frft g κ z s k (rev (p - 1) j) := by
  rw [frft_add F z s (2 * κ) hk hj, sum_congr _ (fun l _ => by rw [(frft_cardinal F hz l j).2.2.1])]
  exact mm_X_J (frft g κ z s) hj

/-- 6:D7, the row-0 entries of `F^{[t]}` off the site `j = 0`: `F^{[t]}_{0j} = (q + q)(1 − z^{2t}) i = (i/2)(1 − g^{−2t})`,
the same value at every `0 < j < n`. -/
theorem frft_row_zero (F : Frame p κ g) (z : Shell p) (t : Nat) {j : Nat} (hj0 : 0 < j) (hj : j < p - 1) :
    frft g κ z t 0 j = (-(ofNat κ) + -(ofNat κ)) * (1 + -(z ^ t * z ^ t)) * quarterTurn g κ := by
  rw [frft_eq F z t 0 j]
  show NF0 (-(ofNat κ)) (-(quarterTurn g κ)) (z ^ t) * idm 0 j + NF1 (-(ofNat κ)) (-(quarterTurn g κ)) (z ^ t) * Fmat g κ 0 j +
    NF2 (-(ofNat κ)) (-(quarterTurn g κ)) (z ^ t) * J (p - 1) 0 j + NF3 (-(ofNat κ)) (-(quarterTurn g κ)) (z ^ t) * FJ g κ 0 j = _
  rw [idm_ne (fun (e : 0 = j) => Nat.lt_irrefl j (e ▸ hj0)), J_zero_row hj0 hj, Fmat_zero_row, FJ_zero_row]
  exact row_zero_id _ _ _ _

/-- `t + t ≡ 0 (mod n)` below `n = 2κ + 2κ` forces `t = 0` or `t = 2κ`. -/
theorem double_mod_n (F : Frame p κ g) {t : Nat} (ht : t < p - 1) (h : (t + t) % (p - 1) = 0) : t = 0 ∨ t = 2 * κ := by
  have hn := F.n_pos
  obtain ⟨c, hc⟩ := FRC.Nat.mod_spec (p - 1) hn (t + t)
  rw [h, Nat.add_zero] at hc
  match c, hc with
  | 0, hc => exact Or.inl (match t, hc with | 0, _ => rfl | t + 1, hc => Nat.noConfusion hc)
  | 1, hc =>
    rw [Nat.mul_one, ← F.four_kappa, ← Nat.two_mul, ← Nat.two_mul] at hc
    exact Or.inr (Nat.eq_of_mul_eq_mul_left (by decide) hc)
  | c + 2, hc =>
    have : t + t < (p - 1) * (c + 2) :=
      Nat.lt_of_lt_of_le (Nat.add_lt_add ht ht) (by rw [Nat.mul_add, Nat.mul_two]; exact Nat.le_add_left _ _)
    exact absurd hc (Nat.ne_of_lt this)

/-- 6:D7, the row-0 entries are nonzero for `t ∉ {0, 2κ}`, so `F^{[t]}` is not monomial and `B_{s+t} ≠ B_s`: exactly
`2κ` measurement bases on the cycle. -/
theorem frft_row_zero_ne_zero (F : Frame p κ g) {z : Shell p} (hz : g * z = 1) {t : Nat} (ht : t < p - 1) (h0 : t ≠ 0)
    (h2 : t ≠ 2 * κ) {j : Nat} (hj0 : 0 < j) (hj : j < p - 1) : frft g κ z t 0 j ≠ 0 := by
  rw [frft_row_zero F z t hj0 hj]
  refine F.mul_ne_zero (F.mul_ne_zero (half_ne_zero F) ?_) (quarter_ne_zero F)
  intro e
  have e1 : z ^ (t + t) = 1 := by rw [pow_add, ← neg_neg (z ^ t * z ^ t), ← neg_eq_of_add_eq_zero e, neg_neg]
  match double_mod_n F ht ((inv_frame F hz).mod_eq_zero_of_pow_eq_one e1) with
  | Or.inl e0 => exact h0 e0
  | Or.inr e2 => exact h2 e2

end Frame
end Shell
end FRC
