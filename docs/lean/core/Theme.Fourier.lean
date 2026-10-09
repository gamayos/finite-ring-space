import FrcCore.Ring
import FrcCore.Meridian
import FrcCore.Transform

/-!
# FrcCore.Theme.Fourier — the fractional family on the cycle, and the conjugate frame (the fourier theme)

The shell transform `F = i W` (`W k j = g^{jk}`, `i = −g^κ`, `Transform.lean`) has `F² = J` and `F⁴ = I` on the cycle of
`n = p − 1 = 4κ` indices. Its spectral projectors `Π_ℓ = 4⁻¹ Σ_m i^{−ℓm} F^m` (`4⁻¹ = −κ`) give the fractional family
`F^{[s]} = Σ_{ℓ<4} z^{ℓs} Π_ℓ`, `z = g⁻¹` the refinement base (6:C3). Every such combination is `c₀ I + c₁ F + c₂ J +
c₃ F J`, and the product of two is the cyclic convolution of their coefficients (`comb_mul`), so the family is a
representation of the cycle, `F^{[s+r]} = F^{[s]} F^{[r]}`, `(n)`-periodic, with the cardinal values `F^{[0]} = I`,
`F^{[κ]} = F`, `F^{[2κ]} = J`, `F^{[3κ]} = F J = F⁻¹` (`frft_add`, `frft_cardinal`). With the meridian covariance of
`Meridian.lean` this is the master's C2 (`scale_shift`). The conjugate frame `g⁻¹` has the transform `−F J` and the
projectors `Π_{ℓ+2}` (6:C9), and the Carrier's quarter-turn `ħ` has `ħ^S = ±1` when `S` is even: the master's C7
(`orientation`). Task LM25 of the ledger migration. No axioms.
-/

namespace FRC
namespace Shell
namespace Frame

variable {p : Nat} [Pos p]

/-! ## Ring identities for the coefficients (generated; `RE.sound`, decided by the kernel) -/

theorem red1 {L T a X : Shell p} (h : L = T + a * X) (ha : a = 0) : L = T := by
  rw [h, ha, zero_mul, add_zero]

theorem red2 {L T a b X Y : Shell p} (h : L = T + a * X + b * Y) (ha : a = 0) (hb : b = 0) : L = T := by
  rw [h, ha, hb, zero_mul, zero_mul, add_zero, add_zero]

theorem frft_aux (q jj u I F J G : Shell p) :
    1 * (q * I + (q * 1) * F + (q * 1) * J + (q * 1) * G) + (1 * u) * (q * I + (q * (1 * jj)) * F + (q * ((1 * jj) * jj)) * J + (q * (((1 * jj) * jj) * jj)) * G) + ((1 * u) * u) * (q * I + (q * ((1 * jj) * jj)) * F + (q * ((((1 * jj) * jj) * jj) * jj)) * J + (q * ((((((1 * jj) * jj) * jj) * jj) * jj) * jj)) * G) + (((1 * u) * u) * u) * (q * I + (q * (((1 * jj) * jj) * jj)) * F + (q * ((((((1 * jj) * jj) * jj) * jj) * jj) * jj)) * J + (q * (((((((((1 * jj) * jj) * jj) * jj) * jj) * jj) * jj) * jj) * jj)) * G) =
      (q * (1 + u + u * u + u * u * u)) * I + (q * (1 + jj * u + -(u * u) + -(jj * (u * u * u)))) * F + (q * (1 + -u + u * u + -(u * u * u))) * J + (q * (1 + -(jj * u) + -(u * u) + jj * (u * u * u))) * G + (jj * jj + 1) * (q * jj * jj * jj * jj * jj * jj * jj * u * u * u * G + -(q * jj * jj * jj * jj * jj * u * u * u * G) + q * jj * jj * jj * jj * u * u * u * J + q * jj * jj * jj * jj * u * u * G + q * jj * jj * jj * u * u * u * G + -(q * jj * jj * u * u * u * J) + q * jj * jj * u * u * J + -(q * jj * jj * u * u * G) + q * jj * u * u * u * F + -(q * jj * u * u * u * G) + q * jj * u * G + q * u * u * u * J + q * u * u * F + -(q * u * u * J) + q * u * u * G + q * u * J) :=
  Shell.Frame.RE.sound (Shell.Frame.look [q, jj, u, I, F, J, G])
    (.add (.add (.add (.mul .one (.add (.add (.add (.mul (.var 0) (.var 3)) (.mul (.mul (.var 0) .one) (.var 4))) (.mul (.mul (.var 0) .one) (.var 5))) (.mul (.mul (.var 0) .one) (.var 6)))) (.mul (.mul .one (.var 2)) (.add (.add (.add (.mul (.var 0) (.var 3)) (.mul (.mul (.var 0) (.mul .one (.var 1))) (.var 4))) (.mul (.mul (.var 0) (.mul (.mul .one (.var 1)) (.var 1))) (.var 5))) (.mul (.mul (.var 0) (.mul (.mul (.mul .one (.var 1)) (.var 1)) (.var 1))) (.var 6))))) (.mul (.mul (.mul .one (.var 2)) (.var 2)) (.add (.add (.add (.mul (.var 0) (.var 3)) (.mul (.mul (.var 0) (.mul (.mul .one (.var 1)) (.var 1))) (.var 4))) (.mul (.mul (.var 0) (.mul (.mul (.mul (.mul .one (.var 1)) (.var 1)) (.var 1)) (.var 1))) (.var 5))) (.mul (.mul (.var 0) (.mul (.mul (.mul (.mul (.mul (.mul .one (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1))) (.var 6))))) (.mul (.mul (.mul (.mul .one (.var 2)) (.var 2)) (.var 2)) (.add (.add (.add (.mul (.var 0) (.var 3)) (.mul (.mul (.var 0) (.mul (.mul (.mul .one (.var 1)) (.var 1)) (.var 1))) (.var 4))) (.mul (.mul (.var 0) (.mul (.mul (.mul (.mul (.mul (.mul .one (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1))) (.var 5))) (.mul (.mul (.var 0) (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul .one (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1))) (.var 6)))))
    (.add (.add (.add (.add (.mul (.mul (.var 0) (.add (.add (.add .one (.var 2)) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 2) (.var 2)) (.var 2)))) (.var 3)) (.mul (.mul (.var 0) (.add (.add (.add .one (.mul (.var 1) (.var 2))) (.neg (.mul (.var 2) (.var 2)))) (.neg (.mul (.var 1) (.mul (.mul (.var 2) (.var 2)) (.var 2)))))) (.var 4))) (.mul (.mul (.var 0) (.add (.add (.add .one (.neg (.var 2))) (.mul (.var 2) (.var 2))) (.neg (.mul (.mul (.var 2) (.var 2)) (.var 2))))) (.var 5))) (.mul (.mul (.var 0) (.add (.add (.add .one (.neg (.mul (.var 1) (.var 2)))) (.neg (.mul (.var 2) (.var 2)))) (.mul (.var 1) (.mul (.mul (.var 2) (.var 2)) (.var 2))))) (.var 6))) (.mul (.add (.mul (.var 1) (.var 1)) .one) (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 2)) (.var 2)) (.var 2)) (.var 6)) (.neg (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 2)) (.var 2)) (.var 2)) (.var 6)))) (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 2)) (.var 2)) (.var 2)) (.var 5))) (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.var 1)) (.var 1)) (.var 2)) (.var 2)) (.var 6))) (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.var 1)) (.var 2)) (.var 2)) (.var 2)) (.var 6))) (.neg (.mul (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.var 2)) (.var 2)) (.var 2)) (.var 5)))) (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.var 2)) (.var 2)) (.var 5))) (.neg (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.var 2)) (.var 2)) (.var 6)))) (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 2)) (.var 2)) (.var 4))) (.neg (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 2)) (.var 2)) (.var 6)))) (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 6))) (.mul (.mul (.mul (.mul (.var 0) (.var 2)) (.var 2)) (.var 2)) (.var 5))) (.mul (.mul (.mul (.var 0) (.var 2)) (.var 2)) (.var 4))) (.neg (.mul (.mul (.mul (.var 0) (.var 2)) (.var 2)) (.var 5)))) (.mul (.mul (.mul (.var 0) (.var 2)) (.var 2)) (.var 6))) (.mul (.mul (.var 0) (.var 2)) (.var 5))))) (by decide +kernel)

theorem conv0_aux (q jj u v : Shell p) :
    (q * (1 + u + u * u + u * u * u)) * (q * (1 + v + v * v + v * v * v)) + (q * (1 + jj * u + -(u * u) + -(jj * (u * u * u)))) * (q * (1 + -(jj * v) + -(v * v) + jj * (v * v * v))) + (q * (1 + -u + u * u + -(u * u * u))) * (q * (1 + -v + v * v + -(v * v * v))) + (q * (1 + -(jj * u) + -(u * u) + jj * (u * u * u))) * (q * (1 + jj * v + -(v * v) + -(jj * (v * v * v)))) =
      q * (1 + (u * v) + (u * v) * (u * v) + (u * v) * (u * v) * (u * v)) + (jj * jj + 1) * (-((1 + 1) * q * q * u * u * u * v * v * v) + (1 + 1) * q * q * u * u * u * v + (1 + 1) * q * q * u * v * v * v + -((1 + 1) * q * q * u * v)) + ((1 + 1 + 1 + 1) * q + -1) * (q * u * u * u * v * v * v + q * u * u * v * v + q * u * v + q) :=
  Shell.Frame.RE.sound (Shell.Frame.look [q, jj, u, v])
    (.add (.add (.add (.mul (.mul (.var 0) (.add (.add (.add .one (.var 2)) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 2) (.var 2)) (.var 2)))) (.mul (.var 0) (.add (.add (.add .one (.var 3)) (.mul (.var 3) (.var 3))) (.mul (.mul (.var 3) (.var 3)) (.var 3))))) (.mul (.mul (.var 0) (.add (.add (.add .one (.mul (.var 1) (.var 2))) (.neg (.mul (.var 2) (.var 2)))) (.neg (.mul (.var 1) (.mul (.mul (.var 2) (.var 2)) (.var 2)))))) (.mul (.var 0) (.add (.add (.add .one (.neg (.mul (.var 1) (.var 3)))) (.neg (.mul (.var 3) (.var 3)))) (.mul (.var 1) (.mul (.mul (.var 3) (.var 3)) (.var 3))))))) (.mul (.mul (.var 0) (.add (.add (.add .one (.neg (.var 2))) (.mul (.var 2) (.var 2))) (.neg (.mul (.mul (.var 2) (.var 2)) (.var 2))))) (.mul (.var 0) (.add (.add (.add .one (.neg (.var 3))) (.mul (.var 3) (.var 3))) (.neg (.mul (.mul (.var 3) (.var 3)) (.var 3))))))) (.mul (.mul (.var 0) (.add (.add (.add .one (.neg (.mul (.var 1) (.var 2)))) (.neg (.mul (.var 2) (.var 2)))) (.mul (.var 1) (.mul (.mul (.var 2) (.var 2)) (.var 2))))) (.mul (.var 0) (.add (.add (.add .one (.mul (.var 1) (.var 3))) (.neg (.mul (.var 3) (.var 3)))) (.neg (.mul (.var 1) (.mul (.mul (.var 3) (.var 3)) (.var 3))))))))
    (.add (.add (.mul (.var 0) (.add (.add (.add .one (.mul (.var 2) (.var 3))) (.mul (.mul (.var 2) (.var 3)) (.mul (.var 2) (.var 3)))) (.mul (.mul (.mul (.var 2) (.var 3)) (.mul (.var 2) (.var 3))) (.mul (.var 2) (.var 3))))) (.mul (.add (.mul (.var 1) (.var 1)) .one) (.add (.add (.add (.neg (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.add .one .one) (.var 0)) (.var 0)) (.var 2)) (.var 2)) (.var 2)) (.var 3)) (.var 3)) (.var 3))) (.mul (.mul (.mul (.mul (.mul (.mul (.add .one .one) (.var 0)) (.var 0)) (.var 2)) (.var 2)) (.var 2)) (.var 3))) (.mul (.mul (.mul (.mul (.mul (.mul (.add .one .one) (.var 0)) (.var 0)) (.var 2)) (.var 3)) (.var 3)) (.var 3))) (.neg (.mul (.mul (.mul (.mul (.add .one .one) (.var 0)) (.var 0)) (.var 2)) (.var 3)))))) (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.neg .one)) (.add (.add (.add (.mul (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 2)) (.var 2)) (.var 2)) (.var 3)) (.var 3)) (.var 3)) (.mul (.mul (.mul (.mul (.var 0) (.var 2)) (.var 2)) (.var 3)) (.var 3))) (.mul (.mul (.var 0) (.var 2)) (.var 3))) (.var 0)))) (by decide +kernel)

theorem conv1_aux (q jj u v : Shell p) :
    (q * (1 + u + u * u + u * u * u)) * (q * (1 + jj * v + -(v * v) + -(jj * (v * v * v)))) + (q * (1 + jj * u + -(u * u) + -(jj * (u * u * u)))) * (q * (1 + v + v * v + v * v * v)) + (q * (1 + -u + u * u + -(u * u * u))) * (q * (1 + -(jj * v) + -(v * v) + jj * (v * v * v))) + (q * (1 + -(jj * u) + -(u * u) + jj * (u * u * u))) * (q * (1 + -v + v * v + -(v * v * v))) =
      q * (1 + jj * (u * v) + -((u * v) * (u * v)) + -(jj * ((u * v) * (u * v) * (u * v)))) + (jj * jj + 1) * (0) + ((1 + 1 + 1 + 1) * q + -1) * (-(q * jj * u * u * u * v * v * v) + q * jj * u * v + -(q * u * u * v * v) + q) :=
  Shell.Frame.RE.sound (Shell.Frame.look [q, jj, u, v])
    (.add (.add (.add (.mul (.mul (.var 0) (.add (.add (.add .one (.var 2)) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 2) (.var 2)) (.var 2)))) (.mul (.var 0) (.add (.add (.add .one (.mul (.var 1) (.var 3))) (.neg (.mul (.var 3) (.var 3)))) (.neg (.mul (.var 1) (.mul (.mul (.var 3) (.var 3)) (.var 3))))))) (.mul (.mul (.var 0) (.add (.add (.add .one (.mul (.var 1) (.var 2))) (.neg (.mul (.var 2) (.var 2)))) (.neg (.mul (.var 1) (.mul (.mul (.var 2) (.var 2)) (.var 2)))))) (.mul (.var 0) (.add (.add (.add .one (.var 3)) (.mul (.var 3) (.var 3))) (.mul (.mul (.var 3) (.var 3)) (.var 3)))))) (.mul (.mul (.var 0) (.add (.add (.add .one (.neg (.var 2))) (.mul (.var 2) (.var 2))) (.neg (.mul (.mul (.var 2) (.var 2)) (.var 2))))) (.mul (.var 0) (.add (.add (.add .one (.neg (.mul (.var 1) (.var 3)))) (.neg (.mul (.var 3) (.var 3)))) (.mul (.var 1) (.mul (.mul (.var 3) (.var 3)) (.var 3))))))) (.mul (.mul (.var 0) (.add (.add (.add .one (.neg (.mul (.var 1) (.var 2)))) (.neg (.mul (.var 2) (.var 2)))) (.mul (.var 1) (.mul (.mul (.var 2) (.var 2)) (.var 2))))) (.mul (.var 0) (.add (.add (.add .one (.neg (.var 3))) (.mul (.var 3) (.var 3))) (.neg (.mul (.mul (.var 3) (.var 3)) (.var 3)))))))
    (.add (.add (.mul (.var 0) (.add (.add (.add .one (.mul (.var 1) (.mul (.var 2) (.var 3)))) (.neg (.mul (.mul (.var 2) (.var 3)) (.mul (.var 2) (.var 3))))) (.neg (.mul (.var 1) (.mul (.mul (.mul (.var 2) (.var 3)) (.mul (.var 2) (.var 3))) (.mul (.var 2) (.var 3))))))) (.mul (.add (.mul (.var 1) (.var 1)) .one) .zero)) (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.neg .one)) (.add (.add (.add (.neg (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 2)) (.var 2)) (.var 3)) (.var 3)) (.var 3))) (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 3))) (.neg (.mul (.mul (.mul (.mul (.var 0) (.var 2)) (.var 2)) (.var 3)) (.var 3)))) (.var 0)))) (by decide +kernel)

theorem conv2_aux (q jj u v : Shell p) :
    (q * (1 + u + u * u + u * u * u)) * (q * (1 + -v + v * v + -(v * v * v))) + (q * (1 + jj * u + -(u * u) + -(jj * (u * u * u)))) * (q * (1 + jj * v + -(v * v) + -(jj * (v * v * v)))) + (q * (1 + -u + u * u + -(u * u * u))) * (q * (1 + v + v * v + v * v * v)) + (q * (1 + -(jj * u) + -(u * u) + jj * (u * u * u))) * (q * (1 + -(jj * v) + -(v * v) + jj * (v * v * v))) =
      q * (1 + -(u * v) + (u * v) * (u * v) + -((u * v) * (u * v) * (u * v))) + (jj * jj + 1) * ((1 + 1) * q * q * u * u * u * v * v * v + -((1 + 1) * q * q * u * u * u * v) + -((1 + 1) * q * q * u * v * v * v) + (1 + 1) * q * q * u * v) + ((1 + 1 + 1 + 1) * q + -1) * (-(q * u * u * u * v * v * v) + q * u * u * v * v + -(q * u * v) + q) :=
  Shell.Frame.RE.sound (Shell.Frame.look [q, jj, u, v])
    (.add (.add (.add (.mul (.mul (.var 0) (.add (.add (.add .one (.var 2)) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 2) (.var 2)) (.var 2)))) (.mul (.var 0) (.add (.add (.add .one (.neg (.var 3))) (.mul (.var 3) (.var 3))) (.neg (.mul (.mul (.var 3) (.var 3)) (.var 3)))))) (.mul (.mul (.var 0) (.add (.add (.add .one (.mul (.var 1) (.var 2))) (.neg (.mul (.var 2) (.var 2)))) (.neg (.mul (.var 1) (.mul (.mul (.var 2) (.var 2)) (.var 2)))))) (.mul (.var 0) (.add (.add (.add .one (.mul (.var 1) (.var 3))) (.neg (.mul (.var 3) (.var 3)))) (.neg (.mul (.var 1) (.mul (.mul (.var 3) (.var 3)) (.var 3)))))))) (.mul (.mul (.var 0) (.add (.add (.add .one (.neg (.var 2))) (.mul (.var 2) (.var 2))) (.neg (.mul (.mul (.var 2) (.var 2)) (.var 2))))) (.mul (.var 0) (.add (.add (.add .one (.var 3)) (.mul (.var 3) (.var 3))) (.mul (.mul (.var 3) (.var 3)) (.var 3)))))) (.mul (.mul (.var 0) (.add (.add (.add .one (.neg (.mul (.var 1) (.var 2)))) (.neg (.mul (.var 2) (.var 2)))) (.mul (.var 1) (.mul (.mul (.var 2) (.var 2)) (.var 2))))) (.mul (.var 0) (.add (.add (.add .one (.neg (.mul (.var 1) (.var 3)))) (.neg (.mul (.var 3) (.var 3)))) (.mul (.var 1) (.mul (.mul (.var 3) (.var 3)) (.var 3)))))))
    (.add (.add (.mul (.var 0) (.add (.add (.add .one (.neg (.mul (.var 2) (.var 3)))) (.mul (.mul (.var 2) (.var 3)) (.mul (.var 2) (.var 3)))) (.neg (.mul (.mul (.mul (.var 2) (.var 3)) (.mul (.var 2) (.var 3))) (.mul (.var 2) (.var 3)))))) (.mul (.add (.mul (.var 1) (.var 1)) .one) (.add (.add (.add (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.add .one .one) (.var 0)) (.var 0)) (.var 2)) (.var 2)) (.var 2)) (.var 3)) (.var 3)) (.var 3)) (.neg (.mul (.mul (.mul (.mul (.mul (.mul (.add .one .one) (.var 0)) (.var 0)) (.var 2)) (.var 2)) (.var 2)) (.var 3)))) (.neg (.mul (.mul (.mul (.mul (.mul (.mul (.add .one .one) (.var 0)) (.var 0)) (.var 2)) (.var 3)) (.var 3)) (.var 3)))) (.mul (.mul (.mul (.mul (.add .one .one) (.var 0)) (.var 0)) (.var 2)) (.var 3))))) (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.neg .one)) (.add (.add (.add (.neg (.mul (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 2)) (.var 2)) (.var 2)) (.var 3)) (.var 3)) (.var 3))) (.mul (.mul (.mul (.mul (.var 0) (.var 2)) (.var 2)) (.var 3)) (.var 3))) (.neg (.mul (.mul (.var 0) (.var 2)) (.var 3)))) (.var 0)))) (by decide +kernel)

theorem conv3_aux (q jj u v : Shell p) :
    (q * (1 + u + u * u + u * u * u)) * (q * (1 + -(jj * v) + -(v * v) + jj * (v * v * v))) + (q * (1 + jj * u + -(u * u) + -(jj * (u * u * u)))) * (q * (1 + -v + v * v + -(v * v * v))) + (q * (1 + -u + u * u + -(u * u * u))) * (q * (1 + jj * v + -(v * v) + -(jj * (v * v * v)))) + (q * (1 + -(jj * u) + -(u * u) + jj * (u * u * u))) * (q * (1 + v + v * v + v * v * v)) =
      q * (1 + -(jj * (u * v)) + -((u * v) * (u * v)) + jj * ((u * v) * (u * v) * (u * v))) + (jj * jj + 1) * (0) + ((1 + 1 + 1 + 1) * q + -1) * (q * jj * u * u * u * v * v * v + -(q * jj * u * v) + -(q * u * u * v * v) + q) :=
  Shell.Frame.RE.sound (Shell.Frame.look [q, jj, u, v])
    (.add (.add (.add (.mul (.mul (.var 0) (.add (.add (.add .one (.var 2)) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 2) (.var 2)) (.var 2)))) (.mul (.var 0) (.add (.add (.add .one (.neg (.mul (.var 1) (.var 3)))) (.neg (.mul (.var 3) (.var 3)))) (.mul (.var 1) (.mul (.mul (.var 3) (.var 3)) (.var 3)))))) (.mul (.mul (.var 0) (.add (.add (.add .one (.mul (.var 1) (.var 2))) (.neg (.mul (.var 2) (.var 2)))) (.neg (.mul (.var 1) (.mul (.mul (.var 2) (.var 2)) (.var 2)))))) (.mul (.var 0) (.add (.add (.add .one (.neg (.var 3))) (.mul (.var 3) (.var 3))) (.neg (.mul (.mul (.var 3) (.var 3)) (.var 3))))))) (.mul (.mul (.var 0) (.add (.add (.add .one (.neg (.var 2))) (.mul (.var 2) (.var 2))) (.neg (.mul (.mul (.var 2) (.var 2)) (.var 2))))) (.mul (.var 0) (.add (.add (.add .one (.mul (.var 1) (.var 3))) (.neg (.mul (.var 3) (.var 3)))) (.neg (.mul (.var 1) (.mul (.mul (.var 3) (.var 3)) (.var 3)))))))) (.mul (.mul (.var 0) (.add (.add (.add .one (.neg (.mul (.var 1) (.var 2)))) (.neg (.mul (.var 2) (.var 2)))) (.mul (.var 1) (.mul (.mul (.var 2) (.var 2)) (.var 2))))) (.mul (.var 0) (.add (.add (.add .one (.var 3)) (.mul (.var 3) (.var 3))) (.mul (.mul (.var 3) (.var 3)) (.var 3))))))
    (.add (.add (.mul (.var 0) (.add (.add (.add .one (.neg (.mul (.var 1) (.mul (.var 2) (.var 3))))) (.neg (.mul (.mul (.var 2) (.var 3)) (.mul (.var 2) (.var 3))))) (.mul (.var 1) (.mul (.mul (.mul (.var 2) (.var 3)) (.mul (.var 2) (.var 3))) (.mul (.var 2) (.var 3)))))) (.mul (.add (.mul (.var 1) (.var 1)) .one) .zero)) (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.neg .one)) (.add (.add (.add (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 2)) (.var 2)) (.var 3)) (.var 3)) (.var 3)) (.neg (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 3)))) (.neg (.mul (.mul (.mul (.mul (.var 0) (.var 2)) (.var 2)) (.var 3)) (.var 3)))) (.var 0)))) (by decide +kernel)

theorem card00_aux (q jj : Shell p) :
    q * (1 + (1) + (1) * (1) + (1) * (1) * (1)) =
      1 + (jj * jj + 1) * (0) + ((1 + 1 + 1 + 1) * q + -1) * (1) :=
  Shell.Frame.RE.sound (Shell.Frame.look [q, jj])
    (.mul (.var 0) (.add (.add (.add .one .one) (.mul .one .one)) (.mul (.mul .one .one) .one)))
    (.add (.add .one (.mul (.add (.mul (.var 1) (.var 1)) .one) .zero)) (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.neg .one)) .one)) (by decide +kernel)

theorem card01_aux (q jj : Shell p) :
    q * (1 + jj * (1) + -((1) * (1)) + -(jj * ((1) * (1) * (1)))) =
      0 + (jj * jj + 1) * (0) + ((1 + 1 + 1 + 1) * q + -1) * (0) :=
  Shell.Frame.RE.sound (Shell.Frame.look [q, jj])
    (.mul (.var 0) (.add (.add (.add .one (.mul (.var 1) .one)) (.neg (.mul .one .one))) (.neg (.mul (.var 1) (.mul (.mul .one .one) .one)))))
    (.add (.add .zero (.mul (.add (.mul (.var 1) (.var 1)) .one) .zero)) (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.neg .one)) .zero)) (by decide +kernel)

theorem card02_aux (q jj : Shell p) :
    q * (1 + -(1) + (1) * (1) + -((1) * (1) * (1))) =
      0 + (jj * jj + 1) * (0) + ((1 + 1 + 1 + 1) * q + -1) * (0) :=
  Shell.Frame.RE.sound (Shell.Frame.look [q, jj])
    (.mul (.var 0) (.add (.add (.add .one (.neg .one)) (.mul .one .one)) (.neg (.mul (.mul .one .one) .one))))
    (.add (.add .zero (.mul (.add (.mul (.var 1) (.var 1)) .one) .zero)) (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.neg .one)) .zero)) (by decide +kernel)

theorem card03_aux (q jj : Shell p) :
    q * (1 + -(jj * (1)) + -((1) * (1)) + jj * ((1) * (1) * (1))) =
      0 + (jj * jj + 1) * (0) + ((1 + 1 + 1 + 1) * q + -1) * (0) :=
  Shell.Frame.RE.sound (Shell.Frame.look [q, jj])
    (.mul (.var 0) (.add (.add (.add .one (.neg (.mul (.var 1) .one))) (.neg (.mul .one .one))) (.mul (.var 1) (.mul (.mul .one .one) .one))))
    (.add (.add .zero (.mul (.add (.mul (.var 1) (.var 1)) .one) .zero)) (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.neg .one)) .zero)) (by decide +kernel)

theorem card10_aux (q jj : Shell p) :
    q * (1 + (-jj) + (-jj) * (-jj) + (-jj) * (-jj) * (-jj)) =
      0 + (jj * jj + 1) * (-(q * jj) + q) + ((1 + 1 + 1 + 1) * q + -1) * (0) :=
  Shell.Frame.RE.sound (Shell.Frame.look [q, jj])
    (.mul (.var 0) (.add (.add (.add .one (.neg (.var 1))) (.mul (.neg (.var 1)) (.neg (.var 1)))) (.mul (.mul (.neg (.var 1)) (.neg (.var 1))) (.neg (.var 1)))))
    (.add (.add .zero (.mul (.add (.mul (.var 1) (.var 1)) .one) (.add (.neg (.mul (.var 0) (.var 1))) (.var 0)))) (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.neg .one)) .zero)) (by decide +kernel)

theorem card11_aux (q jj : Shell p) :
    q * (1 + jj * (-jj) + -((-jj) * (-jj)) + -(jj * ((-jj) * (-jj) * (-jj)))) =
      1 + (jj * jj + 1) * (q * jj * jj + -((1 + 1 + 1) * q)) + ((1 + 1 + 1 + 1) * q + -1) * (1) :=
  Shell.Frame.RE.sound (Shell.Frame.look [q, jj])
    (.mul (.var 0) (.add (.add (.add .one (.mul (.var 1) (.neg (.var 1)))) (.neg (.mul (.neg (.var 1)) (.neg (.var 1))))) (.neg (.mul (.var 1) (.mul (.mul (.neg (.var 1)) (.neg (.var 1))) (.neg (.var 1)))))))
    (.add (.add .one (.mul (.add (.mul (.var 1) (.var 1)) .one) (.add (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.neg (.mul (.add (.add .one .one) .one) (.var 0)))))) (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.neg .one)) .one)) (by decide +kernel)

theorem card12_aux (q jj : Shell p) :
    q * (1 + -(-jj) + (-jj) * (-jj) + -((-jj) * (-jj) * (-jj))) =
      0 + (jj * jj + 1) * (q * jj + q) + ((1 + 1 + 1 + 1) * q + -1) * (0) :=
  Shell.Frame.RE.sound (Shell.Frame.look [q, jj])
    (.mul (.var 0) (.add (.add (.add .one (.neg (.neg (.var 1)))) (.mul (.neg (.var 1)) (.neg (.var 1)))) (.neg (.mul (.mul (.neg (.var 1)) (.neg (.var 1))) (.neg (.var 1))))))
    (.add (.add .zero (.mul (.add (.mul (.var 1) (.var 1)) .one) (.add (.mul (.var 0) (.var 1)) (.var 0)))) (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.neg .one)) .zero)) (by decide +kernel)

theorem card13_aux (q jj : Shell p) :
    q * (1 + -(jj * (-jj)) + -((-jj) * (-jj)) + jj * ((-jj) * (-jj) * (-jj))) =
      0 + (jj * jj + 1) * (-(q * jj * jj) + q) + ((1 + 1 + 1 + 1) * q + -1) * (0) :=
  Shell.Frame.RE.sound (Shell.Frame.look [q, jj])
    (.mul (.var 0) (.add (.add (.add .one (.neg (.mul (.var 1) (.neg (.var 1))))) (.neg (.mul (.neg (.var 1)) (.neg (.var 1))))) (.mul (.var 1) (.mul (.mul (.neg (.var 1)) (.neg (.var 1))) (.neg (.var 1))))))
    (.add (.add .zero (.mul (.add (.mul (.var 1) (.var 1)) .one) (.add (.neg (.mul (.mul (.var 0) (.var 1)) (.var 1))) (.var 0)))) (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.neg .one)) .zero)) (by decide +kernel)

theorem card20_aux (q jj : Shell p) :
    q * (1 + (-1) + (-1) * (-1) + (-1) * (-1) * (-1)) =
      0 + (jj * jj + 1) * (0) + ((1 + 1 + 1 + 1) * q + -1) * (0) :=
  Shell.Frame.RE.sound (Shell.Frame.look [q, jj])
    (.mul (.var 0) (.add (.add (.add .one (.neg .one)) (.mul (.neg .one) (.neg .one))) (.mul (.mul (.neg .one) (.neg .one)) (.neg .one))))
    (.add (.add .zero (.mul (.add (.mul (.var 1) (.var 1)) .one) .zero)) (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.neg .one)) .zero)) (by decide +kernel)

theorem card21_aux (q jj : Shell p) :
    q * (1 + jj * (-1) + -((-1) * (-1)) + -(jj * ((-1) * (-1) * (-1)))) =
      0 + (jj * jj + 1) * (0) + ((1 + 1 + 1 + 1) * q + -1) * (0) :=
  Shell.Frame.RE.sound (Shell.Frame.look [q, jj])
    (.mul (.var 0) (.add (.add (.add .one (.mul (.var 1) (.neg .one))) (.neg (.mul (.neg .one) (.neg .one)))) (.neg (.mul (.var 1) (.mul (.mul (.neg .one) (.neg .one)) (.neg .one))))))
    (.add (.add .zero (.mul (.add (.mul (.var 1) (.var 1)) .one) .zero)) (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.neg .one)) .zero)) (by decide +kernel)

theorem card22_aux (q jj : Shell p) :
    q * (1 + -(-1) + (-1) * (-1) + -((-1) * (-1) * (-1))) =
      1 + (jj * jj + 1) * (0) + ((1 + 1 + 1 + 1) * q + -1) * (1) :=
  Shell.Frame.RE.sound (Shell.Frame.look [q, jj])
    (.mul (.var 0) (.add (.add (.add .one (.neg (.neg .one))) (.mul (.neg .one) (.neg .one))) (.neg (.mul (.mul (.neg .one) (.neg .one)) (.neg .one)))))
    (.add (.add .one (.mul (.add (.mul (.var 1) (.var 1)) .one) .zero)) (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.neg .one)) .one)) (by decide +kernel)

theorem card23_aux (q jj : Shell p) :
    q * (1 + -(jj * (-1)) + -((-1) * (-1)) + jj * ((-1) * (-1) * (-1))) =
      0 + (jj * jj + 1) * (0) + ((1 + 1 + 1 + 1) * q + -1) * (0) :=
  Shell.Frame.RE.sound (Shell.Frame.look [q, jj])
    (.mul (.var 0) (.add (.add (.add .one (.neg (.mul (.var 1) (.neg .one)))) (.neg (.mul (.neg .one) (.neg .one)))) (.mul (.var 1) (.mul (.mul (.neg .one) (.neg .one)) (.neg .one)))))
    (.add (.add .zero (.mul (.add (.mul (.var 1) (.var 1)) .one) .zero)) (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.neg .one)) .zero)) (by decide +kernel)

theorem card30_aux (q jj : Shell p) :
    q * (1 + (jj) + (jj) * (jj) + (jj) * (jj) * (jj)) =
      0 + (jj * jj + 1) * (q * jj + q) + ((1 + 1 + 1 + 1) * q + -1) * (0) :=
  Shell.Frame.RE.sound (Shell.Frame.look [q, jj])
    (.mul (.var 0) (.add (.add (.add .one (.var 1)) (.mul (.var 1) (.var 1))) (.mul (.mul (.var 1) (.var 1)) (.var 1))))
    (.add (.add .zero (.mul (.add (.mul (.var 1) (.var 1)) .one) (.add (.mul (.var 0) (.var 1)) (.var 0)))) (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.neg .one)) .zero)) (by decide +kernel)

theorem card31_aux (q jj : Shell p) :
    q * (1 + jj * (jj) + -((jj) * (jj)) + -(jj * ((jj) * (jj) * (jj)))) =
      0 + (jj * jj + 1) * (-(q * jj * jj) + q) + ((1 + 1 + 1 + 1) * q + -1) * (0) :=
  Shell.Frame.RE.sound (Shell.Frame.look [q, jj])
    (.mul (.var 0) (.add (.add (.add .one (.mul (.var 1) (.var 1))) (.neg (.mul (.var 1) (.var 1)))) (.neg (.mul (.var 1) (.mul (.mul (.var 1) (.var 1)) (.var 1))))))
    (.add (.add .zero (.mul (.add (.mul (.var 1) (.var 1)) .one) (.add (.neg (.mul (.mul (.var 0) (.var 1)) (.var 1))) (.var 0)))) (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.neg .one)) .zero)) (by decide +kernel)

theorem card32_aux (q jj : Shell p) :
    q * (1 + -(jj) + (jj) * (jj) + -((jj) * (jj) * (jj))) =
      0 + (jj * jj + 1) * (-(q * jj) + q) + ((1 + 1 + 1 + 1) * q + -1) * (0) :=
  Shell.Frame.RE.sound (Shell.Frame.look [q, jj])
    (.mul (.var 0) (.add (.add (.add .one (.neg (.var 1))) (.mul (.var 1) (.var 1))) (.neg (.mul (.mul (.var 1) (.var 1)) (.var 1)))))
    (.add (.add .zero (.mul (.add (.mul (.var 1) (.var 1)) .one) (.add (.neg (.mul (.var 0) (.var 1))) (.var 0)))) (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.neg .one)) .zero)) (by decide +kernel)

theorem card33_aux (q jj : Shell p) :
    q * (1 + -(jj * (jj)) + -((jj) * (jj)) + jj * ((jj) * (jj) * (jj))) =
      1 + (jj * jj + 1) * (q * jj * jj + -((1 + 1 + 1) * q)) + ((1 + 1 + 1 + 1) * q + -1) * (1) :=
  Shell.Frame.RE.sound (Shell.Frame.look [q, jj])
    (.mul (.var 0) (.add (.add (.add .one (.neg (.mul (.var 1) (.var 1)))) (.neg (.mul (.var 1) (.var 1)))) (.mul (.var 1) (.mul (.mul (.var 1) (.var 1)) (.var 1)))))
    (.add (.add .one (.mul (.add (.mul (.var 1) (.var 1)) .one) (.add (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.neg (.mul (.add (.add .one .one) .one) (.var 0)))))) (.mul (.add (.mul (.add (.add (.add .one .one) .one) .one) (.var 0)) (.neg .one)) .one)) (by decide +kernel)

/-! ## The four basis matrices on the cycle -/

variable {κ : Nat} {g : Shell p}

/-- The identity matrix. -/
def idm (k j : Nat) : Shell p := if k = j then 1 else 0

/-- `F J`, entrywise `F k (rev j)`. -/
def FJ (g : Shell p) (κ k j : Nat) : Shell p := Fmat g κ k (rev (p - 1) j)

/-- The combination `c₀ I + c₁ F + c₂ J + c₃ F J`. -/
def comb (g : Shell p) (κ : Nat) (c0 c1 c2 c3 : Shell p) (k j : Nat) : Shell p :=
  c0 * idm k j + c1 * Fmat g κ k j + c2 * J (p - 1) k j + c3 * FJ g κ k j

theorem mm_I_X (X : Nat → Nat → Shell p) {k j : Nat} (hk : k < p - 1) :
    sumRange (fun l => idm k l * X l j) (p - 1) = X k j := by
  rw [sum_eq_single hk (fun l _ hne => by unfold idm; rw [ite_eq_right (fun e => hne e.symm), zero_mul])]
  unfold idm; rw [ite_eq_left rfl, one_mul]

theorem mm_X_I (X : Nat → Nat → Shell p) {k j : Nat} (hj : j < p - 1) :
    sumRange (fun l => X k l * idm l j) (p - 1) = X k j := by
  rw [sum_eq_single hj (fun l _ hne => by unfold idm; rw [ite_eq_right hne, mul_zero])]
  unfold idm; rw [ite_eq_left rfl, mul_one]

theorem mm_J_X (X : Nat → Nat → Shell p) {k j : Nat} (hk : k < p - 1) :
    sumRange (fun l => (J (p - 1) k l : Shell p) * X l j) (p - 1) = X (rev (p - 1) k) j := by
  have hn : 0 < p - 1 := Nat.lt_of_le_of_lt (Nat.zero_le k) hk
  rw [sum_eq_single (rev_lt hn k) (fun l hl hne => by rw [J_eq hk hl, ite_eq_right hne, zero_mul])]
  rw [J_eq hk (rev_lt hn k), ite_eq_left rfl, one_mul]

theorem mm_X_J (X : Nat → Nat → Shell p) {k j : Nat} (hj : j < p - 1) :
    sumRange (fun l => X k l * (J (p - 1) l j : Shell p)) (p - 1) = X k (rev (p - 1) j) := by
  have hn : 0 < p - 1 := Nat.lt_of_le_of_lt (Nat.zero_le j) hj
  rw [sum_eq_single (rev_lt hn j) (fun l hl hne => by
    rw [J_eq hl hj, ite_eq_right (fun e => hne (by rw [e, rev_rev hl])), mul_zero])]
  rw [J_eq (rev_lt hn j) hj, ite_eq_left (rev_rev hj).symm, mul_one]

theorem J_rev_right {k j : Nat} (hk : k < p - 1) (hj : j < p - 1) :
    (J (p - 1) k (rev (p - 1) j) : Shell p) = idm k j := by
  have hn : 0 < p - 1 := Nat.lt_of_le_of_lt (Nat.zero_le k) hk
  rw [J_eq hk (rev_lt hn j)]
  unfold idm
  exact match Nat.decEq k j with
    | isTrue e => by rw [ite_eq_left (by rw [e]), ite_eq_left e]
    | isFalse e => by
        rw [ite_eq_right (fun h => e (by rw [← rev_rev hk, ← rev_rev hj, h])), ite_eq_right e]

theorem J_rev_left {k j : Nat} (hk : k < p - 1) (hj : j < p - 1) :
    (J (p - 1) (rev (p - 1) k) j : Shell p) = idm k j := by
  have hn : 0 < p - 1 := Nat.lt_of_le_of_lt (Nat.zero_le k) hk
  rw [J_eq (rev_lt hn k) hj, rev_rev hk]
  unfold idm
  exact match Nat.decEq k j with
    | isTrue e => by rw [ite_eq_left e.symm, ite_eq_left e]
    | isFalse e => by rw [ite_eq_right (fun h => e h.symm), ite_eq_right e]

theorem J_rev_rev {k j : Nat} (hk : k < p - 1) (hj : j < p - 1) :
    (J (p - 1) (rev (p - 1) k) (rev (p - 1) j) : Shell p) = J (p - 1) k j := by
  have hn : 0 < p - 1 := Nat.lt_of_le_of_lt (Nat.zero_le k) hk
  rw [J_eq (rev_lt hn k) (rev_lt hn j), rev_rev hk, J_eq hk hj]
  exact match Nat.decEq j (rev (p - 1) k) with
    | isTrue e => by rw [ite_eq_left e, ite_eq_left (by rw [e, rev_rev hk])]
    | isFalse e => by rw [ite_eq_right e, ite_eq_right (fun h => e (by rw [← h, rev_rev hj]))]

/-- `F (rev k) j = F k (rev j)`: both carry `g^{−jk}`. -/
theorem F_rev (F : Frame p κ g) {k j : Nat} (hk : k < p - 1) (hj : j < p - 1) :
    Fmat g κ (rev (p - 1) k) j = Fmat g κ k (rev (p - 1) j) := by
  have hn := F.n_pos
  unfold Fmat W
  have e1 : g ^ (j * rev (p - 1) k) * g ^ (j * k) = 1 := by
    rw [← pow_add, ← Nat.left_distrib, F.pow_mod, ← FRC.Nat.mul_mod_mod _ _ _ hn, rev_add_mod hk, Nat.mul_zero,
      FRC.Nat.zero_mod, pow_zero]
  have e2 : g ^ (rev (p - 1) j * k) * g ^ (j * k) = 1 := by
    rw [← pow_add, ← FRC.Nat.add_mul, F.pow_mod, ← FRC.Nat.mod_mul_mod _ _ _ hn, rev_add_mod hj, Nat.zero_mul,
      FRC.Nat.zero_mod, pow_zero]
  rw [inv_unique e1 e2]

/-! The sixteen products of the basis `I, F, J, G = F J`: the cyclic group of order four. -/

theorem mm_II {k j : Nat} (hk : k < p - 1) (_hj : j < p - 1) :
    sumRange (fun l => idm k l * idm l j) (p - 1) = (idm k j : Shell p) := mm_I_X idm hk
theorem mm_IF {k j : Nat} (hk : k < p - 1) (_hj : j < p - 1) :
    sumRange (fun l => idm k l * Fmat g κ l j) (p - 1) = Fmat g κ k j := mm_I_X (Fmat g κ) hk
theorem mm_IJ {k j : Nat} (hk : k < p - 1) (_hj : j < p - 1) :
    sumRange (fun l => idm k l * J (p - 1) l j) (p - 1) = (J (p - 1) k j : Shell p) := mm_I_X (J (p - 1)) hk
theorem mm_IG {k j : Nat} (hk : k < p - 1) (_hj : j < p - 1) :
    sumRange (fun l => idm k l * FJ g κ l j) (p - 1) = FJ g κ k j := mm_I_X (FJ g κ) hk
theorem mm_FI {k j : Nat} (_hk : k < p - 1) (hj : j < p - 1) :
    sumRange (fun l => Fmat g κ k l * idm l j) (p - 1) = Fmat g κ k j := mm_X_I (Fmat g κ) hj
theorem mm_JI {k j : Nat} (_hk : k < p - 1) (hj : j < p - 1) :
    sumRange (fun l => (J (p - 1) k l : Shell p) * idm l j) (p - 1) = J (p - 1) k j := mm_X_I (J (p - 1)) hj
theorem mm_GI {k j : Nat} (_hk : k < p - 1) (hj : j < p - 1) :
    sumRange (fun l => FJ g κ k l * idm l j) (p - 1) = FJ g κ k j := mm_X_I (FJ g κ) hj

theorem mm_FF (F : Frame p κ g) {k j : Nat} (_hk : k < p - 1) (_hj : j < p - 1) :
    sumRange (fun l => Fmat g κ k l * Fmat g κ l j) (p - 1) = J (p - 1) k j := F.F_sq k j
theorem mm_FJ {k j : Nat} (_hk : k < p - 1) (hj : j < p - 1) :
    sumRange (fun l => Fmat g κ k l * J (p - 1) l j) (p - 1) = FJ g κ k j := mm_X_J (Fmat g κ) hj
theorem mm_FG (F : Frame p κ g) {k j : Nat} (hk : k < p - 1) (hj : j < p - 1) :
    sumRange (fun l => Fmat g κ k l * FJ g κ l j) (p - 1) = idm k j := by
  show sumRange (fun l => Fmat g κ k l * Fmat g κ l (rev (p - 1) j)) (p - 1) = idm k j
  rw [F.F_sq k (rev (p - 1) j), J_rev_right hk hj]
theorem mm_JF (F : Frame p κ g) {k j : Nat} (hk : k < p - 1) (hj : j < p - 1) :
    sumRange (fun l => (J (p - 1) k l : Shell p) * Fmat g κ l j) (p - 1) = FJ g κ k j := by
  rw [mm_J_X (Fmat g κ) hk, F_rev F hk hj]; rfl
theorem mm_JJ (F : Frame p κ g) {k j : Nat} (hk : k < p - 1) (hj : j < p - 1) :
    sumRange (fun l => (J (p - 1) k l : Shell p) * J (p - 1) l j) (p - 1) = idm k j := F.J_sq hk hj
theorem mm_JG (F : Frame p κ g) {k j : Nat} (hk : k < p - 1) (hj : j < p - 1) :
    sumRange (fun l => (J (p - 1) k l : Shell p) * FJ g κ l j) (p - 1) = Fmat g κ k j := by
  have hn := F.n_pos
  rw [mm_J_X (FJ g κ) hk]
  show Fmat g κ (rev (p - 1) k) (rev (p - 1) j) = Fmat g κ k j
  rw [F_rev F hk (rev_lt hn j), rev_rev hj]
theorem mm_GF (F : Frame p κ g) {k j : Nat} (hk : k < p - 1) (hj : j < p - 1) :
    sumRange (fun l => FJ g κ k l * Fmat g κ l j) (p - 1) = idm k j := by
  have hn := F.n_pos
  rw [sum_congr _ (fun l hl => by
    show Fmat g κ k (rev (p - 1) l) * Fmat g κ l j = Fmat g κ (rev (p - 1) k) l * Fmat g κ l j
    rw [F_rev F hk hl])]
  rw [F.F_sq (rev (p - 1) k) j, J_rev_left hk hj]
theorem mm_GJ {k j : Nat} (_hk : k < p - 1) (hj : j < p - 1) :
    sumRange (fun l => FJ g κ k l * J (p - 1) l j) (p - 1) = Fmat g κ k j := by
  rw [mm_X_J (FJ g κ) hj]
  show Fmat g κ k (rev (p - 1) (rev (p - 1) j)) = Fmat g κ k j
  rw [rev_rev hj]
theorem mm_GG (F : Frame p κ g) {k j : Nat} (hk : k < p - 1) (hj : j < p - 1) :
    sumRange (fun l => FJ g κ k l * FJ g κ l j) (p - 1) = J (p - 1) k j := by
  rw [sum_congr _ (fun l hl => by
    show Fmat g κ k (rev (p - 1) l) * Fmat g κ l (rev (p - 1) j) = Fmat g κ (rev (p - 1) k) l * Fmat g κ l (rev (p - 1) j)
    rw [F_rev F hk hl])]
  have hn := F.n_pos
  rw [F.F_sq (rev (p - 1) k) (rev (p - 1) j), J_rev_rev hk hj]

/-- The product of two combinations is the cyclic convolution of their coefficients. -/
theorem comb_mul (F : Frame p κ g) {k j : Nat} (hk : k < p - 1) (hj : j < p - 1) (a0 a1 a2 a3 b0 b1 b2 b3 : Shell p) :
    sumRange (fun l => comb g κ a0 a1 a2 a3 k l * comb g κ b0 b1 b2 b3 l j) (p - 1) =
      comb g κ (a0 * b0 + a1 * b3 + a2 * b2 + a3 * b1) (a0 * b1 + a1 * b0 + a2 * b3 + a3 * b2)
        (a0 * b2 + a1 * b1 + a2 * b0 + a3 * b3) (a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0) k j := by
  have e : ∀ l, comb g κ a0 a1 a2 a3 k l * comb g κ b0 b1 b2 b3 l j =
      a0 * b0 * (idm k l * idm l j) + a0 * b1 * (idm k l * Fmat g κ l j) + a0 * b2 * (idm k l * J (p - 1) l j) + a0 * b3 * (idm k l * FJ g κ l j) + a1 * b0 * (Fmat g κ k l * idm l j) + a1 * b1 * (Fmat g κ k l * Fmat g κ l j) + a1 * b2 * (Fmat g κ k l * J (p - 1) l j) + a1 * b3 * (Fmat g κ k l * FJ g κ l j) + a2 * b0 * (J (p - 1) k l * idm l j) + a2 * b1 * (J (p - 1) k l * Fmat g κ l j) + a2 * b2 * (J (p - 1) k l * J (p - 1) l j) + a2 * b3 * (J (p - 1) k l * FJ g κ l j) + a3 * b0 * (FJ g κ k l * idm l j) + a3 * b1 * (FJ g κ k l * Fmat g κ l j) + a3 * b2 * (FJ g κ k l * J (p - 1) l j) + a3 * b3 * (FJ g κ k l * FJ g κ l j) := fun l =>
    Shell.Frame.RE.sound (Shell.Frame.look [a0, a1, a2, a3, b0, b1, b2, b3, idm k l, Fmat g κ k l, J (p - 1) k l, FJ g κ k l, idm l j, Fmat g κ l j, J (p - 1) l j, FJ g κ l j])
      (.mul (.add (.add (.add (.mul (.var 0) (.var 8)) (.mul (.var 1) (.var 9))) (.mul (.var 2) (.var 10))) (.mul (.var 3) (.var 11))) (.add (.add (.add (.mul (.var 4) (.var 12)) (.mul (.var 5) (.var 13))) (.mul (.var 6) (.var 14))) (.mul (.var 7) (.var 15))))
      (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.mul (.mul (.var 0) (.var 4)) (.mul (.var 8) (.var 12))) (.mul (.mul (.var 0) (.var 5)) (.mul (.var 8) (.var 13)))) (.mul (.mul (.var 0) (.var 6)) (.mul (.var 8) (.var 14)))) (.mul (.mul (.var 0) (.var 7)) (.mul (.var 8) (.var 15)))) (.mul (.mul (.var 1) (.var 4)) (.mul (.var 9) (.var 12)))) (.mul (.mul (.var 1) (.var 5)) (.mul (.var 9) (.var 13)))) (.mul (.mul (.var 1) (.var 6)) (.mul (.var 9) (.var 14)))) (.mul (.mul (.var 1) (.var 7)) (.mul (.var 9) (.var 15)))) (.mul (.mul (.var 2) (.var 4)) (.mul (.var 10) (.var 12)))) (.mul (.mul (.var 2) (.var 5)) (.mul (.var 10) (.var 13)))) (.mul (.mul (.var 2) (.var 6)) (.mul (.var 10) (.var 14)))) (.mul (.mul (.var 2) (.var 7)) (.mul (.var 10) (.var 15)))) (.mul (.mul (.var 3) (.var 4)) (.mul (.var 11) (.var 12)))) (.mul (.mul (.var 3) (.var 5)) (.mul (.var 11) (.var 13)))) (.mul (.mul (.var 3) (.var 6)) (.mul (.var 11) (.var 14)))) (.mul (.mul (.var 3) (.var 7)) (.mul (.var 11) (.var 15)))) (by decide +kernel)
  rw [sum_congr _ (fun l _ => e l)]
  rw [sum_add, sum_add, sum_add, sum_add, sum_add, sum_add, sum_add, sum_add, sum_add, sum_add, sum_add, sum_add, sum_add, sum_add, sum_add]
  rw [sum_mul_left, sum_mul_left, sum_mul_left, sum_mul_left, sum_mul_left, sum_mul_left, sum_mul_left, sum_mul_left, sum_mul_left, sum_mul_left, sum_mul_left, sum_mul_left, sum_mul_left, sum_mul_left, sum_mul_left, sum_mul_left]
  rw [mm_II hk hj, mm_IF hk hj, mm_IJ hk hj, mm_IG hk hj, mm_FI hk hj, mm_FF F hk hj, mm_FJ hk hj, mm_FG F hk hj, mm_JI hk hj, mm_JF F hk hj, mm_JJ F hk hj, mm_JG F hk hj, mm_GI hk hj, mm_GF F hk hj, mm_GJ hk hj, mm_GG F hk hj]
  exact Shell.Frame.RE.sound (Shell.Frame.look [a0, a1, a2, a3, b0, b1, b2, b3, idm k j, Fmat g κ k j, J (p - 1) k j, FJ g κ k j])
    (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.mul (.mul (.var 0) (.var 4)) (.var 8)) (.mul (.mul (.var 0) (.var 5)) (.var 9))) (.mul (.mul (.var 0) (.var 6)) (.var 10))) (.mul (.mul (.var 0) (.var 7)) (.var 11))) (.mul (.mul (.var 1) (.var 4)) (.var 9))) (.mul (.mul (.var 1) (.var 5)) (.var 10))) (.mul (.mul (.var 1) (.var 6)) (.var 11))) (.mul (.mul (.var 1) (.var 7)) (.var 8))) (.mul (.mul (.var 2) (.var 4)) (.var 10))) (.mul (.mul (.var 2) (.var 5)) (.var 11))) (.mul (.mul (.var 2) (.var 6)) (.var 8))) (.mul (.mul (.var 2) (.var 7)) (.var 9))) (.mul (.mul (.var 3) (.var 4)) (.var 11))) (.mul (.mul (.var 3) (.var 5)) (.var 8))) (.mul (.mul (.var 3) (.var 6)) (.var 9))) (.mul (.mul (.var 3) (.var 7)) (.var 10)))
    (.add (.add (.add (.mul (.add (.add (.add (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 7))) (.mul (.var 2) (.var 6))) (.mul (.var 3) (.var 5))) (.var 8)) (.mul (.add (.add (.add (.mul (.var 0) (.var 5)) (.mul (.var 1) (.var 4))) (.mul (.var 2) (.var 7))) (.mul (.var 3) (.var 6))) (.var 9))) (.mul (.add (.add (.add (.mul (.var 0) (.var 6)) (.mul (.var 1) (.var 5))) (.mul (.var 2) (.var 4))) (.mul (.var 3) (.var 7))) (.var 10))) (.mul (.add (.add (.add (.mul (.var 0) (.var 7)) (.mul (.var 1) (.var 6))) (.mul (.var 2) (.var 5))) (.mul (.var 3) (.var 4))) (.var 11))) (by decide +kernel)

/-! ## The fractional family -/

/-- The coefficients of `Σ_ℓ u^ℓ Π_ℓ` reduced with `j² = −1` (`j = i⁻¹ = −i`). -/
def NF0 (q _jj u : Shell p) : Shell p := q * (1 + u + u * u + u * u * u)
def NF1 (q jj u : Shell p) : Shell p := q * (1 + jj * u + -(u * u) + -(jj * (u * u * u)))
def NF2 (q _jj u : Shell p) : Shell p := q * (1 + -u + u * u + -(u * u * u))
def NF3 (q jj u : Shell p) : Shell p := q * (1 + -(jj * u) + -(u * u) + jj * (u * u * u))

/-- The spectral projector `Π_ℓ = 4⁻¹ Σ_{m<4} i^{−ℓm} F^m`, with `4⁻¹ = −κ` and `i⁻¹ = −i`. -/
def proj (g : Shell p) (κ ℓ : Nat) (k j : Nat) : Shell p :=
  comb g κ (-(ofNat κ)) (-(ofNat κ) * (-(quarterTurn g κ)) ^ ℓ) (-(ofNat κ) * (-(quarterTurn g κ)) ^ (2 * ℓ))
    (-(ofNat κ) * (-(quarterTurn g κ)) ^ (3 * ℓ)) k j

/-- The fractional family `F^{[s]} = Σ_{ℓ<4} z^{ℓs} Π_ℓ` (6:C3), `z` the refinement base. -/
def frft (g : Shell p) (κ : Nat) (z : Shell p) (s : Nat) (k j : Nat) : Shell p :=
  (z ^ s) ^ 0 * proj g κ 0 k j + (z ^ s) ^ 1 * proj g κ 1 k j + (z ^ s) ^ 2 * proj g κ 2 k j +
    (z ^ s) ^ 3 * proj g κ 3 k j

/-- Matrix powers on the cycle. -/
def mpow (A : Nat → Nat → Shell p) : Nat → Nat → Nat → Shell p
  | 0 => idm
  | m + 1 => fun k j => sumRange (fun l => mpow A m k l * A l j) (p - 1)

theorem hjj (F : Frame p κ g) : -(quarterTurn g κ) * -(quarterTurn g κ) + 1 = 0 := by
  rw [neg_mul_neg, F.quarter_turn_sq, neg_add]

theorem hq (F : Frame p κ g) : (1 + 1 + 1 + 1 : Shell p) * -(ofNat κ) + -1 = 0 := by
  have e4 : (1 + 1 + 1 + 1 : Shell p) = ofNat 4 := by
    rw [show (ofNat 4 : Shell p) = ofNat (3 + 1) from rfl, ofNat_succ, show (ofNat 3 : Shell p) = ofNat (2 + 1) from rfl,
      ofNat_succ, show (ofNat 2 : Shell p) = ofNat (1 + 1) from rfl, ofNat_succ]; rfl
  rw [e4, ← mul_neg, ofNat_mul, ← F.n_eq, F.ofNat_n, neg_neg, add_neg]

/-- 6:E7, the expansion `F^{[s]} = Σ_r c_r(s) F^r` in the basis `I, F, J, FJ`: the coefficients `c_r(s) = NF_r(z^s)`
(their geometric-sum form is `frft_coeff` of `Theme/Heisenberg.lean`). -/
theorem frft_eq (F : Frame p κ g) (z : Shell p) (s k j : Nat) :
    frft g κ z s k j = comb g κ (NF0 (-(ofNat κ)) (-(quarterTurn g κ)) (z ^ s)) (NF1 (-(ofNat κ)) (-(quarterTurn g κ)) (z ^ s))
      (NF2 (-(ofNat κ)) (-(quarterTurn g κ)) (z ^ s)) (NF3 (-(ofNat κ)) (-(quarterTurn g κ)) (z ^ s)) k j := by
  have h := frft_aux (-(ofNat κ) : Shell p) (-(quarterTurn g κ)) (z ^ s) (idm k j) (Fmat g κ k j) (J (p - 1) k j)
    (FJ g κ k j)
  exact red1 h (hjj F)

section conv
variable {q jj : Shell p} (h1 : jj * jj + 1 = 0) (h2 : (1 + 1 + 1 + 1 : Shell p) * q + -1 = 0)
include h1 h2

theorem conv0 (u v : Shell p) : NF0 q jj u * NF0 q jj v + NF1 q jj u * NF3 q jj v + NF2 q jj u * NF2 q jj v +
    NF3 q jj u * NF1 q jj v = NF0 q jj (u * v) := by
  exact red2 (conv0_aux q jj u v) h1 h2
theorem conv1 (u v : Shell p) : NF0 q jj u * NF1 q jj v + NF1 q jj u * NF0 q jj v + NF2 q jj u * NF3 q jj v +
    NF3 q jj u * NF2 q jj v = NF1 q jj (u * v) := by
  exact red2 (conv1_aux q jj u v) h1 h2
theorem conv2 (u v : Shell p) : NF0 q jj u * NF2 q jj v + NF1 q jj u * NF1 q jj v + NF2 q jj u * NF0 q jj v +
    NF3 q jj u * NF3 q jj v = NF2 q jj (u * v) := by
  exact red2 (conv2_aux q jj u v) h1 h2
theorem conv3 (u v : Shell p) : NF0 q jj u * NF3 q jj v + NF1 q jj u * NF2 q jj v + NF2 q jj u * NF1 q jj v +
    NF3 q jj u * NF0 q jj v = NF3 q jj (u * v) := by
  exact red2 (conv3_aux q jj u v) h1 h2
end conv

section card
variable {q jj : Shell p} (h1 : jj * jj + 1 = 0) (h2 : (1 + 1 + 1 + 1 : Shell p) * q + -1 = 0)
include h1 h2

theorem card_one : NF0 q jj (1) = 1 ∧ NF1 q jj (1) = 0 ∧ NF2 q jj (1) = 0 ∧ NF3 q jj (1) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact red2 (card00_aux q jj) h1 h2
  · exact red2 (card01_aux q jj) h1 h2
  · exact red2 (card02_aux q jj) h1 h2
  · exact red2 (card03_aux q jj) h1 h2

theorem card_i : NF0 q jj (-jj) = 0 ∧ NF1 q jj (-jj) = 1 ∧ NF2 q jj (-jj) = 0 ∧ NF3 q jj (-jj) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact red2 (card10_aux q jj) h1 h2
  · exact red2 (card11_aux q jj) h1 h2
  · exact red2 (card12_aux q jj) h1 h2
  · exact red2 (card13_aux q jj) h1 h2

theorem card_m1 : NF0 q jj (-1) = 0 ∧ NF1 q jj (-1) = 0 ∧ NF2 q jj (-1) = 1 ∧ NF3 q jj (-1) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact red2 (card20_aux q jj) h1 h2
  · exact red2 (card21_aux q jj) h1 h2
  · exact red2 (card22_aux q jj) h1 h2
  · exact red2 (card23_aux q jj) h1 h2

theorem card_mi : NF0 q jj (jj) = 0 ∧ NF1 q jj (jj) = 0 ∧ NF2 q jj (jj) = 0 ∧ NF3 q jj (jj) = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact red2 (card30_aux q jj) h1 h2
  · exact red2 (card31_aux q jj) h1 h2
  · exact red2 (card32_aux q jj) h1 h2
  · exact red2 (card33_aux q jj) h1 h2

end card

/-- The inverse drive: `z^κ = i` and `z^{p−1} = 1` for `g z = 1`. -/
theorem inv_pow_kappa (F : Frame p κ g) {z : Shell p} (hz : g * z = 1) : z ^ κ = quarterTurn g κ := by
  have e1 : z ^ κ * g ^ κ = 1 := by rw [← mul_pow, mul_comm, hz, one_pow]
  have e2 : quarterTurn g κ * g ^ κ = 1 := by
    show -(g ^ κ) * g ^ κ = 1
    rw [← neg_mul, ← pow_add, ← Nat.two_mul, F.half_period, neg_neg]
  exact inv_unique e1 e2

theorem inv_pow_n (F : Frame p κ g) {z : Shell p} (hz : g * z = 1) : z ^ (p - 1) = 1 := by
  have e : g ^ (p - 1) * z ^ (p - 1) = 1 := by rw [← mul_pow, hz, one_pow]
  rw [F.pow_n, one_mul] at e; exact e

/-- 6:C3, the cardinal values: `F^{[0]} = I`, `F^{[κ]} = F`, `F^{[2κ]} = J`, `F^{[3κ]} = F J`. -/
theorem frft_cardinal (F : Frame p κ g) {z : Shell p} (hz : g * z = 1) (k j : Nat) :
    frft g κ z 0 k j = idm k j ∧ frft g κ z κ k j = Fmat g κ k j ∧ frft g κ z (2 * κ) k j = J (p - 1) k j ∧
      frft g κ z (3 * κ) k j = FJ g κ k j := by
  have hzk := inv_pow_kappa F hz
  have h1 := hjj F; have h2 := hq F
  have z1 : z ^ κ = -(-(quarterTurn g κ)) := by rw [neg_neg]; exact hzk
  have z2 : z ^ (2 * κ) = -1 := by rw [Nat.two_mul, pow_add, hzk, F.quarter_turn_sq]
  have z3 : z ^ (3 * κ) = -(quarterTurn g κ) := by
    rw [show 3 * κ = 2 * κ + κ by rw [Nat.succ_mul, Nat.add_comm], pow_add, z2, hzk, ← neg_mul, one_mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨e0, e1, e2, e3⟩ := card_one h1 h2
    rw [frft_eq F z 0 k j, pow_zero, e0, e1, e2, e3]
    show 1 * idm k j + 0 * Fmat g κ k j + 0 * J (p - 1) k j + 0 * FJ g κ k j = idm k j
    rw [one_mul, zero_mul, zero_mul, zero_mul, add_zero, add_zero, add_zero]
  · obtain ⟨e0, e1, e2, e3⟩ := card_i h1 h2
    rw [frft_eq F z κ k j, z1, e0, e1, e2, e3]
    show 0 * idm k j + 1 * Fmat g κ k j + 0 * J (p - 1) k j + 0 * FJ g κ k j = Fmat g κ k j
    rw [one_mul, zero_mul, zero_mul, zero_mul, zero_add, add_zero, add_zero]
  · obtain ⟨e0, e1, e2, e3⟩ := card_m1 h1 h2
    rw [frft_eq F z (2 * κ) k j, z2, e0, e1, e2, e3]
    show 0 * idm k j + 0 * Fmat g κ k j + 1 * J (p - 1) k j + 0 * FJ g κ k j = J (p - 1) k j
    rw [one_mul, zero_mul, zero_mul, zero_mul, zero_add, zero_add, add_zero]
  · obtain ⟨e0, e1, e2, e3⟩ := card_mi h1 h2
    rw [frft_eq F z (3 * κ) k j, z3, e0, e1, e2, e3]
    show 0 * idm k j + 0 * Fmat g κ k j + 0 * J (p - 1) k j + 1 * FJ g κ k j = FJ g κ k j
    rw [one_mul, zero_mul, zero_mul, zero_mul, zero_add, zero_add, zero_add]

/-- 6:C3, additivity: `F^{[s+r]} = F^{[s]} F^{[r]}` on the cycle, a representation of `ℤ/(p−1)`. -/
theorem frft_add (F : Frame p κ g) (z : Shell p) (s r : Nat) {k j : Nat} (hk : k < p - 1) (hj : j < p - 1) :
    frft g κ z (s + r) k j = sumRange (fun l => frft g κ z s k l * frft g κ z r l j) (p - 1) := by
  rw [sum_congr _ (fun l _ => by rw [frft_eq F z s k l, frft_eq F z r l j]), comb_mul F hk hj, frft_eq F z (s + r) k j,
    pow_add, conv0 (hjj F) (hq F), conv1 (hjj F) (hq F), conv2 (hjj F) (hq F), conv3 (hjj F) (hq F)]

/-- 6:C3, the period: the family is periodic over the cycle, `F^{[s + (p−1)]} = F^{[s]}`, so `F^{[4κ]} = I`. -/
theorem frft_period (F : Frame p κ g) {z : Shell p} (hz : g * z = 1) (s k j : Nat) :
    frft g κ z (s + (p - 1)) k j = frft g κ z s k j := by
  unfold frft; rw [pow_add, inv_pow_n F hz, mul_one]

/-- 6:C3, the root: `F^{[m s]} = (F^{[s]})^m`; in particular `(F^{[1]})^κ = F^{[κ]} = F`. -/
theorem frft_pow (F : Frame p κ g) {z : Shell p} (hz : g * z = 1) (s : Nat) :
    ∀ m k j, k < p - 1 → j < p - 1 → frft g κ z (m * s) k j = mpow (frft g κ z s) m k j
  | 0, k, j, _, _ => by rw [Nat.zero_mul]; exact (frft_cardinal F hz k j).1
  | m + 1, k, j, hk, hj => by
    rw [Nat.succ_mul, frft_add F z (m * s) s hk hj]
    exact sum_congr _ (fun l hl => by rw [frft_pow F hz s m k l hk hl])

/-- **C2 (p00022), scale-shift duality.** Dilation `x ↦ g x` is phase evolution of the frame: it advances the
longitude (`S_r(M_m) = M_{m+r}`), with period `p − 1`; over the cycle it is the fractional Fourier family, a
representation of `ℤ/(p−1)` (`F^{[s+r]} = F^{[s]} F^{[r]}`, period `p − 1`) whose quarter-turn value `F^{[κ]}` is the
transform `F` itself, with `F^{[0]} = I`, `F^{[2κ]} = J`, `F^{[3κ]} = F J = F⁻¹` and `(F^{[1]})^κ = F`. -/
theorem scale_shift (F : Frame p κ g) {z : Shell p} (hz : g * z = 1) :
    (∀ m r, (meridian g κ m).map (scale g r) = meridian g κ (m + r)) ∧
    (∀ r x, scale g (r + (p - 1)) x = scale g r x) ∧
    (∀ s r k j, k < p - 1 → j < p - 1 →
      frft g κ z (s + r) k j = sumRange (fun l => frft g κ z s k l * frft g κ z r l j) (p - 1)) ∧
    (∀ s k j, frft g κ z (s + (p - 1)) k j = frft g κ z s k j) ∧
    (∀ k j, frft g κ z 0 k j = idm k j ∧ frft g κ z κ k j = Fmat g κ k j ∧ frft g κ z (2 * κ) k j = J (p - 1) k j ∧
      frft g κ z (3 * κ) k j = FJ g κ k j) ∧
    (∀ k j, k < p - 1 → j < p - 1 → sumRange (fun l => FJ g κ k l * Fmat g κ l j) (p - 1) = idm k j) ∧
    (∀ k j, k < p - 1 → j < p - 1 → mpow (frft g κ z 1) κ k j = Fmat g κ k j) :=
  ⟨fun m r => meridian_scale g κ m r, fun r x => FRC.Shell.scale_periodic F r x,
   fun s r k j hk hj => frft_add F z s r hk hj, fun s k j => frft_period F hz s k j,
   fun k j => frft_cardinal F hz k j, fun k j hk hj => mm_GF F hk hj,
   fun k j hk hj => by rw [← frft_pow F hz 1 κ k j hk hj, Nat.mul_one]; exact (frft_cardinal F hz k j).2.1⟩

/-- 00:C2 — the transform follows the dilation: `g^s = g^{s'}` gives `F^{[s]} = F^{[s']}`, so the fractional Fourier
family is indexed by the dilations themselves. -/
theorem frft_dilation (F : Frame p κ g) {z : Shell p} (hz : g * z = 1) {s s' : Nat} (h : g ^ s = g ^ s') (k j : Nat) :
    frft g κ z s k j = frft g κ z s' k j := by
  have hper : ∀ n u, frft g κ z (u + n * (p - 1)) k j = frft g κ z u k j := fun n u => by
    induction n with
    | zero => rw [Nat.zero_mul, Nat.add_zero]
    | succ n ih => rw [Nat.succ_mul, ← Nat.add_assoc, frft_period F hz, ih]
  have hred : ∀ u, frft g κ z u k j = frft g κ z (u % (p - 1)) k j := fun u => by
    obtain ⟨q, hq⟩ := FRC.Nat.mod_spec (p - 1) F.n_pos u
    conv => lhs; rw [hq, Nat.add_comm, Nat.mul_comm]
    exact hper q _
  have hm : s % (p - 1) = s' % (p - 1) :=
    F.pow_inj (Nat.mod_lt _ F.n_pos) (Nat.mod_lt _ F.n_pos) (by rw [← F.pow_mod, ← F.pow_mod]; exact h)
  rw [hred s, hred s', hm]

/-! ## C7: the conjugate frame, and the Carrier's quarter-turn -/

/-- 6:C9, the conjugate frame: the inverse drive `g⁻¹` is a frame of the same shell and capacity. -/
theorem inv_frame (F : Frame p κ g) {z : Shell p} (hz : g * z = 1) : Frame p κ z := by
  have hpow : ∀ l, g ^ l * z ^ l = 1 := fun l => by rw [← mul_pow, hz, one_pow]
  exact ⟨F.cap, F.cap_pos, ⟨by have := hpow (p - 1); rwa [F.pow_n, one_mul] at this,
    fun l hl hl0 e => F.prim.2 l hl hl0 (by have := hpow l; rwa [e, mul_one] at this)⟩⟩

theorem inv_quarter (F : Frame p κ g) {z : Shell p} (hz : g * z = 1) : quarterTurn z κ = -quarterTurn g κ := by
  show -(z ^ κ) = -quarterTurn g κ
  rw [inv_pow_kappa F hz]

/-- 6:C9, the conjugate frame's transform is `−F J = −F⁻¹`. -/
theorem Fmat_conj (F : Frame p κ g) {z : Shell p} (hz : g * z = 1) {k j : Nat} (_hk : k < p - 1) (hj : j < p - 1) :
    Fmat z κ k j = -(FJ g κ k j) := by
  have hn := F.n_pos
  have e1 : z ^ (j * k) * g ^ (j * k) = 1 := by rw [← mul_pow, mul_comm, hz, one_pow]
  have e2 : g ^ (rev (p - 1) j * k) * g ^ (j * k) = 1 := by
    rw [← pow_add, ← FRC.Nat.add_mul, F.pow_mod, ← FRC.Nat.mod_mul_mod _ _ _ hn, rev_add_mod hj, Nat.zero_mul,
      FRC.Nat.zero_mod, pow_zero]
  show quarterTurn z κ * z ^ (j * k) = -(quarterTurn g κ * g ^ (rev (p - 1) j * k))
  rw [inv_quarter F hz, inv_unique e1 e2, neg_mul]

theorem FJ_conj (F : Frame p κ g) {z : Shell p} (hz : g * z = 1) {k j : Nat} (hk : k < p - 1) (hj : j < p - 1) :
    FJ z κ k j = -(Fmat g κ k j) := by
  have hn := F.n_pos
  show Fmat z κ k (rev (p - 1) j) = -(Fmat g κ k j)
  rw [Fmat_conj F hz hk (rev_lt hn j)]
  show -(Fmat g κ k (rev (p - 1) (rev (p - 1) j))) = -(Fmat g κ k j)
  rw [rev_rev hj]

theorem comb_conj (F : Frame p κ g) {z : Shell p} (hz : g * z = 1) {k j : Nat} (hk : k < p - 1) (hj : j < p - 1)
    (c0 c1 c2 c3 : Shell p) : comb z κ c0 c1 c2 c3 k j = comb g κ c0 (-c3) c2 (-c1) k j := by
  show c0 * idm k j + c1 * Fmat z κ k j + c2 * J (p - 1) k j + c3 * FJ z κ k j =
    c0 * idm k j + -c3 * Fmat g κ k j + c2 * J (p - 1) k j + -c1 * FJ g κ k j
  rw [Fmat_conj F hz hk hj, FJ_conj F hz hk hj]
  exact Shell.Frame.RE.sound (Shell.Frame.look [c0, c1, c2, c3, idm k j, Fmat g κ k j, J (p - 1) k j, FJ g κ k j])
    (.add (.add (.add (.mul (.var 0) (.var 4)) (.mul (.var 1) (.neg (.var 7)))) (.mul (.var 2) (.var 6)))
      (.mul (.var 3) (.neg (.var 5))))
    (.add (.add (.add (.mul (.var 0) (.var 4)) (.mul (.neg (.var 3)) (.var 5))) (.mul (.var 2) (.var 6)))
      (.mul (.neg (.var 1)) (.var 7))) (by decide +kernel)

theorem neg_sq_pow {i : Shell p} (h : i * i = -1) : (-i) ^ 2 = -1 := by rw [pow_two, neg_mul_neg]; exact h
theorem cube_pow {i : Shell p} (h : i * i = -1) : i ^ 3 = -i := by
  rw [pow_succ, pow_two, h, ← neg_mul, one_mul]
theorem neg_cube_pow {i : Shell p} (h : i * i = -1) : (-i) ^ 3 = i := by
  rw [pow_succ, neg_sq_pow h, neg_mul_neg, one_mul]

/-- 6:C9, the conjugate frame's projectors are the shifted ones, `Π'_ℓ = Π_{ℓ+2}`. -/
theorem proj_conj (F : Frame p κ g) {z : Shell p} (hz : g * z = 1) (ℓ : Nat) {k j : Nat} (hk : k < p - 1)
    (hj : j < p - 1) : proj z κ ℓ k j = proj g κ (ℓ + 2) k j := by
  have h := F.quarter_turn_sq
  unfold proj
  rw [inv_quarter F hz, neg_neg, comb_conj F hz hk hj]
  have a1 : -(-(ofNat κ : Shell p) * quarterTurn g κ ^ (3 * ℓ)) = -(ofNat κ) * (-(quarterTurn g κ)) ^ (ℓ + 2) := by
    rw [pow_mul, cube_pow h, pow_add, neg_sq_pow h, ← mul_neg, mul_one, mul_neg]
  have a2 : -(ofNat κ : Shell p) * quarterTurn g κ ^ (2 * ℓ) = -(ofNat κ) * (-(quarterTurn g κ)) ^ (2 * (ℓ + 2)) := by
    rw [pow_mul, pow_mul, pow_two, h, neg_sq_pow h, pow_add, pow_two (-1 : Shell p), neg_mul_neg, one_mul, mul_one]
  have a3 : -(-(ofNat κ : Shell p) * quarterTurn g κ ^ ℓ) = -(ofNat κ) * (-(quarterTurn g κ)) ^ (3 * (ℓ + 2)) := by
    rw [pow_mul, neg_cube_pow h, pow_add, pow_two, h, ← mul_neg, mul_one, mul_neg]
  rw [a1, a2, a3]

/-- **C7 (p00172), orientation is derived.** On every Carrier the quarter-turn `ħ` (`ħ² = −1`) has `ħ^S = ±1` when
`S` is even: no orientation survives transport. On every frame the oriented quarter-turn is the conjugate drive's
power, `i = −g^κ = (g⁻¹)^κ`; the conjugate `g⁻¹` is a frame with quarter-turn `−i`, its transform is `−F J = −F⁻¹`,
and its projectors are `Π_{ℓ+2}`: the joint flip permutes the registration channels and preserves their family. -/
theorem orientation (F : Frame p κ g) {z : Shell p} (hz : g * z = 1) :
    (∀ {Ω : Nat} [Pos Ω] (h : Shell Ω) (S : Nat), h * h = -1 → S % 2 = 0 → h ^ S = 1 ∨ h ^ S = -1) ∧
    z ^ κ = quarterTurn g κ ∧ Frame p κ z ∧ quarterTurn z κ = -quarterTurn g κ ∧
    (∀ k j, k < p - 1 → j < p - 1 → Fmat z κ k j = -(FJ g κ k j)) ∧
    (∀ ℓ k j, k < p - 1 → j < p - 1 → proj z κ ℓ k j = proj g κ (ℓ + 2) k j) := by
  refine ⟨fun h S hh hS => ?_, inv_pow_kappa F hz, inv_frame F hz, inv_quarter F hz,
    fun k j hk hj => Fmat_conj F hz hk hj, fun ℓ k j hk hj => proj_conj F hz ℓ hk hj⟩
  obtain ⟨m, hm⟩ := FRC.Nat.mod_spec 2 (by decide) S
  rw [hS, Nat.add_zero] at hm
  rw [hm, pow_mul, pow_two, hh, neg_one_pow]
  exact match Nat.decEq (m % 2) 0 with
    | isTrue e => .inl (by rw [ite_eq_left e])
    | isFalse e => .inr (by rw [ite_eq_right e])

end Frame
end Shell
end FRC
