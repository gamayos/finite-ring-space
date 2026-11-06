import FrcCore.Theme.Dirac

/-!
# The Lorentzian plane of 8-dirac — the class datum, the boosts and the Cayley map, no axioms

The second file of the dirac theme (5 November 2026, the core-proof programme of
`8-dirac-20260709/reports/core-proofs-20261105/`): what the Lorentzian plane of the shell gives on every frame
`(τ; 0, 1, g)` with its drive `g` and every nonsquare `ν`, by the frame theme's parity and the ring normaliser
(`RE.sound`, a kernel decision of a polynomial identity on the shell). The class is the datum: the product of two
nonsquares is a square, since both are odd powers of the drive, and the Lorentzian form depends on its coefficient
through the class alone (B2). The boost `Λ(x, y)` of a pair with `δ = x² − νy² ≠ 0` has the entries
`A = (x² + νy²)/δ`, `B = −2xy/δ` with `A² − νB² = 1`, so the extension theme's `boost_preserves` applies (D14); the
boosts compose as the extension multiplies, `Λ(z)Λ(z') = Λ(zz')`, with `Λ(1) = 1` and `Λ(z̄) = Λ(z)⁻¹` (D15). The
scalar Cayley map `φ(λ) = (1 + λw)/(1 − λw)` and its gauge flip `φ⁻(λ) = (1 − λw)/(1 + λw)` are inverse to each
other, with the inverse of the common norm `1 − νλ²` supplied (C16). Every statement is general in the shell; the
inverses enter as hypotheses `d · u = 1`, which Fermat's theorem (`Field.fermat`, `u = d^{p−2}`) discharges on a prime
shell. No axioms.
-/

namespace FRC.Dirac.Plane

open FRC FRC.Shell FRC.Shell.Frame FRC.Extension

variable {p : Nat} [Pos p]

/-! ## 8:B2 — the class is the datum -/
section classdatum
variable {κ : Nat} {g : Shell p}

/-- A nonzero residue is a power of the drive below `p − 1`: the frame generates. -/
theorem exists_pow_eq (F : Frame p κ g) {a : Shell p} (ha : a ≠ 0) : ∃ m, m < p - 1 ∧ g ^ m = a := by
  have hv : 0 < a.val := by
    rcases Nat.eq_zero_or_pos a.val with h0 | h0
    · exact absurd (Shell.ext (by rw [h0]; rfl)) ha
    · exact h0
  obtain ⟨m, hm, he⟩ := F.generates a.val a.lt hv
  exact ⟨m, hm, Shell.ext he⟩

/-- A nonsquare residue is an odd power of the drive. -/
theorem odd_of_nonsquare (F : Frame p κ g) {a : Shell p} (ha : ¬IsSquare a) {m : Nat} (hm : g ^ m = a) :
    m % 2 = 1 := by
  rcases mod_two_cases m with h | h
  · obtain ⟨r, hr⟩ := (parity_iff F m).2 h
    exact absurd ⟨r, by rw [hr, hm]⟩ ha
  · exact h

/-- 8:B2 — the nonsquares form one square class: the product of two nonsquares is a square, on every frame. Each
is an odd power of the drive, so the product is an even power. -/
theorem class_datum (F : Frame p κ g) {a b : Shell p} (ha0 : a ≠ 0) (hb0 : b ≠ 0) (ha : ¬IsSquare a)
    (hb : ¬IsSquare b) : IsSquare (a * b) := by
  obtain ⟨m, -, hm⟩ := exists_pow_eq F ha0
  obtain ⟨n, -, hn⟩ := exists_pow_eq F hb0
  have hmo := odd_of_nonsquare F ha hm
  have hno := odd_of_nonsquare F hb hn
  have he : (m + n) % 2 = 0 := by
    rw [FRC.Nat.add_mod m n 2 (by decide), hmo, hno]
  rw [← hm, ← hn, ← Shell.pow_add]
  exact (parity_iff F (m + n)).2 he

/-- 8:B2 — the Lorentzian form depends on its coefficient through the class alone: for every `m`,
`−(m²ν) x₀² + x₁² + x₂² + x₃² = −ν (m x₀)² + x₁² + x₂² + x₃²`, so the forms of `ν` and `m²ν` are equivalent by
the rescaling `x₀ ↦ m x₀` (a polynomial identity, decided by the normaliser). -/
theorem form_class (ν m x₀ x₁ x₂ x₃ : Shell p) :
    -(m * m * ν) * (x₀ * x₀) + x₁ * x₁ + x₂ * x₂ + x₃ * x₃ =
      -ν * ((m * x₀) * (m * x₀)) + x₁ * x₁ + x₂ * x₂ + x₃ * x₃ :=
  RE.sound (look [ν, m, x₀, x₁, x₂, x₃])
    (.add (.add (.add (.mul (.neg (.mul (.mul (.var 1) (.var 1)) (.var 0))) (.mul (.var 2) (.var 2)))
      (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))
    (.add (.add (.add (.mul (.neg (.var 0)) (.mul (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 2))))
      (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))
    (by decide +kernel)

end classdatum

/-! ## 8:D14, 8:D15 — the boosts -/
section boosts

/-- The boost of the pair `(x, y)`, with `u` the inverse of `δ = x² − νy²`: the extension element `A + Bw`,
`A = (x² + νy²)u`, `B = −2xy·u`. -/
def boostOf (ν x y u : Shell p) : Ext p ν := ⟨(x * x + ν * (y * y)) * u, -((x + x) * y) * u⟩

/-- 8:D14 — the boost entries have `A² − νB² = 1`: `A² − νB² = (δu)²` as polynomials, and `δu = 1`. -/
theorem boost_entries_norm (ν x y u : Shell p) (hu : (x * x + -(ν * (y * y))) * u = 1) :
    (boostOf ν x y u).re * (boostOf ν x y u).re + -(ν * ((boostOf ν x y u).im * (boostOf ν x y u).im)) = 1 := by
  show (x * x + ν * (y * y)) * u * ((x * x + ν * (y * y)) * u) +
      -(ν * (-((x + x) * y) * u * (-((x + x) * y) * u))) = 1
  have e : (x * x + ν * (y * y)) * u * ((x * x + ν * (y * y)) * u) +
      -(ν * (-((x + x) * y) * u * (-((x + x) * y) * u))) =
      ((x * x + -(ν * (y * y))) * u) * ((x * x + -(ν * (y * y))) * u) :=
    RE.sound (look [ν, x, y, u])
      (.add (.mul (.mul (.add (.mul (.var 1) (.var 1)) (.mul (.var 0) (.mul (.var 2) (.var 2)))) (.var 3))
                  (.mul (.add (.mul (.var 1) (.var 1)) (.mul (.var 0) (.mul (.var 2) (.var 2)))) (.var 3)))
            (.neg (.mul (.var 0) (.mul (.mul (.neg (.mul (.add (.var 1) (.var 1)) (.var 2))) (.var 3))
                                       (.mul (.neg (.mul (.add (.var 1) (.var 1)) (.var 2))) (.var 3))))))
      (.mul (.mul (.add (.mul (.var 1) (.var 1)) (.neg (.mul (.var 0) (.mul (.var 2) (.var 2))))) (.var 3))
            (.mul (.add (.mul (.var 1) (.var 1)) (.neg (.mul (.var 0) (.mul (.var 2) (.var 2))))) (.var 3)))
      (by decide +kernel)
  rw [e, hu]; exact Shell.one_mul 1

/-- 8:D14 — the boost is orthogonal: `Λ(x, y)` preserves the coordinate form `x² − νt²` (the extension theme's
`boost_preserves` with `γ = A`, `b = B`). -/
theorem boost_orthogonal (ν x y u : Shell p) (hu : (x * x + -(ν * (y * y))) * u = 1) (t s : Shell p) :
    Q2 ν (boostT ν (boostOf ν x y u).re (boostOf ν x y u).im t s)
         (boostX ν (boostOf ν x y u).re (boostOf ν x y u).im t s) = Q2 ν t s :=
  boost_preserves (boost_entries_norm ν x y u hu) t s

/-- 8:D15 — the boost of the product is the product of the boosts: with `zz' = (xx' + νyy') + (xy' + yx')w` and
the inverse `uu'` of `δ(zz') = δ(z)δ(z')`, `Λ(zz') = Λ(z)Λ(z')` in the extension (two polynomial identities). -/
theorem boost_of_mul (ν x y u x' y' u' : Shell p) :
    boostOf ν (x * x' + ν * (y * y')) (x * y' + y * x') (u * u') = boostOf ν x y u * boostOf ν x' y' u' := by
  apply Ext.ext
  · show (((x * x' + ν * (y * y')) * (x * x' + ν * (y * y')) + ν * ((x * y' + y * x') * (x * y' + y * x'))) * (u * u')) =
      (x * x + ν * (y * y)) * u * ((x' * x' + ν * (y' * y')) * u') + ν * (-((x + x) * y) * u * (-((x' + x') * y') * u'))
    exact RE.sound (look [ν, x, y, u, x', y', u'])
      (.mul (.add (.mul (.add (.mul (.var 1) (.var 4)) (.mul (.var 0) (.mul (.var 2) (.var 5))))
                        (.add (.mul (.var 1) (.var 4)) (.mul (.var 0) (.mul (.var 2) (.var 5)))))
                  (.mul (.var 0) (.mul (.add (.mul (.var 1) (.var 5)) (.mul (.var 2) (.var 4)))
                                       (.add (.mul (.var 1) (.var 5)) (.mul (.var 2) (.var 4))))))
            (.mul (.var 3) (.var 6)))
      (.add (.mul (.mul (.add (.mul (.var 1) (.var 1)) (.mul (.var 0) (.mul (.var 2) (.var 2)))) (.var 3))
                  (.mul (.add (.mul (.var 4) (.var 4)) (.mul (.var 0) (.mul (.var 5) (.var 5)))) (.var 6)))
            (.mul (.var 0) (.mul (.mul (.neg (.mul (.add (.var 1) (.var 1)) (.var 2))) (.var 3))
                                 (.mul (.neg (.mul (.add (.var 4) (.var 4)) (.var 5))) (.var 6)))))
      (by decide +kernel)
  · show -(((x * x' + ν * (y * y')) + (x * x' + ν * (y * y'))) * (x * y' + y * x')) * (u * u') =
      (x * x + ν * (y * y)) * u * (-((x' + x') * y') * u') + -((x + x) * y) * u * ((x' * x' + ν * (y' * y')) * u')
    exact RE.sound (look [ν, x, y, u, x', y', u'])
      (.mul (.neg (.mul (.add (.add (.mul (.var 1) (.var 4)) (.mul (.var 0) (.mul (.var 2) (.var 5))))
                              (.add (.mul (.var 1) (.var 4)) (.mul (.var 0) (.mul (.var 2) (.var 5)))))
                        (.add (.mul (.var 1) (.var 5)) (.mul (.var 2) (.var 4)))))
            (.mul (.var 3) (.var 6)))
      (.add (.mul (.mul (.add (.mul (.var 1) (.var 1)) (.mul (.var 0) (.mul (.var 2) (.var 2)))) (.var 3))
                  (.mul (.neg (.mul (.add (.var 4) (.var 4)) (.var 5))) (.var 6)))
            (.mul (.mul (.neg (.mul (.add (.var 1) (.var 1)) (.var 2))) (.var 3))
                  (.mul (.add (.mul (.var 4) (.var 4)) (.mul (.var 0) (.mul (.var 5) (.var 5)))) (.var 6))))
      (by decide +kernel)

/-- 8:D15 — the identity: `Λ(1, 0) = 1` (with the inverse `1` of `δ = 1`). -/
theorem boost_one (ν : Shell p) : boostOf ν 1 0 1 = 1 := by
  apply Ext.ext
  · show (1 * 1 + ν * (0 * 0)) * 1 = 1
    rw [Shell.mul_one, Shell.mul_zero, Shell.mul_zero, Shell.add_zero]; exact Shell.one_mul 1
  · show -((1 + 1) * 0) * 1 = 0
    rw [Shell.mul_zero, Shell.neg_zero]; exact Shell.zero_mul 1

/-- 8:D15 — the inverse: `Λ(x, −y)` is the conjugate of `Λ(x, y)`, and a norm-one element times its conjugate is
`1` (`conj_inv_of_norm_one`), so `Λ(x, −y) = Λ(x, y)⁻¹`. -/
theorem boost_conj (ν x y u : Shell p) : boostOf ν x (-y) u = Ext.conj (boostOf ν x y u) := by
  apply Ext.ext
  · show (x * x + ν * (-y * -y)) * u = (x * x + ν * (y * y)) * u
    rw [Shell.neg_mul_neg]
  · show -((x + x) * -y) * u = -(-((x + x) * y) * u)
    rw [← Shell.mul_neg, Shell.neg_neg, ← Shell.neg_mul, Shell.neg_neg]

/-- 8:D15 — `Λ(x, y) Λ(x, −y) = 1`: the boosts form a group under the product of the extension, with the conjugate
as the inverse. -/
theorem boost_inv (ν x y u : Shell p) (hu : (x * x + -(ν * (y * y))) * u = 1) :
    boostOf ν x y u * boostOf ν x (-y) u = 1 := by
  rw [boost_conj]
  exact Ext.conj_inv_of_norm_one _ (boost_entries_norm ν x y u hu)

end boosts

/-! ## 8:F7 — the dispersion relation on the characters -/
section dispersion
variable {κ : Nat} {g : Shell p}

/-- 8:F7 — the dispersion relation: on the drive cycle, `χ_k(j) = g^{jk}` and the cycle Laplacian
`(Δχ)(j) = χ(j+1) + χ(j−1) − 2χ(j)` acts on `χ_k` as the scalar `g^k + g^{−k} − 2`: at the site `j + 1`,
`χ_k(j+2) = g^k χ_k(j+1)` and `χ_k(j) = y^k χ_k(j+1)` with `y = g⁻¹` (`drive_eigen`). -/
theorem dispersion {y : Shell p} (hy : g * y = 1) (j k : Nat) :
    g ^ ((j + 2) * k) + g ^ (j * k) + -(2 * g ^ ((j + 1) * k)) = (g ^ k + y ^ k + -2) * g ^ ((j + 1) * k) := by
  have h1 : g ^ ((j + 2) * k) = g ^ k * g ^ ((j + 1) * k) := by
    have e : (j + 2) * k = k + (j + 1) * k := by
      rw [show j + 2 = j + 1 + 1 from rfl, Nat.add_mul (j + 1) 1 k, Nat.one_mul, Nat.add_comm]
    rw [e, Shell.pow_add]
  rw [h1, ← drive_eigen hy j k, Shell.right_distrib, Shell.right_distrib, ← Shell.neg_mul]

end dispersion

/-! ## 8:C16 — the gauge `α ↦ −α` inverts the Cayley map -/
section gauge

/-- The scalar Cayley map `φ(λ) = (1 + λw)/(1 − λw)` with the inverse `u` of the norm `1 − νλ²` supplied:
`(1 + λw) · conj(1 − λw) · u`. The theme's `phi` is this with the searched inverse. -/
def phiU (ν lam u : Shell p) : Ext p ν := (⟨1, lam⟩ : Ext p ν) * Ext.conj ⟨1, -lam⟩ * Ext.ofShell u

/-- The gauge-flipped map `φ⁻(λ) = (1 − λw)/(1 + λw)` (the parameter `−α`), the same inverse: the norms of
`1 ± λw` agree. -/
def phiNegU (ν lam u : Shell p) : Ext p ν := (⟨1, -lam⟩ : Ext p ν) * Ext.conj ⟨1, lam⟩ * Ext.ofShell u

/-- 8:C16 — the orientation gauge inverts every value of the Cayley map: `φ⁻(λ) φ(λ) = 1` when `(1 − νλ²) u = 1`
(the product is `(N u)²` on the real line and `0` on the imaginary one, two polynomial identities). -/
theorem cayley_gauge (ν lam u : Shell p) (hu : (1 + -(ν * (lam * lam))) * u = 1) :
    phiNegU ν lam u * phiU ν lam u = 1 := by
  have h1 : phiU ν lam u = ⟨(1 * 1 + ν * (lam * lam)) * u + ν * ((1 * lam + lam * 1) * 0), (1 * 1 + ν * (lam * lam)) * 0 + (1 * lam + lam * 1) * u⟩ := by
    unfold phiU
    rw [show Ext.conj (⟨1, -lam⟩ : Ext p ν) = ⟨1, lam⟩ from Ext.ext rfl (Shell.neg_neg lam)]
    rfl
  have h2 : phiNegU ν lam u = ⟨(1 * 1 + ν * (-lam * -lam)) * u + ν * ((1 * -lam + -lam * 1) * 0), (1 * 1 + ν * (-lam * -lam)) * 0 + (1 * -lam + -lam * 1) * u⟩ := by
    unfold phiNegU; rfl
  rw [h2, h1]
  apply Ext.ext
  · show ((1 * 1 + ν * (-lam * -lam)) * u + ν * ((1 * -lam + -lam * 1) * 0)) * ((1 * 1 + ν * (lam * lam)) * u + ν * ((1 * lam + lam * 1) * 0)) + ν * (((1 * 1 + ν * (-lam * -lam)) * 0 + (1 * -lam + -lam * 1) * u) * ((1 * 1 + ν * (lam * lam)) * 0 + (1 * lam + lam * 1) * u)) = 1
    have e : ((1 * 1 + ν * (-lam * -lam)) * u + ν * ((1 * -lam + -lam * 1) * 0)) * ((1 * 1 + ν * (lam * lam)) * u + ν * ((1 * lam + lam * 1) * 0)) + ν * (((1 * 1 + ν * (-lam * -lam)) * 0 + (1 * -lam + -lam * 1) * u) * ((1 * 1 + ν * (lam * lam)) * 0 + (1 * lam + lam * 1) * u)) = ((1 + -(ν * (lam * lam))) * u) * ((1 + -(ν * (lam * lam))) * u) :=
      RE.sound (look [ν, lam, u])
        (.add (.mul (.add (.mul (.add (.mul .one .one) (.mul (.var 0) (.mul (.neg (.var 1)) (.neg (.var 1))))) (.var 2)) (.mul (.var 0) (.mul (.add (.mul .one (.neg (.var 1))) (.mul (.neg (.var 1)) .one)) .zero))) (.add (.mul (.add (.mul .one .one) (.mul (.var 0) (.mul (.var 1) (.var 1)))) (.var 2)) (.mul (.var 0) (.mul (.add (.mul .one (.var 1)) (.mul (.var 1) .one)) .zero)))) (.mul (.var 0) (.mul (.add (.mul (.add (.mul .one .one) (.mul (.var 0) (.mul (.neg (.var 1)) (.neg (.var 1))))) .zero) (.mul (.add (.mul .one (.neg (.var 1))) (.mul (.neg (.var 1)) .one)) (.var 2))) (.add (.mul (.add (.mul .one .one) (.mul (.var 0) (.mul (.var 1) (.var 1)))) .zero) (.mul (.add (.mul .one (.var 1)) (.mul (.var 1) .one)) (.var 2))))))
        (.mul (.mul (.add .one (.neg (.mul (.var 0) (.mul (.var 1) (.var 1))))) (.var 2)) (.mul (.add .one (.neg (.mul (.var 0) (.mul (.var 1) (.var 1))))) (.var 2)))
        (by decide +kernel)
    rw [e, hu]; exact Shell.one_mul 1
  · show ((1 * 1 + ν * (-lam * -lam)) * u + ν * ((1 * -lam + -lam * 1) * 0)) * ((1 * 1 + ν * (lam * lam)) * 0 + (1 * lam + lam * 1) * u) + ((1 * 1 + ν * (-lam * -lam)) * 0 + (1 * -lam + -lam * 1) * u) * ((1 * 1 + ν * (lam * lam)) * u + ν * ((1 * lam + lam * 1) * 0)) = 0
    exact RE.sound (look [ν, lam, u])
      (.add (.mul (.add (.mul (.add (.mul .one .one) (.mul (.var 0) (.mul (.neg (.var 1)) (.neg (.var 1))))) (.var 2)) (.mul (.var 0) (.mul (.add (.mul .one (.neg (.var 1))) (.mul (.neg (.var 1)) .one)) .zero))) (.add (.mul (.add (.mul .one .one) (.mul (.var 0) (.mul (.var 1) (.var 1)))) .zero) (.mul (.add (.mul .one (.var 1)) (.mul (.var 1) .one)) (.var 2)))) (.mul (.add (.mul (.add (.mul .one .one) (.mul (.var 0) (.mul (.neg (.var 1)) (.neg (.var 1))))) .zero) (.mul (.add (.mul .one (.neg (.var 1))) (.mul (.neg (.var 1)) .one)) (.var 2))) (.add (.mul (.add (.mul .one .one) (.mul (.var 0) (.mul (.var 1) (.var 1)))) (.var 2)) (.mul (.var 0) (.mul (.add (.mul .one (.var 1)) (.mul (.var 1) .one)) .zero)))))
      .zero
      (by decide +kernel)

end gauge

end FRC.Dirac.Plane
