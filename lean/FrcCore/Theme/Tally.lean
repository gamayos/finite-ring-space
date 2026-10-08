/-!
# FrcCore.Theme.Tally — the pair tally on the `Q₄` core (the extension theme; 00:C11, the push of 8 October 2026)

A file of its own, importing nothing, so that the certificates whose closures reach the extension theme (20-rh) stay
within the size budget of decision Q03. Its python side is `frc/extension.py` (`q4_kernel`, `q4_tally`, …).

The stationary core-valued `Q₄` sector: kernels `K : Q₄ → ℤ[i]` with `K(−d) = conj K(d)` (two-way), tally-valued on
the sector's states. The admissible kernels are the tally combinations `K = Σ_r c_r η_r` of the four characters
`η_r(d) = i^{rd}`; the pair tally `F(K, ψ) = Σ_{u,v} K(v − u) ψ_u conj ψ_v` on a pure winding `ψ_k(u) = i^{ku}` reads the
coefficient, `F(K_c, ψ_k) = 16 c_k`, so the tallies are fixed by the pure windings; Fourier inversion recovers every
coefficient; a single-channel response (channel-selectivity) is a scaled unit coefficient vector, the Born ray; the
core DFT has determinant `−16i`; and a linear functional leaves the tally cone on `i ψ₀`. The box `−1 ≤ c_r ≤ 3` of coefficients (negative ones included) is exhausted by the kernel for the fixing formula and
the tally criterion, the cube `0 ≤ c_r ≤ 3` for the two-way, inversion and selectivity clauses, as the paper's witness
exhausts it; the kernels, states and bilinear form the paper's Lemma degree and its witness U3, U5, U6a name are
instances decided by the kernel. Gaussian integers as pairs. -/

namespace FRC.Extension.Tally

/-- A Gaussian integer `re + im·i`. -/
structure GI where
  re : Int
  im : Int
deriving DecidableEq

namespace GI
def add (x y : GI) : GI := ⟨x.re + y.re, x.im + y.im⟩
def mul (x y : GI) : GI := ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩
def conj (x : GI) : GI := ⟨x.re, -x.im⟩
def smul (c : Int) (x : GI) : GI := ⟨c * x.re, c * x.im⟩
instance : Add GI := ⟨add⟩
instance : Mul GI := ⟨mul⟩
def zero : GI := ⟨0, 0⟩
def i : GI := ⟨0, 1⟩
/-- `i^n`. -/
def ipow (n : Nat) : GI := match n % 4 with
  | 0 => ⟨1, 0⟩ | 1 => ⟨0, 1⟩ | 2 => ⟨-1, 0⟩ | _ => ⟨0, -1⟩
/-- A Gaussian integer is a tally when it is a nonnegative integer. -/
def tally (x : GI) : Prop := x.im = 0 ∧ 0 ≤ x.re
instance (x : GI) : Decidable (tally x) := inferInstanceAs (Decidable (_ ∧ _))
end GI

open GI

/-- The sum of a function over `Q₄`. -/
def sum4 (f : Nat → GI) : GI := f 0 + f 1 + f 2 + f 3
/-- The character `η_r(d) = i^{rd}`. -/
def eta (r d : Nat) : GI := ipow (r * d)
/-- The kernel `K_c = Σ_r c_r η_r` with the coefficients `c = (c₀, c₁, c₂, c₃)`. -/
def kernel (c₀ c₁ c₂ c₃ : Int) (d : Nat) : GI :=
  smul c₀ (eta 0 d) + smul c₁ (eta 1 d) + smul c₂ (eta 2 d) + smul c₃ (eta 3 d)
/-- The pure winding `ψ_k(u) = i^{ku}` restricted to the fibre. -/
def psi (k u : Nat) : GI := ipow (k * u)
/-- The pair tally `F(K, ψ) = Σ_{u,v} K(v − u) ψ_u conj ψ_v`, the offset read modulo four. -/
def F (K : Nat → GI) (ψ : Nat → GI) : GI := sum4 fun u => sum4 fun v => K ((v + 4 - u) % 4) * ψ u * conj (ψ v)
/-- The coefficient `c_k` of the cube point `(c₀, c₁, c₂, c₃)` at the channel `k`. -/
def coeff (c₀ c₁ c₂ c₃ : Int) (k : Nat) : Int := match k % 4 with
  | 0 => c₀ | 1 => c₁ | 2 => c₂ | _ => c₃
/-- Fourier inversion: `Σ_d K(d) i^{−rd}`. -/
def inversion (K : Nat → GI) (r : Nat) : GI := sum4 fun d => K d * ipow ((4 - r % 4) * d)
/-- The number of channels `k < 4` on which the kernel responds. -/
def responses (K : Nat → GI) : Nat :=
  (if F K (psi 0) = zero then 0 else 1) + (if F K (psi 1) = zero then 0 else 1) +
  (if F K (psi 2) = zero then 0 else 1) + (if F K (psi 3) = zero then 0 else 1)
/-- The number of nonzero coefficients. -/
def support (c₀ c₁ c₂ c₃ : Int) : Nat :=
  (if c₀ = 0 then 0 else 1) + (if c₁ = 0 then 0 else 1) + (if c₂ = 0 then 0 else 1) + (if c₃ = 0 then 0 else 1)

set_option maxRecDepth 4000 in
/-- 00:C11 (i) — the pure windings fix the tallies on the box `−1 ≤ c_r ≤ 3` (the naturals `a, b, c, d < 5`, cast to
`ℤ` and shifted by one), which contains negative coefficients: `F(K_c, ψ_k) = 16 c_k` for every kernel of the box and
every channel `k`. -/
theorem winding_fixing : ∀ a : Nat, a < 5 → ∀ b : Nat, b < 5 → ∀ c : Nat, c < 5 → ∀ d : Nat, d < 5 →
    ∀ k : Nat, k < 4 →
    F (kernel (Int.ofNat a - 1) (Int.ofNat b - 1) (Int.ofNat c - 1) (Int.ofNat d - 1)) (psi k) =
      ⟨16 * coeff (Int.ofNat a - 1) (Int.ofNat b - 1) (Int.ofNat c - 1) (Int.ofNat d - 1) k, 0⟩ := by decide +kernel

set_option maxRecDepth 4000 in
/-- 00:C11 (i′) — the tally criterion on the box: the pair tally of `K_c` on `ψ_k` is a tally (a nonnegative integer)
iff `0 ≤ c_k` — the cone's two halves: every tally combination is tally-valued on the windings, and a kernel with a
negative coefficient is excluded by its own winding. -/
theorem tally_criterion : ∀ a : Nat, a < 5 → ∀ b : Nat, b < 5 → ∀ c : Nat, c < 5 → ∀ d : Nat, d < 5 →
    ∀ k : Nat, k < 4 →
    (tally (F (kernel (Int.ofNat a - 1) (Int.ofNat b - 1) (Int.ofNat c - 1) (Int.ofNat d - 1)) (psi k)) ↔
      (0 : Int) ≤ coeff (Int.ofNat a - 1) (Int.ofNat b - 1) (Int.ofNat c - 1) (Int.ofNat d - 1) k) := by decide +kernel

/-- 00:C11 (ii) — every kernel of the cube is two-way, `K(−d) = conj K(d)`, and tally-valued on the pure windings. -/
theorem two_way : ∀ a : Nat, a < 4 → ∀ b : Nat, b < 4 → ∀ c : Nat, c < 4 → ∀ d : Nat, d < 4 →
    (∀ e, e < 4 → kernel (Int.ofNat a) (Int.ofNat b) (Int.ofNat c) (Int.ofNat d) ((4 - e) % 4) = conj (kernel (Int.ofNat a) (Int.ofNat b) (Int.ofNat c) (Int.ofNat d) e)) ∧
    (∀ k, k < 4 → tally (F (kernel (Int.ofNat a) (Int.ofNat b) (Int.ofNat c) (Int.ofNat d)) (psi k))) := by decide

/-- 00:C11 (iii) — Fourier inversion recovers every coefficient exactly: `Σ_d K(d) i^{−rd} = 4 c_r`. -/
theorem fourier_inversion : ∀ a : Nat, a < 4 → ∀ b : Nat, b < 4 → ∀ c : Nat, c < 4 → ∀ d : Nat, d < 4 →
    ∀ r, r < 4 → inversion (kernel (Int.ofNat a) (Int.ofNat b) (Int.ofNat c) (Int.ofNat d)) r = ⟨4 * coeff (Int.ofNat a) (Int.ofNat b) (Int.ofNat c) (Int.ofNat d) r, 0⟩ := by decide

/-- 00:C11 (iv) — channel-selectivity picks the ray: a kernel of the cube responds on exactly one channel iff its
coefficient vector is a scaled unit vector. -/
theorem channel_selectivity : ∀ a : Nat, a < 4 → ∀ b : Nat, b < 4 → ∀ c : Nat, c < 4 → ∀ d : Nat, d < 4 →
    (responses (kernel (Int.ofNat a) (Int.ofNat b) (Int.ofNat c) (Int.ofNat d)) = 1 ↔ support (Int.ofNat a) (Int.ofNat b) (Int.ofNat c) (Int.ofNat d) = 1) := by decide

/-- 00:C11 (v) — the core DFT matrix `(i^{ru})` is invertible: its determinant is `−16i`. -/
theorem dft_det :
    let M := fun r u => ipow (r * u)
    let d2 := fun a b c d : GI => a * d + smul (-1) (b * c)
    let e := fun r => M r
    let det3 := fun (f g h : Nat → GI) => f 1 * d2 (g 2) (g 3) (h 2) (h 3) + smul (-1) (f 2 * d2 (g 1) (g 3) (h 1) (h 3)) + f 3 * d2 (g 1) (g 2) (h 1) (h 2)
    e 0 0 * det3 (e 1) (e 2) (e 3) + smul (-1) (e 1 0 * det3 (e 0) (e 2) (e 3)) +
      e 2 0 * det3 (e 0) (e 1) (e 3) + smul (-1) (e 3 0 * det3 (e 0) (e 1) (e 2)) = ⟨0, -16⟩ := by decide

/-- The unconjugated bilinear form `B(K, ψ) = Σ_{u,v} K(v − u) ψ_u ψ_v` of the same kernel. -/
def B (K : Nat → GI) (ψ : Nat → GI) : GI := sum4 fun u => sum4 fun v => K ((v + 4 - u) % 4) * ψ u * ψ v
/-- The fibre norm `K = [d = 0]`. -/
def fibreNorm (d : Nat) : GI := if d % 4 = 0 then ⟨1, 0⟩ else ⟨0, 0⟩
/-- A two-way kernel outside the box, `5η₁ − 2η₂ + η₃ = (4, 2 + 4i, −8, 2 − 4i)`. -/
def kout (d : Nat) : GI := match d % 4 with
  | 0 => ⟨4, 0⟩ | 1 => ⟨2, 4⟩ | 2 => ⟨-8, 0⟩ | _ => ⟨2, -4⟩
/-- The Gaussian-lattice state `(1 + i) e₀`. -/
def psiA (u : Nat) : GI := if u = 0 then ⟨1, 1⟩ else ⟨0, 0⟩
/-- The Gaussian-lattice state `e₀ + i e₁`. -/
def psiB (u : Nat) : GI := if u = 0 then ⟨1, 0⟩ else if u = 1 then ⟨0, 1⟩ else ⟨0, 0⟩

/-- 00:C11 (vi) — the witnesses of the cone's boundary (22-quantum's U3, U5, U6a): the negative coefficient
`c = (1, −1, 1, 0)` is excluded by its own winding, `F(K_c, ψ₁) = −16`; the two-way kernel `5η₁ − 2η₂ + η₃` outside the
box is excluded on `ψ₂` and Fourier inversion recovers `4c = (0, 20, −8, 4)`; the fibre norm `[d = 0]` is two-way,
responds `(4, 4, 4, 4)` with `4c_r = 1` on every channel (no tally combination) and fails channel-selectivity; the
single character `η₁` responds `16` on its channel and `0` elsewhere, so `η₁/16` reads `1` (c = 1/16, no tally). -/
theorem cone_boundary :
    F (kernel 1 (-1) 1 0) (psi 1) = ⟨-16, 0⟩ ∧ ¬ tally (F (kernel 1 (-1) 1 0) (psi 1)) ∧
    (∀ e, e < 4 → kout ((4 - e) % 4) = conj (kout e)) ∧ F kout (psi 2) = ⟨-32, 0⟩ ∧ ¬ tally (F kout (psi 2)) ∧
    inversion kout 0 = ⟨0, 0⟩ ∧ inversion kout 1 = ⟨20, 0⟩ ∧ inversion kout 2 = ⟨-8, 0⟩ ∧ inversion kout 3 = ⟨4, 0⟩ ∧
    (∀ d, d < 4 → smul 4 (kout d) = sum4 (fun r => inversion kout r * ipow (r * d))) ∧
    (∀ e, e < 4 → fibreNorm ((4 - e) % 4) = conj (fibreNorm e)) ∧ (∀ k, k < 4 → F fibreNorm (psi k) = ⟨4, 0⟩) ∧
    responses fibreNorm = 4 ∧ (∀ r, r < 4 → inversion fibreNorm r = ⟨1, 0⟩) ∧
    F (kernel 0 1 0 0) (psi 1) = ⟨16, 0⟩ ∧ F (kernel 0 1 0 0) (psi 0) = ⟨0, 0⟩ ∧ responses (kernel 0 1 0 0) = 1 := by decide

/-- 00:C11 (vii) — the minimal degree is forced (22-quantum Lemma degree): a linear functional constant on the orbit
vanishes on every nontrivial winding (the complete character sums), and on the trivial winding `F(i ψ₀) = i F(ψ₀)`
leaves the tally cone for every nonzero multiplier `c ≤ 4`; and the unconjugated bilinear form leaves the tally line
on Gaussian-lattice states where the conjugated form of the same kernel stays on it: `B(fn, (1 + i)e₀) = 2i` against
`F = 2`, `B([d = 1], e₀ + i e₁) = i`, and `B(K_(1,1,0,0), (1 + i)e₀) = 4i` against `F = 4`. -/
theorem linear_exclusion :
    (∀ k, k < 4 → 0 < k → sum4 (fun u => ipow (k * u)) = zero) ∧
    (∀ c, c < 5 → 0 < c → ¬ tally (i * ⟨4 * Int.ofNat c, 0⟩)) ∧
    B fibreNorm psiA = ⟨0, 2⟩ ∧ ¬ tally (B fibreNorm psiA) ∧ F fibreNorm psiA = ⟨2, 0⟩ ∧ tally (F fibreNorm psiA) ∧
    B (fun d => if d % 4 = 1 then ⟨1, 0⟩ else ⟨0, 0⟩) psiB = ⟨0, 1⟩ ∧
    ¬ tally (B (fun d => if d % 4 = 1 then ⟨1, 0⟩ else ⟨0, 0⟩) psiB) ∧
    B (kernel 1 1 0 0) psiA = ⟨0, 4⟩ ∧ ¬ tally (B (kernel 1 1 0 0) psiA) ∧ F (kernel 1 1 0 0) psiA = ⟨4, 0⟩ := by decide

end FRC.Extension.Tally
