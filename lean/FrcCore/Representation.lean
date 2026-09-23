import FrcCore.Nat
import FrcCore.Shell
import FrcCore.Frame
import FrcCore.Sum

/-!
# 4-rep — universal latent representation: the ledger predicates with no axioms

Rows of the predicate ledger of *Universal Latent Representation in Finite Ring Continuum* (Entropy 2026, 28, 40;
tree `4-deepfrc-20251217`).  The representation predicates are set theory over arbitrary types: a bijection is carried as
data (`Bij`: the map, its inverse, the two inverse laws), adequacy as a bijection through the observation map, and
every statement is pointwise, so neither function extensionality nor choice is used.  The Gödel row is decided on
two primes by induction, the hypersphere row in the shell's own arithmetic (the character chart has constant
conjugate norm).  Every declaration prints "does not depend on any axioms".
-/

namespace FRC.Representation

/-- A bijection as data: the map, an inverse, and the two inverse laws. -/
structure Bij (Z W : Type) where
  toFun : Z → W
  inv : W → Z
  left : ∀ z, inv (toFun z) = z
  right : ∀ w, toFun (inv w) = w

/-- 4:B3 (Definition 2) — `E : X → W` is adequate for the observation map `g : Z → X` when `E ∘ g` is a
bijection `φ : Z → W` (carried as data), `E (g z) = φ z`. -/
structure Adequate {Z X W : Type} (g : Z → X) (E : X → W) where
  φ : Bij Z W
  eq : ∀ z, E (g z) = φ.toFun z

variable {Z X W W₁ W₂ U : Type}

/-- 4:B4 — adequacy makes the observation map injective on the latent domain: `g z₁ = g z₂ → z₁ = z₂`. -/
theorem adequate_inj {g : Z → X} {E : X → W} (A : Adequate g E) {z₁ z₂ : Z} (h : g z₁ = g z₂) : z₁ = z₂ := by
  have e : A.φ.toFun z₁ = A.φ.toFun z₂ := by rw [← A.eq, ← A.eq, h]
  rw [← A.φ.left z₁, ← A.φ.left z₂, e]

/-- 4:B5 (Lemma 2) — the transition `ψ = φ₂ ∘ φ₁⁻¹` between two adequate representations of one observation map:
`E₂ (g z) = ψ (E₁ (g z))` for every latent state. -/
def transition {g : Z → X} {E₁ : X → W₁} {E₂ : X → W₂} (A₁ : Adequate g E₁) (A₂ : Adequate g E₂) : W₁ → W₂ :=
  fun w => A₂.φ.toFun (A₁.φ.inv w)

/-- 4:B5 — `E₂ ∘ g = ψ ∘ E₁ ∘ g` pointwise. -/
theorem transition_spec {g : Z → X} {E₁ : X → W₁} {E₂ : X → W₂} (A₁ : Adequate g E₁) (A₂ : Adequate g E₂) (z : Z) :
    E₂ (g z) = transition A₁ A₂ (E₁ (g z)) := by
  unfold transition; rw [A₁.eq, A₁.φ.left, A₂.eq]

/-- 4:B5 — the transition is a bijection `W₁ → W₂`: its inverse is `φ₁ ∘ φ₂⁻¹`. -/
def transitionBij {g : Z → X} {E₁ : X → W₁} {E₂ : X → W₂} (A₁ : Adequate g E₁) (A₂ : Adequate g E₂) : Bij W₁ W₂ where
  toFun := transition A₁ A₂
  inv := fun w => A₁.φ.toFun (A₂.φ.inv w)
  left := fun w => by show A₁.φ.toFun (A₂.φ.inv (A₂.φ.toFun (A₁.φ.inv w))) = w; rw [A₂.φ.left, A₁.φ.right]
  right := fun w => by show A₂.φ.toFun (A₁.φ.inv (A₁.φ.toFun (A₂.φ.inv w))) = w; rw [A₁.φ.left, A₂.φ.right]

/-- 4:B5 (the uniqueness clause) — any `ψ'` with `E₂ (g z) = ψ' (E₁ (g z))` for every `z` agrees with the
transition on all of `W₁`, because `E₁ ∘ g` is onto `W₁`. -/
theorem transition_unique {g : Z → X} {E₁ : X → W₁} {E₂ : X → W₂} (A₁ : Adequate g E₁) (A₂ : Adequate g E₂)
    (ψ' : W₁ → W₂) (h : ∀ z, E₂ (g z) = ψ' (E₁ (g z))) (w : W₁) : ψ' w = transition A₁ A₂ w := by
  rw [← A₁.φ.right w, ← A₁.eq, ← h]; exact transition_spec A₁ A₂ _

/-- 4:B6, 4:C2 (the canonical embedding into the shell) — with `incl : Z → U` the inclusion of the latent domain,
`ι := incl ∘ φ⁻¹ : W → U` is injective when `incl` is, and `ι (E (g z)) = incl z`: the chart `ψ = ι ∘ φ` is the
inclusion itself. -/
def iota {g : Z → X} {E : X → W} (A : Adequate g E) (incl : Z → U) : W → U := fun w => incl (A.φ.inv w)

/-- 4:B6 — `ι` is injective when the inclusion is. -/
theorem iota_inj {g : Z → X} {E : X → W} (A : Adequate g E) {incl : Z → U}
    (hincl : ∀ z₁ z₂, incl z₁ = incl z₂ → z₁ = z₂) {w₁ w₂ : W} (h : iota A incl w₁ = iota A incl w₂) : w₁ = w₂ := by
  rw [← A.φ.right w₁, ← A.φ.right w₂, hincl _ _ h]

/-- 4:C2 (Theorem 1 (iii)) — in the canonical parametrisation every chart is the inclusion: `ι (E (g z)) = incl z`. -/
theorem canonical_chart {g : Z → X} {E : X → W} (A : Adequate g E) (incl : Z → U) (z : Z) :
    iota A incl (E (g z)) = incl z := by
  unfold iota; rw [A.eq, A.φ.left]

/-- 4:C1 (Theorem 1 (i)) — the chart `ψ = ι ∘ E ∘ g` is injective for any injective `ι`. -/
theorem chart_inj {g : Z → X} {E : X → W} (A : Adequate g E) {ι : W → U} (hι : ∀ w₁ w₂, ι w₁ = ι w₂ → w₁ = w₂)
    {z₁ z₂ : Z} (h : ι (E (g z₁)) = ι (E (g z₂))) : z₁ = z₂ := by
  have e : A.φ.toFun z₁ = A.φ.toFun z₂ := by rw [← A.eq, ← A.eq]; exact hι _ _ h
  rw [← A.φ.left z₁, ← A.φ.left z₂, e]

/-- 4:C1 (Theorem 1 (ii)) — the transition `Ψ_{m→n} = ψ_n ∘ ψ_m⁻¹` is well defined and bijective between the images:
two latent states have the same `ψ_m`-image exactly when they have the same `ψ_n`-image, so the pairs
`(ψ_m z, ψ_n z)` are the graph of a bijection `ψ_m(Z) → ψ_n(Z)`. -/
theorem transition_graph {ψm ψn : Z → U} (hm : ∀ z₁ z₂, ψm z₁ = ψm z₂ → z₁ = z₂)
    (hn : ∀ z₁ z₂, ψn z₁ = ψn z₂ → z₁ = z₂) (z₁ z₂ : Z) : ψm z₁ = ψm z₂ ↔ ψn z₁ = ψn z₂ :=
  ⟨fun h => by rw [hm _ _ h], fun h => by rw [hn _ _ h]⟩

/-- 4:C3 (Corollary 1) — the latent lift `L := φ⁻¹ ∘ E : X → Z`. -/
def lift {g : Z → X} {E : X → W} (A : Adequate g E) : X → Z := fun x => A.φ.inv (E x)

/-- 4:C3 — the lift recovers the latent state, `L (g z) = z`. -/
theorem lift_g {g : Z → X} {E : X → W} (A : Adequate g E) (z : Z) : lift A (g z) = z := by
  unfold lift; rw [A.eq, A.φ.left]

/-- 4:C3 — `L x` is the unique `z` with `E x = φ z`. -/
theorem lift_unique {g : Z → X} {E : X → W} (A : Adequate g E) (x : X) (z : Z) :
    E x = A.φ.toFun z ↔ lift A x = z := by
  constructor
  · intro h; unfold lift; rw [h, A.φ.left]
  · intro h; unfold lift at h; rw [← h, A.φ.right]

/-- 4:C4 (Corollary 2) — cross-modal consistency: the lifts of two modalities' observations of one latent state
agree, `L_m (g_m z) = L_n (g_n z)`, hence so do their canonical charts `ψ ∘ L_m ∘ g_m = ψ = ψ ∘ L_n ∘ g_n`. -/
theorem consistency {Xm Xn Wm Wn : Type} {gm : Z → Xm} {gn : Z → Xn} {Em : Xm → Wm} {En : Xn → Wn}
    (Am : Adequate gm Em) (An : Adequate gn En) (incl : Z → U) (z : Z) :
    lift Am (gm z) = lift An (gn z) ∧ incl (lift Am (gm z)) = incl z := by
  rw [lift_g, lift_g]; exact ⟨rfl, rfl⟩

/-! ### 4:E3 — Gödel collapse into one residue, the two-prime instance -/

theorem three_pow_mod_two : ∀ b : Nat, 3 ^ b % 2 = 1
  | 0 => rfl
  | b + 1 => by
      rw [Nat.pow_succ, FRC.Nat.mul_mod _ _ 2 (Nat.zero_lt_succ 1), three_pow_mod_two b]

theorem two_mul_mod_two (x : Nat) : 2 * x % 2 = 0 := by
  rw [FRC.Nat.mul_mod_left' 2 x 2 (Nat.zero_lt_succ 1)]
  show 0 * x % 2 = 0
  rw [Nat.zero_mul]

theorem three_pow_inj : ∀ b d : Nat, 3 ^ b = 3 ^ d → b = d
  | 0, 0, _ => rfl
  | 0, d + 1, h => by
      have h1 : 1 * 3 ≤ 3 ^ d * 3 := Nat.mul_le_mul_right 3 (Nat.pow_pos (Nat.zero_lt_succ 2))
      have h' : 1 = 3 ^ d * 3 := h
      rw [← h'] at h1
      exact absurd h1 (by decide)
  | b + 1, 0, h => by
      have h1 : 1 * 3 ≤ 3 ^ b * 3 := Nat.mul_le_mul_right 3 (Nat.pow_pos (Nat.zero_lt_succ 2))
      have h' : 3 ^ b * 3 = 1 := h
      rw [h'] at h1
      exact absurd h1 (by decide)
  | b + 1, d + 1, h =>
      congrArg Nat.succ (three_pow_inj b d (Nat.eq_of_mul_eq_mul_right (Nat.zero_lt_succ 2) h))

/-- 4:E3 (Gödel encoding, two primes) — `2^a 3^b = 2^c 3^d` forces `a = c` and `b = d`: the code is injective, by
parity and cancellation; the general case over `d` distinct primes is `FrcLedger.Representation.godel_injective`. -/
theorem godel2_inj : ∀ a c b d : Nat, 2 ^ a * 3 ^ b = 2 ^ c * 3 ^ d → a = c ∧ b = d
  | 0, 0, b, d, h => ⟨rfl, three_pow_inj b d (by rw [Nat.pow_zero, Nat.one_mul, Nat.one_mul] at h; exact h)⟩
  | 0, c + 1, b, d, h => by
      have hl : 2 ^ 0 * 3 ^ b % 2 = 1 := by rw [Nat.pow_zero, Nat.one_mul]; exact three_pow_mod_two b
      have hr : 2 ^ (c + 1) * 3 ^ d % 2 = 0 := by
        rw [Nat.pow_succ, FRC.Nat.mul_assoc, FRC.Nat.mul_left_comm]; exact two_mul_mod_two _
      rw [h] at hl; rw [hl] at hr; exact absurd hr (by decide)
  | a + 1, 0, b, d, h => by
      have hr : 2 ^ 0 * 3 ^ d % 2 = 1 := by rw [Nat.pow_zero, Nat.one_mul]; exact three_pow_mod_two d
      have hl : 2 ^ (a + 1) * 3 ^ b % 2 = 0 := by
        rw [Nat.pow_succ, FRC.Nat.mul_assoc, FRC.Nat.mul_left_comm]; exact two_mul_mod_two _
      rw [h] at hl; rw [hl] at hr; exact absurd hr (by decide)
  | a + 1, c + 1, b, d, h => by
      have h' : 2 * (2 ^ a * 3 ^ b) = 2 * (2 ^ c * 3 ^ d) := by
        rw [← FRC.Nat.mul_left_comm, ← FRC.Nat.mul_assoc, ← Nat.pow_succ, h, Nat.pow_succ, FRC.Nat.mul_assoc,
          FRC.Nat.mul_left_comm]
      have ih := godel2_inj a c b d (Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_succ 1) h')
      exact ⟨congrArg Nat.succ ih.1, ih.2⟩

/-- 4:E3 (the reduction into the shell) — an injective integer code with values below `q` stays injective
modulo `q`: `f a % q = f b % q` forces `f a = f b`. -/
theorem mod_injective {α : Type} (f : α → Nat) (q : Nat) (hq : ∀ a, f a < q) {a b : α}
    (h : f a % q = f b % q) : f a = f b := by
  rw [FRC.Nat.mod_eq_of_lt (hq a), FRC.Nat.mod_eq_of_lt (hq b)] at h; exact h

/-! ### 4:E1 — the hypersphere in the shell's own arithmetic -/

namespace Shell

open FRC.Shell

variable {p : Nat} [Pos p]

/-- 4:E1 — the character chart of the shell, `z ↦ (g^{kz})_{k}`: the finite shadow of the Fourier embedding
`z ↦ (cos 2πkz/p, sin 2πkz/p)_k`. -/
def charChart (g : Shell p) (z k : Nat) : Shell p := g ^ (k * z)

/-- 4:E1 (equivariance) — translation by `a` multiplies coordinate `k` by `g^{ka}`: the shell's translations act on
the chart coordinatewise, as the rotations act on the Fourier embedding. -/
theorem charChart_shift (g : Shell p) (z a k : Nat) : charChart g (z + a) k = g ^ (k * a) * charChart g z k := by
  unfold charChart; rw [Nat.mul_add, pow_add, mul_comm]

/-- 4:E1 (constant norm) — the conjugate norm `Σ_{k<n} g^{kz} g^{k(n−z)}` of the chart equals `n = p − 1` for every
`z ≤ n`: every point of the chart lies on one sphere, exactly. -/
theorem charChart_norm {κ : Nat} {g : Shell p} (F : Frame p κ g) (z : Nat) (hz : z ≤ p - 1) :
    sumRange (fun k => charChart g z k * charChart g (p - 1 - z) k) (p - 1) = ofNat (p - 1) := by
  have e : ∀ k, k < p - 1 → charChart g z k * charChart g (p - 1 - z) k = (fun _ => (1 : Shell p)) k := by
    intro k _
    show g ^ (k * z) * g ^ (k * (p - 1 - z)) = 1
    rw [← pow_add, ← Nat.mul_add, FRC.Nat.add_sub_of_le hz, Nat.mul_comm, pow_mul, F.pow_n, one_pow]
  rw [sum_congr (p - 1) e, sum_const, mul_one]

end Shell

end FRC.Representation
