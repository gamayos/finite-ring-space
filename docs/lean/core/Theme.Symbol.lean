import FrcCore.Ring
import FrcCore.Series

/-!
# FrcCore.Theme.Symbol — the symbol lemmas of the curvature-square uniqueness (the gravity theme, task LM40)

The first step of the master's E1 (p00052): at a fixed symbol `k`, the gauge-invariant quadratic forms of the
relevant (two-derivative) order form one line, for the vector field and for the symmetric tensor field. The symbol
`k`, the fields and the gauge parameters are vectors `Nat → Shell p` in `n` dimensions. The metric is diagonal,
`η : Nat → Shell p`, so `u·v = Σ_{μ<n} η_μ u_μ v_μ` (`dot`) covers the Euclidean and the Lorentzian signature.
Nothing is assumed of the modulus `p` beyond `Pos p`, so the identities hold on every shell.

* Spin 1. The form `a₁ k² A·A + a₂ (k·A)²` (`vecForm`) changes under the gauge shift `A ↦ A + z k` (`shift`) by
  `(a₁ + a₂) k² (2z (k·A) + z² k²)`, a polynomial identity in `z` (`vec_shift`). So `a₁ + a₂ = 0`, the symbol of
  `F²`, is invariant at every symbol (`vec_invariant`). When `k²` is a unit the converse holds at that symbol
  (`vec_iff_unit`). A null symbol, `k² = 0`, leaves every form invariant (`vec_null`). Over all symbols the invariant
  forms are exactly the line `a₁ + a₂ = 0` once one metric entry is a unit (`maxwell_unique`).
* Spin 2. The four scalars of a symmetric `h` are `k² ⟨h, h⟩`, `(k·h)·(k·h)`, `(k·h·k) tr h` and `k² (tr h)²`, the
  symbols of `∂h ∂h`, `∂·h ∂·h`, `∂·h ∂ tr h` and `∂ tr h ∂ tr h` (`tensForm`). Under `h_μν ↦ h_μν + k_μ ξ_ν + k_ν ξ_μ`
  (`gauge`) the combination changes by three gauge structures with coefficients `2a₁ + a₂`, `a₂ + a₃` and
  `a₃ + 2a₄` (`tens_shift`). The Fierz–Pauli line `(−1, 2, −2, 1)` is invariant on every shell
  (`fierz_pauli_invariant`). When `2` and two metric entries are units and `n ≥ 2`, it is the only invariant line
  (`fierz_pauli_unique`). In characteristic 2 the uniqueness fails: `k² ⟨h, h⟩` alone is invariant there
  (`char_two_not_unique`).

The ring identities are decided by the core's normaliser (`RE.sound`, a kernel computation). The sums are handled by
`sumRange` and its linearity. No axioms.
-/

namespace FRC.Symbol

open FRC.Shell FRC.Shell.Frame

variable {p : Nat} [Pos p]

/-! ## Sums -/

/-- Double sums commute: `Σ_{i<n} Σ_{j<m} f i j = Σ_{j<m} Σ_{i<n} f i j`. -/
theorem sum_swap (f : Nat → Nat → Shell p) (m : Nat) : ∀ n,
    sumRange (fun i => sumRange (fun j => f i j) m) n = sumRange (fun j => sumRange (fun i => f i j) n) m
  | 0 => (sum_zero m (fun _ _ => rfl)).symm
  | n + 1 => by
    rw [sumRange_succ, sum_swap f m n, ← sum_add]
    rfl

theorem lin2_zero (c : Shell p) : 0 = 0 + 0 * c :=
  RE.sound (look [c])
    .zero
    (.add .zero (.mul .zero (.var 0))) (by decide +kernel)

theorem lin2_step (S T a b c : Shell p) : S + T * c + (a + b * c) = S + a + (T + b) * c :=
  RE.sound (look [S, T, a, b, c])
    (.add (.add (.var 0) (.mul (.var 1) (.var 4))) (.add (.var 2) (.mul (.var 3) (.var 4))))
    (.add (.add (.var 0) (.var 2)) (.mul (.add (.var 1) (.var 3)) (.var 4))) (by decide +kernel)

/-- A sum of two terms with constant coefficients. -/
theorem sum_lin2 (f g : Nat → Shell p) (c : Shell p) : ∀ n,
    sumRange (fun μ => f μ + g μ * c) n = sumRange f n + sumRange g n * c
  | 0 => lin2_zero c
  | n + 1 => by
    show sumRange (fun μ => f μ + g μ * c) n + (f n + g n * c) = sumRange f n + f n + (sumRange g n + g n) * c
    rw [sum_lin2 f g c n]; exact lin2_step _ _ _ _ _

theorem lin3_zero (c d : Shell p) : 0 = 0 + 0 * c + 0 * d :=
  RE.sound (look [c, d])
    .zero
    (.add (.add .zero (.mul .zero (.var 0))) (.mul .zero (.var 1))) (by decide +kernel)

theorem lin3_step (S T U a b e c d : Shell p) :
    S + T * c + U * d + (a + b * c + e * d) = S + a + (T + b) * c + (U + e) * d :=
  RE.sound (look [S, T, U, a, b, e, c, d])
    (.add (.add (.add (.var 0) (.mul (.var 1) (.var 6))) (.mul (.var 2) (.var 7))) (.add (.add (.var 3) (.mul (.var 4) (.var 6))) (.mul (.var 5) (.var 7))))
    (.add (.add (.add (.var 0) (.var 3)) (.mul (.add (.var 1) (.var 4)) (.var 6))) (.mul (.add (.var 2) (.var 5)) (.var 7))) (by decide +kernel)

/-- A sum of three terms with constant coefficients. -/
theorem sum_lin3 (f g h : Nat → Shell p) (c d : Shell p) : ∀ n,
    sumRange (fun μ => f μ + g μ * c + h μ * d) n = sumRange f n + sumRange g n * c + sumRange h n * d
  | 0 => lin3_zero c d
  | n + 1 => by
    show sumRange (fun μ => f μ + g μ * c + h μ * d) n + (f n + g n * c + h n * d) =
      sumRange f n + f n + (sumRange g n + g n) * c + (sumRange h n + h n) * d
    rw [sum_lin3 f g h c d n]; exact lin3_step _ _ _ _ _ _ _ _

theorem lin6_zero (c₁ c₂ c₃ c₄ c₅ : Shell p) : 0 = 0 + 0 * c₁ + 0 * c₂ + 0 * c₃ + 0 * c₄ + 0 * c₅ :=
  RE.sound (look [c₁, c₂, c₃, c₄, c₅])
    .zero
    (.add (.add (.add (.add (.add .zero (.mul .zero (.var 0))) (.mul .zero (.var 1))) (.mul .zero (.var 2))) (.mul .zero (.var 3))) (.mul .zero (.var 4))) (by decide +kernel)

theorem lin6_step (S₀ S₁ S₂ S₃ S₄ S₅ b₀ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ : Shell p) :
    S₀ + S₁ * c₁ + S₂ * c₂ + S₃ * c₃ + S₄ * c₄ + S₅ * c₅ + (b₀ + b₁ * c₁ + b₂ * c₂ + b₃ * c₃ + b₄ * c₄ + b₅ * c₅) =
      S₀ + b₀ + (S₁ + b₁) * c₁ + (S₂ + b₂) * c₂ + (S₃ + b₃) * c₃ + (S₄ + b₄) * c₄ + (S₅ + b₅) * c₅ :=
  RE.sound (look [S₀, S₁, S₂, S₃, S₄, S₅, b₀, b₁, b₂, b₃, b₄, b₅, c₁, c₂, c₃, c₄, c₅])
    (.add (.add (.add (.add (.add (.add (.var 0) (.mul (.var 1) (.var 12))) (.mul (.var 2) (.var 13))) (.mul (.var 3) (.var 14))) (.mul (.var 4) (.var 15))) (.mul (.var 5) (.var 16))) (.add (.add (.add (.add (.add (.var 6) (.mul (.var 7) (.var 12))) (.mul (.var 8) (.var 13))) (.mul (.var 9) (.var 14))) (.mul (.var 10) (.var 15))) (.mul (.var 11) (.var 16))))
    (.add (.add (.add (.add (.add (.add (.var 0) (.var 6)) (.mul (.add (.var 1) (.var 7)) (.var 12))) (.mul (.add (.var 2) (.var 8)) (.var 13))) (.mul (.add (.var 3) (.var 9)) (.var 14))) (.mul (.add (.var 4) (.var 10)) (.var 15))) (.mul (.add (.var 5) (.var 11)) (.var 16))) (by decide +kernel)

/-- A sum of six terms with constant coefficients. -/
theorem sum_lin6 (f₀ f₁ f₂ f₃ f₄ f₅ : Nat → Shell p) (c₁ c₂ c₃ c₄ c₅ : Shell p) : ∀ n,
    sumRange (fun μ => f₀ μ + f₁ μ * c₁ + f₂ μ * c₂ + f₃ μ * c₃ + f₄ μ * c₄ + f₅ μ * c₅) n =
      sumRange f₀ n + sumRange f₁ n * c₁ + sumRange f₂ n * c₂ + sumRange f₃ n * c₃ + sumRange f₄ n * c₄ +
        sumRange f₅ n * c₅
  | 0 => lin6_zero c₁ c₂ c₃ c₄ c₅
  | n + 1 => by
    show sumRange (fun μ => f₀ μ + f₁ μ * c₁ + f₂ μ * c₂ + f₃ μ * c₃ + f₄ μ * c₄ + f₅ μ * c₅) n +
        (f₀ n + f₁ n * c₁ + f₂ n * c₂ + f₃ n * c₃ + f₄ n * c₄ + f₅ n * c₅) =
      sumRange f₀ n + f₀ n + (sumRange f₁ n + f₁ n) * c₁ + (sumRange f₂ n + f₂ n) * c₂ +
        (sumRange f₃ n + f₃ n) * c₃ + (sumRange f₄ n + f₄ n) * c₄ + (sumRange f₅ n + f₅ n) * c₅
    rw [sum_lin6 f₀ f₁ f₂ f₃ f₄ f₅ c₁ c₂ c₃ c₄ c₅ n]; exact lin6_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-! ## The metric pairing -/

/-- The metric pairing `u·v = Σ_{μ<n} η_μ u_μ v_μ` for a diagonal metric `η`. -/
def dot (η : Nat → Shell p) (n : Nat) (u v : Nat → Shell p) : Shell p := sumRange (fun μ => η μ * u μ * v μ) n

theorem comm_pt (e u v : Shell p) : e * u * v = e * v * u :=
  RE.sound (look [e, u, v])
    (.mul (.mul (.var 0) (.var 1)) (.var 2))
    (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide +kernel)

theorem dot_comm (η : Nat → Shell p) (n : Nat) (u v : Nat → Shell p) : dot η n u v = dot η n v u :=
  sum_congr n (fun _ _ => comm_pt _ _ _)

theorem dot_zero_left (η : Nat → Shell p) (n : Nat) {u : Nat → Shell p} (v : Nat → Shell p) (hu : ∀ μ, u μ = 0) :
    dot η n u v = 0 :=
  sum_zero n (fun μ _ => by show η μ * u μ * v μ = 0; rw [hu μ, mul_zero, zero_mul])

theorem lin2_pt (e w u x c : Shell p) : e * (w + c * u) * x = e * w * x + e * u * x * c :=
  RE.sound (look [e, w, u, x, c])
    (.mul (.mul (.var 0) (.add (.var 1) (.mul (.var 4) (.var 2)))) (.var 3))
    (.add (.mul (.mul (.var 0) (.var 1)) (.var 3)) (.mul (.mul (.mul (.var 0) (.var 2)) (.var 3)) (.var 4))) (by decide +kernel)

/-- The pairing is linear in its first slot (two terms). -/
theorem dot_lin2 (η : Nat → Shell p) (n : Nat) {W w u : Nat → Shell p} {c : Shell p}
    (hW : ∀ μ, W μ = w μ + c * u μ) (x : Nat → Shell p) :
    dot η n W x = dot η n w x + dot η n u x * c :=
  (sum_congr n (fun μ _ => by rw [hW μ]; exact lin2_pt _ _ _ _ _)).trans (sum_lin2 _ _ c n)

theorem lin3_pt (e w u v c d x : Shell p) :
    e * (w + c * u + d * v) * x = e * w * x + e * u * x * c + e * v * x * d :=
  RE.sound (look [e, w, u, v, c, d, x])
    (.mul (.mul (.var 0) (.add (.add (.var 1) (.mul (.var 4) (.var 2))) (.mul (.var 5) (.var 3)))) (.var 6))
    (.add (.add (.mul (.mul (.var 0) (.var 1)) (.var 6)) (.mul (.mul (.mul (.var 0) (.var 2)) (.var 6)) (.var 4))) (.mul (.mul (.mul (.var 0) (.var 3)) (.var 6)) (.var 5))) (by decide +kernel)

/-- The pairing is linear in its first slot (three terms). -/
theorem dot_lin3 (η : Nat → Shell p) (n : Nat) {W w u v : Nat → Shell p} {c d : Shell p}
    (hW : ∀ μ, W μ = w μ + c * u μ + d * v μ) (x : Nat → Shell p) :
    dot η n W x = dot η n w x + dot η n u x * c + dot η n v x * d :=
  (sum_congr n (fun μ _ => by rw [hW μ]; exact lin3_pt _ _ _ _ _ _ _)).trans (sum_lin3 _ _ _ c d n)

theorem quad2_pt (e w u c : Shell p) :
    e * (w + c * u) * (w + c * u) = e * w * w + e * w * u * ((1 + 1) * c) + e * u * u * (c * c) :=
  RE.sound (look [e, w, u, c])
    (.mul (.mul (.var 0) (.add (.var 1) (.mul (.var 3) (.var 2)))) (.add (.var 1) (.mul (.var 3) (.var 2))))
    (.add (.add (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.mul (.add .one .one) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 2)) (.var 2)) (.mul (.var 3) (.var 3)))) (by decide +kernel)

/-- The square of a two-term combination. -/
theorem dot_quad2 (η : Nat → Shell p) (n : Nat) {W w u : Nat → Shell p} {c : Shell p}
    (hW : ∀ μ, W μ = w μ + c * u μ) :
    dot η n W W = dot η n w w + dot η n w u * ((1 + 1) * c) + dot η n u u * (c * c) :=
  (sum_congr n (fun μ _ => by rw [hW μ]; exact quad2_pt _ _ _ _)).trans (sum_lin3 _ _ _ _ _ n)

theorem quad3_pt (e w u v c d : Shell p) :
    e * (w + c * u + d * v) * (w + c * u + d * v) = e * w * w + e * u * u * (c * c) + e * v * v * (d * d) +
      e * w * u * ((1 + 1) * c) + e * w * v * ((1 + 1) * d) + e * u * v * ((1 + 1) * c * d) :=
  RE.sound (look [e, w, u, v, c, d])
    (.mul (.mul (.var 0) (.add (.add (.var 1) (.mul (.var 4) (.var 2))) (.mul (.var 5) (.var 3)))) (.add (.add (.var 1) (.mul (.var 4) (.var 2))) (.mul (.var 5) (.var 3))))
    (.add (.add (.add (.add (.add (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.mul (.mul (.mul (.var 0) (.var 2)) (.var 2)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 3)) (.var 3)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.mul (.add .one .one) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 1)) (.var 3)) (.mul (.add .one .one) (.var 5)))) (.mul (.mul (.mul (.var 0) (.var 2)) (.var 3)) (.mul (.mul (.add .one .one) (.var 4)) (.var 5)))) (by decide +kernel)

/-- The square of a three-term combination. -/
theorem dot_quad3 (η : Nat → Shell p) (n : Nat) {W w u v : Nat → Shell p} {c d : Shell p}
    (hW : ∀ μ, W μ = w μ + c * u μ + d * v μ) :
    dot η n W W = dot η n w w + dot η n u u * (c * c) + dot η n v v * (d * d) + dot η n w u * ((1 + 1) * c) +
      dot η n w v * ((1 + 1) * d) + dot η n u v * ((1 + 1) * c * d) :=
  (sum_congr n (fun μ _ => by rw [hW μ]; exact quad3_pt _ _ _ _ _ _)).trans (sum_lin6 _ _ _ _ _ _ _ _ _ _ _ n)

/-! ## Spin 1: the vector field -/

/-- The gauge shift `A ↦ A + z k`. -/
def shift (A k : Nat → Shell p) (z : Shell p) : Nat → Shell p := fun μ => A μ + z * k μ

/-- The two relevant quadratic scalars of a vector field at the symbol `k`: `a₁ k² A·A + a₂ (k·A)²`. -/
def vecForm (η : Nat → Shell p) (n : Nat) (a₁ a₂ : Shell p) (k A : Nat → Shell p) : Shell p :=
  a₁ * dot η n k k * dot η n A A + a₂ * (dot η n k A * dot η n k A)

theorem vec_ring (a₁ a₂ K B C z : Shell p) :
    a₁ * K * (C + B * ((1 + 1) * z) + K * (z * z)) + a₂ * ((B + K * z) * (B + K * z)) =
      a₁ * K * C + a₂ * (B * B) + (a₁ + a₂) * K * (z * ((1 + 1) * B) + z * z * K) :=
  RE.sound (look [a₁, a₂, K, B, C, z])
    (.add (.mul (.mul (.var 0) (.var 2)) (.add (.add (.var 4) (.mul (.var 3) (.mul (.add .one .one) (.var 5)))) (.mul (.var 2) (.mul (.var 5) (.var 5))))) (.mul (.var 1) (.mul (.add (.var 3) (.mul (.var 2) (.var 5))) (.add (.var 3) (.mul (.var 2) (.var 5))))))
    (.add (.add (.mul (.mul (.var 0) (.var 2)) (.var 4)) (.mul (.var 1) (.mul (.var 3) (.var 3)))) (.mul (.mul (.add (.var 0) (.var 1)) (.var 2)) (.add (.mul (.var 5) (.mul (.add .one .one) (.var 3))) (.mul (.mul (.var 5) (.var 5)) (.var 2))))) (by decide +kernel)

/-- Spin 1, the gauge variation as a polynomial identity in `z`, on every shell, in every dimension and metric:
`a₁ k² (A + zk)² + a₂ (k·(A + zk))² = a₁ k² A² + a₂ (k·A)² + (a₁ + a₂) k² (2z (k·A) + z² k²)`. -/
theorem vec_shift (η : Nat → Shell p) (n : Nat) (a₁ a₂ : Shell p) (k A : Nat → Shell p) (z : Shell p) :
    vecForm η n a₁ a₂ k (shift A k z) = vecForm η n a₁ a₂ k A +
      (a₁ + a₂) * dot η n k k * (z * ((1 + 1) * dot η n k A) + z * z * dot η n k k) := by
  have e₁ : dot η n k (shift A k z) = dot η n k A + dot η n k k * z := by
    rw [dot_comm η n k (shift A k z), dot_lin2 η n (W := shift A k z) (w := A) (u := k) (c := z) (fun _ => rfl) k, dot_comm η n A k]
  have e₂ : dot η n (shift A k z) (shift A k z) =
      dot η n A A + dot η n k A * ((1 + 1) * z) + dot η n k k * (z * z) := by
    rw [dot_quad2 η n (W := shift A k z) (w := A) (u := k) (c := z) (fun _ => rfl), dot_comm η n A k]
  unfold vecForm
  rw [e₁, e₂]
  exact vec_ring _ _ _ _ _ _

/-- Spin 1: the line `a₁ + a₂ = 0`, the symbol of `F²`, is gauge invariant at every symbol. -/
theorem vec_invariant (η : Nat → Shell p) (n : Nat) {a₁ a₂ : Shell p} (h : a₁ + a₂ = 0) (k A : Nat → Shell p)
    (z : Shell p) : vecForm η n a₁ a₂ k (shift A k z) = vecForm η n a₁ a₂ k A := by
  rw [vec_shift, h, zero_mul, zero_mul, add_zero]

/-- Spin 1 at a null symbol, `k² = 0`: every form is gauge invariant, so the symbol decides nothing there. -/
theorem vec_null (η : Nat → Shell p) (n : Nat) (a₁ a₂ : Shell p) {k : Nat → Shell p} (hk : dot η n k k = 0)
    (A : Nat → Shell p) (z : Shell p) : vecForm η n a₁ a₂ k (shift A k z) = vecForm η n a₁ a₂ k A := by
  rw [vec_shift, hk, mul_zero, zero_mul, add_zero]

/-! ## Cancellation helpers -/

theorem eq_zero_of_add_left {a b : Shell p} (h : a + b = a) : b = 0 :=
  add_right_cancel (c := a) (by rw [add_comm, h, zero_add])

theorem sub_one_zero {a : Shell p} (h : a = 1) : a + -1 = 0 := by rw [h]; exact add_neg 1

theorem lc2 {L R x y e f : Shell p} (h : L = R + x * e + y * f) (he : e = 0) (hf : f = 0) : L = R := by
  rw [h, he, hf, mul_zero, mul_zero, add_zero, add_zero]

theorem lc4 {L R x y z w e f g u : Shell p} (h : L = R + x * e + y * f + z * g + w * u) (he : e = 0) (hf : f = 0)
    (hg : g = 0) (hu : u = 0) : L = R := by
  rw [h, he, hf, hg, hu, mul_zero, mul_zero, mul_zero, mul_zero, add_zero, add_zero, add_zero, add_zero]

theorem cancel3_ring (c x y z x' y' z' : Shell p) :
    c * (x * x' * (y * y') * (z * z')) = c * (x * y * z) * (x' * y' * z') :=
  RE.sound (look [c, x, y, z, x', y', z'])
    (.mul (.var 0) (.mul (.mul (.mul (.var 1) (.var 4)) (.mul (.var 2) (.var 5))) (.mul (.var 3) (.var 6))))
    (.mul (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 3))) (.mul (.mul (.var 4) (.var 5)) (.var 6))) (by decide +kernel)

/-- A product with three unit factors vanishes only if the cofactor does. -/
theorem cancel3 {c x y z x' y' z' : Shell p} (h : c * (x * y * z) = 0) (hx : x * x' = 1) (hy : y * y' = 1)
    (hz : z * z' = 1) : c = 0 := by
  have e := cancel3_ring c x y z x' y' z'
  rw [hx, hy, hz, h, zero_mul, one_mul, one_mul, mul_one] at e
  exact e

theorem cancel4_ring (c x y z w x' y' z' w' : Shell p) :
    c * (x * x' * (y * y') * (z * z') * (w * w')) = c * (x * y * z * w) * (x' * y' * z' * w') :=
  RE.sound (look [c, x, y, z, w, x', y', z', w'])
    (.mul (.var 0) (.mul (.mul (.mul (.mul (.var 1) (.var 5)) (.mul (.var 2) (.var 6))) (.mul (.var 3) (.var 7))) (.mul (.var 4) (.var 8))))
    (.mul (.mul (.var 0) (.mul (.mul (.mul (.var 1) (.var 2)) (.var 3)) (.var 4))) (.mul (.mul (.mul (.var 5) (.var 6)) (.var 7)) (.var 8))) (by decide +kernel)

/-- A product with four unit factors vanishes only if the cofactor does. -/
theorem cancel4 {c x y z w x' y' z' w' : Shell p} (h : c * (x * y * z * w) = 0) (hx : x * x' = 1)
    (hy : y * y' = 1) (hz : z * z' = 1) (hw : w * w' = 1) : c = 0 := by
  have e := cancel4_ring c x y z w x' y' z' w'
  rw [hx, hy, hz, hw, h, zero_mul, one_mul, one_mul, one_mul, mul_one] at e
  exact e

theorem unit_ring (s K w : Shell p) :
    s = 0 + (w * w) * (s * K * (1 * ((1 + 1) * 0) + 1 * 1 * K)) + (-(s * (K * w + 1))) * (K * w + -1) :=
  RE.sound (look [s, K, w])
    (.var 0)
    (.add (.add .zero (.mul (.mul (.var 2) (.var 2)) (.mul (.mul (.var 0) (.var 1)) (.add (.mul .one (.mul (.add .one .one) .zero)) (.mul (.mul .one .one) (.var 1)))))) (.mul (.neg (.mul (.var 0) (.add (.mul (.var 1) (.var 2)) .one))) (.add (.mul (.var 1) (.var 2)) (.neg .one)))) (by decide +kernel)

/-- Spin 1 at a symbol whose square `k²` is a unit: the form is gauge invariant exactly on the line `a₁ + a₂ = 0`. -/
theorem vec_iff_unit (η : Nat → Shell p) (n : Nat) (a₁ a₂ : Shell p) (k : Nat → Shell p) {w : Shell p}
    (hk : dot η n k k * w = 1) :
    (∀ (A : Nat → Shell p) (z : Shell p), vecForm η n a₁ a₂ k (shift A k z) = vecForm η n a₁ a₂ k A) ↔
      a₁ + a₂ = 0 := by
  constructor
  · intro h
    have h₀ := (vec_shift η n a₁ a₂ k (fun _ => 0) 1).symm.trans (h (fun _ => 0) 1)
    rw [dot_comm η n k (fun _ => 0), dot_zero_left η n (u := fun _ => 0) k (fun _ => rfl)] at h₀
    exact lc2 (unit_ring (a₁ + a₂) (dot η n k k) w) (eq_zero_of_add_left h₀) (sub_one_zero hk)
  · intro h A z
    exact vec_invariant η n h k A z

/-! ## Coordinate vectors -/

/-- The coordinate vector `e_i`. -/
def basis (i : Nat) : Nat → Shell p := fun μ => if μ = i then 1 else 0

theorem basis_self (i : Nat) : basis (p := p) i i = 1 := ite_eq_left rfl

theorem basis_ne {i μ : Nat} (h : μ ≠ i) : basis (p := p) i μ = 0 := ite_eq_right h

theorem basis_mul_ne {i j : Nat} (hij : i ≠ j) (μ : Nat) : basis (p := p) i μ * basis j μ = 0 :=
  match Nat.decEq μ i with
  | isTrue e => by rw [basis_ne (fun e' => hij (e.symm.trans e')), mul_zero]
  | isFalse e => by rw [basis_ne e, zero_mul]

theorem dot_basis_self (η : Nat → Shell p) {n i : Nat} (hi : i < n) : dot η n (basis i) (basis i) = η i :=
  (sum_eq_single hi (fun l _ hl => by
    show η l * basis i l * basis i l = 0
    rw [basis_ne hl, mul_zero])).trans (by
    show η i * basis i i * basis i i = η i
    rw [basis_self, mul_one, mul_one])

theorem dot_basis_ne (η : Nat → Shell p) (n : Nat) {i j : Nat} (hij : i ≠ j) : dot η n (basis i) (basis j) = 0 :=
  sum_zero n (fun l _ => by
    show η l * basis i l * basis j l = 0
    rw [mul_assoc, basis_mul_ne hij, mul_zero])

/-- Spin 1 over all symbols: when the metric entry `η₀` is a unit (`n ≥ 1`), the forms gauge invariant at every
symbol are exactly the line `a₁ + a₂ = 0`, Maxwell's `F²`. -/
theorem maxwell_unique (η : Nat → Shell p) {n : Nat} {w : Shell p} (hn : 0 < n) (h₀ : η 0 * w = 1)
    (a₁ a₂ : Shell p) :
    (∀ (k A : Nat → Shell p) (z : Shell p), vecForm η n a₁ a₂ k (shift A k z) = vecForm η n a₁ a₂ k A) ↔
      a₁ + a₂ = 0 :=
  ⟨fun h => (vec_iff_unit η n a₁ a₂ (basis 0) (w := w) (by rw [dot_basis_self η hn]; exact h₀)).mp (h (basis 0)),
   fun h k A z => vec_invariant η n h k A z⟩

/-! ## Spin 2: the symmetric tensor field -/

/-- The trace `tr h = Σ_μ η_μ h_μμ`. -/
def tr (η : Nat → Shell p) (n : Nat) (h : Nat → Nat → Shell p) : Shell p := sumRange (fun μ => η μ * h μ μ) n

/-- The contraction `(u·h)_ν = Σ_μ η_μ u_μ h_μν`. -/
def ctr (η : Nat → Shell p) (n : Nat) (u : Nat → Shell p) (h : Nat → Nat → Shell p) : Nat → Shell p :=
  fun ν => sumRange (fun μ => η μ * u μ * h μ ν) n

/-- The pairing `⟨h, h'⟩ = Σ_μ η_μ (h_μ · h'_μ)`, row by row. -/
def pair (η : Nat → Shell p) (n : Nat) (h h' : Nat → Nat → Shell p) : Shell p :=
  sumRange (fun μ => η μ * dot η n (h μ) (h' μ)) n

/-- The gauge shift `h_μν ↦ h_μν + k_μ ξ_ν + k_ν ξ_μ`. -/
def gauge (h : Nat → Nat → Shell p) (k ξ : Nat → Shell p) : Nat → Nat → Shell p :=
  fun μ ν => h μ ν + (k μ * ξ ν + k ν * ξ μ)

/-- The four two-derivative quadratic scalars of a symmetric field at the symbol `k`, combined:
`a₁ k² ⟨h, h⟩ + a₂ (k·h)·(k·h) + a₃ (k·h·k) tr h + a₄ k² (tr h)²`. -/
def tensForm (η : Nat → Shell p) (n : Nat) (a₁ a₂ a₃ a₄ : Shell p) (k : Nat → Shell p) (h : Nat → Nat → Shell p) :
    Shell p :=
  a₁ * (dot η n k k * pair η n h h) + a₂ * dot η n (ctr η n k h) (ctr η n k h) +
    a₃ * (dot η n (ctr η n k h) k * tr η n h) + a₄ * (dot η n k k * (tr η n h * tr η n h))

theorem tr_pt (e h a b : Shell p) : e * (h + (a * b + a * b)) = e * h + e * a * b * (1 + 1) :=
  RE.sound (look [e, h, a, b])
    (.mul (.var 0) (.add (.var 1) (.add (.mul (.var 2) (.var 3)) (.mul (.var 2) (.var 3)))))
    (.add (.mul (.var 0) (.var 1)) (.mul (.mul (.mul (.var 0) (.var 2)) (.var 3)) (.add .one .one))) (by decide +kernel)

theorem tr_gauge (η : Nat → Shell p) (n : Nat) (h : Nat → Nat → Shell p) (k ξ : Nat → Shell p) :
    tr η n (gauge h k ξ) = tr η n h + dot η n k ξ * (1 + 1) :=
  (sum_congr n (fun _ _ => tr_pt _ _ _ _)).trans (sum_lin2 _ _ _ n)

theorem ctr_pt (e a h b c d : Shell p) :
    e * a * (h + (a * b + c * d)) = e * a * h + e * a * a * b + e * a * d * c :=
  RE.sound (look [e, a, h, b, c, d])
    (.mul (.mul (.var 0) (.var 1)) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.mul (.var 4) (.var 5)))))
    (.add (.add (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.mul (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.var 3))) (.mul (.mul (.mul (.var 0) (.var 1)) (.var 5)) (.var 4))) (by decide +kernel)

theorem ctr_gauge (η : Nat → Shell p) (n : Nat) (k ξ : Nat → Shell p) (h : Nat → Nat → Shell p) (ν : Nat) :
    ctr η n k (gauge h k ξ) ν = ctr η n k h ν + dot η n k k * ξ ν + dot η n k ξ * k ν :=
  (sum_congr n (fun _ _ => ctr_pt _ _ _ _ _ _)).trans (sum_lin3 _ _ _ _ _ n)

theorem rows_pt (a b c d e : Shell p) : a * (b * c * d) * e = b * c * (a * d * e) :=
  RE.sound (look [a, b, c, d, e])
    (.mul (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 3))) (.var 4))
    (.mul (.mul (.var 1) (.var 2)) (.mul (.mul (.var 0) (.var 3)) (.var 4))) (by decide +kernel)

/-- `(u·h)·v` as a double sum. -/
theorem ctr_dot (η : Nat → Shell p) (n : Nat) (u v : Nat → Shell p) (h : Nat → Nat → Shell p) :
    dot η n (ctr η n u h) v = sumRange (fun ν => sumRange (fun μ => η μ * u μ * (η ν * h μ ν * v ν)) n) n :=
  sum_congr n (fun ν _ => by
    show η ν * sumRange (fun μ => η μ * u μ * h μ ν) n * v ν = _
    rw [← sum_mul_left, ← sum_mul_right]
    exact sum_congr n (fun μ _ => rows_pt _ _ _ _ _))

/-- `(u·h)·v` row by row: `Σ_μ η_μ u_μ (h_μ · v)`. -/
theorem rows (η : Nat → Shell p) (n : Nat) (u v : Nat → Shell p) (h : Nat → Nat → Shell p) :
    sumRange (fun μ => η μ * u μ * dot η n (h μ) v) n = dot η n (ctr η n u h) v := by
  rw [ctr_dot, ← sum_swap]
  exact sum_congr n (fun μ _ => (sum_mul_left _ _ n).symm)

theorem sym_pt (a u b h v : Shell p) : a * u * (b * h * v) = b * v * (a * h * u) :=
  RE.sound (look [a, u, b, h, v])
    (.mul (.mul (.var 0) (.var 1)) (.mul (.mul (.var 2) (.var 3)) (.var 4)))
    (.mul (.mul (.var 2) (.var 4)) (.mul (.mul (.var 0) (.var 3)) (.var 1))) (by decide +kernel)

/-- For a symmetric `h`, `(u·h)·v = (v·h)·u`. -/
theorem ctr_symm (η : Nat → Shell p) (n : Nat) (u v : Nat → Shell p) {h : Nat → Nat → Shell p}
    (hs : ∀ μ ν, h μ ν = h ν μ) : dot η n (ctr η n u h) v = dot η n (ctr η n v h) u := by
  rw [ctr_dot η n u v h, ctr_dot η n v u h, sum_swap]
  exact sum_congr n (fun a _ => sum_congr n (fun b _ => by rw [hs a b]; exact sym_pt _ _ _ _ _))

theorem row_pt (h a x b c : Shell p) : h + (a * x + b * c) = h + a * x + c * b :=
  RE.sound (look [h, a, x, b, c])
    (.add (.var 0) (.add (.mul (.var 1) (.var 2)) (.mul (.var 3) (.var 4))))
    (.add (.add (.var 0) (.mul (.var 1) (.var 2))) (.mul (.var 4) (.var 3))) (by decide +kernel)

theorem pair_pt (e P X K a b B C Y : Shell p) :
    e * (P + X * (a * a) + K * (b * b) + B * ((1 + 1) * a) + C * ((1 + 1) * b) + Y * ((1 + 1) * a * b)) =
      e * P + e * a * a * X + e * b * b * K + e * a * B * (1 + 1) + e * b * C * (1 + 1) + e * a * b * ((1 + 1) * Y) :=
  RE.sound (look [e, P, X, K, a, b, B, C, Y])
    (.mul (.var 0) (.add (.add (.add (.add (.add (.var 1) (.mul (.var 2) (.mul (.var 4) (.var 4)))) (.mul (.var 3) (.mul (.var 5) (.var 5)))) (.mul (.var 6) (.mul (.add .one .one) (.var 4)))) (.mul (.var 7) (.mul (.add .one .one) (.var 5)))) (.mul (.var 8) (.mul (.mul (.add .one .one) (.var 4)) (.var 5)))))
    (.add (.add (.add (.add (.add (.mul (.var 0) (.var 1)) (.mul (.mul (.mul (.var 0) (.var 4)) (.var 4)) (.var 2))) (.mul (.mul (.mul (.var 0) (.var 5)) (.var 5)) (.var 3))) (.mul (.mul (.mul (.var 0) (.var 4)) (.var 6)) (.add .one .one))) (.mul (.mul (.mul (.var 0) (.var 5)) (.var 7)) (.add .one .one))) (.mul (.mul (.mul (.var 0) (.var 4)) (.var 5)) (.mul (.add .one .one) (.var 8)))) (by decide +kernel)

theorem pair_gauge (η : Nat → Shell p) (n : Nat) (k ξ : Nat → Shell p) {h : Nat → Nat → Shell p}
    (hs : ∀ μ ν, h μ ν = h ν μ) :
    pair η n (gauge h k ξ) (gauge h k ξ) = pair η n h h + dot η n k k * dot η n ξ ξ + dot η n ξ ξ * dot η n k k +
      dot η n (ctr η n k h) ξ * (1 + 1) + dot η n (ctr η n k h) ξ * (1 + 1) + dot η n k ξ * ((1 + 1) * dot η n k ξ) := by
  have row : ∀ μ, dot η n (gauge h k ξ μ) (gauge h k ξ μ) = dot η n (h μ) (h μ) + dot η n ξ ξ * (k μ * k μ) +
      dot η n k k * (ξ μ * ξ μ) + dot η n (h μ) ξ * ((1 + 1) * k μ) + dot η n (h μ) k * ((1 + 1) * ξ μ) +
      dot η n ξ k * ((1 + 1) * k μ * ξ μ) := fun μ =>
    dot_quad3 η n (W := gauge h k ξ μ) (w := h μ) (u := ξ) (v := k) (c := k μ) (d := ξ μ)
      (fun ν => row_pt _ _ _ _ _)
  have e := sum_lin6 (fun μ => η μ * dot η n (h μ) (h μ)) (fun μ => η μ * k μ * k μ) (fun μ => η μ * ξ μ * ξ μ)
    (fun μ => η μ * k μ * dot η n (h μ) ξ) (fun μ => η μ * ξ μ * dot η n (h μ) k) (fun μ => η μ * k μ * ξ μ)
    (dot η n ξ ξ) (dot η n k k) (1 + 1) (1 + 1) ((1 + 1) * dot η n ξ k) n
  rw [rows η n k ξ h, rows η n ξ k h, ctr_symm η n ξ k hs, dot_comm η n ξ k] at e
  exact (sum_congr n (fun μ _ => by rw [row μ, dot_comm η n ξ k]; exact pair_pt _ _ _ _ _ _ _ _ _)).trans e

theorem tens_ring (a₁ a₂ a₃ a₄ K P X B Y D C T : Shell p) :
    a₁ * (K * (P + K * X + X * K + B * (1 + 1) + B * (1 + 1) + Y * ((1 + 1) * Y))) +
        a₂ * (D + X * (K * K) + K * (Y * Y) + B * ((1 + 1) * K) + C * ((1 + 1) * Y) + Y * ((1 + 1) * K * Y)) +
        a₃ * ((C + Y * K + K * Y) * (T + Y * (1 + 1))) + a₄ * (K * ((T + Y * (1 + 1)) * (T + Y * (1 + 1)))) =
      a₁ * (K * P) + a₂ * D + a₃ * (C * T) + a₄ * (K * (T * T)) +
        ((1 + 1) * a₁ + a₂) * ((1 + 1) * K * B + K * K * X + K * (Y * Y)) +
        (a₂ + a₃) * ((1 + 1) * Y * C + (1 + 1) * K * (Y * Y)) +
        (a₃ + (1 + 1) * a₄) * ((1 + 1) * K * Y * T + (1 + 1) * K * (Y * Y)) :=
  RE.sound (look [a₁, a₂, a₃, a₄, K, P, X, B, Y, D, C, T])
    (.add (.add (.add (.mul (.var 0) (.mul (.var 4) (.add (.add (.add (.add (.add (.var 5) (.mul (.var 4) (.var 6))) (.mul (.var 6) (.var 4))) (.mul (.var 7) (.add .one .one))) (.mul (.var 7) (.add .one .one))) (.mul (.var 8) (.mul (.add .one .one) (.var 8)))))) (.mul (.var 1) (.add (.add (.add (.add (.add (.var 9) (.mul (.var 6) (.mul (.var 4) (.var 4)))) (.mul (.var 4) (.mul (.var 8) (.var 8)))) (.mul (.var 7) (.mul (.add .one .one) (.var 4)))) (.mul (.var 10) (.mul (.add .one .one) (.var 8)))) (.mul (.var 8) (.mul (.mul (.add .one .one) (.var 4)) (.var 8)))))) (.mul (.var 2) (.mul (.add (.add (.var 10) (.mul (.var 8) (.var 4))) (.mul (.var 4) (.var 8))) (.add (.var 11) (.mul (.var 8) (.add .one .one)))))) (.mul (.var 3) (.mul (.var 4) (.mul (.add (.var 11) (.mul (.var 8) (.add .one .one))) (.add (.var 11) (.mul (.var 8) (.add .one .one)))))))
    (.add (.add (.add (.add (.add (.add (.mul (.var 0) (.mul (.var 4) (.var 5))) (.mul (.var 1) (.var 9))) (.mul (.var 2) (.mul (.var 10) (.var 11)))) (.mul (.var 3) (.mul (.var 4) (.mul (.var 11) (.var 11))))) (.mul (.add (.mul (.add .one .one) (.var 0)) (.var 1)) (.add (.add (.mul (.mul (.add .one .one) (.var 4)) (.var 7)) (.mul (.mul (.var 4) (.var 4)) (.var 6))) (.mul (.var 4) (.mul (.var 8) (.var 8)))))) (.mul (.add (.var 1) (.var 2)) (.add (.mul (.mul (.add .one .one) (.var 8)) (.var 10)) (.mul (.mul (.add .one .one) (.var 4)) (.mul (.var 8) (.var 8)))))) (.mul (.add (.var 2) (.mul (.add .one .one) (.var 3))) (.add (.mul (.mul (.mul (.add .one .one) (.var 4)) (.var 8)) (.var 11)) (.mul (.mul (.add .one .one) (.var 4)) (.mul (.var 8) (.var 8)))))) (by decide +kernel)

/-- Spin 2, the gauge variation, on every shell, in every dimension and metric: for a symmetric `h`, the shift
`h ↦ h + kξ + ξk` changes the combination by `(2a₁ + a₂) X₁ + (a₂ + a₃) X₂ + (a₃ + 2a₄) X₃`, with
`X₁ = 2k² (k·h·ξ) + k⁴ ξ² + k² (k·ξ)²`, `X₂ = 2(k·ξ)(k·h·k) + 2k² (k·ξ)²` and `X₃ = 2k² (k·ξ) tr h + 2k² (k·ξ)²`. -/
theorem tens_shift (η : Nat → Shell p) (n : Nat) (a₁ a₂ a₃ a₄ : Shell p) (k ξ : Nat → Shell p)
    {h : Nat → Nat → Shell p} (hs : ∀ μ ν, h μ ν = h ν μ) :
    tensForm η n a₁ a₂ a₃ a₄ k (gauge h k ξ) = tensForm η n a₁ a₂ a₃ a₄ k h +
      ((1 + 1) * a₁ + a₂) * ((1 + 1) * dot η n k k * dot η n (ctr η n k h) ξ +
        dot η n k k * dot η n k k * dot η n ξ ξ + dot η n k k * (dot η n k ξ * dot η n k ξ)) +
      (a₂ + a₃) * ((1 + 1) * dot η n k ξ * dot η n (ctr η n k h) k +
        (1 + 1) * dot η n k k * (dot η n k ξ * dot η n k ξ)) +
      (a₃ + (1 + 1) * a₄) * ((1 + 1) * dot η n k k * dot η n k ξ * tr η n h +
        (1 + 1) * dot η n k k * (dot η n k ξ * dot η n k ξ)) := by
  have hc : ∀ ν, ctr η n k (gauge h k ξ) ν = ctr η n k h ν + dot η n k k * ξ ν + dot η n k ξ * k ν :=
    ctr_gauge η n k ξ h
  unfold tensForm
  rw [pair_gauge η n k ξ hs, dot_quad3 η n hc, dot_lin3 η n hc k, tr_gauge, dot_comm η n ξ k]
  exact tens_ring _ _ _ _ _ _ _ _ _ _ _ _

theorem fp_ring (S X₁ X₂ X₃ c : Shell p) :
    S + ((1 + 1) * (-c) + (1 + 1) * c) * X₁ + ((1 + 1) * c + (-((1 + 1) * c))) * X₂ +
      ((-((1 + 1) * c)) + (1 + 1) * c) * X₃ = S :=
  RE.sound (look [S, X₁, X₂, X₃, c])
    (.add (.add (.add (.var 0) (.mul (.add (.mul (.add .one .one) (.neg (.var 4))) (.mul (.add .one .one) (.var 4))) (.var 1))) (.mul (.add (.mul (.add .one .one) (.var 4)) (.neg (.mul (.add .one .one) (.var 4)))) (.var 2))) (.mul (.add (.neg (.mul (.add .one .one) (.var 4))) (.mul (.add .one .one) (.var 4))) (.var 3)))
    (.var 0) (by decide +kernel)

/-- 00:E1, 21:C9 — spin 2: the Fierz–Pauli line `(−1, 2, −2, 1)` is gauge invariant on every shell, at every symbol. -/
theorem fierz_pauli_invariant (η : Nat → Shell p) (n : Nat) (c : Shell p) (k ξ : Nat → Shell p)
    {h : Nat → Nat → Shell p} (hs : ∀ μ ν, h μ ν = h ν μ) :
    tensForm η n (-c) ((1 + 1) * c) (-((1 + 1) * c)) c k (gauge h k ξ) =
      tensForm η n (-c) ((1 + 1) * c) (-((1 + 1) * c)) c k h := by
  rw [tens_shift η n _ _ _ _ k ξ hs]
  exact fp_ring _ _ _ _ _

/-! ## Spin 2: uniqueness of the Fierz–Pauli line -/

/-- The zero field. -/
def zero2 : Nat → Nat → Shell p := fun _ _ => 0

/-- The field `e₁ ⊗ e₁`. -/
def unit11 : Nat → Nat → Shell p := fun μ ν => basis 1 μ * basis 1 ν

theorem var_ring (S A B C : Shell p) : A + B + C = S + A + B + C + -S :=
  RE.sound (look [S, A, B, C])
    (.add (.add (.var 1) (.var 2)) (.var 3))
    (.add (.add (.add (.add (.var 0) (.var 1)) (.var 2)) (.var 3)) (.neg (.var 0))) (by decide +kernel)

theorem var_zero {S A B C : Shell p} (h : S + A + B + C = S) : A + B + C = 0 := by
  rw [var_ring S A B C, h, add_neg]

theorem ctr_zero2 (η : Nat → Shell p) (n : Nat) (u v : Nat → Shell p) : dot η n (ctr η n u zero2) v = 0 :=
  dot_zero_left η n v (fun _ => sum_zero n (fun _ _ => mul_zero _))

theorem tr_zero2 (η : Nat → Shell p) (n : Nat) : tr η n zero2 = 0 := sum_zero n (fun _ _ => mul_zero _)

theorem u11_pt (e a b c : Shell p) : e * a * (b * c) = e * (a * b) * c :=
  RE.sound (look [e, a, b, c])
    (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
    (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.var 3)) (by decide +kernel)

theorem ctr_unit11 (η : Nat → Shell p) (n : Nat) (v : Nat → Shell p) : dot η n (ctr η n (basis 0) unit11) v = 0 :=
  dot_zero_left η n v (fun ν => sum_zero n (fun μ _ => by
    show η μ * basis 0 μ * (basis 1 μ * basis 1 ν) = 0
    rw [u11_pt, basis_mul_ne (i := 0) (j := 1) (by decide) μ, mul_zero, zero_mul]))

theorem tr_unit11 (η : Nat → Shell p) {n : Nat} (hn : 1 < n) : tr η n unit11 = η 1 :=
  (sum_congr n (fun _ _ => (mul_assoc _ _ _).symm)).trans (dot_basis_self η hn)

theorem t1_ring (A B C e₀ e₁ : Shell p) :
    A * ((1 + 1) * e₀ * 0 + e₀ * e₀ * e₁ + e₀ * (0 * 0)) + B * ((1 + 1) * 0 * 0 + (1 + 1) * e₀ * (0 * 0)) +
      C * ((1 + 1) * e₀ * 0 * 0 + (1 + 1) * e₀ * (0 * 0)) = A * (e₀ * e₀ * e₁) :=
  RE.sound (look [A, B, C, e₀, e₁])
    (.add (.add (.mul (.var 0) (.add (.add (.mul (.mul (.add .one .one) (.var 3)) .zero) (.mul (.mul (.var 3) (.var 3)) (.var 4))) (.mul (.var 3) (.mul .zero .zero)))) (.mul (.var 1) (.add (.mul (.mul (.add .one .one) .zero) .zero) (.mul (.mul (.add .one .one) (.var 3)) (.mul .zero .zero))))) (.mul (.var 2) (.add (.mul (.mul (.mul (.add .one .one) (.var 3)) .zero) .zero) (.mul (.mul (.add .one .one) (.var 3)) (.mul .zero .zero)))))
    (.mul (.var 0) (.mul (.mul (.var 3) (.var 3)) (.var 4))) (by decide +kernel)

theorem t2_ring (A B C e₀ : Shell p) :
    A * ((1 + 1) * e₀ * 0 + e₀ * e₀ * e₀ + e₀ * (e₀ * e₀)) + B * ((1 + 1) * e₀ * 0 + (1 + 1) * e₀ * (e₀ * e₀)) +
      C * ((1 + 1) * e₀ * e₀ * 0 + (1 + 1) * e₀ * (e₀ * e₀)) = (A + B + C) * ((1 + 1) * e₀ * e₀ * e₀) :=
  RE.sound (look [A, B, C, e₀])
    (.add (.add (.mul (.var 0) (.add (.add (.mul (.mul (.add .one .one) (.var 3)) .zero) (.mul (.mul (.var 3) (.var 3)) (.var 3))) (.mul (.var 3) (.mul (.var 3) (.var 3))))) (.mul (.var 1) (.add (.mul (.mul (.add .one .one) (.var 3)) .zero) (.mul (.mul (.add .one .one) (.var 3)) (.mul (.var 3) (.var 3)))))) (.mul (.var 2) (.add (.mul (.mul (.mul (.add .one .one) (.var 3)) (.var 3)) .zero) (.mul (.mul (.add .one .one) (.var 3)) (.mul (.var 3) (.var 3))))))
    (.mul (.add (.add (.var 0) (.var 1)) (.var 2)) (.mul (.mul (.mul (.add .one .one) (.var 3)) (.var 3)) (.var 3))) (by decide +kernel)

theorem t3_ring (A B C e₀ e₁ : Shell p) :
    A * ((1 + 1) * e₀ * 0 + e₀ * e₀ * e₀ + e₀ * (e₀ * e₀)) + B * ((1 + 1) * e₀ * 0 + (1 + 1) * e₀ * (e₀ * e₀)) +
      C * ((1 + 1) * e₀ * e₀ * e₁ + (1 + 1) * e₀ * (e₀ * e₀)) =
    (A + B + C) * ((1 + 1) * e₀ * e₀ * e₀) + C * ((1 + 1) * e₀ * e₀ * e₁) :=
  RE.sound (look [A, B, C, e₀, e₁])
    (.add (.add (.mul (.var 0) (.add (.add (.mul (.mul (.add .one .one) (.var 3)) .zero) (.mul (.mul (.var 3) (.var 3)) (.var 3))) (.mul (.var 3) (.mul (.var 3) (.var 3))))) (.mul (.var 1) (.add (.mul (.mul (.add .one .one) (.var 3)) .zero) (.mul (.mul (.add .one .one) (.var 3)) (.mul (.var 3) (.var 3)))))) (.mul (.var 2) (.add (.mul (.mul (.mul (.add .one .one) (.var 3)) (.var 3)) (.var 4)) (.mul (.mul (.add .one .one) (.var 3)) (.mul (.var 3) (.var 3))))))
    (.add (.mul (.add (.add (.var 0) (.var 1)) (.var 2)) (.mul (.mul (.mul (.add .one .one) (.var 3)) (.var 3)) (.var 3))) (.mul (.var 2) (.mul (.mul (.mul (.add .one .one) (.var 3)) (.var 3)) (.var 4)))) (by decide +kernel)

theorem line_a1 (a₁ a₂ a₃ a₄ t : Shell p) :
    a₁ + a₄ = 0 + (t * (1 + 1)) * ((1 + 1) * a₁ + a₂) +
      (-t) * ((1 + 1) * a₁ + a₂ + (a₂ + a₃) + (a₃ + (1 + 1) * a₄)) + (t * (1 + 1)) * (a₃ + (1 + 1) * a₄) +
      (-(a₁ + a₄)) * ((1 + 1) * t + -1) :=
  RE.sound (look [a₁, a₂, a₃, a₄, t])
    (.add (.var 0) (.var 3))
    (.add (.add (.add (.add .zero (.mul (.mul (.var 4) (.add .one .one)) (.add (.mul (.add .one .one) (.var 0)) (.var 1)))) (.mul (.neg (.var 4)) (.add (.add (.add (.mul (.add .one .one) (.var 0)) (.var 1)) (.add (.var 1) (.var 2))) (.add (.var 2) (.mul (.add .one .one) (.var 3)))))) (.mul (.mul (.var 4) (.add .one .one)) (.add (.var 2) (.mul (.add .one .one) (.var 3))))) (.mul (.neg (.add (.var 0) (.var 3))) (.add (.mul (.add .one .one) (.var 4)) (.neg .one)))) (by decide +kernel)

theorem line_a2 (a₁ a₂ a₄ : Shell p) :
    a₂ = (1 + 1) * a₄ + 1 * ((1 + 1) * a₁ + a₂) + (-(1 + 1)) * (a₁ + a₄) :=
  RE.sound (look [a₁, a₂, a₄])
    (.var 1)
    (.add (.add (.mul (.add .one .one) (.var 2)) (.mul .one (.add (.mul (.add .one .one) (.var 0)) (.var 1)))) (.mul (.neg (.add .one .one)) (.add (.var 0) (.var 2)))) (by decide +kernel)

/-- 00:E1, 21:C9 — spin 2 over all symbols: when `2` and the metric entries `η₀`, `η₁` are units (`n ≥ 2`), the
combinations gauge invariant at every symbol, for every symmetric field and every gauge vector, are exactly the
Fierz–Pauli line `(a₁, a₂, a₃, a₄) = c (−1, 2, −2, 1)`. -/
theorem fierz_pauli_unique (η : Nat → Shell p) {n : Nat} {w₀ w₁ t : Shell p} (hn : 1 < n) (h₀ : η 0 * w₀ = 1)
    (h₁ : η 1 * w₁ = 1) (h₂ : (1 + 1) * t = 1) (a₁ a₂ a₃ a₄ : Shell p) :
    (∀ (k ξ : Nat → Shell p) (h : Nat → Nat → Shell p), (∀ μ ν, h μ ν = h ν μ) →
        tensForm η n a₁ a₂ a₃ a₄ k (gauge h k ξ) = tensForm η n a₁ a₂ a₃ a₄ k h) ↔
      ∃ c : Shell p, a₁ = -c ∧ a₂ = (1 + 1) * c ∧ a₃ = -((1 + 1) * c) ∧ a₄ = c := by
  constructor
  · intro hinv
    have v := fun (k ξ : Nat → Shell p) (h : Nat → Nat → Shell p) (hs : ∀ μ ν, h μ ν = h ν μ) =>
      var_zero ((tens_shift η n a₁ a₂ a₃ a₄ k ξ hs).symm.trans (hinv k ξ h hs))
    have hn0 : 0 < n := Nat.lt_trans (Nat.zero_lt_succ 0) hn
    have v1 := v (basis 0) (basis 1) zero2 (fun _ _ => rfl)
    rw [dot_basis_self η hn0, dot_basis_self η hn, dot_basis_ne η n (i := 0) (j := 1) (by decide), ctr_zero2,
      ctr_zero2, tr_zero2] at v1
    have c₁ := cancel3 ((t1_ring _ _ _ _ _).symm.trans v1) h₀ h₀ h₁
    have v2 := v (basis 0) (basis 0) zero2 (fun _ _ => rfl)
    rw [dot_basis_self η hn0, ctr_zero2, tr_zero2] at v2
    have s := cancel4 ((t2_ring _ _ _ _).symm.trans v2) h₂ h₀ h₀ h₀
    have v3 := v (basis 0) (basis 0) unit11 (fun μ ν => mul_comm _ _)
    rw [dot_basis_self η hn0, ctr_unit11, tr_unit11 η hn] at v3
    have v3' := (t3_ring _ _ _ _ _).symm.trans v3
    rw [s, zero_mul, zero_add] at v3'
    have c₃ := cancel4 v3' h₂ h₀ h₀ h₁
    have h14 : a₁ + a₄ = 0 := lc4 (line_a1 a₁ a₂ a₃ a₄ t) c₁ s c₃ (sub_one_zero h₂)
    exact ⟨a₄, eq_neg_of_add_eq_zero h14, lc2 (line_a2 a₁ a₂ a₄) c₁ h14, eq_neg_of_add_eq_zero c₃, rfl⟩
  · intro ⟨c, e₁, e₂, e₃, e₄⟩ k ξ h hs
    rw [e₁, e₂, e₃, e₄]
    exact fierz_pauli_invariant η n c k ξ hs

/-- The hypothesis on `2` cannot be dropped: on the shell of two residues, `k² ⟨h, h⟩` alone is gauge invariant, and
it is not on the Fierz–Pauli line. -/
theorem char_two_not_unique (η : Nat → Shell 2) (n : Nat) :
    (∀ (k ξ : Nat → Shell 2) (h : Nat → Nat → Shell 2), (∀ μ ν, h μ ν = h ν μ) →
        tensForm η n 1 0 0 0 k (gauge h k ξ) = tensForm η n 1 0 0 0 k h) ∧
      ¬ ∃ c : Shell 2, (1 : Shell 2) = -c ∧ (0 : Shell 2) = (1 + 1) * c ∧ (0 : Shell 2) = -((1 + 1) * c) ∧
        (0 : Shell 2) = c := by
  constructor
  · intro k ξ h hs
    rw [tens_shift η n 1 0 0 0 k ξ hs]
    have e₁ : (1 + 1) * (1 : Shell 2) + 0 = 0 := by decide
    have e₂ : (0 : Shell 2) + 0 = 0 := by decide
    have e₃ : (0 : Shell 2) + (1 + 1) * 0 = 0 := by decide
    rw [e₁, e₂, e₃, zero_mul, zero_mul, zero_mul, add_zero, add_zero, add_zero]
  · intro ⟨c, e₁, _, _, e₄⟩
    rw [← e₄] at e₁
    exact absurd e₁ (by decide)

end FRC.Symbol
