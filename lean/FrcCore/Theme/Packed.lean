import FrcCore.Nat

/-!
# The packed arithmetic of the kernel-decided witnesses — rows as one natural number, no axioms

The first file of the operator theme (6 November 2026). A kernel-decided witness on a cycle of `p` sites or on an
`n × n` matrix over the coefficient field costs the kernel one reduction step per field operation, and the kernel keeps
every intermediate term: the powers of the translation on the 173-cycle, evaluated on lists of field elements, exhausted
six gigabytes (`reports/core-proofs-20261105/execution.md`). Here a row of residues is packed into one natural number with
slots of `W = 48` bits, `pack [a₀, a₁, …] = a₀ + B a₁ + B² a₂ + …` with `B = 2^W`; the product of two packed rows is one
multiplication of natural numbers, which the kernel performs in one step on its big-number representation; the acyclic
convolution of the rows is read off the product's slots, and the cyclic one by adding the high half of the slots to the
low half, one addition more; the residues modulo `p` are taken on unpacking, slot by slot. A product that costs the kernel
`n²` field multiplications on lists costs it about `4n` operations on packed rows, and the memory follows.

The file states the arithmetic on lists (`aconv`, the acyclic convolution; `cfold`, the cyclic fold; `combo`, a linear
combination of rows — the convolution of a cycle and the rows of a matrix product), the same arithmetic on packed numbers
(`packFold`, `unpack`), and proves them equal: `pack` is linear (`pack_smul`, `pack_addL`), turns the acyclic convolution
into the product (`pack_aconv`) and the cyclic fold into the fold of the number (`packFold_pack`), and `unpack` inverts
`pack` on bounded rows (`unpack_pack`) — the slot bound is the one hypothesis, and the bound of a convolution of residues
is computed (`aconv_bound`, `cfold_bound`). The division algorithm for `/` is proved from the definition of `Nat.div`, as
the base theme proves it for `%`, so that nothing here needs the standard library's division lemmas. No axioms.
-/

namespace FRC.Dirac.Packed

/-! ## The division algorithm for `/`, from the definition of `Nat.div` -/
section div

theorem div_go_fuel {y : Nat} (hy : 0 < y) : ∀ (f1 f2 x : Nat) (h1 : x < f1) (h2 : x < f2),
    Nat.div.go y hy f1 x h1 = Nat.div.go y hy f2 x h2 := by
  intro f1
  induction f1 with
  | zero => intro f2 x h1; exact absurd h1 (Nat.not_lt_zero x)
  | succ f1 ih =>
    intro f2 x h1 h2
    cases f2 with
    | zero => exact absurd h2 (Nat.not_lt_zero x)
    | succ f2 =>
      show (if h : y ≤ x then Nat.div.go y hy f1 (x - y) _ + 1 else 0)
          = (if h : y ≤ x then Nat.div.go y hy f2 (x - y) _ + 1 else 0)
      exact match Nat.decLe y x with
        | .isTrue h => by rw [dite_eq_left h, dite_eq_left h, ih f2 (x - y) _ _]
        | .isFalse h => by rw [dite_eq_right h, dite_eq_right h]

theorem div_eq' (x y : Nat) (hy : 0 < y) : x / y = if y ≤ x then (x - y) / y + 1 else 0 := by
  show Nat.div x y = _
  unfold Nat.div
  rw [dite_eq_left hy]
  show (if h : y ≤ x then Nat.div.go y hy x (x - y) _ + 1 else 0) = _
  exact match Nat.decLe y x with
    | .isTrue h => by
        rw [dite_eq_left h, ite_eq_left h]
        show _ = Nat.div (x - y) y + 1
        unfold Nat.div
        rw [dite_eq_left hy, div_go_fuel hy x (x - y + 1) (x - y) _ _]
    | .isFalse h => by rw [dite_eq_right h, ite_eq_right h]

/-- The division algorithm: `x = y (x / y) + x % y`. -/
theorem div_add_mod' (y : Nat) (hy : 0 < y) : ∀ x : Nat, x = y * (x / y) + x % y := by
  intro x
  induction x using Nat.strongRecOn with
  | _ x ih =>
    exact match Nat.decLe y x with
      | .isTrue h => by
          rw [div_eq' x y hy, ite_eq_left h, FRC.Nat.mod_eq_sub_mod hy h, Nat.mul_succ, Nat.add_assoc,
            Nat.add_comm y, ← Nat.add_assoc, ← ih (x - y) (Nat.sub_lt (Nat.lt_of_lt_of_le hy h) hy),
            FRC.Nat.sub_add_cancel h]
      | .isFalse h => by
          rw [div_eq' x y hy, ite_eq_right h, FRC.Nat.mod_eq_of_lt (Nat.lt_of_not_le h), Nat.mul_zero, Nat.zero_add]

/-- The quotient is determined: `x = y q + r` with `r < y` gives `x / y = q`. -/
theorem div_unique {y x q r : Nat} (hr : r < y) (h : x = y * q + r) : x / y = q :=
  FRC.Nat.quot_unique (Nat.mod_lt x (FRC.Nat.pos_of_lt hr)) hr (by rw [← div_add_mod' y (FRC.Nat.pos_of_lt hr) x, ← h])

theorem div_eq_of_lt {x y : Nat} (h : x < y) : x / y = 0 :=
  div_unique h (by rw [Nat.mul_zero, Nat.zero_add])

/-- `(r + y q) / y = q` and `(r + y q) % y = r` for `r < y`. -/
theorem add_mul_div {y q r : Nat} (hr : r < y) : (r + y * q) / y = q :=
  div_unique hr (Nat.add_comm _ _)

theorem add_mul_mod {y q r : Nat} (hr : r < y) : (r + y * q) % y = r :=
  FRC.Nat.mod_unique hr (Nat.add_comm _ _)

end div

/-! ## The slots -/

/-- The slot width, in bits, and the base `B = 2^W`: a slot holds every residue sum the witnesses form (the bound
`cfold_bound`: `2 n p³ < B` on every standard shell, `2 · 1549⁴ < 2⁴⁸`). -/
def W : Nat := 48
def B : Nat := 2 ^ W

theorem B_pos : 0 < B := Nat.pow_pos (by decide)

/-- A row packed into one natural number: `pack [a₀, a₁, …] = a₀ + B (a₁ + B (…))`. -/
def pack : List Nat → Nat
  | [] => 0
  | x :: l => x + B * pack l

/-- The `k` slots of a natural number, each reduced modulo `p`. -/
def unpack (p : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, P => P % B % p :: unpack p k (P / B)

/-- The entries of a row are below `B`. -/
def Bounded : List Nat → Prop
  | [] => True
  | x :: l => x < B ∧ Bounded l

/-- `pack` inverts `unpack` on bounded rows, up to the residues: the slots are the entries modulo `p`. -/
theorem unpack_pack (p : Nat) : ∀ l : List Nat, Bounded l → unpack p l.length (pack l) = l.map (· % p)
  | [], _ => rfl
  | x :: l, ⟨hx, hl⟩ => by
    show (x + B * pack l) % B % p :: unpack p l.length ((x + B * pack l) / B) = x % p :: l.map (· % p)
    rw [add_mul_mod hx, add_mul_div hx, unpack_pack p l hl]

theorem pack_lt : ∀ l : List Nat, Bounded l → pack l < B ^ l.length
  | [], _ => Nat.lt_succ_self 0
  | x :: l, ⟨hx, hl⟩ => by
    show x + B * pack l < B ^ (l.length + 1)
    have h1 : pack l + 1 ≤ B ^ l.length := pack_lt l hl
    calc x + B * pack l < B + B * pack l := Nat.add_lt_add_right hx _
      _ = B * (pack l + 1) := by rw [Nat.mul_succ, Nat.add_comm]
      _ ≤ B * B ^ l.length := Nat.mul_le_mul_left B h1
      _ = B ^ (l.length + 1) := by rw [FRC.Nat.pow_succ', Nat.mul_comm]

/-! ## Linearity: scalar multiples, sums and the acyclic convolution -/

/-- `c · l`, entrywise. -/
def smul (c : Nat) (l : List Nat) : List Nat := l.map (c * ·)

/-- `u + v`, entrywise, the shorter row padded with zeros. -/
def addL : List Nat → List Nat → List Nat
  | [], v => v
  | u, [] => u
  | x :: u, y :: v => (x + y) :: addL u v

/-- The acyclic convolution (the product of the rows as polynomials): `(x :: a) * b = x b + (0 :: a * b)`. -/
def aconv : List Nat → List Nat → List Nat
  | [], _ => []
  | x :: a, b => addL (smul x b) (0 :: aconv a b)

theorem pack_smul (c : Nat) : ∀ l : List Nat, pack (smul c l) = c * pack l
  | [] => by show 0 = c * 0; rw [Nat.mul_zero]
  | x :: l => by
    show c * x + B * pack (smul c l) = c * (x + B * pack l)
    rw [pack_smul c l, Nat.mul_add, FRC.Nat.mul_left_comm]

theorem pack_addL : ∀ u v : List Nat, pack (addL u v) = pack u + pack v
  | [], v => by show pack v = 0 + pack v; rw [Nat.zero_add]
  | x :: u, [] => by show pack (x :: u) = pack (x :: u) + 0; rw [Nat.add_zero]
  | x :: u, y :: v => by
    show x + y + B * pack (addL u v) = x + B * pack u + (y + B * pack v)
    rw [pack_addL u v, Nat.mul_add, Nat.add_assoc, Nat.add_assoc, Nat.add_left_comm y]

/-- The product of the packed rows is the packed acyclic convolution. -/
theorem pack_aconv : ∀ a b : List Nat, pack (aconv a b) = pack a * pack b
  | [], b => by show 0 = 0 * pack b; rw [Nat.zero_mul]
  | x :: a, b => by
    show pack (addL (smul x b) (0 :: aconv a b)) = (x + B * pack a) * pack b
    rw [pack_addL, pack_smul]
    show x * pack b + (0 + B * pack (aconv a b)) = _
    rw [Nat.zero_add, pack_aconv a b, Nat.add_mul, Nat.mul_assoc]

/-! ## The cyclic fold -/

/-- The cyclic fold of a row of `2n − 1` (or `2n`) entries to `n`: the high half added to the low half, the
convolution on the cycle of `n` sites from the acyclic one. -/
def cfold (n : Nat) (c : List Nat) : List Nat := addL (c.take n) (c.drop n)

/-- The same on a packed row: the high slots are `P / Bⁿ`, the low ones `P % Bⁿ`. -/
def packFold (n P : Nat) : Nat := P % B ^ n + P / B ^ n

theorem pack_take_drop : ∀ (n : Nat) (c : List Nat), pack c = pack (c.take n) + B ^ n * pack (c.drop n)
  | 0, c => by show pack c = 0 + 1 * pack c; rw [Nat.zero_add, Nat.one_mul]
  | n + 1, [] => by show 0 = 0 + B ^ (n + 1) * 0; rw [Nat.mul_zero]
  | n + 1, x :: c => by
    show x + B * pack c = x + B * pack (c.take n) + B ^ (n + 1) * pack (c.drop n)
    rw [pack_take_drop n c, Nat.mul_add, Nat.add_assoc, FRC.Nat.pow_succ', Nat.mul_comm (B ^ n) B, Nat.mul_assoc]

theorem bounded_take : ∀ (n : Nat) (c : List Nat), Bounded c → Bounded (c.take n)
  | 0, _, _ => trivial
  | _ + 1, [], _ => trivial
  | n + 1, _ :: c, ⟨hx, hc⟩ => ⟨hx, bounded_take n c hc⟩

theorem length_take_le : ∀ (n : Nat) (c : List Nat), (c.take n).length ≤ n
  | 0, _ => Nat.le_refl 0
  | _ + 1, [] => Nat.zero_le _
  | n + 1, _ :: c => Nat.succ_le_succ (length_take_le n c)

theorem pow_le_pow_of_le {m n : Nat} (h : m ≤ n) : B ^ m ≤ B ^ n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = m + k := ⟨n - m, by rw [Nat.add_comm, FRC.Nat.sub_add_cancel h]⟩
  rw [FRC.Nat.pow_add]
  exact Nat.le_mul_of_pos_right _ (Nat.pow_pos B_pos)

/-- The fold of the packed row is the packed fold, for a bounded row. -/
theorem packFold_pack (n : Nat) (c : List Nat) (hc : Bounded c) : packFold n (pack c) = pack (cfold n c) := by
  have hlt : pack (c.take n) < B ^ n :=
    Nat.lt_of_lt_of_le (pack_lt _ (bounded_take n c hc)) (pow_le_pow_of_le (length_take_le n c))
  show pack c % B ^ n + pack c / B ^ n = pack (addL (c.take n) (c.drop n))
  rw [pack_addL, pack_take_drop n c, add_mul_mod hlt, add_mul_div hlt]

/-! ## The combination of rows (the rows of a matrix product) -/

/-- `Σ_k c_k · r_k`: a row of the product of a matrix with the rows `r` is the combination of the rows by the entries. -/
def combo : List Nat → List (List Nat) → List Nat
  | [], _ => []
  | _, [] => []
  | c :: cs, r :: rs => addL (smul c r) (combo cs rs)

/-- The same on packed rows. -/
def packCombo : List Nat → List Nat → Nat
  | [], _ => 0
  | _, [] => 0
  | c :: cs, P :: Ps => c * P + packCombo cs Ps

theorem pack_combo : ∀ (cs : List Nat) (rs : List (List Nat)), pack (combo cs rs) = packCombo cs (rs.map pack)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | c :: cs, r :: rs => by
    show pack (addL (smul c r) (combo cs rs)) = c * pack r + packCombo cs (rs.map pack)
    rw [pack_addL, pack_smul, pack_combo cs rs]

/-! ## The bounds -/

/-- The entries of a row are below `m`. -/
def Below (m : Nat) : List Nat → Prop
  | [] => True
  | x :: l => x < m ∧ Below m l

theorem below_mono {m m' : Nat} (h : m ≤ m') : ∀ l, Below m l → Below m' l
  | [], _ => trivial
  | _ :: l, ⟨hx, hl⟩ => ⟨Nat.lt_of_lt_of_le hx h, below_mono h l hl⟩

/-- The entries of `u + v` are below `m + m'` when those of `u` are below `m` and those of `v` below `m'`
(`0 < m`, `0 < m'` for the padded tails). -/
theorem below_addL {m m' : Nat} (hm : 0 < m) (hm' : 0 < m') :
    ∀ u v, Below m u → Below m' v → Below (m + m') (addL u v)
  | [], v, _, hv => below_mono (Nat.le_add_left m' m) v hv
  | _ :: _, [], hu, _ => below_mono (Nat.le_add_right m m') _ hu
  | _ :: u, _ :: v, ⟨hx, hu⟩, ⟨hy, hv⟩ => ⟨Nat.add_lt_add hx hy, below_addL hm hm' u v hu hv⟩

theorem below_smul {c m m' : Nat} (hc : c < m) : ∀ l, Below m' l → Below (m * m') (smul c l)
  | [], _ => trivial
  | _ :: l, ⟨hx, hl⟩ => ⟨Nat.mul_lt_mul_of_lt_of_lt hc hx, below_smul hc l hl⟩

theorem below_zero_cons {m : Nat} (hm : 0 < m) {l : List Nat} (h : Below m l) : Below m (0 :: l) := ⟨hm, h⟩

/-- The acyclic convolution of two rows of residues below `p`, the first of `k` entries, has entries below `k p²`. -/
theorem aconv_bound {p : Nat} (hp : 0 < p) : ∀ (a b : List Nat), Below p a → Below p b →
    Below (a.length * (p * p) + 1) (aconv a b)
  | [], _, _, _ => trivial
  | x :: a, b, ⟨hx, ha⟩, hb => by
    show Below ((a.length + 1) * (p * p) + 1) (addL (smul x b) (0 :: aconv a b))
    have h1 : Below (p * p) (smul x b) := below_smul hx b hb
    have h2 : Below (a.length * (p * p) + 1) (0 :: aconv a b) :=
      below_zero_cons (Nat.succ_pos _) (aconv_bound hp a b ha hb)
    have := below_addL (Nat.mul_pos hp hp) (Nat.succ_pos _) _ _ h1 h2
    rw [Nat.succ_mul, Nat.add_comm (a.length * (p * p)) (p * p), Nat.add_assoc]
    exact this

theorem below_take {m : Nat} : ∀ (n : Nat) (c : List Nat), Below m c → Below m (c.take n)
  | 0, _, _ => trivial
  | _ + 1, [], _ => trivial
  | n + 1, _ :: c, ⟨hx, hc⟩ => ⟨hx, below_take n c hc⟩

theorem below_drop {m : Nat} : ∀ (n : Nat) (c : List Nat), Below m c → Below m (c.drop n)
  | 0, _, h => h
  | _ + 1, [], _ => trivial
  | n + 1, _ :: c, ⟨_, hc⟩ => below_drop n c hc

/-- The cyclic fold of a row with entries below `m` has entries below `2m`. -/
theorem cfold_bound {m : Nat} (hm : 0 < m) (n : Nat) (c : List Nat) (h : Below m c) : Below (m + m) (cfold n c) :=
  below_addL hm hm _ _ (below_take n c h) (below_drop n c h)

theorem bounded_of_below {m : Nat} (hm : m ≤ B) : ∀ l, Below m l → Bounded l
  | [], _ => trivial
  | _ :: l, ⟨hx, hl⟩ => ⟨Nat.lt_of_lt_of_le hx hm, bounded_of_below hm l hl⟩

/-! ## The cyclic convolution of residues: the list form, the packed form, and their equality -/

/-- The cyclic convolution of two rows of residues on the cycle of `n` sites, reduced modulo `p`: the list form. -/
def cycList (p n : Nat) (a b : List Nat) : List Nat := (cfold n (aconv a b)).map (· % p)

/-- The packed form: one product, one fold, `n` slots. -/
def cycPacked (p n : Nat) (A C : Nat) : List Nat := unpack p n (packFold n (A * C))

theorem length_addL_left : ∀ u v : List Nat, v.length ≤ u.length → (addL u v).length = u.length
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h (Nat.not_succ_le_zero _)
  | _ :: _, [], _ => rfl
  | _ :: u, _ :: v, h => by
    show (addL u v).length + 1 = u.length + 1
    rw [length_addL_left u v (Nat.le_of_succ_le_succ h)]

theorem length_addL_right : ∀ u v : List Nat, u.length ≤ v.length → (addL u v).length = v.length
  | [], _, _ => rfl
  | _ :: _, [], h => absurd h (Nat.not_succ_le_zero _)
  | _ :: u, _ :: v, h => by
    show (addL u v).length + 1 = v.length + 1
    rw [length_addL_right u v (Nat.le_of_succ_le_succ h)]

theorem length_smul (c : Nat) : ∀ l : List Nat, (smul c l).length = l.length
  | [] => rfl
  | _ :: l => by show (smul c l).length + 1 = l.length + 1; rw [length_smul c l]

/-- `|a * b| + 1 = |a| + |b|` for nonempty rows. -/
theorem length_aconv : ∀ a b : List Nat, 0 < a.length → 0 < b.length → (aconv a b).length + 1 = a.length + b.length
  | [], _, h, _ => absurd h (Nat.lt_irrefl 0)
  | [x], b, _, hb => by
    show (addL (smul x b) (0 :: aconv [] b)).length + 1 = 1 + b.length
    rw [length_addL_left _ _ (by rw [length_smul]; exact hb), length_smul, Nat.add_comm]
  | x :: y :: a, b, _, hb => by
    show (addL (smul x b) (0 :: aconv (y :: a) b)).length + 1 = a.length + 1 + 1 + b.length
    have ih := length_aconv (y :: a) b (Nat.succ_pos _) hb
    have hle : (smul x b).length ≤ (0 :: aconv (y :: a) b).length := by
      show (smul x b).length ≤ (aconv (y :: a) b).length + 1
      rw [length_smul, ih]; exact Nat.le_add_left _ _
    rw [length_addL_right _ _ hle]
    show (aconv (y :: a) b).length + 1 + 1 = a.length + 1 + 1 + b.length
    rw [ih]; show a.length + 1 + b.length + 1 = _; rw [Nat.add_right_comm]

theorem length_take_of_le : ∀ (n : Nat) (c : List Nat), n ≤ c.length → (c.take n).length = n
  | 0, _, _ => rfl
  | _ + 1, [], h => absurd h (Nat.not_succ_le_zero _)
  | n + 1, _ :: c, h => by show (c.take n).length + 1 = n + 1; rw [length_take_of_le n c (Nat.le_of_succ_le_succ h)]

theorem length_drop : ∀ (n : Nat) (c : List Nat), (c.drop n).length = c.length - n
  | 0, _ => rfl
  | n + 1, [] => by show 0 = 0 - (n + 1); rw [Nat.zero_sub]
  | n + 1, _ :: c => by show (c.drop n).length = c.length + 1 - (n + 1); rw [length_drop n c, Nat.succ_sub_succ]

/-- The fold of a row of `2n − 1` entries has `n` entries. -/
theorem length_cfold (n : Nat) (c : List Nat) (hc : c.length + 1 = n + n) : (cfold n c).length = n := by
  have hn : n ≤ c.length := by
    have : n + 1 ≤ c.length + 1 := by
      rw [hc]
      cases n with
      | zero => exact absurd hc (by rw [Nat.add_zero]; exact Nat.succ_ne_zero _)
      | succ n => exact Nat.succ_le_succ (Nat.le_add_right (n + 1) n)
    exact Nat.le_of_succ_le_succ this
  have hd : (c.drop n).length ≤ (c.take n).length := by
    rw [length_drop, length_take_of_le n c hn]
    have e : c.length = n + (n - 1) := by
      cases n with
      | zero => exact absurd hc (by rw [Nat.add_zero]; exact Nat.succ_ne_zero _)
      | succ n =>
        have : c.length + 1 = n + 1 + (n + 1 - 1) + 1 := by rw [hc, Nat.add_sub_cancel]; rfl
        exact Nat.succ.inj this
    rw [e, FRC.Nat.add_sub_cancel_left]
    exact Nat.sub_le n 1
  show (addL (c.take n) (c.drop n)).length = n
  rw [length_addL_left _ _ hd, length_take_of_le n c hn]

/-- The packed cyclic convolution of rows of residues below `p`, each of `n` entries, is the list form, when
`2 n p² ≤ B`: the one bound of the method. -/
theorem cycPacked_eq (p n : Nat) (hp : 0 < p) (hn : 0 < n) (a b : List Nat) (ha : Below p a) (hb : Below p b)
    (la : a.length = n) (lb : b.length = n) (hB : 2 * (n * (p * p) + 1) ≤ B) :
    cycPacked p n (pack a) (pack b) = cycList p n a b := by
  have hc : Below (n * (p * p) + 1) (aconv a b) := la ▸ aconv_bound hp a b ha hb
  have hf : Below (n * (p * p) + 1 + (n * (p * p) + 1)) (cfold n (aconv a b)) :=
    cfold_bound (Nat.succ_pos _) n _ hc
  have hB' : n * (p * p) + 1 + (n * (p * p) + 1) ≤ B := by rw [← Nat.two_mul]; exact hB
  have hbnd : Bounded (cfold n (aconv a b)) := bounded_of_below hB' _ hf
  have hbndc : Bounded (aconv a b) :=
    bounded_of_below (Nat.le_trans (Nat.le_add_right _ _) hB') _ hc
  have hlen : (cfold n (aconv a b)).length = n :=
    length_cfold n _ (by rw [length_aconv a b (la ▸ hn) (lb ▸ hn), la, lb])
  show unpack p n (packFold n (pack a * pack b)) = (cfold n (aconv a b)).map (· % p)
  rw [← pack_aconv, packFold_pack n _ hbndc, ← unpack_pack p _ hbnd, hlen]

/-! ## Rows over the quadratic extension: pairs of rows of residues -/

/-- The cyclic convolution over `K = 𝔽_p(√ν)` on the cycle of `n` sites, the list form: with `a = a₁ + a₂ w` and
`b = b₁ + b₂ w` (rows of residues), `ab = (a₁b₁ + ν a₂b₂) + (a₁b₂ + a₂b₁) w`. -/
def cycExtList (p ν n : Nat) (a b : List Nat × List Nat) : List Nat × List Nat :=
  ((cfold n (addL (aconv a.1 b.1) (smul ν (aconv a.2 b.2)))).map (· % p),
   (cfold n (addL (aconv a.1 b.2) (aconv a.2 b.1))).map (· % p))

/-- The packed form: four products of natural numbers, two folds, `2n` slots. -/
def cycExtPacked (p ν n : Nat) (A C : Nat × Nat) : List Nat × List Nat :=
  (unpack p n (packFold n (A.1 * C.1 + ν * (A.2 * C.2))), unpack p n (packFold n (A.1 * C.2 + A.2 * C.1)))

/-- A pair of rows of residues below `p`, each of `n` entries. -/
def Row (p n : Nat) (a : List Nat × List Nat) : Prop :=
  Below p a.1 ∧ Below p a.2 ∧ a.1.length = n ∧ a.2.length = n

theorem length_aconv' {n : Nat} (hn : 0 < n) {a b : List Nat} (la : a.length = n) (lb : b.length = n) :
    (aconv a b).length + 1 = n + n := by rw [length_aconv a b (la ▸ hn) (lb ▸ hn), la, lb]

theorem length_smul_aconv {n : Nat} (hn : 0 < n) (c : Nat) {a b : List Nat} (la : a.length = n) (lb : b.length = n) :
    (smul c (aconv a b)).length + 1 = n + n := by rw [length_smul, length_aconv' hn la lb]

theorem length_addL_eq {u v : List Nat} {k : Nat} (hu : u.length = k) (hv : v.length = k) : (addL u v).length = k := by
  rw [length_addL_left u v (by rw [hu, hv]; exact Nat.le_refl k), hu]

theorem length_addL_eq' {u v : List Nat} {m : Nat} (hu : u.length + 1 = m) (hv : v.length + 1 = m) :
    (addL u v).length + 1 = m := by
  have e : v.length = u.length := Nat.succ.inj (hv.trans hu.symm)
  rw [length_addL_left u v (e ▸ Nat.le_refl _), hu]

/-- The bound of a term `aconv` or `ν · aconv`: below `p (n p² + 1)`. -/
theorem below_aconv_term {p ν n : Nat} (hp : 0 < p) (hν : ν < p) {a b : List Nat} (ha : Below p a) (hb : Below p b)
    (la : a.length = n) : Below (p * (n * (p * p) + 1)) (smul ν (aconv a b)) :=
  below_smul hν _ (la ▸ aconv_bound hp a b ha hb)

theorem below_aconv_one {p n : Nat} (hp : 0 < p) {a b : List Nat} (ha : Below p a) (hb : Below p b)
    (la : a.length = n) : Below (p * (n * (p * p) + 1)) (aconv a b) :=
  below_mono (Nat.le_mul_of_pos_left _ hp) _ (la ▸ aconv_bound hp a b ha hb)

/-- The packed cyclic convolution over `K` of two rows is the list form, when `4 p (n p² + 1) ≤ B`: the one bound of
the method on the extension. -/
theorem cycExtPacked_eq (p ν n : Nat) (hp : 0 < p) (hν : ν < p) (hn : 0 < n) (a b : List Nat × List Nat)
    (ha : Row p n a) (hb : Row p n b) (hB : 4 * (p * (n * (p * p) + 1)) ≤ B) :
    cycExtPacked p ν n (pack a.1, pack a.2) (pack b.1, pack b.2) = cycExtList p ν n a b := by
  obtain ⟨ha1, ha2, la1, la2⟩ := ha
  obtain ⟨hb1, hb2, lb1, lb2⟩ := hb
  have hm : 0 < p * (n * (p * p) + 1) := Nat.mul_pos hp (Nat.succ_pos _)
  have h2 : p * (n * (p * p) + 1) + p * (n * (p * p) + 1) + (p * (n * (p * p) + 1) + p * (n * (p * p) + 1)) ≤ B := by
    have e : 4 * (p * (n * (p * p) + 1)) =
        p * (n * (p * p) + 1) + p * (n * (p * p) + 1) + (p * (n * (p * p) + 1) + p * (n * (p * p) + 1)) := by
      rw [show (4 : Nat) = 2 + 2 from rfl, Nat.add_mul, Nat.two_mul]
    rw [← e]; exact hB
  have hhalf : p * (n * (p * p) + 1) + p * (n * (p * p) + 1) ≤ B :=
    Nat.le_trans (Nat.le_add_right _ _) h2
  -- the real part
  have hre : Below (p * (n * (p * p) + 1) + p * (n * (p * p) + 1))
      (addL (aconv a.1 b.1) (smul ν (aconv a.2 b.2))) :=
    below_addL hm hm _ _ (below_aconv_one hp ha1 hb1 la1) (below_aconv_term hp hν ha2 hb2 la2)
  have lre : (addL (aconv a.1 b.1) (smul ν (aconv a.2 b.2))).length + 1 = n + n :=
    length_addL_eq' (length_aconv' hn la1 lb1) (length_smul_aconv hn ν la2 lb2)
  have him : Below (p * (n * (p * p) + 1) + p * (n * (p * p) + 1)) (addL (aconv a.1 b.2) (aconv a.2 b.1)) :=
    below_addL hm hm _ _ (below_aconv_one hp ha1 hb2 la1) (below_aconv_one hp ha2 hb1 la2)
  have lim : (addL (aconv a.1 b.2) (aconv a.2 b.1)).length + 1 = n + n :=
    length_addL_eq' (length_aconv' hn la1 lb2) (length_aconv' hn la2 lb1)
  show (unpack p n (packFold n (pack a.1 * pack b.1 + ν * (pack a.2 * pack b.2))),
      unpack p n (packFold n (pack a.1 * pack b.2 + pack a.2 * pack b.1))) =
    ((cfold n (addL (aconv a.1 b.1) (smul ν (aconv a.2 b.2)))).map (· % p),
     (cfold n (addL (aconv a.1 b.2) (aconv a.2 b.1))).map (· % p))
  rw [← pack_aconv, ← pack_aconv, ← pack_aconv, ← pack_aconv, ← pack_smul, ← pack_addL, ← pack_addL,
    packFold_pack n _ (bounded_of_below hhalf _ hre), packFold_pack n _ (bounded_of_below hhalf _ him),
    ← unpack_pack p _ (bounded_of_below h2 _ (cfold_bound (Nat.add_pos_left hm _) n _ hre)), length_cfold n _ lre,
    ← unpack_pack p _ (bounded_of_below h2 _ (cfold_bound (Nat.add_pos_left hm _) n _ him)), length_cfold n _ lim]

/-! ## The rows kept packed: the slot-wise reduction by halving -/

/-- The slot-wise reduction modulo `p` of a packed row of at most sixteen slots, written out: the kernel evaluates
these sixteen quotients and residues without unfolding a recursion (`leaf16_eq`: it is `pack (unpack p 16 P)`). -/
def leaf16 (p P : Nat) : Nat :=
  let P1 := P / B
  let P2 := P1 / B
  let P3 := P2 / B
  let P4 := P3 / B
  let P5 := P4 / B
  let P6 := P5 / B
  let P7 := P6 / B
  let P8 := P7 / B
  let P9 := P8 / B
  let P10 := P9 / B
  let P11 := P10 / B
  let P12 := P11 / B
  let P13 := P12 / B
  let P14 := P13 / B
  let P15 := P14 / B
  P % B % p + B * (P1 % B % p + B * (P2 % B % p + B * (P3 % B % p + B * (P4 % B % p + B * (P5 % B % p + B * (P6 % B % p + B * (P7 % B % p + B * (P8 % B % p + B * (P9 % B % p + B * (P10 % B % p + B * (P11 % B % p + B * (P12 % B % p + B * (P13 % B % p + B * (P14 % B % p + B * (P15 % B % p + B * 0)))))))))))))))

theorem leaf16_eq (p P : Nat) : leaf16 p P = pack (unpack p 16 P) := rfl

/-- The slot-wise reduction modulo `p` of a packed row of at most `16 · 2^k` slots, by halving down to the leaves of
sixteen slots: the low and the high halves reduced and reassembled. A row stays packed between the products this
way; the slot-by-slot chain of `unpack` and `pack` would hold `n` growing numbers at a time, and the kernel, which
keeps every reduction step, would hold them all. -/
def repack (p : Nat) : Nat → Nat → Nat
  | 0, P => leaf16 p P
  | k + 1, P => repack p k (P % B ^ (16 * 2 ^ k)) + B ^ (16 * 2 ^ k) * repack p k (P / B ^ (16 * 2 ^ k))

theorem bounded_drop : ∀ (n : Nat) (c : List Nat), Bounded c → Bounded (c.drop n)
  | 0, _, h => h
  | _ + 1, [], _ => trivial
  | n + 1, _ :: c, ⟨_, hc⟩ => bounded_drop n c hc

theorem map_take (f : Nat → Nat) : ∀ (n : Nat) (l : List Nat), (l.take n).map f = (l.map f).take n
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | n + 1, x :: l => by show f x :: (l.take n).map f = f x :: (l.map f).take n; rw [map_take f n l]

theorem map_drop (f : Nat → Nat) : ∀ (n : Nat) (l : List Nat), (l.drop n).map f = (l.map f).drop n
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | n + 1, _ :: l => map_drop f n l

theorem pack_unpack_zero (p : Nat) : ∀ k : Nat, pack (unpack p k 0) = 0
  | 0 => rfl
  | k + 1 => by
    show 0 % B % p + B * pack (unpack p k (0 / B)) = 0
    rw [Nat.zero_mod, Nat.zero_mod, div_eq_of_lt B_pos, pack_unpack_zero p k, Nat.mul_zero]

/-- `unpack_pack` with spare slots: the slots past the row are zero and do not change the packed value. -/
theorem pack_unpack_pack (p : Nat) : ∀ (l : List Nat) (k : Nat), Bounded l → l.length ≤ k →
    pack (unpack p k (pack l)) = pack (l.map (· % p))
  | [], k, _, _ => pack_unpack_zero p k
  | _ :: _, 0, _, h => absurd h (Nat.not_succ_le_zero _)
  | x :: l, k + 1, ⟨hx, hl⟩, h => by
    show (x + B * pack l) % B % p + B * pack (unpack p k ((x + B * pack l) / B)) = x % p + B * pack (l.map (· % p))
    rw [add_mul_mod hx, add_mul_div hx, pack_unpack_pack p l k hl (Nat.le_of_succ_le_succ h)]

/-- `repack` is the packed slot-wise reduction: on a bounded row of at most `16 · 2^k` entries, the packed row of
the residues. -/
theorem repack_pack (p : Nat) : ∀ (k : Nat) (l : List Nat), Bounded l → l.length ≤ 16 * 2 ^ k →
    repack p k (pack l) = pack (l.map (· % p))
  | 0, l, hl, hlen => by
    show leaf16 p (pack l) = _
    rw [leaf16_eq]; exact pack_unpack_pack p l 16 hl hlen
  | k + 1, l, hl, hlen => by
    have hm : pack (l.take (16 * 2 ^ k)) < B ^ (16 * 2 ^ k) :=
      Nat.lt_of_lt_of_le (pack_lt _ (bounded_take _ l hl)) (pow_le_pow_of_le (length_take_le _ l))
    have h2 : (l.drop (16 * 2 ^ k)).length ≤ 16 * 2 ^ k := by
      rw [length_drop]
      rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_two] at hlen
      exact Nat.le_trans (Nat.sub_le_sub_right hlen _) (by rw [FRC.Nat.add_sub_cancel]; exact Nat.le_refl _)
    show repack p k (pack l % B ^ (16 * 2 ^ k)) + B ^ (16 * 2 ^ k) * repack p k (pack l / B ^ (16 * 2 ^ k)) =
      pack (l.map (· % p))
    rw [pack_take_drop (16 * 2 ^ k) l, add_mul_mod hm, add_mul_div hm,
      repack_pack p k _ (bounded_take _ l hl) (length_take_le _ l), repack_pack p k _ (bounded_drop _ l hl) h2,
      pack_take_drop (16 * 2 ^ k) (l.map (· % p)), map_take, map_drop]

/-- The product on the cycle of two packed real rows (rows of residues), the result reduced slot-wise on
`16 · 2^k ≥ n` slots: one product, one fold, one reduction. -/
def rmul (p n k : Nat) (A C : Nat) : Nat := repack p k (packFold n (A * C))

/-- `rmul` is the packed `cycList`, under the bound of `cycPacked_eq` and `n ≤ 16 · 2^k`. -/
theorem rmul_eq (p n k : Nat) (hp : 0 < p) (hn : 0 < n) (a b : List Nat) (ha : Below p a) (hb : Below p b)
    (la : a.length = n) (lb : b.length = n) (hB : 2 * (n * (p * p) + 1) ≤ B) (hk : n ≤ 16 * 2 ^ k) :
    rmul p n k (pack a) (pack b) = pack (cycList p n a b) := by
  have hc : Below (n * (p * p) + 1) (aconv a b) := la ▸ aconv_bound hp a b ha hb
  have hf : Below (n * (p * p) + 1 + (n * (p * p) + 1)) (cfold n (aconv a b)) :=
    cfold_bound (Nat.succ_pos _) n _ hc
  have hB' : n * (p * p) + 1 + (n * (p * p) + 1) ≤ B := by rw [← Nat.two_mul]; exact hB
  have hbndc : Bounded (aconv a b) :=
    bounded_of_below (Nat.le_trans (Nat.le_add_right _ _) hB') _ hc
  have hlen : (cfold n (aconv a b)).length = n :=
    length_cfold n _ (by rw [length_aconv a b (la ▸ hn) (lb ▸ hn), la, lb])
  show repack p k (packFold n (pack a * pack b)) = pack ((cfold n (aconv a b)).map (· % p))
  rw [← pack_aconv, packFold_pack n _ hbndc]
  exact repack_pack p k _ (bounded_of_below hB' _ hf) (by rw [hlen]; exact hk)

/-- The product on the cycle over `K` of two packed rows, the result reduced slot-wise on `16 · 2^k ≥ n` slots: four
products, two folds, two reductions, and the rows stay packed. -/
def pmul (p ν n k : Nat) (A C : Nat × Nat) : Nat × Nat :=
  (repack p k (packFold n (A.1 * C.1 + ν * (A.2 * C.2))), repack p k (packFold n (A.1 * C.2 + A.2 * C.1)))

/-- `pmul` is the packed `cycExtList`, under the bound of `cycExtPacked_eq` and `n ≤ 16 · 2^k`. -/
theorem pmul_eq (p ν n k : Nat) (hp : 0 < p) (hν : ν < p) (hn : 0 < n) (a b : List Nat × List Nat)
    (ha : Row p n a) (hb : Row p n b) (hB : 4 * (p * (n * (p * p) + 1)) ≤ B) (hk : n ≤ 16 * 2 ^ k) :
    pmul p ν n k (pack a.1, pack a.2) (pack b.1, pack b.2) =
      (pack (cycExtList p ν n a b).1, pack (cycExtList p ν n a b).2) := by
  obtain ⟨ha1, ha2, la1, la2⟩ := ha
  obtain ⟨hb1, hb2, lb1, lb2⟩ := hb
  have hm : 0 < p * (n * (p * p) + 1) := Nat.mul_pos hp (Nat.succ_pos _)
  have h2 : p * (n * (p * p) + 1) + p * (n * (p * p) + 1) + (p * (n * (p * p) + 1) + p * (n * (p * p) + 1)) ≤ B := by
    have e : 4 * (p * (n * (p * p) + 1)) =
        p * (n * (p * p) + 1) + p * (n * (p * p) + 1) + (p * (n * (p * p) + 1) + p * (n * (p * p) + 1)) := by
      rw [show (4 : Nat) = 2 + 2 from rfl, Nat.add_mul, Nat.two_mul]
    rw [← e]; exact hB
  have hhalf : p * (n * (p * p) + 1) + p * (n * (p * p) + 1) ≤ B :=
    Nat.le_trans (Nat.le_add_right _ _) h2
  have hre : Below (p * (n * (p * p) + 1) + p * (n * (p * p) + 1))
      (addL (aconv a.1 b.1) (smul ν (aconv a.2 b.2))) :=
    below_addL hm hm _ _ (below_aconv_one hp ha1 hb1 la1) (below_aconv_term hp hν ha2 hb2 la2)
  have lre : (addL (aconv a.1 b.1) (smul ν (aconv a.2 b.2))).length + 1 = n + n :=
    length_addL_eq' (length_aconv' hn la1 lb1) (length_smul_aconv hn ν la2 lb2)
  have him : Below (p * (n * (p * p) + 1) + p * (n * (p * p) + 1)) (addL (aconv a.1 b.2) (aconv a.2 b.1)) :=
    below_addL hm hm _ _ (below_aconv_one hp ha1 hb2 la1) (below_aconv_one hp ha2 hb1 la2)
  have lim : (addL (aconv a.1 b.2) (aconv a.2 b.1)).length + 1 = n + n :=
    length_addL_eq' (length_aconv' hn la1 lb2) (length_aconv' hn la2 lb1)
  show (repack p k (packFold n (pack a.1 * pack b.1 + ν * (pack a.2 * pack b.2))),
      repack p k (packFold n (pack a.1 * pack b.2 + pack a.2 * pack b.1))) =
    (pack ((cfold n (addL (aconv a.1 b.1) (smul ν (aconv a.2 b.2)))).map (· % p)),
     pack ((cfold n (addL (aconv a.1 b.2) (aconv a.2 b.1))).map (· % p)))
  rw [← pack_aconv, ← pack_aconv, ← pack_aconv, ← pack_aconv, ← pack_smul, ← pack_addL, ← pack_addL,
    packFold_pack n _ (bounded_of_below hhalf _ hre), packFold_pack n _ (bounded_of_below hhalf _ him),
    repack_pack p k _ (bounded_of_below h2 _ (cfold_bound (Nat.add_pos_left hm _) n _ hre))
      (by rw [length_cfold n _ lre]; exact hk),
    repack_pack p k _ (bounded_of_below h2 _ (cfold_bound (Nat.add_pos_left hm _) n _ him))
      (by rw [length_cfold n _ lim]; exact hk)]

/-- The sum of two packed rows, reduced slot-wise. -/
def padd (p k : Nat) (A C : Nat) : Nat := repack p k (A + C)

theorem padd_eq (p k : Nat) (hp : 0 < p) (a b : List Nat) (ha : Below p a) (hb : Below p b) (la : a.length ≤ 16 * 2 ^ k)
    (hab : b.length ≤ a.length) (hB : p + p ≤ B) : padd p k (pack a) (pack b) = pack ((addL a b).map (· % p)) := by
  show repack p k (pack a + pack b) = _
  rw [← pack_addL]
  exact repack_pack p k _ (bounded_of_below hB _ (below_addL hp hp a b ha hb))
    (by rw [length_addL_left a b hab]; exact la)

/-- The number of halvings that cover `n` slots: the least `k` with `n ≤ 2^k`, by halving `n` (its own fuel), and
the halvings above the leaves of sixteen slots, `16 · 2^(slots n) ≥ n`. -/
def slotsAux : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, n => if n ≤ 1 then 0 else slotsAux f ((n + 1) / 2) + 1
def slots (n : Nat) : Nat := slotsAux ((n + 15) / 16) ((n + 15) / 16)

theorem le_two_pow_slotsAux : ∀ (f n : Nat), n ≤ f → n ≤ 2 ^ slotsAux f n
  | 0, n, h => Nat.le_trans h (Nat.zero_le _)
  | f + 1, n, h => by
    show n ≤ 2 ^ (if n ≤ 1 then 0 else slotsAux f ((n + 1) / 2) + 1)
    match Nat.decLe n 1 with
    | .isTrue h1 => rw [ite_eq_left h1]; exact h1
    | .isFalse h1 =>
      rw [ite_eq_right h1]
      have hn : 1 < n := Nat.lt_of_not_le h1
      have e := div_add_mod' 2 (by decide) (n + 1)
      have hq : 2 * ((n + 1) / 2) ≤ n + 1 := Nat.le_trans (Nat.le_add_right _ _) (Nat.le_of_eq e.symm)
      have h2 : 2 * ((n + 1) / 2) < 2 * n :=
        Nat.lt_of_le_of_lt hq (by rw [Nat.two_mul]; exact Nat.add_lt_add_left hn n)
      have hlt : (n + 1) / 2 < n :=
        Nat.lt_of_not_le fun hle => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h2 (Nat.mul_le_mul_left 2 hle))
      have ih := le_two_pow_slotsAux f ((n + 1) / 2) (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hlt h))
      have hdiv : n ≤ 2 * ((n + 1) / 2) := by
        have hr : (n + 1) % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by decide))
        have : n + 1 ≤ 2 * ((n + 1) / 2) + 1 := Nat.le_trans (Nat.le_of_eq e) (Nat.add_le_add_left hr _)
        exact Nat.le_of_succ_le_succ this
      rw [Nat.pow_succ, Nat.mul_comm]
      exact Nat.le_trans hdiv (Nat.mul_le_mul_left 2 ih)

theorem le_two_pow_slots (n : Nat) : n ≤ 16 * 2 ^ slots n := by
  have e := div_add_mod' 16 (by decide) (n + 15)
  have hr : (n + 15) % 16 ≤ 15 := Nat.le_of_lt_succ (Nat.mod_lt _ (by decide))
  have h1 : n ≤ 16 * ((n + 15) / 16) :=
    Nat.le_of_add_le_add_right (Nat.le_trans (Nat.le_of_eq e) (Nat.add_le_add_left hr _))
  exact Nat.le_trans h1 (Nat.mul_le_mul_left 16 (le_two_pow_slotsAux _ _ (Nat.le_refl _)))

/-! ## Matrices over the extension: the rows of a product as combinations of rows -/

/-- The product of two matrices over `K` given as pairs of matrices of residues (the real and the `w` parts, rows as
lists): the row `i` of `AB` is the combination of the rows of `B` by the entries of the row `i` of `A`, the list form. -/
def mulExtList (p ν : Nat) (A B : List (List Nat) × List (List Nat)) : List (List Nat) × List (List Nat) :=
  (List.zipWith (fun ar ai => (addL (combo ar B.1) (smul ν (combo ai B.2))).map (· % p)) A.1 A.2,
   List.zipWith (fun ar ai => (addL (combo ar B.2) (combo ai B.1)).map (· % p)) A.1 A.2)

/-- The packed form: the rows of `B` packed once, each row of the product as sums of scalar multiples of them. -/
def mulExtPacked (p ν n : Nat) (A : List (List Nat) × List (List Nat)) (P : List Nat × List Nat) :
    List (List Nat) × List (List Nat) :=
  (List.zipWith (fun ar ai => unpack p n (packCombo ar P.1 + ν * packCombo ai P.2)) A.1 A.2,
   List.zipWith (fun ar ai => unpack p n (packCombo ar P.2 + packCombo ai P.1)) A.1 A.2)

/-- A matrix of residues below `p`: every row below `p`, of `n` entries. -/
def Mtx (p n : Nat) : List (List Nat) → Prop
  | [] => True
  | r :: rs => Below p r ∧ r.length = n ∧ Mtx p n rs

theorem length_combo {p n : Nat} : ∀ (cs : List Nat) (rs : List (List Nat)), 0 < cs.length → Mtx p n rs →
    cs.length ≤ rs.length → (combo cs rs).length = n
  | [], _, h, _, _ => absurd h (Nat.lt_irrefl 0)
  | _ :: _, [], _, _, hl => absurd hl (Nat.not_succ_le_zero _)
  | [c], r :: _, _, ⟨_, hr, _⟩, _ => by
    show (addL (smul c r) []).length = n
    rw [length_addL_left _ _ (Nat.zero_le _), length_smul, hr]
  | c :: c' :: cs, r :: rs, _, ⟨_, hr, hrs⟩, hl => by
    show (addL (smul c r) (combo (c' :: cs) rs)).length = n
    have ih := length_combo (c' :: cs) rs (Nat.succ_pos _) hrs (Nat.le_of_succ_le_succ hl)
    rw [length_addL_left _ _ (by rw [ih, length_smul, hr]; exact Nat.le_refl n), length_smul, hr]

/-- The combination of rows of residues below `p` by `k` coefficients below `p` has entries below `k p² + 1`. -/
theorem combo_bound {p n : Nat} (hp : 0 < p) : ∀ (cs : List Nat) (rs : List (List Nat)), Below p cs → Mtx p n rs →
    Below (cs.length * (p * p) + 1) (combo cs rs)
  | [], _, _, _ => trivial
  | _ :: _, [], _, _ => trivial
  | c :: cs, r :: rs, ⟨hc, hcs⟩, ⟨hr, _, hrs⟩ => by
    show Below ((cs.length + 1) * (p * p) + 1) (addL (smul c r) (combo cs rs))
    have := below_addL (Nat.mul_pos hp hp) (Nat.succ_pos _) _ _ (below_smul hc r hr) (combo_bound hp cs rs hcs hrs)
    rw [Nat.succ_mul, Nat.add_comm (cs.length * (p * p)) (p * p), Nat.add_assoc]
    exact this

theorem map_pack_length : ∀ rs : List (List Nat), (rs.map pack).length = rs.length
  | [] => rfl
  | _ :: rs => by show (rs.map pack).length + 1 = rs.length + 1; rw [map_pack_length rs]

/-- One row of the product: the packed combination is the list combination. -/
theorem row_eq (p ν n : Nat) (hp : 0 < p) (hν : ν < p) (hn : 0 < n) (ar ai : List Nat) (M : List (List Nat) × List (List Nat))
    (har : Below p ar) (hai : Below p ai) (lar : ar.length = n) (lai : ai.length = n)
    (hM1 : Mtx p n M.1) (hM2 : Mtx p n M.2) (lM1 : M.1.length = n) (lM2 : M.2.length = n)
    (hB : p * (n * (p * p) + 1) + p * (n * (p * p) + 1) ≤ B) :
    unpack p n (packCombo ar (M.1.map pack) + ν * packCombo ai (M.2.map pack)) =
      (addL (combo ar M.1) (smul ν (combo ai M.2))).map (· % p) ∧
    unpack p n (packCombo ar (M.2.map pack) + packCombo ai (M.1.map pack)) =
      (addL (combo ar M.2) (combo ai M.1)).map (· % p) := by
  have hm : 0 < p * (n * (p * p) + 1) := Nat.mul_pos hp (Nat.succ_pos _)
  have c1 : Below (p * (n * (p * p) + 1)) (combo ar M.1) :=
    below_mono (Nat.le_mul_of_pos_left _ hp) _ (lar ▸ combo_bound hp ar M.1 har hM1)
  have c2 : Below (p * (n * (p * p) + 1)) (smul ν (combo ai M.2)) :=
    below_smul hν _ (lai ▸ combo_bound hp ai M.2 hai hM2)
  have c3 : Below (p * (n * (p * p) + 1)) (combo ar M.2) :=
    below_mono (Nat.le_mul_of_pos_left _ hp) _ (lar ▸ combo_bound hp ar M.2 har hM2)
  have c4 : Below (p * (n * (p * p) + 1)) (combo ai M.1) :=
    below_mono (Nat.le_mul_of_pos_left _ hp) _ (lai ▸ combo_bound hp ai M.1 hai hM1)
  have l1 : (combo ar M.1).length = n := length_combo ar M.1 (lar ▸ hn) hM1 (by rw [lar, lM1]; exact Nat.le_refl n)
  have l2 : (combo ai M.2).length = n := length_combo ai M.2 (lai ▸ hn) hM2 (by rw [lai, lM2]; exact Nat.le_refl n)
  have l3 : (combo ar M.2).length = n := length_combo ar M.2 (lar ▸ hn) hM2 (by rw [lar, lM2]; exact Nat.le_refl n)
  have l4 : (combo ai M.1).length = n := length_combo ai M.1 (lai ▸ hn) hM1 (by rw [lai, lM1]; exact Nat.le_refl n)
  constructor
  · rw [← pack_combo, ← pack_combo, ← pack_smul, ← pack_addL,
      ← unpack_pack p _ (bounded_of_below hB _ (below_addL hm hm _ _ c1 c2)),
      length_addL_eq l1 (by rw [length_smul, l2])]
  · rw [← pack_combo, ← pack_combo, ← pack_addL,
      ← unpack_pack p _ (bounded_of_below hB _ (below_addL hm hm _ _ c3 c4)), length_addL_eq l3 l4]

/-- The packed product of two matrices over `K` is the list form, when `2 p (n p² + 1) ≤ B`. -/
theorem mulExtPacked_eq (p ν n : Nat) (hp : 0 < p) (hν : ν < p) (hn : 0 < n)
    (A M : List (List Nat) × List (List Nat)) (hA1 : Mtx p n A.1) (hA2 : Mtx p n A.2)
    (hM1 : Mtx p n M.1) (hM2 : Mtx p n M.2) (lM1 : M.1.length = n) (lM2 : M.2.length = n)
    (hB : p * (n * (p * p) + 1) + p * (n * (p * p) + 1) ≤ B) :
    mulExtPacked p ν n A (M.1.map pack, M.2.map pack) = mulExtList p ν A M := by
  obtain ⟨A1, A2⟩ := A
  unfold mulExtPacked mulExtList
  induction A1 generalizing A2 with
  | nil => cases A2 <;> rfl
  | cons ar A1 ih =>
    cases A2 with
    | nil => rfl
    | cons ai A2 =>
      obtain ⟨har, lar, hA1'⟩ := hA1
      obtain ⟨hai, lai, hA2'⟩ := hA2
      have h := row_eq p ν n hp hν hn ar ai M har hai lar lai hM1 hM2 lM1 lM2 hB
      have ih' := ih A2 hA1' hA2'
      show (unpack p n (packCombo ar (M.1.map pack) + ν * packCombo ai (M.2.map pack)) :: List.zipWith _ A1 A2,
          unpack p n (packCombo ar (M.2.map pack) + packCombo ai (M.1.map pack)) :: List.zipWith _ A1 A2) =
        ((addL (combo ar M.1) (smul ν (combo ai M.2))).map (· % p) :: List.zipWith _ A1 A2,
          (addL (combo ar M.2) (combo ai M.1)).map (· % p) :: List.zipWith _ A1 A2)
      rw [h.1, h.2, (Prod.mk.inj ih').1, (Prod.mk.inj ih').2]

end FRC.Dirac.Packed
