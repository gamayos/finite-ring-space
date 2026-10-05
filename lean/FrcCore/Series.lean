import FrcCore.Shell
import FrcCore.Pigeonhole

/-!
# FrcCore.Series — bounded search, finite sums and products on the shell (the base theme, task LM22)

What every theme above needs and no frame provides: bounded quantifiers decided by search, without `propext`
(`decExistsLT`, `decForallLT`); sums `Σ_{l<n} f l` by structural recursion (`sumRange`), with congruence,
linearity, the single-term and the geometric sum; sums and products over lists of indices, and their invariance
under a permutation of `[0, n)` (`sum_perm`, `prod_perm`). No `Finset`, no quotient, no function extensionality.

Moved here by task LM22 from `Frame.lean` (the two deciders) and `Sum.lean` (the sums and the lists), so that the
prime shell's toolkit (`Theme/Foundation.lean`) stands without the frame; every name is unchanged. The products are
LM22's. No axioms.
-/

namespace FRC
namespace Shell

variable {p : Nat} [Pos p]

/-- Bounded existence `∃ m < n, P m`, decided by search — Lean's own `Nat.decidableExistsLT` carries
`propext` and `Quot.sound`; this one carries nothing. -/
def decExistsLT (P : Nat → Prop) [DecidablePred P] : (n : Nat) → Decidable (∃ m, m < n ∧ P m)
  | 0 => isFalse (fun ⟨m, hm, _⟩ => Nat.not_lt_zero m hm)
  | n + 1 =>
    match decExistsLT P n with
    | isTrue h => isTrue (match h with | ⟨m, hm, hp⟩ => ⟨m, Nat.lt_succ_of_lt hm, hp⟩)
    | isFalse hno =>
      if h : P n then isTrue ⟨n, Nat.lt_succ_self n, h⟩
      else isFalse (fun ⟨m, hm, hp⟩ =>
        match Nat.lt_or_ge m n with
        | .inl hlt => hno ⟨m, hlt, hp⟩
        | .inr hge => h ((Nat.le_antisymm (Nat.le_of_lt_succ hm) hge) ▸ hp))

/-- `∀ m < n, P m`, decided by recursion on `n` — Lean's own instance carries `propext`; this one nothing. -/
def decForallLT (P : Nat → Prop) [DecidablePred P] : (n : Nat) → Decidable (∀ m, m < n → P m)
  | 0 => isTrue (fun m hm => absurd hm (Nat.not_lt_zero m))
  | n + 1 =>
    match decForallLT P n with
    | isFalse h => isFalse (fun hall => h (fun m hm => hall m (Nat.lt_succ_of_lt hm)))
    | isTrue h =>
      if hn : P n then
        isTrue (fun m hm =>
          match Nat.lt_or_ge m n with
          | .inl hlt => h m hlt
          | .inr hge => (Nat.le_antisymm (Nat.le_of_lt_succ hm) hge) ▸ hn)
      else isFalse (fun hall => hn (hall n (Nat.lt_succ_self n)))

/-! ## Finite sums -/

/-- `sumRange f n = f 0 + f 1 + ⋯ + f (n−1)`. -/
def sumRange (f : Nat → Shell p) : Nat → Shell p
  | 0 => 0
  | n + 1 => sumRange f n + f n

theorem sumRange_zero (f : Nat → Shell p) : sumRange f 0 = 0 := rfl
theorem sumRange_succ (f : Nat → Shell p) (n : Nat) : sumRange f (n + 1) = sumRange f n + f n := rfl

theorem sum_congr {f h : Nat → Shell p} (n : Nat) (e : ∀ l, l < n → f l = h l) :
    sumRange f n = sumRange h n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumRange_succ, sumRange_succ, ih (fun l hl => e l (Nat.lt_succ_of_lt hl)),
      e n (Nat.lt_succ_self n)]

theorem sum_add (f h : Nat → Shell p) (n : Nat) :
    sumRange (fun l => f l + h l) n = sumRange f n + sumRange h n := by
  induction n with
  | zero => rw [sumRange_zero, sumRange_zero, sumRange_zero, add_zero]
  | succ n ih =>
    rw [sumRange_succ, sumRange_succ, sumRange_succ, ih, add_add_add_comm]

theorem sum_mul_right (f : Nat → Shell p) (c : Shell p) (n : Nat) :
    sumRange (fun l => f l * c) n = sumRange f n * c := by
  induction n with
  | zero => rw [sumRange_zero, sumRange_zero, zero_mul]
  | succ n ih => rw [sumRange_succ, sumRange_succ, ih, right_distrib]

theorem sum_mul_left (f : Nat → Shell p) (c : Shell p) (n : Nat) :
    sumRange (fun l => c * f l) n = c * sumRange f n := by
  induction n with
  | zero => rw [sumRange_zero, sumRange_zero, mul_zero]
  | succ n ih => rw [sumRange_succ, sumRange_succ, ih, left_distrib]

theorem sum_neg (f : Nat → Shell p) (n : Nat) : sumRange (fun l => -(f l)) n = -(sumRange f n) := by
  induction n with
  | zero => rw [sumRange_zero, sumRange_zero, neg_zero]
  | succ n ih => rw [sumRange_succ, sumRange_succ, ih, neg_add_rev]

theorem sum_const (c : Shell p) (n : Nat) : sumRange (fun _ => c) n = ofNat n * c := by
  induction n with
  | zero => rw [sumRange_zero]; exact (zero_mul c).symm
  | succ n ih =>
    rw [sumRange_succ, ih]
    have : (ofNat (n + 1) : Shell p) = ofNat n + 1 := ext (by
      rw [val_ofNat, val_add, val_ofNat, val_one, FRC.Nat.mod_add_mod _ _ _ hp, FRC.Nat.add_mod_mod _ _ _ hp])
    rw [this, right_distrib, one_mul]

theorem sum_zero {f : Nat → Shell p} (n : Nat) (h : ∀ l, l < n → f l = 0) : sumRange f n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumRange_succ, ih (fun l hl => h l (Nat.lt_succ_of_lt hl)), h n (Nat.lt_succ_self n), add_zero]

/-- A sum with a single nonzero term. -/
theorem sum_eq_single {f : Nat → Shell p} {l₀ : Nat} : ∀ {n : Nat}, l₀ < n → (∀ l, l < n → l ≠ l₀ → f l = 0) →
    sumRange f n = f l₀
  | 0, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, hl₀, h => by
    rw [sumRange_succ]
    exact match Nat.decEq l₀ n with
      | isTrue e => by
          rw [sum_zero n (fun l hl => h l (Nat.lt_succ_of_lt hl) (fun e' => absurd hl (by rw [e', e]; exact Nat.lt_irrefl n))),
            zero_add, e]
      | isFalse e => by
          rw [sum_eq_single (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hl₀) (fun e' => e e')) (fun l hl hne => h l (Nat.lt_succ_of_lt hl) hne),
            h n (Nat.lt_succ_self n) (fun e' => e e'.symm), add_zero]

/-- The telescoping geometric sum: `(Σ_{l<n} x^l)·(x − 1) = x^n − 1`. -/
theorem geom_sum_mul (x : Shell p) (n : Nat) :
    sumRange (fun l => x ^ l) n * (x + -1) = x ^ n + -1 := by
  induction n with
  | zero => rw [sumRange_zero, zero_mul, pow_zero, add_neg]
  | succ n ih =>
    rw [sumRange_succ, right_distrib, ih, left_distrib, ← mul_neg, mul_one, ← pow_succ]
    rw [add_add_add_comm, add_comm (x ^ n) (x ^ (n + 1)), add_comm (-1) (-(x ^ n)), add_assoc,
      ← add_assoc (x ^ n), add_neg, zero_add]

/-- `Σ_{l<n+1} f l = f 0 + Σ_{l<n} f (l + 1)`. -/
theorem sumRange_succ' (f : Nat → Shell p) : ∀ n, sumRange f (n + 1) = f 0 + sumRange (fun l => f (l + 1)) n
  | 0 => by rw [sumRange_succ, sumRange_zero, sumRange_zero, zero_add, add_zero]
  | n + 1 => by rw [sumRange_succ, sumRange_succ' f n, sumRange_succ, add_assoc]

/-! ## Sums over lists, permutation invariance (the reindexing `j ↦ u·j` of 2:F5) -/

/-- The sum of `F` over a list of indices. -/
def sumList (F : Nat → Shell p) : List Nat → Shell p
  | [] => 0
  | a :: l => F a + sumList F l

/-- `[n−1, …, 0]`. -/
def listRange : Nat → List Nat
  | 0 => []
  | n + 1 => n :: listRange n

/-- `[σ (n−1), …, σ 0]`. -/
def imageList (σ : Nat → Nat) : Nat → List Nat
  | 0 => []
  | n + 1 => σ n :: imageList σ n

theorem sumList_imageList (F : Nat → Shell p) (σ : Nat → Nat) (n : Nat) :
    sumList F (imageList σ n) = sumRange (fun j => F (σ j)) n := by
  induction n with
  | zero => rfl
  | succ n ih => show F (σ n) + sumList F (imageList σ n) = sumRange (fun j => F (σ j)) n + F (σ n); rw [ih, add_comm]

theorem sumList_erase (F : Nat → Shell p) {v : Nat} : ∀ {l : List Nat}, Pigeonhole.mem v l →
    sumList F l = F v + sumList F (Pigeonhole.erase v l)
  | [], h => absurd h id
  | a :: l, h => by
    exact match Nat.decEq a v with
      | isTrue e => by rw [show Pigeonhole.erase v (a :: l) = l from ite_eq_left e, e]; rfl
      | isFalse e => by
          rw [show Pigeonhole.erase v (a :: l) = a :: Pigeonhole.erase v l from ite_eq_right e]
          have hm : Pigeonhole.mem v l := match h with
            | Or.inl h' => absurd h'.symm e
            | Or.inr h' => h'
          show F a + sumList F l = F v + (F a + sumList F (Pigeonhole.erase v l))
          rw [sumList_erase F hm, add_left_comm]

theorem imageList_length (σ : Nat → Nat) (n : Nat) : (imageList σ n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => show (imageList σ n).length + 1 = n + 1; rw [ih]

theorem mem_imageList {σ : Nat → Nat} {v : Nat} : ∀ {n : Nat}, Pigeonhole.mem v (imageList σ n) → ∃ j, j < n ∧ σ j = v
  | 0, h => absurd h id
  | n + 1, h => match h with
    | Or.inl e => ⟨n, Nat.lt_succ_self n, e.symm⟩
    | Or.inr h' => match mem_imageList h' with
      | ⟨j, hj, e⟩ => ⟨j, Nat.lt_succ_of_lt hj, e⟩

theorem imageList_nodup {σ : Nat → Nat} {n : Nat} (hinj : ∀ i j, i < n → j < n → σ i = σ j → i = j) :
    ∀ {m : Nat}, m ≤ n → Pigeonhole.NoDup (imageList σ m)
  | 0, _ => trivial
  | m + 1, hm => ⟨fun h => match mem_imageList h with
      | ⟨j, hj, e⟩ => Nat.lt_irrefl j (hinj j m (Nat.lt_of_lt_of_le hj (Nat.le_of_lt hm)) hm e ▸ hj),
    imageList_nodup hinj (Nat.le_of_lt hm)⟩

/-- A sum over any list of `n` distinct indices below `n` is the sum over `0, …, n−1`. -/
theorem sumList_eq_sumRange (F : Nat → Shell p) : ∀ (n : Nat) (l : List Nat), Pigeonhole.NoDup l →
    (∀ e, Pigeonhole.mem e l → e < n) → l.length = n → sumList F l = sumRange F n
  | 0, [], _, _, _ => rfl
  | 0, a :: l, _, hb, _ => absurd (hb a (Or.inl rfl)) (Nat.not_lt_zero a)
  | n + 1, l, hnd, hb, hlen => by
    have hm : Pigeonhole.mem n l := Pigeonhole.mem_of_nodup_of_length_lt (n + 1) l hnd hb hlen n (Nat.lt_succ_self n)
    rw [sumList_erase F hm, sumRange_succ, add_comm]
    have hb' : ∀ e, Pigeonhole.mem e (Pigeonhole.erase n l) → e < n := fun e he =>
      match Nat.lt_or_ge e n with
      | Or.inl hlt => hlt
      | Or.inr hge =>
        have : e = n := Nat.le_antisymm (Nat.le_of_lt_succ (hb e (Pigeonhole.mem_of_mem_erase he))) hge
        absurd (this ▸ he) (Pigeonhole.not_mem_erase_self n hnd)
    have hlen' : (Pigeonhole.erase n l).length = n := by
      have := Pigeonhole.length_erase_of_mem hm; rw [hlen] at this; exact Nat.succ.inj this
    rw [sumList_eq_sumRange F n (Pigeonhole.erase n l) (Pigeonhole.nodup_erase n hnd) hb' hlen']

/-- Permutation invariance: for `σ` injective on `[0, n)` with values below `n`,
`Σ_{j<n} F (σ j) = Σ_{l<n} F l`. -/
theorem sum_perm (F : Nat → Shell p) (σ : Nat → Nat) (n : Nat) (hlt : ∀ j, j < n → σ j < n)
    (hinj : ∀ i j, i < n → j < n → σ i = σ j → i = j) :
    sumRange (fun j => F (σ j)) n = sumRange F n := by
  rw [← sumList_imageList]
  exact sumList_eq_sumRange F n (imageList σ n) (imageList_nodup hinj (Nat.le_refl n))
    (fun e he => match mem_imageList he with | ⟨j, hj, e'⟩ => e' ▸ hlt j hj) (imageList_length σ n)

/-! ## Products over `[0, n)`, invariant under a permutation (the products of `Sum.lean`'s sums) -/

/-- `Π_{j<n} f j`. -/
def prodRange (f : Nat → Shell p) : Nat → Shell p
  | 0 => 1
  | n + 1 => prodRange f n * f n

theorem prodRange_zero (f : Nat → Shell p) : prodRange f 0 = 1 := rfl
theorem prodRange_succ (f : Nat → Shell p) (n : Nat) : prodRange f (n + 1) = prodRange f n * f n := rfl

theorem prodRange_congr {f h : Nat → Shell p} : ∀ n, (∀ j, j < n → f j = h j) → prodRange f n = prodRange h n
  | 0, _ => rfl
  | n + 1, e => by
    rw [prodRange_succ, prodRange_succ, prodRange_congr n (fun j hj => e j (Nat.lt_succ_of_lt hj)),
      e n (Nat.lt_succ_self n)]

/-- A common factor leaves the product as its power: `Π_{j<n} a·G j = aⁿ · Π_{j<n} G j`. -/
theorem prodRange_mul_left (a : Shell p) (G : Nat → Shell p) :
    ∀ n, prodRange (fun j => a * G j) n = a ^ n * prodRange G n
  | 0 => (one_mul 1).symm
  | n + 1 => by rw [prodRange_succ, prodRange_succ, prodRange_mul_left a G n, pow_succ, mul_mul_mul_comm]

/-- The product of `F` over a list of indices. -/
def prodList (F : Nat → Shell p) : List Nat → Shell p
  | [] => 1
  | a :: l => F a * prodList F l

theorem prodList_imageList (F : Nat → Shell p) (σ : Nat → Nat) (n : Nat) :
    prodList F (imageList σ n) = prodRange (fun j => F (σ j)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show F (σ n) * prodList F (imageList σ n) = prodRange (fun j => F (σ j)) n * F (σ n); rw [ih, mul_comm]

theorem prodList_erase (F : Nat → Shell p) {v : Nat} : ∀ {l : List Nat}, Pigeonhole.mem v l →
    prodList F l = F v * prodList F (Pigeonhole.erase v l)
  | [], h => absurd h id
  | a :: l, h => by
    exact match Nat.decEq a v with
      | isTrue e => by rw [show Pigeonhole.erase v (a :: l) = l from ite_eq_left e, e]; rfl
      | isFalse e => by
          rw [show Pigeonhole.erase v (a :: l) = a :: Pigeonhole.erase v l from ite_eq_right e]
          have hm : Pigeonhole.mem v l := match h with
            | Or.inl h' => absurd h'.symm e
            | Or.inr h' => h'
          show F a * prodList F l = F v * (F a * prodList F (Pigeonhole.erase v l))
          rw [prodList_erase F hm, mul_left_comm]

/-- A product over any list of `n` distinct indices below `n` is the product over `0, …, n−1`. -/
theorem prodList_eq_prodRange (F : Nat → Shell p) : ∀ (n : Nat) (l : List Nat), Pigeonhole.NoDup l →
    (∀ e, Pigeonhole.mem e l → e < n) → l.length = n → prodList F l = prodRange F n
  | 0, [], _, _, _ => rfl
  | 0, a :: l, _, hb, _ => absurd (hb a (Or.inl rfl)) (Nat.not_lt_zero a)
  | n + 1, l, hnd, hb, hlen => by
    have hm : Pigeonhole.mem n l := Pigeonhole.mem_of_nodup_of_length_lt (n + 1) l hnd hb hlen n (Nat.lt_succ_self n)
    rw [prodList_erase F hm, prodRange_succ, mul_comm]
    have hb' : ∀ e, Pigeonhole.mem e (Pigeonhole.erase n l) → e < n := fun e he =>
      match Nat.lt_or_ge e n with
      | Or.inl hlt => hlt
      | Or.inr hge =>
        have : e = n := Nat.le_antisymm (Nat.le_of_lt_succ (hb e (Pigeonhole.mem_of_mem_erase he))) hge
        absurd (this ▸ he) (Pigeonhole.not_mem_erase_self n hnd)
    have hlen' : (Pigeonhole.erase n l).length = n := by
      have := Pigeonhole.length_erase_of_mem hm; rw [hlen] at this; exact Nat.succ.inj this
    rw [prodList_eq_prodRange F n (Pigeonhole.erase n l) (Pigeonhole.nodup_erase n hnd) hb' hlen']

/-- Permutation invariance: for `σ` injective on `[0, n)` with values below `n`,
`Π_{j<n} F (σ j) = Π_{l<n} F l`. -/
theorem prod_perm (F : Nat → Shell p) (σ : Nat → Nat) (n : Nat) (hlt : ∀ j, j < n → σ j < n)
    (hinj : ∀ i j, i < n → j < n → σ i = σ j → i = j) :
    prodRange (fun j => F (σ j)) n = prodRange F n := by
  rw [← prodList_imageList]
  exact prodList_eq_prodRange F n (imageList σ n) (imageList_nodup hinj (Nat.le_refl n))
    (fun e he => match mem_imageList he with | ⟨j, hj, e'⟩ => e' ▸ hlt j hj) (imageList_length σ n)

end Shell
end FRC
