import FrcCore.Theme.Thue
import FrcCore.Theme.Count

/-!
# The modes on the window

20-rh's row G17 (26 November 2026), above Thue's lemma (`Theme/Thue.lean`). The window of a shell `𝔽_p` is the
labels `1, …, q`, with `q` the largest label with `q² < p`. A mode of count `k` is `x ↦ x^k`. Its values at the
primes of the window fix the mode. They are all `±1` exactly for the counts `0` and `π = 2κ`, and all `±ℓ^j`
exactly for the counts `j` and `π + j`. The proofs take a property from the primes of the window to every label
(a label is a product of primes) and from the labels to every nonzero residue (Thue's lemma).
-/

namespace FRC
namespace Nat

/-- A number `n ≥ 2` is prime or has a divisor `d` with `2 ≤ d < n`. -/
theorem prime_or_divisor (n : Nat) (h2 : 2 ≤ n) : isPrime n ∨ ∃ d, 2 ≤ d ∧ d < n ∧ n % d = 0 := by
  have key : ∀ m, (∀ d, d < m → 2 ≤ d → n % d ≠ 0) ∨ (∃ d, 2 ≤ d ∧ d < m ∧ n % d = 0) := by
    intro m
    induction m with
    | zero => exact Or.inl (fun d hd _ => absurd hd (Nat.not_lt_zero d))
    | succ m ih =>
      cases ih with
      | inr h =>
        match h with
        | ⟨d, hd2, hdm, hd0⟩ => exact Or.inr ⟨d, hd2, Nat.lt_succ_of_lt hdm, hd0⟩
      | inl h =>
        match Nat.decEq (n % m) 0 with
        | isTrue e =>
          match Nat.decLe 2 m with
          | isTrue h2m => exact Or.inr ⟨m, h2m, Nat.lt_succ_self m, e⟩
          | isFalse h2m =>
            exact Or.inl (fun d hd hd2 => by
              cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hd) with
              | inl hlt => exact h d hlt hd2
              | inr heq => rw [heq] at hd2; exact absurd hd2 h2m)
        | isFalse e =>
          exact Or.inl (fun d hd hd2 => by
            cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hd) with
            | inl hlt => exact h d hlt hd2
            | inr heq => rw [heq]; exact e)
  cases key n with
  | inl h => exact Or.inl ⟨h2, h⟩
  | inr h => exact Or.inr h

/-- A divisor gives a factorisation. -/
theorem dvd_factor {n d : Nat} (hd : 0 < d) (h : n % d = 0) : ∃ e, n = d * e :=
  match mod_spec d hd n with
  | ⟨e, he⟩ => ⟨e, by rw [h, Nat.add_zero] at he; exact he⟩

/-- A property that holds at `1`, at the primes up to `q` and at the product of two numbers that have it holds at
every label `1 ≤ n ≤ q`. -/
theorem label_induction {q : Nat} (P : Nat → Prop) (h1 : P 1) (hmul : ∀ a b, P a → P b → P (a * b))
    (hp : ∀ ℓ, isPrime ℓ → ℓ ≤ q → P ℓ) : ∀ n, 0 < n → n ≤ q → P n := by
  have key : ∀ N n, n ≤ N → 0 < n → n ≤ q → P n := by
    intro N
    induction N with
    | zero => intro n hn h0 _; exact absurd h0 (Nat.not_lt_of_le hn)
    | succ N ih =>
      intro n hn h0 hq
      match Nat.decLe 2 n with
      | isFalse h2 =>
        have : n = 1 := Nat.le_antisymm (Nat.le_of_lt_succ (Nat.lt_of_not_le h2)) h0
        rw [this]; exact h1
      | isTrue h2 =>
        cases prime_or_divisor n h2 with
        | inl hpr => exact hp n hpr hq
        | inr hd =>
          match hd with
          | ⟨d, hd2, hdn, hd0⟩ =>
            have hdpos : 0 < d := Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) hd2
            match dvd_factor hdpos hd0 with
            | ⟨e, he⟩ =>
              have he0 : 0 < e := by
                cases e with
                | zero => rw [he, Nat.mul_zero] at h0; exact absurd h0 (Nat.lt_irrefl 0)
                | succ e => exact Nat.zero_lt_succ e
              have hen : e < n := by
                have := mul_lt_mul_of_lt_of_pos (Nat.lt_of_lt_of_le (Nat.lt_succ_self 1) hd2) he0
                rw [Nat.one_mul, ← he] at this; exact this
              have hdN : d ≤ N := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hdn hn)
              have heN : e ≤ N := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hen hn)
              have := hmul d e (ih d hdN hdpos (Nat.le_trans (Nat.le_of_lt hdn) hq))
                (ih e heN he0 (Nat.le_trans (Nat.le_of_lt hen) hq))
              rw [← he] at this; exact this
  intro n; exact key n n (Nat.le_refl n)

end Nat

namespace Horizon

open FRC.Shell FRC.Shell.Frame

variable {p : Nat} [Pos p] {κ : Nat} {g : Shell p}

section window20261126

/-- A power of a nonzero residue is nonzero. -/
theorem pow_ne_zero_of (F : Frame p κ g) {x : Shell p} (hx : x ≠ 0) : ∀ n : Nat, x ^ n ≠ 0
  | 0 => F.one_ne_zero
  | n + 1 => F.mul_ne_zero (pow_ne_zero_of F hx n) hx

/-- The residue is `1` or `−1`. -/
abbrev Sign (x : Shell p) : Prop := x = 1 ∨ x = -1

theorem sign_mul {x y : Shell p} (hx : Sign x) (hy : Sign y) : Sign (x * y) := by
  cases hx with
  | inl hx =>
    cases hy with
    | inl hy => exact Or.inl (by rw [hx, hy, one_mul])
    | inr hy => exact Or.inr (by rw [hx, hy, one_mul])
  | inr hx =>
    cases hy with
    | inl hy => exact Or.inr (by rw [hx, hy, mul_one])
    | inr hy => exact Or.inl (by rw [hx, hy, neg_mul_neg, one_mul])

theorem sign_sq {x : Shell p} (hx : Sign x) : x * x = 1 := by
  cases hx with
  | inl hx => rw [hx, one_mul]
  | inr hx => rw [hx, neg_mul_neg, one_mul]

theorem sign_neg_one_pow : ∀ m : Nat, Sign ((-1 : Shell p) ^ m)
  | 0 => Or.inl rfl
  | m + 1 => sign_mul (sign_neg_one_pow m) (Or.inr rfl)

theorem neg_one_pow_sq (m : Nat) : ((-1 : Shell p) ^ m) * ((-1) ^ m) = 1 := sign_sq (sign_neg_one_pow m)

/-- 20:G17 — from the primes of the window to every nonzero residue. Let a set `S` of residues hold `1` and
`(−1)^m`, be closed under products, and have `x·x = 1` for its members. If `S` holds the value of the mode of
count `m` at every prime of the window, it holds the value at every nonzero residue. -/
theorem window_lift (F : Frame p κ g) {q : Nat} (hq1 : q * q < p) (hq2 : p < (q + 1) * (q + 1)) (m : Nat)
    (S : Shell p → Prop) (h1 : S 1) (hmul : ∀ x y, S x → S y → S (x * y)) (hsq : ∀ x, S x → x * x = 1)
    (hneg : S ((-1) ^ m)) (hP : ∀ ℓ, Nat.isPrime ℓ → ℓ ≤ q → S ((ofNat ℓ : Shell p) ^ m)) :
    ∀ r : Shell p, r ≠ 0 → S (r ^ m) := by
  have hlab : ∀ n, 0 < n → n ≤ q → S ((ofNat n : Shell p) ^ m) :=
    Nat.label_induction (fun n => S ((ofNat n : Shell p) ^ m))
      (by show S ((ofNat 1 : Shell p) ^ m); rw [show (ofNat 1 : Shell p) = 1 from rfl, one_pow]; exact h1)
      (fun a b ha hb => by show S ((ofNat (a * b) : Shell p) ^ m); rw [← ofNat_mul, mul_pow]; exact hmul _ _ ha hb) hP
  intro r hr
  match thue_ne_zero F hq1 hq2 hr with
  | ⟨a, b, ha0, ha, hb0, hb, hab⟩ =>
    have hA := hlab a ha0 ha
    have hB := hlab b hb0 hb
    have key : ∀ s : Shell p, S s → (ofNat a : Shell p) ^ m = s * (r ^ m * (ofNat b) ^ m) → S (r ^ m) := by
      intro s hs e
      have : r ^ m = s * ((ofNat a : Shell p) ^ m * (ofNat b) ^ m) := by
        rw [e, mul_assoc s, mul_assoc (r ^ m), hsq _ hB, mul_one, ← mul_assoc, hsq _ hs, one_mul]
      rw [this]; exact hmul _ _ hs (hmul _ _ hA hB)
    cases hab with
    | inl h => exact key 1 h1 (by rw [h, mul_pow, one_mul])
    | inr h =>
      exact key ((-1) ^ m) hneg
        (by rw [h, show -(r * ofNat b) = -1 * (r * ofNat b) from (neg_one_mul _).symm, mul_pow, mul_pow])

/-- A power of the generator below the period that is `±1` has the exponent `0` or `π = 2κ`. -/
theorem pow_gen_sign (F : Frame p κ g) {m : Nat} (hm : m < p - 1) (h : Sign (g ^ m)) : m = 0 ∨ m = 2 * κ := by
  cases h with
  | inl h => exact Or.inl (F.pow_inj hm (Nat.lt_of_le_of_lt (Nat.zero_le m) hm) (h.trans (pow_zero g).symm))
  | inr h => exact Or.inr (F.pow_inj hm F.two_kappa_lt (h.trans F.half_period.symm))

/-- The mode of count `π = 2κ` has the values `±1`. -/
theorem half_sign (F : Frame p κ g) {x : Shell p} (hx : x ≠ 0) : Sign (x ^ (2 * κ)) :=
  F.sq_eq_one (by rw [← pow_add, F.four_kappa]; exact unit_pow_card F hx)

/-- 20:G17 — the values of a mode at the primes of the window are all `±1` exactly for the counts `0` and
`π = 2κ`. -/
theorem mode_sign (F : Frame p κ g) {q : Nat} (hq1 : q * q < p) (hq2 : p < (q + 1) * (q + 1)) {k : Nat}
    (hk : k < p - 1) :
    (∀ ℓ, Nat.isPrime ℓ → ℓ ≤ q → ((ofNat ℓ : Shell p) ^ k = 1 ∨ (ofNat ℓ : Shell p) ^ k = -1)) ↔
      (k = 0 ∨ k = 2 * κ) := by
  constructor
  · intro h
    exact pow_gen_sign F hk
      (window_lift F hq1 hq2 k Sign (Or.inl rfl) (fun _ _ => sign_mul) (fun _ => sign_sq) (sign_neg_one_pow k) h g
        F.g_ne_zero)
  · intro h ℓ hℓ hℓq
    have hx : (ofNat ℓ : Shell p) ≠ 0 :=
      window_label_ne_zero hq1 (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) hℓ.1) hℓq
    cases h with
    | inl h => rw [h]; exact Or.inl rfl
    | inr h => rw [h]; exact half_sign F hx

theorem mode_fixed_le (F : Frame p κ g) {q : Nat} (hq1 : q * q < p) (hq2 : p < (q + 1) * (q + 1)) {k j : Nat}
    (hk : k < p - 1) (hjk : j ≤ k)
    (h : ∀ ℓ, Nat.isPrime ℓ → ℓ ≤ q → (ofNat ℓ : Shell p) ^ k = (ofNat ℓ) ^ j) : k = j := by
  have hkm : j + (k - j) = k := Nat.add_sub_of_le hjk
  have hm : k - j < p - 1 := Nat.lt_of_le_of_lt (Nat.sub_le k j) hk
  have hone : ∀ ℓ, Nat.isPrime ℓ → ℓ ≤ q → (ofNat ℓ : Shell p) ^ (k - j) = 1 := by
    intro ℓ hℓ hℓq
    have hx : (ofNat ℓ : Shell p) ≠ 0 :=
      window_label_ne_zero hq1 (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) hℓ.1) hℓq
    have e := h ℓ hℓ hℓq
    rw [← hkm, pow_add] at e
    exact F.mul_left_cancel (pow_ne_zero_of F hx j) (e.trans (mul_one _).symm)
  have hS := window_lift F hq1 hq2 (k - j) (fun x => x = 1 ∨ x = (-1 : Shell p) ^ (k - j)) (Or.inl rfl)
    (fun x y (hx : x = 1 ∨ x = (-1 : Shell p) ^ (k - j)) (hy : y = 1 ∨ y = (-1 : Shell p) ^ (k - j)) => by
      cases hx with
      | inl hx =>
        cases hy with
        | inl hy => exact Or.inl (by rw [hx, hy, one_mul])
        | inr hy => exact Or.inr (by rw [hx, hy, one_mul])
      | inr hx =>
        cases hy with
        | inl hy => exact Or.inr (by rw [hx, hy, mul_one])
        | inr hy => exact Or.inl (by rw [hx, hy]; exact neg_one_pow_sq _))
    (fun x (hx : x = 1 ∨ x = (-1 : Shell p) ^ (k - j)) => by
      cases hx with
      | inl hx => rw [hx, one_mul]
      | inr hx => rw [hx]; exact neg_one_pow_sq _)
    (Or.inr rfl) (fun ℓ hℓ hℓq => Or.inl (hone ℓ hℓ hℓq)) g F.g_ne_zero
  have hpos : 0 < p - 1 := Nat.lt_of_le_of_lt (Nat.zero_le _) hm
  have hm0 : k - j = 0 := by
    cases hS with
    | inl h1 => exact F.pow_inj hm hpos (h1.trans (pow_zero g).symm)
    | inr h2 =>
      cases pow_gen_sign F hm (by rw [h2]; exact sign_neg_one_pow _) with
      | inl h0 => exact h0
      | inr h0 =>
        have hsq : ((-1 : Shell p) ^ 2) = 1 := by
          show ((-1 : Shell p) ^ 1) * (-1) = 1
          rw [pow_one, neg_mul_neg, one_mul]
        have h3 : g ^ (k - j) = 1 := by rw [h2, h0, pow_mul, hsq, one_pow]
        exact F.pow_inj hm hpos (h3.trans (pow_zero g).symm)
  rw [← hkm, hm0, Nat.add_zero]

/-- 20:G17 — the values at the primes of the window fix a mode: two modes with the same values there have one
count. -/
theorem mode_fixed (F : Frame p κ g) {q : Nat} (hq1 : q * q < p) (hq2 : p < (q + 1) * (q + 1)) {k j : Nat}
    (hk : k < p - 1) (hj : j < p - 1)
    (h : ∀ ℓ, Nat.isPrime ℓ → ℓ ≤ q → (ofNat ℓ : Shell p) ^ k = (ofNat ℓ) ^ j) : k = j := by
  cases Nat.le_total j k with
  | inl hjk => exact mode_fixed_le F hq1 hq2 hk hjk h
  | inr hkj => exact (mode_fixed_le F hq1 hq2 hj hkj (fun ℓ hℓ hℓq => (h ℓ hℓ hℓq).symm)).symm

/-- 20:G17 — the values of a mode at the primes of the window are all `±ℓ^j` exactly for the counts `j` and
`π + j`. For two counts `k`, `j` below `p − 1` that is `k = j`, `k = j + 2κ` or `j = k + 2κ`. -/
theorem mode_signed_power (F : Frame p κ g) {q : Nat} (hq1 : q * q < p) (hq2 : p < (q + 1) * (q + 1)) {k j : Nat}
    (hk : k < p - 1) (hj : j < p - 1) :
    (∀ ℓ, Nat.isPrime ℓ → ℓ ≤ q →
        ((ofNat ℓ : Shell p) ^ k = (ofNat ℓ) ^ j ∨ (ofNat ℓ : Shell p) ^ k = -((ofNat ℓ) ^ j))) ↔
      (k = j ∨ k = j + 2 * κ ∨ j = k + 2 * κ) := by
  constructor
  · intro h
    cases Nat.le_total j k with
    | inl hjk =>
      have hkm : j + (k - j) = k := Nat.add_sub_of_le hjk
      have hm : k - j < p - 1 := Nat.lt_of_le_of_lt (Nat.sub_le k j) hk
      have hs : ∀ ℓ, Nat.isPrime ℓ → ℓ ≤ q → Sign ((ofNat ℓ : Shell p) ^ (k - j)) := by
        intro ℓ hℓ hℓq
        have hx : (ofNat ℓ : Shell p) ≠ 0 :=
          window_label_ne_zero hq1 (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) hℓ.1) hℓq
        have e := h ℓ hℓ hℓq
        rw [← hkm, pow_add] at e
        cases e with
        | inl e => exact Or.inl (F.mul_left_cancel (pow_ne_zero_of F hx j) (e.trans (mul_one _).symm))
        | inr e =>
          exact Or.inr (F.mul_left_cancel (pow_ne_zero_of F hx j) (e.trans (by rw [← mul_neg, mul_one])))
      cases (mode_sign F hq1 hq2 hm).1 hs with
      | inl h0 => exact Or.inl (by rw [← hkm, h0, Nat.add_zero])
      | inr h0 => exact Or.inr (Or.inl (by rw [← hkm, h0]))
    | inr hkj =>
      have hjm : k + (j - k) = j := Nat.add_sub_of_le hkj
      have hm : j - k < p - 1 := Nat.lt_of_le_of_lt (Nat.sub_le j k) hj
      have hs : ∀ ℓ, Nat.isPrime ℓ → ℓ ≤ q → Sign ((ofNat ℓ : Shell p) ^ (j - k)) := by
        intro ℓ hℓ hℓq
        have hx : (ofNat ℓ : Shell p) ≠ 0 :=
          window_label_ne_zero hq1 (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) hℓ.1) hℓq
        have e := h ℓ hℓ hℓq
        rw [← hjm, pow_add] at e
        cases e with
        | inl e =>
          exact Or.inl (F.mul_left_cancel (pow_ne_zero_of F hx k) ((mul_one _).trans e)).symm
        | inr e =>
          have h1 : (1 : Shell p) = -((ofNat ℓ : Shell p) ^ (j - k)) :=
            F.mul_left_cancel (pow_ne_zero_of F hx k) ((mul_one _).trans (e.trans (mul_neg _ _)))
          exact Or.inr ((neg_neg _).symm.trans (congrArg Neg.neg h1.symm))
      cases (mode_sign F hq1 hq2 hm).1 hs with
      | inl h0 => exact Or.inl (by rw [← hjm, h0, Nat.add_zero])
      | inr h0 => exact Or.inr (Or.inr (by rw [← hjm, h0]))
  · intro h ℓ hℓ hℓq
    have hx : (ofNat ℓ : Shell p) ≠ 0 :=
      window_label_ne_zero hq1 (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) hℓ.1) hℓq
    have hh := half_sign F hx
    cases h with
    | inl h => rw [h]; exact Or.inl rfl
    | inr h =>
      cases h with
      | inl h =>
        rw [h, pow_add]
        cases hh with
        | inl hh => exact Or.inl (by rw [hh, mul_one])
        | inr hh => exact Or.inr (by rw [hh, ← mul_neg, mul_one])
      | inr h =>
        rw [h, pow_add]
        cases hh with
        | inl hh => exact Or.inl (by rw [hh, mul_one])
        | inr hh => exact Or.inr (by rw [hh, ← mul_neg, mul_one, neg_neg])

end window20261126

end Horizon
end FRC
