import FrcCore.Frame
import FrcCore.Series

/-!
# FrcCore.Theme.Ladder — the horizon theme: the ladder of the four roles, the ascent and the descent (26-pnp, 16 October 2026)

The computational face of the horizon clause (master Z2–Z4, B6), on a frame `(τ; 0, 1, g)` of a prime shell with the
drive `g` of order `n = p − 1`. The index cycle `C_n` is carried to the units by the ascent `m ↦ g^m`; the descent reads
the index back. On every shell, with no hypothesis beyond the frame:

* the power map acts on the index as multiplication by `k` — `(g^m)^k = g^{km mod n}` — and its iterates as
  multiplication by `k^r` (`power_index`, `phase_index`); the ascent is one multiplication per counted step
  (`ascent_step`); a tower exponent is read modulo `n`, so iterated exponentiation opens no fifth role
  (`tower_reduces`, the drive's `pow_mod`);
* multiplication by a unit permutes the units (`mul_perm`), the clause behind the Gauss-sum telescoping;
* every index `m` has a recentring chart, a translation of the cycle that carries it to one step from the origin
  (`recentre`, `recentre_inj`);
* the power map `x ↦ x^k` is a bijection of the units when `k` is invertible modulo `n`, inverted by `x ↦ x^a` with
  `ak ≡ 1` (`power_bijective_of_unit`); when `d` divides `k` and `n`, its image is the cycle of `g^d`, of exactly
  `n/d` elements (`power_image`); the gcd enters as a Bezout witness, never by the prelude's `Nat.gcd` (propext);
* square-and-multiply computes `b^e` with at most `2·bits e` multiplications (`sqmul_spec`, `sqmul_count`,
  `bits_le_of_lt_pow`);
* the baby-step–giant-step search, with `m² ≥ n` baby steps `1, g, …, g^{m−1}` (one multiplication each,
  `baby_step`) and at most `m` giant steps (one multiplication each, `giant_count`), recovers an index `y` with
  `g^y = g^x` from `g^x` (`bsgs_spec`).

The bit length and the halving are the file's own structural recursions (`half`, `par`, `bits`), since the prelude's
`Nat.log2` and `Nat.div` lemmas carry `propext`. No axioms.
-/

namespace FRC.Ladder

open FRC.Shell FRC.Shell.Frame

variable {p : Nat} [Pos p] {κ : Nat} {g : Shell p}

/-! ## The index dynamics of the power map (26:G2, G3) -/

/-- 26:G2, 26:G3 — the power map on the index: `(g^m)^k = g^{km mod n}`, multiplication by `k` on the index cycle. -/
theorem power_index (F : Frame p κ g) (m k : Nat) : (g ^ m) ^ k = g ^ ((k * m) % (p - 1)) := by
  rw [← pow_mul, Nat.mul_comm m k, F.pow_mod]

/-- `r` iterates of a map. -/
def iter {α : Type} (f : α → α) : Nat → α → α
  | 0, x => x
  | r + 1, x => iter f r (f x)

/-- 26:G3 — the iterated power map on the index: `P_k^r(g^m) = g^{k^r m mod n}`. -/
theorem phase_index (F : Frame p κ g) (k : Nat) : ∀ (r m : Nat),
    iter (fun x : Shell p => x ^ k) r (g ^ m) = g ^ ((k ^ r * m) % (p - 1))
  | 0, m => by
    show g ^ m = g ^ ((1 * m) % (p - 1))
    rw [Nat.one_mul, ← F.pow_mod]
  | r + 1, m => by
    show iter (fun x : Shell p => x ^ k) r ((g ^ m) ^ k) = g ^ ((k ^ (r + 1) * m) % (p - 1))
    rw [power_index F, phase_index F k r, FRC.Nat.mul_mod_mod _ _ _ F.n_pos, Nat.pow_succ,
      FRC.Nat.mul_assoc, Nat.mul_comm k m, ← FRC.Nat.mul_assoc]

/-- 26:G3, 26:G4 — the ascent is counting along the orbit: `g^{j+1} = g^j · g`, one multiplication per step. -/
theorem ascent_step (j : Nat) : g ^ (j + 1) = g ^ j * g := pow_succ g j

/-- 26:G2, 27:C10, 27:X9, 27:P1 — a tower exponent is read modulo `n`: `g^{(g^j)} = g^{(g^j) mod n}`; tetration is
exponentiation of a reduced index, and the two cyclic structures host every iterate (the ladder of the four roles closes:
the fifth step returns to counting, 27-fields' C10). -/
theorem tower_reduces (F : Frame p κ g) (j : Nat) : g ^ (g ^ j).val = g ^ ((g ^ j).val % (p - 1)) :=
  F.pow_mod _

/-! ## Multiplication by a unit permutes the units (26:B5) -/

/-- 26:B5 — multiplication by a unit `c` is injective on the shell and reaches every residue. -/
theorem mul_perm (F : Frame p κ g) {c : Shell p} (hc : c ≠ 0) :
    (∀ {x y : Shell p}, c * x = c * y → x = y) ∧ ∀ y : Shell p, ∃ x, c * x = y := by
  refine ⟨fun h => F.mul_left_cancel hc h, fun y => ?_⟩
  obtain ⟨u, hu⟩ := F.exists_inv hc
  exact ⟨u * y, by rw [← mul_assoc, hu, one_mul]⟩

/-! ## The recentring chart (26:E8) -/

/-- The translation of the index cycle that carries the index `m` to `1`. -/
def recentre (n m j : Nat) : Nat := (j + (n - m) + 1) % n

/-- 26:E8 — the recentred witness sits one step from the origin: `g^{recentre m} = g = g^0 · g`. -/
theorem recentre_witness (F : Frame p κ g) {m : Nat} (hm : m < p - 1) :
    g ^ recentre (p - 1) m m = g ∧ g = g ^ 0 * g := by
  refine ⟨?_, by rw [pow_zero, one_mul]⟩
  unfold recentre
  rw [← F.pow_mod, FRC.Nat.add_sub_of_le (Nat.le_of_lt hm), pow_succ, F.pow_n, one_mul]

/-- 26:E8 — the recentring is a chart: a bijection of the index cycle (injective on the `n` indices). -/
theorem recentre_inj (F : Frame p κ g) (m : Nat) {i j : Nat} (hi : i < p - 1) (hj : j < p - 1)
    (h : recentre (p - 1) m i = recentre (p - 1) m j) : i = j := by
  unfold recentre at h
  rw [Nat.add_assoc, Nat.add_assoc] at h
  have e : g ^ (p - 1 - m + 1) * g ^ i = g ^ (p - 1 - m + 1) * g ^ j := by
    rw [mul_comm, mul_comm _ (g ^ j), ← pow_add, ← pow_add, F.pow_mod (i + _), F.pow_mod (j + _), h]
  exact F.pow_inj hi hj (F.mul_left_cancel (F.pow_ne_zero _) e)

/-- 26:E8 — the recentring reaches every index `j < n` (from `i = (j + m + n − 1) % n`): with `recentre_inj`, a
bijection of the index cycle. -/
theorem recentre_surj (F : Frame p κ g) {m : Nat} (hm : m < p - 1) {j : Nat} (hj : j < p - 1) :
    ∃ i, i < p - 1 ∧ recentre (p - 1) m i = j := by
  have hn := F.n_pos
  refine ⟨(j + m + (p - 1 - 1)) % (p - 1), Nat.mod_lt _ hn, ?_⟩
  unfold recentre
  rw [Nat.add_assoc, FRC.Nat.mod_add_mod _ _ _ hn, ← Nat.add_assoc]
  have e : j + m + (p - 1 - 1) + (p - 1 - m) + 1 = (p - 1) * 2 + j := by
    have h1 : m + (p - 1 - m) = p - 1 := FRC.Nat.add_sub_of_le (Nat.le_of_lt hm)
    have h2 : (p - 1 - 1) + 1 = p - 1 := FRC.Nat.sub_add_cancel hn
    rw [Nat.add_assoc (j + m + (p - 1 - 1)), Nat.add_assoc (j + m), Nat.add_assoc j,
      Nat.add_left_comm (p - 1 - 1), ← Nat.add_assoc m, h1, h2, ← Nat.mul_two, Nat.add_comm]
  rw [e, FRC.Nat.add_mul_mod_self_left _ _ _ hn, FRC.Nat.mod_eq_of_lt hj]

/-! ## The power map: bijective or compressive (26:G5) -/

/-- 26:G5 — when `ak ≡ 1 (mod n)` the power map `x ↦ x^k` is a bijection of the units, inverted by `x ↦ x^a`. -/
theorem power_bijective_of_unit (F : Frame p κ g) {a k : Nat} (hak : (a * k) % (p - 1) = 1) (m : Nat) :
    ((g ^ m) ^ k) ^ a = g ^ m ∧ ((g ^ m) ^ a) ^ k = g ^ m := by
  have key : ∀ u v : Nat, (u * v) % (p - 1) = 1 → ((g ^ m) ^ u) ^ v = g ^ m := fun u v huv => by
    rw [← pow_mul, ← pow_mul, F.pow_mod, ← FRC.Nat.mul_mod_mod _ _ _ F.n_pos, huv, Nat.mul_one, ← F.pow_mod]
  exact ⟨key k a (by rw [Nat.mul_comm]; exact hak), key a k hak⟩

/-- 26:G5 — when `d ∣ k`, `n = d·e` and `ak = bn + d` (the gcd as a Bezout witness), the image of the power map
`x ↦ x^k` on the units is the cycle of `g^d`: every value is a power of `g^d`, every power of `g^d` is a value, and
the powers `(g^d)^i`, `i < e`, are distinct — the image has exactly `e = n/d` elements. -/
theorem power_image (F : Frame p κ g) {d e c a b k : Nat} (hn : p - 1 = d * e) (hk : k = d * c)
    (hbez : a * k = b * (p - 1) + d) :
    (∀ m : Nat, (g ^ m) ^ k = (g ^ d) ^ (m * c)) ∧
    (∀ i : Nat, ((g ^ a) ^ i) ^ k = (g ^ d) ^ i) ∧
    (∀ i j : Nat, i < e → j < e → (g ^ d) ^ i = (g ^ d) ^ j → i = j) := by
  have hd : 0 < d := by
    match d, hn with
    | 0, hn =>
      have h0 : 0 < 0 * e := hn ▸ F.n_pos
      rw [Nat.zero_mul] at h0
      exact absurd h0 (Nat.lt_irrefl 0)
    | d + 1, _ => exact Nat.zero_lt_succ d
  refine ⟨fun m => ?_, fun i => ?_, fun i j hi hj h => ?_⟩
  · rw [← pow_mul, ← pow_mul, hk, Nat.mul_comm d c, ← FRC.Nat.mul_assoc, Nat.mul_comm (m * c) d]
  · rw [← pow_mul, ← pow_mul, ← pow_mul, FRC.Nat.mul_left_comm, hbez, Nat.left_distrib, pow_add,
      ← FRC.Nat.mul_assoc, Nat.mul_comm (i * b), pow_mul, F.pow_n, one_pow, one_mul, Nat.mul_comm i d]
  · rw [← pow_mul, ← pow_mul] at h
    have hi' : d * i < p - 1 := by rw [hn]; exact Nat.mul_lt_mul_of_pos_left hi hd
    have hj' : d * j < p - 1 := by rw [hn]; exact Nat.mul_lt_mul_of_pos_left hj hd
    exact Nat.eq_of_mul_eq_mul_left hd (F.pow_inj hi' hj' h)


/-- 26:G5 — the compressive image has at most `e = n/d` elements: every value of `x ↦ x^k` is `(g^d)^i` with `i < e`
(with `power_image`'s distinctness of those powers, exactly `e`). -/
theorem power_image_index (F : Frame p κ g) {d e c k : Nat} (hn : p - 1 = d * e) (hk : k = d * c) (m : Nat) :
    ∃ i, i < e ∧ (g ^ m) ^ k = (g ^ d) ^ i := by
  have he : 0 < e := by
    match e, hn with
    | 0, hn => exact absurd (hn ▸ F.n_pos) (by rw [Nat.mul_zero]; exact Nat.lt_irrefl 0)
    | e + 1, _ => exact Nat.zero_lt_succ e
  have hde : (g ^ d) ^ e = 1 := by rw [← pow_mul, ← hn, F.pow_n]
  have h1 : (g ^ m) ^ k = (g ^ d) ^ (m * c) := by
    rw [← pow_mul, ← pow_mul, hk, Nat.mul_comm d c, ← FRC.Nat.mul_assoc, Nat.mul_comm (m * c) d]
  refine ⟨(m * c) % e, Nat.mod_lt _ he, ?_⟩
  rw [h1]
  match FRC.Nat.mod_spec e he (m * c) with
  | ⟨q, hq⟩ =>
    calc (g ^ d) ^ (m * c) = (g ^ d) ^ (e * q + (m * c) % e) := by rw [← hq]
      _ = ((g ^ d) ^ e) ^ q * (g ^ d) ^ ((m * c) % e) := by rw [pow_add, pow_mul]
      _ = (g ^ d) ^ ((m * c) % e) := by rw [hde, one_pow, one_mul]

/-- 26:G5 — the only-if: when `d = gcd(k, n) > 1` the image has fewer than `n` elements (`e < d·e = n`), so the power map
is no bijection of the units. -/
theorem compressive_of_gcd (F : Frame p κ g) {d e : Nat} (hn : p - 1 = d * e) (hd : 1 < d) : e < p - 1 := by
  have he : 0 < e := by
    match e, hn with
    | 0, hn => exact absurd (hn ▸ F.n_pos) (by rw [Nat.mul_zero]; exact Nat.lt_irrefl 0)
    | e + 1, _ => exact Nat.zero_lt_succ e
  rw [hn]
  calc e = 1 * e := (Nat.one_mul e).symm
    _ < d * e := Nat.mul_lt_mul_of_pos_right hd he

/-! ## The bit length (the file's own recursion) -/

/-- The half of a natural number, by structural recursion. -/
def half : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n + 2 => half n + 1

/-- The parity bit of a natural number. -/
def par : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => par n

theorem half_par : ∀ n : Nat, n = 2 * half n + par n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
    show n + 2 = 2 * (half n + 1) + par n
    rw [Nat.mul_succ, Nat.add_right_comm, ← half_par n]

theorem par_lt_two : ∀ n : Nat, par n < 2
  | 0 => Nat.zero_lt_succ 1
  | 1 => Nat.lt_succ_self 1
  | n + 2 => par_lt_two n

theorem half_lt : ∀ {n : Nat}, 0 < n → half n < n
  | 0, h => absurd h (Nat.lt_irrefl 0)
  | 1, _ => Nat.zero_lt_succ 0
  | n + 2, _ => by
    show half n + 1 < n + 2
    exact Nat.succ_le_succ (Nat.succ_le_succ (half_le n))
where
  half_le : ∀ n : Nat, half n ≤ n
    | 0 => Nat.le_refl 0
    | 1 => Nat.zero_le 1
    | n + 2 => Nat.succ_le_succ (Nat.le_trans (half_le n) (Nat.le_succ n))

/-- `a·b < a·c` gives `b < c` (the prelude's lemma carries `propext`). -/
theorem lt_of_mul_lt_mul_left' {a b c : Nat} (h : a * b < a * c) : b < c :=
  match Nat.lt_or_ge b c with
  | .inl hlt => hlt
  | .inr hge => absurd h (Nat.not_lt_of_le (Nat.mul_le_mul_left a hge))

/-- The bit length by fuel: `bitsAux fuel e` is the length of `e` written in binary when `e ≤ fuel`. -/
def bitsAux : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, e => if e = 0 then 0 else bitsAux fuel (half e) + 1

/-- The bit length of `e` (`0` for `e = 0`). -/
def bits (e : Nat) : Nat := bitsAux e e

theorem bitsAux_eq : ∀ (f₁ f₂ e : Nat), e ≤ f₁ → e ≤ f₂ → bitsAux f₁ e = bitsAux f₂ e
  | 0, f₂, e, h₁, _ => by
    have he : e = 0 := Nat.le_zero.1 h₁
    subst he
    match f₂ with
    | 0 => rfl
    | f₂ + 1 => rfl
  | f₁ + 1, 0, e, _, h₂ => by
    have he : e = 0 := Nat.le_zero.1 h₂
    subst he; rfl
  | f₁ + 1, f₂ + 1, e, h₁, h₂ => by
    show (if e = 0 then 0 else bitsAux f₁ (half e) + 1) = (if e = 0 then 0 else bitsAux f₂ (half e) + 1)
    match Nat.decEq e 0 with
    | isTrue he => rw [ite_eq_left he, ite_eq_left he]
    | isFalse he =>
      rw [ite_eq_right he, ite_eq_right he]
      have hl := half_lt (Nat.pos_of_ne_zero he)
      rw [bitsAux_eq f₁ f₂ (half e) (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hl h₁))
        (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hl h₂))]

/-- 26:F2 — a number below `2^l` has at most `l` bits. -/
theorem bitsAux_le_of_lt_pow : ∀ (l fuel e : Nat), e ≤ fuel → e < 2 ^ l → bitsAux fuel e ≤ l
  | l, 0, e, _, _ => Nat.zero_le l
  | 0, fuel + 1, e, _, he => by
    match e, he with
    | 0, _ => exact Nat.le_refl 0
    | e + 1, he => exact absurd he (Nat.not_lt_of_le (Nat.succ_le_succ (Nat.zero_le e)))
  | l + 1, fuel + 1, e, hf, he => by
    show (if e = 0 then 0 else bitsAux fuel (half e) + 1) ≤ l + 1
    match Nat.decEq e 0 with
    | isTrue h0 => rw [ite_eq_left h0]; exact Nat.zero_le _
    | isFalse h0 =>
      rw [ite_eq_right h0]
      apply Nat.succ_le_succ
      have hl := half_lt (Nat.pos_of_ne_zero h0)
      apply bitsAux_le_of_lt_pow l fuel (half e) (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hl hf))
      -- `2 · half e ≤ e < 2^(l+1) = 2 · 2^l`
      have h2 : 2 * half e < 2 * 2 ^ l := by
        have e2 : 2 * 2 ^ l = 2 ^ (l + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
        rw [e2]
        refine Nat.lt_of_le_of_lt ?_ he
        conv => rhs; rw [half_par e]
        exact Nat.le_add_right _ _
      exact lt_of_mul_lt_mul_left' h2

theorem bits_le_of_lt_pow {l e : Nat} (he : e < 2 ^ l) : bits e ≤ l :=
  bitsAux_le_of_lt_pow l e e (Nat.le_refl e) he

/-- 26:E10 — `e < 2^(bits e)`: the upper half of the bit-length bracket. -/
theorem lt_pow_bits : ∀ (fuel e : Nat), e ≤ fuel → e < 2 ^ bitsAux fuel e
  | 0, e, h => by
    have he : e = 0 := Nat.le_zero.1 h
    subst he; exact Nat.zero_lt_one
  | fuel + 1, e, h => by
    show e < 2 ^ (if e = 0 then 0 else bitsAux fuel (half e) + 1)
    match Nat.decEq e 0 with
    | isTrue h0 => rw [ite_eq_left h0, h0]; exact Nat.zero_lt_one
    | isFalse h0 =>
      rw [ite_eq_right h0]
      have hl := half_lt (Nat.pos_of_ne_zero h0)
      have ih := lt_pow_bits fuel (half e) (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hl h))
      have hp := par_lt_two e
      calc e = 2 * half e + par e := half_par e
        _ < 2 * half e + 2 := Nat.add_lt_add_left hp _
        _ = 2 * (half e + 1) := by rw [Nat.mul_succ]
        _ ≤ 2 * 2 ^ bitsAux fuel (half e) := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (bitsAux fuel (half e) + 1) := by rw [Nat.pow_succ, Nat.mul_comm]

/-- 26:E10 — `2^(bits e − 1) ≤ e` for `e > 0`: the lower half of the bit-length bracket. -/
theorem pow_bits_pred_le : ∀ (fuel e : Nat), e ≤ fuel → 0 < e → 2 ^ (bitsAux fuel e - 1) ≤ e
  | 0, e, h, he => absurd (Nat.lt_of_lt_of_le he h) (Nat.lt_irrefl 0)
  | fuel + 1, e, h, he => by
    show 2 ^ ((if e = 0 then 0 else bitsAux fuel (half e) + 1) - 1) ≤ e
    have h0 : e ≠ 0 := Nat.ne_of_gt he
    rw [ite_eq_right h0, Nat.add_sub_cancel]
    match Nat.decEq (half e) 0 with
    | isTrue hh =>
      have hb : bitsAux fuel 0 = 0 := by cases fuel <;> rfl
      rw [hh, hb]; exact he
    | isFalse hh =>
      have hl := half_lt he
      have ih := pow_bits_pred_le fuel (half e) (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hl h)) (Nat.pos_of_ne_zero hh)
      have hb1 : 1 ≤ bitsAux fuel (half e) := by
        match fuel, (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hl h) : half e ≤ fuel) with
        | 0, hf => exact absurd (Nat.le_zero.1 hf) hh
        | f + 1, _ =>
          show 1 ≤ (if half e = 0 then 0 else bitsAux f (half (half e)) + 1)
          rw [ite_eq_right hh]; exact Nat.succ_le_succ (Nat.zero_le _)
      have key : ∀ b : Nat, 1 ≤ b → 2 ^ b = 2 * 2 ^ (b - 1) := fun b hb => by
        match b, hb with
        | b' + 1, _ => rw [Nat.add_sub_cancel, Nat.pow_succ, Nat.mul_comm]
      calc 2 ^ bitsAux fuel (half e) = 2 * 2 ^ (bitsAux fuel (half e) - 1) := key _ hb1
        _ ≤ 2 * half e := Nat.mul_le_mul_left 2 ih
        _ ≤ 2 * half e + par e := Nat.le_add_right _ _
        _ = e := (half_par e).symm

/-- 26:E10 — the bit-length bracket: `2^(ℓ−1) ≤ e < 2^ℓ` for `ℓ = bits e`, `e > 0`. -/
theorem bits_bracket {e : Nat} (he : 0 < e) : 2 ^ (bits e - 1) ≤ e ∧ e < 2 ^ bits e :=
  ⟨pow_bits_pred_le e e (Nat.le_refl e) he, lt_pow_bits e e (Nat.le_refl e)⟩

/-- The sum of the distances `1, …, n` along the orbit. -/
def distSum : Nat → Nat
  | 0 => 0
  | n + 1 => distSum n + (n + 1)

/-- 26:E10 — the distances `1, …, n` have mean `(n + 1)/2` (`P/2` on the cycle of `n = P − 1` units):
`2 · Σ_{k<n} (k + 1) = n (n + 1)`. -/
theorem two_mul_distSum : ∀ n : Nat, 2 * distSum n = n * (n + 1)
  | 0 => rfl
  | n + 1 => by
    show 2 * (distSum n + (n + 1)) = (n + 1) * (n + 1 + 1)
    rw [Nat.mul_add, two_mul_distSum n, ← Nat.add_mul, Nat.mul_comm]

/-- 26:E10 — the maximum of the distances `1, …, n` is `n`: every `k + 1` with `k < n` is at most `n`. -/
theorem dist_le (n : Nat) : ∀ k, k < n → k + 1 ≤ n := fun _ hk => hk

/-! ## The ascent: square-and-multiply with its count (26:F2, G4) -/

/-- Square-and-multiply, right to left, by fuel: the pair (accumulator, multiplications). -/
def sqmulAux (b r : Shell p) (ops : Nat) : Nat → Nat → Shell p × Nat
  | 0, _ => (r, ops)
  | fuel + 1, e =>
    if e = 0 then (r, ops)
    else
      sqmulAux (b * b) (if par e = 1 then r * b else r) ((if par e = 1 then ops + 1 else ops) + 1) fuel (half e)

/-- Square-and-multiply: `b^e` and the number of modular multiplications used. -/
def sqmul (b : Shell p) (e : Nat) : Shell p × Nat := sqmulAux b 1 0 e e

theorem sqmulAux_spec : ∀ (fuel e : Nat) (b r : Shell p) (ops : Nat), e ≤ fuel →
    (sqmulAux b r ops fuel e).1 = r * b ^ e
  | 0, e, b, r, ops, h => by
    have he : e = 0 := Nat.le_zero.1 h
    subst he; show r = r * 1; rw [mul_one]
  | fuel + 1, e, b, r, ops, h => by
    show (if e = 0 then (r, ops) else sqmulAux (b * b) (if par e = 1 then r * b else r)
      ((if par e = 1 then ops + 1 else ops) + 1) fuel (half e)).1 = r * b ^ e
    match Nat.decEq e 0 with
    | isTrue h0 => rw [ite_eq_left h0, h0, pow_zero, mul_one]
    | isFalse h0 =>
      rw [ite_eq_right h0]
      have hl := half_lt (Nat.pos_of_ne_zero h0)
      rw [sqmulAux_spec fuel (half e) (b * b) _ _ (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hl h))]
      have hb : (b * b) ^ half e = b ^ (2 * half e) := by rw [mul_pow, Nat.mul_comm, pow_mul, pow_succ, pow_one]
      rw [hb]
      match (par_lt_two e), Nat.decEq (par e) 1 with
      | _, isTrue h1 =>
        rw [ite_eq_left h1]
        calc r * b * b ^ (2 * half e) = r * b ^ (2 * half e + 1) := by
              rw [pow_succ, mul_assoc, mul_comm b]
          _ = r * b ^ e := by rw [← h1]; conv => rhs; rw [half_par e]
      | hlt, isFalse h1 =>
        rw [ite_eq_right h1]
        have h0' : par e = 0 := by
          match (par e), hlt, h1 with
          | 0, _, _ => rfl
          | 1, _, h1 => exact absurd rfl h1
          | n + 2, hlt, _ => exact absurd hlt (Nat.not_lt_of_le (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le n))))
        have : e = 2 * half e := by conv => lhs; rw [half_par e, h0', Nat.add_zero]
        rw [← this]

/-- 26:F2 — square-and-multiply computes `b^e`. -/
theorem sqmul_spec (b : Shell p) (e : Nat) : (sqmul b e).1 = b ^ e := by
  unfold sqmul; rw [sqmulAux_spec e e b 1 0 (Nat.le_refl e), one_mul]

theorem sqmulAux_count : ∀ (fuel e : Nat) (b r : Shell p) (ops : Nat), e ≤ fuel →
    (sqmulAux b r ops fuel e).2 ≤ ops + 2 * bitsAux fuel e
  | 0, e, b, r, ops, _ => Nat.le_add_right _ _
  | fuel + 1, e, b, r, ops, h => by
    show (if e = 0 then (r, ops) else sqmulAux (b * b) (if par e = 1 then r * b else r)
      ((if par e = 1 then ops + 1 else ops) + 1) fuel (half e)).2
      ≤ ops + 2 * (if e = 0 then 0 else bitsAux fuel (half e) + 1)
    match Nat.decEq e 0 with
    | isTrue h0 => rw [ite_eq_left h0, ite_eq_left h0]; exact Nat.le_add_right _ _
    | isFalse h0 =>
      rw [ite_eq_right h0, ite_eq_right h0]
      have hl := half_lt (Nat.pos_of_ne_zero h0)
      have ih := sqmulAux_count fuel (half e) (b * b) (if par e = 1 then r * b else r)
        ((if par e = 1 then ops + 1 else ops) + 1) (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hl h))
      have hops : (if par e = 1 then ops + 1 else ops) + 1 ≤ ops + 2 := by
        match Nat.decEq (par e) 1 with
        | isTrue h1 => rw [ite_eq_left h1]; exact Nat.le_refl _
        | isFalse h1 => rw [ite_eq_right h1]; exact Nat.le_succ _
      calc _ ≤ (if par e = 1 then ops + 1 else ops) + 1 + 2 * bitsAux fuel (half e) := ih
        _ ≤ ops + 2 + 2 * bitsAux fuel (half e) := Nat.add_le_add_right hops _
        _ = ops + 2 * (bitsAux fuel (half e) + 1) := by
          rw [Nat.mul_succ, Nat.add_assoc, Nat.add_comm 2]

/-- 26:F2, 26:G4 — square-and-multiply uses at most `2·bits e` multiplications; for `e < 2^l`, at most `2l`. -/
theorem sqmul_count (b : Shell p) (e : Nat) : (sqmul b e).2 ≤ 2 * bits e := by
  have h := sqmulAux_count e e b 1 0 (Nat.le_refl e)
  rw [Nat.zero_add] at h
  exact h

/-- 26:F2, 26:G4 — for an exponent below `2^l`, square-and-multiply uses at most `2l` multiplications: `O(ℓ)` on a shell
of `ℓ` bits. -/
theorem sqmul_count_of_lt_pow (b : Shell p) {e l : Nat} (he : e < 2 ^ l) : (sqmul b e).2 ≤ 2 * l :=
  Nat.le_trans (sqmul_count b e) (Nat.mul_le_mul_left 2 (bits_le_of_lt_pow he))

/-! ## The descent: baby-step–giant-step with its count (26:F3, G4) -/

/-- The least `m < n` with `P m`, by search. -/
def findLT (P : Nat → Prop) [DecidablePred P] : Nat → Option Nat
  | 0 => none
  | n + 1 =>
    match findLT P n with
    | some m => some m
    | none => if P n then some n else none

theorem findLT_some {P : Nat → Prop} [DecidablePred P] : ∀ {n m : Nat}, findLT P n = some m → m < n ∧ P m
  | 0, m, h => by cases h
  | n + 1, m, h => by
    unfold findLT at h
    match hf : findLT P n with
    | some m' =>
      rw [hf] at h
      have hm : m' = m := Option.some.inj h
      have := findLT_some hf
      exact ⟨Nat.lt_succ_of_lt (hm ▸ this.1), hm ▸ this.2⟩
    | none =>
      rw [hf] at h
      have h' : (if P n then some n else none) = some m := h
      match (inferInstance : Decidable (P n)) with
      | isTrue hp =>
        rw [ite_eq_left hp] at h'
        have hm : n = m := Option.some.inj h'
        exact ⟨hm ▸ Nat.lt_succ_self n, hm ▸ hp⟩
      | isFalse hp =>
        rw [ite_eq_right hp] at h'
        cases h'

theorem findLT_of_exists {P : Nat → Prop} [DecidablePred P] : ∀ {n : Nat}, (∃ m, m < n ∧ P m) →
    ∃ m, findLT P n = some m
  | 0, ⟨m, hm, _⟩ => absurd hm (Nat.not_lt_zero m)
  | n + 1, ⟨m, hm, hp⟩ =>
    match hf : findLT P n with
    | some m' => ⟨m', by unfold findLT; rw [hf]⟩
    | none =>
      match Nat.lt_or_ge m n with
      | .inl hlt =>
        match findLT_of_exists ⟨m, hlt, hp⟩ with
        | ⟨m'', h''⟩ => by rw [hf] at h''; cases h''
      | .inr hge =>
        have hmn : m = n := Nat.le_antisymm (Nat.le_of_lt_succ hm) hge
        ⟨n, by
          unfold findLT; rw [hf]
          show (if P n then some n else none) = some n
          rw [ite_eq_left (hmn ▸ hp)]⟩

/-- The giant steps: from `γ`, multiply by `u` until the value is in the baby table; `(some (i, j), ops)` with `i`
the number of giant steps taken, `j` the baby index hit and `ops` the multiplications used. -/
def giantAux (u : Shell p) (m : Nat) (baby : Nat → Shell p) : Nat → Nat → Shell p → Nat → Option (Nat × Nat) × Nat
  | 0, _, _, ops => (none, ops)
  | fuel + 1, i, γ, ops =>
    match findLT (fun j => γ = baby j) m with
    | some j => (some (i, j), ops)
    | none => giantAux u m baby fuel (i + 1) (γ * u) (ops + 1)

/-- Baby-step–giant-step on the frame: `m` baby steps `g^j`, giant steps by `g^{n−m}` from the target `h`. -/
def bsgs (g h : Shell p) (n m : Nat) : Option (Nat × Nat) × Nat :=
  giantAux (g ^ (n - m)) m (fun j => g ^ j) m 0 h 0

/-- 26:F3 — the baby steps are one multiplication each: `g^{j+1} = g^j · g`. -/
theorem baby_step (j : Nat) : g ^ (j + 1) = g ^ j * g := pow_succ g j

theorem giantAux_count (u : Shell p) (m : Nat) (baby : Nat → Shell p) :
    ∀ (fuel i : Nat) (γ : Shell p) (ops : Nat), (giantAux u m baby fuel i γ ops).2 ≤ ops + fuel
  | 0, _, _, ops => Nat.le_refl _
  | fuel + 1, i, γ, ops => by
    unfold giantAux
    match findLT (fun j => γ = baby j) m with
    | some j => exact Nat.le_add_right _ _
    | none =>
      calc _ ≤ ops + 1 + fuel := giantAux_count u m baby fuel (i + 1) (γ * u) (ops + 1)
        _ = ops + (fuel + 1) := by rw [Nat.add_assoc, Nat.add_comm 1]

theorem giantAux_spec (u : Shell p) (m : Nat) (baby : Nat → Shell p) :
    ∀ (fuel i : Nat) (γ : Shell p) (ops i' j : Nat),
      (giantAux u m baby fuel i γ ops).1 = some (i', j) → j < m ∧ i ≤ i' ∧ γ * u ^ (i' - i) = baby j
  | 0, _, _, _, _, _, h => by cases h
  | fuel + 1, i, γ, ops, i', j, h => by
    unfold giantAux at h
    match hf : findLT (fun j => γ = baby j) m with
    | some j' =>
      rw [hf] at h
      have hj := findLT_some hf
      have e := Prod.mk.inj (Option.some.inj h)
      rw [← e.1, ← e.2, Nat.sub_self, pow_zero, mul_one]
      exact ⟨hj.1, Nat.le_refl _, hj.2⟩
    | none =>
      rw [hf] at h
      obtain ⟨hj, hi, hγ⟩ := giantAux_spec u m baby fuel (i + 1) (γ * u) (ops + 1) i' j h
      refine ⟨hj, Nat.le_of_succ_le hi, ?_⟩
      have : i' - i = (i' - (i + 1)) + 1 := by
        conv => lhs; rw [← FRC.Nat.add_sub_of_le hi, Nat.add_assoc, Nat.add_comm 1, FRC.Nat.add_sub_cancel_left]
      rw [this, pow_succ, ← mul_assoc, mul_comm (γ * u ^ (i' - (i + 1))) u, ← mul_assoc, mul_comm u γ]
      exact hγ

theorem giantAux_of_exists (u : Shell p) (m : Nat) (baby : Nat → Shell p) :
    ∀ (fuel i : Nat) (γ : Shell p) (ops : Nat),
      (∃ t, t < fuel ∧ ∃ j, j < m ∧ γ * u ^ t = baby j) → ∃ r, (giantAux u m baby fuel i γ ops).1 = some r
  | 0, _, _, _, ⟨t, ht, _⟩ => absurd ht (Nat.not_lt_zero t)
  | fuel + 1, i, γ, ops, ⟨t, ht, j, hj, hγ⟩ =>
    match hf : findLT (fun j => γ = baby j) m with
    | some j' => ⟨(i, j'), by unfold giantAux; rw [hf]⟩
    | none =>
      match t, ht, hγ with
      | 0, _, hγ =>
        have hγ' : γ = baby j := by rw [pow_zero, mul_one] at hγ; exact hγ
        match findLT_of_exists (P := fun j => γ = baby j) ⟨j, hj, hγ'⟩ with
        | ⟨j'', h''⟩ => by rw [hf] at h''; cases h''
      | t + 1, ht, hγ =>
        match giantAux_of_exists u m baby fuel (i + 1) (γ * u) (ops + 1)
            ⟨t, Nat.lt_of_succ_lt_succ ht, j, hj, by rw [mul_assoc, mul_comm u, ← pow_succ]; exact hγ⟩ with
        | ⟨r, hr⟩ => ⟨r, by unfold giantAux; rw [hf]; exact hr⟩

/-- The descent's verdict on a target, decidable by the kernel: the pair returned reconstructs the target. -/
def descendsB (g h : Shell p) (n m : Nat) : Bool :=
  match (bsgs g h n m).1 with
  | some (i, j) => decide (j < m) && decide (g ^ (j + m * i) = h)
  | none => false

/-- 26:F3 — the kernel's verdict unpacked: when `descendsB` holds, the search returns `(i, j)` with `j < m` and
`g^{j + m i} = h`. -/
theorem descendsB_spec {g h : Shell p} {n m : Nat} (hd : descendsB g h n m = true) :
    ∃ i j, (bsgs g h n m).1 = some (i, j) ∧ j < m ∧ g ^ (j + m * i) = h := by
  unfold descendsB at hd
  match hb : (bsgs g h n m).1 with
  | some (i, j) =>
    rw [hb] at hd
    have hd' : (decide (j < m) && decide (g ^ (j + m * i) = h)) = true := hd
    have h1 : decide (j < m) = true := by
      match hc : decide (j < m) with
      | true => rfl
      | false => rw [hc] at hd'; cases hd'
    rw [h1] at hd'
    have h2 : decide (g ^ (j + m * i) = h) = true := by
      match hc : decide (g ^ (j + m * i) = h) with
      | true => rfl
      | false => rw [hc] at hd'; cases hd'
    exact ⟨i, j, rfl, of_decide_eq_true h1, of_decide_eq_true h2⟩
  | none => rw [hb] at hd; cases hd

/-- 26:F3, 26:G4 — the descent: for `m ≤ n ≤ m²`, baby-step–giant-step from `h = g^x` (`x < n`) returns `(i, j)` with
`g^{j + m i} = h`, so the index is recovered modulo `n`, after at most `m` giant-step multiplications. -/
theorem bsgs_spec (F : Frame p κ g) {m : Nat} (hm : m ≤ p - 1) (hmm : p - 1 ≤ m * m) {x : Nat} (hx : x < p - 1) :
    (∃ i j, (bsgs g (g ^ x) (p - 1) m).1 = some (i, j) ∧ j < m ∧ g ^ (j + m * i) = g ^ x) ∧
    (bsgs g (g ^ x) (p - 1) m).2 ≤ m := by
  have hm0 : 0 < m := by
    match m, hmm with
    | 0, hmm => exact absurd (Nat.lt_of_lt_of_le F.n_pos hmm) (Nat.lt_irrefl 0)
    | m + 1, _ => exact Nat.zero_lt_succ m
  have hu : g ^ (p - 1 - m) * g ^ m = 1 := by rw [← pow_add, FRC.Nat.sub_add_cancel hm, F.pow_n]
  have hcount : (bsgs g (g ^ x) (p - 1) m).2 ≤ m := by
    have hc := giantAux_count (g ^ (p - 1 - m)) m (fun j => g ^ j) m 0 (g ^ x) 0
    rw [Nat.zero_add] at hc
    exact hc
  refine ⟨?_, hcount⟩
  -- the hit exists at the giant step `q`, `x = m q + r`
  obtain ⟨q, hq⟩ := FRC.Nat.mod_spec m hm0 x
  have hr : x % m < m := Nat.mod_lt x hm0
  have hqm : q < m := by
    have h1 : m * q < m * m := Nat.lt_of_le_of_lt (by rw [hq]; exact Nat.le_add_right _ _) (Nat.lt_of_lt_of_le hx hmm)
    exact lt_of_mul_lt_mul_left' h1
  have hhit : g ^ x * (g ^ (p - 1 - m)) ^ q = g ^ (x % m) := by
    have e1 : x + (p - 1 - m) * q = x % m + (p - 1) * q := by
      conv => lhs; rw [hq]
      rw [Nat.add_right_comm, Nat.add_comm, ← FRC.Nat.add_mul, Nat.add_comm m, FRC.Nat.sub_add_cancel hm]
    rw [← pow_mul, ← pow_add, e1, pow_add, pow_mul, F.pow_n, one_pow, mul_one]
  obtain ⟨⟨i', j⟩, hr'⟩ := giantAux_of_exists (g ^ (p - 1 - m)) m (fun j => g ^ j) m 0 (g ^ x) 0
    ⟨q, hqm, x % m, hr, hhit⟩
  obtain ⟨hj, _, hγ⟩ := giantAux_spec (g ^ (p - 1 - m)) m (fun j => g ^ j) m 0 (g ^ x) 0 i' j hr'
  refine ⟨i', j, hr', hj, ?_⟩
  have hγ' : g ^ x * (g ^ (p - 1 - m)) ^ i' = g ^ j := by rw [Nat.sub_zero] at hγ; exact hγ
  calc g ^ (j + m * i') = g ^ j * (g ^ m) ^ i' := by rw [pow_add, pow_mul]
    _ = g ^ x * (g ^ (p - 1 - m)) ^ i' * (g ^ m) ^ i' := by rw [hγ']
    _ = g ^ x * (g ^ (p - 1 - m) * g ^ m) ^ i' := by rw [mul_assoc, ← mul_pow]
    _ = g ^ x := by rw [hu, one_pow, mul_one]

/-- 26:F3 — the descent's total: the `m` baby steps and the giant multiplications together are at most `2m`. -/
theorem bsgs_total (F : Frame p κ g) {m : Nat} (hm : m ≤ p - 1) (hmm : p - 1 ≤ m * m) {x : Nat} (hx : x < p - 1) :
    m + (bsgs g (g ^ x) (p - 1) m).2 ≤ 2 * m := by
  have h := (bsgs_spec F hm hmm hx).2
  rw [Nat.two_mul]
  exact Nat.add_le_add_left h m

/-! ## The reference shape `𝔽₁₃` and `𝔽₁₀₁`, decided by the kernel (26:B3, E8, F2, F3, G2, G3, G5) -/

/-- 26:B3, the reference shape — the twelve eigenvalues `2^ν` of the scale shift on `𝔽₁₃` are distinct. -/
theorem eigenvalues13 : ∀ i, i < 12 → ∀ j, j < 12 → (2 : Shell 13) ^ i = 2 ^ j → i = j :=
  @of_decide_eq_true _ (@decForallLT (fun i => ∀ j, j < 12 → (2 : Shell 13) ^ i = 2 ^ j → i = j)
    (fun i => decForallLT (fun j => (2 : Shell 13) ^ i = 2 ^ j → i = j) 12) 12) (by decide +kernel)

/-- 26:G3, the reference shape — the phase formula on `𝔽₁₃`: two iterates of `x ↦ x³` carry `2^m` to `2^{9m mod 12}`,
and three iterates of `x ↦ x²` to `2^{8m mod 12}`. -/
theorem phase13 : ∀ m, m < 12 → iter (fun x : Shell 13 => x ^ 3) 2 (2 ^ m) = 2 ^ ((9 * m) % 12) ∧
    iter (fun x : Shell 13 => x ^ 2) 3 (2 ^ m) = 2 ^ ((8 * m) % 12) :=
  @of_decide_eq_true _ (decForallLT (fun m => iter (fun x : Shell 13 => x ^ 3) 2 (2 ^ m) = 2 ^ ((9 * m) % 12) ∧
    iter (fun x : Shell 13 => x ^ 2) 3 (2 ^ m) = 2 ^ ((8 * m) % 12)) 12) (by decide +kernel)

/-- 26:G2, the reference shape — a tower exponent is read modulo `12`: `2^{(2^j)} = 2^{(2^j) mod 12}` on `𝔽₁₃`. -/
theorem tower13 : ∀ j, j < 12 → (2 : Shell 13) ^ ((2 : Shell 13) ^ j).val = 2 ^ (((2 : Shell 13) ^ j).val % 12) :=
  @of_decide_eq_true _ (decForallLT (fun j => (2 : Shell 13) ^ ((2 : Shell 13) ^ j).val =
    2 ^ (((2 : Shell 13) ^ j).val % 12)) 12) (by decide +kernel)

/-- 26:E8, the reference shape — every index of `𝔽₁₃` is recentred to one step from the origin. -/
theorem recentre13 : ∀ m, m < 12 → (2 : Shell 13) ^ recentre 12 m m = 2 :=
  @of_decide_eq_true _ (decForallLT (fun m => (2 : Shell 13) ^ recentre 12 m m = 2) 12) (by decide +kernel)

/-- 26:G5, the reference shape — on `𝔽₁₃` the power map `x ↦ x⁵` is a bijection (`5 · 5 = 25 ≡ 1 (mod 12)`), and
`x ↦ x⁴` compresses the units onto the three powers of `2⁴ = 3` (`gcd(4, 12) = 4`, `1 · 4 = 0 · 12 + 4`). -/
theorem powers13 : (∀ m, m < 12 → (((2 : Shell 13) ^ m) ^ 5) ^ 5 = 2 ^ m) ∧
    (∀ m, m < 12 → ∃ i, i < 3 ∧ ((2 : Shell 13) ^ m) ^ 4 = ((2 : Shell 13) ^ 4) ^ i) ∧
    (∀ i, i < 3 → ∃ m, m < 12 ∧ ((2 : Shell 13) ^ m) ^ 4 = ((2 : Shell 13) ^ 4) ^ i) :=
  ⟨@of_decide_eq_true _ (decForallLT (fun m => (((2 : Shell 13) ^ m) ^ 5) ^ 5 = 2 ^ m) 12) (by decide +kernel),
   @of_decide_eq_true _ (@decForallLT (fun m => ∃ i, i < 3 ∧ ((2 : Shell 13) ^ m) ^ 4 = ((2 : Shell 13) ^ 4) ^ i)
     (fun m => decExistsLT (fun i => ((2 : Shell 13) ^ m) ^ 4 = ((2 : Shell 13) ^ 4) ^ i) 3) 12) (by decide +kernel),
   @of_decide_eq_true _ (@decForallLT (fun i => ∃ m, m < 12 ∧ ((2 : Shell 13) ^ m) ^ 4 = ((2 : Shell 13) ^ 4) ^ i)
     (fun i => decExistsLT (fun m => ((2 : Shell 13) ^ m) ^ 4 = ((2 : Shell 13) ^ 4) ^ i) 12) 3) (by decide +kernel)⟩

/-- 26:F2, the reference shape — square-and-multiply on `𝔽₁₃` computes every `2^e`, `e < 64`, within `2·bits e`
multiplications; `2^{11}` in seven. -/
theorem sqmul13 : (∀ e, e < 64 → (sqmul (2 : Shell 13) e).1 = 2 ^ e ∧ (sqmul (2 : Shell 13) e).2 ≤ 2 * bits e) ∧
    (sqmul (2 : Shell 13) 11).2 = 7 :=
  ⟨@of_decide_eq_true _ (decForallLT (fun e => (sqmul (2 : Shell 13) e).1 = 2 ^ e ∧
      (sqmul (2 : Shell 13) e).2 ≤ 2 * bits e) 64) (by decide +kernel), by decide⟩

/-- 26:F3, the reference shape and `𝔽₁₀₁` — baby-step–giant-step recovers every index: on `𝔽₁₃` with `m = 4`
(`16 ≥ 12`), on `𝔽₁₀₁` with `m = 10` (`100 ≥ 100`), the pair returned reconstructs the target. -/
theorem descent13_101 : (∀ x, x < 12 → descendsB (2 : Shell 13) (2 ^ x) 12 4 = true) ∧
    (∀ x, x < 100 → descendsB (2 : Shell 101) (2 ^ x) 100 10 = true) :=
  ⟨@of_decide_eq_true _ (decForallLT (fun x => descendsB (2 : Shell 13) (2 ^ x) 12 4 = true) 12) (by decide +kernel),
   @of_decide_eq_true _ (decForallLT (fun x => descendsB (2 : Shell 101) (2 ^ x) 100 10 = true) 100) (by decide +kernel)⟩

end FRC.Ladder
