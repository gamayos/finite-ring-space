import FrcCore.Theme.Field

/-!
# FrcCore.Theme.Drive — every prime carries a frame (the foundation theme, task LM23)

The formal shadow of C1 (master A14): every prime shell `𝔽_p` has a primitive root, a drive `g` of order `p − 1`, and
its powers reach every nonzero residue. No generator is assumed anywhere: the proof stands on `Theme/Field.lean`
(Fermat's little theorem, no zero divisors, the root bound of `x^m − 1`) and on the naturals.

The order `n` of a nonzero `x` is the least positive `n` with `xⁿ = 1` (`HasOrder`, found by search below `p`); `xᵏ = 1`
iff `n ∣ k`. For a prime power `qᵉ ∣ p − 1` the root bound gives `a` with `a^{(p−1)/q} ≠ 1`, and `a^{(p−1)/qᵉ}` has
order exactly `qᵉ`, since the divisors of `qᵉ` are the powers of `q`. Orders `m` and `qᵉ` with `q ∤ m` multiply: an
element killed by both `qᵉ` and `m` is `1`. Splitting off the least prime factor, every divisor of `p − 1` is an order,
`p − 1` among them. The pigeonhole then makes the `p − 1` powers of the drive exhaust the nonzero residues. No axioms.
-/

namespace FRC

namespace Nat

/-! ## Divisibility, the least witness, prime factors and prime powers -/

theorem dvd_trans' {a b c : Nat} : a ∣ b → b ∣ c → a ∣ c
  | ⟨d, hd⟩, ⟨e, he⟩ => ⟨d * e, by rw [he, hd, FRC.Nat.mul_assoc]⟩

theorem pos_of_dvd {a b : Nat} (hb : 0 < b) : a ∣ b → 0 < a
  | ⟨d, hd⟩ => Nat.pos_of_ne_zero (fun h => by rw [h, Nat.zero_mul] at hd; rw [hd] at hb; exact Nat.lt_irrefl 0 hb)

theorem le_of_dvd' {a b : Nat} (hb : 0 < b) : a ∣ b → a ≤ b
  | ⟨d, hd⟩ => by
    have hd0 : 0 < d := Nat.pos_of_ne_zero (fun h => by rw [h, Nat.mul_zero] at hd; rw [hd] at hb; exact Nat.lt_irrefl 0 hb)
    rw [hd]; exact Nat.le_mul_of_pos_right a hd0

theorem eq_one_of_mul_eq_one {n c : Nat} (h : n * c = 1) : n = 1 :=
  Nat.le_antisymm (le_of_dvd' (Nat.zero_lt_succ 0) ⟨c, h.symm⟩)
    (pos_of_dvd (Nat.zero_lt_succ 0) ⟨c, h.symm⟩)

/-- The least witness below a bound: if some `m < N` has `P m`, a least one does. -/
theorem exists_least (P : Nat → Prop) [DecidablePred P] :
    ∀ N, (∃ m, m < N ∧ P m) → ∃ m, m < N ∧ P m ∧ ∀ l, l < m → ¬ P l
  | 0, ⟨m, hm, _⟩ => absurd hm (Nat.not_lt_zero m)
  | N + 1, h =>
    match FRC.Shell.decExistsLT P N with
    | .isTrue h' => match exists_least P N h' with
      | ⟨m, hm, hP, hl⟩ => ⟨m, Nat.lt_succ_of_lt hm, hP, hl⟩
    | .isFalse hno => match h with
      | ⟨m, hm, hP⟩ => ⟨m, hm, hP, fun l hl hPl => hno ⟨l, Nat.lt_of_lt_of_le hl (Nat.le_of_lt_succ hm), hPl⟩⟩

/-- Every `n ≥ 2` has a prime divisor: its least divisor `d ≥ 2`. -/
theorem exists_prime_dvd {n : Nat} (hn : 2 ≤ n) : ∃ q, isPrime q ∧ q ∣ n := by
  have hn0 : 0 < n := Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) hn
  obtain ⟨d, _, ⟨hd2, hdn⟩, hmin⟩ := exists_least (fun d => 2 ≤ d ∧ n % d = 0) (n + 1)
    ⟨n, Nat.lt_succ_self n, hn, FRC.Nat.mod_self n hn0⟩
  have hd0 : 0 < d := Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) hd2
  have hdvd : d ∣ n := (dvd_iff_mod hd0).2 hdn
  refine ⟨d, ⟨hd2, fun e hed he2 hde => hmin e hed ⟨he2, ?_⟩⟩, hdvd⟩
  have he0 : 0 < e := Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) he2
  exact (dvd_iff_mod he0).1 (dvd_trans' ((dvd_iff_mod he0).2 hde) hdvd)

/-- The `q`-part: every `n > 0` is `qᵉ · m` with `q ∤ m`. -/
theorem exists_pow_mul {q : Nat} (hq : 2 ≤ q) : ∀ B n, n ≤ B → 0 < n → ∃ e m, n = q ^ e * m ∧ m % q ≠ 0
  | 0, n, hB, hn => absurd (Nat.lt_of_lt_of_le hn hB) (Nat.lt_irrefl 0)
  | B + 1, n, hB, hn => by
    have hq0 : 0 < q := Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) hq
    match Nat.decEq (n % q) 0 with
    | .isFalse h => exact ⟨0, n, by rw [Nat.pow_zero, Nat.one_mul], h⟩
    | .isTrue h =>
      obtain ⟨c, hc⟩ := FRC.Nat.mod_spec q hq0 n
      rw [h, Nat.add_zero] at hc
      have hc0 : 0 < c := Nat.pos_of_ne_zero (fun e => by rw [e, Nat.mul_zero] at hc; rw [hc] at hn; exact Nat.lt_irrefl 0 hn)
      have hcn : c < n := by
        rw [hc]
        calc c = 1 * c := (Nat.one_mul c).symm
          _ < q * c := FRC.Nat.mul_lt_mul_of_lt_of_pos (Nat.lt_of_lt_of_le (Nat.lt_succ_self 1) hq) hc0
      obtain ⟨e, m, hem, hm⟩ := exists_pow_mul hq B c (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hcn hB)) hc0
      refine ⟨e + 1, m, ?_, hm⟩
      rw [hc, hem, Nat.pow_succ, Nat.mul_comm (q ^ e) q, FRC.Nat.mul_assoc]

/-- The divisors of a prime power are the powers: `n ∣ qᵉ` gives `n = qʲ` with `j ≤ e`. -/
theorem dvd_prime_pow {q : Nat} (hq : isPrime q) : ∀ e n, n ∣ q ^ e → ∃ j, j ≤ e ∧ n = q ^ j
  | 0, n, ⟨c, hc⟩ => ⟨0, Nat.le_refl 0, eq_one_of_mul_eq_one (by rw [← hc]; rfl)⟩
  | e + 1, n, ⟨c, hc⟩ => by
    have hq0 : 0 < q := Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) hq.1
    have hqe : q ^ (e + 1) = q * q ^ e := by rw [Nat.pow_succ, Nat.mul_comm]
    match Nat.decEq (n % q) 0 with
    | .isTrue hn =>
      obtain ⟨n', hn'⟩ := FRC.Nat.mod_spec q hq0 n
      rw [hn, Nat.add_zero] at hn'
      have e1 : q * q ^ e = q * (n' * c) := by rw [← hqe, hc, hn', FRC.Nat.mul_assoc]
      obtain ⟨j, hj, hj'⟩ := dvd_prime_pow hq e n' ⟨c, Nat.eq_of_mul_eq_mul_left hq0 e1⟩
      exact ⟨j + 1, Nat.succ_le_succ hj, by rw [hn', hj', Nat.pow_succ, Nat.mul_comm]⟩
    | .isFalse hn =>
      have hnc : (n * c) % q = 0 := by
        rw [← hc, hqe]; exact FRC.Nat.mul_mod_eq_zero_left hq0 (FRC.Nat.mod_self q hq0)
      have hcq : c % q = 0 := match prime_mul_mod hq hnc with
        | .inl h => absurd h hn
        | .inr h => h
      obtain ⟨c', hc'⟩ := FRC.Nat.mod_spec q hq0 c
      rw [hcq, Nat.add_zero] at hc'
      have e1 : q * q ^ e = q * (n * c') := by
        rw [← hqe, hc, hc', FRC.Nat.mul_left_comm]
      obtain ⟨j, hj, hj'⟩ := dvd_prime_pow hq e n ⟨c', Nat.eq_of_mul_eq_mul_left hq0 e1⟩
      exact ⟨j, Nat.le_succ_of_le hj, hj'⟩

end Nat

namespace Shell
namespace Prime

variable {p : Nat} [Pos p]

/-! ## The order of a nonzero residue -/

/-- `x` has order `n`: `0 < n`, `xⁿ = 1`, and no positive power below `n` is `1`. -/
def HasOrder (x : Shell p) (n : Nat) : Prop := 0 < n ∧ x ^ n = 1 ∧ ∀ l, l < n → 0 < l → x ^ l ≠ 1

theorem pow_ne_zero (hp : FRC.Nat.isPrime p) {x : Shell p} (hx : x ≠ 0) : ∀ k : Nat, x ^ k ≠ 0
  | 0 => one_ne_zero hp
  | k + 1 => mul_ne_zero hp (pow_ne_zero hp hx k) hx

/-- Every nonzero residue has an order below `p` (the least positive exponent with `xⁿ = 1`; Fermat bounds it). -/
theorem exists_order (hp : FRC.Nat.isPrime p) {x : Shell p} (hx : x ≠ 0) : ∃ n, n < p ∧ HasOrder x n := by
  have hp1 : 0 < p - 1 := by
    match p, hp.1 with
    | k + 2, _ => exact Nat.zero_lt_succ k
  obtain ⟨n, hn, ⟨hn0, hxn⟩, hmin⟩ := FRC.Nat.exists_least (fun l => 0 < l ∧ x ^ l = 1) p
    ⟨p - 1, Nat.sub_lt Pos.pos (Nat.zero_lt_succ 0), hp1, fermat hp hx⟩
  exact ⟨n, hn, hn0, hxn, fun l hl hl0 hxl => hmin l hl ⟨hl0, hxl⟩⟩

theorem pow_eq_one_of_dvd {x : Shell p} {n k : Nat} (h : HasOrder x n) : n ∣ k → x ^ k = 1
  | ⟨c, hc⟩ => by rw [hc, pow_mul, h.2.1, one_pow]

theorem dvd_of_pow_eq_one {x : Shell p} {n k : Nat} (h : HasOrder x n) (hk : x ^ k = 1) : n ∣ k := by
  obtain ⟨c, hc⟩ := FRC.Nat.mod_spec n h.1 k
  rw [hc, pow_add, pow_mul, h.2.1, one_pow, one_mul] at hk
  match Nat.decEq (k % n) 0 with
  | .isTrue h0 => exact ⟨c, by rw [h0, Nat.add_zero] at hc; exact hc⟩
  | .isFalse h0 => exact absurd hk (h.2.2 _ (Nat.mod_lt k h.1) (Nat.pos_of_ne_zero h0))

/-- A nonzero `w` with `w^{qᵉ} = 1` and `w^m = 1`, `q` prime and `q ∤ m`, is `1`: its order divides `qᵉ`, so it is a
power of `q`, and it divides `m`, so it is `q⁰`. -/
theorem eq_one_of_pows (hp : FRC.Nat.isPrime p) {q e m : Nat} (hq : FRC.Nat.isPrime q) {w : Shell p} (hw : w ≠ 0)
    (he : w ^ (q ^ e) = 1) (hm : w ^ m = 1) (hmq : m % q ≠ 0) : w = 1 := by
  obtain ⟨n, _, hn⟩ := exists_order hp hw
  obtain ⟨j, _, hj⟩ := FRC.Nat.dvd_prime_pow hq e n (dvd_of_pow_eq_one hn he)
  have hnm := dvd_of_pow_eq_one hn hm
  match j, hj with
  | 0, hj => rw [hj, Nat.pow_zero] at hn; have := hn.2.1; rwa [pow_one] at this
  | j + 1, hj =>
    have hq0 : 0 < q := Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) hq.1
    have hqn : q ∣ n := ⟨q ^ j, by rw [hj, Nat.pow_succ, Nat.mul_comm]⟩
    exact absurd ((FRC.Nat.dvd_iff_mod hq0).1 (FRC.Nat.dvd_trans' hqn hnm)) hmq

/-- Orders `m` and `qᵉ` with `q ∤ m` multiply: `y z` has order `m qᵉ`. -/
theorem hasOrder_mul (hp : FRC.Nat.isPrime p) {q e m : Nat} (hq : FRC.Nat.isPrime q) {y z : Shell p}
    (hy0 : y ≠ 0) (hz0 : z ≠ 0) (hy : HasOrder y m) (hz : HasOrder z (q ^ e)) (hmq : m % q ≠ 0) :
    HasOrder (y * z) (m * q ^ e) := by
  refine ⟨Nat.mul_pos hy.1 hz.1, ?_, fun l hl hl0 hyz => ?_⟩
  · rw [mul_pow, pow_mul, hy.2.1, one_pow, one_mul, Nat.mul_comm, pow_mul, hz.2.1, one_pow]
  · rw [mul_pow] at hyz
    have hzl : z ^ l = 1 := by
      refine eq_one_of_pows hp hq (pow_ne_zero hp hz0 l) (by rw [pow_mul_comm, hz.2.1, one_pow]) ?_ hmq
      have h1 : (y ^ l * z ^ l) ^ m = 1 := by rw [hyz, one_pow]
      rwa [mul_pow, pow_mul_comm, hy.2.1, one_pow, one_mul] at h1
    have hyl : y ^ l = 1 := by rw [hzl, mul_one] at hyz; exact hyz
    obtain ⟨l', hl'⟩ := dvd_of_pow_eq_one hz hzl
    have hyl' : y ^ l' = 1 := by
      refine eq_one_of_pows hp (e := e) hq (pow_ne_zero hp hy0 l') ?_ (by rw [pow_mul_comm, hy.2.1, one_pow]) hmq
      rw [← pow_mul, Nat.mul_comm, ← hl']; exact hyl
    obtain ⟨c, hc⟩ := dvd_of_pow_eq_one hy hyl'
    have hle : m * q ^ e ≤ l := FRC.Nat.le_of_dvd' hl0
      ⟨c, by rw [hl', hc, Nat.mul_comm m (q ^ e), FRC.Nat.mul_assoc]⟩
    exact absurd hl (Nat.not_lt_of_le hle)

/-- A prime power `qᵉ ∣ p − 1`, `e ≥ 1`, is an order: with `p − 1 = qᵉ t` and `a^{(p−1)/q} ≠ 1` (the root bound),
`aᵗ` has order `qᵉ`. -/
theorem exists_order_prime_pow (hp : FRC.Nat.isPrime p) {q e : Nat} (hq : FRC.Nat.isPrime q) (he : 0 < e)
    (hdvd : q ^ e ∣ p - 1) : ∃ z : Shell p, z ≠ 0 ∧ HasOrder z (q ^ e) := by
  obtain ⟨t, ht⟩ := hdvd
  have hp1 : 0 < p - 1 := by
    match p, hp.1 with
    | k + 2, _ => exact Nat.zero_lt_succ k
  match e, he with
  | e + 1, _ =>
    have hq2 : 2 ≤ q := hq.1
    have hq0 : 0 < q := Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) hq2
    have hpd : p - 1 = q * (q ^ e * t) := by rw [ht, Nat.pow_succ, Nat.mul_comm (q ^ e) q, FRC.Nat.mul_assoc]
    have hd0 : 0 < q ^ e * t := Nat.pos_of_ne_zero (fun h => by rw [h, Nat.mul_zero] at hpd; rw [hpd] at hp1; exact Nat.lt_irrefl 0 hp1)
    have hdlt : q ^ e * t < p - 1 := by
      rw [hpd]
      calc q ^ e * t = 1 * (q ^ e * t) := (Nat.one_mul _).symm
        _ < q * (q ^ e * t) := FRC.Nat.mul_lt_mul_of_lt_of_pos (Nat.lt_of_lt_of_le (Nat.lt_succ_self 1) hq2) hd0
    obtain ⟨a, ha0, had⟩ := exists_pow_ne_one hp hd0 hdlt
    have hz0 : a ^ t ≠ 0 := pow_ne_zero hp ha0 t
    have hzq : (a ^ t) ^ (q ^ (e + 1)) = 1 := by rw [← pow_mul, Nat.mul_comm, ← ht, fermat hp ha0]
    obtain ⟨n, _, hn⟩ := exists_order hp hz0
    obtain ⟨j, hj, hjn⟩ := FRC.Nat.dvd_prime_pow hq (e + 1) n (dvd_of_pow_eq_one hn hzq)
    match Nat.lt_or_ge j (e + 1) with
    | .inl hlt =>
      have hje : q ^ j ∣ q ^ e := ⟨q ^ (e - j), by rw [← FRC.Nat.pow_add, FRC.Nat.add_sub_of_le (Nat.le_of_lt_succ hlt)]⟩
      have h1 : (a ^ t) ^ (q ^ e) = 1 := pow_eq_one_of_dvd hn (by rw [hjn]; exact hje)
      rw [← pow_mul, Nat.mul_comm] at h1
      exact absurd h1 had
    | .inr hge =>
      have : j = e + 1 := Nat.le_antisymm hj hge
      rw [this] at hjn
      exact ⟨a ^ t, hz0, hjn ▸ hn⟩

/-- Every divisor `n` of `p − 1` is an order: `n = qᵉ m` with `q` the least prime factor and `q ∤ m`; `m` is an order
by induction, `qᵉ` by the root bound, and the two multiply. -/
theorem exists_order_of_dvd (hp : FRC.Nat.isPrime p) :
    ∀ B n, n ≤ B → 0 < n → n ∣ p - 1 → ∃ y : Shell p, y ≠ 0 ∧ HasOrder y n
  | 0, n, hB, hn, _ => absurd (Nat.lt_of_lt_of_le hn hB) (Nat.lt_irrefl 0)
  | B + 1, n, hB, hn, hdvd => by
    match n, hn with
    | 1, _ => exact ⟨1, one_ne_zero hp, Nat.zero_lt_succ 0, one_pow 1,
        fun l hl hl0 => absurd (Nat.lt_of_lt_of_le hl0 (Nat.le_of_lt_succ hl)) (Nat.lt_irrefl 0)⟩
    | k + 2, _ =>
      obtain ⟨q, hq, hqn⟩ := FRC.Nat.exists_prime_dvd (Nat.le_add_left 2 k)
      have hq2 : 2 ≤ q := hq.1
      have hq0 : 0 < q := Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) hq2
      obtain ⟨e, m, hem, hmq⟩ := FRC.Nat.exists_pow_mul hq2 (k + 2) (k + 2) (Nat.le_refl _) (Nat.zero_lt_succ _)
      have hm0 : 0 < m := Nat.pos_of_ne_zero (fun h => by rw [h, Nat.mul_zero] at hem; exact Nat.noConfusion hem)
      have he0 : 0 < e := by
        match e, hem with
        | 0, hem =>
          rw [Nat.pow_zero, Nat.one_mul] at hem
          rw [hem] at hqn
          exact absurd ((FRC.Nat.dvd_iff_mod hq0).1 hqn) hmq
        | e + 1, _ => exact Nat.zero_lt_succ e
      have hqe : 2 ≤ q ^ e := by
        match e, he0 with
        | e + 1, _ =>
          rw [Nat.pow_succ]
          calc 2 ≤ q := hq2
            _ = 1 * q := (Nat.one_mul q).symm
            _ ≤ q ^ e * q := Nat.mul_le_mul_right q (Nat.pos_pow_of_pos e hq0)
      have hmn : m < k + 2 := by
        rw [hem]
        calc m = 1 * m := (Nat.one_mul m).symm
          _ < q ^ e * m := FRC.Nat.mul_lt_mul_of_lt_of_pos (Nat.lt_of_lt_of_le (Nat.lt_succ_self 1) hqe) hm0
      obtain ⟨y, hy0, hy⟩ := exists_order_of_dvd hp B m (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hmn hB)) hm0
        (FRC.Nat.dvd_trans' ⟨q ^ e, by rw [hem, Nat.mul_comm]⟩ hdvd)
      obtain ⟨z, hz0, hz⟩ := exists_order_prime_pow hp hq he0 (FRC.Nat.dvd_trans' ⟨m, hem⟩ hdvd)
      have h := hasOrder_mul hp hq hy0 hz0 hy hz hmq
      rw [Nat.mul_comm, ← hem] at h
      exact ⟨y * z, mul_ne_zero hp hy0 hz0, h⟩

/-! ## The drive: a primitive root, and its powers exhaust the nonzero residues -/

/-- A primitive root: `g^{p−1} = 1` and no positive power below `p − 1` is `1`. -/
theorem exists_primitive (hp : FRC.Nat.isPrime p) :
    ∃ g : Shell p, g ≠ 0 ∧ g ^ (p - 1) = 1 ∧ ∀ l, l < p - 1 → 0 < l → g ^ l ≠ 1 := by
  have hp1 : 0 < p - 1 := by
    match p, hp.1 with
    | k + 2, _ => exact Nat.zero_lt_succ k
  obtain ⟨g, hg0, hg⟩ := exists_order_of_dvd hp (p - 1) (p - 1) (Nat.le_refl _) hp1 ⟨1, (Nat.mul_one _).symm⟩
  exact ⟨g, hg0, hg.2.1, hg.2.2⟩

/-- The powers `g⁰, …, g^{p−2}` of a primitive root are distinct. -/
theorem primitive_pow_inj (hp : FRC.Nat.isPrime p) {g : Shell p} (hg0 : g ≠ 0) (hg : HasOrder g (p - 1))
    {i j : Nat} (hi : i < p - 1) (hj : j < p - 1) (h : g ^ i = g ^ j) : i = j := by
  have key : ∀ {i j : Nat}, i ≤ j → j < p - 1 → g ^ i = g ^ j → i = j := by
    intro i j hij hj h
    have e1 : g ^ i * g ^ (j - i) = g ^ i * 1 := by rw [← pow_add, FRC.Nat.add_sub_of_le hij, mul_one, h]
    obtain ⟨c, hc⟩ := dvd_of_pow_eq_one hg (mul_left_cancel hp (pow_ne_zero hp hg0 i) e1)
    match c, hc with
    | 0, hc =>
      rw [Nat.mul_zero] at hc
      rw [← FRC.Nat.add_sub_of_le hij, hc, Nat.add_zero]
    | c + 1, hc =>
      have : p - 1 ≤ j - i := by rw [hc]; exact Nat.le_mul_of_pos_right _ (Nat.zero_lt_succ c)
      exact absurd (Nat.lt_of_le_of_lt this (Nat.lt_of_le_of_lt (Nat.sub_le j i) hj)) (Nat.lt_irrefl _)
  exact match Nat.lt_or_ge i j with
    | .inl hlt => key (Nat.le_of_lt hlt) hj h
    | .inr hge => (key hge hi h.symm).symm

/-- A14 — every prime carries a frame: the prime shell `𝔽_p` has a drive `g`, a primitive root of order `p − 1`, and
its powers `g^m`, `m < p − 1`, reach every nonzero residue (`⟨g⟩ = 𝔽_p^×`, the pigeonhole). -/
theorem exists_drive (hp : FRC.Nat.isPrime p) :
    ∃ g : Shell p, (g ^ (p - 1) = 1 ∧ ∀ l, l < p - 1 → 0 < l → g ^ l ≠ 1) ∧
      ∀ v, v < p → 0 < v → ∃ m, m < p - 1 ∧ (g ^ m).val = v := by
  obtain ⟨g, hg0, hg1, hgl⟩ := exists_primitive hp
  have hp1 : 0 < p - 1 := by
    match p, hp.1 with
    | k + 2, _ => exact Nat.zero_lt_succ k
  have hg : HasOrder g (p - 1) := ⟨hp1, hg1, hgl⟩
  refine ⟨g, ⟨hg1, hgl⟩, fun v hv hv0 => ?_⟩
  have hp' : p = p - 1 + 1 := (FRC.Nat.sub_add_cancel Pos.pos).symm
  have hinj : ∀ i j, i < p - 1 → j < p - 1 → (g ^ i).val = (g ^ j).val → i = j := fun i j hi hj e =>
    primitive_pow_inj hp hg0 hg hi hj (ext e)
  have hb : ∀ e, Pigeonhole.mem e (imageList (fun m => (g ^ m).val) (p - 1)) → 1 ≤ e ∧ e ≤ p - 1 := fun e he =>
    match mem_imageList he with
    | ⟨m, _, hm⟩ =>
      ⟨Nat.pos_of_ne_zero (fun h0 => pow_ne_zero hp hg0 m (ext (by rw [hm, h0]; rfl))),
       by rw [← hm]; exact Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (g ^ m).lt (Nat.le_of_eq hp'))⟩
  exact mem_imageList (Pigeonhole.mem_of_nodup_of_length (p - 1) _ (imageList_nodup hinj (Nat.le_refl _)) hb
    (imageList_length _ _) v hv0 (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hv (Nat.le_of_eq hp'))))

end Prime
end Shell
end FRC
