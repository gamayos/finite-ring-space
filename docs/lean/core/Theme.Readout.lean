import FrcCore.Theme.Window

/-!
# FrcCore.Theme.Readout — the far window's readout of a clock (21-gravity, Proposition 8.2; rows B12, C12)

A window of `H` far ticks, opened at a registered tick of the clock, registers `a H / b` completed ticks of a clock whose
composed rate against the far cut is the rational `a/b`: the unit-pulse sequence `s_k = ⌊k a/b⌋` of the pulse law (21:C27)
read at `k = H`, a tick counted whole (the window count of Lemma 3.3(i), `FRC.Relaxation.count`, rounds a weight and is a
different rule). The window registers no tick exactly when `a H < b`, and the first cut outside the operational cut (the
outermost cut with no tick) registers exactly one tick when the per-cell change of the composed rate is at most one half,
`2 M ≤ q` with `q = r(r + 1)` (22 November 2026, the follow-up review of 21-gravity).

* `clockTicks` — the readout `a H / b`.
* `no_tick_iff` — no tick exactly when `a H < b`.
* `one_tick_outside` — exactly one tick one cut out when `2 M ≤ q`.

Axiom-free: natural-number arithmetic on counts, the division algorithm's quotient face from `Theme/Window.lean`.
-/

namespace FRC.Relaxation

/-- 21:B12, 21:C12 — a window of `H` far ticks, opened at a registered tick of the clock, registers `a H / b` completed ticks of
a clock whose composed rate against the far cut is the rational `a/b`: the unit-pulse sequence `s_k = ⌊k a/b⌋` (`pulse_law`)
read at `k = H`, a tick counted whole (the window count of Lemma 3.3(i), `count`, rounds a weight). -/
def clockTicks (a b H : Nat) : Nat := a * H / b

/-- 21:C12 — the window registers no tick exactly when `a H < b`: the clock's rate against the far cut is below the floor
`1/H`. -/
theorem no_tick_iff (a b H : Nat) (hb : 0 < b) : clockTicks a b H = 0 ↔ a * H < b := by
  unfold clockTicks
  constructor
  · intro h0
    have e := FRC.Nat.div_spec b hb (a * H)
    rw [h0, Nat.mul_zero, Nat.zero_add] at e
    rw [e]; exact FRC.Nat.mod_lt' _ hb
  · intro hlt
    exact FRC.Nat.div_unique hlt (by rw [Nat.mul_zero, Nat.zero_add])

/-- 21:C12 — one tick at the first cut outside the operational cut. The cut's clock registers no tick in the window
(`a H < b`); the rate one cut out is the cut's divided by `1 − M/q`, with `q = r(r + 1)` the product of the cell's two
decoherence counts, that is `a q / (b (q − M))`, and it registers at least one tick, the cut being the outermost with none.
When `2 M ≤ q`, the per-cell change of the composed rate at most one half, it registers exactly one. -/
theorem one_tick_outside (a b H q M : Nat) (hM : M < q) (h2 : 2 * M ≤ q) (hin : a * H < b)
    (hout : b * (q - M) ≤ a * q * H) : clockTicks (a * q) (b * (q - M)) H = 1 := by
  unfold clockTicks
  have hq : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le M) hM
  -- a q H < b q ≤ 2 b (q − M)
  have h1 : a * q * H < b * q := by
    rw [FRC.Nat.mul_assoc, Nat.mul_comm q H, ← FRC.Nat.mul_assoc]; exact FRC.Nat.mul_lt_mul_of_lt_of_pos hin hq
  have hMq : M ≤ q - M := FRC.Nat.le_sub_of_add_le (by rw [← Nat.two_mul]; exact h2)
  have h3 : q ≤ (q - M) + (q - M) := by
    have e : q = M + (q - M) := (FRC.Nat.add_sub_of_le (Nat.le_of_lt hM)).symm
    calc q = M + (q - M) := e
      _ ≤ (q - M) + (q - M) := Nat.add_le_add_right hMq _
  have h4 : b * q ≤ b * (q - M) + b * (q - M) := by
    rw [← Nat.mul_add]; exact Nat.mul_le_mul_left b h3
  have hlt : a * q * H < b * (q - M) + b * (q - M) := Nat.lt_of_lt_of_le h1 h4
  exact FRC.Nat.div_unique (FRC.Nat.sub_lt_of_lt_add hlt hout)
    (by rw [Nat.mul_one, FRC.Nat.add_sub_of_le hout])

end FRC.Relaxation
