/-!
# FrcCore.Theme.Brackets — window fractions, their brackets and the chains (the yangmills theme's first file, 8 November 2026)

The arithmetic in which the chart's constants enter the core: a window fraction `a/b` (1:D8, `FRC.Shell.Frame.frac_window`) is a
pair of an integer and a positive natural; on every shell with `2|a|b < p` it is read as the residue `a·b⁻¹`, two such
fractions with equal residues are equal, and their order is the order of the cross-products. Every comparison here is a
comparison of cross-products in the integers. The file holds the fractions (`WF`), their brackets (`BR`), the artanh chain of
the logarithm with its geometric majorant (`atanhChain`, `atanhTail`, `lnBr`: `ln x = k ln 2 + ln r` for `x = 2^k r`,
`y = (r − 1)/(r + 1) ≤ 1/3`), the six-place bracket of `π` (`piBr`), the readings of the chains at stage `12`
(`chain_readings`), and power series with window-fraction coefficients (`wsMul`, `wsInv`). Split from `Theme/YangMills.lean`
on 8 November 2026 (the round-01 revision of 46-yangmills; T15's note), which imports it. No axioms; imports nothing.
-/

namespace FRC.YangMills

/-- The `k`-th entry of a list, or `d` past its end (`List.getD` carries `propext`; this does not). -/
def nth {α : Type} (d : α) : List α → Nat → α
  | [], _ => d
  | x :: _, 0 => x
  | _ :: xs, n + 1 => nth d xs n

/-! ## Window fractions and the chains of the logarithm

A window fraction `a/b` (1:D8, `FRC.Shell.Frame.frac_window`) is a pair of an integer and a positive natural; on every shell
with `2|a|b < p` it is read as the residue `a·b⁻¹`, two such fractions with equal residues are equal, and their order is the
order of the cross-products. Every comparison below is a comparison of cross-products in the integers. -/

/-- A window fraction: numerator and positive denominator. -/
abbrev WF := Int × Nat

namespace WF

def norm (x : WF) : WF :=
  let g := Nat.gcd x.1.natAbs x.2
  if g ≤ 1 then x else (x.1 / (g : Int), x.2 / g)
def add (x y : WF) : WF := norm (x.1 * y.2 + y.1 * x.2, x.2 * y.2)
def mul (x y : WF) : WF := norm (x.1 * y.1, x.2 * y.2)
def neg (x : WF) : WF := (-x.1, x.2)
def sub (x y : WF) : WF := add x (neg y)
def ofNat (n : Nat) : WF := (n, 1)
def frac (a : Int) (b : Nat) : WF := norm (a, b)
/-- The reciprocal of a nonzero fraction. -/
def inv (x : WF) : WF := if x.1 < 0 then (-(x.2 : Int), x.1.natAbs) else ((x.2 : Int), x.1.natAbs)
def div (x y : WF) : WF := mul x (inv y)
def lt (x y : WF) : Bool := decide (x.1 * (y.2 : Int) < y.1 * (x.2 : Int))
def le (x y : WF) : Bool := decide (x.1 * (y.2 : Int) ≤ y.1 * (x.2 : Int))
def pow (x : WF) : Nat → WF
  | 0 => (1, 1)
  | n + 1 => mul (pow x n) x
def sumRange (f : Nat → WF) : Nat → WF
  | 0 => (0, 1)
  | n + 1 => add (sumRange f n) (f n)
def max (x y : WF) : WF := if lt x y then y else x
def min (x y : WF) : WF := if lt x y then x else y
end WF

/-- A bracket `[lo, hi]` of window fractions. -/
abbrev BR := WF × WF

namespace BR
def add (x y : BR) : BR := (WF.add x.1 y.1, WF.add x.2 y.2)
def sub (x y : BR) : BR := (WF.sub x.1 y.2, WF.sub x.2 y.1)
def smul (n : Nat) (x : BR) : BR := (WF.mul (WF.ofNat n) x.1, WF.mul (WF.ofNat n) x.2)
/-- The bracket lies strictly inside `(lo, hi)`. -/
def within (x : BR) (lo hi : WF) : Bool := WF.lt lo x.1 && WF.lt x.2 hi
end BR

/-- The artanh chain at stage `n`: `2 Σ_{k<n} y^{2k+1}/(2k+1)`, the frame's reading of `ln((1 + y)/(1 − y))` — a
𝔽Q-native chain of geometric rate (13-epi's class of the Machin chain), its partial sums window fractions. -/
def atanhChain (y : WF) (n : Nat) : WF :=
  WF.mul (WF.ofNat 2) (WF.sumRange (fun k => WF.div (WF.pow y (2 * k + 1)) (WF.ofNat (2 * k + 1))) n)

/-- The geometric majorant of the chain's remainder, `2 y^{2n+1} / ((2n + 1)(1 − y²))` for `0 ≤ y < 1`. -/
def atanhTail (y : WF) (n : Nat) : WF :=
  WF.div (WF.mul (WF.ofNat 2) (WF.pow y (2 * n + 1))) (WF.mul (WF.ofNat (2 * n + 1)) (WF.sub (WF.ofNat 1) (WF.mul y y)))

/-- `x ≥ 1` written as `2^k · r` with `1 ≤ r < 2`: `(k, r)` (with the fuel `f`). -/
def reduce2 (x : WF) : Nat → Nat × WF
  | 0 => (0, x)
  | f + 1 => if WF.lt x (WF.ofNat 2) then (0, x) else let (k, r) := reduce2 (WF.div x (WF.ofNat 2)) f; (k + 1, r)

/-- The bracket of `ln x` for a window fraction `x ≥ 1` at stage `n`: `x = 2^k r`, `ln x = k ln 2 + ln r`, each logarithm
read by the artanh chain at `y = (x − 1)/(x + 1) ≤ 1/3` with the chain's partial sum below and the sum plus the
majorant above. -/
def lnBr (x : WF) (n : Nat) : BR :=
  let y2 := WF.frac 1 3
  let l2 : BR := (atanhChain y2 n, WF.add (atanhChain y2 n) (atanhTail y2 n))
  let (k, r) := reduce2 x 64
  let y := WF.div (WF.sub r (WF.ofNat 1)) (WF.add r (WF.ofNat 1))
  BR.add (BR.smul k l2) (atanhChain y n, WF.add (atanhChain y n) (atanhTail y n))

/-- The six-place bracket of `π`, `3.141592 < π < 3.141593`: the chart's reading of the constant, the one Mathlib certifies
(`Real.pi_gt_d6`, `Real.pi_lt_d6`) and 13-epi's Machin bracket contains; as a bracket of window fractions. -/
def piBr : BR := (WF.frac 3141592 1000000, WF.frac 3141593 1000000)

/-- The chains at stage `12`: `ln 2 ∈ (0.69314, 0.69315)`, `ln 3 ∈ (1.0986, 1.0987)`, `ln 5 ∈ (1.6094, 1.6095)`,
`π ∈ (3.14159, 3.14160)`. -/
theorem chain_readings :
    BR.within (lnBr (WF.ofNat 2) 12) (WF.frac 69314 100000) (WF.frac 69315 100000) = true ∧
    BR.within (lnBr (WF.ofNat 3) 12) (WF.frac 10986 10000) (WF.frac 10987 10000) = true ∧
    BR.within (lnBr (WF.ofNat 5) 12) (WF.frac 16094 10000) (WF.frac 16095 10000) = true ∧
    BR.within piBr (WF.frac 314159 100000) (WF.frac 314160 100000) = true := by
  decide +kernel

/-! ## Power series in window fractions -/

def wsCoeff (a : List WF) (k : Nat) : WF := nth (0, 1) a k

def wsMul (a b : List WF) (n : Nat) : List WF :=
  (List.range n).map fun k =>
    (List.range (k + 1)).foldl (fun s i => WF.add s (WF.mul (wsCoeff a i) (wsCoeff b (k - i)))) (0, 1)

def wsInv (a : List WF) (a0inv : WF) : Nat → List WF
  | 0 => []
  | n + 1 =>
    let r := wsInv a a0inv n
    if n = 0 then [a0inv]
    else r ++ [WF.neg (WF.mul a0inv ((List.range n).foldl
      (fun s i => WF.add s (WF.mul (wsCoeff a (i + 1)) (wsCoeff r (n - 1 - i)))) (0, 1)))]

def fact : Nat → Nat
  | 0 => 1
  | k + 1 => fact k * (k + 1)

end FRC.YangMills
