import FrcCore.Theme.Orbital

/-!
# FrcCore.Theme.Cells — the orbital shell and its spherical completion, coded and decided (the geometry theme)

Moved here from the paper module `FrcCore/Complex.lean` on 6 November 2026, every name unchanged.

The completion of the orbital shell `S_p` (Def. 3.1 of 2-geometry) as a finite cell complex on vertex codes:
`N = 0`, the interior vertices `(a, m)` for `1 ≤ a ≤ π − 1`, `m < n`, and `S`; the faces as cyclic vertex lists
(north triangles, quadrilaterals, south triangles); the edges as the faces' sides. `closed p` checks that every
edge lies in exactly two faces and that every vertex link is a single cycle (2:C3, the exhaustive incidence of
the ledger); `cellular p u` checks whether the reindexing `ρ_u` carries faces to faces (2:B4); `poleExchange`
checks the meridian reversal on the completion. Everything is a computation the kernel evaluates by `decide`.
No axioms.
-/

namespace FRC
namespace Complex

/-- The vertex code of `(a, m)` on the shell with `n` phases: `1 + (a − 1)·n + m`. -/
def vtx (n a m : Nat) : Nat := 1 + (a - 1) * n + m % n

/-- The south pole: the vertex after the last interior latitude `a = π − 1`. -/
def south (n pi : Nat) : Nat := 1 + (pi - 1) * n

/-- The faces of the completion, as vertex lists. -/
def faces (n pi : Nat) : List (List Nat) :=
  let north := (List.range n).map fun m => [0, vtx n 1 m, vtx n 1 (m + 1)]
  let quads := ((List.range (pi - 2)).map fun a' => (List.range n).map fun m =>
      [vtx n (a' + 1) m, vtx n (a' + 2) m, vtx n (a' + 2) (m + 1), vtx n (a' + 1) (m + 1)]).foldr (· ++ ·) []
  let souths := (List.range n).map fun m => [vtx n (pi - 1) m, south n pi, vtx n (pi - 1) (m + 1)]
  north ++ quads ++ souths

/-- The sides of a face, as unordered pairs `(min, max)`. -/
def sides : List Nat → List (Nat × Nat)
  | [] => []
  | f@(v :: _) =>
    let rec go : List Nat → List (Nat × Nat)
      | [] => []
      | [w] => [(min w v, max w v)]
      | w :: (w' :: rest) => (min w w', max w w') :: go (w' :: rest)
    go f

def vertexCount (n pi : Nat) : Nat := south n pi + 1

/-- A face with its sides computed once: `(vertices, sides)`. -/
abbrev Face := List Nat × List (Nat × Nat)

def withSides (fs : List (List Nat)) : List Face := fs.map fun f => (f, sides f)

/-- Two faces are adjacent around `v` when they share a side through `v`. -/
def adjacentAt (v : Nat) (f f' : Face) : Bool :=
  f.2.any fun s => (s.1 == v || s.2 == v) && f'.2.contains s

/-- The neighbours of `cur` around `v` other than `prev` (and `cur` itself). -/
def nextFaces (v : Nat) (L : List Face) (prev cur : Face) : List Face :=
  L.filter fun f' => !(f'.1 == cur.1) && !(f'.1 == prev.1) && adjacentAt v cur f'

/-- Walk the link from `f0` along `cur`, never turning back, for `fuel` steps; the number of steps taken until
`f0` is reached again (`fuel` if never). -/
def walk (v : Nat) (L : List Face) (f0 : Face) : Nat → Face → Face → Nat → Nat
  | 0, _, _, k => k
  | fuel + 1, prev, cur, k =>
    match nextFaces v L prev cur with
    | f' :: [] => if f'.1 == f0.1 then k + 1 else walk v L f0 fuel cur f' (k + 1)
    | [] => fuel + k + 1
    | _ :: _ :: _ => fuel + k + 1

/-- The link of `v` is a single cycle: every face around `v` has exactly two neighbours there, and the walk from
the first face returns to it after exactly `|L|` steps. -/
def linkIsCycle (fs : List Face) (v : Nat) : Bool :=
  let L := fs.filter fun f => f.1.contains v
  match L with
  | [] => false
  | f0 :: _ =>
    L.all (fun f => (L.filter (fun f' => !(f'.1 == f.1) && adjacentAt v f f')).length == 2) &&
    (match nextFaces v L f0 f0 with
     | f1 :: _ => walk v L f0 L.length f0 f1 1 == L.length
     | [] => false)

/-- The number of occurrences of `s` in `E`. -/
def count (s : Nat × Nat) : List (Nat × Nat) → Nat
  | [] => 0
  | e :: E => (if e == s then 1 else 0) + count s E

/-- Every side of every face lies in exactly two faces: the sides are bucketed by their smaller vertex and each
side occurs exactly twice in its bucket. -/
def edgesInTwoFaces (fs : List (List Nat)) : Bool :=
  let E := (withSides fs).foldr (fun f acc => f.2 ++ acc) []
  let V := fs.foldr (fun f acc => f.foldr (fun w acc' => if acc'.contains w then acc' else w :: acc') acc) []
  V.all fun v =>
    let B := E.filter fun s => s.1 == v
    B.all fun s => count s B == 2

/-- 2:C3, the exhaustive incidence: the completion is a closed surface. -/
def closed (p : Nat) : Bool :=
  let n := p - 1
  let pi := n / 2
  let fs := faces n pi
  edgesInTwoFaces fs && (List.range (vertexCount n pi)).all fun v => linkIsCycle (withSides fs) v

/-- The reindexing `ρ_u` on vertex codes: `(a, m) ↦ (a, u·m mod n)`, the poles fixed. -/
def rhoV (n pi u : Nat) (v : Nat) : Nat :=
  if v == 0 then 0 else if v == south n pi then v else
    let a := (v - 1) / n + 1
    let m := (v - 1) % n
    vtx n a (u * m)

/-- The meridian reversal on the completion: `N ↔ S`, `(a, m) ↦ (π − a, m)`. -/
def sigmaV (n pi : Nat) (v : Nat) : Nat :=
  if v == 0 then south n pi else if v == south n pi then 0 else
    let a := (v - 1) / n + 1
    let m := (v - 1) % n
    vtx n (pi - a) m

/-- A vertex map is cellular when it carries every face onto a face (as vertex sets). -/
def cellularMap (fs : List (List Nat)) (φ : Nat → Nat) : Bool :=
  fs.all fun f => fs.any fun f' => (f.map φ).all (fun w => f'.contains w) && f'.all (fun w => (f.map φ).contains w)

/-- 2:B4 — whether `ρ_u` is a cellular automorphism of the completion. -/
def cellular (p u : Nat) : Bool :=
  let n := p - 1
  let pi := n / 2
  cellularMap (faces n pi) (rhoV n pi u)

/-- 2:B4 — whether the pole exchange is cellular on the completion. -/
def poleExchange (p : Nat) : Bool :=
  let n := p - 1
  let pi := n / 2
  cellularMap (faces n pi) (sigmaV n pi)

/-- 2:C2 [value] — the counts on `𝔽₁₃`: `62` vertices, `72` faces of the completion. -/
theorem counts13 : vertexCount 12 6 = 62 ∧ (faces 12 6).length = 72 := by decide +kernel

/-- 2:C3 [value] — the completion is a closed surface on `𝔽₁₃` (62 vertices, 72 faces). -/
theorem closed13 : closed 13 = true := by decide +kernel


/-- The orbital shell before the collapse: the terminal latitude `a = π` kept, so the last ring of quadrilaterals
ends on it and nothing closes over it. -/
def facesOpen (n pi : Nat) : List (List Nat) :=
  let north := (List.range n).map fun m => [0, vtx n 1 m, vtx n 1 (m + 1)]
  let quads := ((List.range (pi - 1)).map fun a' => (List.range n).map fun m =>
      [vtx n (a' + 1) m, vtx n (a' + 2) m, vtx n (a' + 2) (m + 1), vtx n (a' + 1) (m + 1)]).foldr (· ++ ·) []
  north ++ quads

/-- 2:C3, 2:B4 [value] — the shell itself is not closed (its terminal latitude is a boundary: those sides lie in
one face only), so the meridian reversal has nothing to act on before the collapse. -/
theorem open13 : edgesInTwoFaces (facesOpen 12 6) = false ∧ (facesOpen 12 6).length = 72 := by decide +kernel

/-- 2:B4, 2:C4 [value] — on `𝔽₁₃` (`n = 12`) the reindexing `ρ_u` is cellular exactly for `u ∈ {1, 11}` among the
units `{1, 5, 7, 11}`, and the pole exchange is cellular on the completion. -/
theorem census13 :
    cellular 13 1 = true ∧ cellular 13 5 = false ∧ cellular 13 7 = false ∧ cellular 13 11 = true ∧
    poleExchange 13 = true := by decide +kernel

/-! ## The edge metric and the curvature of the completion (2:C5, C6, C7) -/

/-- The neighbours of every vertex code: the other ends of the sides through it, without repetition. -/
def nbrs (fs : List (List Nat)) (N : Nat) : List (List Nat) :=
  let E := (withSides fs).foldr (fun f acc => f.2 ++ acc) []
  (List.range N).map fun v =>
    E.foldr (fun s acc =>
      let w := if s.1 == v then s.2 else if s.2 == v then s.1 else v
      if w == v || acc.contains w then acc else w :: acc) []

/-- The `i`-th entry of a list of lists (`[]` past the end), by structural recursion. -/
def nth : List (List Nat) → Nat → List Nat
  | [], _ => []
  | l :: _, 0 => l
  | _ :: L, i + 1 => nth L i

/-- The latitude index `a` of a vertex code (`0` at the north pole, `pi` at the south pole). -/
def lat (n pi v : Nat) : Nat := if v == 0 then 0 else if v == south n pi then pi else (v - 1) / n + 1
def isPole (n pi v : Nat) : Bool := v == 0 || v == south n pi
/-- The cyclic distance of two phase labels on the cycle of `n` phases. -/
def cyc (n m k : Nat) : Nat := let d := (m + n - k % n) % n; min d (n - d)

/-- 2:C5 — the distance formula: `min(|a − a'| + δ(m, m'), a + a', 2π − a − a')`, with `δ` the cyclic distance on the
phase cycle (`0` when a pole is involved). -/
def edgeDist (n pi u v : Nat) : Nat :=
  let a := lat n pi u; let b := lat n pi v
  let δ := if isPole n pi u || isPole n pi v then 0 else cyc n ((u - 1) % n) ((v - 1) % n)
  let da := if a ≤ b then b - a else a - b
  min (da + δ) (min (a + b) (2 * pi - a - b))

/-- `12 K(v)`, the combinatorial curvature `K(v) = 1 − deg(v)/2 + Σ_{f ∋ v} 1/|f|` times twelve, as an integer. -/
def curv12 (fs : List (List Nat)) (A : List (List Nat)) (v : Nat) : Int :=
  12 - 6 * ((nth A v).length : Int) +
    fs.foldr (fun f acc => if f.contains v then acc + (if f.length == 3 then 4 else 3) else acc) 0

/-- The adjacency of the completion on `𝔽₁₃` (`n = 12`, `π = 6`, 62 vertex codes), written out. -/
def A13 : List (List Nat) := [[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 1], [0, 2, 13, 12], [0, 1, 14, 3], [0, 2, 15, 4], [0, 3, 16, 5], [0, 4, 17, 6], [0, 5, 18, 7], [0, 6, 19, 8], [0, 7, 20, 9], [0, 8, 21, 10], [0, 9, 22, 11], [0, 10, 23, 12], [0, 11, 24, 1], [1, 14, 25, 24], [2, 13, 26, 15], [3, 14, 27, 16], [4, 15, 28, 17], [5, 16, 29, 18], [6, 17, 30, 19], [7, 18, 31, 20], [8, 19, 32, 21], [9, 20, 33, 22], [10, 21, 34, 23], [11, 22, 35, 24], [12, 23, 36, 13], [13, 26, 37, 36], [14, 25, 38, 27], [15, 26, 39, 28], [16, 27, 40, 29], [17, 28, 41, 30], [18, 29, 42, 31], [19, 30, 43, 32], [20, 31, 44, 33], [21, 32, 45, 34], [22, 33, 46, 35], [23, 34, 47, 36], [24, 35, 48, 25], [25, 38, 49, 48], [26, 37, 50, 39], [27, 38, 51, 40], [28, 39, 52, 41], [29, 40, 53, 42], [30, 41, 54, 43], [31, 42, 55, 44], [32, 43, 56, 45], [33, 44, 57, 46], [34, 45, 58, 47], [35, 46, 59, 48], [36, 47, 60, 37], [37, 50, 61, 60], [38, 49, 61, 51], [39, 50, 61, 52], [40, 51, 61, 53], [41, 52, 61, 54], [42, 53, 61, 55], [43, 54, 61, 56], [44, 55, 61, 57], [45, 56, 61, 58], [46, 57, 61, 59], [47, 58, 61, 60], [48, 59, 61, 49], [50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 49]]

/-- The written adjacency is the adjacency of the faces of the completion. -/
theorem A13_eq : A13 = nbrs (faces 12 6) 62 := by decide +kernel

/-- 2:C5, 2:C7 [value] — on `𝔽₁₃` the distance formula is the graph distance of the completion: for every source `s` it
vanishes at `s`, changes by at most one along every edge, and every other vertex has a neighbour one step closer. These
three properties characterise the distance from `s` (induction on the formula's value). The diameter is `π = 6`, between
the poles. -/
theorem metric13 :
    (List.range 62).all (fun s => edgeDist 12 6 s s == 0 && (List.range 62).all fun v =>
      (nth A13 v).all (fun w => edgeDist 12 6 s w ≤ edgeDist 12 6 s v + 1 && edgeDist 12 6 s v ≤ edgeDist 12 6 s w + 1) &&
      (v == s || (nth A13 v).any fun w => edgeDist 12 6 s w + 1 == edgeDist 12 6 s v)) = true ∧
    edgeDist 12 6 0 (south 12 6) = 6 := by decide +kernel

/-- 2:C6 [value] — on `𝔽₁₃` the curvature: zero on the band `2 ≤ a ≤ π − 2`, `1/6` on the latitudes `1` and `π − 1`,
`1 − (p − 1)/6 = −1` at each pole (twelve times: `0`, `2`, `−12`); the total is `24/12 = 2`, the Euler characteristic. -/
theorem curvature13 :
    (List.range 62).all (fun v => curv12 (faces 12 6) A13 v ==
      (if isPole 12 6 v then -12 else if lat 12 6 v == 1 || lat 12 6 v == 5 then 2 else 0)) = true ∧
    (List.range 62).foldr (fun v acc => acc + curv12 (faces 12 6) A13 v) 0 = 24 := by decide +kernel

/-- 2:C7 [value] — on `𝔽₁₃` the band is a square grid: every vertex with `2 ≤ a ≤ 4` has four neighbours, pairwise at
distance two (the unit ball of the square lattice), while each pole has `p − 1 = 12` neighbours. -/
theorem flat13 :
    (List.range 62).all (fun v => !(2 ≤ lat 12 6 v && lat 12 6 v ≤ 4 && !isPole 12 6 v) ||
      ((nth A13 v).length == 4 &&
       (nth A13 v).all fun u => (nth A13 v).all fun w => u == w || edgeDist 12 6 u w == 2)) = true ∧
    (nth A13 0).length = 12 ∧ (nth A13 (south 12 6)).length = 12 := by decide +kernel

end Complex
end FRC
