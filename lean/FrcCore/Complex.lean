import FrcCore.Geometry

/-!
# FrcCore.Complex — the orbital shell and its spherical completion, coded and decided

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

/-- 2:C3 [value] — the completion is a closed surface on `𝔽₅`, by exhaustive incidence. -/
theorem closed5 : closed 5 = true := by decide +kernel
/-- 2:C3 [value] — the completion is a closed surface on `𝔽₁₃` (62 vertices, 72 faces). -/
theorem closed13 : closed 13 = true := by decide +kernel
/-- 2:C3 [value] — the completion is a closed surface on `𝔽₁₇` (114 vertices, 128 faces); the kernel decides
it in a few seconds. -/
theorem closed17 : closed 17 = true := by decide +kernel


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

end Complex
end FRC
