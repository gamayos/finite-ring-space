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

namespace FRC.Geometry
-- Ledger rows of 2-geometry (generated by make_rows.py from docs/2-geometry/2-geometry-ledger.json; edit the ledger, not this section)
/-- 2:B4 — Cellular automorphisms of the index grid: $m\mapsto\pm m+c$, the dihedral group of the phase cycle; on the completion also meridian reversal $a\mapsto\pi-a$, exchanging the poles. The reindexing $\rho_{u}\colon m\mapsto um$ preserves latitude adjacency only for $u\equiv\pm1\pmod{\p-1}$; $\sigma$ is not a map of $\Sp$ ($\north$ one vertex, $L_{\pi}$ has $\p-1$); decided on $\p\le29$. -/
theorem row_B4 : (∀ (n u : Nat), (3 : Nat) ≤ n → ((∀ (m : Nat), m < n → FRC.Geometry.Adj n (FRC.Geometry.rho n u m) (FRC.Geometry.rho n u ((m + (1 : Nat)) % n))) ↔ u % n = (1 : Nat) ∨ u % n = n - (1 : Nat))) ∧ FRC.Complex.cellular (13 : Nat) (1 : Nat) = true ∧ FRC.Complex.cellular (13 : Nat) (5 : Nat) = false ∧ FRC.Complex.cellular (13 : Nat) (7 : Nat) = false ∧ FRC.Complex.cellular (13 : Nat) (11 : Nat) = true ∧ FRC.Complex.poleExchange (13 : Nat) = true :=
  And.intro @FRC.Geometry.rho_adj_iff (@FRC.Complex.census13)
/-- 2:C2 — Counts: $|V|=\pi(\p-1)+1$, $|E|=2\pi(\p-1)$, $|F|=\pi(\p-1)$, $\chi(\Sp)=1$; the completion has $(\pi-1)(\p-1)+2$ vertices, $(2\pi-1)(\p-1)$ edges, $\pi(\p-1)$ faces, $\chi=2$ (Rem.~\ref{rem:cell-counts}). -/
theorem row_C2 : (∀ (m n : Nat), (m + (1 : Nat)) * n + (1 : Nat) + (m + (1 : Nat)) * n = (2 : Nat) * ((m + (1 : Nat)) * n) + (1 : Nat) ∧ m * n + (2 : Nat) + (m + (1 : Nat)) * n = ((2 : Nat) * m + (1 : Nat)) * n + (2 : Nat)) ∧ FRC.Complex.vertexCount (12 : Nat) (6 : Nat) = (62 : Nat) ∧ (FRC.Complex.faces (12 : Nat) (6 : Nat)).length = (72 : Nat) :=
  And.intro @FRC.Geometry.euler_characteristic (@FRC.Complex.counts13)
/-- 2:C3 — Canonical spherical completion: collapsing $L_{\pi}$ to $\south$ gives a closed orientable surface --- every edge in two faces, every vertex link a cycle --- with $\chi=2$, hence $S^{2}$ (A3), on every shell (Thm.~\ref{thm:combinatorial-sphere}; decided on $\p\in\{5,13,17,29\}$ by exhaustive incidence). -/
theorem row_C3 : FRC.Complex.closed (5 : Nat) = true ∧ FRC.Complex.closed (13 : Nat) = true ∧ FRC.Complex.closed (17 : Nat) = true ∧ FRC.Complex.edgesInTwoFaces (FRC.Complex.facesOpen (12 : Nat) (6 : Nat)) = false ∧ (FRC.Complex.facesOpen (12 : Nat) (6 : Nat)).length = (72 : Nat) :=
  And.intro @FRC.Complex.closed5 (And.intro @FRC.Complex.closed13 (And.intro @FRC.Complex.closed17 (@FRC.Complex.open13)))
/-- 2:C4 — Frame covariance: $\Sp$ is one complex for every generator --- the index grid $I_{\p}\times\Phi_{\p}$ with its step relations; the frame $\gen'=\gen^{u}$ moves the field labels, $a\gen^{m}\mapsto a\gen^{um}$, by the automorphism $\rho_{u}$ of $\Phi_{\p}$, not the cells. The map $\varphi_{u}$ of Prop.~\ref{prop:shell-covariance} is cellular only for $u\equiv\pm1$. -/
theorem row_C4 : (∀ {p : Nat} [FRC.Pos p] {κ : Nat} {g : FRC.Shell p}, FRC.Shell.Frame p κ g → ∀ (u : Nat) (a : FRC.Shell p) (m : Nat), FRC.Geometry.label (g ^ u) a m = FRC.Geometry.label g a (FRC.Geometry.rho (p - (1 : Nat)) u m)) ∧ FRC.Complex.cellular (13 : Nat) (1 : Nat) = true ∧ FRC.Complex.cellular (13 : Nat) (5 : Nat) = false ∧ FRC.Complex.cellular (13 : Nat) (7 : Nat) = false ∧ FRC.Complex.cellular (13 : Nat) (11 : Nat) = true ∧ FRC.Complex.poleExchange (13 : Nat) = true :=
  And.intro @FRC.Geometry.label_covariance (@FRC.Complex.census13)
-- end ledger rows
end FRC.Geometry
