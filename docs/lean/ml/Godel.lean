import Mathlib
import FrcLedger.Theme.Logic
import FrcLedger.Keys.Logic

/-!
# 25-göd — incompleteness without infinity: the paper module on Mathlib (migrated 20 October 2026)

The predicate declarations of *Incompleteness Without Infinity* (tree `25-godel-20260614`) on Mathlib's hierarchy,
`FRC.Godel.p25NNN`, each the conjunction of the theorems its ledger row cites, and the paper's old names as aliases. Since
the migration of 20 October 2026 the theorems live in the logic theme's `FrcLedger/Theme/Logic.lean`: the pigeonhole on a
finite carrier and every model of `Q` infinite (25:C1), completeness and decidability (25:C2), the `m + 1` sentences
(25:C5), the storage encodings and aliasing (25:D1, D3), the Catalan bound of abundance (25:E1), the records (25:E2), the
dense coding (25:F4), the second-order quantifier over a finite domain (25:H2). The axioms of each declaration are in
`lean/axioms.log`.
-/

open FirstOrder FirstOrder.Language

namespace FRC.Godel

/-! ## Old names: every declaration below is an alias of `FRC.Logic`'s, under the paper's name -/

section aliases
variable {L : Language} {M : Type*} [L.Structure M]

/-- 25:C1, 25:C3 (Proposition noQ, the finite form) — `FRC.Logic.finite_succ_onto` under the paper's name: on a finite carrier an injective map is onto. -/
theorem finite_succ_onto {A : Type*} [Finite A] (S : A → A) (hinj : Function.Injective S) (z : A) : ∃ x, S x = z :=
  FRC.Logic.finite_succ_onto S hinj z
/-- 25:C1 (Proposition noQ) — `FRC.Logic.infinite_of_succ` under the paper's name: a carrier with an injective successor that omits an element is infinite. -/
theorem infinite_of_succ {A : Type*} (S : A → A) (z : A) (hinj : Function.Injective S) (hz : ∀ x, S x ≠ z) :
    Infinite A := FRC.Logic.infinite_of_succ S z hinj hz
/-- 25:C2, 25:C3 (Proposition complete) — `FRC.Logic.theory_complete` under the paper's name: the complete theory of a structure is complete. -/
theorem theory_complete [Nonempty M] : (L.completeTheory M).IsComplete := FRC.Logic.theory_complete
/-- 25:C2 (Proposition complete, the decision) — `FRC.Logic.decTheory` under the paper's name: membership in the theory of a finite structure is decidable, by exhaustive evaluation. -/
@[instance_reducible] def decTheory [Fintype M] [DecidableEq M]
    (hR : ∀ (n : ℕ) (R : L.Relations n) (x : Fin n → M), Decidable (Structure.RelMap R x)) :
    DecidablePred (· ∈ L.completeTheory M) := FRC.Logic.decTheory hR
/-- 25:C5 — the sentences `φ, ¬φ, ¬¬φ, …` (`FRC.Logic.nots`). -/
abbrev nots := @FRC.Logic.nots
/-- 25:C5 — `FRC.Logic.nots_injective` under the paper's name: the sentences `¬^i φ` are pairwise distinct. -/
theorem nots_injective (L : Language) : Function.Injective (nots L) := FRC.Logic.nots_injective L
/-- 25:C5 (Remark tarski) — `FRC.Logic.nots_collide` under the paper's name: the `m + 1` sentences outnumber the `m` elements, so every numbering gives two of them one number. -/
theorem nots_collide {L : Language} {M : Type*} [Fintype M] (f : L.Sentence → M) :
    ∃ i j, i < j ∧ j ≤ Fintype.card M ∧ nots L i ≠ nots L j ∧ f (nots L i) = f (nots L j) := FRC.Logic.nots_collide f
/-- 25:D1 (Theorem part) — `FRC.Logic.no_injective_encoding` under the paper's name: with `a^K < m` no encoding of the elements by `K`-letter words is injective. -/
theorem no_injective_encoding {A Alph : Type*} [Fintype A] [Fintype Alph] (K : ℕ)
    (h : Fintype.card Alph ^ K < Fintype.card A) (ρ : A → (Fin K → Alph)) : ¬ Function.Injective ρ :=
  FRC.Logic.no_injective_encoding K h ρ
/-- 25:D3 (Lemma wrap (1)) — `FRC.Logic.reading_identifies` under the paper's name: fewer readings than elements identify two elements. -/
theorem reading_identifies {A R : Type*} [Fintype A] [Fintype R] (h : Fintype.card R < Fintype.card A) (ρ : A → R) :
    ∃ x y, x ≠ y ∧ ρ x = ρ y := FRC.Logic.reading_identifies h ρ
/-- 25:D3 (Lemma wrap (1)) — `FRC.Logic.alias_fibre` under the paper's name: some reading stands for at least `m / R` elements. -/
theorem alias_fibre {A R : Type*} [Fintype A] [Fintype R] [DecidableEq R] [Nonempty R] (ρ : A → R) :
    ∃ y, Fintype.card A ≤ Fintype.card R * Fintype.card {x // ρ x = y} := FRC.Logic.alias_fibre ρ
/-- 25:D3 (Lemma wrap (1)) — `FRC.Logic.alias_two` under the paper's name: with `R < m` some reading stands for two elements. -/
theorem alias_two {A R : Type*} [Fintype A] [Fintype R] [DecidableEq R] [Nonempty R]
    (h : Fintype.card R < Fintype.card A) (ρ : A → R) : ∃ y, 2 ≤ Fintype.card {x // ρ x = y} := FRC.Logic.alias_two h ρ
/-- 25:D3 (Lemma wrap (1)) — `FRC.Logic.alias_outside` under the paper's name: every element outside a maximal faithfully read range is read as one inside it. -/
theorem alias_outside {A R : Type*} (ρ : A → R) (S : Set A) (hS : Set.InjOn ρ S)
    (hmax : ∀ T : Set A, S ⊆ T → Set.InjOn ρ T → T = S) (x : A) (hx : x ∉ S) : ∃ s ∈ S, ρ s = ρ x :=
  FRC.Logic.alias_outside ρ S hS hmax x hx
/-- 25:E1 (Lemma abundance) — `FRC.Logic.two_pow_le_catalan` under the paper's name: `2^n ≤ C_{n+1}`. -/
theorem two_pow_le_catalan (n : ℕ) : 2 ^ n ≤ catalan (n + 1) := FRC.Logic.two_pow_le_catalan n
/-- 25:E1 (Lemma abundance) — `FRC.Logic.cohort_lower` under the paper's name: the cohort of true equations, `2^{n+6} ≤ C(C_{n+5}, 2)`. -/
theorem cohort_lower (n : ℕ) : 2 ^ (n + 6) ≤ (catalan (n + 5)).choose 2 := FRC.Logic.cohort_lower n
/-- 25:E1 (Lemma abundance) — `FRC.Logic.abundance` under the paper's name: at least `2^n` binary trees with `n + 1` nodes. -/
theorem abundance (n : ℕ) : 2 ^ n ≤ (BinaryTree.treesOfNumNodesEq (n + 1)).card := FRC.Logic.abundance n
/-- 25:E2 (Proposition reach) — `FRC.Logic.records_lt` under the paper's name: the records of length at most `B` over `a` letters number fewer than `a^{B+1}`. -/
theorem records_lt (a B : ℕ) (ha : 2 ≤ a) : ∑ i ∈ Finset.range (B + 1), a ^ i < a ^ (B + 1) :=
  FRC.Logic.records_lt a B ha
/-- 25:F4 (Lemma density) — `FRC.Logic.dense_coding` under the paper's name: an injective coding of the length-`n` strings by `k`-tuples needs `|A|^n ≤ |M|^k`. -/
theorem dense_coding {A M : Type*} [Fintype A] [Fintype M] (n k : ℕ) (c : (Fin n → A) → (Fin k → M))
    (hc : Function.Injective c) : Fintype.card A ^ n ≤ Fintype.card M ^ k := FRC.Logic.dense_coding n k c hc
/-- 25:H2 (Theorem finiteness, the finite direction) — `FRC.Logic.decideAllRelations` under the paper's name: a quantifier over the relations of a finite domain is decided by enumeration. -/
def decideAllRelations {M : Type*} [Fintype M] [DecidableEq M] (k : ℕ) (P : Finset (Fin k → M) → Prop)
    [DecidablePred P] : Decidable (∀ R, P R) := FRC.Logic.decideAllRelations k P
/-- 25:H2, 25:H4 (Theorem finiteness, the finite direction) — `FRC.Logic.card_relations` under the paper's name: the `k`-ary relations on `M` number `2^{m^k}`. -/
theorem card_relations (M : Type*) [Fintype M] [DecidableEq M] (k : ℕ) :
    Fintype.card (Finset (Fin k → M)) = 2 ^ (Fintype.card M ^ k) := FRC.Logic.card_relations M k

end aliases

-- Ledger predicates of 25-godel (generated by make_predicates.py from docs/25-godel/25-godel-ledger.json; edit the ledger, not this section)
/-- 25:C1 (p25010) — No finite structure interprets $\mathsf{Q}$: a model of $\mathsf{Q}$ has an injective successor with $0$ outside its range, and on a finite set an injective map is onto. -/
theorem p25010 : (∀ {A : Type u_1} [Finite A] (S : A → A), Function.Injective S → ∀ (z : A), ∃ x, S x = z) ∧ ∀ {A : Type u_2} (S : A → A) (z : A), Function.Injective S → (∀ (x : A), S x ≠ z) → Infinite A :=
  @FRC.LedgerML.p25010
/-- 25:C2 (p25011) — Completeness and decidability: for finite $\M$ the theory $\Th(\M)$ is complete, consistent and decidable by exhaustive evaluation. A sentence of quantifier depth $q$ takes at most $c\,m^{q}$ atomic evaluations, $c$ depending on its length. One first-order sentence $\sigma_{\M}$ characterises $\M$ up to isomorphism. Cited definitions (not proofs): FRC.Godel.decTheory. -/
theorem p25011 : ∀ {L : FirstOrder.Language} {M : Type u_1} [L.Structure M] [Nonempty M], (L.completeTheory M).IsComplete :=
  @FRC.LedgerML.p25011
/-- 25:C3 (p25012) — Vacuity: over a fixed finite $\M$ neither incompleteness theorem has an instance. $\Th(\M)$ is consistent, effectively axiomatisable and complete. The hypothesis that fails is the interpretation of $\mathsf{Q}$ (C1). No sentence true in $\M$ is undecided by $\Th(\M)$. -/
theorem p25012 : (∀ {A : Type u_1} [Finite A] (S : A → A), Function.Injective S → ∀ (z : A), ∃ x, S x = z) ∧ ∀ {L : FirstOrder.Language} {M : Type u_2} [L.Structure M] [Nonempty M], (L.completeTheory M).IsComplete :=
  @FRC.LedgerML.p25012
/-- 25:C5 (p25014) — Tarski scoped: the $m+1$ sentences $\varphi,\neg\varphi,\dots,\neg^{m}\varphi$ outnumber the $m$ elements of $\M$, so every numbering of the sentences by elements of $\M$ gives two of them the same number. Truth in $\M$ is defined externally by a finite table with the evaluation procedure of C2. What fails is the internalisation of truth. -/
theorem p25014 : ∀ {L : FirstOrder.Language} {M : Type u_1} [Fintype M] (f : L.Sentence → M), ∃ i j, i < j ∧ j ≤ Fintype.card M ∧ FRC.Logic.nots L i ≠ FRC.Logic.nots L j ∧ f (FRC.Logic.nots L i) = f (FRC.Logic.nots L j) :=
  @FRC.LedgerML.p25014
/-- 25:D1 (p25015) — Relational diagonal: an agent of storage capacity $K$ with $a^{K}<m$ has no injective encoding of the elements of $\M$ into its storage states. Every internal representation identifies distinct elements. A fortiori the agent holds no faithful model of $\M$ that also represents the model's own encoding map. -/
theorem p25015 : ∀ {A : Type u_1} {Alph : Type u_2} [Fintype A] [Fintype Alph] (K : ℕ), Fintype.card Alph ^ K < Fintype.card A → ∀ (ρ : A → Fin K → Alph), ¬Function.Injective ρ :=
  @FRC.LedgerML.p25015
/-- 25:D3 (p25017) — Wrap, aliasing: every total assignment of storage readings to the elements of $\M$ identifies distinct elements when $a^{K}<m$. Some reading stands for at least $\lceil m/a^{K}\rceil\ge2$ elements. Every element outside a maximal faithfully represented range is read as an alias of one inside it. -/
theorem p25017 : (∀ {A : Type u_1} {R : Type u_2} [Fintype A] [Fintype R], Fintype.card R < Fintype.card A → ∀ (ρ : A → R), ∃ x y, x ≠ y ∧ ρ x = ρ y) ∧ (∀ {A : Type u_3} {R : Type u_4} [Fintype A] [Fintype R] [DecidableEq R] [Nonempty R] (ρ : A → R), ∃ y, Fintype.card A ≤ Fintype.card R * Fintype.card { x // ρ x = y }) ∧ (∀ {A : Type u_5} {R : Type u_6} [Fintype A] [Fintype R] [DecidableEq R] [Nonempty R], Fintype.card R < Fintype.card A → ∀ (ρ : A → R), ∃ y, (2 : ℕ) ≤ Fintype.card { x // ρ x = y }) ∧ ∀ {A : Type u_7} {R : Type u_8} (ρ : A → R) (S : Set A), Set.InjOn ρ S → (∀ (T : Set A), S ⊆ T → Set.InjOn ρ T → T = S) → ∀ x ∉ S, ∃ s ∈ S, ρ s = ρ x :=
  @FRC.LedgerML.p25017
/-- 25:E1 (p25019) — Abundance: the closed terms over $\{1,+\}$ with $\ell$ leaves are the full binary trees, $C_{\ell-1}\ge2^{\ell-2}$ in number. In $\M_p$ all have the value $\ell\bmod p$, so any two give a true equation of length $O(\ell)$, at least $2^{\ell}$ of them for $\ell\ge6$. The true sentences of length at most $L$ number at least $2^{\alpha L}$ for large $L$, $\alpha>0$ constant. -/
theorem p25019 : (∀ (n : ℕ), (2 : ℕ) ^ n ≤ catalan (n + (1 : ℕ))) ∧ (∀ (n : ℕ), (2 : ℕ) ^ (n + (6 : ℕ)) ≤ (catalan (n + (5 : ℕ))).choose (2 : ℕ)) ∧ ∀ (n : ℕ), (2 : ℕ) ^ n ≤ (BinaryTree.treesOfNumNodesEq (n + (1 : ℕ))).card :=
  @FRC.LedgerML.p25019
/-- 25:E2 (p25020) — Vanishing reach: an agent of capacity $(K,H)$ certifies at most $a^{B+1}$ sentences over all its runs, the records being strings of length at most $B$. The certified fraction of the truths of length at most $L$ (E1) is at most $a^{B+1}/2^{\alpha L}$, below $1/N$ as soon as $\alpha L>(B+1)\log_2a+\log_2N$. -/
theorem p25020 : ∀ (s K : ℕ), (2 : ℕ) ≤ s → ∑ i ∈ Finset.range (K + (1 : ℕ)), s ^ i < s ^ (K + (1 : ℕ)) :=
  @FRC.LedgerML.p25020
/-- 25:F4 (p25048) — Density: $m$ has $d$ base-$a$ digits. An injective coding of length-$n$ strings by $k$-tuples, $k\ge1$, needs $m^{k}\ge a^{n}$, so $n<dk$. In F2's $\delta(u)=\exists v\,(\mathrm{Diag}(u,v)\wedge\theta(v))$ let $v$ have $k$ coordinates and $u$ have $k_{1}$. Each coordinate of $v$ is named three times, each of $u$ once. So $\lvert\delta\rvert\ge2c(k)+c(k+k_{1})$, and $\lambda=\delta(\ulcorner\delta\urcorner)$ has $\lvert\lambda\rvert\ge3c(k)+k_{1}$, $c(j)$ the total length of the $j$ shortest names. -/
theorem p25048 : ∀ {A : Type u_1} {M : Type u_2} [Fintype A] [Fintype M] (n k : ℕ) (c : (Fin n → A) → Fin k → M), Function.Injective c → Fintype.card A ^ n ≤ Fintype.card M ^ k :=
  @FRC.LedgerML.p25048
/-- 25:H2 (p25036) — Finiteness, the finite direction: for finite $\M$ the full second-order theory $\ThSO(\M)$ is decidable. A second-order quantifier over $k$-ary relations ranges over the $2^{m^{k}}$ subsets of $\M^{k}$, and exhaustive evaluation decides every second-order sentence. Cited definitions (not proofs): FRC.Godel.decideAllRelations. -/
theorem p25036 : ∀ (M : Type u_1) [Fintype M] [DecidableEq M] (k : ℕ), Fintype.card (Finset (Fin k → M)) = (2 : ℕ) ^ Fintype.card M ^ k :=
  @FRC.LedgerML.p25036
/-- 25:H4 (p25038) — Determinacy meets effectivity only on the finite. The structures whose entire theory, second-order included under full semantics, is decidable are exactly the finite ones, in H3's sense of infinite (H2, H3). Infinite structures offer determinacy at grade (i) or effectivity over a fragment. Finitude delivers both, at grade (ii). -/
theorem p25038 : ∀ (M : Type u_1) [Fintype M] [DecidableEq M] (k : ℕ), Fintype.card (Finset (Fin k → M)) = (2 : ℕ) ^ Fintype.card M ^ k :=
  @FRC.LedgerML.p25038
-- end ledger predicates

end FRC.Godel
