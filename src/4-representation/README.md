# 4-representation validation package

Validation package of *Universal Latent Representation in Finite Ring Continuum* (Akhtman, Entropy 2026, 28, 40),
`4-rep` of the FRC corpus, added with the paper's predicate ledger (Section 8, 17 September 2026). Three block
scripts, thirteen checks (eleven exact, two chart), standard library only, driven by `4-representation-main.ipynb`
(Google Colab, *Runtime → Run all*, ≈ 30 s) or by `run_all.py`.

Every check names the row(s) of the paper's predicate ledger it witnesses (25 rows in blocks A–E, V, O, cited as
`4:XN`; public copy `docs/4-representation/4-representation-ledger.html`), and the ledger's source column cites the
check ids in return. Where a row is proved in Lean (`lean/FrcCore/Representation.lean` with no axioms, or
`lean/FrcLedger/Representation.lean` on Mathlib), the check here is the instance the reader can run.

The package decides the paper's set theory by exhaustion: on every finite model with `|Z| ≤ 3`, `|X| ≤ 4` and
`|W| = |Z|`, adequacy (`E ∘ g` a bijection `Z → W`) forces the observation map injective, two adequate representations
of one observation map are related by the unique bijection `ψ = φ₂ ∘ φ₁⁻¹` with `E₂ ∘ g = ψ ∘ E₁ ∘ g`, the charts
`ψ_m = ι_m ∘ φ_m` are injective with bijective transitions `Ψ_{m→n}` composing as they should, the canonical
`ι_m = φ_m⁻¹` makes every chart the inclusion, and the lifts `L_m = φ_m⁻¹ ∘ E_m` invert the observation maps. On the
shell it adds what the paper's setting supplies: the host bound `|W_m| = |Z| ≤ p`, the affine frames of `F_p` as the
charts that respect its arithmetic (1:C2), the character chart on a sphere of radius `√(p−1)` (exactly, in `F_p`'s
own arithmetic), the quantisation count with exponent `d − 1`, and the Gödel code with its reduction modulo a prime
above its maximum.

Run: `python3 run_all.py` (python ≥ 3.8, no third-party packages; ≈ 1 s). Each block also runs on its own.

| id | script | kind | claim | ledger row |
|---|---|---|---|---|
| `A1` | `a_adequacy.py` | EXACT | adequacy forces `g` injective; the adequate `E` number `\|Z\|! \|W\|^(\|X\|−\|Z\|)` for injective `g`, none otherwise — 123 observation maps over seven model sizes | `4:B4` |
| `A2` | `a_adequacy.py` | EXACT | `ψ = φ₂ ∘ φ₁⁻¹` is the unique bijection `W₁ → W₂` with `E₂ ∘ g = ψ ∘ E₁ ∘ g`; `E₂ = ψ ∘ E₁` on all of `X` only when `X = g(Z)` — 8096 pairs | `4:B5` |
| `A3` | `a_adequacy.py` | EXACT | Lemma 1 as images: `ψ(E₁(X)) = E₂(X) = W₂` on every pair | `4:B5` |
| `A4` | `a_adequacy.py` | EXACT | Theorem 1: `ψ_m` injective for every injective `ι_m` (60 × 60 embeddings into `F₅`); `Ψ_{m→n}` a bijection of the images with inverse `Ψ_{n→m}`; `ι_m = φ_m⁻¹` makes every chart the inclusion | `4:C1`, `4:C2` |
| `A5` | `a_adequacy.py` | EXACT | Corollaries 1–2: `L_m ∘ g_m = id`, `L_m x` the unique `z` with `E_m x = φ_m z`, `L_m(g_m z) = L_n(g_n z)` | `4:C3`, `4:C4` |
| `B1` | `b_shell.py` | EXACT | `\|W_m\| = \|Z\| ≤ p`; the least shell hosting `N` states is the least prime `p = 4κ+1 ≥ N` (`N ≤ 60`); the canonical `ι_m` on `F₁₃` with three modalities of quantised codes | `4:B6` |
| `B2` | `b_shell.py` | EXACT | the arithmetic charts of the shell are its `p(p−1)` affine frames; `Ψ_{m→n}` between two frames is one invertible affine map — `p = 5, 13, 17` | `4:C5` |
| `B3` | `b_shell.py` | EXACT | the `F₁₃` instance: canonical charts are the inclusion; random embeddings compose, `Ψ_{n→k} ∘ Ψ_{m→n} = Ψ_{m→k}`; the lifts recover every state | `4:C1`, `4:C3` |
| `C1` | `c_geometry.py` | CHART | the character chart `z ↦ (cos 2πkz/p, sin 2πkz/p)_k` has `‖Emb(z)‖² = p − 1` for every `z` and is translation-equivariant; a random chart is not on a sphere | `4:E1` |
| `C2` | `c_geometry.py` | EXACT | `Σ_k g^{kz} g^{k(n−z)} = n = p − 1` in `F_p` for every `z ≤ n` and every generator; translation multiplies coordinate `k` by `g^{ka}` | `4:E1` |
| `C3` | `c_geometry.py` | CHART | grid points within `Δ/2` of the sphere of radius `R` number `~ (R/Δ)^(d−1)`: least-squares exponents 1.05 and 1.96 at `d = 2, 3` | `4:E2` |
| `C4` | `c_geometry.py` | EXACT | `G(x) = 2^a 3^b 5^c` injective on `{0..4}³` (125 codes, maximum 810 000); injective modulo `q = 810 013`, the least prime above the maximum; modulo 101 there are 41 collisions | `4:E3` |
| `C5` | `c_geometry.py` | EXACT | `2^a 3^b` injective on `a, b ≤ 20` (441 codes); signed coordinates in `{−2..2}³` coded after the shift `+2` | `4:E3` |

`results.json` carries one record per check (id, rows, script, kind, claim, PASS/FAIL, detail); the site generator
reads it to colour the witnesses on the public ledger page.
