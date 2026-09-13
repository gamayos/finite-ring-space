# 14-entropy validation suite

Standalone: both scripts take no input and reference no path outside this
directory. Exit status 0 iff all asserted checks pass.

Naming note: the registrable *triangle* (renamed from "wedge"; script and
figure filenames retain the legacy `wedge` name).

## Run

```
python3 estimate_S.py                                    # channel/audit numerics
cd ../figures && python3 ../validation/make-wedge-2.py   # triangle figures + asserts
```

Pin the commit (or archival DOI) at submission; the manuscript cites this
directory as the reproduction of every quantitative claim.

| script | type | gate | verifies | deps |
|---|---|---|---|---|
| `estimate_S.py` | MIXED | asserts + [PASS] lines, exit 0 | **exact faces** (Ω=4S+1; S even; S≡1 mod 3; 4S+1 prime; octant count S/2 integral — integer counts on the toy Carrier Ω=2,408,561); **channel table** with per-row σ (stat+sys) from (Λ, H₀, a₀, t⋆=13.61±0.34 Valcin IV — one vintage everywhere); **concordance** over the 5 evidence rows, gauge 4a excluded (±17% half-range on √S, factor 1.9 on S) and the conventional channels alone (±14%, factor 1.7); **chart identity** S_Λ/S_rate=(H/H₀)²/Ω_Λ verified per row (the cluster split displays the Hubble tension; no framework content); **audit identity** t₀H_Λ=(2/3)artanh√Ω_Λ, π/4 inversion (Ω_Λ=0.6837, 0.19σ); **entailed rate** H₀=67.4±0.7 (independent-error approx ±0.65; full covariance not propagated), pulls Planck 0.1σ / TRGB 1.3σ / Cepheid 4.6σ; **stellar-age confrontation** at the declared vintage (population +0.5σ below the octant bound; prior-dependent inferred age −0.07σ, statistically consistent with the bound); **floor running** (Ciocan: constant floor disfavoured; endpoint 0.5σ; linear rate ~3σ heuristic, 95% bands symmetrised) | python3 stdlib |
| `make-wedge-2.py` | MIXED | asserts + [PASS] lines, exit 0 | triangle figures (`registrable-wedge-plain-*`, `wall-channels-*`, written to cwd — run from `figures/`): audit identities asserted before drawing (octant/t_P identity; two-cluster display ratio 1.71 on the Valcin-IV rows; r_H split; width identity log₁₀(r_H/ℓ_P)=log₁₀√(S/π) exact; entailed rate 67.4); diagonal regression k=3.032 over the 13 mid-triangle objects (intercept 1.00×10³ at the metre pivot — density units only at k=3), constrained k=3 density ρ̃=0.97×10³ kg/m³, sensitivity k=3.007 (15 incl. wall residents); wall intersections (Compton entry 5.3×10⁻¹² m; over-closure exit 1.8×10⁸ M☉, sensitivity band (1.4–2.8)×10⁸ across the four fit variants); electron/Sgr A* wall residency <0.01 dex | python3 + matplotlib |

## Register conventions (in-script)

| tokens | site | register |
|---|---|---|
| `math.pi`, `math.sqrt` | `estimate_S.py`: `S_of`, channel rows, concordance | `[approx]` chart readings of published data; the exact face is the count S=(Ω−1)/4 |
| `math.atanh`, `math.tanh` | audit + entailed-rate blocks | `[ΛCDM]` rival-chart identities, confrontation only |
| float means/divisions | cluster display, confrontations | comparison chart on `[approx]`/`[ΛCDM]` row values |

## Retired

`s-estimate.py`, `make-wedge.py`, `make-wedge-1.py` (superseded generations,
in `_to_delete/`). The concordance figure (`concordance-*.png`) currently has
no in-tree generator — regenerate or recreate the generator before submission.
