# 38-s13 validation suite

Discipline: every exact claim in the paper is integer-pinned; floating point
appears only in declared chart residuals, never behind a T-tagged claim.

## In-tree

| script | class | checks | claims backed |
|---|---|---|---|
| `check_s13.js` | EXACT | 57/57 | blocks A--D of the predicate ledger: the pair constants (A1), the tower identity (A2), the channel gcds and the spinorial norm (A3, Thm 6), the Carrier quarter roots (A4, Thm 3), the recurrence data (B5), the (53,13) kill test (C6), the meridian station sets (D1, D6), the covering with its multiplicity law (D7), the ramification (D8) and fusion (D9) congruences; the registration fibre product (x -> x^kappa, y -> y^S, |R| = 696); the k_B c quarter root ((k_B c)^2 = -1 representative-free, drawn evaluation 124*159 = 144 = hbar); the A2 general form (4a - kappa b = 1 mod 4 kappa, (1,1) only at kappa = 3) |
| `check_o1.js` | EXACT | 10/10 | the two faces of the leak (C7): angular kappa/S, temporal kappa/(2S), ratio 2 = the double cover; the closure structure (696/1392, the half event); the dictionary p_sl = 3(S/kappa) r_g and the capacity reading; the p=53 regression (auxiliary modulus 157); the PPN-lattice forcing (ratio 2 iff 2 gamma - beta = 1) |
| `o1_gr_chart.py` | [APPROX] symbolic | 10/10 | the continuum comparison chart for O1 (Statement 11): apsidal coefficient 2 - beta + 2 gamma, deficit coefficient 3/2 (PPN-free), ratio deviation (2/3)(2 gamma - beta - 1), the dictionary match; the Brans--Dicke exclusion (combination -2/(2+omega), GR limit); sympy Rationals end to end, no floats |
| `check_o2.js` | EXACT | 11/11 | the covering parity theorem (D12, Thm 12): the reflection identity (p = 5,13,17,29), mu in {1,3} with the row-parity decider, the shell-parity position law and the 72/72 direct/echo balance, the per-node candidate identities (four-sum p-2), the shell-1 closed form, the Omega-blind sweep; the all-shell parity table (Lemma 1), closing the decider and position law at every shell |
| `check_o3.js` | EXACT | 7/7 | the drawn winding-family layer (O3, sec. 9): the winding-1/5 identity with the M0/M3 station tables, the 144-slot containment in the drawn observable sector, the covering multiset with parity multiplicities, the axis passages 13j/m (drawn iff m >= 4), the ramification 13/(2m) |

Run: `node check_s13.js && node check_o1.js && node check_o2.js && node check_o3.js && python3 o1_gr_chart.py` (each exits nonzero on any failure). Python dependency: `sympy>=1.12` (verified with 1.14).

## External witnesses (the laboratory suites)

Repository: https://github.com/gamayos/frc-numerics (1-phase). Six suites,
192 checks, all integer-exact in the exact layers; `node run-all.js` runs all
six and exits nonzero on any failure. Frozen phase-5 build: 189.

| suite | checks | claims backed |
|---|---|---|
| `verify-233.js` | 84 | pair dynamics, events, octant bridge (Thm 1--2), precession (Thm 4), the mass--energy channel (Thm 6) |
| `verify-sky.js` | 28 | the sky map (B1--B3), fibered covers, radial ladder, central product isomorphism |
| `verify-space.js` | 25 | register, cone arithmetic, the winding spectrum (sec. 5), curl algebra (C1) |
| `verify-f13.js` | 25 | the shell operator core: H^7 = 0, ord(U) = 13, U exactly unitary (sec. 5) |
| `verify-hopf.js` | 10 | the finite Hopf fibration (Thm 5), Omega-blind at p = 5 |
| `verify-render.js` | 20 | the production rendering (B4, B6--B7, C2--C5, D1, D3--D5, D10) |

The exactness boundary (ledger row V2): station incidence, causal ordering,
winding, anchoring, and the registered flow are exact; connecting curves are
the declared spacetime chart, each constant declared [approx] in the paper.
