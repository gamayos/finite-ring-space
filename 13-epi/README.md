# 13-epi validation suite

Float-free discipline (paper-ready protocol, Step 8): an exact (T) claim is checked in integer or rational arithmetic; a continuum object may appear only as the declared object of study (the IEEE-754 readout itself) or as an [approx]-tagged statistical reading.

| script | class | status | claims backed |
|---|---|---|---|
| `validate_towers.py` | EXACT (int + Fraction only; brackets self-certified) | **63/63 PASS** (run 14 Jul 2026) | Prop. tower-e, Prop. tower-pi, Cayley identities (Def. cayley), orientation rule (Rem. orient), two-level horizon block (§10): pinning relation 2·pi_A+1 ≡ 0 and the H(pi_A)=2 pin on every shell; the full-population height run H(x)=min_{a≥1} max(a,\|⟨ax⟩\|), smallest-primitive-root frame, minimum over the two chiralities, for all 500 shells p ≡ 1 (mod 4), p ≤ 8009 — horizon band H ≤ 2√p, exactly 68 shells with H ≤ 10, height-2 set exactly {13, 1933, 4177, 5857} (median H/√p = 0.525, diagnostic); wrap-free accessible window |
| `validate_e.py` | MIXED | full run recorded in `results_e.txt` (re-run 13 Jul 2026, byte-identical to the source run, zero failures) | Thms enclosure-e, readout-e, wall-e, antiperiod; Prop. duals; Exp. blind; Prop. calib; Exp. null |
| `validate_pi.py` | MIXED | full run recorded in `results_pi.txt` (run 13 Jul 2026, zero failures) | Thms enclosure, readout-pi, window, halfwall, secondorder; Prop. lucas; the arcsin first-order vanishing scan (Thm vanish), 428 odd primes 5 ≤ p < 3000 with T(3)=1 the recorded sole exception; the p = 13 showcase residue line w_1..w_6 = 4, 5, 10, 9, 6, 11 |
| `validate_pi2.py` | EXACT (int + Fraction only) | full run recorded in `results_pi2.txt` (run 13 Jul 2026, zero failures) | Thm quarter; Thm vanish proof ingredients (A+B=2L with the formal-antiderivative bookkeeping, m ≤ 60; Lerch to p < 500; binomial transfer); Thm super: the mod-p² supercongruence for 5 ≤ p < 300, the third-order Bernoulli law σ_p/p² ≡ (−1)^((p+1)/2)·B_(p−3)/36 (mod p) for all 60 primes 5 ≤ p < 300 with B_(p−3) from the exact Bernoulli recurrence, the blind-range Euler congruence for 5 ≤ p < 80 |
| `kurepa_wall.c` | EXACT (`__int128` modular) | 22,043 primes < 2.5e5, zero failures (source run) | Thm wall-e (D-form + non-vanishing) |

MIXED classification, catalogued:
- `validate_e.py`: (a) the binary64 constant obtained as a Python float is the *object of study* of Thm readout-e (the readout), compared exactly against rationals — sanctioned; (b) a 500-digit Decimal reference for e is a controlled bounded-error reference — sanctioned, queued for re-basing on the chain's own certified brackets at the promotion pass; (c) the calibration scan and null-experiment statistics are [approx] by declaration in-paper.
- `validate_pi.py`: same pattern (binary64 readout as object; high-precision reference for the enclosure comparisons; Wieferich search and quotient moments are exact congruence arithmetic).

Revision history:
- Round-01 (13 Jul 2026, `reviews/round-01/disposition.md`): `validate_pi.py` gained the p = 13 showcase residue-line check (erratum E1 was invisible to the suite) and the first-order-vanishing pass criterion now excludes the documented p = 3 exception instead of counting it as a failure; `validate_pi2.py` extended the mod-p² range 240 → 300, replaced the third-order scan with the Bernoulli-law check (exact Bernoulli recurrence), and extended the key-identity check to m ≤ 60 via the finite formal-antiderivative route; all three Python scripts now write their results files next to the script.
- Round-02 (14 Jul 2026, `reviews/round-02/disposition.md`): `validate_towers.py` height block extended from an eleven-shell single-chirality sample to the full 500-shell population with the small-height count and the exceptional set asserted exactly; `validate_e.py` output unified to `results_e.txt`.

Provenance: `validate_e.py`, `validate_pi.py`, `validate_pi2.py`, `kurepa_wall.c` are the scripts of the source memoranda (`reports/epi-report-2/`, `reports/epi-report-3/`), renamed to the canonical suite form and amended per the revision history above; their recorded outputs ship alongside. `validate_towers.py` is new with the manuscript. Full-suite re-run gate before snapshot promotion.

Run: `python3 validate_towers.py`; `python3 validate_e.py`; `python3 validate_pi.py`; `python3 validate_pi2.py`; `cc -O2 kurepa_wall.c -o kurepa_wall && ./kurepa_wall`.
