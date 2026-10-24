"""p16_octant — the ledger file of 16-octant (22 October 2026), served as py/octant.py.

"Registrable depth and the dark-energy output over finite holographic substrate" (Akhtman, 2026). The paper's predicate
ledger carries the octant lemma and its outputs under the keys of 14-entropy (the register resolves each shared key to its
origin; its Lean declarations are linked at the Entropy modules, and its python check runs again here under the shared key;
decision D6 of the blueprint), two theorem rows of 38-s13 carried under the origin's keys and tag (A6 p38008, A7 p38004; the
station arithmetic and the octant mark, their Lean declarations at the module S13) and eleven rows of its own (A5, A8, A9, B6, B8, B9, B10, C5, C6, X4, P4;
keys p16001–p16011). This file reproduces every
numeral of the paper's Table 1, ledger rows and figures: the shared rows under their keys, the four new theorem rows (C5, C6, X4, P4)
as their deciding checks, each marked `# 16:XN (<key>)`.

The checks are EXACT or CHART, one kind per check. An EXACT check decides by integer arithmetic: the octant sector,
the instance clause and the octant mark on the instantiated Carrier (p, Ω) = (173, 30089), the minimal saturating tower
(00:F5; the author's decision of 22 October, in place of 14-entropy's 2 408 561), the dictionary, the exchange reading
as integer inequalities (the station bound 4d < Ω and the exchange count 2x ≤ S), and the coincidence of the exchange
reading's selection with the octant mark (2x ≡ S iff x = S/2 on the stations; the exponents S/2, S, 2S under the generator 3;
the square and fourth-power brackets of Ω). A CHART
check is a continuum reading: the chart theme's certified brackets (π from Machin's formula, e^x from its Taylor
series with the tail bound, artanh from its series with the tail bound) decide the inversion, the locus, the pulls and
the bound; the radiation root is a floating-point computation of the flat age integral, standard library only, with
the bracket it must fall in; every float of the determinations is converted exactly before a comparison. The
determinations are declared data with their sources: Planck 2018 VI Table 2 (TT,TE,EE+lowE+lensing alone and with BAO)
and DESI DR2 Results II Section VI (BAO alone; BAO with the CMB, the CMB being the Planck PR4 CamSpec likelihood with
Planck and ACT DR6 lensing).

No numeral above Ω ∼ 10¹²³ is formed: S enters only through the dictionary's ratios, and the instantiated Carrier is
30 089.

    python3 -m frc.ledgers.p16_octant         every block, the census; exit 1 if a check fails (≈ 1 s)
    python3 -m frc.ledgers.p16_octant C       one block (A to P)
    from frc.ledgers.p16_octant import R; R.predicate("16:C5")    one predicate: its blocks run once per session

Blocks:  A  the octant sector, the instance clause, the octant mark, the exchange equivalence (16:C1, X3; 16:B9, A7; 16:C6, X4)
         B  the dictionary and the exchange reading                                         (16:C2, A6; corroboration)
         C  the inversion, the brackets, the locus and the entailed rate                    (16:C3, C4, X1, X2, P2, P3; corroboration)
         D  the confrontation: the four landings, the deviations, the radiation and curvature roots   (16:C5)
         P  the matter fraction, the DESI falsifier, the bound at the DESI pair, the ages   (16:P4, P1)

Checks: 19, of them 7 EXACT (A1, A2, A3, A4, B1, B2, B3) and 12 CHART (C1, C2, C3, C4, C5, D1, D2, D3, D4, P1, P2, P3). The notebook frc/ledgers/p16_octant.ipynb
runs one predicate per cell, the cell's id its key.
"""
import math
import sys
from fractions import Fraction as Q

from frc.registry import Registry
from frc import chart as CH

# ---- the table of keys (hand-written pending the paper's posting; ci/make_ledgers.py generates it from the ledger JSON then) ----
PAPER = "16-octant"
KEYS = {"A1": "p14001", "A2": "p14004", "A3": "p14005", "A4": "p14007", "A5": "p16001",
        "A6": "p38008", "A7": "p38004", "A8": "p16007", "A9": "p16008",
        "B1": "p14010", "B2": "p14011", "B3": "p14014", "B4": "p14015", "B5": "p14016", "B6": "p16002", "B7": "p14009", "B8": "p16005", "B9": "p16006", "B10": "p16011",
        "C1": "p14023", "C2": "p14022", "C3": "p14024", "C4": "p14025", "C5": "p16003", "C6": "p16009",
        "X1": "p14030", "X2": "p14033", "X3": "p14031", "X4": "p16010",
        "P1": "p14037", "P2": "p14038", "P3": "p14039", "P4": "p16004"}
LEAN = {"A6": "core", "A7": "core", "C1": "core, ml", "C2": "core, ml", "C3": "ml", "C4": "ml", "C5": "ml",
        "C6": "ml", "X1": "ml", "X2": "ml", "X3": "core, ml", "X4": "ml", "P1": "ml", "P2": "ml", "P3": "ml", "P4": "ml"}
ORIGIN = {k: "14-entropy" for k, v in KEYS.items() if v.startswith("p14")}   # the shared keys: witnessed at their origin
ORIGIN.update({k: "38-s13" for k, v in KEYS.items() if v.startswith("p38")})     # the laboratory's theorems, at the module S13

LEAN_ONLY = ()

# The paper's predicate ledger (predicates cited as 16:XN): the predicate(s) each check witnesses.
LEDGER = {
    "A1": "16:C1, 16:X3", "A2": "16:C1", "A3": "16:B9, 16:C1, 16:A7", "A4": "16:C6, 16:X4",
    "B1": "16:C2", "B2": "16:C2", "B3": "16:C2, 16:A6",
    "C1": "16:C3, 16:X1, 16:X2", "C2": "16:P2", "C3": "16:C4", "C4": "16:P3", "C5": "16:P2, 16:P1",
    "D1": "16:C5", "D2": "16:C5, 16:X1", "D3": "16:C5", "D4": "16:C5",
    "P1": "16:P4", "P2": "16:P4", "P3": "16:P1",
}

BLOCK = {"A": "the octant sector, the instance clause, the octant mark and the exchange equivalence on the instantiated Carrier",
         "B": "the dictionary and the exchange reading",
         "C": "the inversion, the brackets, the locus and the entailed rate",
         "D": "the confrontation: the four landings, the deviations, the radiation and curvature roots",
         "P": "the matter fraction, the DESI falsifier, the bound at the DESI pair, the ages"}

# the deciding check of each witnessed predicate; the shared predicates are decided at their origin, corroborated here
PREDICATES = {"16:C1": "A1", "16:X3": "A1", "16:B9": "A3", "16:A7": "A3", "16:A6": "B3", "16:C2": "B1", "16:C3": "C1", "16:X1": "C1", "16:X2": "C1",
              "16:C4": "C3", "16:P2": "C2", "16:P3": "C4", "16:C5": "D1", "16:P4": "P1", "16:P1": "P3", "16:C6": "A4", "16:X4": "A4"}

R = Registry("16", "octant", LEDGER, PREDICATES, sources=[__file__])

# ---- declared data (the sources in the paper's row A5) ----------------------------------------------------------------
OMEGA_LAB = 30089                                      # the instantiated Carrier, Ω = 4S + 1 with S = 7 522: the minimal saturating tower (173, 30089), 00:F5
P_LAB = 173                                            # its Subject, p = 4κ + 1 with κ = 43
DETERMINATIONS = {                                     # name: (Ω_Λ, σ, H₀ or None, the flat-ΛCDM age in Gyr or None)
    "Planck 2018 alone":   (Q("0.6847"), Q("0.0073"), Q("67.36"), Q("13.797")),   # Planck 2018 VI, Table 2, TT,TE,EE+lowE+lensing
    "Planck 2018 + BAO":   (Q("0.6889"), Q("0.0056"), Q("67.66"), Q("13.787")),   # the same, with BAO
    "DESI DR2 BAO alone":  (Q("0.7025"), Q("0.0086"), None, None),                 # DESI DR2 Results II, §VI: Ω_m = 0.2975 ± 0.0086
    "DESI DR2 BAO + CMB":  (Q("0.6973"), Q("0.0036"), Q("68.17"), None),           # the same: Ω_m = 0.3027 ± 0.0036, H₀ = 68.17 ± 0.28
}
OMEGA_R = Q("9.2e-5")                                  # the radiation fraction [import]
OMEGA_K = (Q("0.0007"), Q("0.0019"))                     # the measured curvature, Planck 2018 VI with BAO (47b) [import]
STELLAR = (Q("13.61"), Q("0.34"))                      # the oldest cluster population, Valcin et al. 2026 (statistical and systematic combined)
INFERRED = (Q("13.81"), Q("0.34"))                     # the inferred cosmic age of the same work
TRGB = (Q("69.8"), Q("1.7"))                           # Freedman 2021
CEPHEID = (Q("73.04"), Q("1.04"))                      # Riess 2022
GYR_S = Q("1e9") * CH.JULIAN_YEAR                       # seconds per Gyr


def _inv_h_gyr(h0_kms):
    """1/H₀ in Gyr for H₀ in km s⁻¹ Mpc⁻¹, exactly."""
    return CH.MPC_KM / (Q(h0_kms) * GYR_S)


def _between(x, lo, hi):
    return Q(lo) < Q(x) < Q(hi)


def _landing(bracket, fit):
    """How far the determination `fit = (value, error)` lies above a bracket of the output, in units of the error:
    (fit − output)/error, a positive number when the output lies below the determination."""
    lo, hi = CH.sigma_bracket(bracket, fit)
    return (-hi, -lo)


# ---- A. the octant sector ---------------------------------------------------------------------------------------------
@R.block("A", BLOCK["A"])
def block_A():
    S = (OMEGA_LAB - 1) // 4
    # 16:C1 (p14023), 16:X3 (p14031)
    R.check("A1", "the octant sector exists iff S is even; on the instantiated Carrier S = 7 522 is even and 8 | 4S",
            4 * S + 1 == OMEGA_LAB and S % 2 == 0 and (4 * S) % 8 == 0 and 8 * (S // 2) == 4 * S,
            f"S = {S}, S/2 = {S // 2}, 8·(S/2) = 4S = {4 * S}")
    # 16:C1 (p14023): the character of order eight exists on the laboratory Carrier: a primitive root raised to (Ω−1)/8 has ζ⁴ ≡ −1
    primes, m, q = [], OMEGA_LAB - 1, 2                                     # the prime factors of Ω − 1 by trial division (2³·3761)
    while q * q <= m:
        if m % q == 0:
            primes.append(q)
            while m % q == 0: m //= q
        q += 1
    if m > 1: primes.append(m)
    g = next(g for g in range(2, 50) if all(pow(g, (OMEGA_LAB - 1) // q, OMEGA_LAB) != 1 for q in primes))   # a primitive root
    zeta = pow(g, (OMEGA_LAB - 1) // 8, OMEGA_LAB)
    R.check("A2", "the octant character on the instantiated Carrier: ζ⁴ ≡ −1 and ζ⁸ ≡ 1, and (2(ζ + ζ⁻¹))² ≡ 8",
            pow(zeta, 4, OMEGA_LAB) == OMEGA_LAB - 1 and pow(zeta, 8, OMEGA_LAB) == 1
            and (2 * (zeta + pow(zeta, -1, OMEGA_LAB))) ** 2 % OMEGA_LAB == 8,
            f"g = {g}, ζ = {zeta}")
    # 16:B9 (p16006), 16:C1 (p14023), 16:A7 (p38004): the instance clause S ≡ 2 (mod 4) and the octant mark (38-s13 A4 read at the instance): the 2-part of
    # the cycle is exactly C₈, Ω − 1 = 8·3761 with 3761 prime; p² < Ω ≤ (p+1)² (the saturating tower, 00:F5); κ odd; the chart
    # cardinals under the least primitive root 3: ζ₈ = 14004, h = 22003, ħ = 8086, ζ₈² = h, ħ + h = Ω; the octant exponent S/2 is
    # odd and g·ζ₈⁻¹ lies in the even-exponent layer (the completion: the octant carries the odd crossing classes)
    kap = (P_LAB - 1) // 4
    g0 = next(g for g in range(2, OMEGA_LAB) if all(pow(g, (OMEGA_LAB - 1) // q, OMEGA_LAB) != 1 for q in primes))   # the least primitive root
    z8, h, hbar = pow(g0, S // 2, OMEGA_LAB), pow(g0, S, OMEGA_LAB), pow(g0, 3 * S, OMEGA_LAB)
    v2 = 0; m2 = OMEGA_LAB - 1
    while m2 % 2 == 0: m2 //= 2; v2 += 1
    even_layer = {pow(g0, 2 * u, OMEGA_LAB) for u in range(2 * S)}
    R.check("A3", "the instance clause: S ≡ 2 (mod 4), the 2-part of the cycle exactly C₈, Ω − 1 = 8·3761 with 3761 prime, "
                  "p² < Ω ≤ (p+1)², κ odd; the octant mark ζ₈ = 14004, h = 22003, ħ = 8086 under the least primitive root 3, "
                  "ζ₈² = h, ħ + h = Ω, the octant exponent odd and g·ζ₈⁻¹ in the even layer",
            S % 4 == 2 and v2 == 3 and OMEGA_LAB - 1 == 8 * 3761 and m2 == 3761
            and all(3761 % d for d in range(2, 62)) and P_LAB * P_LAB < OMEGA_LAB <= (P_LAB + 1) ** 2 and kap % 2 == 1
            and 4 * kap + 1 == P_LAB and g0 == 3 and (z8, h, hbar) == (14004, 22003, 8086)
            and z8 * z8 % OMEGA_LAB == h and (hbar + h) % OMEGA_LAB == 0 and (S // 2) % 2 == 1
            and (g0 * pow(z8, -1, OMEGA_LAB)) % OMEGA_LAB in even_layer,
            f"S = {S}, S/2 = {S // 2}, v₂(Ω−1) = {v2}, GOM = {g0}, ζ₈ = {z8}, h = {h}, ħ = {hbar}")

    # 16:C6 (p16009), 16:X4 (p16010): the exchange reading and the octant mark coincide: on the stations x ≤ S the exchange count
    # 2x is the quarter exponent S exactly when x = S/2, the exponent of a primitive eighth root with square h; under the generator 3
    # the exponents S/2, S, 2S carry ζ₈ = 14004, h = 22003 and −1, the ring fourth, square and first roots of 4S ≡ −1; the
    # cardinality lies between the squares 173², 174² and between the fourth powers 13⁴, 14⁴ (the two horizons of the ladder at
    # the instance, as integer brackets)
    R.check("A4", "the exchange equivalence and the octant mark: {x ≤ S : 2x ≡ S (mod 4S)} = {S/2}; 3^(S/2) ≡ 14004 = ζ₈, 3^S ≡ 22003 = h, "
                  "3^(2S) ≡ −1, ζ₈² = h, ζ₈⁴ ≡ −1; 173² < Ω < 174² and 13⁴ < Ω < 14⁴",
            [x for x in range(S + 1) if (2 * x) % (4 * S) == S] == [S // 2]
            and pow(3, S // 2, OMEGA_LAB) == 14004 and pow(3, S, OMEGA_LAB) == 22003 and pow(3, 2 * S, OMEGA_LAB) == OMEGA_LAB - 1
            and pow(14004, 2, OMEGA_LAB) == 22003 and pow(14004, 4, OMEGA_LAB) == OMEGA_LAB - 1
            and 173 ** 2 < OMEGA_LAB < 174 ** 2 and 13 ** 4 < OMEGA_LAB < 14 ** 4,
            f"S/2 = {S // 2}: the one station whose exchange count is the quarter; 173² = {173 ** 2}, 174² = {174 ** 2}, 13⁴ = {13 ** 4}, 14⁴ = {14 ** 4}")


# ---- B. the dictionary and the exchange reading ---------------------------------------------------------------------------------------
@R.block("B", BLOCK["B"])
def block_B():
    S = (OMEGA_LAB - 1) // 4
    # 16:C2 (p14022)
    R.check("B1", "the exchange reading: 2x ≤ S iff x ≤ S/2 for every x below S, and the octant's count is the quarter, 2·(S/2) = S",
            all((2 * x <= S) == (x <= S // 2) for x in range(S + 1)) and 2 * (S // 2) == S,
            f"S = {S}, checked for every x ≤ S")
    # 16:C2 (p14022)
    R.check("B2", "the dictionary: (S/2)/(4S) of the cycle 2π r_H/c is (π/4) r_H/c, as a ratio of counts 1/8 = (π/4)/(2π)",
            Q(S // 2, 4 * S) == Q(1, 8),
            "the octant is one eighth of the cycle on the count face and on the chart face")
    # 16:C2 (p14022), 16:A6 (p38008): the station arithmetic (38-s13 A8/D1 read at κ = S): the station bound 4d < Ω ⟺ d ≤ S, the exchange count 2x a station
    # ⟺ x ≤ S/2, the deepest such x = S/2, and the exact addition of two stations below the period, 2S < 4S
    R.check("B3", "the station arithmetic at the instance: 4d < Ω iff d ≤ S on 0 ≤ d ≤ 2S+1; 4·(2x) < Ω iff x ≤ S/2 on 0 ≤ x ≤ S; "
                  "the deepest x with a station for its count is S/2; two stations sum below the period, 2S < 4S",
            all((4 * d < OMEGA_LAB) == (d <= S) for d in range(0, 2 * S + 2))
            and all((4 * (2 * x) < OMEGA_LAB) == (x <= S // 2) for x in range(0, S + 1))
            and max(x for x in range(S + 1) if 4 * (2 * x) < OMEGA_LAB) == S // 2 and 2 * S < 4 * S,
            f"S = {S}, S/2 = {S // 2}, 2S = {2 * S} < 4S = {4 * S}")


# ---- C. the inversion, the locus, the rate --------------------------------------------------------------------------------
@R.block("C", BLOCK["C"])
def block_C():
    om_lo, om_hi = CH.omega_lambda_bracket()
    # 16:C3 (p14024), 16:X1 (p14030), 16:X2 (p14033)
    R.check("C1", "Ω_Λ = tanh²(3π/8) between 0.68368 and 0.68369; the Planck-only landing between 0.13σ and 0.15σ",
            _between(om_lo, "0.68368", "0.68369") and _between(om_hi, "0.68368", "0.68369")
            and all(_between(s, "0.13", "0.15") for s in _landing((om_lo, om_hi), DETERMINATIONS["Planck 2018 alone"][:2])),
            f"Ω_Λ = {CH.omega_lambda():.6f}, lands {-CH.sigma(CH.omega_lambda(), tuple(float(v) for v in DETERMINATIONS['Planck 2018 alone'][:2])):.3f}σ below Planck alone",
            kind="CHART")
    lo, hi = CH.locus_bracket()
    h0 = CH.locus() / (float(STELLAR[0]) * 1e9 * float(CH.JULIAN_YEAR)) * float(CH.MPC_KM)
    err = h0 * float(STELLAR[1] / STELLAR[0])
    pulls = {n: (float(v[0]) - h0) / math.sqrt(float(v[1]) ** 2 + err ** 2) for n, v in
             [("Planck", (DETERMINATIONS["Planck 2018 alone"][2], Q("0.54"))), ("TRGB", TRGB), ("Cepheid", CEPHEID)]}
    # 16:P2 (p14038)
    h0_inf = CH.locus() / (float(INFERRED[0]) * 1e9 * float(CH.JULIAN_YEAR)) * float(CH.MPC_KM)
    err_inf = h0_inf * float(INFERRED[1] / INFERRED[0])
    R.check("C2", "the locus (π/4)/tanh(3π/8) between 0.9498 and 0.9499; on t★ = 13.61 ± 0.34 Gyr, H₀ = 68.2 ± 1.7 (an upper limit), 0.5σ from Planck, 0.65σ from TRGB, 2.4σ from the Cepheid ladder; on the inferred age 13.81 ± 0.34 Gyr, 67.3 ± 1.7",
            _between(lo, "0.9498", "0.9499") and _between(hi, "0.9498", "0.9499") and 68.15 < h0 < 68.25 and 1.70 < err < 1.71
            and abs(pulls["Planck"]) < 0.55 and 0.6 < pulls["TRGB"] < 0.7 and 2.35 < pulls["Cepheid"] < 2.45
            and 67.25 < h0_inf < 67.35 and 1.65 < err_inf < 1.70,
            f"locus = {CH.locus():.5f}; H₀ = {h0:.2f} ± {err:.2f}; pulls " + ", ".join(f"{k} {v:+.2f}σ" for k, v in pulls.items()) + f"; on the inferred age {h0_inf:.2f} ± {err_inf:.2f}",
            kind="CHART")
    # 16:C4 (p14025): with the Planck-only Λ (H_Λ = H₀√Ω_Λ, 1/H_Λ = 17.54 Gyr) the locus returns H₀ = 67.4 to 0.1 %
    planck = DETERMINATIONS["Planck 2018 alone"]
    h_lambda = float(planck[2]) * math.sqrt(float(planck[0]))
    inv_h_lambda = float(_inv_h_gyr(Q(h_lambda)))
    h_back = h_lambda / CH.tanh_octant()
    R.check("C3", "the entailed-rate consistency: the Planck-only Λ (1/H_Λ = 17.54 Gyr, depth 13.78 Gyr) returns H₀ = 67.4 km s⁻¹ Mpc⁻¹ to 0.1 %",
            abs(h_back - 67.4) / 67.4 < 1e-3 and 17.535 < inv_h_lambda < 17.545 and abs(13.80 / inv_h_lambda - 0.787) < 0.0005,
            f"1/H_Λ = {inv_h_lambda:.3f} Gyr, H_Λ = {h_lambda:.2f}, H₀ = H_Λ/tanh(3π/8) = {h_back:.2f}; 13.80/{inv_h_lambda:.2f} = {13.80 / inv_h_lambda:.4f}", kind="CHART")
    # 16:P2 (p14038), 16:P1 (p14037): the chart's own product at the Planck-only Ω_Λ, the Ω_Λ that accommodates the Cepheid pair, the separation rate
    t_h0 = lambda om: CH.lcdm_age(om) / math.sqrt(om)                       # t H₀ = t H_Λ / √Ω_Λ in the flat chart
    lo_c, hi_c = 0.5, 0.95
    for _ in range(80):                                                   # bisection: t H₀ = 1.016 at Ω_Λ ≈ 0.752
        mid = (lo_c + hi_c) / 2
        if t_h0(mid) < 1.016: lo_c = mid
        else: hi_c = mid
    om_c = (lo_c + hi_c) / 2
    t_star_h0 = 73.0 / float(CH.MPC_KM) * 13.61e9 * float(CH.JULIAN_YEAR)      # H₀ in s⁻¹ is 73 km s⁻¹ per Mpc in km
    sep = 1 / (CH.lcdm_age(float(planck[0])) * inv_h_lambda)              # the ΛCDM age grows one Gyr per Gyr: the bound falls behind by 1/13.8 ≈ 7 % per Gyr
    R.check("C5", "the chart's own product t H₀ at the Planck-only Ω_Λ is 0.951; (13.61 Gyr, 73 km/s/Mpc) gives t★H₀ = 1.016, accommodated at Ω_Λ ≈ 0.75; the bound and the ΛCDM age separate at ≈ 7 % per Gyr",
            0.9505 < t_h0(float(planck[0])) < 0.9510 and 1.0155 < t_star_h0 < 1.0165 and 0.748 < om_c < 0.756 and 0.070 < sep < 0.075,
            f"t H₀(0.6847) = {t_h0(float(planck[0])):.4f}; t★H₀ = {t_star_h0:.4f}; Ω_Λ = {om_c:.4f}; {100 * sep:.2f} % per Gyr", kind="CHART")
    # 16:P3 (p14039): the continuity law with ρ̇_Λ = 0 gives w = −1 exactly, for any H ≠ 0, ρ ≠ 0
    ok = all(Q(-3 * H * rho, 3 * H * rho) == -1 for H in (Q(1), Q(7, 3)) for rho in (Q(2), Q(5, 11)))
    R.check("C4", "the effective fluid: ρ̇_Λ + 3H(ρ_Λ + p_Λ) = 0 with ρ̇_Λ = 0 forces p_Λ = −ρ_Λ, w = −1 exactly",
            ok, "p = −ρ on every sampled (H, ρ)", kind="CHART")


# ---- D. the confrontation ------------------------------------------------------------------------------------------------
def _age_ratio_radiation(omega_l, n=4000):
    """t H_Λ with radiation: √Ω_Λ · ∫₀¹ a da / √(Ω_m a + Ω_r + Ω_Λ a⁴), Ω_m = 1 − Ω_Λ − Ω_r (flat), by Simpson's rule after the
    substitution a = u², which removes the √a behaviour of the integrand near a = 0: ∫₀¹ 2u³ du / √(Ω_m u² + Ω_r + Ω_Λ u⁸),
    smooth on [0, 1]; the rule's error at n = 4000 is below 1e-13."""
    om_r = float(OMEGA_R); om_m = 1 - omega_l - om_r
    f = lambda u: 2 * u ** 3 / math.sqrt(om_m * u ** 2 + om_r + omega_l * u ** 8)
    h = 1 / n
    total = f(0) + f(1) + sum((4 if k % 2 else 2) * f(k * h) for k in range(1, n))
    return math.sqrt(omega_l) * total * h / 3


def _age_ratio_curved(omega_l, omega_k, n=4000):
    """t H_Λ with curvature and no radiation: √Ω_Λ · ∫₀¹ da / √(Ω_m/a + Ω_k + Ω_Λ a²), Ω_m = 1 − Ω_Λ − Ω_k, after a = u²:
    ∫₀¹ 2u² du / √(Ω_m + Ω_k u² + Ω_Λ u⁶), smooth on [0, 1], by Simpson's rule."""
    om_m = 1 - omega_l - omega_k
    f = lambda u: 2 * u ** 2 / math.sqrt(om_m + omega_k * u ** 2 + omega_l * u ** 6)
    h = 1 / n
    total = f(0) + f(1) + sum((4 if k % 2 else 2) * f(k * h) for k in range(1, n))
    return math.sqrt(omega_l) * total * h / 3


def _curved_root(omega_k):
    lo, hi = 0.67, 0.70
    for _ in range(60):
        mid = (lo + hi) / 2
        if _age_ratio_curved(mid, omega_k) < math.pi / 4: lo = mid
        else: hi = mid
    return (lo + hi) / 2


def _radiation_root():
    lo, hi = 0.68, 0.69
    for _ in range(60):
        mid = (lo + hi) / 2
        if _age_ratio_radiation(mid) < math.pi / 4: lo = mid
        else: hi = mid
    return (lo + hi) / 2


@R.block("D", BLOCK["D"])
def block_D():
    om = CH.omega_lambda_bracket()
    targets = {"Planck 2018 alone": ("0.13", "0.15"), "Planck 2018 + BAO": ("0.92", "0.94"),
               "DESI DR2 BAO alone": ("2.1", "2.3"), "DESI DR2 BAO + CMB": ("3.7", "3.9")}
    pulls = {n: _landing(om, DETERMINATIONS[n][:2]) for n in targets}
    # 16:C5 (p16003)
    R.check("D1", "the four landings of 0.6837: Planck alone 0.14σ, Planck + BAO 0.93σ, DESI DR2 BAO alone 2.2σ, DESI DR2 BAO + CMB 3.8σ (each bracketed)",
            all(_between(p[0], *targets[n]) and _between(p[1], *targets[n]) for n, p in pulls.items()),
            "; ".join(f"{n} {float(p[0]):.3f}σ" for n, p in pulls.items()), kind="CHART")
    # 16:C5 (p16003), 16:X1 (p14030)
    devs = {n: CH.lcdm_age(float(v[0])) / (math.pi / 4) - 1 for n, v in DETERMINATIONS.items()}
    dev_targets = {"Planck 2018 alone": (0.0015, 0.0018), "Planck 2018 + BAO": (0.008, 0.009),
                   "DESI DR2 BAO alone": (0.030, 0.032), "DESI DR2 BAO + CMB": (0.022, 0.023)}
    R.check("D2", "the age–de Sitter ratio exceeds π/4 at every determination: by 0.17 %, 0.85 %, 3.1 % and 2.2 %",
            all(dev_targets[n][0] < d < dev_targets[n][1] for n, d in devs.items()),
            "; ".join(f"{n} {100 * d:+.2f} %" for n, d in devs.items()), kind="CHART")
    # 16:C5 (p16003)
    root = _radiation_root()
    om_m_rad = 1 - root - float(OMEGA_R)
    pull_rad = (float(DETERMINATIONS["DESI DR2 BAO + CMB"][0]) - root) / float(DETERMINATIONS["DESI DR2 BAO + CMB"][1])
    R.check("D3", "with radiation Ω_r = 9.2 × 10⁻⁵ the root of t H_Λ = π/4 is 0.68388, a shift of +0.0002 above tanh²(3π/8); the flat matter fraction there is 0.3160 and the DESI-with-CMB landing 3.7σ",
            0.68387 < root < 0.68389 and 0.00015 < root - CH.omega_lambda() < 0.00025 and 0.31595 < om_m_rad < 0.31605 and 3.70 < pull_rad < 3.76,
            f"root = {root:.6f}, shift = {root - CH.omega_lambda():+.6f}; Ω_m = {om_m_rad:.5f}; landing {pull_rad:.3f}σ", kind="CHART")
    # 16:C5 (p16003): the flat identity used as a measured bound on curvature, not a postulate
    k0, dk = float(OMEGA_K[0]), float(OMEGA_K[1])
    r_flat, r_k, r_up, r_dn = _curved_root(0.0), _curved_root(k0), _curved_root(k0 + dk), _curved_root(k0 - dk)
    R.check("D4", "at the measured curvature Ω_K = 0.0007 ± 0.0019 the root of t H_Λ = π/4 moves by −0.0003 ± 0.0007 from the flat value, below every quoted error (the curved integrand at Ω_K = 0 returns the flat root)",
            abs(r_flat - CH.omega_lambda()) < 2e-6 and -0.0003 < r_k - r_flat < -0.0002
            and 0.0006 < r_k - r_up < 0.0008 and 0.0006 < r_dn - r_k < 0.0008,
            f"flat root {r_flat:.6f}; at Ω_K = {k0}: {r_k:.6f} ({r_k - r_flat:+.6f}); at ±{dk}: {r_up - r_flat:+.6f}, {r_dn - r_flat:+.6f}", kind="CHART")


# ---- P. the prediction and the ages ---------------------------------------------------------------------------------------
@R.block("P", BLOCK["P"])
def block_P():
    om_lo, om_hi = CH.omega_lambda_bracket()
    om_m = (1 - om_hi, 1 - om_lo)
    desi = DETERMINATIONS["DESI DR2 BAO + CMB"]
    pull = ((om_m[0] - (1 - desi[0])) / desi[1], (om_m[1] - (1 - desi[0])) / desi[1])
    # 16:P4 (p16004)
    R.check("P1", "the matter fraction Ω_m = 1 − tanh²(3π/8) between 0.31631 and 0.31632; the DESI DR2 BAO + CMB value 0.3027 ± 0.0036 lies between 3.7σ and 3.9σ from it",
            _between(om_m[0], "0.31631", "0.31632") and _between(om_m[1], "0.31631", "0.31632")
            and _between(pull[0], "3.7", "3.9") and _between(pull[1], "3.7", "3.9"),
            f"Ω_m = {1 - CH.omega_lambda():.6f}, pull {float(pull[0]):.3f}σ", kind="CHART")
    (p_lo, p_hi) = CH.pi_bracket()
    s_lo, s_hi = CH.sqrt_bracket(desi[0])
    h_lambda = (desi[2] * s_lo, desi[2] * s_hi)                              # H_Λ = H₀ √Ω_Λ, km s⁻¹ Mpc⁻¹
    bound = (p_lo / 4 * _inv_h_gyr(h_lambda[1]), p_hi / 4 * _inv_h_gyr(h_lambda[0]))
    t_pull = ((STELLAR[0] - bound[1]) / STELLAR[1], (STELLAR[0] - bound[0]) / STELLAR[1])
    # 16:P4 (p16004)
    inv_h_lambda_desi = float(_inv_h_gyr(Q(float(desi[2]) * math.sqrt(float(desi[0])))))
    age_desi = CH.lcdm_age(float(desi[0])) * inv_h_lambda_desi
    R.check("P2", "the octant bound at the DESI DR2 BAO + CMB pair between 13.48 and 13.50 Gyr (1/H_Λ = 17.18 Gyr); the oldest cluster population 13.61 ± 0.34 Gyr between 0.3σ and 0.4σ above it; the chart's own age there 13.79 Gyr, 2.2 % above the bound",
            _between(bound[0], "13.48", "13.50") and _between(bound[1], "13.48", "13.50")
            and _between(t_pull[0], "0.3", "0.4") and _between(t_pull[1], "0.3", "0.4")
            and 17.17 < inv_h_lambda_desi < 17.19 and 13.785 < age_desi < 13.80 and 0.0220 < age_desi / float(bound[0]) - 1 < 0.0230,
            f"bound {float(bound[0]):.3f}–{float(bound[1]):.3f} Gyr; 1/H_Λ = {inv_h_lambda_desi:.3f} Gyr; t★ pull {float(t_pull[0]):.2f}σ; chart age {age_desi:.3f} Gyr, {100 * (age_desi / float(bound[0]) - 1):.2f} % above", kind="CHART")
    planck = DETERMINATIONS["Planck 2018 alone"]
    bound_p = (math.pi / 4) * float(_inv_h_gyr(Q(float(planck[2]) * math.sqrt(float(planck[0])))))   # the Planck pair, H_Λ = H₀√Ω_Λ, the Julian year
    pull_s = (float(STELLAR[0]) - bound_p) / float(STELLAR[1]); pull_i = (float(INFERRED[0]) - bound_p) / float(INFERRED[1])
    # 16:P1 (p14037)
    R.check("P3", "the bound at the Planck-only pair, 13.78 Gyr: the oldest cluster population 0.5σ below it, the inferred cosmic age 0.03 Gyr above it, within 0.1σ",
            abs(bound_p - 13.78) < 0.005 and -0.55 < pull_s < -0.45 and abs(pull_i) < 0.1 and 0.025 < float(INFERRED[0]) - bound_p < 0.035,
            f"bound {bound_p:.3f} Gyr; pulls {pull_s:+.2f}σ, {pull_i:+.2f}σ; inferred age above by {float(INFERRED[0]) - bound_p:.3f} Gyr", kind="CHART")


if __name__ == "__main__":
    import sys as _sys
    _sys.set_int_max_str_digits(0)
    if len(sys.argv) > 1:
        R.run_block(sys.argv[1].upper()); ok = R.summary(write=False)
    else:
        ok = R.verify_all(); R.summary(write=True, expect=list(LEDGER))
    raise SystemExit(0 if ok else 1)
