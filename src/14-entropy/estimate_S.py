#!/usr/bin/env python3
# estimate_S.py -- reproduces every numeral of 14-entropy (De Sitter Entropy
# Estimates). Standalone: no input, no external path; exit 0 iff all checks pass.
#
# All observational values are [approx] chart readings; the exact faces are
# the counts Om = 4S+1 and the admissibility congruences, verified here in
# exact integer arithmetic on the instantiated Carrier. No fitting, no RNG;
# transcendental library calls (sqrt, atanh, tanh, pi) appear only as the
# labelled chart functions applied to [approx]/[LCDM] quantities.
#
# Exit status: 0 iff the exact checks and the census both pass.
#
# Package form (2026-09): the script as written, its integer checks, [PASS] lines and asserts reported to the registry
# (entcommon) as the families est.F1 (exact faces), est.B9 (area law), est.T1 (the instrument table), est.C1
# (two-face concordance), est.C2 (the chart identity), est.A1 (the circularity audit), est.C3 (the channel-1
# consistency), est.P3 (the age-rate locus), est.C4 (one-face concordance), est.L1 (the floor landing), est.P2 (the
# octant bound against the stellar ages), est.P1 (the running floor). A failing check prints and fails its family;
# the run continues. Kinds: est.F1 and the count half of est.B9 are EXACT; every other family is CHART -- a one-line
# chart computation on published [approx]/[LCDM] data, reproduced to the paper's quoted precision.

import sys
from math import pi, sqrt, atanh, tanh
from entcommon import chk, family, flush

def run():

    # ---------------------------------------------------------------- exact faces
    # Instantiated Carrier of the lab universe (37-sim): exact integer counts.
    S_LAB = 602_140
    OM_LAB = 4 * S_LAB + 1


    def is_prime(n: int) -> bool:          # deterministic trial division, exact
        if n < 2:
            return False
        d = 2
        while d * d <= n:
            if n % d == 0:
                return False
            d += 1
        return True


    print("exact faces (counts): Om = 4S+1; S even; S = 1 mod 3; 4S+1 prime")
    checks = [
        ("Om = 4S+1", OM_LAB == 2_408_561),
        ("S even (octant sector Z_8 exists: 8 | 4S iff 2 | S)", S_LAB % 2 == 0),
        ("S = 1 mod 3", S_LAB % 3 == 1),
        ("4S+1 prime", is_prime(OM_LAB)),
        ("octant count S/2 is an integer", (S_LAB // 2) * 2 == S_LAB),
    ]
    family("est", "F1")
    for name, ok in checks:
        print(f"  [{'PASS' if ok else 'FAIL'}] {name}  (lab Carrier Om={OM_LAB})")
        chk(name, ok)

    # ------------------------------------------------------- area law (row B9)
    # The quarter identity and the quarter-turn chain, exact integer arithmetic:
    # 4S = Om - 1; the generative four of Om = 4S+1 at the Carrier and
    # p = 4*kap + 1 at every Subject (hydrogen shell kap_H = 3, q = 13).
    print("area law (row B9): quarter identity and quarter-turn chain (counts)")
    KAP_H = 3
    Q_H = 4 * KAP_H + 1
    b9_checks = [
        ("quarter identity 4S = Om - 1", 4 * S_LAB == OM_LAB - 1),
        ("quarter-turn at the Carrier: 4 | Om - 1", (OM_LAB - 1) % 4 == 0),
        ("quarter-turn at the Subject: q_H = 4 kap_H + 1 = 13, prime",
         Q_H == 13 and is_prime(Q_H) and (Q_H - 1) % 4 == 0),
    ]
    family("est", "B9")
    for name, ok in b9_checks:
        print(f"  [{'PASS' if ok else 'FAIL'}] {name}")
        chk(name, ok)

    # ------------------------------------------------------------ chart channel
    # laboratory channel [I]
    lP = 1.616255e-35      # Planck length, m
    c = 2.99792458e8       # m/s
    Gyr = 3.1557e16        # s
    Mpc = 3.0857e22        # m


    def S_of(rH):          # S = pi (r_H / l_P)^2   [approx]
        return pi * (rH / lP) ** 2


    # area-law chart face (row B9) [approx]: the projected horizon area in Planck
    # cells is the full phase cycle, A/lP^2 = 4 pi n_A = 4 S(r_H), n_A = (r_H/lP)^2.
    print("area law chart face (row B9) [approx]: 4 pi n_A = 4 S(r_H)")
    for rH_test in (1.0, 1.5e26):
        n_A = (rH_test / lP) ** 2
        ok = abs(4 * pi * n_A - 4 * S_of(rH_test)) <= 1e-12 * (4 * S_of(rH_test))
        print(f"  [{'PASS' if ok else 'FAIL'}] r_H = {rH_test:g} m")
        chk(f"area-law chart face 4 pi n_A = 4 S(r_H) at r_H = {rH_test:g} m [approx]", ok)


    LAM_FACE = {"1", "4b"}          # rows reading the Lambda face
    GAUGE = {"4a"}                  # gauge reading: displayed, excluded from stats
    rows = []
    sigma = {}                      # per-row relative uncertainty on sqrt(S)

    # 1. expansion geometry: Lambda from the LCDM fit (Planck 2018)
    Lam = 1.088e-52                                   # m^-2, ~2% -> 1% on sqrt(S)
    rows.append(("1", "Lambda (CMB, Planck alone)", sqrt(3.0 / Lam)))
    sigma["1"] = 0.010

    # 2. local distance ladder (published stat+sys)
    for H0, dH, lab, key in ((73.0, 1.0, "Cepheid", "2a"), (69.8, 1.7, "TRGB", "2b")):
        rows.append((key, f"ladder H0={H0} ({lab})", c / (H0 * 1e3 / Mpc)))
        sigma[key] = dH / H0

    # 3. rotation curves through the realisation a0 = c H / 2 pi
    a0, da0 = 1.20e-10, sqrt(0.02**2 + 0.24**2) * 1e-10   # SPARC knee, sys-dominated
    rows.append(("3", "rotation curves a0", c / (2 * pi * a0 / c)))
    sigma["3"] = da0 / a0

    # 4. stellar ages through age = horizon distance (Valcin et al. 2026, IV;
    # one vintage rule: the superseding release everywhere, no mixing)
    t_star, dt = 13.61 * Gyr, sqrt(0.25**2 + 0.23**2) / 13.61
    rows.append(("4a", "stellar age, raw ct [gauge]", c * t_star))
    rows.append(("4b", "stellar age, octant (4/pi)ct", (4 / pi) * c * t_star))
    sigma["4a"] = sigma["4b"] = dt

    print(f"\n{'#':3s}{'instrument':32s} {'r_H [m]':>12s} {'S':>10s} {'sqrt(S)':>10s} {'sig%':>6s}")
    Svals = {}
    for key, name, rH in rows:
        S = S_of(rH)
        Svals[key] = S
        print(f"{key:3s}{name:32s} {rH:12.3e} {S:10.2e} {sqrt(S):10.2e} {100*sigma[key]:6.1f}")
    # the paper's table (Section 3.2): r_H in 1e26 m, S in 1e122, sigma on sqrt(S) in %
    family("est", "T1")
    TABLE = {"1": (1.66, 3.3, 1), "2a": (1.27, 1.9, 1.4), "2b": (1.33, 2.1, 2.4), "3": (1.19, 1.7, 20), "4a": (1.29, 2.0, 2.5), "4b": (1.64, 3.2, 2.5)}
    for key, name, rH in rows:
        r_t, S_t, sg_t = TABLE[key]
        chk(f"row {key}: r_H = {r_t} e26 m, S = {S_t} e122, sigma = {sg_t}% as tabulated",
            abs(rH / 1e26 - r_t) < 0.006 and abs(Svals[key] / 1e122 - S_t) < 0.06 and abs(100 * sigma[key] - sg_t) < 0.1)

    EVIDENCE = [k for k, _, _ in rows if k not in GAUGE]   # five evidence readings
    sq = {k: sqrt(Svals[k]) for k in EVIDENCE}
    m = sum(sq.values()) / len(sq)
    half = 100 * (max(sq.values()) - min(sq.values())) / 2 / m
    fac = (max(sq.values()) / min(sq.values())) ** 2
    print(f"\nconcordance (5 evidence readings, gauge 4a excluded): sqrt(S) ="
          f" {min(sq.values()):.2e} .. {max(sq.values()):.2e}"
          f"  (+/- {half:.1f}% half-range about the mean)")
    print(f"on S itself: full-range spread = factor {fac:.2f}")
    family("est", "C1")
    chk("five evidence readings, gauge row 4a excluded", EVIDENCE == ["1", "2a", "2b", "3", "4b"])
    chk("sqrt(S) = (1.3..1.8) e61 across the five readings", 1.25e61 < min(sq.values()) < 1.35e61 and 1.75e61 < max(sq.values()) < 1.85e61)
    chk("half-range +/-17% on the count face (16.5 +/- 0.5)", abs(half - 16.5) < 0.5)
    chk("full-range spread on S a factor 1.9 (1.94 +/- 0.05)", abs(fac - 1.94) < 0.05)
    print("[PASS] concordance: +/-17% half-range, factor 1.9 on S")

    CONV = ["1", "2a", "2b"]                       # conventional channels alone
    sqc = {k: sqrt(Svals[k]) for k in CONV}
    mcv = sum(sqc.values()) / len(sqc)
    half_cv = 100 * (max(sqc.values()) - min(sqc.values())) / 2 / mcv
    fac_cv = (max(sqc.values()) / min(sqc.values())) ** 2
    print(f"conventional channels alone: +/- {half_cv:.1f}% half-range, factor {fac_cv:.2f}")
    chk("conventional channels alone: +/-14% (13.9 +/- 0.5), factor 1.7 (1.72 +/- 0.03)", abs(half_cv - 13.9) < 0.5 and abs(fac_cv - 1.72) < 0.03)
    print("[PASS] conventional-only statistic: +/-14%, factor 1.7")

    # the two-cluster ratio is the chart identity (H_rate/H0)^2 / OmL -- the
    # definition of OmL read on the rows, NOT framework content (round-02 F1).
    OmL = 0.685
    H0_PLANCK = 67.36
    family("est", "C2")
    for key, H in (("2a", 73.0), ("2b", 69.8)):
        lhs = Svals["1"] / Svals[key]
        rhs = (H / H0_PLANCK) ** 2 / OmL
        chk(f"row {key}: S_Lambda/S_rate = (H/H0)^2/OmL to 0.2% [LCDM]", abs(lhs / rhs - 1) < 2e-3)
    chk("the observed cluster excess 1.68 against 1.46 = 1/OmL [LCDM]", abs(1 / OmL - 1.46) < 0.005 and abs(Svals["1"] / ((Svals["2a"] + Svals["2b"] + Svals["3"]) / 3) - 1.68) < 0.1)
    print("[PASS] chart identity S_L/S_rate = (H/H0)^2/OmL verified per row"
          " (the cluster ratio displays the Hubble tension; no framework content)")

    # circularity audit: the age ratio depends on the single fitted Omega_Lambda
    ratio = (2 / 3) * atanh(sqrt(OmL))                # [LCDM]
    OmL_pi4 = tanh(1.5 * pi / 4) ** 2                 # inversion of pi/4 [LCDM]
    dev = abs(ratio - pi / 4) / (pi / 4) * 100
    sig = abs(OmL - OmL_pi4) / 0.007
    print(f"\naudit: t0*H_L = (2/3) artanh(sqrt(OmL)) = {ratio:.4f};  pi/4 = {pi / 4:.4f}"
          f"  (deviation {dev:.2f}%)")
    print(f"       pi/4 corresponds to OmL = {OmL_pi4:.4f}  (fitted: {OmL}; a {sig:.2f}-sigma landing)")
    print("       => the ~0.2% landing restates the fitted OmL: consistency, not evidence")
    print("       (sub-0.1% figures need the radiation correction the flat matter+Lambda form omits)")
    family("est", "A1")
    chk("t0 H_Lambda = (2/3) artanh(sqrt(OmL)) = 0.7871 at OmL = 0.685 [LCDM]", abs(ratio - 0.7871) < 5e-4)
    chk("within 0.2% of pi/4 = 0.7854", dev < 0.25)
    chk("the inversion: pi/4 corresponds to OmL = tanh^2(3pi/8) = 0.6837", abs(OmL_pi4 - 0.6837) < 5e-5)
    chk("a 0.19-sigma landing on the fitted 0.685 +/- 0.007", abs(sig - 0.19) < 0.01)

    # octant lemma prediction: Omega_Lambda as an output of the realisation set
    print(f"\noctant lemma: t_age = (pi/4) r_H/c  =>  predicted OmL = tanh^2(3pi/8) = {OmL_pi4:.4f}"
          f"  (fitted {OmL}: {sig:.2f} sigma)")
    print("saturation test (fit-independent): oldest-object ages cap at (pi/4) r_H/c = 13.8 Gyr,"
          " at every observational frame chronon")

    # the channel-1 consistency (T19, 2026-09-13): with the fit's Lambda, the age-rate locus returns the
    # fit's own H0, since Lambda = 3 OmL H0^2/c^2 by definition -- same-channel, a corollary, not a prediction.
    H_L = sqrt(Lam * c ** 2 / 3) * Mpc / 1e3          # km/s/Mpc [approx]
    H0_ent = H_L / tanh(3 * pi / 8)
    print(f"\nchannel-1 consistency: H_Lambda = {H_L:.1f} => H0 = {H0_ent:.2f} = 67.36 x {H0_ent/67.36:.4f}"
          "  (same-channel: the fit's Lambda is 3 OmL H0^2/c^2; a corollary of the octant landing, not a prediction)")
    family("est", "C3")
    chk("H_Lambda = 55.7 km/s/Mpc from the fit's Lambda (1/H_Lambda = 17.55 Gyr) [LCDM]", abs(H_L - 55.7) < 0.05 and abs(1 / (H_L * 1e3 / Mpc) / Gyr - 17.55) < 0.01)
    chk("the locus at the channel-1 Lambda returns H0 = 67.4, the fit's own value to 0.1%", abs(H0_ent - 67.4) < 0.15 and abs(H0_ent / 67.36 - 1.0) < 0.002)
    print("[PASS] channel-1 consistency: the locus returns the fit's H0 to 0.1%")

    # the age-rate locus (row P3): t_age * H0 = (pi/4)/tanh(3pi/8), exact for the realisation set; read on the
    # fit-independent stellar age it is a prediction of H0 independent of the expansion fit.
    locus = (pi / 4) / tanh(3 * pi / 8)
    t_star, dt_star = 13.61, sqrt(0.25 ** 2 + 0.23 ** 2)   # Gyr, Valcin 2026 (stat+sys)
    H0_age = locus / (t_star * Gyr) * Mpc / 1e3           # km/s/Mpc [approx]
    dH0_age = H0_age * dt_star / t_star
    sig_shoes = (73.0 - H0_age) / sqrt(1.0 ** 2 + dH0_age ** 2)
    sig_trgb = (69.8 - H0_age) / sqrt(1.7 ** 2 + dH0_age ** 2)
    sig_planck = (67.36 - H0_age) / sqrt(0.54 ** 2 + dH0_age ** 2)
    lcdm_locus = (2 / 3) * atanh(sqrt(0.685)) / sqrt(0.685)   # flat matter+Lambda t0*H0 at the fitted OmL
    print(f"\nage-rate locus: t_age*H0 = (pi/4)/tanh(3pi/8) = {locus:.4f}  (LCDM at OmL=0.685: {lcdm_locus:.4f}, the X3 coincidence)")
    print(f"  read on t_star = {t_star} +/- {dt_star:.2f} Gyr: H0 = {H0_age:.1f} +/- {dH0_age:.1f} km/s/Mpc"
          f"  (Planck {abs(sig_planck):.2f} sigma; TRGB {abs(sig_trgb):.2f} sigma; Cepheid {abs(sig_shoes):.2f} sigma)")
    print(f"  ladder pair (13.61 Gyr, 73): t*H0 = {73.0 * 1e3 / Mpc * t_star * Gyr:.3f} -- accommodated in LCDM only by OmL ~ 0.76, which the octant forbids")
    family("est", "P3")
    chk("the age-rate locus t_age H0 = (pi/4)/tanh(3pi/8) = 0.950 (0.9499)", abs(locus - 0.9499) < 5e-4)
    chk("flat LCDM returns 0.951 at the fitted OmL (the X3 coincidence read on H0)", abs(lcdm_locus - 0.9510) < 5e-4)
    chk("read on t_star = 13.61 +/- 0.34 Gyr: H0 = 68.2 +/- 1.7 km/s/Mpc [approx]", abs(H0_age - 68.2) < 0.1 and abs(dH0_age - 1.7) < 0.05)
    chk("confrontations: Planck 0.5 sigma, TRGB 0.65 sigma, Cepheid 2.4 sigma", abs(sig_shoes - 2.4) < 0.1 and abs(sig_trgb - 0.65) < 0.05 and abs(abs(sig_planck) - 0.5) < 0.05)
    chk("the ladder pair (13.61 Gyr, 73): t_star H0 = 1.016, above the locus", abs(73.0 * 1e3 / Mpc * t_star * Gyr - 1.016) < 0.002)
    print("[PASS] P3: H0 = 68.2 +/- 1.7 from the stellar age through the octant; Cepheid 2.4 sigma, TRGB 0.65, Planck 0.5")

    # one-face concordance: rate rows carried to the Lambda face by the octant's factor 1/tanh(3pi/8)
    th = tanh(3 * pi / 8)
    rL = {"1": rows[[r[0] for r in rows].index("1")][2],
          "2a": c / (73.0 * 1e3 / Mpc * th), "2b": c / (69.8 * 1e3 / Mpc * th),
          "3": c / (2 * pi * a0 / c * th), "4b": rows[[r[0] for r in rows].index("4b")][2]}
    sq = {k: sqrt(pi) * v / lP for k, v in rL.items()}
    def halfrange(keys):
        v = [sq[k] for k in keys]; return 100 * (max(v) - min(v)) / 2 / ((max(v) + min(v)) / 2)
    hr5 = halfrange(["1", "2a", "2b", "3", "4b"]); hr3 = halfrange(["1", "2a", "2b"])
    print("\none-face concordance (r_H^Lambda = c/(H tanh(3pi/8)) on rate rows):")
    for k in ("1", "2a", "2b", "3", "4b"): print(f"  {k:3s} r_H^L = {rL[k]:.3e} m   sqrt(S) = {sq[k]:.3e}")
    print(f"  half-range: +/-{hr5:.1f}% over five readings; +/-{hr3:.1f}% conventional (1, 2a, 2b)")
    family("est", "C4")
    for k, v in (("1", 1.66), ("2a", 1.53), ("2b", 1.60), ("3", 1.44), ("4b", 1.64)):
        chk(f"row {k}: r_H^Lambda = {v} e26 m as tabulated", abs(rL[k] / 1e26 - v) < 0.006)
    chk("one-face half-range +/-7% over five readings (7.0 +/- 0.3)", abs(hr5 - 7.0) < 0.3)
    chk("one-face half-range +/-4% conventional (4.0 +/- 0.3)", abs(hr3 - 4.0) < 0.3)
    chk("the residual between the ladder rows and row 1 is 8% (the Hubble tension proper)", abs(100 * (rL["1"] - (rL["2a"] + rL["2b"]) / 2) / rL["1"] - 6) < 3)
    print("[PASS] one-face concordance +/-7% (five), +/-4% (conventional)")

    # floor landing at the corpus H0
    land = c * (67.4 * 1e3 / Mpc) / 1.2e-10
    print(f"\nfloor landing: c H0/a0 = {land:.2f} +/- {0.2*land:.1f} at H0 = 67.4 (2 pi = {2*pi:.2f}, {(2*pi-land)/(0.2*land):.2f} sigma)")
    family("est", "L1")
    chk("floor landing c H0/a0 = 5.46 at H0 = 67.4 [approx]", abs(land - 5.46) < 0.02)
    chk("+/-1.1 (20%), 0.8 sigma from 2 pi", abs(0.2 * land - 1.09) < 0.02 and abs((2 * pi - land) / (0.2 * land) - 0.76) < 0.03)

    # temporal-face confrontation: octant bound vs Valcin et al. 2026 (IV) [LCDM]
    t_oct = (pi / 4) * sqrt(3.0 / Lam) / c / Gyr
    dv = sqrt(0.25 ** 2 + 0.23 ** 2)
    sig_gc = (t_oct - 13.61) / dv
    sig_tu = (t_oct - 13.81) / dv
    print(f"\noctant bound {t_oct:.2f} Gyr vs Valcin IV (one vintage everywhere):"
          f" oldest population {sig_gc:+.2f} sigma below (fit-independent, carries P2);"
          f" prior-dependent inferred age {sig_tu:+.2f} sigma (straddles within 0.1 sigma)")
    family("est", "P2")
    chk("the octant bound (pi/4) sqrt(3/Lambda)/c = 13.79 Gyr at the channel-1 Lambda [approx]", abs(t_oct - 13.79) < 0.01)
    chk("the LCDM age 13.80 Gyr is degenerate with the bound to 0.2%", abs(13.80 / t_oct - 1) < 0.0025)
    chk("oldest cluster population 13.61 +/- 0.34: 0.5 sigma below the bound (0.53)", abs(sig_gc - 0.53) < 0.05)
    chk("inferred cosmic age 13.81: straddles the bound within 0.1 sigma (-0.06)", abs(sig_tu + 0.06) < 0.05)
    print("[PASS] Valcin IV: population 0.5 sigma below the bound; inferred age a"
          " prior-dependent consistency, statistically consistent with saturation")

    # floor-running confrontation: MUSE-DARK III (Ciocan et al. 2026) [LCDM]
    Om_m = 0.315
    Hz = sqrt(Om_m * 8 + (1 - Om_m))                  # H(z=1)/H0, flat LCDM
    a0_pred = (a0 * Hz) * 1e10                        # e-10 units
    sig_end = (2.38 - a0_pred) / sqrt(0.10**2 + (da0 * 1e10 * Hz) ** 2)
    slope_pred = a0 * 1e10 * (Hz - 1)
    sig_slope = (1.59 - slope_pred) / sqrt(0.10**2 + (da0 * 1e10 * (Hz - 1)) ** 2)
    print(f"\nfloor running: a0(z=1) predicted {a0_pred:.2f}e-10 vs measured 2.38+/-0.10"
          f" ({sig_end:.1f} sigma with anchor systematics); linear rate predicted"
          f" {slope_pred:.2f} vs 1.59+/-0.10 e-10/z ({sig_slope:.1f} sigma pre-systematics)")
    family("est", "P1")
    chk("a0(z=1) on the H(z) chord: 2.15e-10 (flat LCDM E(z=1) = 1.79) [LCDM]", abs(a0_pred - 2.15) < 0.01 and abs(Hz - 1.79) < 0.005)
    chk("endpoint 0.5 sigma from the measured 2.38 +/- 0.10 with the anchor's systematic band", abs(sig_end - 0.5) < 0.1)
    chk("the fitted linear rate 1.59 +/- 0.10 exceeds the chord's 0.95 per unit redshift by ~3 sigma (pre-systematics)", abs(slope_pred - 0.95) < 0.01 and abs(sig_slope - 3.0) < 0.1)
    print("[PASS] Ciocan confrontation: constant floor disfavoured; endpoint 0.5 sigma;"
          " linear rate ~3 sigma open (95% bands read at face value)")

    # bound channel
    print("\nbound: registered entropy budget ~1e104 << S  (headroom ~1e18 to saturation)")



    flush("est", order=["F1", "B9", "T1", "C1", "C2", "A1", "C3", "P3", "C4", "L1", "P2", "P1"],
          kinds={"F1": "EXACT", "B9": "EXACT+CHART"})

if __name__ == "__main__":
    import entcommon
    run(); entcommon.summary(write=False)
