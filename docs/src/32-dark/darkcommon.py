"""
darkcommon.py — shared registry for the 32-dark validation package
===================================================================
"The Dark Sector over Finite Relational Substrate" (Akhtman, Geifman & Voether, 2026), validation package of the FRC
corpus (finite-ring-space/src/32-dark). The paper's twelve validation scripts and the figure script are kept as
written — four print a verdict (flux_exact, born_exact, deep_regime_fp, rar_scatter), the rest print their values —
and run here through one registry: a *family* is one script (identified as dark.<stem>, e.g. dark.interpolation), run
in its own namespace inside out/ (its figures and deep.json land there, the paper's two figures in figures/; every saved figure gets a PNG sibling, shown inline in the notebook), its
printed verdict lines captured; its micro-checks are those lines together with the registry's predicates (PRED
below), which read the script's namespace and output and decide the manuscript's stated values explicitly — the
exact Gauss law and the amplitude identity recomputed, the slopes 1.03/1.11 and the exact slope 1, the discriminant
0.051 at x = 5.2 and the two pinning checks, the first-passage reduction with rel.err/s → 1/6, the SPARC scatter
0.038 dex and the bound δα ≲ 3.5°, the prediction numerals. An exception, a nonzero exit or a failed predicate
fails the family. Each family names the row(s) of the paper's predicate ledger it witnesses (LEDGER; rows cited as
32:XN), and the ledger's source column cites the family ids in return. rar_shape.py, the named test of row B8 owed
by the paper's Appendix A, is added here (the binned relation from data/RAR.mrt).

Kinds, recorded per family: EXACT — exact rationals, Z[i], or 60-digit identities, no tolerance in the verdict;
SIM — a seeded stochastic simulation (the noisy link, the killed walk), verdict by stated tolerance; CHART — a
continuum reading or a comparison with data (the interpolation, the RAR/BTFR, the SPARC scatter, the predictions,
the cluster law's illustration), tagged [approx] in the paper, verdict by stated tolerance.

Master-ledger rows of the corpus sourced from this paper: 00:L1 (the floor a0 = cH0/2pi and the RAR's barrier identification,
32:B8, C2, C4-C6), 00:L7 (the running floor a0(z), 32:P1), 00:Z7 (the running's normalisation, 32:Y2 and the predictions),
00:D3 (distance is decoherence, 32:B1), 00:N1 (the exclusion predictions, 32:P6), 00:N2 (parameter-freeness, 32:C2).
"""
import io, json, os, re, sys, time, traceback, math
from fractions import Fraction as Fr

RESULTS = []
MICRO = []                    # (family, label, ok)
HERE = os.path.dirname(os.path.abspath(__file__))

# family -> paper rows witnessed
LEDGER = {
    "dark.flux_exact":          "32:C1, 32:X1",
    "dark.born_exact":          "32:C3, 32:C7",
    "dark.firstpassage_finite": "32:B8, 32:C7",
    "dark.meridian_walk":       "32:B8, 32:C6, 32:C7",
    "dark.deep_regime":         "32:C4",
    "dark.deep_regime_fp":      "32:C4",
    "dark.interpolation":       "32:B8, 32:C6, 32:X4",
    "dark.rar_shape":           "32:B8, 32:C2, 32:C6",
    "dark.deep_mond":           "32:C2, 32:C4, 32:C5, 32:X2, 32:X3",
    "dark.rar_scatter":         "32:C8, 32:P2, 32:X5, 32:Y1, 32:Y2",
    "dark.cluster_coherent":    "32:C10, 32:X7, 32:X8, 32:Y1",
    "dark.predictions":         "32:P1, 32:P2, 32:P3, 32:P4",
    "dark.make_figures":        "32:V2",
}

KIND = {f: "CHART" for f in LEDGER}
for f in ("dark.flux_exact", "dark.born_exact", "dark.firstpassage_finite"):
    KIND[f] = "EXACT"
for f in ("dark.deep_regime", "dark.meridian_walk"):
    KIND[f] = "SIM"

LABELS = {
    "dark.flux_exact": "the discrete Gauss law of the synchronisation flux in exact rationals on the 5³ box: a unit point source gives unit flux through both enclosing surfaces, a source-free noise field gives zero, their superposition gives one — Newton's law as the high-acceleration reading",
    "dark.born_exact": "amplitude = √count, exact in Z[i]: n aligned unit phasors have |Σ|² = n² (coherent, amplitude n) and the mean of |Σ|² over all sign patterns is n (incoherent, amplitude √n) for n up to 10 — the cross-term cancellation that forces the deep-regime square root",
    "dark.firstpassage_finite": "the finite-cycle first-passage law at 60 digits: the single-step identity f(e^(−s)) = e^(−arccosh e^s); the reduction arccosh(e^s) = √(2s)(1 + s/6 + …) with rel.err/s → 1/6, carrier-exact to ~10⁻⁶¹ at s ~ Ω^(−1/2); the wrap correction of the killed walk on Z_N against the infinite line, O(e^(−(N−a) arccosh e^s))",
    "dark.meridian_walk": "the meridian killed walk: the exact rational discriminant 1 − z² of the first-passage quadratic; the simulated escape probability against e^(−a√(2s)) (seeded); the assembled resolved fraction 1 − e^(−√x) with deep slope 1/2 (the RAR fit form); the mechanism figure",
    "dark.deep_regime": "the noisy Kuramoto (Adler) link dφ = (T − sin φ)dt + √(2D) dW, seeded: the mean response is Newtonian at every noise level (deep slopes 1.03 at D = 0.3 and 1.11 at D = 0.6, the boost constant to rising) — the √ law is registration, not force modification; deep.json and the figure",
    "dark.deep_regime_fp": "the stationary Fokker–Planck solution of the same link: the small-tilt log-slope exactly 1 at D = 0.3 and 0.6 (within 2 × 10⁻³), the boost constant to rising; no √ regime in the mean force",
    "dark.interpolation": "the interpolation from the rotation angle: deep slope 1/2 and Newtonian slope 1; the discriminant against the simple rational form, maximum 0.051 in g_obs/g_b at x = 5.2; the two pinning checks of B8 (a barrier κx^β gives deep slope 1 − β; the knee at 1/κ²); the chart angle sin²α = e^(−√x); the figure",
    "dark.rar_shape": "the named test of B8 against the binned radial acceleration relation (data/RAR.mrt, 0.2-dex bins, the bin scatter as uncertainty): the exponential form's free a₀ within 10 % of the RAR fit 1.20 × 10⁻¹⁰ and below the simple form in χ²; in the band 2 < x < 10 the departure from the exponential form is within the bin scatter in every bin and the rational form has the larger χ²; the floor cH₀/2π 5–25 % below the free fit (the paper's 13 %) [approx]",
    "dark.deep_mond": "the two-chart Gauss law: a₀ = cH₀/2π = 1.042 × 10⁻¹⁰ at H₀ = 67.4; the RAR deep-regime slope 1/2 and the BTFR slope 1/4 (v⁴ = GMa₀, 5 × 10¹⁰ M⊙ → 162 km/s); the exponential-disk rotation curve flattening at the registered speed; the figure [approx]",
    "dark.rar_scatter": "the SPARC residual test at fixed a₀ = cH₀/2π: intrinsic scatter 0.038 dex overall, 0.04 at the knee, rising to ≈ 0.13 at x ≈ 0.02; the two-variable law bounding δα ≲ 3.5° (σ_v/v = 0.1–0.2 excluded, Y2); no correlation of the within-galaxy scatter with 1/V_flat over 116 disks (ρ = −0.02); a gas–disk–bulge amplitude sum would boost the RAR by 0.14 dex (Y1's within-galaxy constraint); ν(0.1) = 3.69 [approx, data]",
    "dark.cluster_coherent": "the coherence-matrix amplitude law: N_eff = (Σ√g)²/Σg equals N for equal components and is suppressed by a dominant BCG (4:1:1 → 2.67); the core boost √N_eff with N_core = 6 (2.45) decaying to 1 by ~Mpc in the illustrative radial profile — the Bullet selection (C → 0) and the core addition (C → 1) in one law, the factor-two closure a conjecture (Y1) [illustrative]",
    "dark.predictions": "the falsifiable predictions computed: a₀(z) = cH(z)/2π with v_flat ∝ E(z)^(1/4) (+7 %, +15 %, +31 % at z = 0.5, 1, 2); the two-variable scatter law σ(x, σ_v/v) (0.27 dex at x = 0.01, σ_v/v = 0.1); the wide-binary velocity enhancement with the Galactic external field 1.8a₀ (√ν − 1 = 12–16 % at 10–40 kAU, the paper's 10–30 %); the pressure-supported coherence offset √w (−0.05 to −0.15 dex for σ_v/v = 0.5–1) [approx]",
    "dark.make_figures": "the paper's two figures regenerated (fig_rar.pdf: the RAR with the rational alternative and the exponential-disk rotation curve; fig_mechanism.pdf: the first-passage collapse and the chart angle), written to figures/",
}

def script_of(fam):
    return fam.split(".")[1]            # dark.<stem> runs <stem>.py

_CUR = [None]

def chk(label, ok):
    """A labelled micro-check, recorded under the running family."""
    ok = bool(ok)
    MICRO.append((_CUR[0], str(label), ok))
    print(("PASS " if ok else "FAIL ") + str(label))

class _Exit(Exception):
    def __init__(self, code): self.code = code

def _out(name):
    """A file the script wrote into out/ (the scripts run with out/ as the working directory)."""
    return os.path.exists(os.path.join(HERE, "out", name))

def _show_pngs(pngs):
    """Inside a notebook, display the PNG copies of the figures a script saved; a no-op under plain python."""
    try:
        from IPython.display import display, Image
        get_ipython()                                     # NameError outside IPython
    except Exception:
        return
    for p in pngs:
        display(Image(filename=p))



# ----------------------------------------------------------------------------------------------------------------
# the registry's predicates: fam -> function(ns, out) making chk calls on the script's namespace / printed output
# ----------------------------------------------------------------------------------------------------------------
def _pred_flux(ns, out):
    flux, Us, Un, Usn = ns["flux"], ns["Us"], ns["Un"], ns["Usn"]
    chk("unit point source: flux = 1 exactly through the R = 0 and R = 1 surfaces", flux(Us, 0) == Fr(1) and flux(Us, 1) == Fr(1))
    chk("source-free noise field: flux = 0 exactly", flux(Un, 1) == Fr(0))
    chk("source + noise: flux = 1 exactly (superposition)", flux(Usn, 1) == Fr(1))

def _pred_born(ns, out):
    add, norm2, units, msq = ns["add"], ns["norm2"], ns["units"], ns["mean_sq_pm"]
    ok = True
    for n in range(1, 11):
        s = (0, 0)
        for _ in range(n): s = add(s, units[0])
        ok &= norm2(s) == n * n
    chk("coherent stack: |Σ|² = n² exactly for n = 1 … 10", ok)
    chk("incoherent ensemble: ⟨|Σ|²⟩ = n exactly over all sign patterns for n = 1 … 10", all(msq(n) == Fr(n) for n in range(1, 11)))

def _pred_fp(ns, out):
    mp = ns["mp"]
    z = mp.e ** (-mp.mpf("0.1")); f = (1 - mp.sqrt(1 - z ** 2)) / z; g = mp.e ** (-mp.acosh(mp.e ** mp.mpf("0.1")))
    chk("f(e^(−s)) = e^(−arccosh e^s) at s = 0.1 to 50 digits", abs(f - g) < mp.mpf("1e-50"))
    s = mp.mpf("1e-4"); rel = (mp.acosh(mp.e ** s) - mp.sqrt(2 * s)) / mp.sqrt(2 * s)
    chk(f"rel.err/s = {mp.nstr(rel / s, 6)} → 1/6 at s = 10⁻⁴", abs(rel / s - mp.mpf(1) / 6) < mp.mpf("1e-4"))
    ec = ns["escape_cycle"](200, 8, mp.e ** (-mp.mpf("0.02"))); el = ns["escape_line"](8, mp.e ** (-mp.mpf("0.02")))
    chk(f"finite cycle N = 200, a = 8, s = 0.02: |cycle − line| = {mp.nstr(abs(ec - el), 3)} < 10⁻¹⁵ (the wrap correction)", abs(ec - el) < mp.mpf("1e-15"))

def _pred_walk(ns, out):
    z = Fr(3, 5); f = (1 - Fr(4, 5)) / z                      # 1 − z² = 16/25 a rational square: f1 = 1/3 exactly
    chk("the first-passage quadratic (z/2)f² − f + z/2 = 0 holds exactly at z = 3/5 with f = (1 − √(1 − z²))/z = 1/3", z / 2 * f * f - f + z / 2 == 0 and f == Fr(1, 3))
    P = ns["escape_prob"](5, 0.02, seed=5 * 100 + 20); u = 5 * math.sqrt(0.04)
    chk(f"seeded walk a = 5, q = 0.02: P_escape = {P:.3f} against e^(−a√(2q)) = {math.exp(-u):.3f} within 0.03", abs(P - math.exp(-u)) < 0.03)
    chk(f"deep slope of g_obs = g_b/(1 − e^(−√x)) below x = 10⁻² is {ns['sl']:.3f} (→ 1/2)", abs(ns["sl"] - 0.5) < 0.03)
    chk("the figure written (cons3_firstpassage.pdf, .png)", _out("cons3_firstpassage.pdf") and _out("cons3_firstpassage.png"))

def _pred_deep(ns, out):
    o = ns["out"]
    chk(f"D = 0.3: deep slope {o[0.3]['slope']:.3f} (the paper's 1.03)", abs(o[0.3]["slope"] - 1.03) < 0.02)
    chk(f"D = 0.6: deep slope {o[0.6]['slope']:.3f} (the paper's 1.11)", abs(o[0.6]["slope"] - 1.11) < 0.02)
    chk("the boost g_eff/g_N is constant to rising at both D (no √ regime)", all(all(b2 >= b1 - 0.05 for b1, b2 in zip(o[D]["boost"], o[D]["boost"][1:])) for D in (0.3, 0.6)))
    chk("deep.json and the figure written (cons1_deepregime.pdf, .png)", _out("deep.json") and _out("cons1_deepregime.pdf") and _out("cons1_deepregime.png"))

def _pred_deep_fp(ns, out):
    chk("the script's verdict: mean response Newtonian (slope 1 within 2 × 10⁻³) at D = 0.3 and 0.6, boost constant to rising", ns["ok"])
    m = re.findall(r"log-slope d ln g_eff/d ln g_N = ([0-9.]+)", out)
    chk(f"the two slopes {m} within 2 × 10⁻³ of 1", len(m) == 2 and all(abs(float(v) - 1) < 2e-3 for v in m))

def _pred_interp(ns, out):
    chk(f"deep slope {ns['sl_deep']:.3f} → 1/2 and Newtonian slope {ns['sl_newt']:.3f} → 1", abs(ns["sl_deep"] - 0.5) < 0.02 and abs(ns["sl_newt"] - 1.0) < 0.02)
    d, x, i = ns["d"], ns["x"], ns["i"]
    chk(f"the discriminant ν_simple − ν_frc peaks at {d[i]:.4f} at x = {x[i]:.2f} (the paper's 0.051 at 5.2)", abs(d[i] - 0.051) < 0.002 and abs(x[i] - 5.2) < 0.2)
    np = ns["np"]; xd = ns["xd"]; nu_gen = ns["nu_gen"]
    chk("pinning check 1: a barrier κx^β gives deep slope 1 − β for β = 0.4, 0.5, 0.6", all(abs(np.polyfit(np.log(xd), np.log(xd * nu_gen(xd, 1.0, b)), 1)[0] - (1 - b)) < 0.02 for b in (0.4, 0.5, 0.6)))
    knees = re.findall(r"knee \(nu = nu_frc\(1\)\) at x = ([0-9.]+)\s+vs 1/kappa\^2 = ([0-9.]+)", out)
    chk(f"pinning check 2: the knee sits at 1/κ² for κ = 1, 0.93, 1.1 ({len(knees)} cases)", len(knees) == 3 and all(abs(float(a) - float(b)) < 0.01 for a, b in knees))
    chk("the figure written (cons3_interpolation.pdf, .png)", _out("cons3_interpolation.pdf") and _out("cons3_interpolation.png"))

def _pred_rar_shape(ns, out):
    chk(f"the script's own tally: {ns['fails']} failed checks", ns["fails"] == 0)
    chk(f"the exponential form's free a₀ = {ns['a_e']:.3e}; floor/fit = {ns['a0_floor'] / ns['a_e']:.3f}", 0.8 < ns["a0_floor"] / ns["a_e"] < 0.95)

def _pred_deep_mond(ns, out):
    chk(f"a₀ = cH₀/2π = {ns['a0']:.4e} at H₀ = 67.4 (1.042 × 10⁻¹⁰)", abs(ns["a0"] - 1.042e-10) < 2e-13)
    chk(f"RAR deep-regime slope {ns['slope']:.3f} → 1/2", abs(ns["slope"] - 0.5) < 0.02)
    chk(f"BTFR slope {ns['bt']:.3f} → 1/4", abs(ns["bt"] - 0.25) < 1e-3)
    v = (ns["G"] * 5e10 * ns["Msun"] * ns["a0"]) ** 0.25 / 1000
    chk(f"v_flat(5 × 10¹⁰ M⊙) = {v:.0f} km/s (the paper's 162)", abs(v - 162) < 3)
    chk("the exponential-disk curve: the registered speed flattens (scipy present)", ns["have_disk"] and abs(ns["vo"][-50:].std()) < 0.05 * ns["vo"][-50:].mean())
    chk("the figure written (cons2_rar_btfr.pdf, .png)", _out("cons2_rar_btfr.pdf") and _out("cons2_rar_btfr.png"))

def _pred_cluster(ns, out):
    np = ns["np"]
    Neff = lambda g: np.sum(np.sqrt(g)) ** 2 / np.sum(g)          # the script's law (its own Neff name is rebound to a float by part 2)
    chk("N_eff = (Σ√g)²/Σg = N for equal components (4 → 4, 6 → 6)", abs(Neff([1, 1, 1, 1]) - 4) < 1e-12 and abs(Neff([1] * 6) - 6) < 1e-12)
    chk(f"a dominant BCG suppresses N_eff (4:1:1 → {Neff([4, 1, 1]):.3f} < 3)", Neff([4, 1, 1]) < 3)
    m = re.findall(r"BCG-dominated 4:1:1\s+([0-9.]+)", out)
    chk(f"the script's printed value {m} equals the law's {Neff([4, 1, 1]):.3f}", len(m) == 1 and abs(float(m[0]) - Neff([4, 1, 1])) < 1e-3)
    chk(f"the core boost √N_core = {math.sqrt(ns['Ncore']):.3f} for N_core = 6, decaying to 1 by ~Mpc in the illustration", abs(math.sqrt(ns["Ncore"]) - 2.449) < 0.01)

def _pred_rar_scatter(ns, out):
    chk(f"the script's own tally: {ns['fails']} failed checks", ns["fails"] == 0)
    chk(f"[approx] intrinsic scatter at fixed a₀ = {ns['intr']:.3f} dex (the paper's 0.038)", abs(ns["intr"] - 0.038) < 0.003)
    b = ns["binned"]
    chk(f"[approx] the knee bins 0.3 < x < 3: {b[(-0.5, 0)]:.3f}, {b[(0, 0.5)]:.3f} dex (0.04); the deep bin x < 0.03: {b[(-2, -1.5)]:.3f} dex (0.13)", abs(b[(-0.5, 0)] - 0.04) < 0.01 and abs(b[(0, 0.5)] - 0.04) < 0.01 and abs(b[(-2, -1.5)] - 0.13) < 0.02)
    chk(f"[approx] the bound δα ≲ {ns['da_knee']:.1f}° (3.5°)", abs(ns["da_knee"] - 3.5) < 0.5)
    chk(f"[approx] Spearman ρ(intrinsic, 1/V_flat) = {ns['rho']:+.3f} over {len(ns['res'])} disks (−0.02, n = 116)", abs(ns["rho"] + 0.02) < 0.05 and len(ns["res"]) == 116)
    chk(f"[approx] the gas–disk–bulge amplitude sum would boost the RAR by {ns['np'].median(ns['boost']):.3f} dex (0.14)", abs(ns["np"].median(ns["boost"]) - 0.14) < 0.01)

def _pred_predictions(ns, out):
    Ez, sig, nu, a0, G, Msun, AU = ns["Ez"], ns["sig"], ns["nu"], ns["a0"], ns["G"], ns["Msun"], ns["AU"]
    chk("[approx] v_flat(z)/v₀ = E(z)^(1/4): +7 %, +15 %, +31 % at z = 0.5, 1, 2", abs(Ez(0.5) ** 0.25 - 1.07) < 0.01 and abs(Ez(1.0) ** 0.25 - 1.15) < 0.01 and abs(Ez(2.0) ** 0.25 - 1.31) < 0.01)
    chk(f"[approx] the scatter law at x = 0.01, σ_v/v = 0.1: {sig(0.01, 0.1):.3f} dex (0.27)", abs(sig(0.01, 0.1) - 0.27) < 0.02)
    gext = 1.8 * a0
    nus = [float(nu((G * 1.5 * Msun / (s * 1000 * AU) ** 2 + gext) / a0)) for s in (10, 20, 40)]
    chk(f"[approx] wide binaries with the Galactic field 1.8a₀: ν = {[round(v, 3) for v in nus]} at 10, 20, 40 kAU, a velocity enhancement √ν − 1 of {[round(100 * (v ** 0.5 - 1)) for v in nus]} % (the paper's 10–30 %)", all(0.10 < v ** 0.5 - 1 < 0.30 for v in nus))
    off = [math.log10(math.sqrt(1 / (1 + r * r))) for r in (0.5, 1.0)]
    chk(f"[approx] the coherence offset for σ_v/v = 0.5, 1: {[round(o, 3) for o in off]} dex (−0.05 to −0.15)", -0.16 < off[1] < off[0] < -0.04)

def _pred_figures(ns, out):
    chk("fig_rar.pdf (and .png) regenerated in figures/", all(os.path.exists(os.path.join(HERE, "figures", "fig_rar" + e)) for e in (".pdf", ".png")))
    chk("fig_mechanism.pdf (and .png) regenerated in figures/", all(os.path.exists(os.path.join(HERE, "figures", "fig_mechanism" + e)) for e in (".pdf", ".png")))

PRED = {
    "dark.flux_exact": _pred_flux, "dark.born_exact": _pred_born, "dark.firstpassage_finite": _pred_fp,
    "dark.meridian_walk": _pred_walk, "dark.deep_regime": _pred_deep, "dark.deep_regime_fp": _pred_deep_fp,
    "dark.interpolation": _pred_interp, "dark.rar_shape": _pred_rar_shape, "dark.deep_mond": _pred_deep_mond,
    "dark.cluster_coherent": _pred_cluster, "dark.rar_scatter": _pred_rar_scatter, "dark.predictions": _pred_predictions,
    "dark.make_figures": _pred_figures,
}

def run_block(fam):
    """Run one script of the suite under the registry, apply the registry's predicates, record the family verdict."""
    stem = script_of(fam)
    path = os.path.join(HERE, stem + ".py")
    src = io.open(path, encoding="utf-8").read()
    src = src.replace("raise SystemExit(", "raise __exit__(").replace("sys.exit(", "__exit__(")
    verdicts, lines = [], []
    def _print(*args, **kw):
        s = " ".join(str(a) for a in args)
        kw.pop("file", None); print(s, **kw)
        for line in s.split("\n"):
            lines.append(line)
            t = line.strip()
            m = re.match(r"^ALL PASS: (True|False)", t)
            if m:
                verdicts.append(m.group(1) == "True")
            elif re.match(r"^(\[?(PASS|FAIL|OK|XX)\]?(?![A-Za-z])|\[EXACT\])", t):     # a script's per-check verdict line
                verdicts.append(t[:6].find("PASS") >= 0 or t[:4].find("OK") >= 0 or t.startswith("[EXACT]"))
    def _exit(code=0):
        raise _Exit(code)
    g = {"__name__": "__main__", "__file__": path, "print": _print, "__exit__": _exit}
    pngs = []                                            # every figure a script saves gets a PNG sibling (shown inline in the notebook)
    import matplotlib; matplotlib.use("Agg")
    from matplotlib.figure import Figure
    _savefig = Figure.savefig
    def _savefig_png(fig, fname, *a, **kw):
        _savefig(fig, fname, *a, **kw)
        if isinstance(fname, (str, os.PathLike)):
            png = os.path.splitext(os.fspath(fname))[0] + ".png"
            _savefig(fig, png, dpi=130, bbox_inches="tight"); pngs.append(os.path.abspath(png))
    Figure.savefig = _savefig_png
    _CUR[0] = fam
    n0 = len(MICRO)
    t0 = time.time(); code = 0; err = None
    OUT = os.path.join(HERE, "out"); os.makedirs(OUT, exist_ok=True); os.makedirs(os.path.join(HERE, "figures"), exist_ok=True)
    old = os.getcwd(); os.chdir(OUT); sys.path.insert(0, HERE)      # the scripts write cons*.pdf, deep.json here and ../figures/ = figures/
    try:
        exec(compile(src, path, "exec"), g)
    except _Exit as e:
        code = e.code if isinstance(e.code, int) else (0 if e.code in (None, 0) else 1)
    except Exception:
        err = traceback.format_exc().strip().splitlines()[-1]
        print("    EXCEPTION: " + err)
    finally:
        os.chdir(old)
        Figure.savefig = _savefig
        import matplotlib.pyplot as plt; plt.close("all")
    _show_pngs(pngs)
    for i, v in enumerate(verdicts):                     # the script's own printed verdict lines
        MICRO.append((fam, f"verdict line {i + 1}", v))
    if err is None and fam in PRED:                      # the registry's predicates on the namespace and output
        try:
            PRED[fam](g, "\n".join(lines))
        except Exception:
            err = "predicate: " + traceback.format_exc().strip().splitlines()[-1]
            print("    EXCEPTION: " + err)
    _CUR[0] = None
    micro = [ok for f, _, ok in MICRO[n0:]]
    ok = err is None and code == 0 and all(micro) and len(micro) > 0
    detail = f"{len(micro)} checks, {time.time() - t0:.1f} s" + (f"; {err}" if err else "") + (f"; exit {code}" if code else "")
    check(fam, ok, detail=detail, kind=KIND.get(fam, "EXACT"))
    return ok

def check(pid, ok, detail="", kind="EXACT", label=None):
    ok = bool(ok)
    rows = LEDGER.get(pid, "")
    label = label or LABELS.get(pid, pid)
    RESULTS.append({"id": pid, "rows": rows, "script": script_of(pid), "label": label, "ok": ok, "detail": detail, "kind": kind})
    print(f"  [{'PASS' if ok else 'FAIL'}] {pid:22s} {kind:6s} [{rows}] {label[:90]}" + (f"  --  {detail}" if detail else ""))
    return ok

def summary(write=True):
    n_ok = sum(r["ok"] for r in RESULTS)
    print(f"\nSUMMARY: {n_ok}/{len(RESULTS)} checks passed ({len(MICRO)} micro-checks)" + ("" if n_ok == len(RESULTS) else "  <-- FAILURES"))
    if write:
        with open(os.path.join(HERE, "results.json"), "w") as f:
            json.dump(RESULTS, f, indent=1, ensure_ascii=False)
    return n_ok == len(RESULTS)
