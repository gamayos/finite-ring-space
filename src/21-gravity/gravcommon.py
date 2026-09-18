"""
gravcommon.py — shared registry for the 21-gravity validation package
======================================================================
"Gravitation as Phase Synchronisation over Finite Relational Substrate" (Akhtman & Voether, 2026), validation package
of the FRC corpus (finite-ring-space/src/21-gravity). The paper's validation suite is kept as written — twenty
scripts, each self-contained, printing its computed values against the manuscript's targets and ending in a PASS/FAIL
verdict — and run here through one registry: a *family* is one script's verdict (identified as grav.<stem>, e.g.
grav.newton, grav.strongfield), its micro-checks the script's own labelled checks (the `chk(...)` calls of the newer
scripts) and every PASS/FAIL line it prints; an uncaught exception or a nonzero exit fails the family. Each family
names the row(s) of the paper's predicate ledger it witnesses (LEDGER; rows cited as 21:XN), and the ledger's source
column cites the family ids in return.

Kinds. EXACT — decidable identities over finite fields, cyclotomic extensions, exact rationals, or symbolic identities
(sympy) with no floating-point tolerance in the verdict; CHART — a continuum reading (a limit, a series coefficient, a
numerical extremum) or a comparison with measured data, tagged [approx]/[data] in the script, verdict by stated
tolerance; SIM — a seeded stochastic simulation (the Kuramoto chain of validate_fluxnoise), verdict by stated
tolerance on time averages. The kind is recorded per family in results.json.

Master-ledger rows reached through the paper rows: 00:L1 (21:P3, 21:C19, 21:X2), 00:D5 (21:B1–B6), 00:L7 (21:P5),
00:C21 (21:C11), 00:E4, 00:E7 (the master's 21-grav pointers, audited in the T26 record), 00:Z7 (21:Z1).
"""
import io, json, os, re, sys, time, traceback
from collections import OrderedDict

RESULTS = []
MICRO = []                    # (family, label, ok)
HERE = os.path.dirname(os.path.abspath(__file__))

# family -> paper rows witnessed
LEDGER = {
    "grav.newton":           "21:C1, 21:C2",
    "grav.ppn":              "21:C7, 21:C8, 21:C12",
    "grav.strongfield":      "21:C12, 21:C13, 21:P1, 21:P7",
    "grav.fp_gauge":         "21:C9",
    "grav.fierz_pauli":      "21:C9",
    "grav.branch":           "21:C11",
    "grav.fluxnoise":        "21:C19",
    "grav.rar":              "21:C4, 21:P3",
    "grav.deepregime":       "21:C19, 21:P4",
    "grav.deepregime_orbit": "21:C19, 21:C20",
    "grav.radiative":        "21:C15",
    "grav.orderone":         "21:C5, 21:C16, 21:C13",
    "grav.rotating":         "21:C10, 21:C17",
    "grav.primordial":       "21:C18, 21:X6, 21:P8",
    "grav.inertia":          "21:C20",
    "grav.defect":           "21:C21",
    "grav.counting":         "21:C7, 21:C21",
    "grav.binding":          "21:C21, 21:C23",
    "grav.1pn_eih":          "21:C23",
    "grav.2pn":              "21:C8, 21:P6",
    "grav.fold_echo":        "21:C12, 21:P7",
}

KIND = {
    "grav.newton": "CHART", "grav.ppn": "EXACT", "grav.strongfield": "CHART", "grav.fp_gauge": "EXACT",
    "grav.fierz_pauli": "EXACT", "grav.branch": "CHART", "grav.fluxnoise": "SIM", "grav.rar": "CHART",
    "grav.deepregime": "EXACT", "grav.deepregime_orbit": "EXACT", "grav.radiative": "EXACT", "grav.orderone": "EXACT",
    "grav.rotating": "CHART", "grav.primordial": "EXACT", "grav.inertia": "EXACT", "grav.defect": "EXACT",
    "grav.counting": "EXACT", "grav.binding": "EXACT", "grav.1pn_eih": "EXACT", "grav.2pn": "EXACT", "grav.fold_echo": "EXACT",
}

LABELS = {
    "grav.newton": "the Newtonian layer: the exact lattice Green's function of Z³ (Montroll–Bessel) with 4πr·G(r) → 1 and the O(r⁻²) correction, the r⁻¹ potential (r⁻² force), the locked ensemble coupling as m against the incoherent √m; the spanning-tree admissibility det L_red = τ(C_n) = n (n = 5, 8, 12), the finite solvability predicate",
    "grav.ppn": "the relativistic layer: Fermat deflection 4Gm/c²b in the index n = 1 + 2u; β = γ = 1 from the exponential metric; the perihelion factor (2 + 2γ − β)/3 = 1; the static-profile series Gm/r·(1 + (Gm/r²)²/30) — symbolic identities",
    "grav.strongfield": "the strong field: the slip-core boundary r* = √(Gm); the photon sphere r_ph = 2Gm with b_c = 2e·Gm (shadow +4.6 %, ringdown −4.4 %); the ISCO at r = (3 + √5)Gm with accretion efficiency 5.48 % against Schwarzschild's 5.72 % and Gm·Ω/c³ = 0.0633 (0.931×); r_f = r_s/ln Ω, S/S_BH = ln⁻²Ω, the echo delay factor Ω/ln²Ω; Sgr A*/M87* angular diameters 53.3 → 55.7 µas, 39.7 → 41.5 µas [approx]",
    "grav.fp_gauge": "the discrete Fierz–Pauli functional on a periodic (3+1) lattice with integer random fields: gauge invariance under h → h + Δξ an exact integer identity for central differences and failing for one-sided differences (the control) — anti-self-adjointness Δᵀ = −Δ carries the proof; Schwartz–Zippel on random integer fields",
    "grav.fierz_pauli": "uniqueness: by the symbol/transversality method the discrete Fierz–Pauli functional is the unique adjacency-local gauge functional on the shell in the (3+1) signature — the rank-2 analogue of Maxwell uniqueness",
    "grav.branch": "the nonlinear completion: the cut-flux law of the full sine model (transfer antisymmetry) — flux through every closed surface equals the enclosed demand to solver precision for one and two sources at strong gradients, the nonlinear deviation scaling as m³ (no m² self-sourcing); symbolically, isotropic Schwarzschild is the exponential reading of ψ = 2 artanh(U/2), ψ non-harmonic, and the Schwarzschild reading violates the composition law R(a+b) = R(a)R(b) the exponential uniquely satisfies",
    "grav.fluxnoise": "flux conservation under noise: a driven, pinned Kuramoto chain in the statistically stationary regime — the time-averaged transport through every link equals the source demand with and without drive noise (seeded simulation)",
    "grav.rar": "the weak-acceleration floor a₀ = cH₀/2π for H₀ ∈ {67.4, 70, 73} against the SPARC 1.20 ± 0.24 × 10⁻¹⁰ m s⁻² (all within one systematic σ); the Local-Group turnaround radius (Gm/H²)^{1/3} ≈ 1.6 Mpc against the observed ~1 Mpc [data]",
    "grav.deepregime": "the registration crossover: the floor as link-decorrelation rate, x = g_b/a₀ cycles per Hubble time with Born amplitude √x; the resolved fraction f = 1 − η^a with η the in-(0,1) root of the rational quadratic wη² − 2η + w = 0; the deep-MOND limit g_obs → √(g_b a₀) (BTFR), the Newtonian limit f → 1, the η root exact; the e^{−√x} reading [approx]",
    "grav.deepregime_orbit": "the registered-inertia identity and the two-boundary law: the Chebyshev masking weight q_{L,d} against the direct tridiagonal solve of the killed recurrence, exact-rational, on three (L, d, w) triples; impulse in = m g T = registered momentum change identically for framed-rational f = N/T; the event-based killed-registration orbit — registered circular balance v²/r = g_N/f as an exact identity of the event tallies, the offset-sector ledger closing the window total exactly",
    "grav.radiative": "the radiative sector: the quarter-turn conjugate momentum makes the dynamics Hamiltonian, χü = κΔu; channel unity gives c_g² = κ/χ = c²; the Fierz–Pauli field carries two transverse-traceless polarisations of helicity ±2; the dispersion relation, the long-wave speed, TT rank 2, no mode doubling (Nyquist); the symbol even in k, on the continuum form and on C₁₃",
    "grav.orderone": "the order-one constants: c_S′ = 1/4 from the de Sitter closure (the same area law on the cosmological horizon √Ω reproduces the de Sitter entropy defining the cardinality); the 2π of a₀ as the angular period of one phase turn; the radiation constant as the spin-2 quadrupole factor; the 4π; in exact rationals — and on the instantiated Carrier Ω = 2 408 561 the register residues (4S)² ≡ 1, G = 2S = (2·4S)⁻¹, G = −c², c² = 2⁻¹, ħ² = −1, G_p = π_p on four shells",
    "grav.rotating": "the rotating solution as the quarter-turn dual of the static field: the Lense–Thirring frame-dragging ω = 2GJ/c²r³, the gravitomagnetic dipole, horizonless-ness (the redshift floor only), the O(a) shadow spin shift (structure only)",
    "grav.primordial": "the primordial spectrum: P ∝ kⁿ scale-invariant iff n = −3 (n_s = 1) uniquely; the observed red tilt n_s − 1 = −0.035 has the predicted sign [data]; wrapped-chart truncation of correlations beyond ~60°; the O2 probe K²λ₁ → π² monotonically (99.1 % at K = 281)",
    "grav.inertia": "the two-shift update law: the kick as the finite Fourier shift theorem in F_p (exact, no error term); the Ehrenfest parabola on exact chirps, Δ²⟨q⟩ = −s/m as an exact integer second difference; the equivalence principle bitwise — the runs (m, F) and (3m, 3F) give identical registered trajectories",
    "grav.defect": "the projection defect on dev shells: cycle-quotient closure exact (defect 1); windowed registration accumulating exactly the wrap count; K_S = P U_C P contractive on a non-invariant sector while U_C is a permutation of finite order; on the odd-character space of C₁₂ the antisymmetric currents are spanned by odd harmonics with the sine mode the unique minimal degree — the minimal-degree condition a declared realisation",
    "grav.counting": "unified counting in exact integers: the Christoffel registration pattern (a advances per recurrence b, gaps ⌊b/a⌋, ⌈b/a⌉); the censored geometric identity symbolically; the readout instance Ω = 641, g = 3 (s₄ = 114, R₄ = 23/54 and 2/27, the largest-remainder allocation 35 + 34 + 6 + 6 = 81); the negative control at B = 108 (Kesten); the per-stratum split at B = 2, 3 as Galois-symmetric multinomials of (W₊ + W₋)^B in Z[√2] and mod 641",
    "grav.binding": "binding bookkeeping decided in exact arithmetic on the torus Z_N³: superposition exact (no O(G²) term); the far-field cut flux around a bound pair equals m₁ + m₂ exactly (substrate winding sources); the interaction energy exactly bilinear; the binding defect m₁(1 − u₂(a)) a registered-clock identity — hence η_Nordtvedt = 0 with the two-shift cancellation",
    "grav.1pn_eih": "the 1PN equivalence lemma: through first post-Newtonian order the two-body metric coefficients A to O(U²) and B to O(U) coincide with GR's isotropic form on the superposed potential U₁ + U₂, cross term included — the Einstein–Infeld–Hoffmann sector shared exactly; the 2PN ν-sector left open",
    "grav.2pn": "the 2PN inputs: the isotropic-gauge deviations of the exponential metric from Schwarzschild, δA = U³/6 in −g₀₀ and δB = U²/2 in g_ij, certified term by term; the test-particle periastron excess π(GM/c²p)²(2 + e²/2) from the matched-invariant orbit equation (δc₂, δc₃ and their apsidal sum); for PSR J0737−3039 the fractional excess ≈ 1.5 × 10⁻⁶ [chart]",
    "grav.fold_echo": "the fold-return criterion at dev scale, exact over F₁₇: on the chain C₈ with the interior block folded by its exact DFT, the period-averaged exterior return P_E F_I Uⁿ F_I⁻¹ P_E equals the rank-one uniform-floor operator N⁻¹J_E, fold-independent (the fold drops out of the average; master E10)",
}

SCRIPT = {"grav.fierz_pauli": "fierz_pauli_uniqueness"}   # every other family is validate_<stem>.py

def script_of(fam):
    return SCRIPT.get(fam, "validate_" + fam.split(".")[1])

_CUR = [None]

def chk(label, ok):
    """A labelled micro-check of the running script, recorded under its family."""
    ok = bool(ok)
    MICRO.append((_CUR[0], str(label), ok))
    print(("PASS " if ok else "FAIL ") + str(label))

class _Exit(Exception):
    def __init__(self, code): self.code = code

def run_block(fam):
    """Run one script of the suite under the registry and record its family verdict."""
    stem = script_of(fam)
    path = os.path.join(HERE, stem + ".py")
    src = io.open(path, encoding="utf-8").read()
    # the script's own chk (where it defines one) is replaced by the registry's; its exits are caught
    src = re.sub(r"^def chk\(", "def _chk_local(", src, flags=re.M)
    src = src.replace("raise SystemExit(", "raise __exit__(").replace("sys.exit(", "__exit__(")
    verdicts = []
    def _print(*args, **kw):
        s = " ".join(str(a) for a in args)
        kw.pop("file", None); print(s, **kw)
        for line in s.split("\n"):
            t = line.strip()
            if re.match(r"^\[?(PASS|FAIL)\]?\b", t):
                verdicts.append("PASS" in t[:6])
            elif t in ("ALL PASS", "FAILURES PRESENT"):
                verdicts.append(t == "ALL PASS")
    def _exit(code=0):
        raise _Exit(code)
    g = {"__name__": "__main__", "__file__": path, "chk": chk, "print": _print, "__exit__": _exit}
    _CUR[0] = fam
    n0 = len(MICRO)
    t0 = time.time(); code = 0; err = None
    old = os.getcwd(); os.chdir(HERE)
    try:
        exec(compile(src, path, "exec"), g)
    except _Exit as e:
        code = e.code if isinstance(e.code, int) else (0 if e.code in (None, 0) else 1)
    except Exception:
        err = traceback.format_exc().strip().splitlines()[-1]
        print("    EXCEPTION: " + err)
    finally:
        os.chdir(old)
    _CUR[0] = None
    # the script's own printed PASS/FAIL lines (the registry's chk prints through the builtin, not through _print)
    for i, v in enumerate(verdicts):
        MICRO.append((fam, f"verdict line {i + 1}", v))
    micro = [ok for f, _, ok in MICRO[n0:]]
    ok = err is None and code == 0 and all(micro)
    detail = f"{len(micro)} checks, {time.time() - t0:.1f} s" + (f"; {err}" if err else "") + (f"; exit {code}" if code else "")
    check(fam, ok, detail=detail, kind=KIND.get(fam, "EXACT"))
    return ok

def check(pid, ok, detail="", kind="EXACT", label=None):
    ok = bool(ok)
    rows = LEDGER.get(pid, "")
    label = label or LABELS.get(pid, pid)
    RESULTS.append({"id": pid, "rows": rows, "script": script_of(pid), "label": label, "ok": ok, "detail": detail, "kind": kind})
    print(f"  [{'PASS' if ok else 'FAIL'}] {pid:22s} {kind:5s} [{rows}] {label[:90]}" + (f"  --  {detail}" if detail else ""))
    return ok

def summary(write=True):
    n_ok = sum(r["ok"] for r in RESULTS)
    print(f"\nSUMMARY: {n_ok}/{len(RESULTS)} checks passed ({len(MICRO)} micro-checks)" + ("" if n_ok == len(RESULTS) else "  <-- FAILURES"))
    if write:
        with open(os.path.join(HERE, "results.json"), "w") as f:
            json.dump(RESULTS, f, indent=1, ensure_ascii=False)
    return n_ok == len(RESULTS)
