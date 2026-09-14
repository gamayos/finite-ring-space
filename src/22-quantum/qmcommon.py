"""
qmcommon.py — shared registry for the 22-quantum validation package
====================================================================
"Quantum Observation over Finite Holographic Substrate" (Akhtman & Voether, 2026), validation package of the FRC
corpus (finite-ring-space/src/22-quantum). The paper's seventeen validation suites are kept as written — each
self-contained, one PASS line per check (187 in all), a FAIL raising an assertion, a terminal "<suite>: all checks
passed" — and run here through one registry: a *family* is one suite's verdict (identified as qm.<suite>, e.g.
qm.composite), its micro-checks the suite's PASS/FAIL lines; an assertion, an exception or a nonzero exit fails the
family. Each family names the row(s) of the paper's predicate ledger it witnesses (LEDGER; rows cited as 22:XN), and
the ledger's source column cites the family ids in return; the paper's Appendix B (the per-claim validation map)
is the finer, check-level mapping.

Kinds. EXACT — exact arithmetic throughout (modular integers, Gaussian integers, cyclotomic rings, exact rationals),
exhaustive where the domain is finite, deterministic (fixed test states, no RNG in any verdict); NUM — floating point
as the numeric image of exact references (qm.emulation, the hardware compilations, agreement to 1e-12). The kind is
recorded per family in results.json.

Master-ledger rows reached through the paper rows: 00:D4 (22:B1), 00:F1 (22:C10, 22:C12), 00:C10 (22:C10, 22:C11),
00:C11 (22:C12), 00:F2 (22:C15), 00:F3 (22:C21), 00:D3 (22:B6), 00:D1 (22:B2), 00:C4, 00:C9 (22:A1), 00:D10 (22:C11),
00:B8 (22:Z1), 00:F4, 00:T6, 00:Y5 (22:B2).
"""
import io, json, os, re, sys, time, traceback
from collections import OrderedDict

RESULTS = []
MICRO = []                    # (family, label, ok)
HERE = os.path.dirname(os.path.abspath(__file__))

# family -> paper rows witnessed
LEDGER = {
    "qm.validate":        "22:C1, 22:C2, 22:C3, 22:C4, 22:C5, 22:C7, 22:C9, 22:C24",
    "qm.sorkin":          "22:C8, 22:P2, 22:X8",
    "qm.dispersion":      "22:A2, 22:P4",
    "qm.composite":       "22:C15, 22:C16, 22:C17, 22:C26, 22:P3, 22:X7",
    "qm.synchronisation": "22:C15",
    "qm.renou":           "22:C18, 22:P3",
    "qm.bmv":             "22:C19, 22:P1",
    "qm.decoherence":     "22:C7, 22:C20",
    "qm.equivalence":     "22:C22",
    "qm.granularity":     "22:C14, 22:P5",
    "qm.stratum":         "22:C10, 22:C11",
    "qm.gravfraction":    "22:C21",
    "qm.gleason":         "22:C12",
    "qm.emulation":       "22:V3",
    "qm.omega":           "22:A5, 22:Z2",
    "qm.intersubject":    "22:C23, 22:X4",
    "qm.transport":       "22:C27",
}

KIND = {f: "EXACT" for f in LEDGER}
KIND["qm.emulation"] = "NUM"

LABELS = {
    "qm.validate": "the single-system formalism on F₁₅₇ and F₄₂₁ (Z[i], Z[ζ₁₂]): frame data and cores of both worked carriers, fibre partitions, the selection rule over all channel pairs, drive eigenstates for all windings, forced-basis orthogonality, Parseval (1124 = 1124) and Lüders on a fixed state, the ledger selection rule, reduction commutation, the two-regime dichotomy",
    "qm.sorkin": "Sorkin nullity I₃ = I₄ = 0 with I₂ ≠ 0 on F₁₅₇ and F₄₂₁ (Z[i], shadows mod 157); sub-horizon shadow exactness; wrap quantisation in pZ",
    "qm.dispersion": "exact boost transport on F₁₃, F₁₆₉: Clifford relations, spin conjugation for all 168 boosts, the group law, covariance over the full norm-one cycle on F₁₃⁴ spinor fields, Dirac→Klein–Gordon factorisation, full-cycle closure with the finite spinor double cover S^((p+1)/2) = −I",
    "qm.composite": "the composite gate on F₆₄₁ (Z[ζ₈₀], Z[ζ₈]): conserved offset, σₓ doublet readout (16 × 80 cases), the singlet law E(Δ) = cos(πΔ/40), composite reduction, exact no-signalling, the exhaustive 80³ CHSH sweep, Tsirelson saturation S = 2(ζ₈ + ζ₈⁻¹), S² = 8; the unequal-cycle gate U1–U6 on F₄₂₁ (C₆₀, C₂₈): the recurrence over all 1680 winding vectors, gcd-offset superselection, 1676/1676 orbit-nontrivial characters cancelling, carrier-internal reduction, the Born window guard",
    "qm.synchronisation": "the m-body extension of the conserved offset on F₆₄₁, F₁₃ (Z[ζ₁₆], Z[ζ₄]): the offset vector conserved on all Nᵐ configurations, every orbit of length N, Nᵐ⁻¹ orbits with the offset a bijective label, the synchronised orbit unique with |·|² = m², the offset-uniform average |·|² = m by exact character orthogonality — exhaustive for m ≤ 6",
    "qm.renou": "the real-vs-complex network over Q(ζ₈): Bell basis = orbit-sector states, entanglement swapping, the full conditional table = the complex-quantum table (3 × 6 × 4 entries), the canonical witness 6√2 as a ring identity, source independence as three exact statements",
    "qm.bmv": "the gravitational channel over Q(ζ₈₀): C² = sin²(φ/2) exactly over the full sweep, the Horodecki S²_max = 4(1 + C²) = 4 + |ad − bc|² exactly, drive commutation and no-signalling as ring identities, V² + C² = 1 as a ring identity",
    "qm.decoherence": "forbidden collapse (contrast 1 exactly at every drive time), dilation dephasing as the characteristic function of the internal winding distribution, the Gaussian envelope, the exact revival V(n) = 1 (Q(ζ₄₀)); the registered drive-frequency count integral and uniform (P = 1/7) for a distinct-eigenvalue superposition, the snapshot dephasing over the recurrence (Z[ζ₇])",
    "qm.equivalence": "the two scaling laws on the exact rational lattice Poisson: field linearity and exact m-coefficients (full gas sourcing), η = 0 identically, E|Σζ^θ|² = m exactly by character orthogonality against m² locked; the sampled √m scaling as a numerical illustration",
    "qm.granularity": "the depth ceiling over Q(ζ₈): the denominator law 2^⌈k/2⌉ with minimality, the tally-norm law 2^k / 2^(k+1), the exact ceilings k* = max{k : d·W(k) < Ω} (unit core k* = 8 and Bell core k* = 6 in F₆₄₁; 404 and 202 at the corpus windows, by integer comparison), lift-ambiguity onset past k*, wrap discrepancies as multiples of Ω; the conductor-4 splitting law (the Gaussian Hadamard over Q(i), no ζ₈)",
    "qm.stratum": "the two probability strata (Z[i], Z[ζ₁₂], F₆₄₁): the two-way part of the Gaussian ledger = the tally lattice (exhaustive); engineered-core weights as exact Carrier residues on Ω = 641; the chart-ring counterexample 1 + ζ₁₂ excluded; the zoom-grid witness; the framed readout map by integer square root (the Bell-weight instance 23/54, the largest-remainder allocation 35 + 34 + 6 + 6 = 81, grid nesting, the M3 √3 instance); the conjugate-pair trace tally and the dial-ensemble Parseval tally (160/160)",
    "qm.gravfraction": "the coherent-fraction channel over Z[ζ₁₆]: the synchronised branch phase ζ^(m_c a) exact, pairwise m_c1·m_c2 scaling, the offset-spread systematic phase zero by complete character sums, envelope separation (m² against 0), the reduced channel Γ assembled exactly with a thermal instance, the complete-spread diagonality under the nondegeneracy hypothesis with an exact PPT instance, the exhaustive 15-partition classification (NPT exactly at size-3 blocks, minimal PT eigenvalue (1 − √3)/4), the local-additivity theorem",
    "qm.gleason": "uniqueness of the pair tally on the Q₄ core (Z[i], exhaustive): nonnegative-tally character combinations = the admissible two-way drive-invariant kernels, Fourier inversion exact, the negative-coefficient witness, single-channel response iff a scaled unit coefficient vector (channel fixing), the fibre-norm counterexample failing channel selectivity, the w_r/16 multiplier instance and the linear-degree exclusion, the in-sector pure-winding fixing F(ψ_k) = d²c_{k mod d}, the spanning/polarisation transfer (core DFT invertible, det −16i)",
    "qm.emulation": "the hardware compilations: the I₃⊗QFT₄† (12-level) and I₂⊗QFT₈† (16-level) unitaries equal the forced bases, the selection rules, the uniform-outcome law, the three-outcome interference law, the σₓ doublet law at π/40, the gate decomposition H–CS–H–SWAP; the two experiment cards emitted (numeric, 10⁻¹² against the exact references)",
    "qm.omega": "the Ω ledger in scale arithmetic: every floor below the anchor with recorded margins, the joint window [8 × 10⁴⁹, ∞) containing Ω = 10¹²², scale coherence of √Ω and Ω^(1/4), the identification of the binding floor; the ledger table printed",
    "qm.intersubject": "inter-Subject consistency on F₄₂₁ (Z[ζₙ]): two Subjects reading one Object with equal cores (S₆₁, S₁₃ on O₂₉) and embedded cores (S₂₉, S₁₃ on O₆₁) — order-independent joint refinement to the common core, selection-rule agreement on the quarter-turn datum, realisability iff the channels agree on Q₄, order-independence on the shared cell; a Gaussian-integer superposition input and the incomparable-core (C₁₂, C₈ in C₂₄) refinement control",
    "qm.transport": "the quarter-turn transport trichotomy on F₁₅₇, F₄₂₁, F₆₄₁: the winding reduction carries the ambient quarter-turn faithfully iff κ ≡ κₙ (mod n), conjugately iff κ ≡ −κₙ, κ mod 4 the coarsest invariant — faithful (F₁₅₇→C₁₂; F₄₂₁→Q₄), conjugate (F₄₂₁→C₆₀, C₂₈, C₁₂; F₁₅₇→C₅₂), broken (F₆₄₁→C₄₀)",
}

def script_of(fam):
    return fam.split(".")[1]            # qm.<suite> runs <suite>.py

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
