"""
s13common.py — shared registry for the 38-s13 validation package
================================================================
"Exact Quantum Dynamics on the Minimal (13,233) Holographic Substrate" (Akhtman & Voether, 2026), validation package
of the FRC corpus (finite-ring-space/src/38-s13). Thirteen families, each one script run as its own process, its
printed verdict lines captured: the six in-tree audits kept here (check_s13.js, check_o1.js, check_o2.js,
check_o3.js — node, integer-exact; o1_gr_chart.py — sympy, the continuum comparison chart; check_phi.py — the
golden-ratio audit of the Carrier quarter roots; check_fibrations.py — the two fibrations of the frame variety, from the Y4 push of 2026-09-17) and the laboratory's six suites, which live with the laboratory at
finite-ring-space/docs/38-s13 (verify-233, verify-sky, verify-space, verify-f13, verify-hopf, verify-render — node)
and are run from there, one source. A family is identified as s13.<stem>; its micro-checks are the script's own
PASS/FAIL lines together with the registry's predicates (PRED), which pin the stated totals (58, 10, 10, 11, 7, 10, 30;
84, 28, 25, 25, 26, 20 — 208 laboratory checks) and the lines the paper's rows rest on: the pair constants, the
quarter roots hbar = 144, h = 89, the apsidal fraction 3/58 = (p-1)/(Om-1), the per-chronon leak rate 1/232 at both
(13,233) and (5,233), the face ratio 2 <=> 2*gamma - beta = 1, the covering parity, the winding family. A nonzero exit,
a FAIL line or a failed predicate fails the family. Each family names the row(s) of the paper's predicate ledger it
witnesses (LEDGER; rows cited as 38:XN) and the ledger's source column cites the family ids in return.

Kinds: EXACT — integer arithmetic (node BigInt/Number, python int), no float behind any claim; SYMBOLIC — exact
rationals in sympy over a declared continuum chart ([approx: continuum comparison], o1_gr_chart).

Master-ledger rows of the corpus sourced from this paper: 00:C16–C19 (the Carrier quarter-turn mechanism),
00:C22 (the frame variety and its two fibrations: 38:A7, A9, X4), 00:C25 and 00:D13 (the horizon as antipode, observation as the Hopf section), 00:E8, E9 (gravity — the apsidal bound and the laboratory dictionary: 38:C7, C8, C10--C13), 00:D14 (mass is dilation), 00:Y6 (38:A8).
"""
import json, os, re, subprocess, sys, time

RESULTS = []
MICRO = []                    # (family, label, ok)
HERE = os.path.dirname(os.path.abspath(__file__))
LAB = os.path.normpath(os.path.join(HERE, "..", "..", "docs", "38-s13"))    # the laboratory: the six verify-*.js suites

LEDGER = {
    "s13.check_s13":    "38:A1, 38:A2, 38:A3, 38:A4, 38:A6, 38:A7, 38:A8, 38:C6, 38:C10, 38:D2, 38:D6, 38:D7, 38:D8, 38:D9, 38:V3",
    "s13.check_o1":     "38:C7, 38:C8, 38:C12, 38:V4",
    "s13.o1_gr_chart":  "38:C8, 38:V4",
    "s13.check_o2":     "38:D12, 38:V5",
    "s13.check_o3":     "38:D13, 38:V6",
    "s13.check_phi":    "38:A4",
    "s13.verify-233":   "38:B5, 38:V1",
    "s13.verify-sky":   "38:B1, 38:B2, 38:B3, 38:V1",
    "s13.verify-space": "38:D11, 38:V1",
    "s13.verify-f13":   "38:D11, 38:V1",
    "s13.verify-hopf":  "38:A7, 38:A9, 38:X4, 38:V1",
    "s13.check_fibrations": "38:A9, 38:X4",
    "s13.verify-render":"38:B4, 38:B6, 38:B7, 38:C1, 38:C2, 38:C3, 38:C4, 38:C5, 38:D1, 38:D3, 38:D4, 38:D5, 38:D10, 38:V1, 38:V2",
}
FILE = {                      # family -> the script it runs, relative to the repository root
    "s13.check_s13": "src/38-s13/check_s13.js", "s13.check_o1": "src/38-s13/check_o1.js",
    "s13.o1_gr_chart": "src/38-s13/o1_gr_chart.py", "s13.check_o2": "src/38-s13/check_o2.js",
    "s13.check_o3": "src/38-s13/check_o3.js", "s13.check_phi": "src/38-s13/check_phi.py",
    "s13.check_fibrations": "src/38-s13/check_fibrations.py",
    **{f"s13.verify-{s}": f"docs/38-s13/verify-{s}.js" for s in ("233", "sky", "space", "f13", "hopf", "render")},
}
KIND = {f: "EXACT" for f in LEDGER}
KIND["s13.o1_gr_chart"] = "SYMBOLIC"
COUNT = {"s13.check_s13": 58, "s13.check_o1": 10, "s13.o1_gr_chart": 10, "s13.check_o2": 11, "s13.check_o3": 7, "s13.check_phi": 10,
         "s13.verify-233": 84, "s13.verify-sky": 28, "s13.verify-space": 25, "s13.verify-f13": 25, "s13.verify-hopf": 26, "s13.verify-render": 20, "s13.check_fibrations": 30}

LABELS = {
    "s13.check_s13": "the in-tree audit, 58 integer checks: the pair (13, 233), κ = 3, S = 58, g = 2, i = 5; the tower identity C₁₂ = C₄ × C₃ with its general form 4a − κb ≡ 1 (mod 4κ); the channel gcds and N(i) = −1; the Carrier quarter roots 78⁵⁸ = 89 = h, ħ = 144, ħh = 1, ħ + h = Ω; the algebra half ½ = 7; the frame counts 2184 = 156 × 14; the resolvable window; the dilation instance 3/58 = 12/232 = (p−1)/(Ω−1) and the per-chronon rate (κ/S)/(p−1) = 1/(Ω−1) at (13,233) and (5,233); the (53,13) kill test in Carrier 157; the meridian stations, the covering 144 = 36 + 108, the ramification 13/(2m), the fusion 5·39 ≡ −13 (104); the registration fibre product |R| = 696",
    "s13.check_o1": "the dictionary audit, 10 exact-rational checks: the two faces of the leak (angular κ/S, temporal κ/(2S)), ratio exactly 2, the double cover; the closure structure 696/1392 and the half event; the dictionary p_sl = 3(S/κ) r_g and its capacity reading p_sl = S r_g at κ = 3; the p = 53 regression (modulus 157); face ratio 2 ⟺ 2γ − β = 1 over the half-integer PPN lattice",
    "s13.o1_gr_chart": "the continuum comparison chart for the face-ratio identity (C8) and the dictionary (C12), 10 sympy identities [approx: continuum chart]: the parametrised isotropic metric's apsidal coefficient 2 − β + 2γ and clock-deficit coefficient 3/2 (PPN-free), the ratio deviation (2/3)(2γ − β − 1), the dictionary match p_sl = 3(S/κ) r_g, the angular face 3r_g/p_sl = κ/S automatically; Brans–Dicke's combination −2/(2+ω) with the ω → ∞ limit",
    "s13.check_o2": "the multiplicity audit, 11 exact checks: the covering parity theorem (D12) — the reflection identity at p = 5, 13, 17, 29, μ ∈ {1, 3} by the row-parity decider, the shell-parity position law, the 72/72 direct/echo balance, the per-node candidate identities, the shell-1 closed form; the decider Ω-blind at p = 5, 17, 29",
    "s13.check_o3": "the family audit, 7 exact checks: the winding-1/5 identity with the M₀/M₃ station tables, the 144-slot containment in the drawn observable sector, the covering multiset with parity multiplicities, the axis passages 13j/m (drawn iff m ≥ 4), the ramification 13/(2m) in the observable sector",
    "s13.check_phi": "the golden-ratio audit of the quarter roots (A4), 10 integer checks: h = 13/8 ≡ 89 and ħ = 8/13 ≡ 144 on F₂₃₃ (the Fibonacci convergents F₇/F₆), φ present iff 5 is a square (absent at 233, present at 30089), the Pisano closure in-register or in the quadratic extension, the Y6 lock constraint κ_O = 3N ⇒ q = 12N + 1 prime (registrable N = 1, 3, 5, 6, 8, 9)",
    "s13.verify-233": "the laboratory's pair suite, 84 checks: the minimal pair under the complete admissibility predicate (Ω ≡ 41 mod 48, no earlier complete Carrier), the pair dynamics and events, the octant bridge, the precession 3/58 with the joint cycle 696 and the half event at 348, the mass–energy channel",
    "s13.verify-sky": "the laboratory's sky suite, 28 checks: the node field 72 = 3 × 2 × 12 with retarded labels, the fibered covers, the radial ladder R sin(2aπ/13) with capacity 4a < 13, the mounting ×3 = g⁴, the central product isomorphism φ(a, b) = 13a + 12b mod 312",
    "s13.verify-space": "the laboratory's register suite, 25 checks: the register and cone arithmetic, the winding spectrum H_wind, the curl algebra δ_k = 78^k with δ₅₈ = h, the Schrödinger dictionary ψ_{τ+1} = g ψ_τ",
    "s13.verify-f13": "the laboratory's shell-operator suite, 25 checks: H⁷ = 0, ord(U) = 13, U exactly unitary on F₁₃",
    "s13.verify-hopf": "the laboratory's Hopf suite, 26 checks: the non-split fibration by the boost torus with the frame counts 2184 = 156 × 14, SL₂ obstructing at −1; the norm-one sphere ↔ SL₂ (norm = det), the involution counts, the adjoint action PGL₂ → SO₃, the two 2-sphere counts, the centralisers and orbits of the boost axis and of the unit i, the split circle inside the Borel, the bijection G ≅ P¹ × B; Ω-blind at p = 5",
    "s13.check_fibrations": "the two torus fibrations of the frame variety (A9, master C22), 30 exact checks at p = 5, 13, 17: the split fibration by the drive torus C_{p−1} over the unit 2-sphere (p(p+1) points) and the non-split fibration by the boost torus C_{p+1} over the nonsquare-radius 2-sphere (p(p−1) points), the same count p(p²−1); the frame triple G ≅ P¹ × F_p × C_{p−1}; the boundary clause",
    "s13.verify-render": "the laboratory's rendering suite, 20 checks on the production rendering itself: the sky chronon τ mod 24, the Hopf representation node-on-fiber, the frame leak at the halved tick π/232, the one retarded flow law φ(k) = −(b_C − k)π/116, ownership, the half-turn and the C₄ stations, the capacity stations, the scale-tower circuit, the four rays, the quadrature pair",
}

def script_of(fam):
    return os.path.splitext(os.path.basename(FILE[fam]))[0]

def path_of(fam):
    return os.path.normpath(os.path.join(HERE, "..", "..", FILE[fam]))

_CUR = [None]

def chk(label, ok):
    ok = bool(ok)
    MICRO.append((_CUR[0], str(label), ok))
    print(("PASS " if ok else "FAIL ") + str(label))

VERDICT = re.compile(r"^(\[?(PASS|FAIL|OK|XX)\]?(?![A-Za-z])|pass \(|fail \()")

def _count(out, fam):
    """The script's own verdict lines: (passes, fails)."""
    p = f = 0
    for line in out.splitlines():
        t = line.strip()
        m = VERDICT.match(t)
        if not m: continue
        if t.startswith(("PASS", "[PASS", "OK", "pass (")): p += 1
        else: f += 1
    return p, f

def _pred_totals(fam, out, code):
    p, f = _count(out, fam)
    chk(f"{p} verdict lines, {f} failing, exit {code}: the stated {COUNT[fam]} checks all pass", p == COUNT[fam] and f == 0 and code == 0)

def _has(out, *frags):
    return all(any(fr in line for line in out.splitlines()) for fr in frags)

def _pred_s13(fam, out, code):
    _pred_totals(fam, out, code)
    chk("the pair constants and the quarter roots: 78^58 = 89 = h, hbar = 144, hbar*h = 1", _has(out, "PASS  Om = 233 = 4S+1, S=58", "PASS  78^58 = 89 on F233", "PASS  hbar * h = 144*89 = 1 on F233"))
    chk("the apsidal fraction 3/58 = 12/232 = (p-1)/(Om-1)", _has(out, "PASS  apsidal fraction kappa/S = 3/58 = 12/232 = (p-1)/(Om-1)"))
    chk("the per-chronon leak rate (kappa/S)/(p-1) = 1/(Om-1), kappa-free at (13,233) and (5,233) (C10)", _has(out, "PASS  per-chronon leak rate (kappa/S)/(p-1) = 1/(Om-1) = 1/(4S), kappa-free"))
    chk("the (53,13) kill test in Carrier 157", _has(out, "PASS  Om = 157 = 4*39+1"))

def _pred_o1(fam, out, code):
    _pred_totals(fam, out, code)
    chk("the face ratio 2 <=> 2*gamma - beta = 1 over the half-integer PPN lattice; the dictionary p_sl = 3(S/kappa) r_g", _has(out, "ALL O1 DICTIONARY CHECKS PASS") and _has(out, "2*gamma - beta = 1"))

def _pred_chart(fam, out, code):
    _pred_totals(fam, out, code)
    chk("[approx: continuum chart] the ratio deviation (2/3)(2 gamma - beta - 1); the dictionary match p_sl = 3 (S/kappa) r_g; Brans--Dicke's -2/(2+omega) with the GR limit", _has(out, "ALL O1 GR-CHART IDENTITIES PASS") and _has(out, "p_sl = 3 (S/kappa) r_g") and _has(out, "-2/(2+omega)"))

def _pred_phi(fam, out, code):
    n = sum(1 for line in out.splitlines() if re.match(r"^P\d+ ", line.strip()))
    chk(f"{n} numbered checks reported, the script's closing line present, exit {code}: the stated 10 pass", n == 10 and _has(out, "check_phi: all checks passed") and code == 0)
    chk("h = 13/8 = 89 and hbar = 8/13 = 144 on F_233 (A4); phi absent at 233 (5 a non-square), present at 30089", _has(out, "89") and _has(out, "144") and _has(out, "30089"))

PRED = {f: _pred_totals for f in LEDGER}
PRED.update({"s13.check_s13": _pred_s13, "s13.check_o1": _pred_o1, "s13.o1_gr_chart": _pred_chart, "s13.check_phi": _pred_phi})

def run_block(fam):
    """Run one script as its own process (node or python), echo its output, apply the registry's predicates, record the verdict."""
    path = path_of(fam)
    cmd = ["node", path] if path.endswith(".js") else [sys.executable, path]
    _CUR[0] = fam
    n0 = len(MICRO); t0 = time.time(); err = None; out = ""; code = 0
    if not os.path.exists(path):
        err = f"missing script {os.path.relpath(path, HERE)}"; code = 127
        print("    EXCEPTION: " + err)
    else:
        try:
            r = subprocess.run(cmd, cwd=os.path.dirname(path), capture_output=True, text=True, timeout=600)
            out, code = r.stdout, r.returncode
            print(out.rstrip())
            if r.stderr.strip(): print("    stderr: " + r.stderr.strip().splitlines()[-1])
        except Exception as e:
            err = f"{type(e).__name__}: {e}"; print("    EXCEPTION: " + err)
    for i, line in enumerate(l for l in out.splitlines() if VERDICT.match(l.strip())):   # the script's own verdict lines
        MICRO.append((fam, f"verdict line {i + 1}: {line.strip()[:80]}", line.strip().startswith(("PASS", "[PASS", "OK", "pass ("))))
    if err is None:
        try:
            PRED[fam](fam, out, code)
        except Exception as e:
            err = f"predicate: {type(e).__name__}: {e}"; print("    EXCEPTION: " + err)
    _CUR[0] = None
    micro = [ok for f, _, ok in MICRO[n0:]]
    p, f = _count(out, fam)
    ok = err is None and code == 0 and all(micro) and len(micro) > 0
    detail = f"{p} script checks, {len(micro)} predicates, {time.time() - t0:.1f} s" + (f"; {err}" if err else "") + (f"; exit {code}" if code else "")
    check(fam, ok, detail=detail, kind=KIND.get(fam, "EXACT"))
    return ok

def check(pid, ok, detail="", kind="EXACT", label=None):
    ok = bool(ok)
    rows = LEDGER.get(pid, "")
    label = label or LABELS.get(pid, pid)
    RESULTS.append({"id": pid, "rows": rows, "script": script_of(pid), "file": FILE[pid], "label": label, "ok": ok, "detail": detail, "kind": kind})
    print(f"  [{'PASS' if ok else 'FAIL'}] {pid:20s} {kind:9s} [{rows[:60]}{'…' if len(rows) > 60 else ''}] {label[:80]}" + (f"  --  {detail}" if detail else ""))
    return ok

def summary(write=True):
    n_ok = sum(r["ok"] for r in RESULTS)
    print(f"\nSUMMARY: {n_ok}/{len(RESULTS)} checks passed ({len(MICRO)} micro-checks)" + ("" if n_ok == len(RESULTS) else "  <-- FAILURES"))
    if write:
        with open(os.path.join(HERE, "results.json"), "w") as f:
            json.dump(RESULTS, f, indent=1, ensure_ascii=False)
    return n_ok == len(RESULTS)
