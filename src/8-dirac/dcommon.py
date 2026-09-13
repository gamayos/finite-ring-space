"""
dcommon.py — shared registry for the 8-dirac validation package
================================================================
"Schrödinger and Dirac Dynamics over Finite Substrate" (Akhtman, 2026), validation package of the FRC corpus
(finite-ring-space/src/8-dirac). Every script is exact integer arithmetic over F_p and K = F_p[w]/(w² − ν):
no floats, no random sampling. Each script decides families of micro-checks (a family is the labelled claim of
its docstring: Z1, C3, P5, O1a, X7, L2, …); a family is one check of the registry, identified as
<script tag>.<family> (shell.Z1, o2.C3, o7.P5, o134.O1a, o8.X7, lat.L2, fin.S1, o9.S1), and names the row(s)
of the paper's predicate ledger it witnesses (LEDGER; rows cited as 8:XN). The ledger's source column cites
these check ids in return. Master-ledger rows of the corpus reached through the paper rows: 00:C3 (8:B4),
00:C8 (8:B5, 8:B6), 00:B10 (8:B5, the chart grading clause).
"""
import os, json, sys
from collections import OrderedDict

RESULTS = []           # one record per family check
MICRO = []             # (script tag, family, label, ok) — every micro-check

# check id -> paper ledger row(s)
LEDGER = {
    "fin.S1": "8:E2", "fin.S2": "8:C4, 8:C6, 8:E3", "fin.S3": "8:D2, 8:D6, 8:D7, 8:D8, 8:D12",
    "shell.Z1": "8:F3", "shell.Z2": "8:F3", "shell.Z3": "8:F4", "shell.Z4": "8:D5, 8:D12",
    "o2.C1": "8:B3", "o2.C2": "8:B2", "o2.C3": "8:B3", "o2.C4": "8:B3", "o2.C5": "8:B3", "o2.C6": "8:D5",
    "o2.C7": "8:B4", "o2.C8": "8:B4, 8:D12", "o2.C9": "8:B4",
    "o7.P1": "8:B5", "o7.P2": "8:B4", "o7.P3": "8:B4", "o7.P4": "8:B5", "o7.P5": "8:B6", "o7.P6": "8:B6",
    "o134.O1a": "8:D5", "o134.O1b": "8:D5", "o134.O1c": "8:D5", "o134.O1d": "8:D5", "o134.O1e": "8:D12",
    "o134.O3a": "8:C5", "o134.O3b": "8:C5", "o134.O4a": "8:C6, 8:E4", "o134.O4b": "8:E4", "o134.O4c": "8:E4", "o134.O4d": "8:E4",
    "o8.X1": "8:D9", "o8.X2": "8:D9", "o8.X3": "8:D9", "o8.X4": "8:D9", "o8.X5": "8:D10", "o8.X6": "8:D10", "o8.X7": "8:F4", "o8.X8": "8:D11",
    "lat.L1": "8:F2", "lat.L2": "8:F2", "lat.L3": "8:F2", "lat.L4": "8:F2", "lat.L5": "8:F2",
    "o9.S1": "8:B7", "o9.S2": "8:B7", "o9.S3": "8:B7", "o9.S4": "8:B7",
}

# check id -> the claim it decides (the family lines of the script docstrings, condensed)
LABELS = {
    "fin.S1": "power maps on F_13^×: image counts (p−1)/gcd(ε, p−1) and loss factors gcd(ε, p−1) for ε = 1, 2, 3, 4, 6, 12",
    "fin.S2": "Cayley step of H = −Δ on F_13 at α = c: U^13 = I; every trace-zero α = kc admissible with exact order 13 (k ≠ 0)",
    "fin.S3": "F_13 Dirac example: Clifford relations for η = diag(−2,1,1,1); S⁻¹γ^μS boost formulas; transported γ̂⁰ = 10γ⁰ − 4γ¹, γ̂¹ = −2γ⁰ + 10γ¹; A = 10, B = 2; covariance on a sample field",
    "shell.Z1": "the drive pullback is a permutation operator with D χ_k = g^{−k} χ_k on every character and cycle point (p = 13, 17)",
    "shell.Z2": "isotropy: ⟨χ_k, χ_k⟩ = 0 except k = 0, (p−1)/2 with eigenvalues ±1",
    "shell.Z3": "sector separation: ord(g⁻¹) = p − 1 > 2, the free evolution is no Cayley step of a Frobenius-fixed Hamiltonian",
    "shell.Z4": "F_17 example: i = 3^{−4} = 4, 2, i, e squares, g nonsquare; ν = 3, A = 15, B = 1, A² − νB² = 1; |G_3| = 18, |G_2| = 14; an order-3 boost at 17, none at 13",
    "o2.C1": "every primitive g is a nonsquare on every symmetry-complete shell p < 2000",
    "o2.C2": "the nonsquare class is unique: the product of two nonsquares is a square",
    "o2.C3": "i, 2, 2⁻¹, −2 are squares iff κ is even: on κ-even shells g is the only named nonsquare",
    "o2.C4": "e = g^i has no stable square class (counterexamples both ways)",
    "o2.C5": "flip stability: [g⁻¹] = [g]",
    "o2.C6": "|G_ν| = p + 1 with ν = g, by exhaustive enumeration on small shells",
    "o2.C7": "F_13 anchor: g = 2 = ν, i = 5, 2⁻¹ = 7 nonsquare (κ odd, non-admissible)",
    "o2.C8": "F_17 anchor: 2, i = 4, e squares, only g = 3 nonsquare, |G_3| = 18",
    "o2.C9": "lab Carrier Ω = 2,408,561: g = 6 nonsquare; 2, 2⁻¹, −2, i = ħ = 18,688 squares; c = √(2⁻¹) = 171,106 base-rational",
    "o7.P1": "squares = ⟨g²⟩: the square class is the drive-step parity, exhaustive on every primitive g of F_13, F_17, Euler form on p < 2000",
    "o7.P2": "ν = c² · (2g) exactly (2c² = 1); lab-Carrier instance 1,204,281 · 12 = 6 = g",
    "o7.P3": "[c²] even iff κ even, [2g] odd iff κ even, the product odd on every shell",
    "o7.P4": "on κ-even shells every element of Q₄ = {1, i, −1, −i} is a square: the chart grading carries no signature",
    "o7.P5": "N(gx) = g² N(x), g² a square (registered transport even), g odd, x² = g unsolvable in F_p",
    "o7.P6": "gauge stability: dlog_g(g⁻¹) = −1 odd — the flip preserves the parity class",
    "o134.O1a": "kernel of (x, y) ↦ Λ(x, y) is the scalar line: p − 1 preimages per boost, |G_ν| = p + 1",
    "o134.O1b": "Hilbert 90: A − Bw = z/z̄, z F_p^× ↦ z/z̄ a bijection onto N¹",
    "o134.O1c": "G_ν is cyclic: an element of order p + 1 exists",
    "o134.O1d": "an order-3 boost exists iff 3 | p + 1 (17 yes, 13 no)",
    "o134.O1e": "F_17 is the minimal admissible shell: κ = 4 even, κ ≡ 1 (mod 3), p ≡ 5 (mod 12), no smaller symmetry-complete p",
    "o134.O3a": "the Cayley map φ(λ) = (1+aλ)/(1−aλ), a ∈ K⁻ nonzero, bijects P¹(F_p) onto N¹ with φ(∞) = −1",
    "o134.O3b": "the unitary group of one channel is N¹ = C_{p+1}",
    "o134.O4a": "kinetic case: H = −Δ nilpotent, U unipotent, ord(U) = p",
    "o134.O4b": "potential case: H = M_V diagonal, eigenphases in N¹, ord(U) = p + 1 (13 → 14, 17 → 18)",
    "o134.O4c": "mixed case: ord(U) = 1563 for H = −Δ + M_id at p = 5",
    "o134.O4d": "composite: the order of a block-diagonal pair is the lcm (13, 14 → 182)",
    "o8.X1": "plain adjoints: (γ⁰)† = −γ⁰, (γ¹)† = −γ¹, (γ²)† = +γ², (γ³)† = −γ³ (p = 5, 13, 17)",
    "o8.X2": "the spinor twist X = γ⁰γ¹γ³: Hermitian, X² = ν, commutes with γ⁰, γ¹, γ³, anticommutes with γ²; X⁻¹(γ^μ)†X = −γ^μ for all μ",
    "o8.X3": "the γ⁰-twist fails: signs remain mixed",
    "o8.X4": "T − T⁻¹ nilpotent and anti-self-adjoint; D^s X-self-adjoint and nilpotent",
    "o8.X5": "1+1 at p = 5: H = D^s X-self-adjoint, the Cayley step X-unitary, unipotent with ord(U) = 5",
    "o8.X6": "massive: H = D^s − mI, ord(U) = lcm(p-power, ord_{N¹} φ(−m)) for m = 1, 2 at p = 5",
    "o8.X7": "the cycle Laplacian Δ_Φ is self-adjoint, its Cayley steps commute with D, the composite is unitary (p = 13)",
    "o8.X8": "spin lift vs the spinor form: S(x,y)# = S(x,−y) = δS⁻¹; the transport scales the X-form by N(z), norm-one lifts preserve it",
    "lat.L1": "ladder bounds: the energy index κ + 1 is the first rung past the midpoint of the ladder 1 … 2κ",
    "lat.L2": "one shift, two ladders: m ↦ m + κ is multiplication by g^κ = ±i; a ↦ a + κ sends 1 ↦ κ + 1",
    "lat.L3": "κ = −4⁻¹, so the energy radius is 1 + κ = 3·4⁻¹",
    "lat.L4": "terminal latitude: π = 2κ = −2⁻¹ = −c²; on the Carrier π_Ω = 2S",
    "lat.L5": "chart consistency: the unit-norm circle has p − 1 points; the energy circle carries norm 9/16",
    "o9.S1": "the Euclidean form t² + x² + y² + z² has p³ + p² − p zeros on every symmetry-complete shell p < 60",
    "o9.S2": "the form −νt² + x² + y² + z², ν = g, has p³ − p² + p zeros",
    "o9.S3": "p = 13: the counts are 2353 and 2041",
    "o9.S4": "over F_{p²} every element of F_p is a square: the extension erases the dichotomy",
}

def chk(label, ok, tag=None):
    """A micro-check: label = '<family> …' (the family is the first token); recorded, never exits."""
    fam = label.split()[0]
    MICRO.append((tag or _current_tag(), fam, label, bool(ok)))
    if not ok:
        print(f"    FAIL: {label}")

_TAG = [None]
def _current_tag():
    return _TAG[0] or "?"

def begin(tag):
    _TAG[0] = tag

def flush(tag, order=None):
    """Aggregate the micro-checks of a script into one registry check per family."""
    fams = OrderedDict()
    for t, fam, label, ok in MICRO:
        if t == tag:
            fams.setdefault(fam, []).append(ok)
    for fam in (order or fams):
        oks = fams.get(fam, [])
        check(f"{tag}.{fam}", ok=bool(oks) and all(oks), detail=f"{len(oks)} exact micro-checks")
    _TAG[0] = None

def check(pid, ok, detail="", kind="EXACT", label=None):
    ok = bool(ok)
    rows = LEDGER.get(pid, "")
    label = label or LABELS.get(pid, pid)
    script = pid.split(".")[0]
    script = {"shell": "shell_checks", "o2": "o2_checks", "o7": "o7_checks", "o134": "o134_checks", "o8": "o8_checks",
              "lat": "latitude_checks", "fin": "worked_checks", "o9": "o9_signature_counts"}.get(script, script)
    RESULTS.append({"id": pid, "rows": rows, "script": script, "label": label, "ok": ok, "detail": detail, "kind": kind})
    print(f"  [{'PASS' if ok else 'FAIL'}] {pid:9s} {kind:5s} [{rows}] {label}" + (f"  --  {detail}" if detail else ""))
    return ok

def summary(write=True):
    n_ok = sum(r["ok"] for r in RESULTS)
    n_micro = len(MICRO)
    print(f"\nSUMMARY: {n_ok}/{len(RESULTS)} checks passed ({n_micro} exact micro-checks)" + ("" if n_ok == len(RESULTS) else "  <-- FAILURES"))
    if write:
        with open("results.json", "w") as f:
            json.dump(RESULTS, f, indent=1, ensure_ascii=False)
    return n_ok == len(RESULTS)
